import os
import yaml
import argparse

from subprocess import run, PIPE, TimeoutExpired
from dataclasses import dataclass

VALIDATOR_TESTS = "tests/witness_validation"

class colors:
    gray = "\033[90m"
    red = "\033[91m"
    green = "\033[92m"
    yellow = "\033[93m"
    cyan = "\033[96m"
    end = '\033[0m'
    bold = '\033[1m'
    white = "\033[m"


def print_ok(text, level=0):
    print(f"{colors.green}{text}{colors.white}")

def print_debug(text, level=0):
    print(f"{colors.gray}{text}{colors.white}")

def print_err(text, level=0):
    print(f"{colors.red}{text}{colors.white}")


def print_unknown(text, level=0):
    print(f"{colors.yellow}{text}{colors.white}")




@dataclass
class TestCase:
    name: str
    witness_path : str
    source_path: str
    expected_verdict: str

    @classmethod
    def from_witness(cls, witness_path):
        with open(witness_path, "r") as f:
            try:
                header = f.readlines()[0]
                expected = header.split(":")[1].strip()
                assert(expected in ["valid", "invalid"])
                f.seek(0)
                yaml_data = yaml.safe_load(f)
            except yaml.YAMLError as e:
                print("Error loading yaml")
                return None

        metadata = None
        for entry in yaml_data:
            if entry.get("entry_type") == "invariant_set":
                metadata = entry

        source_paths = metadata.get("task").get("input_files")
        if len(source_paths) != 1:
            print("Not a single file")
            exit(1)

        source_path = source_paths[0]
        if not os.path.isabs(source_path):
            base_path = os.path.dirname(witness_path)
            source_path = os.path.join(base_path, source_path)

        return cls(
            name = os.path.basename(witness_path),
            witness_path = witness_path,
            source_path = source_path,
            expected_verdict = expected
        )

    def run(self, timeout=10, debug=False):
        # fmt: off
        command = [
            "frama-c", "-seal",
            "-seal-svcomp-mode",
            "-seal-no-memcleanup",
            "-kernel-verbose=0",
            "-seal-validate-witness", self.witness_path,
            self.source_path]
        # fmt: on
        if debug:
            print_debug(" ".join(command))

        def read_verdict(stdout):
            res = stdout.lower()
            if "witness rejected" in res:
                return "invalid"
            if "successful validation" in res:
                return "valid"

            assert(False)

        try:
            process = run(command, timeout=timeout, stdout=PIPE, stderr=PIPE)

            if process.returncode != 0:
                print_err(f"[ERR] {self.name}: error")

            elif self.expected_verdict != read_verdict(process.stdout.decode().strip()):
                print_err(f"[ERR] {self.name}: verdict does not match")

            else:
                print_ok(f"[OK] {self.name}")

            if debug:
                print_debug(process.stdout.decode().strip())
                print_debug(f"<exit: {process.returncode}>")

        except TimeoutExpired as to:
            print(to)
            print_err(f"{self.name}: timeout")



def run_test_case(p, debug):
    test = TestCase.from_witness(p)
    test.run(debug=debug)

def run_all(debug):
    for root, _, files in sorted(os.walk(VALIDATOR_TESTS)):
        if any([f.endswith(".yml") for f in files]):
            print(f"{colors.bold}{os.path.basename(root)}{colors.end}")
        for f in sorted(files):
            if f.endswith(".yml"):
                p = os.path.join(root, f)
                run_test_case(p, debug)

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action="store_true")
    return parser.parse_args()

def main():
    args = parse_args()
    run_all(args.debug)

if __name__ == "__main__":
    main()
