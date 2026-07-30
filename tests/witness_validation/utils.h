//void *safe_malloc(size_t size)
//{
//    void *ptr = malloc(size);
//    if (ptr == NULL)
//        exit(1);
//    return ptr;
//}


void *safe_malloc(size_t size)
{
    return malloc(size);
}

