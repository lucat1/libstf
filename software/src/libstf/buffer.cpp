#include "libstf/buffer.hpp"

namespace libstf {

std::shared_ptr<Buffer> make_buffer(MemoryPool &memory_pool, void *ptr, size_t size, size_t capacity) {
    return std::shared_ptr<Buffer>(
        new Buffer{.ptr = ptr, .size = size, .capacity = capacity}, 
        BufferDeleter(memory_pool));
}

} // namespace libstf
