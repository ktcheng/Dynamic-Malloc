# Dynamic-Malloc
N.B. This project is finished.

# Description
This is a project pulled from a C programming course on computer organization (COM SCI 33 @ UCLA), in which we were tasked with creating an original, efficient, and fast implementation of the malloc and free routines. The guidelines of our dynamic memory allocator included instantaneous responses (i.e. responding immediately to system calls), and required direct knowledge of how C handles pointer manipulation and memory allocation. 

The allocator is implemented using a unique combination of bucket sizes for the segregated free list model, one that maximizes both the performance and utility of the allocator. Throughout this project, pointer arithmetic is used extensively, and operation calls on malloc and free were handled on a pseudo-memory layout, one that mimics the heap of the operating system itself. Proper performance required an acute understanding of the technical tradeoffs between throughput and utilization. 

N.B. As this is a project pulled from a CS course, the posting of this repository is to demonstrate the code and what I have learned, and is in no way meant to be a resource for plagiarism or cheating (copying code will only stunt your growth as a programmer anyways). To further reinforce this, the test files for the allocator have not been uploaded, in order to discourage copying code.

# Performance
Throughput Ops: 20884.960
Scaled Utilization: 90.5%
Unscaled Utilization: 97%
