TEMPLATE = app
CONFIG += console c++17
CONFIG -= app_bundle
CONFIG -= qt

debug {
    #DEFINES += DEBUG_OUT
    #DEFINES += DEBUG_NO_AUT
    #DEFINES += DEBUG_SLOW_ASSERTS
}

SOURCES += \
        main.cpp

HEADERS += \
    algorithm_argo.h \
    algorithm_dfs.h \
    algorithm_selector.h \
    array.h \
    assertions.h \
    bitarray.h \
    coloring.h \
    graph.h \
    group.h \
    hash.h \
    matrix.h \
    memory.h \
    partition.h \
    permutation.h \
    priority_queue.h \
    proof.h \
    utility.h \
    vector.h
