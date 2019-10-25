#### Dependency

1. python3
2. [z3 prover](https://github.com/Z3Prover/z3)
3. some [dependencies](https://github.com/p4bughunt/p4c#ubuntu-dependencies) for p4c
4. [p4_tv](https://github.com/p4bughunt/p4_tv)


#### Build

clone the repo

```
git clone https://github.com/p4bughunt/p4c.git

```

and update the submodules

```
git submodule update --init --recursive
```

then, go to the p4c folder and build the source

```
mkdir build
cd build
cmake .. -DCMAKE_BUILD_TYPE=DEBUG
make -j4
```

#### Test

Hopefully, executable ```p4toz3``` is generated in the folder ```p4c/build```.


First, generate z3 formula files,

```
./p4toz3 /path/to/p4c/backends/toz3/doc/key-bmv2-frontend.p4 --output=/path/to/p4c/backends/toz3/doc/a.py --n_pass=0

./p4toz3 /path/to/p4c/backends/toz3/doc/simplifykey.p4 --output=/path/to/p4c/backends/toz3/doc/b.py --n_pass=1
```

then, link some base python files from 

```
git clone https://github.com/p4bughunt/p4_tv.git
cd /path/to/p4c/backends/toz3/doc
ln -s /path/to/p4_tv/z3_p4/p4z3_base.py /path/to/p4c/backends/toz3/doc/p4z3_base.py
ln -s /path/to/p4_tv/z3_p4/v1model.py /path/to/p4c/backends/toz3/doc/v1model.py
```

finally, run

```
python3 main.py
```


#### Miscs

| Option | Description | 
| :--- | :---: |
| ```--ouput``` | file name of the output python z3 formula |
| ```--n_pass``` | for tagging different p4 program, i.e., ```p4_program_${n_pass}``` in output python file |


#### Minor Issues
1. table names should be indentical in both programs, since they are variables in z3 formula.
2. all user-defined struct or header should be in lower-case.
