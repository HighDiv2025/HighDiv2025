## Instructions for Building HighDiv

### Prerequisites
```bash
sudo apt update
sudo apt install -y python3 python3-pip python3-venv
sudo apt-get install build-essential cmake
```

### Obtain *HighDiv*
To obtain *HighDiv*, a user may use `git clone` to get a local copy of the Github repository:
```bash
git clone git@github.com:HighDiv2025/HighDiv2025.git
```

### Compile Z3
```bash
# Activate the Python virtual environment
python3 -m venv venv
source venv/bin/activate

pushd z3
python3 scripts/mk_make.py --python
cd build
make -j 15
make install
popd
```

### Compile HighDiv
```bash
cd HighDiv
make
```

By executing this commands, users can build *HighDiv*. Note that *HighDiv* should be built on a 64-bit GNU/Linux operating system.

## Quick Installation Testing
To check whether the compilation is successful or not, the user may run the following command in the `HighDiv` directory:

```bash
./HighDiv -i LIA_bench/LIA_convert_query-1164.smt2 -o samples -n 10 -t 900 -s 123 -m hybrid
```

