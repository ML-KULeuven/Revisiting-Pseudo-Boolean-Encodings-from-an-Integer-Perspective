# Repo to reproduce results "Revisiting Pseudo-Boolean Encodings from an Integer Perspective"

Authors: Hendrik Bierlee; Jip J. Dekker; Peter J. Stuckey 
Venue: The 22nd International Conference on the Integration of Constraint Programming, Artificial Intelligence, and Operations Research (CPAIOR'25)

Another version of this repo is available on Zenodo: https://doi.org/10.5281/zenodo.14500064

Dependencies:

- Cadical 2.1.0 (already included as subtree)
- Rust `>=1.82` (for main implementation)
- JRE `>=23` (optional, for control encoders Savile Row and Fun-sCOP)
- MiniZinc `>=2.8.5` (optional, for control encoder Picat-SAT)
- Tectonic  `>=0.15.0` (optional, to compile the latex table from the paper)

With these dependencies installed, we can build the tooling and analyze the results presented in the paper

```
# Build software; control encoder dependencies should be included in `bin`. Some integration tests are run as well without requiring optional dependencies.
./build.sh
# Check, analyze, and compile latex table for the results presented in the paper
cargo run -r analyze experiments/mbkp experiments/mbkp-control experiments/mbssp experiments/mbssp-control --table --check
```

The optional dependencies (primarily the control encoders) are not separately hosted in this repo, so may fail to download from their respective hosts in the future. If the baseline solvers are present, it is good to run the integration tests with them by adding `"./solvers/pbc-pb.json"` to the `experiments` field in "./experiments/integration/slurm.json", then running `cargo test`.

To reproduce the experiments with Slurm, change the `nodelist` parameter in each `experiments/*/slurm.json` to what you would add to the `--nodelist` argument.
To reproduce results on the local machine, change it to `Local` instead.
Then, run:

```
cargo run -r load experiments/mbkp
cargo run -r load experiments/mbkp-control
cargo run -r load experiments/mbssp
cargo run -r load experiments/mbssp-control
```

For any questions, please email me at `henk.bierlee@kuleuven.be`

Kind regards,

Hendrik 'Henk' Bierlee

