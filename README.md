# SCP

Attempt at formalising split conformal prediction in Lean4.
Many thanks to everyone from [formalising mathematics].

## Usage

```
nix develop
```

You should now have Lean and Lake pointing to the right toolchain
and about 6 GiB of local cache in local `.lake` directory.
Mind the first run on a fresh clone takes a while to fetch.
Your editor may now be able to use Lean directly via LSP.
For example, I use [nvim] with [lean.nvim].
To interact with the proof

```
nvim SCP/FM1/Project.lean
```

To build everything without an editor

```
lake build SCP
```

To build report(s)

```
tectonic SCP/FM1/report.tex
```

[nix]: https://github.com/DeterminateSystems/nix-installer
[nvim]: https://github.com/kowale/homelab/blob/4ee3ea6dd4c0e8cec11a302044d1b005d0b52aae/pkgs/nvim/lua/plugins.lua#L304-L307
[lean.nvim]: https://github.com/Julian/lean.nvim
[formalising mathematics]: https://github.com/b-mehta/formalising-mathematics-notes

