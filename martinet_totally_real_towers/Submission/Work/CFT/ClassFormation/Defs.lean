import Mathlib
import Submission.Work.Tower.Shafarevich.Defs

/-!
# The Schur bridge and class formations: vocabulary

This file fixes the vocabulary for the area `Work.CFT.ClassFormation`, the homological-algebra
input to Shafarevich's relation-rank estimate (see `Submission/Work/CFT/README.md`, "route 2").

## The two invariants

For a finite group `G` and a prime `p`, Shafarevich's estimate compares

* `dim_{𝔽_p} H¹(G, 𝔽_p)`, the *generator rank* `d(G)`, and
* `dim_{𝔽_p} H²(G, 𝔽_p)`, the *relation rank* `r(G)`,

with the *Schur multiplier* `H_2(G, ℤ)`.  The two cohomology groups with trivial `𝔽_p`
coefficients are already named in `Work.Tower.Shafarevich`
(`H1Fp`, `H2Fp`, `proPRelationRank`, `proPGeneratorRank`); this file adds:

* `HnFp p G n` — `H^n(G, 𝔽_p)` with trivial coefficients (general degree, agrees definitionally
  with `H1Fp`/`H2Fp` in degrees `1`/`2`);
* `HnHomFp p G n` — `H_n(G, 𝔽_p)` with trivial coefficients (group *homology*);
* `HnZ G n` — `H_n(G, ℤ)` with trivial integral coefficients (an abelian group);
* `rankP p A` — `dim_{𝔽_p} (A ⊗_ℤ 𝔽_p)`, the `p`-rank of an abelian group `A`.

The **Schur bridge** (the main result of the sub-area `Work.CFT.ClassFormation.Schur`) is then

`dim_{𝔽_p} H²(G, 𝔽_p) = dim_{𝔽_p} H¹(G, 𝔽_p) + rankP p (H_2(G, ℤ))`,

equivalently `≤`.  It is obtained from three ingredients:

1. `dim_{𝔽_p} H^n(G, 𝔽_p) = dim_{𝔽_p} H_n(G, 𝔽_p)` (*field duality*);
2. the homology Bockstein sequence of `0 → ℤ --p--> ℤ → 𝔽_p → 0`,
   `dim_{𝔽_p} H_n(G, 𝔽_p) = rankP p (H_n(G, ℤ)) + rankP p (H_{n-1}(G, ℤ))` for `n ≥ 2`;
3. `dim_{𝔽_p} H¹(G, 𝔽_p) = rankP p (H_1(G, ℤ))`.

## Conventions

* `rankP` is written with the coefficient `𝔽_p` on the *left*, `ZMod p ⊗[ℤ] A`, because that is
  the side carrying the canonical `Module (ZMod p)` structure (`TensorProduct.leftModule`); it
  agrees with `A ⊗[ℤ] ZMod p` up to `TensorProduct.comm`.
* All groups are finite (`Fintype G`) unless stated otherwise, and all `𝔽_p`-vector spaces are
  finite-dimensional in the applications.
-/

open scoped TensorProduct

namespace Work.CFT.ClassFormation

/-- `H_n(G, ℤ)`, the `n`-th group homology of `G` with trivial integral coefficients,
presented as an abelian group (a `ℤ`-module). -/
noncomputable abbrev HnZ (G : Type) [Group G] (n : ℕ) : ModuleCat ℤ :=
  groupHomology (Rep.trivial ℤ G ℤ) n

/-- `H_n(G, 𝔽_p)`, the `n`-th group homology of `G` with trivial `𝔽_p` coefficients. -/
noncomputable abbrev HnHomFp (p : ℕ) (G : Type) [Group G] (n : ℕ) : ModuleCat (ZMod p) :=
  groupHomology (Rep.trivial (ZMod p) G (ZMod p)) n

/-- `H^n(G, 𝔽_p)`, the `n`-th group cohomology of `G` with trivial `𝔽_p` coefficients.
In degrees `1` and `2` this is definitionally `Work.Tower.Shafarevich.H1Fp` and `H2Fp`. -/
noncomputable abbrev HnFp (p : ℕ) (G : Type) [Group G] (n : ℕ) : ModuleCat (ZMod p) :=
  groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) n

/-- The `p`-rank of an abelian group `A`: `dim_{𝔽_p} (A ⊗_ℤ 𝔽_p)`.  Written with the coefficient
on the left; see the module docstring. -/
noncomputable def rankP (p : ℕ) (A : Type) [AddCommGroup A] : ℕ :=
  Module.finrank (ZMod p) (ZMod p ⊗[ℤ] A)

/-- The `𝔽_p`-dimension of `H^n(G, 𝔽_p)` (trivial coefficients). -/
noncomputable abbrev dimHnFp (p : ℕ) (G : Type) [Group G] (n : ℕ) : ℕ :=
  Module.finrank (ZMod p) (HnFp p G n)

end Work.CFT.ClassFormation
