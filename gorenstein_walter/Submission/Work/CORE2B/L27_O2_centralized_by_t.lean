import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27_two_part
import Submission.Work.CORE2B.L27cf_twoResidual
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic

/-!
# CORE2B — `O₂(M)` is centralized by `t` (Bender 1981, Lemma 2.7, step 1)

Under `L27Hyp B M`, Bender's Lemma 2.7 asserts (among other things) that the involution `t`
centralizes `O₂(M)`.  This file proves exactly that, as `Work.CORE2B.L27_O2_centralized_by_t`:

```
Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G).
```

The route is the "`t` is 2-central in `M`" argument, which is the shape the workspace's
`L27Hyp.size` was designed for.  A normal `2`-subgroup of `M` is contained in every Sylow
`2`-subgroup of `M` (`L27two.pCoreIn_two_le_centralizer_of_sylow`), so it suffices to produce a
Sylow `2`-subgroup `P` of `M` with `P ≤ C_G(t)`; the disjunction `L27Hyp.size` supplies one in
each of its three alternatives:

* `8 ≤ |S ⊓ M|` — Bender's "large intersection" case: `L27two.sylow_central_of_large_inter`
  (from `CORE2B.sylow_central_of_large_inter`).  The centralizer of a non-central involution of
  the dihedral Sylow `S` is a four-group, so `S ⊓ M ∋ t` of order `≥ 8` is already abelian;
* `|S| = 4` — then every `2`-subgroup of `G` has order `≤ 4`, hence is commutative
  (`L27two.sylow_central_of_card_four`);
* `t ∈ O²(M)` — the transfer case, `CORE2B.L27cf_twoResidual` (Thompson's transfer lemma
  applied to the reflection sign of a dihedral Sylow of `M`), which is where the residual
  hypothesis is actually used.

`t`'s centrality in the Sylow `S` of `G` is `CORE2B.t_central_in_S`, and the fact that the Sylow
`2`-subgroups of the minimal counterexample are cyclic-or-dihedral (here: not cyclic, hence
dihedral) is `BenderCtx.sylow` + `CORE2B.BenderCtx_sylow_not_cyclic`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- **Bender 1981, Lemma 2.7, step 1**: the involution `t` centralizes `O₂(M)`.

This is the statement `pCoreIn 2 M ≤ C_G(t)` under `L27Hyp B M`.  Note that `pCoreIn 2 M` is the
`2`-part of the Fitting subgroup only up to its defining universal property here: the proof uses
no identification of `O₂(M)` with `F₂(M)`, but produces the required Sylow `2`-subgroup of `M`
directly from the three alternatives of `L27Hyp.size`. -/
theorem L27_O2_centralized_by_t :
    ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G) := by
  intro T h23 h26 G _ _ hFT hCtx B M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the Sylow `2`-subgroups of `G` are dihedral (not cyclic, by simplicity of `G`)
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hS⟩ : ∃ n : ℕ, Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · exact h
  -- `t` is central in the Sylow `S` of `G`
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  -- a normal `2`-subgroup of `M` lies in every Sylow `2`-subgroup of `M`
  have key : ∀ P : Sylow 2 M, (∀ x ∈ (P : Subgroup M), (x : G) * B.t = B.t * (x : G)) →
      Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fun P hP => L27two.pCoreIn_two_le_centralizer_of_sylow M B.t P hP
  rcases hM.size with h8 | h4 | hres
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_large_inter B.S n hS B.t B.t_order htc M hM.t_mem
      hM.sylow_nc h8
    exact key P hP
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_card_four B.S B.t B.t_order h4 M hM.t_mem
      hM.sylow_nc
    exact key P hP
  · obtain ⟨P, hP⟩ := L27cf_twoResidual B.S n hS B.t B.t_order htc M hM.t_mem hM.sylow_nc hres
    exact key P hP

end Work.CORE2B
