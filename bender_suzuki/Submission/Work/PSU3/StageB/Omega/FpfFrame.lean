/-
# `Work.PSU3.StageB.Omega.FpfFrame` — the frame-level decision of `STATUS_B1.md` §3, written down

**The decision.**  In the fixed-point-free branch (`DFpfBar H Q t`), Peterfalvi's Proposition
(p. 274) uses that the frame's `KW` is *all* of `D = twoPoint H t`, i.e. that `ζ` generates the
ambient `W = C_V(J(D,t))`; in the model this is exactly the fpf case, where
`|D| = |KW| = q² - 1`.  With it:

* `h (x) ∈ fr.KW` for every `x ∈ Q` (the glue of `Omega/hcan_mem_KW_of_le.lean`) — this is the
  single hypothesis `hKW` that the reviewed conditional lemma
  `Omega.square_eq_shift_of_good_cover_hKW` needs, and the input the source's proof takes from
  §2 (18) + "the Sylow subgroups of `D` are cyclic" + `W ⊴ D`;
* the index `k` of that argument cannot be the self-index in the way that breaks the chain
  (`STATUS_B1.md` §8), because the model of `D = KW = E*` is the one in which the strict shift
  relation of §2 (20) applies to every pair of distinct `KW`-orbits;
* `Omega/exists_good_square.lean` then closes node B1 (`exists_omega_of_fpf`) in a single
  application of the conditional lemma.

**Why this is *not* a new field of `CoarseFrame`.**  `CoarseFrame` (`Submission/Work/PSU3/Defs.lean`)
is the shared interface of the whole area, and Stage A *constructs* frames in the
**non**-fixed-point-free branch too (`Work.PSU3.StageA.coarseFrame_exists`: "for every
`ζ ∈ W#` there is a coarse frame with that `ζ`"), where `ζ` need not generate `W`, so
`D ≤ KW` is *false* (and so is `orderOf fr.ζ = |W H t|`).  Adding `twoPoint H t ≤ KW` as a field
would therefore make those frame constructions (A6, and the frames consumed by B2
`exists_omega_of_not_fpf`) unprovable.  The hypothesis belongs to the **fpf branch**, which is
exactly how it is recorded here: a *bundle* of a frame with the branch condition, usable by any
consumer of B1 that has already decided which branch it is in.

**Closure once the conditional lemma lands** (this is the whole remaining chain, nothing else):

  `FpfFrame.hKW`  →  `Omega.square_eq_shift_of_good_cover_hKW`  →  `Omega.good_of_orbit` +
  `Omega.alpha_eq_of_two_orbits` + orbit bookkeeping (all in
  `Omega/exists_good_square.lean`)  →  `Omega.omegaHyp_of_good`   ⟹   `∃ ω, OmegaHyp fr ω`.

Only `Omega/square_eq_shift_of_good_cover_hKW` is still missing; every other link above is
hole-free in this directory.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.hcan_mem_KW_of_le
import Submission.Work.PSU3.StageB.Canon

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- A coarse frame **in the fixed-point-free branch**, with the branch decision `D = KW` of
`STATUS_B1.md` §3: `KW` is all of `D = twoPoint H t`, i.e. `ζ` generates `W = C_V(K)`.
(Kept as a bundle rather than a field of `CoarseFrame`, see the module docstring.) -/
structure FpfFrame (G : Type) [Group G] (H Q : Subgroup G) (t : G) (n : ℕ) where
  /-- the coarse frame -/
  fr : CoarseFrame H Q t n
  /-- the branch condition: every element of `D` lies in `KW` -/
  KW_eq_twoPoint : twoPoint H t ≤ fr.KW

/-- **The `hKW` input of the source's Proposition**, now immediate: every `h`-component lies in
`fr.KW`.  This is exactly the hypothesis of `Omega.square_eq_shift_of_good_cover_hKW`. -/
theorem FpfFrame.hKW (hS : PSU3Hyp H Q t) (F : FpfFrame G H Q t n) :
    ∀ x : ↥Q, (x : G) ∉ F.fr.Q0 →
      ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ F.fr.KW :=
  hKW_of_twoPoint_le_KW hS F.fr F.KW_eq_twoPoint

/-- `h (x) ∈ fr.KW` with no `Q₀`-side condition (the form used by `H4` manipulations). -/
theorem FpfFrame.hcan_mem_KW (hS : PSU3Hyp H Q t) (F : FpfFrame G H Q t n) (x : ↥Q) :
    ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ F.fr.KW :=
  hcan_mem_KW_of_twoPoint_le_KW hS F.fr F.KW_eq_twoPoint x

/-- The basic step of the chain of §2 Prop: a `KW`-conjugate of `x` lies in the `KW`-orbit of
`x`.  (Used with `d = h(x)⁻¹`: `h (x) · x · h (x)⁻¹ ∈ orbKW x` once `h (x) ∈ fr.KW`.) -/
theorem mem_orbKW_kact (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : ↥Q) :
    kact hS fr d x ∈ orbKW hS fr x :=
  ⟨d, 1, Q0_one_mem fr, by rw [mul_one]⟩

/-- `h (x)⁻¹` as an element of `fr.KW` (fpf branch), the conjugator of the `(f∘j)³` chain. -/
noncomputable def FpfFrame.hinvKW (hS : PSU3Hyp H Q t) (F : FpfFrame G H Q t n) (x : ↥Q) :
    F.fr.KW :=
  ⟨((hcan hS.split x : ↥(twoPoint H t))⁻¹ : ↥(twoPoint H t)).1,
    by simpa using F.fr.KW.inv_mem (F.hcan_mem_KW hS x)⟩

/-- `h (x) · x · h (x)⁻¹ ∈ orbKW x` for every `x ∈ Q`, in the fpf branch (where `h (x) ∈ fr.KW`). -/
theorem FpfFrame.hcan_conj_mem_orbKW (hS : PSU3Hyp H Q t) (F : FpfFrame G H Q t n) (x : ↥Q) :
    kact hS F.fr (F.hinvKW hS x) x ∈ orbKW hS F.fr x :=
  mem_orbKW_kact hS F.fr _ x

end Work.PSU3.StageB.Omega
