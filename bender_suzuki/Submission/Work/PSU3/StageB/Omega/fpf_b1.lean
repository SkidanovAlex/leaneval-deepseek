/-
# `Work.PSU3.StageB.Omega.fpf_b1` — **node B1 in the fixed-point-free branch, closed**

This is `Omega/exists_good_square.lean` with the frame-level decision of `STATUS_B1.md` §3
supplied as a hypothesis (`twoPoint H t ≤ fr.KW`, bundled as `Omega.FpfFrame`), so that the
*reviewed and now proved* conditional lemma `Omega.square_eq_shift_of_good_cover_hKW` applies.
Nothing here is conditional on any `hole`: the whole chain

  `FpfFrame`  →  `Omega.good_of_orbit` (§2 (9))  →  common `α` (`alpha_eq_of_two_orbits`, §2 (19)/(20))
  →  `square_eq_shift_of_good_cover_hKW` (the Prop, using `hKW` from `twoPoint H t ≤ KW`)
  →  `Omega.omegaHyp_of_good` (H5 + `DFpfBar`: `h(ω) = ζ³ ∈ W`)
  ⟹  `∃ ω, OmegaHyp fr ω`

is hole-free.

The unconditional node `Work.PSU3.StageB.exists_omega_of_fpf` (`fr : CoarseFrame`, no hypothesis
on `D` vs `KW`) is **not** obtainable this way: for a non-generating `ζ` the frame does not
determine `D = KW`, and the self-case shift relation fails (§8).  The frame decision therefore
has to be taken at the level of the interface, which is what `FpfFrame` records.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.alpha_eq_of_two_orbits
import Submission.Work.PSU3.StageB.Omega.good_of_orbit
import Submission.Work.PSU3.StageB.Omega.FpfFrame
import Submission.Work.PSU3.StageB.Omega.square_eq_shift_of_good_cover_hKW
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_good

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `fval` is injective on `F*`. -/
lemma fval_injective : Function.Injective (fval : ↥(FX n) → E n) := by
  intro u v h
  exact Subtype.ext (Units.ext h)

/-! ## Stage B / B1 -/

theorem exists_good_square_of_le (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hDK : twoPoint H t ≤ fr.KW) (hfpf : DFpfBar H Q t) :
    ∃ ω : ↥Q, ∃ α : ↥(FX n), (ω : G) ∉ fr.Q0 ∧
      fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α) ∧
      ω * ω = zcQF fr α := by
  classical
  haveI : Finite (OrbSet fr) := inferInstance
  -- ## orbit representatives in `Q`
  let ωO : OrbSet fr → ↥Q := fun O => Classical.choose (orbSet_exists_rep fr O)
  have hωO_ne : ∀ O : OrbSet fr, (ωO O : G) ∉ fr.Q0 :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).1
  have hωO_orb : ∀ O : OrbSet fr,
      (O : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).2
  -- ## the good element of each orbit
  let g : OrbSet fr → ↥Q := fun O => Classical.choose (good_of_orbit hS fr (hωO_ne O))
  have hg : ∀ O : OrbSet fr, g O ∈ orbKW hS fr (ωO O) ∧ ((g O : G) ∉ fr.Q0) ∧
      (∃ α : ↥(FX n), fcan hS.split (g O) =
        qconj hS.split (zetaD fr) (g O * zcQF fr α)) :=
    fun O => Classical.choose_spec (good_of_orbit hS fr (hωO_ne O))
  have hg_ne : ∀ O : OrbSet fr, (g O : G) ∉ fr.Q0 := fun O => (hg O).2.1
  -- ## the good elements lie in their orbit's class
  have hbar_inE : ∀ O : OrbSet fr,
      Multiplicative.toAdd (fr.bar (g O)) ∈ orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) := by
    intro O
    have hmem : g O ∈ orbKW hS fr (ωO O) := (hg O).1
    rwa [mem_orbKW_iff_orbE] at hmem
  have hbar_in : ∀ O : OrbSet fr, Multiplicative.toAdd (fr.bar (g O)) ∈ (O : Set (E n)) := by
    intro O
    rw [hωO_orb O]
    exact hbar_inE O
  have hbar_orb : ∀ O : OrbSet fr,
      orbE fr (Multiplicative.toAdd (fr.bar (g O))) = (O : Set (E n)) := by
    intro O
    rw [orbE_eq_of_mem fr (hbar_inE O), hωO_orb O]
  have hdis : ∀ O₁ O₂ : OrbSet fr, O₁ ≠ O₂ →
      Multiplicative.toAdd (fr.bar (g O₁)) ∉ orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := by
    intro O₁ O₂ hne hmem
    have h1 : orbE fr (Multiplicative.toAdd (fr.bar (g O₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := orbE_eq_of_mem fr hmem
    rw [hbar_orb O₁, hbar_orb O₂] at h1
    exact hne (Subtype.ext h1)
  -- ## common coordinate `α` for all the representatives (Peterfalvi (19)/(20))
  have hgood_ex : ∀ O : OrbSet fr, ∃ α : ↥(FX n), fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr α) := fun O => (hg O).2.2
  let αO : OrbSet fr → ↥(FX n) := fun O => Classical.choose (hgood_ex O)
  have hαO : ∀ O : OrbSet fr, fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr (αO O)) :=
    fun O => Classical.choose_spec (hgood_ex O)
  let O₀ : OrbSet fr := ⟨orbE fr 1, ⟨1, one_ne_zero, rfl⟩⟩
  have hαeq : ∀ O : OrbSet fr, fval (αO O) = fval (αO O₀) := by
    intro O
    by_cases h : O = O₀
    · rw [h]
    · exact alpha_eq_of_two_orbits hS fr (hg_ne O) (hg_ne O₀) (hαO O) (hαO O₀) (hdis O O₀ h)
  have hαeq' : ∀ O : OrbSet fr, αO O = αO O₀ := fun O => fval_injective (hαeq O)
  -- ## the covering hypothesis
  have hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ O : OrbSet fr, y ∈ orbKW hS fr (g O) := by
    intro y hy
    refine ⟨⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
      ⟨Multiplicative.toAdd (fr.bar y), toAdd_bar_ne_zero fr hy, rfl⟩⟩, ?_⟩
    have hOe : ((⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
        ⟨Multiplicative.toAdd (fr.bar y), toAdd_bar_ne_zero fr hy, rfl⟩⟩ : OrbSet fr) : Set (E n))
        = orbE fr (Multiplicative.toAdd (fr.bar y)) := rfl
    rw [mem_orbKW_iff_orbE, hbar_orb _, hOe]
    exact orbE_refl fr _
  -- ## the Proposition (p. 274)
  obtain ⟨O, hO⟩ := square_eq_shift_of_good_cover_hKW hS fr hfpf g (α := αO O₀) hg_ne
    (fun O => by rw [← hαeq' O]; exact hαO O) hcover hdis
    (hKW_of_twoPoint_le_KW hS fr hDK)
  exact ⟨g O, αO O₀, hg_ne O, (by rw [← hαeq' O]; exact hαO O), hO⟩

/-- **Stage B, node B1** (`exists_omega_of_fpf`): a frame with `DFpfBar` has an `OmegaHyp`
element. -/
theorem exists_omega_of_fpf_of_D_eq_KW (hS : PSU3Hyp H Q t) {n : ℕ} (F : FpfFrame G H Q t n)
    (hfpf : DFpfBar H Q t) : ∃ ω : G, OmegaHyp F.fr ω := by
  obtain ⟨ω, α, hω0, hf, hsq⟩ := exists_good_square_of_le hS F.fr F.KW_eq_twoPoint hfpf
  exact ⟨(ω : G), omegaHyp_of_good hS F.fr hfpf hω0 hf hsq⟩

end Work.PSU3.StageB.Omega
