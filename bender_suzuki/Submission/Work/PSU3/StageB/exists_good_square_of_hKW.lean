/-
# `Work.PSU3.StageB.exists_good_square_of_hKW`

This is `Work.PSU3.StageB.Omega.exists_good_square` (Stage B, node B1: Peterfalvi II, Ch. VII
§2) with the source's own structural input written as an explicit hypothesis, namely that the
canonical `h`-component of every element of `Q ∖ Q₀` lies in the frame's `KW`:

  `hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 → (hcan hS.split x : G) ∈ fr.KW`.

Under that hypothesis the Proposition of §2 (p. 274) is exactly
`Omega.square_eq_shift_of_good_cover_hKW` (proved, hole-free), so the assembly of §2 (9)
(`Omega.good_of_orbit`), §2 (19)/(20) (`Omega.alpha_eq_of_two_orbits`) and the Proposition gives
a **good square** `ω * ω = zcQF fr α` with `f (ω) = (ω · zcQF fr α)^ζ`.

The proof below is the proof of `Omega.exists_good_square_of_le` with its frame-level branch
decision `twoPoint H t ≤ fr.KW` replaced by the strictly weaker statement `hKW`; the `hKW` form is
what the callers in the fixed-point-free branch (`Omega.fpf_b1`, whose `FpfFrame.hKW` produces
this hypothesis) actually have available.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.fpf_b1
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

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB.Omega

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `fval` is injective on `F*`. -/
lemma fval_injective_hKW : Function.Injective (fval : ↥(FX n) → E n) := by
  intro u v h
  exact Subtype.ext (Units.ext h)

theorem exists_good_square_of_hKW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfpf : Work.PSU3.DFpfBar H Q t)
    (hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 →
      ((Work.PSU3.StageB.hcan hS.split x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) :
    ∃ ω : ↥Q, ∃ α : ↥(Work.PSU3.StageB.FX n), (ω : G) ∉ fr.Q0 ∧
      Work.PSU3.StageB.fcan hS.split ω =
        Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α) ∧
      ω * ω = Work.PSU3.StageB.zcQF fr α := by
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
  have hαeq' : ∀ O : OrbSet fr, αO O = αO O₀ := fun O => fval_injective_hKW (hαeq O)
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
    (fun O => by rw [← hαeq' O]; exact hαO O) hcover hdis hKW
  exact ⟨g O, αO O₀, hg_ne O, (by rw [← hαeq' O]; exact hαO O), hO⟩

end Work.PSU3.StageB
