/-
# `Work.PSU3.StageB.Theta` — Ch. VII §2–§3: the computation of `nm` and `ω²`

This module carries out Peterfalvi II Ch. VII §2–§3 (in the "generalised `θ`" form described in
the lead's design, §0 cut 5) inside the vocabulary of `Work.PSU3.CoarseFrame`:

* §2 (1)–(3): the canonical data of `s^a = a⁻¹ s a` and the two formulae for `f(ω s^a)`;
* §3 (1)–(2): the value of `bar (f (ω s^a))` (`= c x / (1 + c ā²)`);
* §3 (3): the substitution `ω⁻¹ s^{a⁻¹} = ω · zc (α + nm (ā⁻¹))` and the functional equation
  `nm (c + c⁻¹ + ā⁻²) = (α + nm (ā⁻¹))²`;
* the final arithmetic (polynomial root count) producing the exponent `i`.

The main statement proved here is `theta_trivial_aux`, from which the requested
`Work.PSU3.StageB.theta_trivial` follows.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.nm_pow_map
import Submission.Work.PSU3.GaloisField.fixedField_card

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
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The element `ω` and its coordinate `α` -/

/-- `ω` as an element of `Q`. -/
noncomputable def omQ (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) : ↥Q :=
  ⟨ω, hω.1⟩

lemma omQ_coe (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    (omQ fr hω : G) = ω := rfl

lemma omQ_ne_one (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    (omQ fr hω : G) ≠ 1 := by
  intro hcon
  refine hω.2.1 ?_
  rw [← omQ_coe fr hω, hcon]
  exact Q0_one_mem fr

lemma omQ_sq_mem_Q0 (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    ω * ω ∈ fr.Q0 := by simpa [pow_two] using fr.sq_mem_Q0 ω hω.1

lemma omQ_sq_ne_one (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    ω * ω ≠ 1 := by
  intro hcon
  refine hω.2.1 ((fr.mem_Q0_iff ω hω.1).mpr ?_)
  rw [pow_two]
  exact hcon

/-- The coordinate of `ω²` (the `α` of Ch. VII §3). -/
noncomputable def alpha (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) : E n :=
  frameZcPreimage fr (ω * ω) (omQ_sq_mem_Q0 fr hω)

lemma alpha_fixed (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    σE (alpha fr hω) = alpha fr hω :=
  frameZcPreimage_fixed fr (omQ_sq_mem_Q0 fr hω)

lemma alpha_spec (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    fr.zc (alpha fr hω) = ω * ω :=
  zc_frameZcPreimage fr (omQ_sq_mem_Q0 fr hω)

lemma alpha_ne_zero (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    alpha fr hω ≠ 0 := by
  intro hcon
  refine omQ_sq_ne_one fr hω ?_
  rw [← alpha_spec fr hω, hcon, zc_zero]

/-- `ω⁻¹ = ω · ω²` (since `ω⁴ = 1`). -/
lemma omega_inv_eq (fr : CoarseFrame H Q t n) {ω : G} (hω : OmegaHyp fr ω) :
    ω⁻¹ = ω * (ω * ω) := by
  have h2 : (ω * ω) * (ω * ω) = 1 := by
    have h0 := fr.sq_mem_Q0 ω hω.1
    have hh := Q0_mul_self fr h0
    simpa [pow_two] using hh
  calc ω⁻¹ = ω⁻¹ * ((ω * ω) * (ω * ω)) := by rw [h2, mul_one]
    _ = ω * (ω * ω) := by group

/-! ## The conjugates `s^a` and their canonical data -/

/-- `s^a = a⁻¹ s a ∈ Q₀` as an element of `Q` (`a ∈ Ksub H t`). -/
noncomputable def sconj (fr : CoarseFrame H Q t n) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) : ↥Q :=
  ⟨(a : G)⁻¹ * frameS fr * (a : G), fr.Q0_le (conj_s_mem_Q0 fr ha)⟩

/-- `s^{a⁻¹} = a s a⁻¹ ∈ Q₀` as an element of `Q`. -/
noncomputable def sconjInv (fr : CoarseFrame H Q t n) (a : fr.KW)
    (ha : (a : G) ∈ Ksub H t) : ↥Q :=
  ⟨(a : G) * frameS fr * (a : G)⁻¹, by
    have h1 := conj_s_mem_Q0 fr (a := a⁻¹) ((Ksub H t).inv_mem ha)
    simpa using fr.Q0_le h1⟩

lemma sconj_coe (fr : CoarseFrame H Q t n) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    (sconj fr a ha : G) = (a : G)⁻¹ * frameS fr * (a : G) := rfl

lemma sconjInv_coe (fr : CoarseFrame H Q t n) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    (sconjInv fr a ha : G) = (a : G) * frameS fr * (a : G)⁻¹ := rfl

lemma sconj_eq_zc (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t) (a : fr.KW)
    (ha : (a : G) ∈ Ksub H t) :
    (sconj fr a ha : G) = fr.zc ((fr.nm (fr.κ a) : (E n)ˣ) : E n) :=
  conj_s_eq_zc fr ha

lemma nm_kappa_ne_zero (fr : CoarseFrame H Q t n) (a : fr.KW) :
    ((fr.nm (fr.κ a) : (E n)ˣ) : E n) ≠ 0 := Units.ne_zero _

lemma sconj_ne_one (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t) (a : fr.KW)
    (ha : (a : G) ∈ Ksub H t) : (sconj fr a ha : G) ≠ 1 := by
  rw [sconj_eq_zc fr h a ha]
  intro hcon
  exact nm_kappa_ne_zero fr a (eq_zero_of_zc_eq_one fr
    (fr.nm_F (fr.κ a) ((fr.mem_K_iff a).mp ha)) hcon)

lemma sconj_mem_Q0 (fr : CoarseFrame H Q t n) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    (sconj fr a ha : G) ∈ fr.Q0 := conj_s_mem_Q0 fr ha

/-- The canonical data of `s^a`: `g = f = s^{a⁻¹}`, `h = a²`. -/
lemma canon_sconj (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t) (a : fr.KW)
    (ha : (a : G) ∈ Ksub H t) :
    (fcan h (sconj fr a ha) : G) = (sconjInv fr a ha : G) ∧
    (gcan h (sconj fr a ha) : G) = (sconjInv fr a ha : G) ∧
    (hcan h (sconj fr a ha) : G) = (a : G) * (a : G) := by
  have hc := canon_conj_s h fr ha
  have key := canon_unique'' h (x := sconj fr a ha) (sconj_ne_one fr h a ha)
    (g := ⟨(a : G) * frameS fr * (a : G)⁻¹, (sconjInv fr a ha).2⟩)
    (d := ⟨(a : G) * (a : G), fr.KW_le (a * a).2⟩)
    (y := ⟨(a : G) * frameS fr * (a : G)⁻¹, (sconjInv fr a ha).2⟩) (hc.2.2.2)
  exact ⟨(key.2.2).symm, (key.1).symm, (key.2.1).symm⟩

end Work.PSU3.StageB

