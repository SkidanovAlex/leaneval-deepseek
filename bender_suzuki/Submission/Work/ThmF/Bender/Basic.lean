import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bender-group generalities (Peterfalvi I, Ch. I §1–2)

The facts about a strongly embedded `H ≤ G` that Chapter V uses.  Everything here is stated for
a fixed strongly embedded `H` and an involution `t ∉ H` (`D = H ∩ H^t`, `K = J(D,t)`).

Source: Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I pp. 147–152.

The heavier lemmas of Ch. I §2 are delegated in the sibling files
`ThmF/Bender/{twoInvolutionsOdd,existsUniqueConjInvolution,involutionMemConj,cardInvGeTwo,
DTranstiveInv,cardKsetEqInv}.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF

open Submission.Blueprint
open Work.Models

variable {G : Type*} [Group G]

/-! ## §1: an involution lies in a unique conjugate of `H` -/

/-- If an involution `u ∈ H` also lies in a conjugate `H^g`, then `H^g = H`.  (Ch. I §1 (2):
`|H ∩ H^g|` is odd for `g ∉ H`.) -/
theorem conj_eq_self_of_involution_mem {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {u : G} (hu : u ∈ H) (hu2 : orderOf u = 2) {g : G} (hgu : u ∈ conj g H) :
    conj g H = H := by
  have hgH : g ∈ H := by
    by_contra hg
    have hmem : u ∈ twoPoint H g := ⟨hu, hgu⟩
    have hdvd : orderOf u ∣ Nat.card (twoPoint H g) := Subgroup.orderOf_dvd_natCard _ hmem
    have heven : Even (Nat.card (twoPoint H g)) :=
      even_iff_two_dvd.mpr (hu2 ▸ hdvd)
    exact Nat.not_even_iff_odd.mpr (hH.2.2 g hg) heven
  exact Work.Models.conj_self_of_mem_normalizer (H.le_normalizer hgH)

/-- Ch. I §1 (2): the centraliser of an involution of `H` is contained in `H`. -/
theorem centralizer_involution_le {H : Subgroup G} (hH : IsStronglyEmbedded H) {u : G}
    (hu : u ∈ H) (hu2 : orderOf u = 2) : Subgroup.centralizer ({u} : Set G) ≤ H := by
  intro x hx
  have hux : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hx) u (by simp)
  have hxu : x * u * x⁻¹ = u := by rw [← hux]; group
  have hxu' : x⁻¹ * u * x = u := by
    have := congrArg (fun z => x⁻¹ * z) hux
    simpa [mul_assoc] using this
  have hmem : u ∈ conj x H := by
    rw [Work.Models.mem_conj_iff]
    show x⁻¹ * u * x ∈ H
    rw [hxu']
    exact hu
  have h1 : x ∈ Subgroup.normalizer (H : Set G) :=
    Work.Models.mem_normalizer_of_conj_eq (conj_eq_self_of_involution_mem hH hu hu2 hmem)
  rwa [Work.Models.IsStronglyEmbedded.normalizer_eq hH] at h1

/-- `H^g = H ↔ g ∈ H` (self-normalising, `Work.Models.IsStronglyEmbedded.normalizer_eq`). -/
theorem conj_eq_iff_mem {H : Subgroup G} (hH : IsStronglyEmbedded H) (g : G) :
    conj g H = H ↔ g ∈ H := by
  constructor
  · intro h
    have h1 : g ∈ Subgroup.normalizer (H : Set G) := Work.Models.mem_normalizer_of_conj_eq h
    rwa [Work.Models.IsStronglyEmbedded.normalizer_eq hH] at h1
  · intro hg
    exact Work.Models.conj_self_of_mem_normalizer (H.le_normalizer hg)

/-- If `t ∈ H^g ∩ H^{g'}` with `t` an involution, then `H^g = H^{g'}` (Ch. I §2 Prop. 1 (c),
uniqueness half). -/
theorem conj_eq_conj_of_mem {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht2 : orderOf t = 2) {x y : G} (hx : t ∈ conj x H) (hy : t ∈ conj y H) :
    conj x H = conj y H := by
  have hA : IsStronglyEmbedded (conj y H) := Work.Models.IsStronglyEmbedded.conj hH y
  have hty : t ∈ conj (x * y⁻¹) (conj y H) := by
    rw [Work.Models.conj_mul, Work.Models.conj_inv_conj]
    exact hx
  have h := conj_eq_self_of_involution_mem hA hy ht2 hty
  rw [Work.Models.conj_mul, Work.Models.conj_inv_conj] at h
  exact h

end Work.ThmF
