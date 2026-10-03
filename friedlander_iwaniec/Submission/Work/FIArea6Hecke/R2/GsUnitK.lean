/-
# `Work.FIArea6Hecke.R2.GsUnitK`

The **duality of the conductor Gauss sum at a unit frequency**, without any cardinality
hypothesis on the complete residue system:

  `Gs M chi S a = star (chi a) · Gs M chi S 1`   for `a` a unit modulo `M`,

where `Gs M chi S a = ∑_{s ∈ S} chi s · e^{2πi·Re(s·ā)/N}`, `N = gnorm M`.

This is the classical identity `τ(χ,a) = χ̄(a)·τ(χ,1)` for `a` coprime to the modulus; no
primitivity of `chi` is needed, only that `a` is a unit modulo `M`.  The companion
`Work.FIArea6Hecke.CGD.GsUnit` states the same identity with the extra hypothesis
`S.card = gnorm M`, which its proof never uses; here that hypothesis is dropped.

The proof reindexes the sum over the complete residue system `S` by multiplication with the
inverse `w` of `a` modulo `M` (a unit, hence a bijection on residues), using `CrsCalculus`:

* `ekern M (M · star a) s = ekern M M (s · a)` (`ekern_smul_star_k`), from
  `Re(s·conj(M·star a)) = Re((s·a)·conj M)`;
* `M ∣ z - z' → ekern M M z = ekern M M z'` (`ekern_self_periodic_k`), the periodicity in the
  point of the additive character `ekern M M`;
* `chi w = star (chi a)` (`chi_unit_eq_k`) for `a·w ≡ 1 (mod M)`, from the multiplicativity,
  periodicity and boundedness of `chi` (via `CGD.chi_unit_mul_star`).

The hypothesis `2 ≤ gnorm M` is used only to exclude the degenerate case in which `M` is a unit
(then the inverse `w` of `a` would be `0`, so that `s ↦ s·w` is not injective).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus
import Submission.Work.FIArea6Hecke.CGD.ChiUnits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-! ## The additive character at the shifted frequency -/

/-- `ekern M (M · star a) s = ekern M M (s · a)`: the frequency `M·star a` at the point `s` is the
frequency `M` at the point `s·a`.  (Both exponents are `2πi·Re(s·ā·conj M)/N`.) -/
lemma ekern_smul_star_k (M a s : GaussianInt) :
    ekern M (M * star a) s = ekern M M (s * a) := by
  rw [ekern, ekern, ← gdot_mul_left s a M]

/-- The additive character of frequency `M` is periodic modulo `M` in its point:
`M ∣ z - z' → ekern M M z = ekern M M z'`. -/
lemma ekern_self_periodic_k (M : GaussianInt) (hM : M ≠ 0) {z z' : GaussianInt}
    (h : M ∣ z - z') : ekern M M z = ekern M M z' := by
  have hz : z = z' + (z - z') := by ring
  rw [hz, ekern_add_of_dvd M M z' (z - z') hM dvd_rfl h]

/-! ## The value of the character at the inverse of a unit -/

/-- If `a·w ≡ 1 (mod M)` then `chi w = star (chi a)`, for `chi` a strict character mod `M`. -/
lemma chi_unit_eq_k (M a w : GaussianInt) (chi : GaussianInt → ℂ)
    (hchi : IsCharModStrict M chi) (hw : M ∣ a * w - 1) :
    chi w = star (chi a) := by
  have hchicopy := hchi
  obtain ⟨h1, hmul, _hbound, hper, _hvanish⟩ := hchicopy
  have hcong : M ∣ w * a - 1 := by rwa [mul_comm a w] at hw
  have hwa : chi (w * a) = chi w * chi a := hmul w a
  rw [hper (w * a) 1 hcong, h1] at hwa
  have hprod : chi w * chi a = 1 := hwa.symm
  have ha_unit : IsUnitMod M a := ⟨w, hw⟩
  have hstar : star (chi a) * chi a = 1 := by
    rw [mul_comm]
    exact Work.FIArea6Hecke.CGD.chi_unit_mul_star M chi hchi a ha_unit
  have hane : chi a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact one_ne_zero hprod.symm
  exact mul_right_cancel₀ hane (by rw [hprod, hstar])

/-! ## The duality at a unit frequency -/

theorem GsUnitK (M : GaussianInt) (hM : M ≠ 0) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (S : Finset GaussianInt) (hS : Work.FIArea6Hecke.R.IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi)
    (a : GaussianInt) (ha : Work.FIArea6Hecke.R.IsUnitMod M a) :
    Work.FIArea6Hecke.R.Gs M chi S a =
      star (chi a) * Work.FIArea6Hecke.R.Gs M chi S 1 := by
  obtain ⟨w, hw⟩ := ha
  have hchicopy := hchi
  obtain ⟨_h1, hmul, _hbound, hper, _hvanish⟩ := hchicopy
  have hchw : chi w = star (chi a) := chi_unit_eq_k M a w chi hchi hw
  have hcong : M ∣ w * a - 1 := by rwa [mul_comm a w] at hw
  have hwunit : IsUnitMod M w := ⟨a, hcong⟩
  have hw0 : w ≠ 0 := Work.FIArea6Hecke.CGD.unit_ne_zero_of_IsUnitMod M w hg hwunit
  set f : GaussianInt → ℂ := fun s => chi s * ekern M M (s * a) with hf
  -- `f` is invariant under changes of the representative modulo `M`
  have hfper : ∀ z z' : GaussianInt, M ∣ (z - z') → f z = f z' := by
    intro z z' hzz'
    simp only [hf]
    rw [hper z z' hzz']
    congr 1
    apply ekern_self_periodic_k M hM
    have hsub : z * a - z' * a = (z - z') * a := by ring
    rw [hsub]
    exact dvd_mul_of_dvd_left hzz' a
  -- multiplication by the unit `w` reindexes the complete residue system `S`
  have hT : Work.FIArea6Hecke.R.IsCRS M (S.image (fun s => s * w)) :=
    (Work.FIArea6Hecke.CGD.CrsCalculus M S S hS hS f hfper).2.2.1 w hwunit hw0
  have hAE := Work.FIArea6Hecke.CGD.CrsCalculus M S (S.image (fun s => s * w)) hS hT f hfper
  have hreindex : Finset.sum S f = Finset.sum S (fun s => f (s * w)) := by
    rw [hAE.1, hAE.2.2.2.2 w hw0]
  have hsum : Finset.sum S (fun s => f (s * w)) =
      star (chi a) * Finset.sum S (fun s => chi s * ekern M M s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [hf]
    rw [hmul s w, hchw]
    have hper2 : ekern M M (s * w * a) = ekern M M s := by
      apply ekern_self_periodic_k M hM
      have hsub : s * w * a - s = (w * a - 1) * s := by ring
      rw [hsub]
      exact dvd_mul_of_dvd_left hcong s
    rw [hper2]
    ring
  have hGsA : Work.FIArea6Hecke.R.Gs M chi S a = Finset.sum S f := by
    simp only [Work.FIArea6Hecke.R.Gs, hf]
    apply Finset.sum_congr rfl
    intro s _
    rw [ekern_smul_star_k M a s]
  have hGs1 : Work.FIArea6Hecke.R.Gs M chi S 1 =
      Finset.sum S (fun s => chi s * ekern M M s) := by
    simp only [Work.FIArea6Hecke.R.Gs]
    apply Finset.sum_congr rfl
    intro s _
    simp
  rw [hGsA, hreindex, hsum, ← hGs1]

end

end Work.FIArea6Hecke.R2
