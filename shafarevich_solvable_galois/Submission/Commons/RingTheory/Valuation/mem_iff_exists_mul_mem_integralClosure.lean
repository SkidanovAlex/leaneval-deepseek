import Mathlib.RingTheory.Valuation.LocalSubring
import Submission.Commons.RingTheory.Valuation.exists_integral_denominator_of_mem_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open ValuationSubring

set_option linter.style.haveILetI false

/-- Every valuation subring of a field is integrally closed in it. -/
private lemma isIntegrallyClosedIn_toSubring' {L : Type*} [Field L] (W : ValuationSubring L) :
    IsIntegrallyClosedIn ↥W.toSubring L :=
  Subring.isIntegrallyClosedIn_iff.mpr
    (fun _ hz => LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz)

/-- An element of `L` which is integral over a subring `S ≤ W` lies in `W`. -/
private lemma mem_of_isIntegral_of_le' {L : Type*} [Field L] (S : Subring L)
    (W : ValuationSubring L) (hSW : S ≤ W.toSubring) {b : L} (hb : IsIntegral ↥S b) : b ∈ W := by
  haveI : IsIntegrallyClosedIn ↥W.toSubring L := isIntegrallyClosedIn_toSubring' W
  have hle : (integralClosure ↥S L).toSubring ≤ W.toSubring :=
    (Subring.integralClosure_subring_le_iff (S := S) (T := W.toSubring)).mpr hSW
  exact hle ((mem_integralClosure_iff (R := ↥S) (A := L)).mpr hb)

/-- The image of `O` in `L` is contained in `W` when `W` restricts to `O`. -/
private lemma image_le' {F L : Type*} [Field F] [Field L] [Algebra F L]
    (O : ValuationSubring F) (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = O) :
    Subring.map (algebraMap F L) O.toSubring ≤ W.toSubring := by
  intro z hz
  rw [Subring.mem_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have h1 : y ∈ W.comap (algebraMap F L) := by rw [hW]; exact hy
  rw [ValuationSubring.mem_comap] at h1
  rw [← hyz]
  exact h1

/-- Let `O` be a valuation subring of a field `F`, let `L/F` be a finite extension and let `W` be a
valuation subring of `L` restricting to `O`.  Then an element `x ∈ L` lies in `W` if and only if it
can be written with a denominator which is integral over `O` and a unit of `W`. -/
theorem mem_iff_exists_mul_mem_integralClosure {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) (x : L) :
    x ∈ W ↔ ∃ b : L, IsIntegral (Subring.map (algebraMap F L) O.toSubring) b ∧
      W.valuation b = 1 ∧ IsIntegral (Subring.map (algebraMap F L) O.toSubring) (b * x) := by
  constructor
  · intro hx
    exact exists_integral_denominator_of_mem_valuationSubring O W hW hx
  · rintro ⟨b, hb, hb1, hbx⟩
    have hS := image_le' O W hW
    have hbinv : b⁻¹ ∈ W := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hbxW : b * x ∈ W := mem_of_isIntegral_of_le' _ W hS hbx
    have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb1; exact zero_ne_one hb1
    have hbinv' : b⁻¹ ∈ W.toSubring := (ValuationSubring.mem_toSubring W _).mpr hbinv
    have hbxW' : b * x ∈ W.toSubring := (ValuationSubring.mem_toSubring W _).mpr hbxW
    refine (ValuationSubring.mem_toSubring W x).mp ?_
    have : b⁻¹ * (b * x) = x := by rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
    rw [← this]
    exact W.toSubring.mul_mem hbinv' hbxW'

end Commons.RingTheory.Valuation
