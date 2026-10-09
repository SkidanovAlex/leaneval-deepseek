import Mathlib
import Submission.Commons.RingTheory.Valuation.mem_iff_exists_mul_mem_integralClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open ValuationSubring

set_option linter.style.haveILetI false

/-- The image `S` of the common centre `P.comap (algebraMap F L) = Q.comap (algebraMap F L)` inside `L`
is contained in `Q`. -/
private lemma map_comap_le_of_comap_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P Q : ValuationSubring L) (hC : P.comap (algebraMap F L) = Q.comap (algebraMap F L)) :
    Subring.map (algebraMap F L) (P.comap (algebraMap F L)).toSubring ≤ Q.toSubring := by
  intro z hz
  rw [Subring.mem_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  rw [← hyz]
  rw [ValuationSubring.mem_toSubring] at hy
  rw [hC, ValuationSubring.mem_comap] at hy
  exact hy

/-- The image `S` of the common centre is contained in `P`. -/
private lemma map_comap_le_self {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : ValuationSubring L) :
    Subring.map (algebraMap F L) (P.comap (algebraMap F L)).toSubring ≤ P.toSubring := by
  intro z hz
  rw [Subring.mem_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  rw [← hyz]
  rw [ValuationSubring.mem_toSubring, ValuationSubring.mem_comap] at hy
  exact hy

/-- Every valuation subring of a field is integrally closed in it. -/
private lemma isIntegrallyClosedIn_toSubring {L : Type*} [Field L] (W : ValuationSubring L) :
    IsIntegrallyClosedIn ↥W.toSubring L :=
  Subring.isIntegrallyClosedIn_iff.mpr
    (fun _ hz => LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz)

/-- If `b` is integral over a subring `S ⊆ W` of `L` and `W` is a valuation subring of `L`, then
`b ∈ W`. -/
private lemma mem_of_isIntegral_of_le {L : Type*} [Field L] (S : Subring L)
    (W : ValuationSubring L) (hSW : S ≤ W.toSubring) {b : L} (hb : IsIntegral ↥S b) : b ∈ W := by
  haveI : IsIntegrallyClosedIn ↥W.toSubring L := isIntegrallyClosedIn_toSubring W
  have hle : (integralClosure ↥S L).toSubring ≤ W.toSubring :=
    (Subring.integralClosure_subring_le_iff (S := S) (T := W.toSubring)).mpr hSW
  have hb' : b ∈ (integralClosure ↥S L).toSubring := by
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := integralClosure ↥S L) (R := ↥S) (B := L)).mp hb
    rw [← hy]; exact y.2
  exact hle hb'

/-- **Two extensions of a valuation agreeing on the integral closure of the common centre are equal.**

Let `F ⊆ L` be a finite extension of fields and let `P, Q` be valuation subrings of `L` with the same
restriction `O` to `F`.  If `P` and `Q` define the same subsets of `L` on the elements integral over
the image of `O` (i.e. they have the same intersetion with the integral closure `B` of `O` in `L`),
then `P = Q`.

Indeed, a valuation subring of `L` restricting to `O` is exactly the localisation of `B` at the prime
`m ∩ B` (the "localisation theorem" for the extensions of a valuation to a finite extension); hence
`P` and `Q` are determined by their intersections with `B`, which agree by hypothesis. -/
theorem eq_of_comap_eq_of_center_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (P Q : ValuationSubring L)
    (hC : P.comap (algebraMap F L) = Q.comap (algebraMap F L))
    (h : ∀ x : L, IsIntegral (Subring.map (algebraMap F L) (P.comap (algebraMap F L)).toSubring) x →
        (P.valuation x < 1 ↔ Q.valuation x < 1)) : P = Q := by
  apply ValuationSubring.ext
  intro x
  have hP := mem_iff_exists_mul_mem_integralClosure (P.comap (algebraMap F L)) P rfl x
  have hQ := mem_iff_exists_mul_mem_integralClosure (P.comap (algebraMap F L)) Q (by rw [hC]) x
  rw [hP, hQ]
  constructor
  · rintro ⟨b, hb, hb1, hbx⟩
    refine ⟨b, hb, ?_, hbx⟩
    have hbQ : b ∈ Q :=
      mem_of_isIntegral_of_le _ Q (map_comap_le_of_comap_eq P Q hC) hb
    have hge : 1 ≤ Q.valuation b := by
      rw [← not_lt]
      intro hlt
      exact absurd (h b hb |>.mpr hlt) (by rw [hb1]; exact lt_irrefl 1)
    exact le_antisymm ((ValuationSubring.valuation_le_one_iff Q b).mpr hbQ) hge
  · rintro ⟨b, hb, hb1, hbx⟩
    refine ⟨b, hb, ?_, hbx⟩
    have hbP : b ∈ P :=
      mem_of_isIntegral_of_le _ P (map_comap_le_self P) hb
    have hge : 1 ≤ P.valuation b := by
      rw [← not_lt]
      intro hlt
      exact absurd (h b hb |>.mp hlt) (by rw [hb1]; exact lt_irrefl 1)
    exact le_antisymm ((ValuationSubring.valuation_le_one_iff P b).mpr hbP) hge

end Commons.RingTheory.Valuation
