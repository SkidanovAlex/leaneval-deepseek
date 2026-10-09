import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.NewtonPolygon.exists_coeff_score_eq_of_unique_val
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise
open Polynomial

/-- In a Galois extension `L/K`, every root in `L` of the push-forward `(minpoly K β).map _` of the
minimal polynomial of `β` is a conjugate `σ β` of `β`. -/
lemma exists_algEquiv_eq_of_mem_roots_map_minpoly {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] {β α : L} (hα : α ∈ ((minpoly K β).map (algebraMap K L)).roots) :
    ∃ σ : L ≃ₐ[K] L, σ β = α := by
  classical
  have hne : (minpoly K β).map (algebraMap K L) ≠ 0 :=
    ((minpoly.monic (IsGalois.integral K β)).map (algebraMap K L)).ne_zero
  have haeval : (minpoly K β).aeval α = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact (Polynomial.mem_roots hne).mp hα
  have hmono : minpoly K α = minpoly K β :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (IsGalois.integral K β)) haeval
      (minpoly.monic (IsGalois.integral K β))).symm
  have horbit : α ∈ MulAction.orbit (L ≃ₐ[K] L) β :=
    (Normal.minpoly_eq_iff_mem_orbit L).mp hmono
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp horbit
  exact ⟨σ, hσ⟩

/-- Every conjugate `σ β` of `β` is a root of the push-forward `(minpoly K β).map _`. -/
lemma mem_roots_map_minpoly_of_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (β : L) (σ : L ≃ₐ[K] L) :
    σ β ∈ ((minpoly K β).map (algebraMap K L)).roots := by
  have hne : (minpoly K β).map (algebraMap K L) ≠ 0 :=
    ((minpoly.monic (IsGalois.integral K β)).map (algebraMap K L)).ne_zero
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot]
  have haev : (minpoly K β).aeval (σ β) = 0 := by
    rw [← minpoly.algEquiv_eq σ β]
    exact minpoly.aeval K (σ β)
  rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
  exact haev

/-- **The value of an element whose conjugates have different values lies in the base value group.**
Let `L/K` be a finite Galois extension, `A` a valuation subring of `L`, and `β : L` such that no
*other* conjugate of `β` has the same `A`-value as `β` (`A.valuation (σ β) ≠ A.valuation β`
whenever `σ β ≠ β`).  Then `A.valuation β` is the value of an element of `K`.

Equivalently: under this "isolated value" hypothesis, `A.valuation β ∈ v(K)`.  This is the
Newton-polygon / elementary-symmetric-function step: if `g = minpoly K β` and `g = ∏ (X - αᵢ)`
over the distinct conjugates `αᵢ`, then `g.nextCoeff = -∑ αᵢ ∈ K`, and the Newton polygon of `g`
has a segment of horizontal length `1` at the slope corresponding to `β`, whose slope is a
difference of two coefficient valuations, hence in `v(K)`. -/
theorem exists_val_eq_algebraMap_of_conj_val_ne {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (A : ValuationSubring L) {β : L}
    (hβ : ∀ σ : L ≃ₐ[K] L, σ β ≠ β → A.valuation (σ β) ≠ A.valuation β) :
    ∃ y : K, A.valuation β = A.valuation (algebraMap K L y) := by
  classical
  by_cases hβ0 : β = 0
  · exact ⟨0, by simp [hβ0]⟩
  -- work with the valuation `w` of `A` and the value `γ = w β`
  set w := A.valuation with hw
  set γ := w β with hγdef
  have hγ : γ ≠ 0 := by
    rw [hγdef]
    exact (Valuation.ne_zero_iff w).mpr hβ0
  -- the push-forward of the minimal polynomial of `β`
  set f : Polynomial L := (minpoly K β).map (algebraMap K L) with hfdef
  have hβint : IsIntegral K β := IsGalois.integral K β
  have hfmonic : f.Monic := by
    rw [hfdef]; exact (minpoly.monic hβint).map _
  have hfne : f ≠ 0 := hfmonic.ne_zero
  have hfsplits : f.Splits := by
    rw [hfdef]; exact IsGalois.splits K β
  -- `f` is separable, hence its roots are distinct
  have hnodup : f.roots.Nodup := by
    rw [hfdef]
    exact Polynomial.nodup_roots (Polynomial.Separable.map (IsGalois.separable K β))
  -- exactly one root of `f` has value `γ`
  have hcard : (f.roots.filter (fun C => w C = γ)).card = 1 := by
    have hnd : (f.roots.filter (fun C => w C = γ)).Nodup := hnodup.filter _
    have hβroot : β ∈ f.roots := by
      rw [hfdef]
      exact mem_roots_map_minpoly_of_algEquiv β 1
    have hsingle : (f.roots.filter (fun C => w C = γ)).toFinset = {β} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · rw [Multiset.toFinset_filter, Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hβroot, by rw [hγdef]⟩
      · intro x hx
        rw [Multiset.toFinset_filter, Finset.mem_filter, Multiset.mem_toFinset] at hx
        obtain ⟨hxroot, hxval⟩ := hx
        rw [hfdef] at hxroot
        obtain ⟨σ, hσ⟩ := exists_algEquiv_eq_of_mem_roots_map_minpoly hxroot
        by_contra hxb
        exact (hβ σ (by rw [hσ]; exact hxb)) (by rw [hσ, hxval, hγdef])
    rw [← Multiset.toFinset_card_of_nodup hnd, hsingle, Finset.card_singleton]
  -- Newton polygon: two consecutive `γ`-scores of the coefficients of `f` agree
  obtain ⟨i, -, hci, hci1, heq⟩ :=
    NewtonPolygon.exists_coeff_score_eq_of_unique_val w hfmonic hfsplits hγ hcard
  -- consequently `γ` is a quotient of two values of elements of `K`
  have hkey : w (algebraMap K L ((minpoly K β).coeff i))
      = w (algebraMap K L ((minpoly K β).coeff (i + 1))) * γ := by
    have h2 : w (f.coeff i) * γ ^ i = (w (f.coeff (i + 1)) * γ) * γ ^ i := by
      rw [heq, pow_succ', ← mul_assoc]
    have h3 := mul_right_cancel₀ (pow_ne_zero i hγ) h2
    rwa [hfdef, Polynomial.coeff_map, Polynomial.coeff_map] at h3
  have hW1 : w (algebraMap K L ((minpoly K β).coeff (i + 1))) ≠ 0 := by
    rw [hfdef, Polynomial.coeff_map] at hci1
    exact (Valuation.ne_zero_iff w).mpr hci1
  have hgoal : γ = w (algebraMap K L ((minpoly K β).coeff i))
      * (w (algebraMap K L ((minpoly K β).coeff (i + 1))))⁻¹ := by
    have h1 : γ = (w (algebraMap K L ((minpoly K β).coeff (i + 1))))⁻¹
        * w (algebraMap K L ((minpoly K β).coeff i)) := by
      rw [hkey, inv_mul_cancel_left₀ hW1]
    rw [← mul_comm] at h1
    exact h1
  have hfinal : γ = w (algebraMap K L ((minpoly K β).coeff i / (minpoly K β).coeff (i + 1))) := by
    rw [map_div₀ (algebraMap K L), map_div₀ w, div_eq_mul_inv]
    exact hgoal
  exact ⟨(minpoly K β).coeff i / (minpoly K β).coeff (i + 1), hfinal⟩

end Commons.RingTheory.Valuation