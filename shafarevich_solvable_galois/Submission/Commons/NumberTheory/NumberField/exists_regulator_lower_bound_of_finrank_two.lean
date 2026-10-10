import Mathlib.RingTheory.Henselian
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Submission.Commons.NumberTheory.NumberField.regulator_eq_one_of_rank_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField
open Module

namespace Commons.NumberTheory.NumberField

/-- The norm of a unit of the ring of integers of a number field is `±1`. -/
lemma norm_unit_eq_one_or_neg_one (K : Type*) [Field K] [NumberField K] (u : (𝓞 K)ˣ) :
    Algebra.norm ℚ ((u : (𝓞 K)ˣ) : K) = 1 ∨ Algebra.norm ℚ ((u : (𝓞 K)ˣ) : K) = -1 := by
  set a : ℤ := Algebra.norm ℤ ((u : (𝓞 K)ˣ) : 𝓞 K) with ha
  have hab : a * Algebra.norm ℤ (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
    rw [ha, ← map_mul]
    simp
  have h1 : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hab
  have hco := Algebra.coe_norm_int ((u : (𝓞 K)ˣ) : 𝓞 K)
  rw [← ha] at hco
  rcases h1 with h | h
  · left; rw [← hco, h]; norm_num
  · right; rw [← hco, h]; norm_num

/-- The infinite part of the product formula for a unit: the product of the normalized absolute
values of a unit over all infinite places is `1`. -/
lemma prod_apply_unit_eq_one (K : Type*) [Field K] [NumberField K] (u : (𝓞 K)ˣ) :
    ∏ w : InfinitePlace K, (w ((u : (𝓞 K)ˣ) : K)) ^ (w.mult) = 1 := by
  rw [InfinitePlace.prod_eq_abs_norm]
  rcases norm_unit_eq_one_or_neg_one K u with h | h <;> rw [h] <;> norm_num

/-- The units of a fundamental system are not torsion units. -/
lemma fundSystem_notMem_torsion (K : Type*) [Field K] [NumberField K]
    (i : Fin (Units.rank K)) : Units.fundSystem K i ∉ Units.torsion K := by
  intro h
  have h1 := dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr h
  rw [Units.logEmbedding_fundSystem] at h1
  exact (Basis.ne_zero (Units.basisUnitLattice K) i) (Subtype.ext h1)

/-- A quadratic number field has unit rank `0` or `1`. -/
lemma rank_eq_zero_or_one_of_finrank_eq_two (K : Type*) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) : Units.rank K = 0 ∨ Units.rank K = 1 := by
  have ha : InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K = 2 := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  rcases Nat.eq_zero_or_pos (InfinitePlace.nrComplexPlaces K) with hb | hb
  · right
    have ha2 : InfinitePlace.nrRealPlaces K = 2 := by omega
    have hcard : Fintype.card (InfinitePlace K) = 2 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K, ha2, hb]
    rw [Units.rank, hcard]
  · left
    have hb1 : InfinitePlace.nrComplexPlaces K = 1 := by omega
    have ha0 : InfinitePlace.nrRealPlaces K = 0 := by omega
    have hcard : Fintype.card (InfinitePlace K) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K, ha0, hb1]
    rw [Units.rank, hcard]

/-- If the unit rank is `1`, the number field has exactly two infinite places. -/
lemma card_infinitePlace_eq_two_of_rank_eq_one (K : Type*) [Field K] [NumberField K]
    (h : Units.rank K = 1) : Fintype.card (InfinitePlace K) = 2 := by
  rw [Units.rank] at h
  omega

/-- A quadratic number field of unit rank `1` is totally real. -/
lemma nrComplexPlaces_eq_zero_of_rank_eq_one (K : Type*) [Field K] [NumberField K]
    (h : Units.rank K = 1) (hf : Module.finrank ℚ K = 2) :
    InfinitePlace.nrComplexPlaces K = 0 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [Units.rank] at h
  omega

/-- If a number field has no complex infinite place, every infinite place is real. -/
lemma isReal_of_nrComplexPlaces_eq_zero (K : Type*) [Field K] [NumberField K]
    (h : InfinitePlace.nrComplexPlaces K = 0) (w : InfinitePlace K) : w.IsReal := by
  classical
  rcases InfinitePlace.isReal_or_isComplex w with hr | hc
  · exact hr
  · exfalso
    have : 0 < InfinitePlace.nrComplexPlaces K := Fintype.card_pos_iff.mpr ⟨⟨w, hc⟩⟩
    omega

/-- In unit rank `1`, the regulator is the absolute value of the (single) component of the
logarithmic embedding of a fundamental unit. -/
lemma regulator_eq_abs_logEmbedding_of_rank_eq_one (K : Type*) [Field K] [NumberField K]
    (h : Units.rank K = 1) (w : InfinitePlace K) (hw : w ≠ dirichletUnitTheorem.w₀)
    (i : Fin (Units.rank K)) :
    Units.regulator K =
      |(Units.logEmbedding K (Additive.ofMul (Units.fundSystem K i))) ⟨w, hw⟩| := by
  classical
  rw [Units.regulator_eq_det']
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀} = 1 := by
    rw [show Fintype.card {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀} = Units.rank K
      from by simp [Units.rank], h]
  rw [Matrix.det_eq_elem_of_card_eq_one hcard ⟨w, hw⟩]
  simp only [Matrix.of_apply]
  have hsub : Subsingleton (Fin (Units.rank K)) := by rw [h]; infer_instance
  have heq : (Units.equivFinRank K).symm ⟨w, hw⟩ = i := hsub.elim _ _
  rw [heq]

/-- **Key estimate.**  In a totally real quadratic number field, the absolute logarithm of the
absolute value of a non-torsion unit at any infinite place is at least `1/4`.
The proof uses the product formula: for a unit `v` with `w v = x > 1` the element
`v - v⁻¹` is a nonzero algebraic integer all of whose conjugates have absolute value `x - x⁻¹`,
so its norm has absolute value `(x - x⁻¹)² ≥ 1`, whence `x ≥ 3/2` and `log x ≥ 1/4`. -/
theorem log_lower_bound_of_two_real_places (K : Type*) [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2)
    (hreal : ∀ w : InfinitePlace K, w.IsReal)
    (u : (𝓞 K)ˣ) (hu : u ∉ Units.torsion K) (w : InfinitePlace K) :
    1 / 4 ≤ |Real.log (w ((u : (𝓞 K)ˣ) : K))| := by
  classical
  obtain ⟨w', hw'⟩ : ∃ w' : InfinitePlace K, w' ≠ w := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsub : (Finset.univ : Finset (InfinitePlace K)) ⊆ {w} := by
      intro y _
      simp [h y]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at hc
    simp at hc
  have huniv : (Finset.univ : Finset (InfinitePlace K)) = {w, w'} :=
    (Finset.eq_of_subset_of_card_le (s := {w, w'}) (t := Finset.univ)
      (by intro y _; simp) (by
        rw [Finset.card_univ, hcard, Finset.card_pair hw'.symm])).symm
  have hmult1 : ∀ y : InfinitePlace K, y.mult = 1 := fun y ↦ (hreal y).mult_eq_one
  have hprod : ∀ v : (𝓞 K)ˣ,
      w ((v : (𝓞 K)ˣ) : K) * w' ((v : (𝓞 K)ˣ) : K) = 1 := by
    intro v
    have h := prod_apply_unit_eq_one K v
    rw [huniv, Finset.prod_insert (by simp [Ne.symm hw']), Finset.prod_singleton] at h
    simpa [hmult1] using h
  have key : ∀ v : (𝓞 K)ˣ, 1 < w ((v : (𝓞 K)ˣ) : K) →
      1 / 4 ≤ Real.log (w ((v : (𝓞 K)ˣ) : K)) := by
    intro v hv
    set x : ℝ := w ((v : (𝓞 K)ˣ) : K) with hxdef
    have hx1 : 1 < x := hv
    have hx0 : 0 < x := by linarith
    have hxinv1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1
    have hwv' : w' ((v : (𝓞 K)ˣ) : K) = x⁻¹ := by
      have h := hprod v
      rw [← hxdef] at h
      exact eq_inv_of_mul_eq_one_right h
    set V : K := ((v : (𝓞 K)ˣ) : K) with hV
    set Z : K := V - V⁻¹ with hZ
    set z : 𝓞 K := (v : 𝓞 K) - (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) with hz
    have hzK : (z : K) = Z := by
      rw [hz, hZ, hV, show V⁻¹ = (((v⁻¹ : (𝓞 K)ˣ) : K)) from by rw [hV]; simp]
      push_cast
      ring
    have hσV : |(InfinitePlace.embedding_of_isReal (hreal w)) V| = x := by
      have h := InfinitePlace.norm_embedding_of_isReal (hreal w) V
      rw [Real.norm_eq_abs] at h
      rw [h, hV, ← hxdef]
    have hZw : w Z = x - x⁻¹ := by
      have hσ : (InfinitePlace.embedding_of_isReal (hreal w)) Z =
          (InfinitePlace.embedding_of_isReal (hreal w)) V -
            ((InfinitePlace.embedding_of_isReal (hreal w)) V)⁻¹ := by
        rw [hZ, map_sub, map_inv₀]
      rw [(InfinitePlace.norm_embedding_of_isReal (hreal w) Z).symm, hσ, Real.norm_eq_abs]
      rcases (abs_eq hx0.le).mp hσV with h | h
      · rw [h, abs_of_pos (by linarith)]
      · rw [h]
        have h2 : -x - (-x)⁻¹ = -(x - x⁻¹) := by rw [inv_neg]; ring
        rw [h2, abs_neg, abs_of_pos (by linarith)]
    have hσV' : |(InfinitePlace.embedding_of_isReal (hreal w')) V| = x⁻¹ := by
      have h := InfinitePlace.norm_embedding_of_isReal (hreal w') V
      rw [Real.norm_eq_abs] at h
      rw [h, hV, hwv']
    have hZw' : w' Z = x - x⁻¹ := by
      have hσ : (InfinitePlace.embedding_of_isReal (hreal w')) Z =
          (InfinitePlace.embedding_of_isReal (hreal w')) V -
            ((InfinitePlace.embedding_of_isReal (hreal w')) V)⁻¹ := by
        rw [hZ, map_sub, map_inv₀]
      rw [(InfinitePlace.norm_embedding_of_isReal (hreal w') Z).symm, hσ, Real.norm_eq_abs]
      rcases (abs_eq (inv_pos.mpr hx0).le).mp hσV' with h | h
      · rw [h]
        have h2 : x⁻¹ - (x⁻¹)⁻¹ = x⁻¹ - x := by rw [inv_inv]
        rw [h2, abs_of_neg (by linarith)]
        ring
      · rw [h]
        have h2 : -x⁻¹ - (-x⁻¹)⁻¹ = x - x⁻¹ := by rw [inv_neg, inv_inv]; ring
        rw [h2, abs_of_pos (by linarith)]
    have hZ0 : Z ≠ 0 := by
      intro h0
      have : w Z = 0 := by rw [h0, map_zero]
      rw [hZw] at this
      linarith
    have hz0 : z ≠ 0 := by
      intro h0
      refine hZ0 ?_
      rw [← hzK, h0]
      simp
    have hNormEq : ((|Algebra.norm ℚ Z| : ℚ) : ℝ) = (x - x⁻¹) ^ 2 := by
      have h := InfinitePlace.prod_eq_abs_norm Z
      rw [huniv, Finset.prod_insert (by simp [Ne.symm hw']), Finset.prod_singleton,
        hmult1 w, hmult1 w', pow_one, pow_one, hZw, hZw'] at h
      rw [← h]; ring
    have hNz : (1 : ℝ) ≤ ((|Algebra.norm ℚ Z| : ℚ) : ℝ) := by
      have hcoef : Algebra.norm ℚ Z = ((Algebra.norm ℤ z : ℤ) : ℚ) := by
        rw [← hzK]; exact (Algebra.coe_norm_int z).symm
      have hn0 : Algebra.norm ℤ z ≠ 0 := by
        intro h0
        have : Algebra.norm ℚ Z = 0 := by rw [hcoef, h0]; norm_num
        exact (Algebra.norm_ne_zero_iff.mpr hZ0) this
      have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ z| := Int.one_le_abs hn0
      rw [hcoef, ← Int.cast_abs]
      exact_mod_cast h1
    have hsq : (1 : ℝ) ≤ (x - x⁻¹) ^ 2 := by rw [← hNormEq]; exact hNz
    have hsub1 : 1 ≤ x - x⁻¹ := by
      have hpos : 0 < x - x⁻¹ := by linarith
      have h : (1 : ℝ) ≤ |x - x⁻¹| := by
        have h2 : |(1 : ℝ)| ≤ |x - x⁻¹| := by
          rw [← sq_le_sq]
          simpa using hsq
        simpa using h2
      rwa [abs_of_pos hpos] at h
    have hx32 : 3 / 2 ≤ x := by
      by_contra hc
      have hc' : x < 3 / 2 := not_le.mp hc
      have hx2 : x ^ 2 - 1 ≥ x := by
        have h := mul_le_mul_of_nonneg_left hsub1 hx0.le
        rw [mul_one, mul_sub, mul_inv_cancel₀ hx0.ne'] at h
        linarith
      have hx3 : x ^ 2 - 1 < x := by
        have h : (x - 3 / 2) * (x + 1 / 2) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        nlinarith [h]
      linarith
    have hlog : 1 / 4 ≤ Real.log x := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
      rw [Real.log_inv] at h
      have h3 : x⁻¹ ≤ 2 / 3 := by
        have := (inv_le_inv₀ hx0 (by norm_num : (0 : ℝ) < 3 / 2)).mpr hx32
        simpa using this
      linarith
    exact hlog
  by_cases hgt : 1 < w ((u : (𝓞 K)ˣ) : K)
  · have h := key u hgt
    rwa [abs_of_pos (Real.log_pos hgt)]
  · have hle : w ((u : (𝓞 K)ˣ) : K) ≤ 1 := not_lt.mp hgt
    have hpos : 0 < w ((u : (𝓞 K)ˣ) : K) := by
      rw [InfinitePlace.pos_iff]
      exact fun h => Units.ne_zero u (Subtype.coe_injective h)
    have hne1 : w ((u : (𝓞 K)ˣ) : K) ≠ 1 := by
      intro h1
      refine hu ?_
      rw [← dirichletUnitTheorem.logEmbedding_eq_zero_iff]
      funext y
      have hy : (y : InfinitePlace K) = w ∨ (y : InfinitePlace K) = w' := by
        have hy' : (y : InfinitePlace K) ∈ ({w, w'} : Finset (InfinitePlace K)) := by
          rw [← huniv]; simp
        rw [Finset.mem_insert, Finset.mem_singleton] at hy'
        exact hy'
      rw [dirichletUnitTheorem.logEmbedding_component]
      rcases hy with hy | hy
      · rw [hy, h1]; simp
      · have hp := hprod u
        rw [h1, one_mul] at hp
        rw [hy, hp]; simp
    have hlt : w ((u : (𝓞 K)ˣ) : K) < 1 := lt_of_le_of_ne hle hne1
    have hinv : 1 < w (((u⁻¹ : (𝓞 K)ˣ) : K)) := by
      rw [show (((u⁻¹ : (𝓞 K)ˣ) : K)) = ((u : (𝓞 K)ˣ) : K)⁻¹ from by simp,
        map_inv₀, one_lt_inv₀ hpos]
      exact hlt
    have h := key (u⁻¹) hinv
    rw [show (((u⁻¹ : (𝓞 K)ˣ) : K)) = ((u : (𝓞 K)ˣ) : K)⁻¹ from by simp,
      map_inv₀, Real.log_inv] at h
    rw [abs_of_neg (Real.log_neg hpos hlt)]
    linarith

/-- There is a positive lower bound for the regulators of all quadratic number fields (namely
`1/4`): an imaginary quadratic field has regulator `1`, while a real quadratic field is totally
real with two infinite places and has regulator `log |ε| ≥ 1/4` for a non-torsion unit `ε`. -/
theorem exists_regulator_lower_bound_of_finrank_two :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K = 2 → c ≤ NumberField.Units.regulator K := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro K _ _ hfin
  rcases rank_eq_zero_or_one_of_finrank_eq_two K hfin with h0 | h1
  · rw [regulator_eq_one_of_rank_eq_zero K h0]
    norm_num
  · have hnr : InfinitePlace.nrComplexPlaces K = 0 :=
      nrComplexPlaces_eq_zero_of_rank_eq_one K h1 hfin
    have hreal : ∀ w : InfinitePlace K, w.IsReal :=
      fun w ↦ isReal_of_nrComplexPlaces_eq_zero K hnr w
    have hcard : Fintype.card (InfinitePlace K) = 2 :=
      card_infinitePlace_eq_two_of_rank_eq_one K h1
    let i : Fin (Units.rank K) := ⟨0, by omega⟩
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace K, w ≠ dirichletUnitTheorem.w₀ := by
      by_contra h
      simp only [not_exists, not_not] at h
      have hsub : (Finset.univ : Finset (InfinitePlace K)) ⊆ {dirichletUnitTheorem.w₀} := by
        intro y _
        simp [h y]
      have hc := Finset.card_le_card hsub
      rw [Finset.card_univ, hcard] at hc
      simp at hc
    rw [regulator_eq_abs_logEmbedding_of_rank_eq_one K h1 w hw i,
      dirichletUnitTheorem.logEmbedding_component, (hreal w).mult_eq_one, Nat.cast_one,
      one_mul]
    exact log_lower_bound_of_two_real_places K hcard hreal (Units.fundSystem K i)
      (fundSystem_notMem_torsion K i) w

end Commons.NumberTheory.NumberField