import Mathlib
import Submission.Work.WilkiesH.Defs

set_option linter.style.haveILetI false

/-!
# A height lower bound for algebraic reals

For an algebraic real number `x` and `K = ℚ⟮x⟯` with `y = AdjoinSimple.gen ℚ x` the generator,
we prove that the multiplicative height of `y` dominates the archimedean absolute value of `x`
(and, by symmetry `H(y) = H(y⁻¹)`, also its inverse).  Consequently

  `1 / (absMulHeight₁ x) ^ [K : ℚ] ≤ |x|`.

This is the "Liouville-type" inequality used to bound the denominator of a point of small
height in the counting argument.
-/

open Classical IntermediateField NumberField

namespace Work.WilkiesH.NT

/-- For `x` an algebraic real number, `K = ℚ⟮x⟯` with its number field structure, the
archimedean absolute value of any `z : K` is at most the multiplicative height of `z`.

The proof picks the infinite place `w` of `K` induced by the inclusion `K ⊆ ℝ`; it satisfies
`w z = |(z : ℝ)|` and has multiplicity `1`.  This single factor of the archimedean product in
`NumberField.mulHeight₁` already dominates `|(z : ℝ)|`. -/
theorem abs_coe_le_mulHeight₁ (x : ℝ) [NumberField ℚ⟮x⟯] (z : ℚ⟮x⟯) :
    |(z : ℝ)| ≤ Height.mulHeight₁ z := by
  let φ : ℚ⟮x⟯ →+* ℂ := Complex.ofRealHom.comp (IntermediateField.val ℚ⟮x⟯).toRingHom
  have hφreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext w
    show star (φ w) = φ w
    simp [φ]
  have hwmult : (InfinitePlace.mk φ).mult = 1 :=
    InfinitePlace.IsReal.mult_eq_one ⟨φ, hφreal, rfl⟩
  have hwz : ∀ w : ℚ⟮x⟯, (InfinitePlace.mk φ) w = |(w : ℝ)| := by
    intro w
    rw [InfinitePlace.apply]
    have : φ w = (w : ℂ) := by simp [φ]
    rw [this]
    exact RCLike.norm_ofReal (w : ℝ)
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hlogeq := NumberField.logHeight₁_eq z
  have hsingle :
      Real.posLog |(z : ℝ)| ≤ ∑ v : InfinitePlace ℚ⟮x⟯, (v.mult : ℝ) * Real.posLog (v z) := by
    have hmem : (InfinitePlace.mk φ) ∈ (Finset.univ : Finset (InfinitePlace ℚ⟮x⟯)) :=
      Finset.mem_univ _
    have := Finset.single_le_sum
      (f := fun v : InfinitePlace ℚ⟮x⟯ => (v.mult : ℝ) * Real.posLog (v z))
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg) hmem
    simpa [hwmult, hwz z] using this
  have hfin : 0 ≤ ∑ᶠ v : FinitePlace ℚ⟮x⟯, Real.posLog (v z) :=
    finsum_nonneg (fun v => Real.posLog_nonneg)
  have hz0 : (z : ℝ) ≠ 0 := by simpa using hz
  have hle : Real.log |(z : ℝ)| ≤ Real.log (Height.mulHeight₁ z) := by
    rw [← Height.logHeight₁_eq_log_mulHeight₁, hlogeq]
    calc Real.log |(z : ℝ)| ≤ Real.posLog |(z : ℝ)| := le_max_right _ _
      _ ≤ (∑ v : InfinitePlace ℚ⟮x⟯, (v.mult : ℝ) * Real.posLog (v z))
            + ∑ᶠ v : FinitePlace ℚ⟮x⟯, Real.posLog (v z) := by
          linarith [hsingle, hfin]
  exact (Real.log_le_log_iff (abs_pos.mpr hz0) (Height.mulHeight₁_pos z)).mp hle

theorem inv_absMulHeight_pow_le_abs {x : ℝ} (hx : IsIntegral ℚ x) (hx0 : x ≠ 0) :
    1 / (NumberField.absMulHeight₁ x) ^
        (Module.finrank ℚ (IntermediateField.adjoin ℚ ({x} : Set ℝ))) ≤ |x| := by
  let S := IntermediateField.adjoin ℚ ({x} : Set ℝ)
  haveI : FiniteDimensional ℚ S := IntermediateField.adjoin.finiteDimensional hx
  haveI : NumberField S := {}
  let y : S := AdjoinSimple.gen ℚ x
  have hyx : (y : ℝ) = x := IntermediateField.AdjoinSimple.coe_gen ℚ x
  -- The absolute height of the generator dominates the inverse of `|x|`, by applying the
  -- archimedean bound to `y⁻¹` and using `H(y⁻¹) = H(y)`.
  have h2 : 1 / |x| ≤ Height.mulHeight₁ y := by
    have h := abs_coe_le_mulHeight₁ x y⁻¹
    rw [Height.mulHeight₁_inv y] at h
    have hyi : ((y⁻¹ : S) : ℝ) = x⁻¹ := by
      rw [IntermediateField.coe_inv, hyx]
    rw [hyi, abs_inv, inv_eq_one_div] at h
    exact h
  -- `absMulHeight₁ x` is the `finrank`-th root of `mulHeight₁ y`, so its `finrank`-th power is it.
  have hHd : (NumberField.absMulHeight₁ x) ^
        (Module.finrank ℚ (IntermediateField.adjoin ℚ ({x} : Set ℝ))) = Height.mulHeight₁ y := by
    rw [NumberField.absMulHeight₁, dite_eq_left hx]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Height.mulHeight₁_nonneg y)]
    have hd : ((Module.finrank ℚ S : ℝ))⁻¹ * (Module.finrank ℚ S : ℝ) = 1 := by
      rw [inv_mul_cancel₀]
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := S)).ne'
    rw [hd, Real.rpow_one]
  rw [hHd]
  have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx0
  have hhpos : (0 : ℝ) < Height.mulHeight₁ y := Height.mulHeight₁_pos y
  rw [div_le_iff₀ hhpos]
  have hmul : |x| * (1 / |x|) = 1 := mul_one_div_cancel hxpos.ne'
  have hle2 : |x| * (1 / |x|) ≤ |x| * Height.mulHeight₁ y :=
    mul_le_mul_of_nonneg_left h2 hxpos.le
  rwa [hmul] at hle2

end Work.WilkiesH.NT
