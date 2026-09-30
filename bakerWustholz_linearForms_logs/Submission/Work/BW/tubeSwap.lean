import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace Work.BW

open MeasureTheory MeasureTheory.Measure Set Matrix

/-- The integrand of the tube-swap statement: the indicator of the set of pairs `(x,y)`
for which every coordinate of `B x + Bp y` has absolute value at most `1/2`. -/
noncomputable def tubeIntegrand {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ) (x : Fin k → ℝ) (y : Fin (n-k) → ℝ) : ℝ :=
  if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then 1 else 0

theorem tubeSwap {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : B.transpose * B = 1)
    (Bp : Matrix (Fin n) (Fin (n-k)) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : Fin k → ℝ, ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
        (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
      = ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
          ∫ x : Fin k → ℝ,
            (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) := by
  classical
  set s : Set (Fin (n-k) → ℝ) :=
    Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)) with hsdef
  set C : ℝ := 1/2 + ∑ p : Fin n, ∑ j : Fin (n-k), |Bp p j| * (δ/2) with hCdef
  set V : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (-C) C) with hVdef
  set W : Set (Fin k → ℝ) := (fun v : Fin n → ℝ => B.transpose.mulVec v) '' V with hWdef
  change (∫ x : Fin k → ℝ, ∫ y in s, tubeIntegrand B Bp x y)
      = ∫ y in s, ∫ x : Fin k → ℝ, tubeIntegrand B Bp x y
  -- measurability / compactness of the two boxes and of `W`
  have hs_meas : MeasurableSet s := by
    rw [hsdef]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hs_compact : IsCompact s := by
    rw [hsdef]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hs_fin : volume s < ⊤ := hs_compact.measure_lt_top
  have hV_compact : IsCompact V := by
    rw [hVdef]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hT_cont : Continuous (fun v : Fin n → ℝ => B.transpose.mulVec v) := by
    rw [show (fun v : Fin n → ℝ => B.transpose.mulVec v)
        = (⇑(Matrix.toLin' B.transpose) : (Fin n → ℝ) → (Fin k → ℝ)) from
          by funext v; rw [Matrix.toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hW_compact : IsCompact W := by
    rw [hWdef]
    exact hV_compact.image hT_cont
  have hW_fin : volume W < ⊤ := hW_compact.measure_lt_top
  -- key pointwise fact: outside `W` the integrand vanishes on the tube over `s`
  have hkey : ∀ x y, y ∈ s → x ∉ W → tubeIntegrand B Bp x y = 0 := by
    intro x y hy hxW
    unfold tubeIntegrand
    rw [if_neg]
    intro hc
    apply hxW
    rw [hWdef]
    refine ⟨B.mulVec x, ?_, ?_⟩
    · rw [hVdef]
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      intro i
      have hy' : ∀ j : Fin (n-k), |y j| ≤ δ/2 := by
        have hy2 := hy
        rw [hsdef, Set.mem_pi] at hy2
        intro j
        exact abs_le.mpr (Set.mem_Icc.mp (hy2 j trivial))
      have h1 : |(B.mulVec x) i| ≤ 1/2 + |(Bp.mulVec y) i| := by
        have he : (B.mulVec x) i = (B.mulVec x + Bp.mulVec y) i - (Bp.mulVec y) i := by
          simp only [Pi.add_apply]; ring
        calc |(B.mulVec x) i| = |(B.mulVec x + Bp.mulVec y) i - (Bp.mulVec y) i| := by rw [he]
          _ = |(B.mulVec x + Bp.mulVec y) i + -(Bp.mulVec y) i| := by rw [sub_eq_add_neg]
          _ ≤ |(B.mulVec x + Bp.mulVec y) i| + |-(Bp.mulVec y) i| := abs_add_le _ _
          _ = |(B.mulVec x + Bp.mulVec y) i| + |(Bp.mulVec y) i| := by rw [abs_neg]
          _ ≤ 1/2 + |(Bp.mulVec y) i| := add_le_add (hc i) le_rfl
      have h2 : |(Bp.mulVec y) i| ≤ ∑ j : Fin (n-k), |Bp i j| * (δ/2) := by
        calc |(Bp.mulVec y) i| = |∑ j, Bp i j * y j| := by
                simp only [Matrix.mulVec, dotProduct]
          _ ≤ ∑ j, |Bp i j * y j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |Bp i j| * |y j| := by simp only [abs_mul]
          _ ≤ ∑ j, |Bp i j| * (δ/2) :=
              Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy' j) (abs_nonneg _))
      have h2' : (∑ j : Fin (n-k), |Bp i j| * (δ/2))
          ≤ ∑ p : Fin n, ∑ j : Fin (n-k), |Bp p j| * (δ/2) := by
        have hslem := Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun p : Fin n => ∑ j : Fin (n-k), |Bp p j| * (δ/2))
          (fun p _ => Finset.sum_nonneg
            (fun j _ => mul_nonneg (abs_nonneg _) (by positivity)))
          (Finset.mem_univ i)
        simpa using hslem
      have h3 : 1/2 + |(Bp.mulVec y) i| ≤ C := by
        rw [hCdef]; linarith [h2, h2']
      exact Set.mem_Icc.mpr (abs_le.mp (h1.trans h3))
    · show B.transpose.mulVec (B.mulVec x) = x
      rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  -- measurability of the integrand on the product
  have hmvB : Continuous (fun x : Fin k → ℝ => B.mulVec x) := by
    rw [show (fun x : Fin k → ℝ => B.mulVec x)
        = (⇑(Matrix.toLin' B) : (Fin k → ℝ) → (Fin n → ℝ)) from
          by funext x; rw [Matrix.toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hmvBp : Continuous (fun y : Fin (n-k) → ℝ => Bp.mulVec y) := by
    rw [show (fun y : Fin (n-k) → ℝ => Bp.mulVec y)
        = (⇑(Matrix.toLin' Bp) : (Fin (n-k) → ℝ) → (Fin n → ℝ)) from
          by funext y; rw [Matrix.toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hK_meas : MeasurableSet {v : Fin n → ℝ | ∀ i, |v i| ≤ 1/2} := by
    have he : {v : Fin n → ℝ | ∀ i, |v i| ≤ 1/2} = ⋂ i, {v : Fin n → ℝ | |v i| ≤ 1/2} := by
      ext v; simp
    rw [he]
    refine MeasurableSet.iInter (fun i => ?_)
    have hi : {v : Fin n → ℝ | |v i| ≤ 1/2}
        = (fun v : Fin n → ℝ => v i) ⁻¹' Set.Icc (-(1/2)) (1/2) := by
      ext v; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]; exact abs_le
    rw [hi]
    exact measurableSet_Icc.preimage (continuous_apply i).measurable
  have hcond : MeasurableSet {p : (Fin k → ℝ) × (Fin (n-k) → ℝ) |
      ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2} := by
    have he : {p : (Fin k → ℝ) × (Fin (n-k) → ℝ) |
          ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2}
        = (fun p : (Fin k → ℝ) × (Fin (n-k) → ℝ) => B.mulVec p.1 + Bp.mulVec p.2) ⁻¹'
            {v : Fin n → ℝ | ∀ i, |v i| ≤ 1/2} := rfl
    rw [he]
    exact hK_meas.preimage
      (((hmvB.comp continuous_fst).add (hmvBp.comp continuous_snd)).measurable)
  have hF_meas : Measurable
      (fun p : (Fin k → ℝ) × (Fin (n-k) → ℝ) => tubeIntegrand B Bp p.1 p.2) := by
    simp only [tubeIntegrand]
    exact Measurable.ite hcond measurable_const measurable_const
  -- the product measure with both sides restricted is finite
  haveI : IsFiniteMeasure ((volume.restrict W).prod (volume.restrict s)) := by
    refine ⟨?_⟩
    rw [show (univ : Set ((Fin k → ℝ) × (Fin (n-k) → ℝ))) = univ ×ˢ univ from
      Set.univ_prod_univ.symm]
    rw [Measure.prod_prod]
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top hW_fin hs_fin
  -- integrability of the integrand
  have hint : Integrable (Function.uncurry (tubeIntegrand B Bp))
      ((volume.restrict W).prod (volume.restrict s)) := by
    refine Integrable.of_bound ?_ 1 ?_
    · rw [Function.uncurry_def]
      exact hF_meas.aestronglyMeasurable
    · filter_upwards with z
      rw [Function.uncurry_def]
      simp only [tubeIntegrand]
      split_ifs <;> norm_num
  have hfub := integral_integral_swap (f := tubeIntegrand B Bp) hint
  calc (∫ x : Fin k → ℝ, ∫ y in s, tubeIntegrand B Bp x y)
      = ∫ x in W, ∫ y in s, tubeIntegrand B Bp x y :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => setIntegral_eq_zero_of_forall_eq_zero
            (fun y hy => hkey x y hy hx))).symm
    _ = ∫ y in s, ∫ x in W, tubeIntegrand B Bp x y := hfub
    _ = ∫ y in s, ∫ x : Fin k → ℝ, tubeIntegrand B Bp x y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hs_meas] with y hy
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hkey x y hy hx)

end Work.BW
