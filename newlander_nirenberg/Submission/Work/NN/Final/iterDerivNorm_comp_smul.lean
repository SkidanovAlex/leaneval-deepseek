import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Final

open scoped NNReal ENNReal
open Set

/-- Pulling a constant out of a supremum indexed by a set. -/
private lemma mul_iSup_mem {X : Type*} (a : ℝ≥0∞) (f : X → ℝ≥0∞) (s : Set X) :
    a * (⨆ x ∈ s, f x) = ⨆ x ∈ s, a * f x := by
  simp only [ENNReal.mul_iSup]

/-- Pulling a constant out of a double supremum with the off-diagonal condition. -/
private lemma mul_iSup_pair_ne {X : Type*} (a : ℝ≥0∞) (g : X → X → ℝ≥0∞) (s t : Set X) :
    a * (⨆ x ∈ s, ⨆ y ∈ t, ⨆ (_ : x ≠ y), g x y)
      = ⨆ x ∈ s, ⨆ y ∈ t, ⨆ (_ : x ≠ y), a * g x y := by
  simp only [ENNReal.mul_iSup]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `i`-fold precomposition of a continuous multilinear map with the dilation `z ↦ c • z`
is the same as multiplying the map by `c ^ i`. -/
private lemma compContinuousLinearMap_smul_id (c : ℝ) (i : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => X) ℂ) :
    A.compContinuousLinearMap (fun _ : Fin i => c • (1 : X →L[ℝ] X)) = c ^ i • A := by
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    one_apply_eq_self]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- The `i`-th iterated derivative of `z ↦ f (c • z)` on the set `{z | c • z ∈ Ω}` equals
`c ^ i` times the `i`-th iterated derivative of `f` on `Ω`, composed with the dilation. -/
private lemma iteratedFDerivWithin_comp_smul (c : ℝ) (hc : c ≠ 0) (i : ℕ) (f : X → ℂ)
    {Ω : Set X} (hΩ : IsOpen Ω) {x : X} (hx : c • x ∈ Ω) :
    iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} x
      = c ^ i • iteratedFDerivWithin ℝ i f Ω (c • x) := by
  have hsmul : ∀ (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => X) ℂ),
      A.compContinuousLinearMap (fun _ : Fin i => c • (1 : X →L[ℝ] X)) = c ^ i • A :=
    fun A => compContinuousLinearMap_smul_id c i A
  have h := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (s := Ω)
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X) f hΩ.uniqueDiffOn hx i
  have hkey :
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X) : X →L[ℝ] X) = c • 1 := by
    ext z
    simp [ContinuousLinearEquiv.smulLeft_apply_apply]
  have hset :
      (⇑(ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X) ⁻¹' Ω)
        = {z | c • z ∈ Ω} := by
    ext z; simp [ContinuousLinearEquiv.smulLeft_apply_apply]
  have hfun : (f ∘ ⇑(ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X))
      = (fun z => f (c • z)) := by
    funext z; simp [ContinuousLinearEquiv.smulLeft_apply_apply]
  rw [hfun, hset] at h
  rw [h]
  have hx' : (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X) x = c • x := by
    simp [ContinuousLinearEquiv.smulLeft_apply_apply]
  rw [hx']
  rw [show (fun _ : Fin i =>
        ((ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : X ≃L[ℝ] X) : X →L[ℝ] X))
      = (fun _ => c • (1 : X →L[ℝ] X)) from by rw [hkey]]
  exact hsmul (iteratedFDerivWithin ℝ i f Ω (c • x))

/-- Norm form of `iteratedFDerivWithin_comp_smul`. -/
private lemma norm_iteratedFDerivWithin_comp_smul (c : ℝ) (hc : c ≠ 0) (i : ℕ) (f : X → ℂ)
    {Ω : Set X} (hΩ : IsOpen Ω) {x : X} (hx : c • x ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} x‖
      = |c| ^ i * ‖iteratedFDerivWithin ℝ i f Ω (c • x)‖ := by
  rw [iteratedFDerivWithin_comp_smul c hc i f hΩ hx, norm_smul, Real.norm_eq_abs, abs_pow]

/-- Elementary rearrangement. -/
private lemma div_inv_mul_eq (a N D : ℝ) : N / (a⁻¹ * D) = a * (N / D) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The Hölder quotient of `z ↦ f (c • z)` at a pair of points of `{z | c • z ∈ Ω}` is
`|c| ^ (i + α)` times the Hölder quotient of `f` at the dilated pair. -/
private lemma ratio_comp_smul (c : ℝ) (hc : c ≠ 0) (i : ℕ) (α : ℝ) (f : X → ℂ)
    {Ω : Set X} (hΩ : IsOpen Ω) {x y : X} (hx : c • x ∈ Ω) (hy : c • y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} x
        - iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} y‖
      / ‖x - y‖ ^ α
    = |c| ^ ((i : ℝ) + α) *
      (‖iteratedFDerivWithin ℝ i f Ω (c • x) - iteratedFDerivWithin ℝ i f Ω (c • y)‖
        / ‖c • x - c • y‖ ^ α) := by
  have hdiff : iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} x
        - iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} y
      = c ^ i •
        (iteratedFDerivWithin ℝ i f Ω (c • x) - iteratedFDerivWithin ℝ i f Ω (c • y)) := by
    rw [iteratedFDerivWithin_comp_smul c hc i f hΩ hx,
      iteratedFDerivWithin_comp_smul c hc i f hΩ hy, smul_sub]
  have hnorm : ‖c • x - c • y‖ = |c| * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have hxynorm : ‖x - y‖ = |c|⁻¹ * ‖c • x - c • y‖ := by
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hc), one_mul]
  have hden : ‖x - y‖ ^ α = (|c|⁻¹) ^ α * ‖c • x - c • y‖ ^ α := by
    rw [hxynorm, Real.mul_rpow (inv_nonneg.mpr (abs_nonneg c)) (norm_nonneg _)]
  have hnum : ‖iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} x
        - iteratedFDerivWithin ℝ i (fun z => f (c • z)) {z | c • z ∈ Ω} y‖
      = |c| ^ i *
        ‖iteratedFDerivWithin ℝ i f Ω (c • x) - iteratedFDerivWithin ℝ i f Ω (c • y)‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_pow]
  rw [hnum, hden, Real.rpow_add (abs_pos.mpr hc), Real.rpow_natCast,
    Real.inv_rpow (abs_nonneg c) α]
  rw [div_inv_mul_eq, mul_div_assoc]
  ring

/-- Reindexing a supremum along the dilation. -/
private lemma iSup₂_comp_smul_shift (c : ℝ) (hc : c ≠ 0) (i : ℕ) (f : X → ℂ) (Ω : Set X) :
    (⨆ x ∈ {z : X | c • z ∈ Ω}, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω (c • x)‖)
      = ⨆ w ∈ Ω, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω w‖ := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => le_iSup₂_of_le (c • x) hx le_rfl
  · refine iSup₂_le fun w hw => le_iSup₂_of_le (c⁻¹ • w) ?_ ?_
    · show c • (c⁻¹ • w) ∈ Ω
      rwa [smul_inv_smul₀ hc]
    · show ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω w‖
          ≤ ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω (c • (c⁻¹ • w))‖
      rw [smul_inv_smul₀ hc]

/-- Reindexing a double supremum (with the off-diagonal condition) along the dilation. -/
private lemma iSup₃_comp_smul_shift (c : ℝ) (hc : c ≠ 0) (Ω : Set X)
    (P : X → X → ℝ≥0∞) :
    (⨆ x ∈ {z : X | c • z ∈ Ω}, ⨆ y ∈ {z : X | c • z ∈ Ω}, ⨆ (_ : x ≠ y),
        P (c • x) (c • y))
      = ⨆ u ∈ Ω, ⨆ v ∈ Ω, ⨆ (_ : u ≠ v), P u v := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hne : c • x ≠ c • y := fun h => hxy (by
      have h' := congrArg (fun w => c⁻¹ • w) h
      simpa [smul_smul, inv_mul_cancel₀ hc] using h')
    exact le_iSup₂_of_le (c • x) hx (le_iSup₂_of_le (c • y) hy (le_iSup_of_le hne le_rfl))
  · refine iSup₂_le fun u hu => iSup₂_le fun v hv => iSup_le fun huv => ?_
    have hu' : c • (c⁻¹ • u) ∈ Ω := by rwa [smul_inv_smul₀ hc]
    have hv' : c • (c⁻¹ • v) ∈ Ω := by rwa [smul_inv_smul₀ hc]
    have hnuv : c⁻¹ • u ≠ c⁻¹ • v := fun h => huv (by
      have h' := congrArg (fun w => c • w) h
      simpa [smul_smul, mul_inv_cancel₀ hc] using h')
    rw [show P u v = P (c • (c⁻¹ • u)) (c • (c⁻¹ • v)) from by
      rw [smul_inv_smul₀ hc, smul_inv_smul₀ hc]]
    exact le_iSup₂_of_le (c⁻¹ • u) hu'
      (le_iSup₂_of_le (c⁻¹ • v) hv' (le_iSup_of_le hnuv le_rfl))

/-- **Scaling of the Hölder norms under a dilation.** -/
theorem iterDerivNorm_comp_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c : ℝ) (hc : c ≠ 0) (i : ℕ) (α : ℝ) (f : X → ℂ) {Ω : Set X} (hΩ : IsOpen Ω) :
    Work.CR.Flat.iterDerivNorm i (fun z => f (c • z)) {z | c • z ∈ Ω}
        = ENNReal.ofReal (|c| ^ i) * Work.CR.Flat.iterDerivNorm i f Ω
      ∧ Work.CR.Flat.holderSeminorm i α (fun z => f (c • z)) {z | c • z ∈ Ω}
        = ENNReal.ofReal (|c| ^ ((i : ℝ) + α)) * Work.CR.Flat.holderSeminorm i α f Ω := by
  have hA : Work.CR.Flat.iterDerivNorm i (fun z => f (c • z)) {z | c • z ∈ Ω}
      = ENNReal.ofReal (|c| ^ i) *
        ⨆ x ∈ {z : X | c • z ∈ Ω},
          ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω (c • x)‖ := by
    rw [Work.CR.Flat.iterDerivNorm]
    rw [mul_iSup_mem]
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [norm_iteratedFDerivWithin_comp_smul c hc i f hΩ hx,
      ENNReal.ofReal_mul (pow_nonneg (abs_nonneg c) i)]
  have hB : (⨆ x ∈ {z : X | c • z ∈ Ω},
        ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω (c • x)‖)
      = Work.CR.Flat.iterDerivNorm i f Ω := by
    rw [Work.CR.Flat.iterDerivNorm]
    exact iSup₂_comp_smul_shift c hc i f Ω
  have hC : Work.CR.Flat.holderSeminorm i α (fun z => f (c • z)) {z | c • z ∈ Ω}
      = ENNReal.ofReal (|c| ^ ((i : ℝ) + α)) *
        ⨆ x ∈ {z : X | c • z ∈ Ω}, ⨆ y ∈ {z : X | c • z ∈ Ω}, ⨆ (_ : x ≠ y),
          ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f Ω (c • x)
            - iteratedFDerivWithin ℝ i f Ω (c • y)‖ / ‖c • x - c • y‖ ^ α) := by
    rw [Work.CR.Flat.holderSeminorm]
    rw [mul_iSup_pair_ne]
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      iSup_congr fun hxy => ?_
    rw [ratio_comp_smul c hc i α f hΩ hx hy,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg c) _)]
  have hD : (⨆ x ∈ {z : X | c • z ∈ Ω}, ⨆ y ∈ {z : X | c • z ∈ Ω}, ⨆ (_ : x ≠ y),
        ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f Ω (c • x)
          - iteratedFDerivWithin ℝ i f Ω (c • y)‖ / ‖c • x - c • y‖ ^ α))
      = Work.CR.Flat.holderSeminorm i α f Ω := by
    rw [Work.CR.Flat.holderSeminorm]
    exact iSup₃_comp_smul_shift c hc Ω
      (fun u v => ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f Ω u
        - iteratedFDerivWithin ℝ i f Ω v‖ / ‖u - v‖ ^ α))
  exact ⟨hA.trans (by rw [hB]), hC.trans (by rw [hD])⟩

end Work.NN.Final
