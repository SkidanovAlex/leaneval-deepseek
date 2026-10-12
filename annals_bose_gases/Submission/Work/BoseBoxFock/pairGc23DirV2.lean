import Mathlib
import Submission.Work.BoseBoxFock.pairS23_setIntegral_fst
import Submission.Work.BoseBoxFock.pgW_L2_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23DirV2` — differentiability and the gradient bound of the `pairGc23` fibre

The clean fibre `pairGc23 ℓ p hp Θ₀ A B` (`pairGCore`) is the box integral

    ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z * pgKer p Θ₀ w₁ w z

(`pairGc23DirDefs`), i.e. a *parametric* integral whose parameter `w` sits only in the smooth
kernel factor `pgKer p Θ₀ w₁ w z = star (Θ₀ (insertCoord2 p w w₁ z.1))`, while `pgW` is a
`w`-independent weight involving the two bounded measurable factors `A`, `B`.

The two conclusions of the target are

* `w ↦ pairGc23 ℓ p hp Θ₀ A B w w₁` is differentiable everywhere (dominated differentiation under
  the integral sign with a bounded measurable weight, `hasFDerivAt_setIntegral_weighted`);
* its gradient is bounded by `cA² cB² ℓ⁶ · dirX23 ℓ p Θ₀ w w₁ · pinL2 ℓ Θ₀`;

the second is the *Cauchy–Schwarz* split of the derivative integral

    ∂_j pairGc23 = ∫ z in K, pgW z * star (fderiv Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j)) :

the kernel factor `star (fderiv Θ₀ …)` depends only on `z.1`, so `‖∫‖²` is bounded by
`(∫_K ‖pgW‖²)·(∫_K ‖∂_j Θ₀‖²)`, the first factor being `≤ cA²cB² pinL2` (`pgW_L2_le`) and the
second being `ℓ⁶` times the `j`-th summand of `dirX23` (`pairS23_setIntegral_fst`).

`sorry`-free.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. General bricks -/

/-- Conjugation on `ℂ` is the continuous `ℝ`-linear equivalence `RCLike.conjCLE`. -/
private lemma conjCLE_coe : (⇑(RCLike.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) = fun z => star z := by
  ext z
  simp only [RCLike.conjCLE_apply]
  simp [RCLike.star_def]

/-- **Joint continuity of the partial derivative family** of a jointly `C^∞` function. -/
private theorem continuous_uncurry_fderiv {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : P → G → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g)) :
    Continuous (fun r : P × G => fderiv ℝ (fun q : P => g q r.2) r.1) := by
  have h1 : ContDiff ℝ (((0 : ℕ) + 1 : ℕ) : ℕ∞) (Function.uncurry g) := by
    simpa using contDiff_infty.mp hg 1
  have h2 := Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (F := g) h1
  have he : (Function.uncurry fun (p : P) (x : G) => fderiv ℝ (fun q : P => g q x) p)
      = fun r : P × G => fderiv ℝ (fun q : P => g q r.2) r.1 := rfl
  rw [he] at h2
  exact contDiff_zero.mp h2

/-- **Dominated differentiation under the integral sign with a bounded measurable weight.**

For a compact `k`, an a.e. strongly measurable weight `a` bounded on `k`, and a jointly `C^∞`
kernel `g`, the parametric integral `p ↦ ∫ z in k, a z * g p z` is differentiable at every point,
with derivative `∫ z in k, a z • fderiv ℝ (fun q => g q z) p₀`. -/
private theorem hasFDerivAt_setIntegral_weighted
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    [MeasureTheory.IsFiniteMeasureOnCompacts (volume : Measure G)]
    {k : Set G} (hk : IsCompact k) {a : G → ℂ} {ca : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict k)) (hab : ∀ z ∈ k, ‖a z‖ ≤ ca)
    {g : P → G → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g)) (p₀ : P) :
    HasFDerivAt (fun p => ∫ z in k, a z * g p z)
      (∫ z in k, a z • fderiv ℝ (fun q => g q z) p₀) p₀ := by
  haveI hfin : IsFiniteMeasure (volume.restrict k) :=
    isFiniteMeasure_restrict.mpr hk.measure_ne_top
  set L : P × G → (P →L[ℝ] ℂ) := fun r => fderiv ℝ (fun q : P => g q r.2) r.1 with hL
  have hLcont : Continuous L := continuous_uncurry_fderiv hg
  have hLp₀c : Continuous (fun z : G => L (p₀, z)) :=
    hLcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := hk.exists_bound_of_continuousOn hLp₀c.continuousOn
  obtain ⟨v, hv, hv'⟩ : ∃ v ∈ 𝓝 p₀, ∀ q ∈ v, ∀ z ∈ k, ‖L (q, z) - L (p₀, z)‖ ≤ 1 := by
    have hu : {y : (P →L[ℝ] ℂ) × (P →L[ℝ] ℂ) | dist y.1 y.2 < 1} ∈ uniformity (P →L[ℝ] ℂ) :=
      Metric.dist_mem_uniformity one_pos
    have hcont : ContinuousOn (fun r : P × G => L r) (Set.univ ×ˢ k) :=
      hLcont.continuousOn.mono (fun x _ => trivial)
    obtain ⟨w, hw, hw'⟩ := hk.mem_uniformity_of_prod (s := Set.univ)
      (f := fun (q : P) (z : G) => L (q, z)) (q := p₀)
      (u := {y : (P →L[ℝ] ℂ) × (P →L[ℝ] ℂ) | dist y.1 y.2 < 1}) hcont (Set.mem_univ p₀) hu
    refine ⟨w, ?_, fun q hq z hz => ?_⟩
    · simpa using hw
    · have h : dist (L (q, z)) (L (p₀, z)) < 1 := hw' q hq z hz
      rw [dist_eq_norm] at h
      exact le_of_lt h
  set C : ℝ := max M 0 + 1 with hC
  have hCnn : 0 ≤ C := by positivity
  have hgcont : Continuous (Function.uncurry g) := hg.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume.restrict k)
    (F := fun x z => a z * g x z) (F' := fun x z => a z • L (x, z))
    (x₀ := p₀) (s := v) (bound := fun z => C * ‖a z‖) hv ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with x
    exact ha.mul ((hgcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · obtain ⟨M₂, hM₂⟩ := hk.exists_bound_of_continuousOn
      ((hgcont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine Integrable.of_bound
      (ha.mul ((hgcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
      (max ca 0 * max M₂ 0) ?_
    refine (ae_restrict_iff' hk.measurableSet).mpr ?_
    filter_upwards with z hz
    calc ‖a z * g p₀ z‖ = ‖a z‖ * ‖g p₀ z‖ := norm_mul _ _
      _ ≤ max ca 0 * max M₂ 0 := mul_le_mul (le_trans (hab z hz) (le_max_left _ _))
          (le_trans (hM₂ z hz) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  · exact ha.smul (hLp₀c.aestronglyMeasurable)
  · refine (ae_restrict_iff' hk.measurableSet).mpr ?_
    filter_upwards with z hz x hx
    have h1 : ‖L (x, z)‖ ≤ C := by
      have h := hv' x hx z hz
      have h2 : ‖L (x, z)‖ ≤ ‖L (p₀, z)‖ + 1 := by
        calc ‖L (x, z)‖ = ‖(L (x, z) - L (p₀, z)) + L (p₀, z)‖ := by rw [sub_add_cancel]
          _ ≤ ‖L (x, z) - L (p₀, z)‖ + ‖L (p₀, z)‖ := norm_add_le _ _
          _ ≤ 1 + ‖L (p₀, z)‖ := by linarith
          _ = ‖L (p₀, z)‖ + 1 := by ring
      have h3 : ‖L (p₀, z)‖ ≤ M := hM z hz
      have hMle : M + 1 ≤ C := by rw [hC]; linarith [le_max_left M 0]
      linarith
    calc ‖a z • L (x, z)‖ = ‖a z‖ * ‖L (x, z)‖ := norm_smul (a z) (L (x, z))
      _ ≤ ‖a z‖ * C := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C * ‖a z‖ := by ring
  · refine Integrable.of_bound (ha.norm.const_mul C) (C * max ca 0) ?_
    refine (ae_restrict_iff' hk.measurableSet).mpr ?_
    filter_upwards with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hCnn (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (le_trans (hab z hz) (le_max_left _ _)) hCnn
  · filter_upwards with z x hx
    have hd : HasFDerivAt (fun q : P => g q z) (L (x, z)) x := by
      have hgz : ContDiff ℝ (⊤ : ℕ∞) (fun q : P => g q z) :=
        hg.comp (contDiff_id.prodMk contDiff_const)
      have hdiff : DifferentiableAt ℝ (fun q : P => g q z) x :=
        ((contDiff_infty.mp hgz 1).differentiable (by norm_num)).differentiableAt
      simpa [hL] using hdiff.hasFDerivAt
    rw [show (fun q : P => a z * g q z) = (a z • fun q => g q z) from by
      funext q; simp [smul_eq_mul]]
    exact hd.const_smul (a z)

/-- **Cauchy–Schwarz for the integral of a product of two `ℂ`-valued functions.** -/
private theorem cs_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f (ENNReal.ofReal 2) μ) (hg : MemLp g (ENNReal.ofReal 2) μ) :
    ‖∫ z, f z * g z ∂μ‖ ^ 2 ≤ (∫ z, ‖f z‖ ^ 2 ∂μ) * (∫ z, ‖g z‖ ^ 2 ∂μ) := by
  have h1 : ‖∫ z, f z * g z ∂μ‖ ≤ ∫ z, ‖f z‖ * ‖g z‖ ∂μ := by
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [norm_mul])
  have h2 : ∫ z, ‖f z‖ * ‖g z‖ ∂μ
      ≤ (∫ z, ‖f z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, ‖g z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) (p := 2) (q := 2)
      Real.HolderConjugate.two_two hf hg
    have h' : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) = ∫ a, ‖f a‖ ^ (2 : ℕ) ∂μ := by
      congr 1 with a
      exact Real.rpow_natCast (‖f a‖) 2
    have h'' : (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) = ∫ a, ‖g a‖ ^ (2 : ℕ) ∂μ := by
      congr 1 with a
      exact Real.rpow_natCast (‖g a‖) 2
    rw [h', h''] at h
    exact h
  have hA : 0 ≤ ∫ z, ‖f z‖ ^ 2 ∂μ := integral_nonneg fun z => by positivity
  have hB : 0 ≤ ∫ z, ‖g z‖ ^ 2 ∂μ := integral_nonneg fun z => by positivity
  calc ‖∫ z, f z * g z ∂μ‖ ^ 2
      ≤ (∫ z, ‖f z‖ * ‖g z‖ ∂μ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ((∫ z, ‖f z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, ‖g z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun z => by positivity) h2 2
    _ = (∫ z, ‖f z‖ ^ 2 ∂μ) * (∫ z, ‖g z‖ ^ 2 ∂μ) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-! ## 2. The single-slot insertion and the chain rule for the kernel factor -/

/-- The single-slot insertion `v ↦ Function.update 0 i v` as a continuous linear map. -/
private noncomputable def insLin {n : ℕ} (i : Fin n) : E3 →L[ℝ] Xn n :=
  ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i

private lemma insLin_apply {n : ℕ} (i : Fin n) (v : E3) :
    insLin i v = Function.update (0 : Xn n) i v := by
  rw [insLin, ContinuousLinearMap.single_apply]
  funext k
  simp only [Pi.single_apply, Function.update_apply, Pi.zero_apply]

private lemma insLin_single {n : ℕ} (i : Fin n) (j : Fin 3) :
    insLin i (EuclideanSpace.single j (1 : ℝ)) = slotDirVec i j := by
  rw [insLin_apply, slotDirVec]

/-- **Chain rule for the kernel factor.**  Differentiating
`q ↦ pgKer p Θ₀ w₁ q z = star (Θ₀ (insertCoord2 p q w₁ z.1))` at `w` in the coordinate direction
`EuclideanSpace.single j 1` gives the `p.1`-slot derivative of `Θ₀` at `insertCoord2 p w w₁ z.1`. -/
private theorem fderiv_pgKer_single {n : ℕ} {p : Fin n × Fin n} {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (w w₁ : E3)
    (z : (pairFib23 n p → E3) × (E3 × E3)) (j : Fin 3) :
    fderiv ℝ (fun q : E3 => pgKer p Θ₀ w₁ q z) w (EuclideanSpace.single j (1 : ℝ))
      = star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j)) := by
  have hS : HasFDerivAt (fun q : E3 => insertCoord2 p q w₁ z.1)
      (insLin p.1 : E3 →L[ℝ] Xn n) w := by
    have h1 : HasFDerivAt (fun q : E3 => (insLin p.1) q + insertCoord2 p (0 : E3) w₁ z.1)
        (insLin p.1 : E3 →L[ℝ] Xn n) w := (insLin p.1).hasFDerivAt.add_const _
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    funext k
    show insertCoord2 p q w₁ z.1 k = ((insLin p.1) q + insertCoord2 p (0 : E3) w₁ z.1) k
    rw [Pi.add_apply, insLin_apply]
    simp only [Pi.zero_apply, Function.update_apply, insertCoord2_eq, insertCoord2_eq]
    split_ifs <;> simp_all
  have h2 : HasFDerivAt (fun q : E3 => Θ₀ (insertCoord2 p q w₁ z.1))
      ((fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1)).comp (insLin p.1 : E3 →L[ℝ] Xn n)) w :=
    ((hΘ₀.differentiable (by simp)).differentiableAt.hasFDerivAt).comp w hS
  have h3 : HasFDerivAt (fun q : E3 => star (Θ₀ (insertCoord2 p q w₁ z.1)))
      (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp
        ((fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1)).comp (insLin p.1 : E3 →L[ℝ] Xn n))) w := by
    have hstar : HasFDerivAt (fun y : ℂ => star y)
        ((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)
        (Θ₀ (insertCoord2 p w w₁ z.1)) := by
      have h := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
        (x := Θ₀ (insertCoord2 p w w₁ z.1))
      rwa [conjCLE_coe] at h
    exact hstar.comp w h2
  change fderiv ℝ (fun q : E3 => star (Θ₀ (insertCoord2 p q w₁ z.1))) w
      (EuclideanSpace.single j (1 : ℝ))
    = star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j))
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [insLin_single]
  simp [RCLike.conjCLE_apply, RCLike.star_def]

theorem pairGc23DirV2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun w' => Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1)
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * Work.BoseBoxFock.dirX23 ℓ p Θ₀ z.1 z.2
              * Work.BoseBoxFock.pinL2 ℓ Θ₀) := by
  have hKc : IsCompact (pairS23 ℓ p) := isCompact_pairS23 hℓ p
  have hKmeas : MeasurableSet (pairS23 ℓ p) := hKc.measurableSet
  haveI hfinK : IsFiniteMeasure (volume.restrict (pairS23 ℓ p)) :=
    isFiniteMeasure_restrict.mpr hKc.measure_ne_top
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_on_abox hℓ hΘ₀.continuous
  -- the weight is measurable and bounded on the box
  have hins : Continuous fun z : (pairFib23 n p → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1 := continuous_insertCoord2_joint_pg23 p
  have hWmeas : AEStronglyMeasurable (pgW p Θ₀ A B) (volume.restrict (pairS23 ℓ p)) := by
    have h1 : Measurable fun z : (pairFib23 n p → E3) × (E3 × E3) => A z.2.1 :=
      hA.comp ((continuous_fst.comp continuous_snd).measurable)
    have h2 : Measurable fun z : (pairFib23 n p → E3) × (E3 × E3) => B z.2.2 :=
      hB.comp ((continuous_snd.comp continuous_snd).measurable)
    have h3 : Measurable fun z : (pairFib23 n p → E3) × (E3 × E3) =>
        Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) := hΘ₀.continuous.measurable.comp hins.measurable
    have h4 := ((continuous_star.measurable.comp h1).mul
      (continuous_star.measurable.comp h2)).mul h3
    exact h4.aestronglyMeasurable
  have hWb : ∀ z ∈ pairS23 ℓ p, ‖pgW p Θ₀ A B z‖ ≤ cA * cB * M₀ := by
    intro z hz
    obtain ⟨hz1, hz2a, hz2b⟩ := mem_pairS23.mp hz
    have hmem : insertCoord2 p z.2.1 z.2.2 z.1 ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord2_mem_abox_iff hℓ hz2a hz2b z.1).mpr hz1
    have h1 : ‖A z.2.1‖ ≤ cA := hAb _
    have h2 : ‖B z.2.2‖ ≤ cB := hBb _
    have h3 : ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ≤ M₀ := hM₀ _ hmem
    rw [pgW, norm_mul, norm_mul, norm_star, norm_star]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hcA) h3 (norm_nonneg _)
      (mul_nonneg hcA hcB)
  have hW2 : (∫ z in pairS23 ℓ p, ‖pgW p Θ₀ A B z‖ ^ 2) ≤ cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ :=
    pgW_L2_le hℓ p hp hΘ₀ hAb hBb hcA hcB
  have main : ∀ pz : E3 × E3,
      DifferentiableAt ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' pz.2) pz.1
      ∧ (∑ j : Fin 3, ‖fderiv ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' pz.2) pz.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ pz.1 pz.2 * pinL2 ℓ Θ₀) := by
    intro pz
    obtain ⟨w, w₁⟩ := pz
    have hGcont : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (pgKer p Θ₀ w₁)) := by
      show ContDiff ℝ (⊤ : ℕ∞) (fun r : E3 × ((pairFib23 n p → E3) × (E3 × E3)) =>
        star (Θ₀ (insertCoord2 p r.1 w₁ r.2.1)))
      exact contDiff_starC.comp (hΘ₀.comp (contDiff_insertCoord2_comp p contDiff_fst
        contDiff_const (contDiff_fst.comp contDiff_snd)))
    have hbrick : HasFDerivAt (fun q : E3 =>
        ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z * pgKer p Θ₀ w₁ q z)
        (∫ z in pairS23 ℓ p, pgW p Θ₀ A B z • fderiv ℝ (fun q => pgKer p Θ₀ w₁ q z) w) w :=
      hasFDerivAt_setIntegral_weighted hKc hWmeas hWb hGcont w
    have hfib : (fun q : E3 => pairGc23 ℓ p hp Θ₀ A B q w₁)
        = fun q : E3 => ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z * pgKer p Θ₀ w₁ q z := by
      funext q
      exact pairGc23_eq_weight p hp Θ₀ A B q w₁
    have hfd : fderiv ℝ (fun q : E3 => pairGc23 ℓ p hp Θ₀ A B q w₁) w
        = ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z • fderiv ℝ (fun q => pgKer p Θ₀ w₁ q z) w := by
      rw [hfib]
      exact hbrick.fderiv
    have hLwc : Continuous fun z : (pairFib23 n p → E3) × (E3 × E3) =>
        fderiv ℝ (fun q : E3 => pgKer p Θ₀ w₁ q z) w :=
      (continuous_uncurry_fderiv hGcont).comp (continuous_const.prodMk continuous_id)
    obtain ⟨ML, hML⟩ := hKc.exists_bound_of_continuousOn hLwc.continuousOn
    have hInt : Integrable (fun z => pgW p Θ₀ A B z •
        fderiv ℝ (fun q : E3 => pgKer p Θ₀ w₁ q z) w) (volume.restrict (pairS23 ℓ p)) := by
      refine Integrable.of_bound (hWmeas.smul hLwc.aestronglyMeasurable)
        (cA * cB * M₀ * max ML 0) ?_
      refine (ae_restrict_iff' hKmeas).mpr ?_
      filter_upwards with z hz
      rw [norm_smul]
      exact mul_le_mul (hWb z hz) (le_trans (hML z hz) (le_max_left _ _)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hcA hcB) hM₀0)
    have hval : ∀ j : Fin 3, fderiv ℝ (fun q : E3 => pairGc23 ℓ p hp Θ₀ A B q w₁) w
        (EuclideanSpace.single j (1 : ℝ))
        = ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z *
            star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j)) := by
      intro j
      rw [hfd, ContinuousLinearMap.integral_apply hInt]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
        fderiv_pgKer_single hΘ₀ w w₁ z j]
    have hcs : ∀ j : Fin 3,
        ‖∫ z in pairS23 ℓ p, pgW p Θ₀ A B z *
            star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 *
            (∫ x'' in boxPiSet (pairFib23 n p) ℓ,
              ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2)
          * pinL2 ℓ Θ₀ := by
      intro j
      set cj : (pairFib23 n p → E3) × (E3 × E3) → ℂ := fun z =>
        star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j)) with hcj
      have hcjcont : Continuous cj := by
        rw [hcj]
        exact continuous_star.comp
          (((hΘ₀.continuous_fderiv (by simp)).comp
            ((continuous_insertCoord2_fixed_pg23 p w w₁).comp continuous_fst)).clm_apply
            continuous_const)
      have hcjAE : AEStronglyMeasurable cj (volume.restrict (pairS23 ℓ p)) :=
        hcjcont.aestronglyMeasurable
      obtain ⟨Mcj, hMcj⟩ := hKc.exists_bound_of_continuousOn hcjcont.continuousOn
      have hmemW : MemLp (pgW p Θ₀ A B) (ENNReal.ofReal 2) (volume.restrict (pairS23 ℓ p)) :=
        MemLp.of_bound hWmeas (cA * cB * M₀)
          ((ae_restrict_iff' hKmeas).mpr (Filter.Eventually.of_forall fun z hz => hWb z hz))
      have hmemcj : MemLp cj (ENNReal.ofReal 2) (volume.restrict (pairS23 ℓ p)) :=
        MemLp.of_bound hcjAE (max Mcj 0)
          ((ae_restrict_iff' hKmeas).mpr (Filter.Eventually.of_forall fun z hz =>
            le_trans (hMcj z hz) (le_max_left _ _)))
      have hsq := cs_integral hmemW hmemcj
      have hcjint : (∫ z in pairS23 ℓ p, ‖cj z‖ ^ 2)
          = ℓ ^ 6 * ∫ x'' in boxPiSet (pairFib23 n p) ℓ,
              ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2 := by
        have hfc : Continuous fun x'' : pairFib23 n p → E3 =>
            ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2 :=
          ((((hΘ₀.continuous_fderiv (by simp)).comp
            (continuous_insertCoord2_fixed_pg23 p w w₁)).clm_apply continuous_const).norm).pow 2
        have hfint : IntegrableOn (fun x'' : pairFib23 n p → E3 =>
            ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2)
            (boxPiSet (pairFib23 n p) ℓ) :=
          hfc.continuousOn.integrableOn_compact (isCompact_boxPiSet hℓ)
        rw [← pairS23_setIntegral_fst hℓ p hfint]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hcj, norm_star]
      have hdj : (0 : ℝ) ≤ ∫ x'' in boxPiSet (pairFib23 n p) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2 :=
        integral_nonneg fun x'' => by positivity
      calc ‖∫ z in pairS23 ℓ p, pgW p Θ₀ A B z *
              star (fderiv ℝ Θ₀ (insertCoord2 p w w₁ z.1) (slotDirVec p.1 j))‖ ^ 2
          = ‖∫ z in pairS23 ℓ p, pgW p Θ₀ A B z * cj z‖ ^ 2 := by rw [hcj]
        _ ≤ (∫ z in pairS23 ℓ p, ‖pgW p Θ₀ A B z‖ ^ 2)
              * (∫ z in pairS23 ℓ p, ‖cj z‖ ^ 2) := hsq
        _ ≤ (cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀) * (ℓ ^ 6 * ∫ x'' in boxPiSet (pairFib23 n p) ℓ,
              ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2) := by
            rw [hcjint]
            exact mul_le_mul_of_nonneg_right hW2 (mul_nonneg (by positivity) hdj)
        _ = cA ^ 2 * cB ^ 2 * ℓ ^ 6 *
              (∫ x'' in boxPiSet (pairFib23 n p) ℓ,
                ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2)
            * pinL2 ℓ Θ₀ := by ring
    constructor
    · rw [hfib]
      exact hbrick.differentiableAt
    · have hsum : (∑ j : Fin 3, ‖fderiv ℝ (fun q : E3 => pairGc23 ℓ p hp Θ₀ A B q w₁) w
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ ∑ j : Fin 3, cA ^ 2 * cB ^ 2 * ℓ ^ 6 *
              (∫ x'' in boxPiSet (pairFib23 n p) ℓ,
                ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2)
            * pinL2 ℓ Θ₀ :=
        Finset.sum_le_sum fun j _ => by rw [hval j]; exact hcs j
      have hfix : (∑ j : Fin 3, cA ^ 2 * cB ^ 2 * ℓ ^ 6 *
              (∫ x'' in boxPiSet (pairFib23 n p) ℓ,
                ‖fderiv ℝ Θ₀ (insertCoord2 p w w₁ x'') (slotDirVec p.1 j)‖ ^ 2)
            * pinL2 ℓ Θ₀)
          = cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ w w₁ * pinL2 ℓ Θ₀ := by
        rw [dirX23, Finset.mul_sum, Finset.sum_mul]
      exact le_trans hsum (le_of_eq hfix)
  exact ⟨fun pz => (main pz).1, fun pz => (main pz).2⟩

end Work.BoseBoxFock

end
