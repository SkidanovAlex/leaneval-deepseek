import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## Elementary identities for the `pairGc13` fibre -/

/-- `insertCoord` as an update of the zero configuration. -/
lemma insertCoord_eq_update {n : ℕ} (p : Fin n × Fin n) (w : E3)
    (x : {k : Fin n // k ≠ p.2} → E3) :
    insertCoord p.2 w x = Function.update (insertCoord p.2 (0 : E3) x) p.2 w := by
  funext k
  by_cases hk : k = p.2
  · subst hk; simp [insertCoord]
  · simp [insertCoord, hk]

/-- `confY13` as an update of `insertCoord`. -/
lemma confY13_eq_update {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (y u : E3)
    (x' : {k : Fin n // k ≠ p.2} → E3) :
    confY13 p y u x' = Function.update (insertCoord p.2 u x') p.1 y := by
  funext k
  rw [Function.update_apply]
  by_cases h1 : k = p.1
  · subst h1
    rw [if_pos rfl]
    simp [confY13]
  · rw [if_neg h1]
    by_cases h2 : k = p.2
    · subst h2
      simp [confY13, insertCoord, h1]
    · simp [confY13, insertCoord, h1, h2]

/-- The `w`-fibre `w ↦ star (Θ₀ (insertCoord p.2 w x'))` is differentiable. -/
lemma differentiableAt_star_comp_insertCoord {n : ℕ} {p : Fin n × Fin n} {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (x : {k : Fin n // k ≠ p.2} → E3) (w : E3) :
    DifferentiableAt ℝ (fun q : E3 => star (Θ₀ (insertCoord p.2 q x))) w := by
  have hEq : (fun q : E3 => star (Θ₀ (insertCoord p.2 q x)))
      = fun q : E3 => star (Θ₀ (Function.update (insertCoord p.2 (0 : E3) x) p.2 q)) := by
    funext q; rw [insertCoord_eq_update]
  rw [hEq]
  exact (contDiff_starC.comp (hΘ₀.comp
    (contDiff_update (⊤ : ℕ∞) (insertCoord p.2 (0 : E3) x) p.2))).differentiable (by simp) w

/-- The derivative of the `w`-fibre of `pairGc13`. -/
lemma fderiv_star_comp_insertCoord {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (x : {k : Fin n // k ≠ p.2} → E3) (w v : E3) :
    fderiv ℝ (fun q : E3 => star (Θ₀ (insertCoord p.2 q x))) w v
      = star (fderiv ℝ Θ₀ (insertCoord p.2 w x) (Function.update (0 : Xn n) p.2 v)) := by
  have hins_eq : (fun q : E3 => insertCoord p.2 q x)
      = fun q : E3 => Function.update (insertCoord p.2 (0 : E3) x) p.2 q := by
    funext q; rw [insertCoord_eq_update]
  set T : E3 →L[ℝ] Xn n :=
    ContinuousLinearMap.pi (Pi.single p.2 (ContinuousLinearMap.id ℝ E3)) with hTdef
  have hfderiv : fderiv ℝ (fun q : E3 => insertCoord p.2 q x) w = T := by
    rw [hins_eq, hTdef]
    exact fderiv_update (insertCoord p.2 (0 : E3) x) w
  have hTv : T v = Function.update (0 : Xn n) p.2 v := by
    ext i j
    rw [hTdef]
    simp only [ContinuousLinearMap.pi_apply, Pi.single_apply, Function.update_apply]
    by_cases hi : i = p.2
    · subst hi; simp
    · simp [hi]
  have hdiff : DifferentiableAt ℝ (fun q : E3 => insertCoord p.2 q x) w := by
    rw [hins_eq]
    exact (contDiff_update (⊤ : ℕ∞) (insertCoord p.2 (0:E3) x) p.2).differentiable (by simp) w
  have hT : HasFDerivAt (fun q : E3 => insertCoord p.2 q x) T w := by
    rw [← hfderiv]; exact hdiff.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E3 => Θ₀ (insertCoord p.2 q x))
      ((fderiv ℝ Θ₀ (insertCoord p.2 w x)) ∘L T) w :=
    (hΘ₀.differentiable (by simp) (insertCoord p.2 w x)).hasFDerivAt.comp w hT
  have h2 := h1.star
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hTv]
  simp

/-- Parametric differentiation of `w ↦ ∫ z, Φ w z * c z ∂μ`, in the form in which the two
hypotheses produced by the concrete bounds of the `pairGc13` fibre are available: the
differentiability of the fibre, the measurability of the two families, a uniform bound on a ball
for the derivative, and the integrability of the integrand. -/
theorem hasFDerivAt_integral_mul_const_of_fibres {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    [IsFiniteMeasure μ] {Φ : E3 → Z → ℂ} {c : Z → ℂ} {M : ℝ} {w : E3}
    (hΦd : ∀ z x, DifferentiableAt ℝ (fun w' => Φ w' z) x)
    (hΦm : ∀ᶠ x in 𝓝 w, AEStronglyMeasurable (fun z => Φ x z * c z) μ)
    (hF'm : AEStronglyMeasurable (fun z => c z • fderiv ℝ (fun w' => Φ w' z) w) μ)
    (hM : ∀ᵐ z ∂μ, ∀ x ∈ Metric.closedBall w 1, ‖c z • fderiv ℝ (fun w' => Φ w' z) x‖ ≤ M)
    (hIntF : Integrable (fun z => Φ w z * c z) μ) :
    HasFDerivAt (fun w' => ∫ z, Φ w' z * c z ∂μ)
      (∫ z, c z • fderiv ℝ (fun w' => Φ w' z) w ∂μ) w := by
  refine hasFDerivAt_integral_mul_const (μ := μ) (Φ := Φ) (c := c)
    (s := Metric.closedBall w 1) (M := M) (w₀ := w)
    (Metric.closedBall_mem_nhds w (by norm_num)) hM hΦm hIntF hF'm ?_
  intro z x _
  exact (hΦd z x).hasFDerivAt

theorem pairGc13_fderiv {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (y w v : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w' => Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B w' y) w v
      = ∫ z in (Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) ×ˢ
            (Work.BoseK15.corpusBox.boxL ℓ),
          star (fderiv ℝ Θ₀ (Work.BoseBoxFock.insertCoord p.2 w z.1)
                 (Function.update (0 : Work.BoseDict.Xn n) p.2 v))
            * A (z.1 ⟨p.1, hp⟩) * star (B z.2)
            * Θ₀ (Work.BoseBoxFock.confY13 p y z.2 z.1) := by
  let E : Set (({k : Fin n // k ≠ p.2} → E3) × E3) :=
    boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ
  have hS : IsCompact E :=
    (isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.2}) hℓ).prod
      (by rw [corpusBox_boxL_eq_acube hℓ]; exact Submission.BoseGases.acube_compact hℓ)
  haveI hμfin : IsFiniteMeasure (volume.restrict E) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hS.measure_lt_top)
  let Φ : E3 → (({k : Fin n // k ≠ p.2} → E3) × E3) → ℂ :=
    fun w' z => star (Θ₀ (insertCoord p.2 w' z.1))
  have hΦdef : Φ = fun (w' : E3) (z : ({k : Fin n // k ≠ p.2} → E3) × E3) =>
      star (Θ₀ (insertCoord p.2 w' z.1)) := rfl
  let c : (({k : Fin n // k ≠ p.2} → E3) × E3) → ℂ :=
    fun z => A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1)
  have hcdef : c = fun (z : ({k : Fin n // k ≠ p.2} → E3) × E3) =>
      A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1) := rfl
  -- continuity of the `Y`-configuration factor
  have hconf_cont : Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      confY13 p y z.2 z.1) := by
    have hEq : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => confY13 p y z.2 z.1)
        = fun z => Function.update (insertCoord p.2 z.2 z.1) p.1 y := by
      funext z; exact confY13_eq_update p hp y z.2 z.1
    rw [hEq]
    exact (contDiff_update_comp p.1
      (contDiff_insertCoord_comp p.2 contDiff_snd contDiff_fst) contDiff_const).continuous
  -- measurability of the two families
  have hc_meas : Measurable c := by
    rw [hcdef]
    have h1 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        A (z.1 ⟨p.1, hp⟩)) :=
      hA.comp (((continuous_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2}) : Continuous
        (fun (u : {k : Fin n // k ≠ p.2} → E3) => u ⟨p.1, hp⟩)).comp continuous_fst).measurable)
    have h2 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => star (B z.2)) :=
      continuous_star.measurable.comp (hB.comp continuous_snd.measurable)
    have h3 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        Θ₀ (confY13 p y z.2 z.1)) := (hΘ₀.continuous.comp hconf_cont).measurable
    exact (h1.mul h2).mul h3
  have hΦmeas : ∀ x : E3, Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => Φ x z) := by
    intro x
    have h : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        star (Θ₀ (insertCoord p.2 x z.1))) :=
      ((hΘ₀.continuous.comp
        ((contDiff_insertCoord_comp p.2 contDiff_const contDiff_fst).continuous)).star).measurable
    exact h
  have hΦd : ∀ z x, DifferentiableAt ℝ (fun w' => Φ w' z) x := by
    intro z x
    exact differentiableAt_star_comp_insertCoord hΘ₀ z.1 x
  -- joint regularity of the uncurried family and the partial-derivative identity
  have hPsi_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        star (Θ₀ (insertCoord p.2 q.1 q.2.1))) :=
    contDiff_starC.comp (hΘ₀.comp (contDiff_insertCoord_comp p.2 contDiff_fst
      (contDiff_fst.comp contDiff_snd)))
  have hpt : ∀ (x : E3) (z : ({k : Fin n // k ≠ p.2} → E3) × E3),
      fderiv ℝ (fun w' : E3 => Φ w' z) x
        = (fderiv ℝ (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
              star (Θ₀ (insertCoord p.2 q.1 q.2.1))) (x, z)).comp
            (ContinuousLinearMap.inl ℝ E3 (({k : Fin n // k ≠ p.2} → E3) × E3)) := by
    intro x z
    have hd : HasFDerivAt (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
          star (Θ₀ (insertCoord p.2 q.1 q.2.1)))
        (fderiv ℝ (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
          star (Θ₀ (insertCoord p.2 q.1 q.2.1))) (x, z)) (x, z) :=
      (hPsi_cd.differentiable (by simp) (x, z)).hasFDerivAt
    have h3 := hd.comp (f := fun e : E3 => (e, z)) (x := x) (hasFDerivAt_prodMk_left x z)
    rw [show ((fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
          star (Θ₀ (insertCoord p.2 q.1 q.2.1))) ∘ fun e : E3 => (e, z))
        = fun e : E3 => star (Θ₀ (insertCoord p.2 e z.1)) from rfl] at h3
    exact h3.fderiv
  have hL_cont : Continuous (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
      fderiv ℝ (fun w' : E3 => Φ w' q.2) q.1) := by
    have hfd : Continuous (fderiv ℝ (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        star (Θ₀ (insertCoord p.2 q.1 q.2.1)))) := hPsi_cd.continuous_fderiv (by simp)
    have h1 : Continuous (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        (fderiv ℝ (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
          star (Θ₀ (insertCoord p.2 q.1 q.2.1))) q).comp
            (ContinuousLinearMap.inl ℝ E3 (({k : Fin n // k ≠ p.2} → E3) × E3))) :=
      hfd.clm_comp continuous_const
    rw [show (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
            fderiv ℝ (fun w' : E3 => Φ w' q.2) q.1)
        = fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
            (fderiv ℝ (fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
              star (Θ₀ (insertCoord p.2 q.1 q.2.1))) q).comp
                (ContinuousLinearMap.inl ℝ E3 (({k : Fin n // k ≠ p.2} → E3) × E3))
        from funext (fun q => hpt q.1 q.2)]
    exact h1
  -- the three uniform bounds
  obtain ⟨C₁, hC₁⟩ := hS.exists_bound_of_continuousOn
    ((hΘ₀.continuous.comp hconf_cont).norm.continuousOn)
  have hN₁ : ∀ z ∈ E, ‖Θ₀ (confY13 p y z.2 z.1)‖ ≤ max C₁ 0 := by
    intro z hz
    have h := hC₁ z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact le_trans h (le_max_left _ _)
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn
    (((hΘ₀.continuous.comp
      (contDiff_insertCoord_comp p.2 contDiff_const contDiff_fst).continuous).norm).continuousOn)
  have hN₀ : ∀ z ∈ E, ‖Θ₀ (insertCoord p.2 w z.1)‖ ≤ max C₀ 0 := by
    intro z hz
    have h := hC₀ z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact le_trans h (le_max_left _ _)
  obtain ⟨C₂, hC₂⟩ := ((isCompact_closedBall w (1 : ℝ)).prod hS).exists_bound_of_continuousOn
    hL_cont.continuousOn
  have hM₂ : ∀ x ∈ Metric.closedBall w (1 : ℝ), ∀ z ∈ E,
      ‖fderiv ℝ (fun w' : E3 => Φ w' z) x‖ ≤ max C₂ 0 := by
    intro x hx z hz
    exact le_trans (hC₂ (x, z) ⟨hx, hz⟩) (le_max_left _ _)
  have hc_bound : ∀ z ∈ E,
      ‖c z‖ ≤ ((max cA 0) * (max cB 0)) * (max C₁ 0) := by
    intro z hz
    rw [hcdef]
    have h1 : ‖A (z.1 ⟨p.1, hp⟩)‖ ≤ max cA 0 := le_trans (hAb _) (le_max_left _ _)
    have h2 : ‖star (B z.2)‖ ≤ max cB 0 := by
      rw [norm_star]; exact le_trans (hBb _) (le_max_left _ _)
    have h4 : ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖star (B z.2)‖ ≤ (max cA 0) * (max cB 0) :=
      mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
    calc ‖A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1)‖
        = ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖star (B z.2)‖ * ‖Θ₀ (confY13 p y z.2 z.1)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ((max cA 0) * (max cB 0)) * (max C₁ 0) :=
          mul_le_mul h4 (hN₁ z hz) (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hsmul_bound : ∀ (c₀ : ℂ) (L : E3 →L[ℝ] ℂ), ‖c₀ • L‖ ≤ ‖c₀‖ * ‖L‖ := by
    intro c₀ L
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    show ‖(c₀ • L) v‖ ≤ (‖c₀‖ * ‖L‖) * ‖v‖
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg _)
  have hder_bnd : ∀ x ∈ Metric.closedBall w (1 : ℝ), ∀ z ∈ E,
      ‖c z • fderiv ℝ (fun w' : E3 => Φ w' z) x‖
        ≤ (((max cA 0) * (max cB 0)) * (max C₁ 0)) * (max C₂ 0) := by
    intro x hx z hz
    calc ‖c z • fderiv ℝ (fun w' : E3 => Φ w' z) x‖
        ≤ ‖c z‖ * ‖fderiv ℝ (fun w' : E3 => Φ w' z) x‖ :=
          hsmul_bound _ _
      _ ≤ (((max cA 0) * (max cB 0)) * (max C₁ 0)) * (max C₂ 0) :=
          mul_le_mul (hc_bound z hz) (hM₂ x hx z hz) (norm_nonneg _)
            (mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
  -- the hypotheses of the parametric-differentiation step
  have hM : ∀ᵐ z ∂(volume.restrict E), ∀ x ∈ Metric.closedBall w (1 : ℝ),
      ‖c z • fderiv ℝ (fun w' : E3 => Φ w' z) x‖
        ≤ (((max cA 0) * (max cB 0)) * (max C₁ 0)) * (max C₂ 0) := by
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards with z hz x hx
    exact hder_bnd x hx z hz
  have hΦm : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (fun z => Φ x z * c z) (volume.restrict E) :=
    Filter.Eventually.of_forall fun x => ((hΦmeas x).mul hc_meas).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable
      (fun z => c z • fderiv ℝ (fun w' : E3 => Φ w' z) w) (volume.restrict E) := by
    have hfdmeas : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        fderiv ℝ (fun w' : E3 => Φ w' z) w) :=
      (hL_cont.comp (continuous_const.prodMk continuous_id)).measurable
    exact (hc_meas.smul hfdmeas).aestronglyMeasurable
  have hIntF : Integrable (fun z => Φ w z * c z) (volume.restrict E) := by
    refine Integrable.mono' (g := fun _ : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        (max C₀ 0) * (((max cA 0) * (max cB 0)) * (max C₁ 0)))
      (integrable_const _) ((hΦmeas w).mul hc_meas).aestronglyMeasurable ?_
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards with z hz
    have hΦw : ‖Φ w z‖ ≤ max C₀ 0 := by
      have h2 : ‖Φ w z‖ = ‖Θ₀ (insertCoord p.2 w z.1)‖ := by
        show ‖star (Θ₀ (insertCoord p.2 w z.1))‖ = ‖Θ₀ (insertCoord p.2 w z.1)‖
        rw [norm_star]
      rw [h2]; exact hN₀ z hz
    calc ‖Φ w z * c z‖ = ‖Φ w z‖ * ‖c z‖ := norm_mul _ _
      _ ≤ (max C₀ 0) * (((max cA 0) * (max cB 0)) * (max C₁ 0)) :=
          mul_le_mul hΦw (hc_bound z hz) (norm_nonneg _) (le_max_right _ _)
  -- the derivative of the parametric integral
  have hmain := hasFDerivAt_integral_mul_const_of_fibres (μ := volume.restrict E)
    (Φ := Φ) (c := c) (M := (((max cA 0) * (max cB 0)) * (max C₁ 0)) * (max C₂ 0))
    (w := w) hΦd hΦm hF'm hM hIntF
  -- identify the fibre with the parametric integral
  have hfun : (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y)
      = fun w' => ∫ z, Φ w' z * c z ∂(volume.restrict E) := by
    funext w'
    have hpoint : ∀ z : ({k : Fin n // k ≠ p.2} → E3) × E3,
        star (Θ₀ (insertCoord p.2 w' z.1)) * A (z.1 ⟨p.1, hp⟩) * star (B z.2)
          * Θ₀ (confY13 p y z.2 z.1) = Φ w' z * c z := by
      intro z
      simp only [hΦdef, hcdef]
      ring
    calc pairGc13 ℓ p hp Θ₀ A B w' y
        = ∫ z in E, star (Θ₀ (insertCoord p.2 w' z.1)) * A (z.1 ⟨p.1, hp⟩)
            * star (B z.2) * Θ₀ (confY13 p y z.2 z.1) := rfl
      _ = ∫ z in E, Φ w' z * c z :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = ∫ z, Φ w' z * c z ∂(volume.restrict E) := rfl
  have hfe : fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
      = ∫ z, c z • fderiv ℝ (fun w' : E3 => Φ w' z) w ∂(volume.restrict E) := by
    rw [hfun]
    exact hmain.fderiv
  have hInt_CLM : Integrable (fun z => c z • fderiv ℝ (fun w' : E3 => Φ w' z) w)
      (volume.restrict E) := by
    refine Integrable.mono' (g := fun _ : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        (((max cA 0) * (max cB 0)) * (max C₁ 0)) * (max C₂ 0))
      (integrable_const _) hF'm ?_
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards with z hz
    exact hder_bnd w (Metric.mem_closedBall_self (by norm_num)) z hz
  calc fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w v
      = (∫ z, c z • fderiv ℝ (fun w' : E3 => Φ w' z) w ∂(volume.restrict E)) v := by
          rw [hfe]
    _ = ∫ z, (c z • fderiv ℝ (fun w' : E3 => Φ w' z) w) v ∂(volume.restrict E) :=
          ContinuousLinearMap.integral_apply hInt_CLM v
    _ = ∫ z in E, star (fderiv ℝ Θ₀ (insertCoord p.2 w z.1)
            (Function.update (0 : Xn n) p.2 v))
            * A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show (c z • fderiv ℝ (fun w' : E3 => Φ w' z) w) v
            = star (fderiv ℝ Θ₀ (insertCoord p.2 w z.1)
                (Function.update (0 : Xn n) p.2 v))
              * A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1)
          rw [show (c z • fderiv ℝ (fun w' : E3 => Φ w' z) w) v
              = c z * (fderiv ℝ (fun w' : E3 => Φ w' z) w v) from by
                rw [ContinuousLinearMap.smul_apply, smul_eq_mul]]
          rw [show fderiv ℝ (fun w' : E3 => Φ w' z) w v
              = star (fderiv ℝ Θ₀ (insertCoord p.2 w z.1)
                  (Function.update (0 : Xn n) p.2 v))
              from fderiv_star_comp_insertCoord hp hΘ₀ z.1 w v]
          simp only [hcdef]
          ring
    _ = ∫ z in (Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) ×ˢ
            (Work.BoseK15.corpusBox.boxL ℓ),
          star (fderiv ℝ Θ₀ (Work.BoseBoxFock.insertCoord p.2 w z.1)
                 (Function.update (0 : Work.BoseDict.Xn n) p.2 v))
            * A (z.1 ⟨p.1, hp⟩) * star (B z.2)
            * Θ₀ (Work.BoseBoxFock.confY13 p y z.2 z.1) := rfl

end Work.BoseBoxFock
