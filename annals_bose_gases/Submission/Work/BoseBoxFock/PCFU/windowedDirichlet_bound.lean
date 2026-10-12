import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.kinetic_le_of_isLowB
import Submission.Work.BoseBoxFock.PCFU.windowedDirichlet_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 1000000

/-! ## The bookkeeping of the window length

The composition below trades the derivative price `2·(M/ℓ)²` of the window against the box scale
`μ²aℓ³`.  Since `ℓ = sideAt μ a = a·(μa³)^{−163/323}` at FS's parameters, the ratio is

  `(M/ℓ)² / (μ²aℓ³) = M²·(μa³)^{169/323}`,

which is `≤ M²` in the whole diluteness range `μa³ ≤ 1`; equivalently `1 ≤ μ²aℓ⁵`.  The next lemma
records exactly this, by converting the closed form `sideAt_eq_rpow` into a *negative* power of the
diluteness parameter. -/

/-- **The window length beats the window derivative**: `1 ≤ μ²·a·(sideAt μ a)⁵` in the diluteness
range `μa³ ≤ 1`.  In closed form (`sideAt_eq_rpow`) the left side is `(μa³)^{−169/323}`, and the
exponent is negative. -/
lemma one_le_mu_sq_mul_sideAt_pow_five {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (ht : μ * a ^ 3 ≤ 1) :
    1 ≤ μ ^ 2 * a * (Work.BoseBox.sideAt μ a) ^ 5 := by
  have ht0 : 0 < μ * a ^ 3 := by positivity
  rw [Work.BoseBox.sideAt_eq_rpow ha hμ]
  have hX : ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ 5
      = (μ * a ^ 3) ^ (-(815 / 323) : ℝ) := by
    have h1 : ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ ((5 : ℕ) : ℝ)
        = (μ * a ^ 3) ^ ((-(163 / 323)) * ((5 : ℕ) : ℝ) : ℝ) :=
      (Real.rpow_mul ht0.le _ _).symm
    rw [← Real.rpow_natCast ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) 5, h1]
    norm_num
  have hmu : μ ^ 2 * a * a ^ 5 = (μ * a ^ 3) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; ring
  have hmain : μ ^ 2 * a * (a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ 5
      = (μ * a ^ 3) ^ (-(169 / 323) : ℝ) := by
    calc μ ^ 2 * a * (a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ 5
        = μ ^ 2 * a * (a ^ 5 * ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ 5) := by rw [mul_pow]
      _ = (μ ^ 2 * a * a ^ 5) * ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) ^ 5 := by ring
      _ = (μ * a ^ 3) ^ (2 : ℝ) * (μ * a ^ 3) ^ (-(815 / 323) : ℝ) := by rw [hmu, hX]
      _ = (μ * a ^ 3) ^ (-(169 / 323) : ℝ) := by
          rw [← Real.rpow_add ht0]; norm_num
  rw [hmain]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht (by norm_num)

/-- **The windowed Dirichlet form of a low box state is `O(μ²aℓ³‖Φ‖²)`.**

This is the composition of the two halves of the localised kinetic estimate:

* the product rule `windowedDirichlet_le` splits the Dirichlet form of `z ↦ χ_ℓ(z)Φ(x[i↦z])` into
  twice the `χ_ℓ(x_i)²`-weighted *fibre* Dirichlet form of `Φ` plus the window price
  `2·(M/ℓ)²·∫_{box}Φ²`;
* `kinetic_le_of_isLowB` bounds the fibre Dirichlet form by `C·μ²aℓ³·normB` for a low state;
* the window price is absorbed into the same scale: by `one_le_mu_sq_mul_sideAt_pow_five`,
  `(M/ℓ)² ≤ M²·μ²aℓ³` in the diluteness range `μa³ ≤ 1` (which `ParamsOK` supplies).

Hence `Cd = 2C + 2M²`. -/
theorem windowedDirichlet_bound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R J ε₀ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 ∧
        2 * R ≤ Work.BoseBoxFock.ellH v μ) →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ i : Fin n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) z *
                  (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          ≤ Cd * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
              * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨M, hM0, hMbd⟩ := Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
  obtain ⟨C, hC0, hC⟩ :=
    Work.BoseBoxFock.PCFU.kinetic_le_of_isLowB v h hv hv1 hvrad hR hv_supp hav
  refine ⟨2 * C + 2 * M ^ 2, by nlinarith [hC0, hM0, sq_nonneg M], ?_⟩
  intro μ hAdm hrange hJ n Φ hnc hnorm hLow i
  have hμ : 0 < μ := hAdm.1
  have hℓeq : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
    Work.BoseBoxFock.ellH_eq_sideAt_of_pos hμ hav
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := by
    rw [hℓeq]; exact Work.BoseBox.sideAt_pos hμ hav
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 :=
    Work.BoseBoxFock.paramsOK_fsParams_le_one hAdm.2.2
  have hnormB : Work.BoseBoxFix.normB v μ n Φ
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hℓeq]
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  have hDbd : ∀ x w : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ)) x w|
        ≤ (M / Work.BoseBoxFock.ellH v μ) * ‖w‖ :=
    fun x w => hMbd (Work.BoseBoxFock.ellH v μ) hℓpos x w
  have hwd := Work.BoseBoxFock.PCFU.windowedDirichlet_le (n := n)
    (ℓ := Work.BoseBoxFock.ellH v μ) (M := M) i hℓpos hM0 hDbd hΦc
  have hkin := hC μ hAdm hrange hJ n Φ hnc hnorm hLow i
  have hwin : 2 * (M / Work.BoseBoxFock.ellH v μ) ^ 2
      ≤ 2 * M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
    have h1le : 1 ≤ μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 5 := by
      rw [hℓeq]
      exact one_le_mu_sq_mul_sideAt_pow_five hav hμ ht1
    have hℓ2 : 0 < (Work.BoseBoxFock.ellH v μ) ^ 2 := pow_pos hℓpos 2
    have hstep : M ^ 2 / (Work.BoseBoxFock.ellH v μ) ^ 2
        ≤ M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
      rw [div_le_iff₀ hℓ2]
      have hring : M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3)
            * (Work.BoseBoxFock.ellH v μ) ^ 2
          = M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 5) := by ring
      rw [hring]
      nlinarith [sq_nonneg M, h1le]
    calc 2 * (M / Work.BoseBoxFock.ellH v μ) ^ 2
        = 2 * (M ^ 2 / (Work.BoseBoxFock.ellH v μ) ^ 2) := by rw [div_pow]
      _ ≤ 2 * (M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3)) := by
          linarith
      _ = 2 * M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3) := by ring
  have hQnn : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hwinQ := mul_le_mul_of_nonneg_right hwin hQnn
  have hkin' : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
        Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) ^ 2 *
          (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
            (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
      ≤ C * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
    rw [← hnormB]; exact hkin
  calc ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
        (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) z *
            (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      ≤ 2 * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
            Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) ^ 2 *
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
          + 2 * (M / Work.BoseBoxFock.ellH v μ) ^ 2
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := hwd
    _ ≤ 2 * (C * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2))
          + 2 * M ^ 2 * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3)
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hkin' (by norm_num)) hwinQ
    _ = (2 * C + 2 * M ^ 2) * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by ring
    _ = (2 * C + 2 * M ^ 2) * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
          * Work.BoseBoxFix.normB v μ n Φ := by rw [hnormB]

end Work.BoseBoxFock.PCFU
