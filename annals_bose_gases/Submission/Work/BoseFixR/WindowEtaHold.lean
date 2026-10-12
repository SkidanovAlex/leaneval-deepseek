import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.WindowRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.WindowEtaHold`

The `η`-regime of FS's small box (`Work.BoseBoxFix.Adm`-window), at the concrete
box parameters `ℓ = sideAt μ (a v)`, `d = t^{6/323}`, `s = t^{1/323}`
(`t = μ (a v)³`):

    (1/2)·|η|·8π(a v)·((N+1)²)·ℓ⁻³ ≤ μ²(a v)ℓ³ + μ(a v),

where `η = d4Eta Ct R ℓ (2 d s ℓ)⁻¹ v` is D1's loss factor
`η = (1 + d1C·(R/ℓ))·(1 + d1C·(2 d s ℓ)⁻¹·(a v)) − 1`.

## The mathematics

At FS's parameters the two factors of `η` are monomials in the diluteness
`t = μ(a v)³`:

    R/ℓ = (R/(a v))·t^{163/323},       c₀·(a v) = (2 d s ℓ)⁻¹(a v) = t^{156/323}/2.

Both tend to `0` as `t → 0⁺`, so choosing the diluteness threshold `ε₀` small
enough makes each of them at most `δ = 1/10000`:
* `t ≤ (δ·A/(C·R+1))^{323/163}` gives `C·(R/ℓ) ≤ δ`,
* `t ≤ (2δ/(C+1))^{323/156}` gives `C·(c₀·(a v)) ≤ δ`,
with `A = a v`, `C = d1C Ct ≥ 0`.  Hence `0 ≤ η ≤ 2δ + δ² ≤ 1/4000`.

On the other side, the box window `N/ℓ³ ≤ 9μ` and the large-box regime
`1 ≤ μℓ³` (supplied by `Work.BoseFixR.WindowRegime`, which gives the much
stronger `157 ≤ μℓ³`) give `N + 1 ≤ 10 μℓ³`, hence `(N+1)²ℓ⁻³ ≤ 100 μ²ℓ³`.
Therefore

    (1/2)·|η|·8π(a v)·((N+1)²)·ℓ⁻³ ≤ (1/8000)·8π(a v)·100μ²ℓ³ = (π/10)μ²(a v)ℓ³
      ≤ μ²(a v)ℓ³ + μ(a v).

All of this is elementary real arithmetic in the monomials of the diluteness;
the only input from the analytic corpus is `Work.BoseFixR.WindowRegime` (which
supplies the regime `157 ≤ μℓ³` together with `R ≤ ℓ·χ_{R₀}`).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixR

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 0. `d1C ≥ 0` -/

/-- D1's constant is non-negative. -/
lemma d1C_nonneg' (Ct : ℝ) : 0 ≤ Work.SmallBoxA0.d1C Ct := by
  rw [Work.SmallBoxA0.d1C, Submission.BoseGases.d1TargetC]
  exact le_trans (by positivity : (0 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3) (le_max_left _ _)

/-! ## 1. The two diluteness thresholds for the factors of `η` -/

/-- **The threshold making the `R/ℓ` factor of `η` small.**
For `0 < t ≤ (δA/(CR+1))^{323/163}` one has `C·(R/(A·t^{-163/323})) ≤ δ`. -/
lemma eta_u_thresh {A C R δ t : ℝ} (hA : 0 < A) (hR : 0 < R) (hC : 0 ≤ C) (hδ : 0 < δ)
    (ht0 : 0 < t) (ht : t ≤ (δ * A / (C * R + 1)) ^ (323 / 163 : ℝ)) :
    C * (R / (A * Work.BoseBox.fsXp t (-163))) ≤ δ := by
  have hCR : 0 ≤ C * R := mul_nonneg hC hR.le
  have hbase : 0 < δ * A / (C * R + 1) :=
    div_pos (mul_pos hδ hA) (by linarith)
  have hpow : Work.BoseBox.fsXp t 163 ≤ δ * A / (C * R + 1) := by
    have h1 : t ^ (163 / 323 : ℝ)
        ≤ ((δ * A / (C * R + 1)) ^ (323 / 163 : ℝ)) ^ (163 / 323 : ℝ) :=
      Real.rpow_le_rpow ht0.le ht (by norm_num)
    rw [← Real.rpow_mul hbase.le, show (323 / 163 : ℝ) * (163 / 323) = 1 by norm_num,
      Real.rpow_one] at h1
    simpa only [Work.BoseBox.fsXp] using h1
  have hfs : Work.BoseBox.fsXp t (-163) = (Work.BoseBox.fsXp t 163)⁻¹ :=
    (Work.BoseBox.fsXp_inv ht0 163).symm
  rw [hfs]
  have hrw : R / (A * (Work.BoseBox.fsXp t 163)⁻¹) = R * Work.BoseBox.fsXp t 163 / A :=
    div_div_eq_mul_div R A (Work.BoseBox.fsXp t 163)
  rw [hrw]
  have hstep : C * (R * Work.BoseBox.fsXp t 163 / A)
      ≤ C * (R * (δ * A / (C * R + 1)) / A) := by
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hR.le)
      (inv_nonneg.mpr hA.le)
  have hval : C * (R * (δ * A / (C * R + 1)) / A) = δ * (C * R / (C * R + 1)) := by
    have h1 : (C * R + 1) ≠ 0 := by linarith
    have h2 : A ≠ 0 := ne_of_gt hA
    field_simp
  have hfin : δ * (C * R / (C * R + 1)) ≤ δ := by
    have hpos : (0 : ℝ) < C * R + 1 := by linarith
    have hle1 : C * R / (C * R + 1) ≤ 1 := by
      rw [div_le_iff₀ hpos]; linarith
    exact mul_le_of_le_one_right hδ.le hle1
  linarith

/-- **The closed form of `c₀·A`.**  At FS's parameters `d = X⁶`, `s = X`,
`ℓ = A·X^{-163}` (with `X = t^{1/323}`, `t = μA³`), so that
`2 d s ℓ = 2A t^{-156/323}` and `(2 d s ℓ)⁻¹·A = t^{156/323}/2`. -/
lemma c0A_closed {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
        * Work.BoseBox.sideAt μ A)⁻¹ * A = Work.BoseBox.fsXp (μ * A ^ 3) 156 / 2 := by
  have ht : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  have hsℓ : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ * A ^ 3) (-163) :=
    Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  rw [d_eq_fsXp_at, s_eq_fsXp_at, hsℓ]
  have hprod : Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) 1
      * Work.BoseBox.fsXp (μ * A ^ 3) (-163) = Work.BoseBox.fsXp (μ * A ^ 3) (-156) := by
    rw [Work.BoseBox.fsXp_mul ht 6 1, show (6 : ℝ) + 1 = 7 by norm_num,
      Work.BoseBox.fsXp_mul ht 7 (-163)]
    norm_num
  rw [show 2 * Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) 1
        * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-163))
      = 2 * A * (Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) 1
          * Work.BoseBox.fsXp (μ * A ^ 3) (-163)) by ring, hprod]
  rw [← Work.BoseBox.fsXp_inv ht 156]
  have hg : Work.BoseBox.fsXp (μ * A ^ 3) 156 ≠ 0 :=
    ne_of_gt (Work.BoseBox.fsXp_pos ht)
  have hAne : A ≠ 0 := ne_of_gt hA
  field_simp

/-- **The threshold making the `c₀·(a v)` factor of `η` small**, together with
the (trivial) non-negativity of that factor.  For `t = μA³ ≤ (2δ/(C+1))^{323/156}`
one has `C·(c₀·A) ≤ δ` where `c₀ = (2 d s ℓ)⁻¹`. -/
lemma eta_w_thresh {A μ C δ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (ht : μ * A ^ 3 ≤ (2 * δ / (C + 1)) ^ (323 / 156 : ℝ)) :
    0 ≤ ((2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
        * Work.BoseBox.sideAt μ A)⁻¹ * A)
      ∧ C * ((2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
        * Work.BoseBox.sideAt μ A)⁻¹ * A) ≤ δ := by
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  have hcl := c0A_closed hA hμ
  refine ⟨?_, ?_⟩
  · rw [hcl]
    exact div_nonneg (Work.BoseBox.fsXp_nonneg ht0.le) (by norm_num)
  · rw [hcl]
    have hbase : 0 < 2 * δ / (C + 1) := div_pos (by linarith) (by linarith)
    have h1 : (μ * A ^ 3) ^ (156 / 323 : ℝ)
        ≤ ((2 * δ / (C + 1)) ^ (323 / 156 : ℝ)) ^ (156 / 323 : ℝ) :=
      Real.rpow_le_rpow ht0.le ht (by norm_num)
    rw [← Real.rpow_mul hbase.le, show (323 / 156 : ℝ) * (156 / 323) = 1 by norm_num,
      Real.rpow_one] at h1
    have hfs : Work.BoseBox.fsXp (μ * A ^ 3) 156 = (μ * A ^ 3) ^ (156 / 323 : ℝ) := rfl
    rw [hfs]
    have h2 : (μ * A ^ 3) ^ (156 / 323 : ℝ) / 2 ≤ 2 * δ / (C + 1) / 2 := by linarith
    have h3 : C * ((μ * A ^ 3) ^ (156 / 323 : ℝ) / 2) ≤ C * (2 * δ / (C + 1) / 2) :=
      mul_le_mul_of_nonneg_left h2 hC
    have h4 : C * (2 * δ / (C + 1) / 2) = δ * (C / (C + 1)) := by
      have h1 : (C + 1) ≠ 0 := by linarith
      field_simp
    have h5 : δ * (C / (C + 1)) ≤ δ := by
      have hpos : (0 : ℝ) < C + 1 := by linarith
      have hle1 : C / (C + 1) ≤ 1 := by
        rw [div_le_iff₀ hpos]; linarith
      exact mul_le_of_le_one_right hδ.le hle1
    linarith

/-! ## 2. The pure window arithmetic -/

/-- **The `η`-window bound.**  If `1 ≤ μℓ³`, `|η| ≤ 1/4000` and `N/ℓ³ ≤ 9μ`,
then `(1/2)|η|·8πA·(N+1)²·ℓ⁻³ ≤ μ²Aℓ³ + μA`. -/
lemma eta_window_arith {A μ ℓ η : ℝ} {N : ℕ} (hA : 0 < A) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hμℓ : 1 ≤ μ * ℓ ^ 3) (hη : |η| ≤ 1 / 4000)
    (hwin : (N : ℝ) / ℓ ^ 3 ≤ 9 * μ) :
    (1 / 2) * |η| * (8 * Real.pi * A) * (((N : ℝ) + 1) ^ 2) * (ℓ ^ 3)⁻¹
      ≤ μ ^ 2 * A * ℓ ^ 3 + μ * A := by
  have hℓ3pos : 0 < ℓ ^ 3 := pow_pos hℓ 3
  have hinvnn : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr hℓ3pos.le
  have hNle : (N : ℝ) ≤ 9 * μ * ℓ ^ 3 := by
    rw [div_le_iff₀ hℓ3pos] at hwin
    linarith
  have hN1 : ((N : ℝ) + 1) ≤ 10 * μ * ℓ ^ 3 := by nlinarith [hNle, hμℓ]
  have hsq : (((N : ℝ) + 1) ^ 2) ≤ (10 * μ * ℓ ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hN1 2
  have hπ : 0 ≤ 8 * Real.pi * A := by
    have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
    exact (mul_pos h8 hA).le
  have h1 : (1 / 2) * |η| ≤ 1 / 8000 := by linarith [hη]
  have h3 : (1 / 2) * |η| * (8 * Real.pi * A) ≤ (1 / 8000) * (8 * Real.pi * A) :=
    mul_le_mul_of_nonneg_right h1 hπ
  have h4 : (1 / 2) * |η| * (8 * Real.pi * A) * (((N : ℝ) + 1) ^ 2)
      ≤ ((1 / 8000) * (8 * Real.pi * A)) * (10 * μ * ℓ ^ 3) ^ 2 :=
    mul_le_mul h3 hsq (by positivity) (by positivity)
  have h5 := mul_le_mul_of_nonneg_right h4 hinvnn
  have h6 : (1 / 8000) * (8 * Real.pi * A) * (10 * μ * ℓ ^ 3) ^ 2 * (ℓ ^ 3)⁻¹
      = (Real.pi / 10) * (μ ^ 2 * A * ℓ ^ 3) := by
    have h1 : ℓ ^ 3 ≠ 0 := ne_of_gt hℓ3pos
    field_simp
    ring
  have h7 : (Real.pi / 10) * (μ ^ 2 * A * ℓ ^ 3) ≤ μ ^ 2 * A * ℓ ^ 3 :=
    mul_le_of_le_one_left (by positivity) (by linarith [Real.pi_lt_four])
  have h8 : μ ^ 2 * A * ℓ ^ 3 ≤ μ ^ 2 * A * ℓ ^ 3 + μ * A := by
    have : 0 ≤ μ * A := mul_nonneg hμ.le hA.le
    linarith
  calc (1 / 2) * |η| * (8 * Real.pi * A) * (((N : ℝ) + 1) ^ 2) * (ℓ ^ 3)⁻¹
      ≤ (1 / 8000) * (8 * Real.pi * A) * (10 * μ * ℓ ^ 3) ^ 2 * (ℓ ^ 3)⁻¹ := h5
    _ = (Real.pi / 10) * (μ ^ 2 * A * ℓ ^ 3) := h6
    _ ≤ μ ^ 2 * A * ℓ ^ 3 := h7
    _ ≤ μ ^ 2 * A * ℓ ^ 3 + μ * A := h8

/-! ## 3. The `η`-regime at FS's parameters -/

theorem WindowEtaHold {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (Ct : ℝ) (hCt : 0 ≤ Ct) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ →
      (1 / 2) * |Work.BlockBound4.d4Eta Ct R
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) v|
          * (8 * Real.pi * (_root_.BoseGases.a v)) * (((N : ℝ) + 1) ^ 2)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)⁻¹
        ≤ μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          + μ * (_root_.BoseGases.a v) := by
  obtain ⟨εr, hεrpos, hreg⟩ := WindowRegime h hv hv1 hvrad hR hv_supp hav
  set δ : ℝ := 1 / 10000 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; norm_num
  set ε₁ : ℝ := (δ * _root_.BoseGases.a v / (Work.SmallBoxA0.d1C Ct * R + 1)) ^ (323 / 163 : ℝ)
    with hε₁def
  set ε₂ : ℝ := (2 * δ / (Work.SmallBoxA0.d1C Ct + 1)) ^ (323 / 156 : ℝ) with hε₂def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    refine Real.rpow_pos_of_pos ?_ _
    exact div_pos (mul_pos hδpos hav) (by nlinarith [d1C_nonneg' Ct, hR.le])
  have hε₂pos : 0 < ε₂ := by
    rw [hε₂def]
    refine Real.rpow_pos_of_pos ?_ _
    exact div_pos (by linarith) (by linarith [d1C_nonneg' Ct])
  refine ⟨min εr (min ε₁ (min ε₂ 1)),
    lt_min hεrpos (lt_min hε₁pos (lt_min hε₂pos one_pos)), ?_⟩
  intro μ hAdm N hN2 hwin
  obtain ⟨hμ, hdil, hOK⟩ := hAdm
  have htεr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr := le_trans hdil (min_le_left _ _)
  have htε₁ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _))
  have htε₂ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₂ :=
    le_trans hdil (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  obtain ⟨-, hμℓ3, -, -⟩ := hreg μ ⟨hμ, htεr, hOK⟩
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  -- the two factors of `η` are at most `δ`
  have hu_le : Work.SmallBoxA0.d1C Ct * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ≤ δ := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hav hμ]
    refine eta_u_thresh hav hR (d1C_nonneg' Ct) hδpos ht0 ?_
    rw [← hε₁def]
    exact htε₁
  have hw := eta_w_thresh (A := _root_.BoseGases.a v) (μ := μ) (C := Work.SmallBoxA0.d1C Ct)
    (δ := δ) hav hμ (d1C_nonneg' Ct) hδpos (by rw [← hε₂def]; exact htε₂)
  obtain ⟨hw0, hw_le⟩ := hw
  have hu0 : 0 ≤ Work.SmallBoxA0.d1C Ct * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    mul_nonneg (d1C_nonneg' Ct) (div_pos hR hℓpos).le
  -- the `η`-bound
  have hηle : |Work.BlockBound4.d4Eta Ct R (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) v| ≤ 1 / 4000 := by
    have hηeq : Work.BlockBound4.d4Eta Ct R (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) v
        = (1 + Work.SmallBoxA0.d1C Ct * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          * (1 + Work.SmallBoxA0.d1C Ct
              * (((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹)
                * (_root_.BoseGases.a v))) - 1 := by
      simp only [Work.BlockBound4.d4Eta, Work.SmallBoxA0.kinPeta]
      ring
    have key : ∀ u w : ℝ, 0 ≤ u → u ≤ δ → 0 ≤ w → w ≤ δ →
        |(1 + u) * (1 + w) - 1| ≤ 1 / 4000 := by
      intro u w hu0 hu hw0 hw
      have hprod : (1 + u) * (1 + w) - 1 ≤ 2 * δ + δ ^ 2 := by
        nlinarith [mul_le_mul hu hw hw0 hδpos.le, hu0, hw0]
      have hnn : 0 ≤ (1 + u) * (1 + w) - 1 := by nlinarith [hu0, hw0]
      rw [abs_of_nonneg hnn]
      rw [hδdef] at hprod
      have : 2 * (1 / 10000) + (1 / 10000) ^ 2 ≤ 1 / 4000 := by norm_num
      linarith
    have hw0' : 0 ≤ Work.SmallBoxA0.d1C Ct
        * (((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) * (_root_.BoseGases.a v)) :=
      mul_nonneg (d1C_nonneg' Ct) hw0
    rw [hηeq]
    exact key _ _ hu0 hu_le hw0' hw_le
  exact eta_window_arith hav hμ hℓpos (by linarith) hηle hwin

end Work.BoseFixR
