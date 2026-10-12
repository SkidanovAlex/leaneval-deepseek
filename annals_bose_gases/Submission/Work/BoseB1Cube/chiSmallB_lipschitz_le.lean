import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.SectorAux.chiSmallB_lipschitz
import Submission.Work.BoseFixB1S.fibreAeTransfer
import Submission.Work.BoseFixB1S.flatFibDeviationB1
import Submission.Work.BoseFixB1S.flatOmegaAllStateB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.chiSmallB_lipschitz_le`

The *sharp* first-difference (Lipschitz) bound for the two-factor sliding cutoff

    chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓd)⁻¹ • x − u)

at the small-box scale `ℓd`:

    ∃ K ≥ 0, ∀ M ℓ d u x v, 0 < ℓ → 0 < d → d ≤ 1 →
      |chiSmallB M ℓ d u (x+v) − chiSmallB M ℓ d u x|
        ≤ K · chiSmallNormFactor M · (M+1) · (ℓd)⁻¹ · ‖v‖ .

This is the sharp-constant version of `Work.BoseFixB1.SectorAux.chiSmallB_lipschitz`, which
carries the exponentially large `chiSmallDecay M = chiSmallNormFactor M · 4^M` as the sup bound
of the small-box factor.  The improvement comes from bounding the sup of the *unnormalised* bump
`chiSmallBase M` by `1` (each cosine factor of `ζζζ` lies in `[0,1]`, so its `M`-th power too),
so the small-box factor contributes only `chiSmallNormFactor M`, and from the Lipschitz bound
`3πM` for `z ↦ (ζ z₀ ζ z₁ ζ z₂)^M` (a product of three `π`-Lipschitz functions — `ζ = zeta1d`
is `π`-Lipschitz — raised to the `M`-th power).

Assembly: with `A = chiScale ℓ`, `B = chiSmall M ((ℓd)⁻¹· − u)`,
`|A| ≤ chiSupAbs`, `|B| ≤ chiSmallNormFactor M`, `Lip(A) ≤ C/ℓ`
(`Work.BoseFixB1B.exists_lipschitz_chi`) and `Lip(B) ≤ 3πM·chiSmallNormFactor M/(ℓd)`, the
product rule

    A(x+v)B(x+v) − A(x)B(x) = (A(x+v) − A(x))·B(x+v) + A(x)·(B(x+v) − B(x))

gives `K = C + chiSupAbs·3π`; the `1/ℓ` of `Lip(A)` is absorbed into `1/(ℓd)` because `d ≤ 1`.
-/

namespace Work.BoseB1Cube

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The unnormalised cosine-`M`-th-power bump is bounded by `1`: it is
`(ζ z₀ ζ z₁ ζ z₂)^M` with `0 ≤ ζ ≤ 1`. -/
lemma chiSmallBase_abs_le_one (M : ℕ) (z : E3) :
    |Submission.BoseGases.chiSmallBase M z| ≤ 1 := by
  unfold Submission.BoseGases.chiSmallBase
  rw [abs_pow]
  refine pow_le_one₀ (abs_nonneg _) ?_
  rw [abs_mul, abs_mul]
  have h0 := Submission.BoseGases.abs_zeta1d_le_one (z.ofLp 0)
  have h1 := Submission.BoseGases.abs_zeta1d_le_one (z.ofLp 1)
  have h2 := Submission.BoseGases.abs_zeta1d_le_one (z.ofLp 2)
  calc |Submission.BoseGases.zeta1d (z.ofLp 0)| * |Submission.BoseGases.zeta1d (z.ofLp 1)|
        * |Submission.BoseGases.zeta1d (z.ofLp 2)|
      ≤ 1 * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul h0 h1 (abs_nonneg _) (by norm_num)
        · exact h2
        · exact abs_nonneg _
        · norm_num
    _ = 1 := by ring

/-- `chiSmallBase M` is `3πM`-Lipschitz, **uniformly in `M ≥ 0`** (at `M = 0` the function is
the constant `1` and the bound reads `0`). -/
lemma chiSmallBase_lipschitz (M : ℕ) (z w : E3) :
    |Submission.BoseGases.chiSmallBase M z - Submission.BoseGases.chiSmallBase M w|
      ≤ 3 * Real.pi * M * ‖z - w‖ := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hprod := Work.BoseFixB1S.chiLip_prod3_abs_sub_le
    (a0 := Submission.BoseGases.zeta1d (z.ofLp 0))
    (a1 := Submission.BoseGases.zeta1d (z.ofLp 1))
    (a2 := Submission.BoseGases.zeta1d (z.ofLp 2))
    (b0 := Submission.BoseGases.zeta1d (w.ofLp 0))
    (b1 := Submission.BoseGases.zeta1d (w.ofLp 1))
    (b2 := Submission.BoseGases.zeta1d (w.ofLp 2))
    (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_nonneg _)
    (Submission.BoseGases.zeta1d_nonneg _)
    (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_nonneg _)
    (Submission.BoseGases.zeta1d_nonneg _)
    (Submission.BoseGases.zeta1d_le_one _) (Submission.BoseGases.zeta1d_le_one _)
    (Submission.BoseGases.zeta1d_le_one _)
    (Submission.BoseGases.zeta1d_le_one _) (Submission.BoseGases.zeta1d_le_one _)
    (Submission.BoseGases.zeta1d_le_one _)
  have hterm : ∀ j : Fin 3,
      |Submission.BoseGases.zeta1d (z.ofLp j) - Submission.BoseGases.zeta1d (w.ofLp j)|
        ≤ Real.pi * ‖z - w‖ := by
    intro j
    have h := Work.BoseFixB1S.chiLip_zeta1d_lipschitz (z.ofLp j) (w.ofLp j)
    have hd : |z.ofLp j - w.ofLp j| ≤ ‖z - w‖ := by
      have h2 := PiLp.norm_apply_le (z - w) j
      rwa [show (z - w).ofLp j = z.ofLp j - w.ofLp j from rfl, Real.norm_eq_abs] at h2
    calc |Submission.BoseGases.zeta1d (z.ofLp j) - Submission.BoseGases.zeta1d (w.ofLp j)|
        ≤ Real.pi * |z.ofLp j - w.ofLp j| := h
      _ ≤ Real.pi * ‖z - w‖ := mul_le_mul_of_nonneg_left hd hpi
  have hAB : |Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
        * Submission.BoseGases.zeta1d (z.ofLp 2)
        - Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
          * Submission.BoseGases.zeta1d (w.ofLp 2)| ≤ 3 * Real.pi * ‖z - w‖ := by
    linarith [hprod, hterm 0, hterm 1, hterm 2]
  have hA0 : 0 ≤ Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
      * Submission.BoseGases.zeta1d (z.ofLp 2) :=
    mul_nonneg (mul_nonneg (Submission.BoseGases.zeta1d_nonneg _)
      (Submission.BoseGases.zeta1d_nonneg _)) (Submission.BoseGases.zeta1d_nonneg _)
  have hB0 : 0 ≤ Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
      * Submission.BoseGases.zeta1d (w.ofLp 2) :=
    mul_nonneg (mul_nonneg (Submission.BoseGases.zeta1d_nonneg _)
      (Submission.BoseGases.zeta1d_nonneg _)) (Submission.BoseGases.zeta1d_nonneg _)
  have hA1 : Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
      * Submission.BoseGases.zeta1d (z.ofLp 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (Submission.BoseGases.zeta1d_le_one _)
      (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_le_one _))
      (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_le_one _)
  have hB1 : Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
      * Submission.BoseGases.zeta1d (w.ofLp 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (Submission.BoseGases.zeta1d_le_one _)
      (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_le_one _))
      (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_le_one _)
  have hp := Work.BoseFixB1S.chiLip_pow_abs_sub_le hA0 hB0 hA1 hB1 M
  change |(Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
        * Submission.BoseGases.zeta1d (z.ofLp 2)) ^ M
      - (Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
        * Submission.BoseGases.zeta1d (w.ofLp 2)) ^ M| ≤ 3 * Real.pi * M * ‖z - w‖
  calc |(Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
          * Submission.BoseGases.zeta1d (z.ofLp 2)) ^ M
        - (Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
          * Submission.BoseGases.zeta1d (w.ofLp 2)) ^ M|
      ≤ M * |Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
          * Submission.BoseGases.zeta1d (z.ofLp 2)
          - Submission.BoseGases.zeta1d (w.ofLp 0) * Submission.BoseGases.zeta1d (w.ofLp 1)
            * Submission.BoseGases.zeta1d (w.ofLp 2)| := hp
    _ ≤ M * (3 * Real.pi * ‖z - w‖) := mul_le_mul_of_nonneg_left hAB (Nat.cast_nonneg M)
    _ = 3 * Real.pi * M * ‖z - w‖ := by ring

theorem chiSmallB_lipschitz_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℕ) (ℓ d : ℝ) (u x v : EuclideanSpace ℝ (Fin 3)),
      0 < ℓ → 0 < d → d ≤ 1 →
      |Submission.BoseGases.chiSmallB M ℓ d u (x + v)
        - Submission.BoseGases.chiSmallB M ℓ d u x|
      ≤ K * Submission.BoseGases.chiSmallNormFactor M * ((M : ℝ) + 1)
          * (ℓ * d)⁻¹ * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1B.exists_lipschitz_chi
  refine ⟨C + Submission.BoseGases.chiSupAbs * (3 * Real.pi), add_nonneg hC0
    (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg (by positivity)), ?_⟩
  intro M ℓ d u x v hℓ hd hd1
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hℓdinv : 0 ≤ (ℓ * d)⁻¹ := le_of_lt (inv_pos.mpr hℓd)
  have hnf : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hle_inv : ℓ⁻¹ ≤ (ℓ * d)⁻¹ := by
    rw [inv_le_inv₀ hℓ hℓd]
    exact mul_le_of_le_one_right (le_of_lt hℓ) hd1
  -- the `ℓ`-scale factor's derivative
  have hA : |Submission.BoseGases.chiScale ℓ (x + v) - Submission.BoseGases.chiScale ℓ x|
      ≤ C * ℓ⁻¹ * ‖v‖ := by
    have h := Work.BoseFixB1.SectorAux.chiScale_lipschitz hC hℓ (x + v) x
    rwa [add_sub_cancel_left] at h
  -- the sup of the small-box factor
  have hBsup : ∀ w : E3, |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)|
      ≤ Submission.BoseGases.chiSmallNormFactor M := by
    intro w
    rw [Work.BoseFixB1S.chiLip_chiSmall_eq_factor M ((ℓ * d)⁻¹ • w - u), abs_mul,
      abs_of_nonneg hnf]
    calc |Submission.BoseGases.chiSmallBase M ((ℓ * d)⁻¹ • w - u)|
          * Submission.BoseGases.chiSmallNormFactor M
        ≤ 1 * Submission.BoseGases.chiSmallNormFactor M :=
          mul_le_mul_of_nonneg_right (chiSmallBase_abs_le_one M _) hnf
      _ = Submission.BoseGases.chiSmallNormFactor M := one_mul _
  -- the Lipschitz bound of the small-box factor
  have hBlip : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
        - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)|
      ≤ 3 * Real.pi * M * Submission.BoseGases.chiSmallNormFactor M * (ℓ * d)⁻¹ * ‖v‖ := by
    rw [Work.BoseFixB1S.chiLip_chiSmall_eq_factor M ((ℓ * d)⁻¹ • (x + v) - u),
      Work.BoseFixB1S.chiLip_chiSmall_eq_factor M ((ℓ * d)⁻¹ • x - u), ← sub_mul, abs_mul,
      abs_of_nonneg hnf]
    have hdiff : ((ℓ * d)⁻¹ • (x + v) - u) - ((ℓ * d)⁻¹ • x - u) = (ℓ * d)⁻¹ • v := by
      rw [sub_sub_sub_cancel_right, ← smul_sub, add_sub_cancel_left]
    have hz : ‖((ℓ * d)⁻¹ • (x + v) - u) - ((ℓ * d)⁻¹ • x - u)‖ = (ℓ * d)⁻¹ * ‖v‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓdinv]
    have hBL := chiSmallBase_lipschitz M ((ℓ * d)⁻¹ • (x + v) - u) ((ℓ * d)⁻¹ • x - u)
    rw [hz] at hBL
    calc |Submission.BoseGases.chiSmallBase M ((ℓ * d)⁻¹ • (x + v) - u)
          - Submission.BoseGases.chiSmallBase M ((ℓ * d)⁻¹ • x - u)|
          * Submission.BoseGases.chiSmallNormFactor M
        ≤ (3 * Real.pi * M * ((ℓ * d)⁻¹ * ‖v‖)) * Submission.BoseGases.chiSmallNormFactor M :=
          mul_le_mul_of_nonneg_right hBL hnf
      _ = 3 * Real.pi * M * Submission.BoseGases.chiSmallNormFactor M * (ℓ * d)⁻¹ * ‖v‖ := by
          ring
  have hbnd : 0 ≤ C * ℓ⁻¹ * ‖v‖ := mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le))
    (norm_nonneg v)
  have h1 : |(Submission.BoseGases.chiScale ℓ (x + v) - Submission.BoseGases.chiScale ℓ x)
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)|
      ≤ (C * ℓ⁻¹ * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M := by
    rw [abs_mul]
    exact mul_le_mul hA (hBsup (x + v)) (abs_nonneg _) hbnd
  have h2 : |Submission.BoseGases.chiScale ℓ x
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))|
      ≤ Submission.BoseGases.chiSupAbs
          * (3 * Real.pi * M * Submission.BoseGases.chiSmallNormFactor M * (ℓ * d)⁻¹ * ‖v‖) := by
    rw [abs_mul]
    exact mul_le_mul (Submission.BoseGases.chiScale_abs_le_sup ℓ x) hBlip (abs_nonneg _)
      Submission.BoseGases.chiSupAbs_nonneg
  have hkey : Submission.BoseGases.chiSmallB M ℓ d u (x + v)
        - Submission.BoseGases.chiSmallB M ℓ d u x
      = (Submission.BoseGases.chiScale ℓ (x + v) - Submission.BoseGases.chiScale ℓ x)
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
        + Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
    simp only [Submission.BoseGases.chiSmallB]
    ring
  rw [hkey]
  -- the arithmetic: `1/ℓ ≤ 1/(ℓd)`, and `M ≤ M+1`
  have ht1 : (C * ℓ⁻¹ * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M
      ≤ C * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) := by
    have h1' : C * ℓ⁻¹ ≤ C * (ℓ * d)⁻¹ := mul_le_mul_of_nonneg_left hle_inv hC0
    have h2' : (C * ℓ⁻¹) * ‖v‖ ≤ (C * (ℓ * d)⁻¹) * ‖v‖ :=
      mul_le_mul_of_nonneg_right h1' (norm_nonneg v)
    have h3' : ((C * ℓ⁻¹) * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M
        ≤ ((C * (ℓ * d)⁻¹) * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M :=
      mul_le_mul_of_nonneg_right h2' hnf
    calc (C * ℓ⁻¹ * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M
        = ((C * ℓ⁻¹) * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M := by ring
      _ ≤ ((C * (ℓ * d)⁻¹) * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M := h3'
      _ = C * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) := by ring
  have ht2 : Submission.BoseGases.chiSupAbs
        * (3 * Real.pi * M * Submission.BoseGases.chiSmallNormFactor M * (ℓ * d)⁻¹ * ‖v‖)
      ≤ Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M
          * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) :=
    le_of_eq (by ring)
  have hfac : 0 ≤ (ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖ :=
    mul_nonneg (mul_nonneg hℓdinv hnf) (norm_nonneg v)
  have hCK : C + Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M
      ≤ (C + Submission.BoseGases.chiSupAbs * (3 * Real.pi)) * ((M : ℝ) + 1) := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have h1' : C ≤ C * ((M : ℝ) + 1) := le_mul_of_one_le_right hC0 hM1
    have h2' : Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M
        ≤ Submission.BoseGases.chiSupAbs * (3 * Real.pi) * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith : (M : ℝ) ≤ (M : ℝ) + 1)
        (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg (by positivity))
    calc C + Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M
        ≤ C * ((M : ℝ) + 1) + Submission.BoseGases.chiSupAbs * (3 * Real.pi) * ((M : ℝ) + 1) :=
          add_le_add h1' h2'
      _ = (C + Submission.BoseGases.chiSupAbs * (3 * Real.pi)) * ((M : ℝ) + 1) := by ring
  calc |(Submission.BoseGases.chiScale ℓ (x + v) - Submission.BoseGases.chiScale ℓ x)
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
        + Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))|
      ≤ |(Submission.BoseGases.chiScale ℓ (x + v) - Submission.BoseGases.chiScale ℓ x)
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)|
        + |Submission.BoseGases.chiScale ℓ x
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x + v) - u)
                - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))| := abs_add_le _ _
    _ ≤ (C * ℓ⁻¹ * ‖v‖) * Submission.BoseGases.chiSmallNormFactor M
        + Submission.BoseGases.chiSupAbs
            * (3 * Real.pi * M * Submission.BoseGases.chiSmallNormFactor M * (ℓ * d)⁻¹
                * ‖v‖) := add_le_add h1 h2
    _ ≤ C * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖)
        + Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M
            * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) :=
          add_le_add ht1 ht2
    _ = (C + Submission.BoseGases.chiSupAbs * (3 * Real.pi) * M)
          * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) := by ring
    _ ≤ (C + Submission.BoseGases.chiSupAbs * (3 * Real.pi)) * ((M : ℝ) + 1)
          * ((ℓ * d)⁻¹ * Submission.BoseGases.chiSmallNormFactor M * ‖v‖) :=
          mul_le_mul_of_nonneg_right hCK hfac
    _ = (C + Submission.BoseGases.chiSupAbs * (3 * Real.pi))
          * Submission.BoseGases.chiSmallNormFactor M * ((M : ℝ) + 1) * (ℓ * d)⁻¹ * ‖v‖ := by
          ring

end Work.BoseB1Cube
