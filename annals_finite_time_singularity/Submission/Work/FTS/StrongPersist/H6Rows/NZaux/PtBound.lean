import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/PtBound` — the pointwise bound of the `N`-zero-mode estimate

From the four coefficient majorants (`NZaux/NZ_coefs`), the five terms of `N` are dominated
pointwise on the open quadrant by `9·Kcoef` times the sum of the six slots.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The pointwise bound of the five terms of `N`.**  On the open quadrant `|K θ·N|` is
dominated by `9·Kcoef` times the sum of the six slots. -/
theorem NZ_pt {α M Ce Cs : ℝ} {f Ef Φs : Fn} {Cp Cu Cag : ℝ} {z θ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCp : 0 < Cp) (hCu : 0 < Cu)
    (hCag : 0 < Cag) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2)
    (hRle : |Work.Construction.Rop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hUle : |Work.Construction.Uop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hVle : |Work.Construction.Vop (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag)
    (hFKle : |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag) :
    |Work.Spaces.K θ * Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ) z θ|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * (∑ j : Fin 6, |slots α f j z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  -- =============== 5. the algebra and the pointwise bound
  have hKc0 : 0 ≤ Kcoef α M Ce Cs Cp Cu Cag := (Kcoef_pos hα0 hCp hCu hCag hM0).le
  have hs2ne : Work.Construction.s2 θ ≠ 0 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ, Real.pi_pos])
      (by linarith [hθ2, Real.pi_pos]))
  have hK3 : |Work.Spaces.K θ| ≤ 3 :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hratio : Work.Spaces.K θ / Work.Construction.s2 θ = (3 / 2) * Real.cos θ := by
    have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
      rw [Work.Spaces.K, Real.sin_two_mul]; ring
    have hs2' : Real.sin (2 * θ) ≠ 0 := hs2ne
    rw [hK, show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact mul_div_cancel_right₀ _ hs2'
  have hc1 : |Work.Spaces.K θ * (2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have hsin : (Real.sin θ) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.sin_nonneg_of_mem_Icc ⟨hθ.le, by linarith [Real.pi_pos]⟩)
        (Real.sin_le_one θ)
    have h2 : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ|
        ≤ 2 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hRle (by norm_num)
    have h3 : |(Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      exact le_trans (mul_le_mul_of_nonneg_right hsin (abs_nonneg _)) (by simpa using hFKle)
    have hX : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      calc |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
          ≤ |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|
            + |(Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z| := by
            have h := abs_add_le (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ)
              (-((Real.sin θ) ^ 2 * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            simpa only [sub_eq_add_neg, abs_neg] using h
        _ ≤ 2 * Kcoef α M Ce Cs Cp Cu Cag + Kcoef α M Ce Cs Cp Cu Cag := add_le_add h2 h3
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    rw [abs_mul]
    calc |Work.Spaces.K θ| * |2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ 3 * (3 * Kcoef α M Ce Cs Cp Cu Cag) :=
          mul_le_mul hK3 hX (abs_nonneg _) (by norm_num)
      _ = 9 * Kcoef α M Ce Cs Cp Cu Cag := by ring
  have hc2 : |Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
          + (1 / 2) * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hsplit : Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
          + (1 / 2) * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        = (Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
          + (-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))) := by
      field_simp
      ring
    have hA : |(Work.Spaces.K θ / Work.Construction.s2 θ)
          * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ))| ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [hratio, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2),
        abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc (3 / 2) * |Real.cos θ| * (2 * |Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|)
          ≤ (3 / 2) * (2 * Kcoef α M Ce Cs Cp Cu Cag) := by
            refine mul_le_mul (by linarith [hcos])
              (mul_le_mul_of_nonneg_left hUle (by norm_num)) (by positivity) (by norm_num)
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    have hB : |-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))|
        ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc |Work.Spaces.K θ| * ((1 / 2) * |Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|)
          ≤ 3 * ((1 / 2) * Kcoef α M Ce Cs Cp Cu Cag) := by
            refine mul_le_mul hK3 (mul_le_mul_of_nonneg_left hFKle (by norm_num))
              (by positivity) (by norm_num)
        _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
    rw [hsplit]
    calc |(Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
          + (-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))|
        ≤ |(Work.Spaces.K θ / Work.Construction.s2 θ)
            * (-(2 * Work.Construction.Uop α (Work.Construction.PhiTil α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))|
          + |-(Work.Spaces.K θ * ((1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))| := abs_add_le _ _
      _ ≤ 3 * Kcoef α M Ce Cs Cp Cu Cag + 3 * Kcoef α M Ce Cs Cp Cu Cag := add_le_add hA hB
      _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by linarith [hKc0]
  have hc3 : |Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ)| ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
    have e1 : |-(2 * α)| = 2 * α := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hα0.le]
    have e2 : |Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ)|
        = |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ|) := by
      rw [abs_mul, abs_mul, e1]
    rw [e2]
    calc |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|)
        ≤ 3 * (2 * α * Kcoef α M Ce Cs Cp Cu Cag) := by
          refine mul_le_mul hK3 ?_ (by positivity) (by norm_num)
          have h1 : α * |Work.Construction.Vop (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ α * Kcoef α M Ce Cs Cp Cu Cag :=
            mul_le_mul_of_nonneg_left hVle (le_of_lt hα0)
          calc 2 * α * |Work.Construction.Vop (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ|
              = 2 * (α * |Work.Construction.Vop (Work.Construction.PhiTil α
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ|) := by ring
            _ ≤ 2 * (α * Kcoef α M Ce Cs Cp Cu Cag) :=
                mul_le_mul_of_nonneg_left h1 (by norm_num)
            _ = 2 * α * Kcoef α M Ce Cs Cp Cu Cag := by ring
      _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by
          have h1 : 3 * (2 * α) ≤ 9 := by linarith
          calc 3 * (2 * α * Kcoef α M Ce Cs Cp Cu Cag)
              = (3 * (2 * α)) * Kcoef α M Ce Cs Cp Cu Cag := by ring
            _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := mul_le_mul_of_nonneg_right h1 hKc0
  -- the slot additivity on `F = F_* + f`
  have hDthF : Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ := by
    have hth := Work.FTS.NonlinRows.Rl1.openSlice_pth_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))
      hso hz ⟨hθ, hθ2⟩
    simp only [Work.Spaces.Dth]
    rw [hth]
    ring
  have hDzF : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ := by
    have hpz := Work.FTS.NonlinRows.Rl1.openSlice_pz_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))
      hso hz ⟨hθ, hθ2⟩
    simp only [Work.Spaces.Dz]
    rw [hpz]
    ring
  have hsum6 : (∑ j : Fin 6, |slots α f j z θ|)
      = |f z θ| + |Work.Spaces.Dth f z θ| + |Work.Spaces.Dz f z θ|
        + |Work.Construction.Fstar α z θ| + |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := by
    simp only [slots, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val]
  have hid : Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = (2 * Work.Construction.Rop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)
        * (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      + (-(2 * (Work.Construction.Uop α (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
            + (1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        * Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      + (-(2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ)
        * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := by
    have hs2' : Real.sin (2 * θ) ≠ 0 := hs2ne
    simp only [Work.Construction.N, Work.Spaces.Dth, Work.Construction.s2]
    field_simp [hs2']
    ring_nf
  rw [hid, hDthF, hDzF]
  have hexp : Work.Spaces.K θ * ((2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)
        * (Work.Construction.Fstar α z θ + f z θ)
      + (-(2 * (Work.Construction.Uop α (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ
            / Work.Construction.s2 θ)
            + (1 / 2) * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
      + (-(2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) (fun z θ => Φs z θ + Ef z θ)) z θ)
          * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ))
      = (Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ) := by
    ring
  rw [hexp]
  have hT1 : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
        * (Work.Construction.Fstar α z θ + f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * |Work.Construction.Fstar α z θ + f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
  have hT2 : |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
        + (1 / 2) * Work.Construction.FK
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
        * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
        * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)
  have hT3 : |(Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
        (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ))
        * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
        * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc3 (abs_nonneg _)
  have htri : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)|
        + |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
        + |(Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)| := by
    have h1 : |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)
          + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                + (1 / 2) * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
              * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)|
          ≤ |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ
                - (Real.sin θ) ^ 2 * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
                * (Work.Construction.Fstar α z θ + f z θ)|
            + |(Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                  (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                    (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                  + (1 / 2) * Work.Construction.FK
                    (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
                * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)| :=
      abs_add_le _ _
    have h2 := abs_add_le ((Work.Spaces.K θ * (2 * Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
              (fun z θ => Φs z θ + Ef z θ)) z θ
            - (Real.sin θ) ^ 2 * Work.Construction.FK
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
            * (Work.Construction.Fstar α z θ + f z θ)
          + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
                (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                  (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
                + (1 / 2) * Work.Construction.FK
                  (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
              * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ))
        ((Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ))
    linarith [h1, h2]
  have hb1 : |Work.Construction.Fstar α z θ + f z θ|
      ≤ |Work.Construction.Fstar α z θ| + |f z θ| := abs_add_le _ _
  have hb2 : |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ|
      ≤ |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth f z θ| :=
    abs_add_le _ _
  have hb3 : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ|
      ≤ |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dz f z θ| :=
    abs_add_le _ _
  have h9 : 0 ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag := by linarith
  calc |(Work.Spaces.K θ * (2 * Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z))
          * (Work.Construction.Fstar α z θ + f z θ)
        + (Work.Spaces.K θ * (-(2 * (Work.Construction.Uop α
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ)
              + (1 / 2) * Work.Construction.FK
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) z)))
            * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ)
        + (Work.Spaces.K θ * (-(2 * α) * Work.Construction.Vop
              (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
                (fun z θ => Φs z θ + Ef z θ)) z θ))
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ)|
      ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag * |Work.Construction.Fstar α z θ + f z θ|
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ|
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ| := by
        linarith [htri, hT1, hT2, hT3]
    _ ≤ 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Construction.Fstar α z θ| + |f z θ|)
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth f z θ|)
        + 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dz f z θ|) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left hb1 h9
        · exact mul_le_mul_of_nonneg_left hb2 h9
        · exact mul_le_mul_of_nonneg_left hb3 h9
    _ = 9 * Kcoef α M Ce Cs Cp Cu Cag
          * (|f z θ| + |Work.Spaces.Dth f z θ| + |Work.Spaces.Dz f z θ|
            + |Work.Construction.Fstar α z θ|
            + |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
            + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|) := by ring
    _ = 9 * Kcoef α M Ce Cs Cp Cu Cag * (∑ j : Fin 6, |slots α f j z θ|) := by rw [hsum6]

end Work.FTS.StrongPersist.H6Rows
