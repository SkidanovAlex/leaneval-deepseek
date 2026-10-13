/-
# `FTS/PhiStar/Honesty/SlotsLimit/IBPsub.Iterate`

Iterated integrations by parts: the plain iterates `∂_z^j`, `∂_θ^i` (with the sign `(-1)^j`,
`(-1)^i`) and the weighted transposes `D_z^j`, `D_θ^i` (whose transposes are the iterates of
`DzStar`, `DthStar` from `Defs.lean`), together with the mixed transposition which is used to
pass from `mixed j i (slot_r f)` to `slot_r f` against `mixedStar j i φ`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Master

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Pointwise product rules for the weighted factors -/

/-- `∂_z(z · ψ) = ψ + z ∂_zψ`. -/
theorem pz_mul_z {ψ : ℝ → ℝ → ℝ} (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => z * ψ z θ) z θ
      = ψ z θ + z * Work.Spaces.pz ψ z θ := by
  have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z' : ℝ => ψ z' θ) (Work.Spaces.pz ψ z θ) z :=
    ((hψ.smooth.comp (contDiff_id.prodMk (contDiff_const (c := θ)))).differentiable
      (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have hmul : HasDerivAt (fun z' : ℝ => z' * ψ z' θ)
      (1 * ψ z θ + z * Work.Spaces.pz ψ z θ) z := h1.mul h2
  show deriv (fun z' : ℝ => z' * ψ z' θ) z = ψ z θ + z * Work.Spaces.pz ψ z θ
  rw [hmul.deriv]
  ring

/-- `∂_θ(sin 2θ · ψ) = sin 2θ ∂_θψ + 2 cos 2θ · ψ`. -/
theorem pth_mul_sin {ψ : ℝ → ℝ → ℝ} (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth ψ z θ
        + 2 * Real.cos (2 * θ) * ψ z θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
      (2 * Real.cos (2 * θ)) θ := by
    have h := ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    simpa only [id_eq, mul_one, mul_comm (Real.cos (2 * θ))] using h
  have h2 : HasDerivAt (fun θ' : ℝ => ψ z θ') (Work.Spaces.pth ψ z θ) θ :=
    ((hψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by norm_num)).differentiableAt (x := θ) |>.hasDerivAt
  have hmul : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * ψ z θ')
      (2 * Real.cos (2 * θ) * ψ z θ + Real.sin (2 * θ) * Work.Spaces.pth ψ z θ) θ :=
    h1.mul h2
  show deriv (fun θ' : ℝ => Real.sin (2 * θ') * ψ z θ') θ
      = Real.sin (2 * θ) * Work.Spaces.pth ψ z θ + 2 * Real.cos (2 * θ) * ψ z θ
  rw [hmul.deriv]
  ring

/-! ## The iterated plain transposes -/

/-- `∂_z^j (∂_zψ) = ∂_z(∂_z^j ψ)`. -/
theorem pzIter_pz_comm (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pz ψ) = Work.Spaces.pz (Work.Spaces.pzIter j ψ) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-- `∂_θ^i (∂_θψ) = ∂_θ(∂_θ^i ψ)`. -/
theorem pthIter_pth_comm (i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter i (Work.Spaces.pth ψ) = Work.Spaces.pth (Work.Spaces.pthIter i ψ) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- **Iterated integration by parts for `∂_z`.** -/
theorem integral_pzIter_mul_eq : ∀ j : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.pzIter j g p.1 p.2 * ψ p.1 p.2
      = (-1 : ℝ) ^ j * ∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pzIter j ψ p.1 p.2
  | 0, g, ψ, hg, hψ => by simp
  | (j + 1), g, ψ, hg, hψ => by
      have hpg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter j g) :=
        Work.FTS.EllipticEst.SmoothOpen.pzIter hg j
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.pzIter (j + 1) g p.1 p.2 * ψ p.1 p.2
          = -∫ p : ℝ × ℝ,
              Work.Spaces.pzIter j g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 :=
        integral_pz_mul_eq_neg (g := Work.Spaces.pzIter j g) (ψ := ψ) hpg hψ
      rw [hstep]
      rw [integral_pzIter_mul_eq j (ψ := Work.Spaces.pz ψ) hg (testQ0_pz hψ)]
      rw [pzIter_pz_comm j ψ, ← Work.Spaces.pzIter_succ]
      rw [pow_succ]
      ring

/-- **Iterated integration by parts for `∂_θ`.** -/
theorem integral_pthIter_mul_eq : ∀ i : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.pthIter i g p.1 p.2 * ψ p.1 p.2
      = (-1 : ℝ) ^ i * ∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pthIter i ψ p.1 p.2
  | 0, g, ψ, hg, hψ => by simp
  | (i + 1), g, ψ, hg, hψ => by
      have hpg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i g) :=
        smoothOpen_pthIter hg i
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.pthIter (i + 1) g p.1 p.2 * ψ p.1 p.2
          = -∫ p : ℝ × ℝ,
              Work.Spaces.pthIter i g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 :=
        integral_pth_mul_eq_neg (g := Work.Spaces.pthIter i g) (ψ := ψ) hpg hψ
      rw [hstep]
      rw [integral_pthIter_mul_eq i (ψ := Work.Spaces.pth ψ) hg (testQ0_pth hψ)]
      rw [pthIter_pth_comm i ψ, ← Work.Spaces.pthIter_succ]
      rw [pow_succ]
      ring

/-! ## The weighted transposes `D_z`, `D_θ` and their iterates -/

/-- **Integration by parts for `D_z = z ∂_z`**: the transpose `DzStar ψ = -(z ∂_zψ + ψ)`. -/
theorem integral_Dz_mul_eq {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.Dz g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DzStar ψ p.1 p.2 := by
  have hzψ : TestQ0 (fun z θ => z * ψ z θ) := by
    simpa using testQ0_zpow_mul 1 hψ
  have h1 : ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * (p.1 * ψ p.1 p.2)
      = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2 :=
    integral_pz_mul_eq_neg hg hzψ
  calc ∫ p : ℝ × ℝ, Work.Spaces.Dz g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * (p.1 * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Work.Spaces.Dz]; ring
    _ = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2 := h1
    _ = ∫ p : ℝ × ℝ,
          -(g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2) :=
        (MeasureTheory.integral_neg _).symm
    _ = ∫ p : ℝ × ℝ, g p.1 p.2 * DzStar ψ p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show -(g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2)
            = g p.1 p.2 * DzStar ψ p.1 p.2
        rw [pz_mul_z hψ p.1 p.2]
        simp only [DzStar, Work.Spaces.Dz]; ring

/-- **Integration by parts for `D_θ = sin 2θ · ∂_θ`**: the transpose
`DthStar ψ = -(sin 2θ ∂_θψ + 2 cos 2θ · ψ)`. -/
theorem integral_Dth_mul_eq {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.Dth g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DthStar ψ p.1 p.2 := by
  have hsψ : TestQ0 (fun z θ => Real.sin (2 * θ) * ψ z θ) := testQ0_sin_mul hψ
  have h1 : ∫ p : ℝ × ℝ,
        Work.Spaces.pth g p.1 p.2 * (Real.sin (2 * p.2) * ψ p.1 p.2)
      = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2 :=
    integral_pth_mul_eq_neg hg hsψ
  calc ∫ p : ℝ × ℝ, Work.Spaces.Dth g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ,
          Work.Spaces.pth g p.1 p.2 * (Real.sin (2 * p.2) * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Work.Spaces.Dth]; ring
    _ = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2 := h1
    _ = ∫ p : ℝ × ℝ,
          -(g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2) :=
        (MeasureTheory.integral_neg _).symm
    _ = ∫ p : ℝ × ℝ, g p.1 p.2 * DthStar ψ p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show -(g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2)
            = g p.1 p.2 * DthStar ψ p.1 p.2
        rw [pth_mul_sin hψ p.1 p.2]
        simp only [DthStar, Work.Spaces.Dth]; ring

/-- **Iterated integration by parts for `D_z`**: the transpose is the iterate of `DzStar`. -/
theorem integral_DzIter_mul_eq : ∀ j : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.DzIter j g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DzIterStar j ψ p.1 p.2
  | 0, g, ψ, hg, hψ => rfl
  | (j + 1), g, ψ, hg, hψ => by
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.DzIter (j + 1) g p.1 p.2 * ψ p.1 p.2
          = ∫ p : ℝ × ℝ,
              Work.Spaces.DzIter j g p.1 p.2 * DzStar ψ p.1 p.2 :=
        integral_Dz_mul_eq (g := Work.Spaces.DzIter j g) (ψ := ψ)
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hg j) hψ
      rw [hstep]
      exact integral_DzIter_mul_eq j (ψ := DzStar ψ) hg (testQ0_DzStar hψ)

/-- **Iterated integration by parts for `D_θ`**: the transpose is the iterate of `DthStar`. -/
theorem integral_DthIter_mul_eq : ∀ i : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.DthIter i g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DthIterStar i ψ p.1 p.2
  | 0, g, ψ, hg, hψ => rfl
  | (i + 1), g, ψ, hg, hψ => by
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.DthIter (i + 1) g p.1 p.2 * ψ p.1 p.2
          = ∫ p : ℝ × ℝ,
              Work.Spaces.DthIter i g p.1 p.2 * DthStar ψ p.1 p.2 :=
        integral_Dth_mul_eq (g := Work.Spaces.DthIter i g) (ψ := ψ)
          (Work.FTS.EllipticEst.SmoothOpen.DthIter hg i) hψ
      rw [hstep]
      exact integral_DthIter_mul_eq i (ψ := DthStar ψ) hg (testQ0_DthStar hψ)

/-- **Integration by parts for a mixed operator** `mixed j i = D_z^j D_θ^i`. -/
theorem integral_mixed_mul_eq (j i : ℕ) {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * mixedStar j i ψ p.1 p.2 := by
  rw [Work.Spaces.mixed]
  rw [integral_DzIter_mul_eq j (ψ := ψ)
    (Work.FTS.EllipticEst.SmoothOpen.DthIter hg i) hψ]
  exact integral_DthIter_mul_eq i (ψ := DzIterStar j ψ) hg (testQ0_DzIterStar hψ j)

end Work.FTS.PhiStar.Honesty.SlotsLimit
