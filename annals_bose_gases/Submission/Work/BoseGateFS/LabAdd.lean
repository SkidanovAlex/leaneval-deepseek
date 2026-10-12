import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.LatBox.kmom_rows
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.LabAdd` — the guarded label arithmetic at the honest cube

The rows `kink.kmom_add` / `kink.kmom_add_inner` of the kinked bundle at the
honest model are the *guarded additivity* of the cube momentum map
`kmomLab ℓ N : Lab N → ℝ³`:

`kmomLab ℓ N (s - k) = kmomLab ℓ N s - kmomLab ℓ N k`

whenever the labels do not wrap.  `Work.BoseB7AK.LatBox.kmom_rows` proves the
additivity of `Work.BoseB7AK.LatBox.kmom (2N+1) ℓ` from explicit
representative bounds; this module identifies the two momentum maps and converts
the *norm* bounds used at the honest model (`‖kmomLab s‖ ≤ X`, `‖kmomLab k‖ ≤ Y`,
`ℓ(X+Y)/(2π) ≤ N`) into those representative bounds.

At the honest model one takes `X = 2K_L√(μa)` (the `f_L` support, factor 2) and
`Y = 2Λ` (the `Ŵ₁` cut-off radius); the cube size condition `N ≥ Ng μ` makes
`ℓ(X+Y)/(2π) ≤ N` hold.
-/

noncomputable section

open scoped BigOperators Pointwise
open scoped Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseBoxFock

/-- `kmomLab` is `Work.BoseB7AK.LatBox.kmom`. -/
theorem kmomLab_eq_latBox (ℓ : ℝ) (N : ℕ) (n : Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N n = Work.BoseB7AK.LatBox.kmom (2 * N + 1) ℓ n := by
  apply WithLp.ofLp_injective
  funext μ
  simp only [Work.BoseBoxFock.kmomLab, Work.BoseB7AK.LatBox.kmom, Work.BoseBoxFock.labVec,
    Work.BoseB4.vec, WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]

/-- The representative bound behind `‖kmomLab ℓ N i‖`: the coordinates of
`labVec N i` are bounded by `ℓ‖kmomLab ℓ N i‖/(2π)`. -/
lemma abs_labVec_le (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (i : Lab N) (μ : Fin 3) :
    |(((Work.BoseBoxFock.labVec N i μ : ℤ)) : ℝ)|
      ≤ ℓ * ‖Work.BoseBoxFock.kmomLab ℓ N i‖ / (2 * π) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set g : Fin 3 → ℝ := fun j => (((Work.BoseBoxFock.labVec N i j : ℤ)) : ℝ) with hg
  -- the coordinate bound in the Euclidean (`L²`) norm
  have h1 : |g μ| ≤ ‖WithLp.toLp 2 g‖ := PiLp.norm_apply_le (WithLp.toLp 2 g) μ
  -- the geometric mean of `vec` and `toLp`
  have h2 : ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N i)‖ = 2 * π * ‖WithLp.toLp 2 g‖ := by
    rw [Work.BoseB4.vec]
    have hf : (fun j : Fin 3 => 2 * Real.pi * (((Work.BoseBoxFock.labVec N i j : ℤ)) : ℝ))
        = (2 * Real.pi) • g := rfl
    rw [hf]
    have hsm : WithLp.toLp 2 ((2 * Real.pi) • g)
        = (2 * Real.pi) • WithLp.toLp 2 g := rfl
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos h2π]
  have h3 : ℓ * ‖Work.BoseBoxFock.kmomLab ℓ N i‖ = 2 * π * ‖WithLp.toLp 2 g‖ := by
    rw [Work.BoseBoxFock.kmomLab, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), h2]
    field_simp
  rw [h3]
  rw [le_div_iff₀ h2π]
  nlinarith [h1, h2π]

/-- **The guarded additivity of `kmomLab`**, in norm form. -/
theorem kmomLab_sub_of_norm_le (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 1 ≤ N)
    (s k : Lab N) (X Y : ℝ) (hs : ‖Work.BoseBoxFock.kmomLab ℓ N s‖ ≤ X)
    (hk : ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ≤ Y)
    (hXY : ℓ * (X + Y) / (2 * π) ≤ (N : ℝ)) :
    Work.BoseBoxFock.kmomLab ℓ N (s - k)
      = Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k := by
  classical
  rw [kmomLab_eq_latBox, kmomLab_eq_latBox, kmomLab_eq_latBox]
  refine (Work.BoseB7AK.LatBox.kmom_rows (n := 2 * N + 1) (Nat.odd_iff.mpr (by omega)) hℓ).2.2.2.2
    (ℓ * X / (2 * π)) (ℓ * Y / (2 * π)) s k ?_ ?_ ?_
  · intro μ
    calc |(((Work.BoseBoxFock.labVec N s μ : ℤ)) : ℝ)|
        ≤ ℓ * ‖Work.BoseBoxFock.kmomLab ℓ N s‖ / (2 * π) := abs_labVec_le ℓ hℓ N s μ
      _ ≤ ℓ * X / (2 * π) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (le_of_lt hℓ))
            (by positivity)
  · intro μ
    calc |(((Work.BoseBoxFock.labVec N k μ : ℤ)) : ℝ)|
        ≤ ℓ * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ / (2 * π) := abs_labVec_le ℓ hℓ N k μ
      _ ≤ ℓ * Y / (2 * π) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (le_of_lt hℓ))
            (by positivity)
  · have hπ : 0 < 2 * π := by positivity
    have hπ0 : 0 < π := Real.pi_pos
    have hXY' : ℓ * (X + Y) ≤ (N : ℝ) * (2 * π) := (div_le_iff₀ hπ).mp hXY
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hfin : 2 * (ℓ * X / (2 * π) + ℓ * Y / (2 * π)) ≤ 2 * (N : ℝ) + 1 := by
      have h1 : ℓ * X / (2 * π) + ℓ * Y / (2 * π) = ℓ * (X + Y) / (2 * π) := by field_simp
      rw [h1]
      have h2 : 2 * (ℓ * (X + Y) / (2 * π)) = ℓ * (X + Y) / π := by field_simp
      rw [h2]
      have h3 : ℓ * (X + Y) / π ≤ 2 * (N : ℝ) := by
        rw [div_le_iff₀ hπ0]
        nlinarith [hXY', hπ0]
      linarith
    exact hfin

end Work.BoseGateFS
