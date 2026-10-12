import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.zBall_finite`

The enlargement set of the assembly of `Work.BoseBogFS.ZPLatticeRow`,
`zBall v μ Lam = {n : Fin 3 → ℤ | n ≠ 0 ∧ ‖kAt v μ n‖ ≤ Lam}`, is **finite**
as soon as `0 < ell v μ`: the momenta `kAt v μ n = (ell v μ)⁻¹ • vec n` are the
dual-lattice points, so a bound on `‖kAt v μ n‖` bounds every lattice coordinate
`n i`, and `Fin 3 → ℤ` is `ℤ³`.

Concretely, for `ell v μ > 0` and `n ∈ zBall v μ Lam`,

  `2π·|n i| ≤ ‖vec n‖ = (ell v μ)·‖kAt v μ n‖ ≤ (ell v μ)·Lam`,

hence `|n i| ≤ C := (ell v μ)·Lam/(2π)`, and `{n | ∀ i, |n i| ≤ C}` is a finite
product of finite (bounded) subsets of `ℤ`.
-/

namespace Work.BoseBogFS

open scoped Real

theorem zBall_finite (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ Lam : ℝ) (hℓ : 0 < Work.BoseFixR.ell v μ) :
    (Work.BoseBogFS.zBall v μ Lam).Finite := by
  -- The coordinate bound.  If `Lam < 0` then `C < 0` and the "bound" is
  -- contradictory, which is exactly right: `zBall` is then empty.
  set C : ℝ := Work.BoseFixR.ell v μ * Lam / (2 * Real.pi) with hCdef
  -- A real bound on the integer coordinate makes the set of integers finite.
  have hIntFin : ({m : ℤ | |((m : ℝ))| ≤ C}).Finite := by
    refine (Set.finite_Icc (-(⌈C⌉ : ℤ)) (⌈C⌉ : ℤ)).subset ?_
    intro m hm
    have hm' : |(m : ℝ)| ≤ C := hm
    have h1 : C ≤ ((⌈C⌉ : ℤ) : ℝ) := Int.le_ceil C
    constructor
    · apply (Int.cast_le (R := ℝ)).mp
      push_cast
      have h2 : -|(m : ℝ)| ≤ (m : ℝ) := neg_abs_le _
      linarith
    · apply (Int.cast_le (R := ℝ)).mp
      have h2 : (m : ℝ) ≤ |(m : ℝ)| := le_abs_self _
      linarith
  refine (Set.Finite.pi' (t := fun _ : Fin 3 => {m : ℤ | |(m : ℝ)| ≤ C})
    (fun _ => hIntFin)).subset ?_
  intro n hn i
  obtain ⟨_, hnL⟩ := hn
  -- The `i`-th coordinate of the momentum vector.
  have hvecapp : (Work.BoseB4.vec n).ofLp i = 2 * Real.pi * (n i : ℝ) := by
    rw [Work.BoseB4.vec, PiLp.toLp_apply]
  have hstep1 : ‖(Work.BoseB4.vec n).ofLp i‖ ≤ ‖(Work.BoseB4.vec n)‖ :=
    PiLp.norm_apply_le _ _
  -- `kAt` is `(ell v μ)⁻¹ • vec n` with `ell v μ > 0`.
  have h2 : ‖Work.BoseBogFS.kAt v μ n‖
      = (Work.BoseFixR.ell v μ)⁻¹ * ‖Work.BoseB4.vec n‖ := by
    rw [Work.BoseBogFS.kAt, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hℓ)]
  have h3 : ‖Work.BoseB4.vec n‖ ≤ Work.BoseFixR.ell v μ * Lam := by
    have h4 : (Work.BoseFixR.ell v μ)⁻¹ * ‖Work.BoseB4.vec n‖ ≤ Lam := by
      rw [← h2]; exact hnL
    have h5 := mul_le_mul_of_nonneg_left h4 hℓ.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hℓ)] at h5
  have h6 : 2 * Real.pi * |((n i : ℝ))| ≤ Work.BoseFixR.ell v μ * Lam := by
    have h7 := le_trans hstep1 h3
    rw [hvecapp, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg Real.pi_pos.le] at h7
    linarith
  change |((n i : ℝ))| ≤ Work.BoseFixR.ell v μ * Lam / (2 * Real.pi)
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
  nlinarith [h6]

end Work.BoseBogFS
