import Mathlib
import Submission.Work.CharCore.isChar_iff_exists_nat_coeffs
import Submission.Work.CharCore.norm_char_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Constituents of a non-negative integral combination attaining its degree

If `f : G → ℂ` is a non-negative integral combination of irreducible characters of the finite
group `G` and `f n = f 1` for some `n : G`, then every irreducible constituent `θ` of `f`
appearing with non-zero coefficient satisfies `θ n = θ 1`.

The argument is the classical extremal one: `‖θ n‖ ≤ θ 1` for every `θ`, so
`Re (θ n) ≤ θ 1`; summing the (manifestly non-negative) defects `c θ (θ 1 - Re (θ n))` against
`f n = f 1` shows that each of them vanishes, hence `Re (θ n) = θ 1` and therefore
`‖θ n‖ = θ 1 = Re (θ n)`, which forces `θ n` to be the non-negative real `θ 1`.
-/

noncomputable section

open Finset

namespace Work.Clifford

theorem irr_apply_eq_one_of_natCoeffs {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    {c : ↥(Work.CharCore.Irr G) → ℕ}
    (hc : f = ∑ θ : ↥(Work.CharCore.Irr G), (c θ : ℂ) • (θ : G → ℂ)) {n : G}
    (hn : f n = f 1) {θ : ↥(Work.CharCore.Irr G)} (hθ : c θ ≠ 0) :
    (θ : G → ℂ) n = (θ : G → ℂ) 1 := by
  classical
  -- Evaluate the defining sum at `n` and at `1`.
  have hfn : f n = ∑ φ : ↥(Work.CharCore.Irr G), (c φ : ℂ) * ((φ : G → ℂ) n) := by
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hf1 : f 1 = ∑ φ : ↥(Work.CharCore.Irr G), (c φ : ℂ) * ((φ : G → ℂ) 1) := by
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Take real parts: `f 1` is the sum of the non-negative terms `c φ * deg φ`.
  have hRe_fn : (f n).re = ∑ φ : ↥(Work.CharCore.Irr G),
      (c φ : ℝ) * ((φ : G → ℂ) n).re := by
    rw [hfn, Complex.re_sum]
    exact Finset.sum_congr rfl fun φ _ => by simp [Complex.mul_re]
  have hRe_f1 : (f 1).re = ∑ φ : ↥(Work.CharCore.Irr G),
      (c φ : ℝ) * (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ) := by
    rw [hf1, Complex.re_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Work.CharCore.irrDeg_spec φ.2]
    simp [Complex.mul_re]
  -- Every term is bounded by the corresponding degree.
  have hle : ∀ φ : ↥(Work.CharCore.Irr G),
      ((φ : G → ℂ) n).re ≤ (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ) := by
    intro φ
    calc ((φ : G → ℂ) n).re ≤ ‖(φ : G → ℂ) n‖ := Complex.re_le_norm _
      _ ≤ (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ) := Work.CharCore.norm_char_le φ.2 n
  -- The two sums agree, since `f n = f 1`.
  have hsumeq : ∑ φ : ↥(Work.CharCore.Irr G), (c φ : ℝ) * ((φ : G → ℂ) n).re
      = ∑ φ : ↥(Work.CharCore.Irr G),
          (c φ : ℝ) * (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ) := by
    rw [← hRe_fn, ← hRe_f1, hn]
  -- Hence each individual term has no defect.
  have hterm : ∀ φ : ↥(Work.CharCore.Irr G),
      (c φ : ℝ) * ((φ : G → ℂ) n).re
        = (c φ : ℝ) * (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ) := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun φ : ↥(Work.CharCore.Irr G) => (c φ : ℝ) * ((φ : G → ℂ) n).re)
      (g := fun φ : ↥(Work.CharCore.Irr G) =>
        (c φ : ℝ) * (Work.CharCore.irrDeg (φ : G → ℂ) : ℝ))
      (fun φ _ => mul_le_mul_of_nonneg_left (hle φ) (Nat.cast_nonneg _))).mp hsumeq
    exact fun φ => h φ (Finset.mem_univ φ)
  have hRθ : ((θ : G → ℂ) n).re = (Work.CharCore.irrDeg (θ : G → ℂ) : ℝ) := by
    have hcpos : (0 : ℝ) < (c θ : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hθ)
    exact mul_left_cancel₀ (ne_of_gt hcpos) (hterm θ)
  -- So the modulus of `θ n` is also the degree, and `θ n` equals its real part.
  have hnormθ : ‖(θ : G → ℂ) n‖ = (Work.CharCore.irrDeg (θ : G → ℂ) : ℝ) :=
    le_antisymm (Work.CharCore.norm_char_le θ.2 n)
      (by rw [← hRθ]; exact Complex.re_le_norm _)
  have hz : (θ : G → ℂ) n = (Work.CharCore.irrDeg (θ : G → ℂ) : ℂ) := by
    have himsq : ((θ : G → ℂ) n).im * ((θ : G → ℂ) n).im = 0 := by
      have h := Complex.normSq_apply ((θ : G → ℂ) n)
      rw [Complex.normSq_eq_norm_sq, hnormθ, hRθ] at h
      nlinarith [h]
    have him : ((θ : G → ℂ) n).im = 0 := mul_self_eq_zero.mp himsq
    have hthis : (θ : G → ℂ) n = (((θ : G → ℂ) n).re : ℂ) :=
      Complex.ext rfl (by simpa using him)
    rw [hthis, hRθ]
    simp
  rw [hz, ← Work.CharCore.irrDeg_spec θ.2]

end Work.Clifford
