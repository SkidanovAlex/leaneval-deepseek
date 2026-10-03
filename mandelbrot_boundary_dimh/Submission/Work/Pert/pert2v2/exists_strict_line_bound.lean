import Mathlib

/-! # From a pointwise strict bound on the boundary line to a uniform strict bound

**Statement.** Let `f : ℂ → ℂ` be holomorphic on the closed half-plane `{w | w.im ≤ -y₁}`, `1`-periodic
there (`f (w + 1) = f w`), and suppose `‖f w‖ < δ` at every point of the boundary line
`{w | w.im = -y₁}`.  Then there is `δ' < δ` with `‖f w‖ ≤ δ'` on that line.

**Proof.**  Parametrise the line by its real part: `g t := f (t - i y₁)`.  Then `g` is (globally)
`1`-periodic on `ℝ` and continuous, so `t ↦ ‖g t‖` attains its maximum `δ' := ‖g t₀‖` on the compact
fundamental domain `[0,1]`; at `t₀` the hypothesis gives `δ' < δ`.  Every point `w` of the line is
`w = z + k` with `z` of the form `x - i y₁`, `x ∈ [0,1]` and `k = ⌊w.re⌋ ∈ ℤ`; integral
periodicity of `g` (equivalently, iterated use of `f (w+1) = f w` along the line) gives
`‖f w‖ = ‖g w.re‖ = ‖g (w.re - ⌊w.re⌋)‖ ≤ δ'`. -/

namespace Work.Pert.pert2v2

open Set Metric Filter Topology

theorem exists_strict_line_bound {f : ℂ → ℂ} {y₁ δ : ℝ}
    (hdiff : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ f w)
    (hper : ∀ w : ℂ, w.im ≤ -y₁ → f (w + 1) = f w)
    (hlt : ∀ w : ℂ, w.im = -y₁ → ‖f w‖ < δ) :
    ∃ δ', δ' < δ ∧ ∀ w : ℂ, w.im = -y₁ → ‖f w‖ ≤ δ' := by
  -- the parametrisation `t ↦ t - i y₁` of the boundary line
  let g : ℝ → ℂ := fun t => f ((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)
  have him : ∀ t : ℝ, ((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I).im = -y₁ := by
    intro t
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
  -- `g` is `1`-periodic on `ℝ`, because `hper` applies all along the line
  have hgper : Function.Periodic g 1 := by
    intro t
    have h1 : (((t + 1 : ℝ) : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)
        = (((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I) + 1) := by push_cast; ring
    show f (((t + 1 : ℝ) : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)
        = f ((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)
    rw [h1]
    exact hper _ (by rw [him t])
  -- `‖g ·‖` is continuous
  have hgcontAt : ∀ t : ℝ, ContinuousAt (fun t : ℝ => ‖g t‖) t := by
    intro t
    have hmap : Continuous (fun t : ℝ => ((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)) := by fun_prop
    have h1 : ContinuousAt (fun t : ℝ => f ((t : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I)) t :=
      ((hdiff _ (by rw [him t])).continuousAt).comp hmap.continuousAt
    simpa [g] using h1.norm
  have hgcont : ContinuousOn (fun t : ℝ => ‖g t‖) (Set.Icc (0 : ℝ) 1) :=
    fun t _ => (hgcontAt t).continuousWithinAt
  -- the maximum on the compact fundamental domain `[0,1]`
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num)) hgcont
  refine ⟨‖g t₀‖, ?_, ?_⟩
  · simpa [g] using hlt _ (him t₀)
  · intro w hw
    -- write `w` as a point of the parametrised line
    have hwrep : w = ((w.re : ℂ) + ((-y₁ : ℝ) : ℂ) * Complex.I) := by
      have h := Complex.re_add_im w
      rw [hw] at h
      exact h.symm
    rw [hwrep]
    show ‖g w.re‖ ≤ ‖g t₀‖
    -- reduce `w.re` modulo `1` using the integral periodicity of `g`
    have hperf : g w.re = g (w.re - (⌊w.re⌋ : ℝ)) := by
      have h := (hgper.int_mul ⌊w.re⌋) (w.re - (⌊w.re⌋ : ℝ))
      rw [mul_one, sub_add_cancel] at h
      exact h
    rw [hperf]
    apply hmax
    constructor
    · have := Int.floor_le w.re; linarith
    · have := Int.lt_floor_add_one w.re; linarith

end Work.Pert.pert2v2
