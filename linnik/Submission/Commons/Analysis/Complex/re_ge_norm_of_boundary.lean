import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax

noncomputable section

open Complex Set Metric Filter Function

namespace Commons.Analysis.Complex

/-!
# Phragmén–Lindelöf minimum principle on the right half-plane

The main result `re_ge_norm_of_boundary` is the standard *minimum modulus /
Phragmén–Lindelöf* step used in Heath-Brown (1992), §2: two functions holomorphic
on the right half-plane `{z | 0 < z.re}` and continuous on its closure, both
tending to `0` uniformly as `‖z‖ → ∞` in the closed half-plane, satisfy on the
whole closed half-plane the inequality that already holds on the imaginary axis.

More precisely: if `Re F₁ ≥ ‖F₂‖` on the imaginary axis and both `F₁`, `F₂`
decay at infinity inside the closed right half-plane, then
`‖F₂ z‖ ≤ Re (F₁ z)` for every `z` with `0 ≤ z.re`.

The proof passes through a one-function version (a minimum principle for the
real part): if `f` is holomorphic on the right half-plane, continuous on its
closure, `Re f ≥ 0` on the imaginary axis, and `f → 0` at infinity inside the
closed half-plane, then `Re f ≥ 0` everywhere in the half-plane.  That is
obtained by the maximum modulus principle applied to `exp (-f)` on the
half-disks `{0 < z.re ∧ ‖z‖ < R}` (`Complex.norm_le_of_forall_mem_frontier_norm_le`),
letting `R → ∞`.
-/

/-- A point with real part zero lies on the imaginary axis `I · ℝ`. -/
private lemma eq_I_mul_im_of_re_eq_zero {z : ℂ} (hz : z.re = 0) :
    z = Complex.I * (z.im : ℂ) := by
  rw [← Complex.re_add_im z]
  simp [hz, mul_comm]

/-- The unit vector pointing at `w`: `conj w / ‖w‖` has norm at most one
(even for `w = 0`). -/
private lemma norm_star_div_norm_le_one (w : ℂ) : ‖star w / (‖w‖ : ℂ)‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp [hw]
  · have hnormw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    calc
      ‖star w / (‖w‖ : ℂ)‖ = ‖w‖ / ‖w‖ := by
        rw [norm_div]
        congr 1
        · simp
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
      _ = 1 := div_self hnormw0
      _ ≤ 1 := le_rfl

/-- For `w ≠ 0` the real part of `(conj w / ‖w‖) * w` is `‖w‖`. -/
private lemma re_mul_star_div_norm_eq_norm {w : ℂ} (hw : w ≠ 0) :
    ((star w / (‖w‖ : ℂ)) * w).re = ‖w‖ := by
  have hnormw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hprod : (star w / (‖w‖ : ℂ)) * w = (‖w‖ : ℂ) := by
    rw [div_mul_eq_mul_div]
    have hsq : star w * w = (‖w‖ ^ 2 : ℂ) := by
      have h1 : star w * w = ↑(Complex.normSq w) := by
        simpa using (Complex.normSq_eq_conj_mul_self (z := w)).symm
      rw [h1, Complex.normSq_eq_norm_sq]
      exact Complex.ofReal_pow ‖w‖ 2
    rw [hsq]
    field_simp [hnormw0]
  calc
    ((star w / (‖w‖ : ℂ)) * w).re = ((‖w‖ : ℂ)).re := by rw [hprod]
    _ = ‖w‖ := by simp

/-- `Re (μ * w) ≤ ‖w‖` whenever `‖μ‖ ≤ 1`. -/
private lemma mul_re_le_of_norm_le_one {μ w : ℂ} (hμ : ‖μ‖ ≤ 1) : (μ * w).re ≤ ‖w‖ := by
  calc
    (μ * w).re ≤ ‖μ * w‖ := Complex.re_le_norm _
    _ = ‖μ‖ * ‖w‖ := by rw [norm_mul]
    _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg w)
    _ = ‖w‖ := by simp

/-- **Minimum principle for real parts on the right half-plane.**  If `f` is
holomorphic on `{z | 0 < z.re}`, continuous on `{z | 0 ≤ z.re}`, has
`Re f ≥ 0` on the imaginary axis and tends to `0` uniformly at infinity in the
closed half-plane, then `Re f ≥ 0` in the open half-plane. -/
private lemma re_nonneg_of_boundary_nonneg_of_decay {f : ℂ → ℂ}
    (hdf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hcf : ContinuousOn f {z | 0 ≤ z.re})
    (hbd : ∀ t : ℝ, 0 ≤ (f (Complex.I * (t : ℂ))).re)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ → ‖f z‖ < ε) :
    ∀ z : ℂ, 0 < z.re → 0 ≤ (f z).re := by
  intro z0 hz0
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  rcases hdec ε hε with ⟨R₀, hR₀⟩
  let R : ℝ := max R₀ (‖z0‖ + 1)
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ ‖z‖ < R}
  let g : ℂ → ℂ := fun z => Complex.exp (-(f z))
  have hR0le : R₀ ≤ R := le_max_left _ _
  have hz0norm : ‖z0‖ < R := by
    dsimp [R]
    exact lt_of_lt_of_le (lt_add_one ‖z0‖) (le_max_right R₀ (‖z0‖ + 1))
  have hz0U : z0 ∈ U := ⟨hz0, hz0norm⟩
  have hcl0 : z0 ∈ closure U := subset_closure hz0U
  have hbdd : Bornology.IsBounded U := by
    refine (Metric.isBounded_iff_subset_ball (0 : ℂ)).2 ⟨R, ?_⟩
    intro z hz
    rw [mem_ball_iff_norm, sub_zero]
    exact hz.2
  have hUopen : IsOpen U := by
    have hUeq : U = {z : ℂ | 0 < z.re} ∩ {z : ℂ | ‖z‖ < R} := by
      ext z; simp [U]
    rw [hUeq]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (by simpa [ball_zero_eq] using (isOpen_ball (x := (0 : ℂ)) (ε := R)))
  have hcl_re : IsClosed {z : ℂ | 0 ≤ z.re} := by
    simpa using (isClosed_le (f := fun _ : ℂ => (0 : ℝ)) (g := Complex.re)
      continuous_const Complex.continuous_re)
  have hclU_re : closure U ⊆ {z : ℂ | 0 ≤ z.re} := by
    have hsub : U ⊆ {z : ℂ | 0 ≤ z.re} := by
      intro z hz; exact le_of_lt hz.1
    rw [← hcl_re.closure_eq]
    exact closure_mono hsub
  have hIntU : interior U = U := hUopen.interior_eq
  have hdU : DifferentiableOn ℂ f U := hdf.mono (by intro z hz; exact hz.1)
  have hdg : DiffContOnCl ℂ g U := by
    refine ⟨?_, ?_⟩
    · dsimp [g]
      exact (hdU.neg).cexp
    · dsimp [g]
      exact Complex.continuous_exp.comp_continuousOn ((hcf.mono hclU_re).neg)
  have hC : ∀ w ∈ frontier U, ‖g w‖ ≤ Real.exp ε := by
    intro w hw
    have hwcl : w ∈ closure U := frontier_subset_closure hw
    have hwre : 0 ≤ w.re := hclU_re hwcl
    have hwU : w ∉ U := by
      intro hwUmem
      have hwint : w ∈ interior U := by rw [hIntU]; exact hwUmem
      exact (mem_frontier_iff_notMem_interior hwUmem).mp hw hwint
    have hnorm : ‖g w‖ = Real.exp (-(f w).re) := by
      dsimp [g]
      rw [Complex.norm_exp, Complex.neg_re]
    rw [hnorm]
    exact Real.exp_le_exp.mpr (by
      have hsplit : w.re = 0 ∨ R ≤ ‖w‖ := by
        by_cases hwre0 : w.re = 0
        · exact Or.inl hwre0
        · right
          apply le_of_not_gt
          intro hwlt
          have hwrepos : 0 < w.re := lt_of_le_of_ne hwre (by
            exact fun h : (0 : ℝ) = w.re => hwre0 h.symm)
          exact hwU ⟨hwrepos, hwlt⟩
      rcases hsplit with hwre0 | hRw
      · have hw_axis : w = Complex.I * (w.im : ℂ) := eq_I_mul_im_of_re_eq_zero hwre0
        have hb : 0 ≤ (f (Complex.I * (w.im : ℂ))).re := hbd w.im
        have hrepos : 0 ≤ (f w).re := by
          rw [← hw_axis] at hb
          exact hb
        linarith
      · have hfε : ‖f w‖ < ε := hR₀ w hwre (le_trans hR0le hRw)
        have hb1 : -(f w).re ≤ |(f w).re| := neg_le_abs (f w).re
        have hb2 : |(f w).re| ≤ ‖f w‖ := abs_re_le_norm (f w)
        linarith)
  have hmm : ‖g z0‖ ≤ Real.exp ε :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (E := ℂ) (f := g) (U := U) hbdd hdg hC hcl0
  have hres : Real.exp (-(f z0).re) ≤ Real.exp ε := by
    simpa [g, Complex.norm_exp, Complex.neg_re] using hmm
  have hε' : -(f z0).re ≤ ε := Real.exp_le_exp.mp hres
  linarith

/-- If `F₁`, `F₂` are holomorphic on the right half-plane, continuous on its
closure, `Re F₁ ≥ ‖F₂‖` on the imaginary axis, and both decay to `0` uniformly
at infinity inside the closed right half-plane, then `‖F₂ z‖ ≤ Re (F₁ z)`
throughout the closed right half-plane. -/
theorem re_ge_norm_of_boundary {F1 F2 : ℂ → ℂ}
    (hd1 : DifferentiableOn ℂ F1 {z | 0 < z.re})
    (hd2 : DifferentiableOn ℂ F2 {z | 0 < z.re})
    (hc1 : ContinuousOn F1 {z | 0 ≤ z.re})
    (hc2 : ContinuousOn F2 {z | 0 ≤ z.re})
    (hbd : ∀ t : ℝ, 0 ≤ (F1 (Complex.I * (t : ℂ))).re - ‖F2 (Complex.I * (t : ℂ))‖)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
        ‖F1 z‖ < ε ∧ ‖F2 z‖ < ε) :
    ∀ z : ℂ, 0 ≤ z.re → ‖F2 z‖ ≤ (F1 z).re := by
  intro z hz
  by_cases hz0 : z.re = 0
  · -- `z` lies on the imaginary axis: this is exactly the boundary hypothesis
    have hz_axis : z = Complex.I * (z.im : ℂ) := eq_I_mul_im_of_re_eq_zero hz0
    have h := hbd z.im
    rw [← hz_axis] at h
    linarith
  · -- `z` is in the open half-plane
    have hzpos : 0 < z.re := lt_of_le_of_ne hz (Ne.symm hz0)
    let μ : ℂ := star (F2 z) / (‖F2 z‖ : ℂ)
    let f : ℂ → ℂ := fun w => F1 w - μ * F2 w
    have hμnorm : ‖μ‖ ≤ 1 := norm_star_div_norm_le_one (F2 z)
    have hdf : DifferentiableOn ℂ f {z | 0 < z.re} := by
      dsimp [f, μ]
      exact hd1.sub (hd2.const_mul (star (F2 z) / (‖F2 z‖ : ℂ)))
    have hcf : ContinuousOn f {z | 0 ≤ z.re} := by
      dsimp [f, μ]
      exact hc1.sub (hc2.const_mul (star (F2 z) / (‖F2 z‖ : ℂ)))
    have hfbd : ∀ t : ℝ, 0 ≤ (f (Complex.I * (t : ℂ))).re := by
      intro t
      have h := hbd t
      have hle : (μ * F2 (Complex.I * (t : ℂ))).re ≤ ‖F2 (Complex.I * (t : ℂ))‖ :=
        mul_re_le_of_norm_le_one hμnorm
      dsimp [f]
      linarith
    have hfdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ,
        ∀ w : ℂ, 0 ≤ w.re → R ≤ ‖w‖ → ‖f w‖ < ε := by
      intro ε hε
      have hε2 : 0 < ε / 2 := by linarith
      rcases hdec (ε / 2) hε2 with ⟨R1, hR1⟩
      rcases hdec (ε / 2) hε2 with ⟨R2, hR2⟩
      refine ⟨max R1 R2, ?_⟩
      intro w hw hRw
      have hw1 : R1 ≤ ‖w‖ := le_trans (le_max_left R1 R2) hRw
      have hw2 : R2 ≤ ‖w‖ := le_trans (le_max_right R1 R2) hRw
      rcases hR1 w hw hw1 with ⟨hF1, _⟩
      rcases hR2 w hw hw2 with ⟨_, hF2⟩
      have hμF2 : ‖μ * F2 w‖ ≤ ‖F2 w‖ := by
        calc
          ‖μ * F2 w‖ = ‖μ‖ * ‖F2 w‖ := by rw [norm_mul]
          _ ≤ 1 * ‖F2 w‖ := mul_le_mul_of_nonneg_right hμnorm (norm_nonneg _)
          _ = ‖F2 w‖ := by simp
      have hnorm : ‖f w‖ ≤ ‖F1 w‖ + ‖F2 w‖ := by
        dsimp [f]
        calc
          ‖F1 w - μ * F2 w‖ ≤ ‖F1 w‖ + ‖μ * F2 w‖ := norm_sub_le _ _
          _ ≤ ‖F1 w‖ + ‖F2 w‖ := add_le_add_right hμF2 ‖F1 w‖
      have hlt : ‖F1 w‖ + ‖F2 w‖ < ε := by linarith
      exact lt_of_le_of_lt hnorm hlt
    have hpos : 0 ≤ (f z).re := re_nonneg_of_boundary_nonneg_of_decay hdf hcf hfbd hfdec z hzpos
    have hz2 : (f z).re = (F1 z).re - (μ * F2 z).re := by
      dsimp [f]
    by_cases hw0 : F2 z = 0
    · have hμz : (μ * F2 z).re = 0 := by simp [hw0]
      have hF1re : 0 ≤ (F1 z).re := by
        rw [hz2, hμz, sub_zero] at hpos
        exact hpos
      have hF2 : ‖F2 z‖ = 0 := by simp [hw0]
      linarith
    · have hμz : (μ * F2 z).re = ‖F2 z‖ := by
        dsimp [μ]
        exact re_mul_star_div_norm_eq_norm hw0
      rw [hz2, hμz] at hpos
      linarith

end Commons.Analysis.Complex