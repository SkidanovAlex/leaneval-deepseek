import Mathlib
import Submission.Work.Drive.curvatureAPI

/-!
# Existence of a non-inflection point on a smooth knot

This file proves `Work.Drive.exists_noninflection_point`: every smooth knot
(`IsSmoothKnot`, i.e. an analytic, `period`-periodic, simple, regular closed curve) has at least
one parameter `t ∈ [0, period]` at which the velocity and the acceleration are linearly
independent — a *non-inflection* point.

Equivalently: the curvature (equivalently the cross product `velocity × acceleration`) does not
vanish identically along a smooth knot.  If it did, the velocity would be everywhere parallel to a
fixed direction (its value at `0`), hence the curve would travel along a straight line, and a
straight line is neither periodic with positive period nor simple — contradiction.

The proof is elementary and only uses

* the mean value theorem (both the slope form and the "vanishing derivative on an interval"
  consequence `eq_of_deriv_eq_zero_Icc`), and
* Rolle's theorem on `[0, period]`.

Two reusable helper lemmas are proved first:

* `velocity_eq_smul_initial`: if a differentiable nowhere-vanishing vector field `v` has
  `deriv v t ∥ v t` on `[a,b]`, then `v` is everywhere parallel to `v a` on `[a,b]`
  (proved via the MVT applied to the ratio `⟪v t, v a⟫² / ‖v t‖²`, which is the squared cosine of
  the angle between `v t` and `v a` and is a conserved quantity of the linear ODE `v' = λ v`);
* `affine_of_deriv_parallel`: if `deriv r t ∥ w` for a fixed nonzero `w` on `[a,b]`, then `r` is
  affine with direction `w` on `[a,b]` (proved by applying the MVT to the inner products
  `t ↦ ⟪r t, e⟫` for `e ⊥ w`).
-/

set_option linter.unusedVariables false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Vanishing derivative on an interval implies constancy.**  If `f : ℝ → ℝ` is continuous on
`[a,b]`, differentiable on `(a,b)` and `deriv f` vanishes on `(a,b)`, then `f a = f b`. -/
lemma eq_of_deriv_eq_zero_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (h : ∀ x ∈ Set.Ioo a b, deriv f x = 0) : f a = f b := by
  obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope f hab hf hfd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hdiv : (f b - f a) / (b - a) = 0 := by rw [← hcs, h c hc]
  have hz : f b - f a = 0 := by
    rcases div_eq_zero_iff.mp hdiv with h' | h'
    · exact h'
    · exact absurd h' hba
  linarith

/-- **A vector field with `v' ∥ v` is parallel to its initial value.**  If `v : ℝ → Space` is
differentiable, nowhere vanishing, and `deriv v` is everywhere a multiple of `v` on `[a,b]`, then
`v t` is a multiple of `v a` for every `t ∈ [a,b]`.

The proof studies the scalar function `t ↦ ⟪v t, v a⟫² / ‖v t‖²`, which is the squared cosine of
the angle between `v t` and `v a`: it is conserved along the flow `v' = λ v`, and equals `1` (i.e.
`‖v a‖²`) at `t = a`; conservation forces the orthogonal component of `v t` to vanish. -/
lemma velocity_eq_smul_initial {v : ℝ → Space}
    (hd : Differentiable ℝ v) (hne : ∀ t, v t ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpar : ∀ t ∈ Set.Icc a b, ∃ lam : ℝ, deriv v t = lam • v t) :
    ∀ t ∈ Set.Icc a b, ∃ c : ℝ, v t = c • v a := by
  set M : ℝ → ℝ := fun s => inner ℝ (v s) (v a) with hMdef
  set N : ℝ → ℝ := fun s => inner ℝ (v s) (v s) with hNdef
  have hNpos : ∀ s, 0 < N s := by
    intro s; rw [hNdef]; exact real_inner_self_pos.mpr (hne s)
  have hMd : Differentiable ℝ M := by
    rw [hMdef]; exact Differentiable.inner ℝ hd (differentiable_const (v a))
  have hNd : Differentiable ℝ N := by
    rw [hNdef]; exact Differentiable.inner ℝ hd hd
  have hFd : Differentiable ℝ (M ^ 2 / N) :=
    (hMd.pow 2).div hNd (fun s => ne_of_gt (hNpos s))
  have hFderiv : ∀ s ∈ Set.Ioo a b, deriv (M ^ 2 / N) s = 0 := by
    intro s hs
    obtain ⟨lam, hlam⟩ := hpar s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hMh : HasDerivAt M (lam * M s) s := by
      rw [hMdef]
      have h := (hd s).hasDerivAt.inner ℝ (hasDerivAt_const s (v a))
      rw [hlam] at h
      simpa [real_inner_smul_left] using h
    have hNh : HasDerivAt N (2 * lam * N s) s := by
      rw [hNdef]
      have h := (hd s).hasDerivAt.inner ℝ (hd s).hasDerivAt
      rw [hlam] at h
      rw [real_inner_smul_right, real_inner_smul_left] at h
      have h2 : lam * inner ℝ (v s) (v s) + lam * inner ℝ (v s) (v s)
          = 2 * lam * inner ℝ (v s) (v s) := by ring
      rw [h2] at h
      simpa using h
    have hdiv := (hMh.pow 2).div hNh (ne_of_gt (hNpos s))
    rw [hdiv.deriv, div_eq_zero_iff]
    left
    simp only [Pi.pow_apply]
    ring
  have hconst : ∀ t ∈ Set.Icc a b, M t ^ 2 / N t = M a ^ 2 / N a := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hta | hat
    · rw [← hta]
    · have h := eq_of_deriv_eq_zero_Icc hat hFd.continuous.continuousOn hFd.differentiableOn
        (fun x hx => hFderiv x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩)
      simp only [Pi.div_apply, Pi.pow_apply] at h
      exact h.symm
  have hMa_eq : M a = N a := by simp only [hMdef, hNdef]
  have hFa : M a ^ 2 / N a = N a := by
    rw [hMa_eq, sq]
    exact mul_div_cancel_left₀ (N a) (ne_of_gt (hNpos a))
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hta | hat
  · exact ⟨1, by rw [← hta, one_smul]⟩
  have hconv : (inner ℝ (v t) (v a)) ^ 2 = ‖v a‖ ^ 2 * ‖v t‖ ^ 2 := by
    have h := hconst t ht
    rw [hFa] at h
    simp only [hMdef, hNdef] at h
    rw [div_eq_iff (ne_of_gt (real_inner_self_pos.mpr (hne t)))] at h
    rw [real_inner_self_eq_norm_sq (v a), real_inner_self_eq_norm_sq (v t)] at h
    exact h
  have hq : ‖v a‖ ≠ 0 := norm_ne_zero_iff.mpr (hne a)
  have hproj : inner ℝ (v t - (inner ℝ (v t) (v a) / ‖v a‖ ^ 2) • v a)
      (v t - (inner ℝ (v t) (v a) / ‖v a‖ ^ 2) • v a) = 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (v t) (v a)]
    rw [real_inner_self_eq_norm_sq (v t), real_inner_self_eq_norm_sq (v a)]
    field_simp
    rw [hconv]
    field_simp
    ring
  exact ⟨inner ℝ (v t) (v a) / ‖v a‖ ^ 2, sub_eq_zero.mp (inner_self_eq_zero.mp hproj)⟩

/-- **A curve whose derivative stays parallel to a fixed vector is affine.**  If `r : ℝ → Space` is
differentiable on `[a,b]` and `deriv r` is everywhere a multiple of a fixed nonzero `w`, then `r`
travels along the affine line `r a + ℝ • w`, with the orthogonal-projection formula for the
coefficient. -/
lemma affine_of_deriv_parallel {r : ℝ → Space}
    (hd : Differentiable ℝ r) {a b : ℝ} (hab : a ≤ b) {w : Space} (hw : w ≠ 0)
    (hpar : ∀ t ∈ Set.Icc a b, ∃ c : ℝ, deriv r t = c • w) :
    ∀ t ∈ Set.Icc a b, r t = r a + (inner ℝ (r t - r a) w / ‖w‖ ^ 2) • w := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hta | hat
  · rw [← hta, sub_self, inner_zero_left, zero_div, zero_smul, add_zero]
  set e : Space := (r t - r a) - (inner ℝ (r t - r a) w / ‖w‖ ^ 2) • w with hedef
  have hwe : inner ℝ w e = 0 := by
    rw [hedef, inner_sub_right, real_inner_smul_right, real_inner_comm (r t - r a) w,
      real_inner_self_eq_norm_sq]
    have hq : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    field_simp
    ring
  set ψ : ℝ → ℝ := fun s => inner ℝ (r s) e with hψdef
  have hψd : Differentiable ℝ ψ := by
    rw [hψdef]; exact Differentiable.inner ℝ hd (differentiable_const e)
  have hψderiv : ∀ s ∈ Set.Ioo a t, deriv ψ s = 0 := by
    intro s hs
    obtain ⟨c, hc⟩ := hpar s ⟨le_of_lt hs.1, le_trans (le_of_lt hs.2) ht.2⟩
    rw [hψdef]
    rw [deriv_inner_apply ℝ (hd s) (differentiableAt_const (x := s) e)]
    rw [deriv_const, inner_zero_right, zero_add, hc, real_inner_smul_left, hwe, mul_zero]
  have hψeq : ψ t = ψ a := by
    exact (eq_of_deriv_eq_zero_Icc hat hψd.continuous.continuousOn hψd.differentiableOn
      (fun x hx => hψderiv x hx)).symm
  have hinner : inner ℝ (r t - r a) e = 0 := by
    have h := hψeq
    simp only [hψdef] at h
    rw [inner_sub_left, h, sub_self]
  have hx : r t - r a = e + (inner ℝ (r t - r a) w / ‖w‖ ^ 2) • w := by
    rw [hedef]; abel
  have he : e = 0 := by
    have h1 : inner ℝ e e = 0 := by
      have h2 := hinner
      rw [hx, inner_add_left, real_inner_smul_left, hwe, mul_zero, add_zero] at h2
      exact h2
    exact inner_self_eq_zero.mp h1
  have hsub : r t - r a = (inner ℝ (r t - r a) w / ‖w‖ ^ 2) • w := by
    have h := hx
    rw [he] at h
    simpa using h
  exact sub_eq_iff_eq_add'.mp hsub

theorem exists_noninflection_point {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ t ∈ Set.Icc 0 LeanEval.KnotTheory.Quadrisecant.period,
      LinearIndependent ℝ
        ![LeanEval.KnotTheory.Quadrisecant.velocity r t,
          deriv (LeanEval.KnotTheory.Quadrisecant.velocity r) t] := by
  by_contra hcon
  -- no point of `[0, period]` is a non-inflection point
  have hne : ∀ t ∈ Set.Icc 0 period,
      ¬ LinearIndependent ℝ ![velocity r t, deriv (velocity r) t] := fun t ht hLI =>
    hcon ⟨t, ht, hLI⟩
  have hperiod : 0 < period := by unfold period; positivity
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hvel : Differentiable ℝ (velocity r) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := (contDiff_infty_iff_deriv.mp hs).2
    exact h.differentiable (by simp)
  -- the curvature vector vanishes on the whole period
  have hcross : ∀ t ∈ Set.Icc 0 period, cross3 (velocity r t) (deriv (velocity r) t) = 0 := by
    intro t ht
    by_contra hx
    exact hne t ht
      ((Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent
        (velocity r t) (deriv (velocity r) t)).mp hx)
  -- hence the acceleration is everywhere a multiple of the velocity
  have hpar : ∀ t ∈ Set.Icc 0 period, ∃ lam : ℝ, deriv (velocity r) t = lam • velocity r t := by
    intro t ht
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
      (velocity r t) (deriv (velocity r) t)).mp (hcross t ht) with h0 | ⟨lam, hlam⟩
    · exact absurd h0 (hr.regular t)
    · exact ⟨lam, hlam⟩
  -- the velocity is everywhere parallel to its value at `0`
  have hpar0 : ∀ t ∈ Set.Icc 0 period, ∃ c : ℝ, deriv r t = c • velocity r 0 := by
    intro t ht
    obtain ⟨c, hc⟩ := velocity_eq_smul_initial hvel hr.regular (le_of_lt hperiod) hpar t ht
    exact ⟨c, hc⟩
  -- whence the curve is affine along that direction
  have haff := affine_of_deriv_parallel hrd (le_of_lt hperiod) (hr.regular 0) hpar0
  set A : ℝ → ℝ := fun t => inner ℝ (r t - r 0) (velocity r 0) / ‖velocity r 0‖ ^ 2 with hAdef
  have hAaff : ∀ t ∈ Set.Icc 0 period, r t = r 0 + A t • velocity r 0 := by
    intro t ht
    have h := haff t ht
    rw [hAdef]
    exact h
  have hAdiff : Differentiable ℝ A := by
    rw [hAdef]
    exact (Differentiable.inner ℝ (hrd.sub_const (r 0)) (differentiable_const _)).div_const _
  have hA0 : A 0 = 0 := by rw [hAdef]; simp
  have hAper : A period = 0 := by
    have hrp : r period = r 0 := by simpa using hr.periodic 0
    simp only [hAdef]
    rw [hrp, sub_self, inner_zero_left, zero_div]
  -- Rolle: `A` has a critical point in the interior of the period
  obtain ⟨ξ, hξ, hξderiv⟩ :=
    exists_deriv_eq_zero hperiod hAdiff.continuous.continuousOn (by rw [hA0, hAper])
  -- the curve agrees with an affine function near `ξ`, so its derivative vanishes there
  have hev : r =ᶠ[nhds ξ] (fun t => r 0 + A t • velocity r 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hξ] with t ht
    exact hAaff t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hderivr : deriv r ξ = deriv (fun t => r 0 + A t • velocity r 0) ξ :=
    Filter.EventuallyEq.deriv_eq hev
  have hderivA : deriv (fun t => r 0 + A t • velocity r 0) ξ = deriv A ξ • velocity r 0 := by
    have h1 : HasDerivAt A (deriv A ξ) ξ := (hAdiff ξ).hasDerivAt
    exact ((h1.smul_const (velocity r 0)).const_add (r 0)).deriv
  have hvelzero : velocity r ξ = 0 := by
    rw [show velocity r ξ = deriv r ξ from rfl, hderivr, hderivA, hξderiv, zero_smul]
  exact hr.regular ξ hvelzero

end

end Work.Drive
