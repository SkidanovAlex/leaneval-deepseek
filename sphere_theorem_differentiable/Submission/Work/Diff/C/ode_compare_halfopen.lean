import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

-- `hε` is genuinely not needed for the conclusion (for `s > 0` the hypothesis `h3` with `ε < 0`
-- is unsatisfiable, and for `s = 0` the conclusion is trivial); silence the binder linter.
set_option linter.unusedVariables false

namespace Work.Diff.C

/-- **Scalar Sturm comparison, half-open forcing bound.**

If `φ` is differentiable on `[0,s]` with derivative `φ'`, `φ'` is differentiable on `[0,s]` with
derivative `φ''`, and the forcing `|φ'' + φ|` is bounded by `ε` on the half-open interval `(0,s]`
(so that `φ''` may behave arbitrarily at the left endpoint `0`), then `φ` is within `ε s` of the
solution of `y'' + y = 0` with the same initial data — both for the values and for the derivatives.

The proof is the usual one: put `z := φ - (φ 0 cos + φ' 0 sin)`, `z'` its derivative,
`ζ := z' + i z` and `ξ := exp(-i t) ζ`; then `ξ' = exp(-i t) (φ'' + φ)` and `ξ 0 = 0`, so
`‖ξ s‖ ≤ ε s` whenever the bound `|φ'' + φ| ≤ ε` holds on `(0,s]`.  Since that bound is *not*
required at `0`, the mean value estimate is applied on `[δ,s]` for every `δ ∈ (0,s]` and combined
with the continuity of `ξ` at `0`. -/
theorem ode_compare_halfopen {φ φ' φ'' : ℝ → ℝ} {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t)
    (h3 : ∀ t ∈ Set.Ioc (0 : ℝ) s, |φ'' t + φ t| ≤ ε) :
    |φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s)| ≤ ε * s
      ∧ |φ' s - (φ' 0 * Real.cos s - φ 0 * Real.sin s)| ≤ ε * s := by
  set z : ℝ → ℝ := fun t => φ t - (φ 0 * Real.cos t + φ' 0 * Real.sin t) with hzdef
  set z' : ℝ → ℝ := fun t => φ' t + (φ 0 * Real.sin t - φ' 0 * Real.cos t) with hz'def
  set hh : ℝ → ℝ := fun t => φ'' t + φ t with hhdef
  have hz0 : z 0 = 0 := by simp [hzdef]
  have hz'0 : z' 0 = 0 := by simp [hz'def]
  have hdz : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z (z' t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.cos u + φ' 0 * Real.sin u)
        (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (φ 0)).add ((Real.hasDerivAt_sin t).const_mul (φ' 0))
    have h := (h1 t ht).sub hc
    have heq : φ' t - (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) = z' t := by
      rw [hz'def]; ring
    rw [heq] at h
    exact h
  have hdz' : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z' (hh t - z t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.sin u - φ' 0 * Real.cos u)
        (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) t :=
      ((Real.hasDerivAt_sin t).const_mul (φ 0)).sub ((Real.hasDerivAt_cos t).const_mul (φ' 0))
    have h := (h2 t ht).add hc
    have heq : φ'' t + (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) = hh t - z t := by
      rw [hhdef, hzdef]; ring
    rw [heq] at h
    exact h
  set ζ : ℝ → ℂ := fun t => (z' t : ℂ) + Complex.I * (z t : ℂ) with hζdef
  set ξ : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I) * ζ t with hξdef
  have hdζ : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt ζ (Complex.I * ζ t + (hh t : ℂ)) t := by
    intro t ht
    have ha : HasDerivAt (fun u : ℝ => (z' u : ℂ)) ((hh t - z t : ℝ) : ℂ) t :=
      (hdz' t ht).ofReal_comp
    have hb : HasDerivAt (fun u : ℝ => (z u : ℂ)) ((z' t : ℝ) : ℂ) t := (hdz t ht).ofReal_comp
    have h := ha.add (hb.const_mul Complex.I)
    have heq : ((hh t - z t : ℝ) : ℂ) + Complex.I * ((z' t : ℝ) : ℂ)
        = Complex.I * ζ t + (hh t : ℂ) := by
      rw [hζdef]
      push_cast
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [heq] at h
    exact h
  have hdξ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      HasDerivAt ξ (Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)) t := by
    intro t ht
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ) * Complex.I) (-Complex.I) t := by
      have h := (hu.neg).mul_const Complex.I
      simpa using h
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I))
        (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := hlin.cexp
    have h := hexp.mul (hdζ t ht)
    have heq : Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I) * ζ t
        + Complex.exp (-(t : ℂ) * Complex.I) * (Complex.I * ζ t + (hh t : ℂ))
        = Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ) := by
      ring
    rw [heq] at h
    exact h
  have hξ0 : ξ 0 = 0 := by
    simp [hξdef, hζdef, hz0, hz'0]
  have hbnd : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      ‖Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)‖ ≤ ε := by
    intro t ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    have h5 : ‖((hh t : ℝ) : ℂ)‖ = |hh t| := by simp
    rw [h5]
    exact h3 t ht
  -- The main estimate `‖ξ s‖ ≤ ε * s`.
  have hexpc : ContinuousAt (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) 0 :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.neg.mul_const Complex.I)).continuousAt
  have hξs : ‖ξ s‖ ≤ ε * s := by
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [← hs0, hξ0]; simp
    · have hzc : ContinuousAt z 0 := (hdz 0 ⟨le_rfl, hs⟩).continuousAt
      have hz'c : ContinuousAt z' 0 := (hdz' 0 ⟨le_rfl, hs⟩).continuousAt
      have hζc : ContinuousAt ζ 0 := by
        rw [hζdef]
        exact (Complex.continuous_ofReal.continuousAt.comp hz'c).add
          ((Complex.continuous_ofReal.continuousAt.comp hzc).const_mul Complex.I)
      have hξc : ContinuousAt ξ 0 := by
        rw [hξdef]
        exact hexpc.mul hζc
      set G : ℝ → ℝ := fun δ => ε * (s - δ) + ‖ξ δ‖ with hGdef
      have hG0 : G 0 = ε * s := by rw [hGdef]; simp [hξ0]
      have hGcont : ContinuousAt G 0 := by
        have hlin : Continuous (fun δ : ℝ => ε * (s - δ)) :=
          continuous_const.mul (continuous_const.sub continuous_id)
        rw [hGdef]
        exact (hlin.continuousAt).add hξc.norm
      -- Mean value estimate on `[δ,s]` for every `δ ∈ (0,s]`.
      have hseg : ∀ δ ∈ Set.Ioc (0 : ℝ) s, ‖ξ s - ξ δ‖ ≤ ε * (s - δ) := by
        intro δ hδ
        have hb : ∀ t ∈ Set.Ico δ s,
            ‖Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)‖ ≤ ε := by
          intro t ht
          exact hbnd t ⟨lt_of_lt_of_le hδ.1 ht.1, le_of_lt ht.2⟩
        exact norm_image_sub_le_of_norm_deriv_le_segment' (f := ξ)
          (f' := fun t => Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ))
          (a := δ) (b := s)
          (fun t ht => (hdξ t ⟨le_of_lt (lt_of_lt_of_le hδ.1 ht.1), ht.2⟩).hasDerivWithinAt)
          hb s ⟨hδ.2, le_rfl⟩
      have hle : ∀ δ ∈ Set.Ioc (0 : ℝ) s, ‖ξ s‖ ≤ G δ := by
        intro δ hδ
        have hsd := hseg δ hδ
        rw [hGdef]
        calc ‖ξ s‖ = ‖(ξ s - ξ δ) + ξ δ‖ := by rw [sub_add_cancel]
          _ ≤ ‖ξ s - ξ δ‖ + ‖ξ δ‖ := norm_add_le _ _
          _ ≤ ε * (s - δ) + ‖ξ δ‖ := by linarith
      have htend : Filter.Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
        hGcont.tendsto.mono_left nhdsWithin_le_nhds
      have hfin := ge_of_tendsto htend (Filter.eventually_of_mem (Ioc_mem_nhdsGT hs0) hle)
      rwa [hG0] at hfin
  have hζle : ‖ζ s‖ = ‖ξ s‖ := by
    rw [hξdef, norm_mul]
    have hn : ‖Complex.exp (-(s : ℂ) * Complex.I)‖ = 1 := by
      have hcast : (-(s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [hn, one_mul]
  have hzle : |z s| ≤ ε * s := by
    have him : (ζ s).im = z s := by simp [hζdef]
    have hn2 : ‖(z s : ℂ)‖ ≤ ‖ζ s‖ := by
      calc ‖(z s : ℂ)‖ = |z s| := by simp
        _ = |(ζ s).im| := by rw [him]
        _ ≤ ‖ζ s‖ := Complex.abs_im_le_norm _
    calc |z s| = ‖(z s : ℂ)‖ := by simp
      _ ≤ ‖ζ s‖ := hn2
      _ = ‖ξ s‖ := hζle
      _ ≤ ε * s := hξs
  have hz'le : |z' s| ≤ ε * s := by
    have hre : (ζ s).re = z' s := by simp [hζdef]
    have hn2 : ‖(z' s : ℂ)‖ ≤ ‖ζ s‖ := by
      calc ‖(z' s : ℂ)‖ = |z' s| := by simp
        _ = |(ζ s).re| := by rw [hre]
        _ ≤ ‖ζ s‖ := Complex.abs_re_le_norm _
    calc |z' s| = ‖(z' s : ℂ)‖ := by simp
      _ ≤ ‖ζ s‖ := hn2
      _ = ‖ξ s‖ := hζle
      _ ≤ ε * s := hξs
  constructor
  · have hzval : z s = φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s) := rfl
    rwa [hzval] at hzle
  · have hzval : z' s = φ' s - (φ' 0 * Real.cos s - φ 0 * Real.sin s) := by
      rw [hz'def]; ring
    rwa [hzval] at hz'le

end Work.Diff.C
