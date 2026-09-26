import Mathlib

namespace Work.Asymptotics

open Filter Topology

/-- A function which vanishes strictly to the left of `ρ` has derivative `0` at `ρ`.

Either the function is not differentiable at `ρ`, in which case `deriv` is `0` by
convention, or it is differentiable there; then continuity forces `g ρ = 0` (the left
limit of `g` is `0`) and the slope `(g y - g ρ)/(y - ρ)` is identically `0` on the
one-sided neighbourhood `(-∞, ρ)`, so the (two-sided) derivative must be `0`. -/
lemma deriv_eq_zero_of_forall_lt_eq_zero {g : ℝ → ℂ} {ρ : ℝ}
    (h : ∀ y : ℝ, y < ρ → g y = 0) : deriv g ρ = 0 := by
  by_cases hd : DifferentiableAt ℝ g ρ
  · have hρ : g ρ = 0 := by
      have h1 : Tendsto g (nhdsWithin ρ (Set.Iio ρ)) (𝓝 (g ρ)) :=
        hd.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto g (nhdsWithin ρ (Set.Iio ρ)) (𝓝 0) := by
        have hev2 : g =ᶠ[nhdsWithin ρ (Set.Iio ρ)] (fun _ => 0) :=
          Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => h y hy)
        exact tendsto_const_nhds.congr' hev2.symm
      exact tendsto_nhds_unique h1 h2
    have hslope : Tendsto (slope g ρ) (nhdsWithin ρ ({ρ}ᶜ)) (𝓝 (deriv g ρ)) :=
      hd.hasDerivAt.tendsto_slope
    have hmono : nhdsWithin ρ (Set.Iio ρ) ≤ nhdsWithin ρ ({ρ}ᶜ) :=
      nhdsWithin_mono ρ (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_lt hy)
    have h0 : Tendsto (slope g ρ) (nhdsWithin ρ (Set.Iio ρ)) (𝓝 0) := by
      have hev0 : slope g ρ =ᶠ[nhdsWithin ρ (Set.Iio ρ)] (fun _ => 0) :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => by
          simp only [slope_def_module, h y hy, hρ, sub_self, smul_zero])
      exact tendsto_const_nhds.congr' hev0.symm
    exact tendsto_nhds_unique (hslope.mono_left hmono) h0
  · exact deriv_zero_of_not_differentiableAt hd

/-- **Junction lemma.**  A function which agrees with a smooth `G` strictly to the right of `ρ`
and vanishes strictly to the left of `ρ`, with the value at `ρ` itself bounded by `C 0`, has all
its iterated derivatives bounded by the bounds for `G`'s iterated derivatives.  Away from `ρ` one
is in the interior of one of the two pieces (`f = G` resp. `f = 0` on a neighbourhood); at `ρ`
the derivative value is either `0` (the function is not differentiable there) or the one-sided
limit of `G`'s derivative (which exists by the smoothness of `G` at `ρ`). -/
theorem junction_iteratedDeriv {f G : ℝ → ℂ} {ρ : ℝ} {l : ℕ} {C : ℕ → ℝ}
    (hC : ∀ j ≤ l, 0 ≤ C j)
    (hval : ‖f ρ‖ ≤ C 0)
    (hright : ∀ y : ℝ, ρ < y → f y = G y)
    (hleft : ∀ y : ℝ, y < ρ → f y = 0)
    (hGdiff : ∀ j ≤ l, DifferentiableAt ℝ (fun y : ℝ => iteratedDeriv j G) ρ)
    (hG : ∀ j ≤ l, ∀ y : ℝ, ‖iteratedDeriv j G y‖ ≤ C j) :
    ∀ j ≤ l, ∀ x : ℝ, ‖iteratedDeriv j f x‖ ≤ C j := by
  -- `iteratedDeriv j f` coincides with `iteratedDeriv j G` to the right of `ρ` ...
  have hR : ∀ j, ∀ y, ρ < y → iteratedDeriv j f y = iteratedDeriv j G y := by
    intro j
    induction j with
    | zero =>
      intro y hy
      rw [iteratedDeriv_zero, iteratedDeriv_zero]
      exact hright y hy
    | succ k ih =>
      intro y hy
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hevR : iteratedDeriv k f =ᶠ[𝓝 y] iteratedDeriv k G :=
        Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hy) (fun z hz => ih z hz)
      exact hevR.deriv_eq
  -- ... and vanishes to the left of `ρ`.
  have hL : ∀ j, ∀ y, y < ρ → iteratedDeriv j f y = 0 := by
    intro j
    induction j with
    | zero =>
      intro y hy
      rw [iteratedDeriv_zero]
      exact hleft y hy
    | succ k ih =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k f =ᶠ[𝓝 y] (fun _ => 0) :=
        Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio hy) (fun z hz => ih z hz)
      rw [hev.deriv_eq, deriv_const]
  intro j hj x
  rcases lt_trichotomy x ρ with hlt | heq | hgt
  · rw [hL j x hlt]
    simp [hC j hj]
  · subst heq
    cases j with
    | zero =>
      rw [iteratedDeriv_zero]
      exact hval
    | succ k =>
      rw [iteratedDeriv_succ]
      rw [deriv_eq_zero_of_forall_lt_eq_zero (fun y hy => hL k y hy)]
      simp [hC (k+1) hj]
  · rw [hR j x hgt]
    exact hG j hj x

end Work.Asymptotics
