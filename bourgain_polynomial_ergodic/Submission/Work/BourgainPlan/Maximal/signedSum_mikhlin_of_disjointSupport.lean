import Mathlib

/-!
# Mikhlin conditions are preserved by finite sums of functions with disjoint supports

`S := ∑ i, ε i * M i` satisfies the Mikhlin conditions (`‖S‖ ≤ A`, `|ξ| ‖S'‖ ≤ A`,
`|ξ|² ‖S''‖ ≤ A`) with the *same* constant `A` as the `M i`, provided `‖ε i‖ ≤ 1` and the
supports of the `M i` are pointwise disjoint (for `i ≠ j` and every `ξ`, `M i ξ = 0` or
`M j ξ = 0`).

The point of the disjointness hypothesis is that at every `ξ` at most one `M i` is
non-zero, so no `L¹`-type sum of the individual bounds is ever needed: each of the three
bounds is inherited from a *single* `M i`, through the elementary observation

> if `f` is `C²`, `f ξ = 0`, and `f' ξ ≠ 0` or `f'' ξ ≠ 0`, then `f` is non-zero on a
> punctured neighbourhood of `ξ`.

Together with continuity this forces `{ξ | M i ξ ≠ 0}` (and the analogous sets for the
first and second derivatives) to be pairwise disjoint families of *open* sets, whence at
most one of the `deriv (M i) ξ` and at most one of the `iteratedDeriv 2 (M i) ξ` can be
non-zero.
-/

namespace Work.BourgainPlan.Maximal

open Filter Asymptotics
open scoped Topology BigOperators

/-- **Isolated zeros.** If `f : ℝ → ℂ` is `C²`, `f ξ = 0`, and at least one of the first
two derivatives of `f` at `ξ` is non-zero, then `f` does not vanish on a punctured
neighbourhood of `ξ`.

For the first derivative this is the statement that `slope f ξ` tends to `f' ξ ≠ 0`; for
the second derivative (with `f' ξ = 0`) it is the second-order Taylor expansion
`f x = (1/2) f'' ξ (x - ξ)² + o((x - ξ)²)`. -/
lemma signedSum_punctured_ne {f : ℝ → ℂ} {ξ : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : f ξ = 0) (hd : deriv f ξ ≠ 0 ∨ iteratedDeriv 2 f ξ ≠ 0) :
    ∃ δ > 0, ∀ x, 0 < |x - ξ| ∧ |x - ξ| < δ → f x ≠ 0 := by
  have hmain : ∀ᶠ y in 𝓝[≠] ξ, f y ≠ 0 := by
    by_cases hd1 : deriv f ξ = 0
    · -- second-order case
      have hc : iteratedDeriv 2 f ξ ≠ 0 := by
        rcases hd with h | h
        · exact absurd hd1 h
        · exact h
      have hT := taylor_isLittleO_univ (f := f) (x₀ := ξ) (n := 2) hf
      have hTay : ∀ x, taylorWithinEval f 2 Set.univ ξ x
          = ((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ := by
        intro x
        rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
        simp only [show ((0:ℕ) + 1) = 1 from rfl, show ((1:ℕ) + 1) = 2 from rfl]
        rw [iteratedDerivWithin_one, derivWithin_univ, iteratedDerivWithin_univ, h0, hd1]
        norm_num
      have hT' : (fun x => f x - ((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ)
          =o[𝓝 ξ] (fun x => (x - ξ)^2) := by
        have hfun : (fun x => f x - ((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ)
            = (fun x => f x - taylorWithinEval f 2 Set.univ ξ x) := by
          funext x; rw [hTay x]
        rw [hfun]; exact hT
      have hb := hT'.def (show 0 < ‖iteratedDeriv 2 f ξ‖ / 4 by positivity)
      have hb' : ∀ᶠ x in 𝓝[≠] ξ,
          ‖f x - ((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ‖
            ≤ (‖iteratedDeriv 2 f ξ‖ / 4) * (x - ξ)^2 := by
        filter_upwards [hb.filter_mono nhdsWithin_le_nhds] with x hx
        rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hx
      filter_upwards [hb', self_mem_nhdsWithin] with x hx hxne
      intro hfx
      have hx2 : 0 < (x - ξ)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxne)
      have key : (1/2:ℝ) * (x - ξ)^2 * ‖iteratedDeriv 2 f ξ‖
          ≤ (‖iteratedDeriv 2 f ξ‖ / 4) * (x - ξ)^2 := by
        have hnorm : ‖((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ‖
            = (1/2:ℝ) * (x - ξ)^2 * ‖iteratedDeriv 2 f ξ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_nonneg (sq_nonneg _)]
        calc (1/2:ℝ) * (x - ξ)^2 * ‖iteratedDeriv 2 f ξ‖
            = ‖((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ‖ := hnorm.symm
          _ = ‖f x - ((1/2:ℝ) * (x - ξ)^2) • iteratedDeriv 2 f ξ‖ := by
                rw [hfx, zero_sub, norm_neg]
          _ ≤ (‖iteratedDeriv 2 f ξ‖ / 4) * (x - ξ)^2 := hx
      nlinarith [key, norm_pos_iff.mpr hc, hx2]
    · -- first-order case: `slope f ξ` tends to `deriv f ξ ≠ 0`
      have hda : HasDerivAt f (deriv f ξ) ξ :=
        (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
      have hev : ∀ᶠ y in 𝓝[≠] ξ, slope f ξ y ≠ 0 := hda.tendsto_slope.eventually_ne hd1
      filter_upwards [hev] with y hy
      intro hfy
      exact hy (by rw [slope_def_module, hfy, h0, sub_self, smul_zero])
  have h2 : ∀ᶠ y in 𝓝 ξ, y ∈ ({ξ}ᶜ : Set ℝ) → f y ≠ 0 := by
    rw [← Filter.eventually_inf_principal]
    exact hmain
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨δ, hδpos, hδ⟩ := h2
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  exact hδ (y := x) (by rw [Real.dist_eq]; exact hx.2) (by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxe
    rw [hxe, sub_self, abs_zero] at hx
    exact absurd hx.1 (lt_irrefl 0))

/-- **At most one index carries a non-vanishing derivative.** For `i ≠ j`, if `M i ξ` and
`M j ξ` are both zero then the first and second derivatives of (at least) one of `M i`,
`M j` vanish at `ξ`.

Indeed, if `M i ξ = M j ξ = 0` and both `M i` and `M j` had a non-vanishing derivative
(first or second) at `ξ`, then both would be non-zero on a punctured neighbourhood of `ξ`
(`signedSum_punctured_ne`), contradicting the pointwise disjointness. If one of them is
non-zero at `ξ` it is non-zero on a neighbourhood, and disjointness forces the other to
vanish identically there. -/
lemma signedSum_deriv_deriv2_pairwise {K : ℕ} {M : Fin K → ℝ → ℂ}
    (hcd : ∀ i, ContDiff ℝ 2 (M i))
    (hdisj : ∀ i j, i ≠ j → ∀ ξ, M i ξ = 0 ∨ M j ξ = 0) :
    ∀ i j, i ≠ j → ∀ ξ, (deriv (M i) ξ = 0 ∧ iteratedDeriv 2 (M i) ξ = 0) ∨
                            (deriv (M j) ξ = 0 ∧ iteratedDeriv 2 (M j) ξ = 0) := by
  intro i j hij ξ
  have vanish : ∀ k, (∀ᶠ x in 𝓝 ξ, M k x = 0) →
      deriv (M k) ξ = 0 ∧ iteratedDeriv 2 (M k) ξ = 0 := by
    intro k hz
    have hz' : M k =ᶠ[𝓝 ξ] (fun _ => 0) := hz
    refine ⟨?_, ?_⟩
    · rw [Filter.EventuallyEq.deriv_eq hz', deriv_const]
    · rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hz', iteratedDeriv_const]
      simp
  by_cases hi : M i ξ = 0
  · by_cases hj : M j ξ = 0
    · by_cases hQ : deriv (M i) ξ ≠ 0 ∨ iteratedDeriv 2 (M i) ξ ≠ 0
      · right
        have contra : ∀ (h' : deriv (M j) ξ ≠ 0 ∨ iteratedDeriv 2 (M j) ξ ≠ 0), False := by
          intro h'
          obtain ⟨δi, hδi, hnei⟩ := signedSum_punctured_ne (hcd i) hi hQ
          obtain ⟨δj, hδj, hnej⟩ := signedSum_punctured_ne (hcd j) hj h'
          set x : ℝ := ξ + min δi δj / 2 with hxdef
          have hmin : 0 < min δi δj := lt_min hδi hδj
          have hx0 : 0 < |x - ξ| := by
            rw [hxdef, add_sub_cancel_left, abs_of_pos (by positivity)]
            positivity
          have hxi : |x - ξ| < δi := by
            rw [hxdef, add_sub_cancel_left, abs_of_pos (by positivity)]
            calc min δi δj / 2 < min δi δj := by linarith
              _ ≤ δi := min_le_left _ _
          have hxj : |x - ξ| < δj := by
            rw [hxdef, add_sub_cancel_left, abs_of_pos (by positivity)]
            calc min δi δj / 2 < min δi δj := by linarith
              _ ≤ δj := min_le_right _ _
          rcases hdisj i j hij x with hh | hh
          · exact hnei x ⟨hx0, hxi⟩ hh
          · exact hnej x ⟨hx0, hxj⟩ hh
        refine ⟨?_, ?_⟩
        · by_contra hd; exact contra (Or.inl hd)
        · by_contra hd; exact contra (Or.inr hd)
      · left
        simp only [not_or, not_not] at hQ
        exact hQ
    · left
      have hU : ∀ᶠ x in 𝓝 ξ, M j x ≠ 0 := (hcd j).continuous.continuousAt.eventually_ne hj
      have hz : ∀ᶠ x in 𝓝 ξ, M i x = 0 :=
        hU.mono fun x hx => (hdisj i j hij x).resolve_right hx
      exact vanish i hz
  · right
    have hU : ∀ᶠ x in 𝓝 ξ, M i x ≠ 0 := (hcd i).continuous.continuousAt.eventually_ne hi
    have hz : ∀ᶠ x in 𝓝 ξ, M j x = 0 :=
      hU.mono fun x hx => (hdisj i j hij x).resolve_left hx
    exact vanish j hz

/-- A finite sum of complex numbers with the property that of any two distinct terms at
least one is zero is bounded in norm by the maximum of `b` over the terms. -/
lemma signedSum_norm_sum_le_of_pairwise {ι : Type*} [Fintype ι] {F : ι → ℂ} {b : ℝ}
    (hb : 0 ≤ b) (hpair : ∀ i j, i ≠ j → F i = 0 ∨ F j = 0) (hF : ∀ i, ‖F i‖ ≤ b) :
    ‖∑ i, F i‖ ≤ b := by
  by_cases h : ∃ i, F i ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    rw [Finset.sum_eq_single i0 (fun j _ hj => (hpair i0 j (Ne.symm hj)).resolve_left hi0)
      (fun hnot => absurd (Finset.mem_univ i0) hnot)]
    exact hF i0
  · simp only [not_exists, not_not] at h
    rw [Finset.sum_eq_zero (fun j _ => h j)]
    simpa using hb

/-- **Mikhlin conditions are preserved by finite sums of functions with disjoint
supports.** See the module docstring. -/
theorem signedSum_mikhlin_of_disjointSupport {K : ℕ} (M : Fin K → ℝ → ℂ) (ε : Fin K → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (hε : ∀ i, ‖ε i‖ ≤ 1)
    (hcd : ∀ i, ContDiff ℝ 2 (M i))
    (hbdd : ∀ i ξ, ‖M i ξ‖ ≤ A)
    (h1 : ∀ i ξ, |ξ| * ‖deriv (M i) ξ‖ ≤ A)
    (h2 : ∀ i ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 (M i) ξ‖ ≤ A)
    (hdisj : ∀ i j : Fin K, i ≠ j → ∀ ξ : ℝ, M i ξ = 0 ∨ M j ξ = 0) :
    ContDiff ℝ 2 (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) ∧
    (∀ ξ : ℝ, ‖∑ i : Fin K, ε i * M i ξ‖ ≤ A) ∧
    (∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) ξ‖ ≤ A) ∧
    (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) ξ‖ ≤ A) := by
  have hpair := signedSum_deriv_deriv2_pairwise hcd hdisj
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ContDiff.sum (fun i _ => contDiff_const.mul (hcd i))
  · intro ξ
    refine signedSum_norm_sum_le_of_pairwise hA ?_ ?_
    · intro i j hij
      rcases hdisj i j hij ξ with hh | hh
      · exact Or.inl (by rw [hh, mul_zero])
      · exact Or.inr (by rw [hh, mul_zero])
    · intro i
      calc ‖ε i * M i ξ‖ = ‖ε i‖ * ‖M i ξ‖ := norm_mul _ _
        _ ≤ 1 * A := mul_le_mul (hε i) (hbdd i ξ) (norm_nonneg _) zero_le_one
        _ = A := one_mul A
  · intro ξ
    have hderiv : deriv (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) ξ
        = ∑ i : Fin K, ε i * deriv (M i) ξ := by
      have hfun : (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ)
          = (∑ i : Fin K, fun ξ : ℝ => ε i * M i ξ) := by
        funext x; simp [Finset.sum_apply]
      rw [hfun]
      have key := deriv_sum (u := Finset.univ) (A := fun i : Fin K => fun ξ : ℝ => ε i * M i ξ)
        (x := ξ)
        (fun i _ => ((hcd i).differentiable (by norm_num)).differentiableAt.const_mul (ε i))
      simp only [deriv_const_mul_field] at key
      exact key
    rw [hderiv]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_mul]
      exact hA
    · have hξpos : 0 < |ξ| := abs_pos.mpr hξ
      have hle : ‖∑ i : Fin K, ε i * deriv (M i) ξ‖ ≤ A / |ξ| := by
        refine signedSum_norm_sum_le_of_pairwise (div_nonneg hA (abs_nonneg _)) ?_ ?_
        · intro i j hij
          rcases hpair i j hij ξ with ⟨h', _⟩ | ⟨h', _⟩
          · exact Or.inl (by rw [h', mul_zero])
          · exact Or.inr (by rw [h', mul_zero])
        · intro i
          have hle' : ‖deriv (M i) ξ‖ ≤ A / |ξ| := by
            rw [le_div_iff₀ hξpos, mul_comm]
            exact h1 i ξ
          calc ‖ε i * deriv (M i) ξ‖ = ‖ε i‖ * ‖deriv (M i) ξ‖ := norm_mul _ _
            _ ≤ 1 * (A / |ξ|) := mul_le_mul (hε i) hle' (norm_nonneg _) zero_le_one
            _ = A / |ξ| := one_mul _
      calc |ξ| * ‖∑ i : Fin K, ε i * deriv (M i) ξ‖ ≤ |ξ| * (A / |ξ|) :=
            mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = A := mul_div_cancel₀ A (ne_of_gt hξpos)
  · intro ξ
    have hderiv2 : iteratedDeriv 2 (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) ξ
        = ∑ i : Fin K, ε i * iteratedDeriv 2 (M i) ξ := by
      have hfun : (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ)
          = (∑ i : Fin K, fun ξ : ℝ => ε i * M i ξ) := by
        funext x; simp [Finset.sum_apply]
      rw [hfun]
      rw [iteratedDeriv_sum (I := Finset.univ)
        (f := fun i : Fin K => fun ξ : ℝ => ε i * M i ξ) (x := ξ) (n := 2)
        (fun i _ => (contDiff_const.mul (hcd i)).contDiffAt)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iteratedDeriv_const_mul (ε i) ((hcd i).contDiffAt)]
    rw [hderiv2]
    by_cases hξ : ξ = 0
    · rw [hξ, abs_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul]
      exact hA
    · have hξpos : 0 < |ξ| := abs_pos.mpr hξ
      have hle : ‖∑ i : Fin K, ε i * iteratedDeriv 2 (M i) ξ‖ ≤ A / |ξ|^2 := by
        refine signedSum_norm_sum_le_of_pairwise (div_nonneg hA (by positivity)) ?_ ?_
        · intro i j hij
          rcases hpair i j hij ξ with ⟨_, h'⟩ | ⟨_, h'⟩
          · exact Or.inl (by rw [h', mul_zero])
          · exact Or.inr (by rw [h', mul_zero])
        · intro i
          have hle' : ‖iteratedDeriv 2 (M i) ξ‖ ≤ A / |ξ|^2 := by
            rw [le_div_iff₀ (pow_pos hξpos 2), mul_comm]
            exact h2 i ξ
          calc ‖ε i * iteratedDeriv 2 (M i) ξ‖
              = ‖ε i‖ * ‖iteratedDeriv 2 (M i) ξ‖ := norm_mul _ _
            _ ≤ 1 * (A / |ξ|^2) := mul_le_mul (hε i) hle' (norm_nonneg _) zero_le_one
            _ = A / |ξ|^2 := one_mul _
      calc |ξ|^2 * ‖∑ i : Fin K, ε i * iteratedDeriv 2 (M i) ξ‖ ≤ |ξ|^2 * (A / |ξ|^2) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = A := mul_div_cancel₀ A (ne_of_gt (pow_pos hξpos 2))

end Work.BourgainPlan.Maximal
