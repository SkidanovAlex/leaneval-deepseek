import Mathlib
import Submission.Work.WilG4a.Defs

open Filter
open scoped Topology

namespace Work.WilG4a

/-- Iterated derivatives of a function composed with an affine reparametrisation.

For `F : ℝ → ℝ` which is `C^n` at the point `c + d * t`, the `n`-th derivative of
`s ↦ F (c + d * s)` at `t` is `d ^ n` times the `n`-th derivative of `F` at `c + d * t`. -/
theorem iteratedDeriv_comp_affine (c d : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ) (t : ℝ), ContDiffAt ℝ n F (c + d * t) →
      iteratedDeriv n (fun s => F (c + d * s)) t = d ^ n * iteratedDeriv n F (c + d * t) := by
  intro n
  induction n with
  | zero => intro F t _; simp
  | succ n ih =>
    intro F t hF
    have hdiff_eventually : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ F (c + d * s) := by
      obtain ⟨u, hu, hFu⟩ :=
        hF.contDiffOn (m := (↑(n + 1) : WithTop ℕ∞)) le_rfl
          (by intro h; exact absurd h (by simp))
      obtain ⟨v, hvu, hvopen, hcv⟩ := mem_nhds_iff.mp hu
      have hv : ContDiffOn ℝ (n + 1) F v := hFu.mono hvu
      have hpre : (fun s : ℝ => c + d * s) ⁻¹' v ∈ 𝓝 t :=
        (by fun_prop : ContinuousAt (fun s : ℝ => c + d * s) t).preimage_mem_nhds
          (hvopen.mem_nhds hcv)
      filter_upwards [hpre] with s hs
      exact (hv.contDiffAt (hvopen.mem_nhds hs)).differentiableAt (by simp)
    have hderiv : (fun s => deriv (fun u => F (c + d * u)) s) =ᶠ[𝓝 t]
        fun s => d * deriv F (c + d * s) := by
      filter_upwards [hdiff_eventually] with s hs
      have hg : HasDerivAt (fun u : ℝ => c + d * u) d s := by
        simpa using ((hasDerivAt_id s).const_mul d).const_add c
      change deriv (F ∘ fun u : ℝ => c + d * u) s = d * deriv F (c + d * s)
      rw [deriv_comp s hs (hg.differentiableAt), hg.deriv]; ring
    calc iteratedDeriv (n + 1) (fun s => F (c + d * s)) t
        = iteratedDeriv n (deriv (fun s => F (c + d * s))) t := by rw [iteratedDeriv_succ']
      _ = iteratedDeriv n (fun s => d * deriv F (c + d * s)) t :=
            Filter.EventuallyEq.iteratedDeriv_eq n hderiv
      _ = d * iteratedDeriv n (fun s => deriv F (c + d * s)) t := by
            rw [iteratedDeriv_const_mul_field]
      _ = d * (d ^ n * iteratedDeriv n (deriv F) (c + d * t)) := by
            rw [ih (deriv F) t (hF.derivWithin (by simp))]
      _ = d ^ (n + 1) * iteratedDeriv (n + 1) F (c + d * t) := by
            rw [iteratedDeriv_succ']; ring

theorem affine_reparam_bound (hG3 : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (r : ℕ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ (r + 1) f Work.WilG4a.I) (hI : ∀ x ∈ Work.WilG4a.I, f x ∈ Work.WilG4a.I) (hsign : ∀ j ≤ r + 1, (∀ x ∈ Work.WilG4a.I, 0 ≤ iteratedDeriv j f x) ∨ (∀ x ∈ Work.WilG4a.I, iteratedDeriv j f x ≤ 0)) {α β : ℝ} (hβ : 0 < β) (hα : 0 ≤ α) (hαβ : α + β ≤ 1) (hcov : β * ((r : ℝ) + 1) ≤ min α (1 - (α + β))) : ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I, |iteratedDeriv m (fun t : ℝ => f (α + β * t)) t| ≤ 1 := by
  have hmin1 : β * ((r : ℝ) + 1) ≤ α := le_trans hcov (min_le_left _ _)
  have hmin2 : β * ((r : ℝ) + 1) ≤ 1 - (α + β) := le_trans hcov (min_le_right _ _)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r; linarith
  have hβ_lt : β < 1 := by
    have h2 : β ≤ 1 - (α + β) := by nlinarith [hmin2, hβ, hr1]
    linarith
  have hsign' : ∀ j ≤ r + 1,
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0) := by
    intro j hj
    rcases hsign j hj with h | h
    · left; intro x hx
      rw [iteratedDerivWithin_of_isOpen (s := Set.Ioo (0 : ℝ) 1) isOpen_Ioo hx]; exact h x hx
    · right; intro x hx
      rw [iteratedDerivWithin_of_isOpen (s := Set.Ioo (0 : ℝ) 1) isOpen_Ioo hx]; exact h x hx
  intro m hm t ht
  have hM : 1 < 1 / β := by rw [one_lt_div hβ]; linarith
  have hxI : α + β * t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by nlinarith [ht.1, hβ, hα], by nlinarith [ht.2, hβ, hαβ]⟩
  have hmr : (m : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast (Nat.add_le_add_right hm 1)
  have hdiv : (m : ℝ) / (1 / β) = (m : ℝ) * β := by
    rw [one_div, div_eq_mul_inv, inv_inv]
  have h1 : (m : ℝ) / (1 / β) < α + β * t := by
    rw [hdiv]
    nlinarith [hmin1, hmr, hβ, ht.1]
  have h2 : α + β * t < 1 - (m : ℝ) / (1 / β) := by
    rw [hdiv]
    nlinarith [hmin2, hmr, hβ, ht.2]
  have hb := hG3 r f hf hI hsign' (1 / β) hM m hm (α + β * t) hxI h1 h2
  have hwit : iteratedDerivWithin m f (Set.Ioo (0 : ℝ) 1) (α + β * t) =
      iteratedDeriv m f (α + β * t) :=
    iteratedDerivWithin_of_isOpen (s := Set.Ioo (0 : ℝ) 1) isOpen_Ioo hxI
  rw [hwit] at hb
  have hcA : ContDiffAt ℝ m f (α + β * t) :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds hxI)).of_le (by exact_mod_cast (Nat.le_succ_of_le hm))
  have hchain := iteratedDeriv_comp_affine α β m f t hcA
  rw [hchain]
  have hfinal : |β ^ m * iteratedDeriv m f (α + β * t)| < 1 := by
    calc |β ^ m * iteratedDeriv m f (α + β * t)|
        = β ^ m * |iteratedDeriv m f (α + β * t)| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hβ.le m)]
      _ < β ^ m * (1 / β) ^ m := mul_lt_mul_of_pos_left hb (pow_pos hβ m)
      _ = 1 := by rw [← mul_pow, mul_one_div, div_self hβ.ne', one_pow]
  exact le_of_lt hfinal

end Work.WilG4a
