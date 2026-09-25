import Mathlib

namespace Work.BourgainPlan.Maximal

/-! ### Auxiliary lemmas

The main result of this file is a pointwise `L¹`-type estimate for the second derivative of a
product `Θ (·/c) · η`, which is obtained by combining

* the Leibniz rule for the second iterated derivative (`iteratedDeriv_mul`),
* the chain rule for the dilated factor `x ↦ Θ (x / c)` (`iteratedDeriv_comp_const_smul`),
* the fact that `iteratedDeriv 2 η w ≠ 0` forces `w` into the closure of the support of `η`,
  which is what makes the hypothesis `hsmall` applicable at `w / c`.
-/

/-- Leibniz rule for the second iterated derivative of a product, in the form of a norm bound:
`‖(f g)'' w‖ ≤ ‖f'' w‖ ‖g w‖ + 2 ‖f' w‖ ‖g' w‖ + ‖f w‖ ‖g'' w‖`. -/
private lemma norm_iteratedDeriv_mul_two_le (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (w : ℝ) :
    ‖iteratedDeriv 2 (f * g) w‖
      ≤ ‖iteratedDeriv 2 f w‖ * ‖g w‖ + 2 * (‖deriv f w‖ * ‖deriv g w‖)
        + ‖f w‖ * ‖iteratedDeriv 2 g w‖ := by
  have h2 : iteratedDeriv 2 (f * g) w
      = iteratedDeriv 2 f w * g w + 2 * deriv f w * deriv g w + f w * iteratedDeriv 2 g w := by
    rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.reduceSub, Nat.choose_self, iteratedDeriv_zero, iteratedDeriv_one,
      zero_add, add_assoc, Nat.cast_ofNat]
    ring
  rw [h2]
  refine le_trans (norm_add_le _ _) ?_
  have h3 := norm_add_le (iteratedDeriv 2 f w * g w) (2 * deriv f w * deriv g w)
  have h4 : ‖2 * deriv f w * deriv g w‖ = 2 * (‖deriv f w‖ * ‖deriv g w‖) := by
    rw [norm_mul, norm_mul]; norm_num; ring
  have h5 : ‖iteratedDeriv 2 f w * g w‖ = ‖iteratedDeriv 2 f w‖ * ‖g w‖ := norm_mul _ _
  have h6 : ‖f w * iteratedDeriv 2 g w‖ = ‖f w‖ * ‖iteratedDeriv 2 g w‖ := norm_mul _ _
  linarith

/-- First derivative of a dilated function: `(Θ (·/c))' w = c⁻¹ • Θ'(w/c)`. -/
private lemma deriv_dilated (Θ : ℝ → ℂ) (hΘ : ContDiff ℝ 2 Θ) (c w : ℝ) :
    deriv (fun x : ℝ => Θ (x / c)) w = c⁻¹ • deriv Θ (w / c) := by
  have h : (fun x : ℝ => Θ (x / c)) = fun x : ℝ => Θ (c⁻¹ * x) := by
    funext x; rw [div_eq_mul_inv, mul_comm]
  have key : iteratedDeriv 1 (fun x : ℝ => Θ (c⁻¹ * x)) w = c⁻¹ • deriv Θ (c⁻¹ * w) := by
    have h2 := congrFun (iteratedDeriv_comp_const_smul (n := 1) (hΘ.of_le (by norm_num)) (c⁻¹)) w
    simpa using h2
  rw [h, ← iteratedDeriv_one (f := fun x : ℝ => Θ (c⁻¹ * x)), key,
      show c⁻¹ * w = w / c from by rw [div_eq_mul_inv, mul_comm]]

/-- Second iterated derivative of a dilated function:
`(Θ (·/c))'' w = (c⁻¹)^2 • Θ''(w/c)`. -/
private lemma iteratedDeriv_two_dilated (Θ : ℝ → ℂ) (hΘ : ContDiff ℝ 2 Θ) (c w : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Θ (x / c)) w = (c⁻¹)^2 • iteratedDeriv 2 Θ (w / c) := by
  have h : (fun x : ℝ => Θ (x / c)) = fun x : ℝ => Θ (c⁻¹ * x) := by
    funext x; rw [div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_const_smul hΘ (c⁻¹)]
  simp only [div_eq_mul_inv, mul_comm c⁻¹ w]

/-- Outside the closure of the support of a `C²` function the function is locally zero, hence all
of its iterated derivatives vanish: a non-zero second derivative forces the point into the
closure of the support. -/
private lemma mem_closure_support_of_iteratedDeriv_two_ne_zero (η : ℝ → ℂ) (w : ℝ)
    (h : iteratedDeriv 2 η w ≠ 0) : w ∈ closure (Function.support η) := by
  by_contra hw
  have hopen : IsOpen (closure (Function.support η))ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hw)
  have hev : ∀ᶠ y in nhds w, η y = 0 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hy' : y ∉ Function.support η := fun hc => hball hy (subset_closure hc)
    simpa using hy'
  have h2 : η =ᶠ[nhds w] fun _ : ℝ => 0 := hev
  have := h2.iteratedDeriv_eq 2
  simp at this
  exact h this

/-- The set `{v | η (c v) ≠ 0}` is the preimage of the support of `η` under the homeomorphism
`v ↦ c v`; hence `w ∈ closure (support η)` gives `w / c ∈ closure {v | η (c v) ≠ 0}`. -/
private lemma div_mem_closure_dilated_support (η : ℝ → ℂ) (c : ℝ) (hc : 0 < c) (w : ℝ)
    (hw : w ∈ closure (Function.support η)) :
    w / c ∈ closure {v : ℝ | η (c * v) ≠ 0} := by
  rw [Metric.mem_closure_iff] at hw ⊢
  intro ε hε
  obtain ⟨z, hz, hdist⟩ := hw (ε * c) (mul_pos hε hc)
  refine ⟨z / c, ?_, ?_⟩
  · show η (c * (z / c)) ≠ 0
    rwa [mul_div_cancel₀ z (ne_of_gt hc)]
  · have hd : |w - z| < ε * c := by
      rw [Real.dist_eq] at hdist; exact hdist
    rw [Real.dist_eq, show w / c - z / c = (w - z) / c from by ring, abs_div, abs_of_pos hc,
        div_lt_iff₀ hc]
    exact hd

/-- The bound giving the `A`-term: `‖Θ (w/c)‖ ‖η'' w‖ ≤ A ‖η'' w‖`. Indeed either `η'' w = 0`,
or `w` lies in the closure of the support of `η`, whence `w/c` lies in the set on which `hsmall`
gives `‖Θ (w/c)‖ ≤ A`. -/
private lemma norm_mul_iteratedDeriv_two_le {A : ℝ} (Θ η : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (hsmall : ∀ u : ℝ, u ∈ closure {v : ℝ | η (c * v) ≠ 0} → ‖Θ u‖ ≤ A) (w : ℝ) :
    ‖Θ (w / c)‖ * ‖iteratedDeriv 2 η w‖ ≤ A * ‖iteratedDeriv 2 η w‖ := by
  by_cases hr : iteratedDeriv 2 η w = 0
  · rw [hr]; simp
  · have hmem : w ∈ closure (Function.support η) :=
      mem_closure_support_of_iteratedDeriv_two_ne_zero η w hr
    have hmem' : w / c ∈ closure {v : ℝ | η (c * v) ≠ 0} :=
      div_mem_closure_dilated_support η c hc w hmem
    exact mul_le_mul_of_nonneg_right (hsmall (w / c) hmem') (norm_nonneg _)

/-- Pointwise `L¹`-type bound for the second derivative of a product with a dilated factor:
if `‖Θ'‖ ≤ L`, `‖Θ''‖ ≤ L²` everywhere and `‖Θ‖ ≤ A` on the closure of `{v | η (c v) ≠ 0}`
(which, since `w ↦ c w` is a homeomorphism, is the set of `w` with `w/c` in the closure of
`support η`; it contains `support (iteratedDeriv 2 η)`, the second derivative of a function
vanishing off the closure of its support), then for every `w`
`‖(Θ (·/c) · η)'' w‖ ≤ (L²/c²)‖η w‖ + 2 (L/c)‖η' w‖ + A ‖η'' w‖`. -/
theorem norm_deriv2_dilated_mul_le (Θ η : ℝ → ℂ) (hΘ : ContDiff ℝ 2 Θ) (hη : ContDiff ℝ 2 η)
    (c : ℝ) (hc : 0 < c) {L A : ℝ}
    (hder1 : ∀ u : ℝ, ‖deriv Θ u‖ ≤ L) (hder2 : ∀ u : ℝ, ‖iteratedDeriv 2 Θ u‖ ≤ L ^ 2)
    (hsmall : ∀ u : ℝ, u ∈ closure {v : ℝ | η (c * v) ≠ 0} → ‖Θ u‖ ≤ A) (w : ℝ) :
    ‖deriv (deriv (fun x : ℝ => Θ (x / c) * η x)) w‖
      ≤ (L ^ 2 / c ^ 2) * ‖η w‖ + 2 * (L / c) * ‖deriv η w‖
        + A * ‖iteratedDeriv 2 η w‖ := by
  have hcd : ContDiff ℝ 2 (fun x : ℝ => Θ (x / c)) := hΘ.comp (by fun_prop)
  -- bound on `‖(Θ (·/c))'' w‖`
  have hB2 : ‖iteratedDeriv 2 (fun x : ℝ => Θ (x / c)) w‖ ≤ L ^ 2 / c ^ 2 := by
    rw [iteratedDeriv_two_dilated Θ hΘ c w, norm_smul]
    have h1 : ‖(c⁻¹)^2‖ = (c⁻¹)^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h1]
    refine le_trans (mul_le_mul_of_nonneg_left (hder2 (w / c)) (sq_nonneg _)) ?_
    rw [mul_comm ((c⁻¹)^2) (L ^ 2), inv_pow, ← div_eq_mul_inv]
  -- bound on `‖(Θ (·/c))' w‖`
  have hB1 : ‖deriv (fun x : ℝ => Θ (x / c)) w‖ ≤ L / c := by
    rw [deriv_dilated Θ hΘ c w, norm_smul]
    have h1 : ‖c⁻¹‖ = c⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    rw [h1]
    refine le_trans (mul_le_mul_of_nonneg_left (hder1 (w / c)) (le_of_lt (inv_pos.mpr hc))) ?_
    rw [mul_comm, ← div_eq_mul_inv]
  -- bound on the term involving `Θ (w/c)` itself
  have hA := norm_mul_iteratedDeriv_two_le Θ η c hc hsmall w
  -- the lifted factor as a function
  have hfun : ((fun x : ℝ => Θ (x / c)) * η) = fun x : ℝ => Θ (x / c) * η x := rfl
  have hiter : deriv (deriv (fun x : ℝ => Θ (x / c) * η x)) w
      = iteratedDeriv 2 ((fun x : ℝ => Θ (x / c)) * η) w := by
    have e : iteratedDeriv 2 ((fun x : ℝ => Θ (x / c)) * η) w
        = deriv (deriv ((fun x : ℝ => Θ (x / c)) * η)) w := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e, ← hfun]
  rw [hiter]
  refine le_trans (norm_iteratedDeriv_mul_two_le (fun x : ℝ => Θ (x / c)) η hcd hη w) ?_
  have hstep1 : ‖iteratedDeriv 2 (fun x : ℝ => Θ (x / c)) w‖ * ‖η w‖ ≤ (L ^ 2 / c ^ 2) * ‖η w‖ :=
    mul_le_mul_of_nonneg_right hB2 (norm_nonneg _)
  have hstep2 : 2 * (‖deriv (fun x : ℝ => Θ (x / c)) w‖ * ‖deriv η w‖)
      ≤ 2 * (L / c) * ‖deriv η w‖ := by
    calc 2 * (‖deriv (fun x : ℝ => Θ (x / c)) w‖ * ‖deriv η w‖)
        = 2 * ‖deriv (fun x : ℝ => Θ (x / c)) w‖ * ‖deriv η w‖ := by ring
      _ ≤ 2 * (L / c) * ‖deriv η w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB1 (by norm_num))
              (norm_nonneg _)
  linarith [hstep1, hstep2, hA]

end Work.BourgainPlan.Maximal
