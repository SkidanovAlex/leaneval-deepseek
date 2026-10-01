import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# `Work.LinnikAreas.TuranOther.twMultMax`

The zero multiset of the twisted product
`D(s) = ζ(s)·L(s,χ₀)·L(s+iγ,χ)·L(s+iγ,χ₀χ)` used in the Turán power-sum proof of the
Deuring–Heilbronn phenomenon is **locally finite**: for every closed ball `K` only finitely many
`u` have `twMult u ≠ 0`.  Consequently the weight function
`z(ω) = (1+α-ω)^{-2}` attains its maximum modulus over that multiset.

The finiteness rests on the standard discreteness of the zeros of an analytic function: each of
the four factors is (after "multiplying away" the pole at `s = 1` of the trivial character's
`L`-function, resp. of `ζ`) an entire function which is not identically zero, so its zero set
meets a compact set in a finite set (`Work.LinnikAreas.boxMaxZeroAux.finite_entire_zeros_closedBall`).

More precisely we use

* `riemannZeta₁ = (s-1)ζ(s)` for `ζ` (`riemannZeta₁` is entire, `riemannZeta₁ 1 = 1`);
* `L(·,χ)` itself for a non-trivial `χ` (`differentiable_LFunction`);
* `LFunctionTrivChar₁ q = (s-1)·L(s, 1_q)` for the trivial character mod `q`
  (`differentiable_LFunctionTrivChar₁`), together with the single point `s = 1`.

Finally, `twMult` vanishes at `1 + α` (`Re(1+α) ≥ 2`), so no maximiser can have `zval α u = 0`.
-/

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-! ## Elementary reformulations -/

/-- The definition of `zval`, written with the exponent as a `ℤ`-power. -/
lemma zval_def' (α : ℝ) (u : ℂ) : zval α u = ((1 + (α : ℂ)) - u) ^ (-2 : ℤ) := rfl

/-- The norm of the power-sum variable. -/
lemma norm_zval_eq (α : ℝ) (u : ℂ) :
    ‖zval α u‖ = 1 / ‖1 + (α : ℂ) - u‖ ^ 2 := by
  rw [zval, norm_zpow, show (-2 : ℤ) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast,
    inv_eq_one_div]

/-- `multZeta` vanishes at points where `ζ` does not. -/
lemma multZeta_eq_zero_of_ne {u : ℂ} (h : riemannZeta u ≠ 0) : multZeta u = 0 := by
  by_contra hc
  exact h (apply_eq_zero_of_analyticOrderNatAt_ne_zero hc)

/-- `multL` vanishes at points where `L(·,χ)` does not. -/
lemma multL_eq_zero_of_ne {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {u : ℂ}
    (h : DirichletCharacter.LFunction χ u ≠ 0) : multL χ u = 0 := by
  by_contra hc
  exact h (apply_eq_zero_of_analyticOrderNatAt_ne_zero hc)

/-- Away from the two exceptional points `0` and `β₀` the twisted multiplicity is simply the
sum of the four multiplicities. -/
lemma twMult_eq_sum {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ : ℝ) {u : ℂ}
    (h0 : u ≠ 0) (hβ : u ≠ (β₀ : ℂ)) :
    twMult χ₀ χ β₀ γ u = multZeta u + multL χ₀ u + multL χ (u + Complex.I * (γ : ℂ))
      + multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) := by
  rw [twMult, if_neg (fun h => h.elim h0 hβ)]

/-! ## `1 + α` is not a zero of any of the four factors -/

/-- The real part of `1 + α` for `α ≥ 1`. -/
lemma re_one_add (α : ℝ) : (1 + (α : ℂ) : ℂ).re = 1 + α := by simp

/-- The real part of the `iγ`-shift of `1 + α`. -/
lemma re_one_add_shift (α γ : ℝ) : ((1 + (α : ℂ)) + Complex.I * (γ : ℂ)).re = 1 + α := by
  simp

/-- For `α ≥ 1` the point `1 + α` is not `1`. -/
lemma one_add_ne_one {α : ℝ} (hα : 1 ≤ α) : (1 + (α : ℂ) : ℂ) ≠ 1 := by
  intro h
  have h1 : (1 + (α : ℂ) : ℂ).re = 1 := by rw [h]; simp
  rw [re_one_add] at h1
  linarith

/-- For `α ≥ 1` the `iγ`-shift of `1 + α` is not `1`. -/
lemma one_add_shift_ne_one {α γ : ℝ} (hα : 1 ≤ α) :
    (1 + (α : ℂ)) + Complex.I * (γ : ℂ) ≠ 1 := by
  intro h
  have h1 : ((1 + (α : ℂ)) + Complex.I * (γ : ℂ)).re = 1 := by rw [h]; simp
  rw [re_one_add_shift] at h1
  linarith

/-- **`twMult` vanishes at `1 + α`**: the point has real part `≥ 2`, where none of `ζ`,
`L(·,χ₀)`, `L(·,χ)` nor `L(·,χ₀χ)` vanishes. -/
lemma twMult_one_add_alpha_eq_zero {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (β₀ γ α : ℝ) (hα : 1 ≤ α) : twMult χ₀ χ β₀ γ (1 + (α : ℂ)) = 0 := by
  by_cases h : (1 + (α : ℂ) : ℂ) = 0 ∨ (1 + (α : ℂ) : ℂ) = (β₀ : ℂ)
  · rw [twMult, if_pos h]
  · rw [twMult, if_neg h]
    have hre : 1 ≤ (1 + (α : ℂ) : ℂ).re := by rw [re_one_add]; linarith
    have hne : (1 + (α : ℂ) : ℂ) ≠ 1 := one_add_ne_one hα
    have hre' : 1 ≤ ((1 + (α : ℂ)) + Complex.I * (γ : ℂ)).re := by
      rw [re_one_add_shift]; linarith
    have hne' : (1 + (α : ℂ)) + Complex.I * (γ : ℂ) ≠ 1 := one_add_shift_ne_one hα
    have h1 : multZeta (1 + (α : ℂ)) = 0 :=
      multZeta_eq_zero_of_ne (riemannZeta_ne_zero_of_one_le_re hre)
    have h2 : multL χ₀ (1 + (α : ℂ)) = 0 :=
      multL_eq_zero_of_ne (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₀ (Or.inr hne) hre)
    have h3 : multL χ ((1 + (α : ℂ)) + Complex.I * (γ : ℂ)) = 0 :=
      multL_eq_zero_of_ne
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne') hre')
    have h4 : multL (χ₀ * χ) ((1 + (α : ℂ)) + Complex.I * (γ : ℂ)) = 0 :=
      multL_eq_zero_of_ne
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ₀ * χ) (Or.inr hne') hre')
    rw [h1, h2, h3, h4]

/-! ## Local finiteness of the zero multiset -/

/-- **The zeros of `ζ` (with multiplicity) are finite in a closed ball.**

`multZeta u ≠ 0` forces `ζ u = 0`, hence `riemannZeta₁ u = (u-1)ζ(u) = 0` (for `u ≠ 1`; and
`u = 1` is not a zero), and `riemannZeta₁` is entire with `riemannZeta₁ 1 = 1`. -/
lemma finite_multZeta_ball (c : ℂ) (R : ℝ) :
    ({u : ℂ | multZeta u ≠ 0} ∩ Metric.closedBall c R).Finite := by
  refine (Work.LinnikAreas.boxMaxZeroAux.finite_entire_zeros_closedBall
    (f := riemannZeta₁) (fun z _ => differentiable_riemannZeta₁.analyticAt z)
    (w := 1) (by rw [riemannZeta₁_one]; norm_num) c R).subset ?_
  intro u hu
  obtain ⟨huT, huK⟩ := hu
  refine ⟨?_, huK⟩
  rcases eq_or_ne u 1 with rfl | hu1
  · exact absurd (multZeta_eq_zero_of_ne (riemannZeta_ne_zero_of_one_le_re (by simp))) huT
  · have hζ : riemannZeta u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero huT
    have hne : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    have h' : (u - 1) * riemannZeta u = riemannZeta₁ u := by
      rw [riemannZeta_eq_inv_sub_mul hu1, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    show riemannZeta₁ u = 0
    rw [← h', hζ, mul_zero]

/-- **The zeros of `L(·,χ)` (with multiplicity) are finite in a closed ball.**

For a non-trivial character `L(·,χ)` is entire; for the trivial character mod `q` the zero set of
`L(·, 1_q)` is contained in the zero set of the entire function `LFunctionTrivChar₁ q =
(s-1)·L(s,1_q)` together with the single point `s = 1`. -/
lemma finite_multL_ball {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℂ) (R : ℝ) :
    ({u : ℂ | multL χ u ≠ 0} ∩ Metric.closedBall c R).Finite := by
  by_cases hχ : χ = 1
  · subst hχ
    have hfin₁ : ({u : ℂ | LFunctionTrivChar₁ q u = 0} ∩ Metric.closedBall c R).Finite :=
      Work.LinnikAreas.boxMaxZeroAux.finite_entire_zeros_closedBall
        (f := LFunctionTrivChar₁ q)
        (fun z _ => (differentiable_LFunctionTrivChar₁ q).analyticAt z)
        (w := 1) (LFunctionTrivChar₁_apply_one_ne_zero q) c R
    have hfin₂ : ({u : ℂ | u = 1} ∩ Metric.closedBall c R).Finite :=
      (Set.finite_singleton (1 : ℂ)).subset Set.inter_subset_left
    refine (hfin₁.union hfin₂).subset ?_
    intro u hu
    obtain ⟨huT, huK⟩ := hu
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) u = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero huT
    by_cases hu1 : u = 1
    · exact Or.inr ⟨hu1, huK⟩
    · refine Or.inl ⟨?_, huK⟩
      have hL' : LFunctionTrivChar q u = 0 := hL
      have hL₁ : LFunctionTrivChar₁ q u = (u - 1) * LFunctionTrivChar q u := by
        simp only [LFunctionTrivChar₁, Function.update_of_ne hu1]
      show LFunctionTrivChar₁ q u = 0
      rw [hL₁, hL', mul_zero]
  · refine (Work.LinnikAreas.boxMaxZeroAux.finite_entire_zeros_closedBall
      (f := DirichletCharacter.LFunction χ)
      (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
      (w := 2) ?_ c R).subset ?_
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    · intro u hu
      exact ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero hu.1, hu.2⟩

/-- **The zero multiset of the twisted product is locally finite.**

For every closed ball `K` the set of `u ∈ K` with `twMult u ≠ 0` is finite: it is contained in the
union of the (shifted) zero sets of `ζ`, `L(·,χ₀)`, `L(·,χ)` and `L(·,χ₀χ)`, each of which meets
`K` in a finite set. -/
lemma finite_twMult_ball {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ : ℝ)
    (c : ℂ) (R : ℝ) :
    ({u : ℂ | twMult χ₀ χ β₀ γ u ≠ 0} ∩ Metric.closedBall c R).Finite := by
  have h1 := finite_multZeta_ball c R
  have h2 := finite_multL_ball χ₀ c R
  have h3 := finite_multL_ball χ (c + Complex.I * (γ : ℂ)) R
  have h4 := finite_multL_ball (χ₀ * χ) (c + Complex.I * (γ : ℂ)) R
  -- the two `iγ`-shifted families, transported back along `u ↦ u + iγ`
  have h3' : ({u : ℂ | multL χ (u + Complex.I * (γ : ℂ)) ≠ 0} ∩
      Metric.closedBall c R).Finite := by
    refine (h3.image (fun w : ℂ => w - Complex.I * (γ : ℂ))).subset ?_
    intro u hu
    refine ⟨u + Complex.I * (γ : ℂ), ⟨hu.1, ?_⟩, by ring⟩
    have hu2 : u ∈ Metric.closedBall c R := hu.2
    rw [Metric.mem_closedBall] at hu2 ⊢
    rwa [dist_add_right]
  have h4' : ({u : ℂ | multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) ≠ 0} ∩
      Metric.closedBall c R).Finite := by
    refine (h4.image (fun w : ℂ => w - Complex.I * (γ : ℂ))).subset ?_
    intro u hu
    refine ⟨u + Complex.I * (γ : ℂ), ⟨hu.1, ?_⟩, by ring⟩
    have hu2 : u ∈ Metric.closedBall c R := hu.2
    rw [Metric.mem_closedBall] at hu2 ⊢
    rwa [dist_add_right]
  refine (h1.union (h2.union (h3'.union h4'))).subset ?_
  intro u hu
  obtain ⟨huT, huK⟩ := hu
  have h0 : u ≠ 0 := by rintro rfl; exact huT (by rw [twMult, if_pos (Or.inl rfl)])
  have hβ : u ≠ (β₀ : ℂ) := by rintro rfl; exact huT (by rw [twMult, if_pos (Or.inr rfl)])
  have hsum : multZeta u + multL χ₀ u + multL χ (u + Complex.I * (γ : ℂ))
      + multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) ≠ 0 := by
    have huT' : twMult χ₀ χ β₀ γ u ≠ 0 := huT
    rw [twMult_eq_sum χ₀ χ β₀ γ h0 hβ] at huT'
    exact huT'
  have hdisj : multZeta u ≠ 0 ∨ multL χ₀ u ≠ 0 ∨ multL χ (u + Complex.I * (γ : ℂ)) ≠ 0
      ∨ multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hsum (by rw [h.1, h.2.1, h.2.2.1, h.2.2.2])
  rcases hdisj with h | h | h | h
  · exact Or.inl ⟨h, huK⟩
  · exact Or.inr (Or.inl ⟨h, huK⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, huK⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, huK⟩))

/-! ## The maximum -/

/-- **The weight `z(ω) = (1+α-ω)^{-2}` attains its maximum modulus on the zero multiset of the
twisted product.**

Since the multiset is locally finite and the weight tends to `0` when `|1+α-ω| → ∞`, the maximum
of `‖zval α ·‖` over `{u | twMult u ≠ 0}` is attained at a point whose weight is non-zero (the
point `1+α` itself is not a zero of the twisted product). -/
theorem twMultMax {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ)
    (hα : 1 ≤ α) (hne : ∃ u : ℂ, Work.LinnikAreas.TuranOther.twMult χ₀ χ β₀ γ u ≠ 0) :
    ∃ u₀ : ℂ, Work.LinnikAreas.TuranOther.twMult χ₀ χ β₀ γ u₀ ≠ 0 ∧
      Work.LinnikAreas.TuranOther.zval α u₀ ≠ 0 ∧
      ∀ u : ℂ, Work.LinnikAreas.TuranOther.twMult χ₀ χ β₀ γ u ≠ 0 →
        ‖Work.LinnikAreas.TuranOther.zval α u‖ ≤ ‖Work.LinnikAreas.TuranOther.zval α u₀‖ := by
  classical
  obtain ⟨u₁, hu₁⟩ := hne
  have h1a : twMult χ₀ χ β₀ γ (1 + (α : ℂ)) = 0 :=
    twMult_one_add_alpha_eq_zero χ₀ χ β₀ γ α hα
  have hu₁ne : u₁ ≠ 1 + (α : ℂ) := fun h => hu₁ (by rw [h]; exact h1a)
  have hRpos : 0 < ‖1 + (α : ℂ) - u₁‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu₁ne))
  have hmem : u₁ ∈ Metric.closedBall (1 + (α : ℂ)) ‖1 + (α : ℂ) - u₁‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm,
      show u₁ - (1 + (α : ℂ)) = -(1 + (α : ℂ) - u₁) by ring, norm_neg]
  have hfin := finite_twMult_ball χ₀ χ β₀ γ (1 + (α : ℂ)) ‖1 + (α : ℂ) - u₁‖
  have hmemT : ∀ u : ℂ, u ∈ hfin.toFinset ↔
      twMult χ₀ χ β₀ γ u ≠ 0 ∧
        u ∈ Metric.closedBall (1 + (α : ℂ)) ‖1 + (α : ℂ) - u₁‖ := by
    intro u
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨u₀, hu₀T, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun u => ‖zval α u‖)
    ⟨u₁, (hmemT u₁).mpr ⟨hu₁, hmem⟩⟩
  have hu₁T : u₁ ∈ hfin.toFinset := (hmemT u₁).mpr ⟨hu₁, hmem⟩
  have hval : ‖zval α u₁‖ ≤ ‖zval α u₀‖ := hmax u₁ hu₁T
  have hu₁nz : ‖zval α u₁‖ ≠ 0 := by
    rw [norm_zval_eq]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 (ne_of_gt hRpos))
  refine ⟨u₀, ((hmemT u₀).mp hu₀T).1, ?_, ?_⟩
  · intro h0
    have h0' : ‖zval α u₀‖ = 0 := by rw [h0, norm_zero]
    exact hu₁nz (le_antisymm (hval.trans (le_of_eq h0')) (norm_nonneg _))
  · intro u hu
    by_cases huK : u ∈ Metric.closedBall (1 + (α : ℂ)) ‖1 + (α : ℂ) - u₁‖
    · exact hmax u ((hmemT u).mpr ⟨hu, huK⟩)
    · have hd : ‖1 + (α : ℂ) - u₁‖ < ‖1 + (α : ℂ) - u‖ := by
        have h1 : ¬ (dist u (1 + (α : ℂ)) ≤ ‖1 + (α : ℂ) - u₁‖) := by
          simpa [Metric.mem_closedBall] using huK
        have h2 : ‖1 + (α : ℂ) - u₁‖ < dist u (1 + (α : ℂ)) := not_le.mp h1
        rwa [dist_eq_norm, show u - (1 + (α : ℂ)) = -(1 + (α : ℂ) - u) by ring,
          norm_neg] at h2
      have hmain : ‖zval α u‖ < ‖zval α u₀‖ := by
        calc ‖zval α u‖ = 1 / ‖1 + (α : ℂ) - u‖ ^ 2 := norm_zval_eq α u
          _ < 1 / ‖1 + (α : ℂ) - u₁‖ ^ 2 :=
              one_div_lt_one_div_of_lt (pow_pos hRpos 2)
                (pow_lt_pow_left₀ hd (le_of_lt hRpos) (by norm_num))
          _ = ‖zval α u₁‖ := by rw [norm_zval_eq α u₁]
          _ ≤ ‖zval α u₀‖ := hval
      exact le_of_lt hmain

end Work.LinnikAreas.TuranOther

end
