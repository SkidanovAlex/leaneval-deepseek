import Mathlib
import Submission.Work.WilkiesH.Interp.siegel_poly_exists_v2
import Submission.Work.WilkiesH.Interp.V2Defs
import Submission.Work.WilkiesH.Interp.poly_comp_taylor_per_order
import Submission.Work.WilkiesH.Interp.poly_lipschitz_bound
import Submission.Work.WilkiesH.Interp.vanishes_of_bounds
import Submission.Work.WilkiesH.Interp.exists_convexBoxCover_openCube
import Submission.Work.WilkiesH.Interp.v2_taylor_sum_le
import Submission.Work.WilkiesH.Interp.v2_remainder_le
import Submission.Work.WilkiesH.Interp.v2_support_sum_le

/-!
# Area I (`v2` route): the Siegel–Wilkie box polynomial

This is the per-box step of the second (`v2`) route to the interpolation step of
`Work.WilkiesH.InterpPerChart` (BNZ Prop. 6.1).

Given a small convex box `s` of the chart domain `openCube μ`, a `C^{b+1}` chart `Ψ` with
bounded jets and values on the open cube, and the Siegel cardinality condition on
`b, d, Q, ρ`, we produce a nonzero integral polynomial `P` of degree `≤ d` and coefficients
`≤ Q` which vanishes at every point `y` of `degreeHeightLE univ g H` that lies within `ε` of
`Ψ s` — provided the numerical comparison `above μ b d Q ρ ε < liou μ d Q g H` holds.

The pieces:

* `Interp.siegel_poly_exists_v2` — Siegel's lemma produces `P` whose jets at the box centre
  `s₀` are bounded order by order;
* `Interp.poly_comp_taylor_per_order` — the Taylor expansion of `P ∘ Ψ` at `s₀` on the box,
  consuming those jet bounds (via the arithmetic lemma `Interp.v2_taylor_sum_le` for the
  Taylor part and `Interp.v2_remainder_le` for the Lagrange remainder);
* `Interp.poly_lipschitz_bound` — the Lipschitz step from the point where the bound holds to
  the point `y` within distance `ε`;
* `Interp.vanishes_of_bounds` — the Liouville comparison.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

/-- `totalDegree` does not increase under a coefficient map. -/
private lemma totalDegree_map_le' {R S : Type*} {σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) : (p.map f).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  exact Finset.le_sup (f := fun m : σ →₀ ℕ => m.sum fun _ e => e) (by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h
    exact hm (by rw [MvPolynomial.coeff_map, h, map_zero]))

/-- The open cube is convex. -/
private lemma convex_openCube' (μ : ℕ) : Convex ℝ (WilkiesDesign.openCube μ) := by
  intro x hx y hy a b ha hb hab i
  have key := convex_Ioo (0 : ℝ) 1 (hx i) (hy i) ha hb hab
  simpa [Pi.add_apply, Pi.smul_apply] using key

/-- The open cube is open. -/
private lemma isOpen_openCube' (μ : ℕ) : IsOpen (WilkiesDesign.openCube μ) := by
  have h : WilkiesDesign.openCube μ
      = ⋂ i : Fin μ, {t : Fin μ → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t; simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

/-- For `ρ ≥ 0` the diameter bound `‖t - s₀‖ ≤ ρ` upgrades to `‖t - s₀‖ ≤ √μ · ρ`
(for `μ = 0` the function space is trivial, so `t = s₀`). -/
private lemma norm_sub_le_sqrt_mul {μ : ℕ} {t s₀ : Fin μ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ‖t - s₀‖ ≤ ρ) : ‖t - s₀‖ ≤ Real.sqrt (μ : ℝ) * ρ := by
  rcases Nat.eq_zero_or_pos μ with hμ | hμ
  · subst hμ
    have hs : Subsingleton (Fin 0 → ℝ) := inferInstance
    rw [show t - s₀ = 0 from hs.elim _ _, norm_zero, Nat.cast_zero, Real.sqrt_zero, zero_mul]
  · have hμ1 : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
    exact h.trans (le_mul_of_one_le_left hρ (Real.one_le_sqrt.mpr hμ1))

/-- The `ℓ¹`-distance of two points of `ℝ^{μ+1}` is at most `(μ+1)` times their distance. -/
private lemma sum_abs_sub_le {μ : ℕ} {y y' : Fin (μ + 1) → ℝ} {ε : ℝ}
    (h : ‖y - y'‖ < ε) : (∑ i, |y i - y' i|) ≤ ((μ : ℝ) + 1) * ε := by
  calc (∑ i : Fin (μ + 1), |y i - y' i|) ≤ ∑ _i : Fin (μ + 1), ε :=
        Finset.sum_le_sum fun i _ => by
          have h1 := norm_le_pi_norm (y - y') i
          rw [Pi.sub_apply, Real.norm_eq_abs] at h1
          exact le_of_lt (lt_of_le_of_lt h1 h)
    _ = ((μ : ℝ) + 1) * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem v2_box_poly {μ b d Q : ℕ} {ρ ε : ℝ} {g H : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hQ : 1 ≤ Q) (hH : 1 ≤ H)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsqr : Real.sqrt (μ : ℝ) * ρ ≤ 1)
    (hcard : (Q + 1) ^ Work.WilkiesH.monoCount (μ + 1) d
      > (2 * (Work.WilkiesH.monoCount (μ + 1) d * Nat.ceil (ρ ^ (-(b : ℤ))) * Q) + 1)
          ^ Work.WilkiesH.monoCount μ b)
    {Ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)}
    {s : Set (Fin μ → ℝ)} {s₀ : Fin μ → ℝ}
    (hsconv : Convex ℝ s) (hssub : s ⊆ WilkiesDesign.openCube μ) (hs₀ : s₀ ∈ s)
    (hdiam : ∀ t ∈ s, ‖t - s₀‖ ≤ ρ)
    (hΨsmooth : ContDiffOn ℝ (b + 1 : ℕ) Ψ (WilkiesDesign.openCube μ))
    (hΨjet : ∀ k, k ≤ b + 1 → ∀ t ∈ WilkiesDesign.openCube μ,
      ‖iteratedFDeriv ℝ k Ψ t‖ ≤ 1)
    (hΨval : ∀ t ∈ WilkiesDesign.openCube μ, ∀ i, |Ψ t i| ≤ 1)
    (hineq : Work.WilkiesH.Interp.above μ b d Q ρ ε < Work.WilkiesH.Interp.liou μ d Q g H) :
    ∃ P : MvPolynomial (Fin (μ + 1)) ℤ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      (∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (Q : ℤ)) ∧
      ∀ y : Fin (μ + 1) → ℝ, (∀ i, |y i| ≤ 1) →
        y ∈ WilkiesConjecture.degreeHeightLE Set.univ g H →
        (∃ t ∈ s, dist (Ψ t) y < ε) →
        MvPolynomial.eval y (P.map (Int.castRingHom ℝ)) = 0 := by
  classical
  have hρ0 : 0 ≤ ρ := hρ.le
  -- ## Step 1: Siegel's lemma produces the polynomial and its jet bounds
  obtain ⟨P, hPne, hPdeg, hPcoef, hPjet⟩ :=
    siegel_poly_exists_v2 hb hd hρ hρ1 Q hQ hΨsmooth
      (fun k hk t ht => hΨjet k (le_trans hk (Nat.le_succ b)) t ht) hΨval
      (hssub hs₀) hcard
  refine ⟨P, hPne, hPdeg, hPcoef, ?_⟩
  intro y hy1 hyHH hnear
  obtain ⟨t, ht, hdist⟩ := hnear
  have htU : t ∈ WilkiesDesign.openCube μ := hssub ht
  have hs0U : s₀ ∈ WilkiesDesign.openCube μ := hssub hs₀
  have hdiam' : ‖t - s₀‖ ≤ ρ := hdiam t ht
  have hlt : ‖t - s₀‖ ≤ Real.sqrt (μ : ℝ) * ρ := norm_sub_le_sqrt_mul hρ0 hdiam'
  -- ## Step 2: the Taylor part plus the Lagrange remainder is `A1 + A2`
  have hPSdeg : (P.map (Int.castRingHom ℝ)).totalDegree ≤ d :=
    (totalDegree_map_le' (Int.castRingHom ℝ) P).trans hPdeg
  have hcoefsum := v2_support_sum_le P hPdeg hPcoef
  have htaylor := poly_comp_taylor_per_order (μ := μ) (b := b)
      (U := WilkiesDesign.openCube μ) (isOpen_openCube' μ) (convex_openCube' μ)
      (ψ := Ψ) hΨsmooth hΨjet hΨval (P.map (Int.castRingHom ℝ))
      (t₀ := s₀) (t := t) hs0U htU
      (β := fun j => (μ : ℝ) ^ j * ρ ^ (b - j)
          * Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (d : ℝ) ^ j)
      (fun j hj => by simpa only [Real.norm_eq_abs] using hPjet j hj (t - s₀))
  have hS := v2_taylor_sum_le (μ := μ) (b := b) (d := d) (ρ := ρ) (t := t) (s₀ := s₀) hρ0 hlt
  have hR := v2_remainder_le (μ := μ) (b := b) (d := d) (Q := Q) (ρ := ρ) (t := t) (s₀ := s₀)
      (PS := P.map (Int.castRingHom ℝ)) hcoefsum hPSdeg hρ0 hρ1 hdiam' hlt
  have hT : |(P.map (Int.castRingHom ℝ)).eval (Ψ t)|
      ≤ Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
          * (∑ j ∈ Finset.range (b + 1),
              ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ)))
        + (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * ((d : ℝ) + 1) ^ (b + 1)
          * ((Real.sqrt (μ : ℝ) * ρ) ^ (b + 1)) / ((((b + 1).factorial : ℕ) : ℝ)) :=
    htaylor.trans (add_le_add hS hR)
  -- ## Step 3: the Lipschitz bound from `Ψ t` to `y`
  have hlip := poly_lipschitz_bound (μ := μ) (d := d) (N := Q) (y := y) (y' := Ψ t)
    P hPdeg hPcoef hy1 (hΨval t htU)
  have hdist' : ‖y - Ψ t‖ < ε := by
    have h : ‖y - Ψ t‖ = dist (Ψ t) y := by rw [dist_eq_norm, norm_sub_rev]
    rw [h]; exact hdist
  have hsum := sum_abs_sub_le (μ := μ) (y := y) (y' := Ψ t) hdist'
  have hG : |(P.map (Int.castRingHom ℝ)).eval y - (P.map (Int.castRingHom ℝ)).eval (Ψ t)|
      ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ) * ((μ : ℝ) + 1) * ε := by
    refine hlip.trans ?_
    have hK : 0 ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ) := by positivity
    calc ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ))
          * (∑ i, |y i - Ψ t i|)
        ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ))
            * (((μ : ℝ) + 1) * ε) := mul_le_mul_of_nonneg_left hsum hK
      _ = (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) * (d : ℝ) * ((μ : ℝ) + 1) * ε := by
          ring
  -- ## Step 4: the Liouville comparison
  refine vanishes_of_bounds (μ := μ) (d := d) (g := g) (H := H) (N := Q)
    (y := y) (y' := Ψ t) hH hQ P hPne hPdeg hPcoef hyHH hT hG ?_
  have h := hineq
  rw [Work.WilkiesH.Interp.above, Work.WilkiesH.Interp.liou] at h
  exact h

end Work.WilkiesH.Interp
