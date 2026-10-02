/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The transit error of the approximate perturbed Fatou coordinate

Summing the per-step error of `Work.Implosion.Approx.approxEcal_step` along an orbit
that stays in the transit strip gives, uniformly in the number of steps,

  `Ũ(u_n) - Ũ(u_0) + n = O(1/R + λ)`,

where `u_n = modelOrbit a h n u_0`, `Ũ = approxEcal a (1-h₁)`, `λ = ‖a‖` and `R`
is the distance to the ends of the strip.  Two ingredients make the sum uniform:
the per-step displacement has real part `≤ -1/40` (so the number of steps inside
the strip is `≤ 40π/λ`), and `‖ecalPt a u‖ ≤ 10(λ + 1/dist(u,ends))` on the strip
(so `∑ ‖ζ(u_k)‖² ≤ O(1/R)` by telescoping).
-/

import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Phase
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Approx.approxEcal_step
import Submission.Work.Implosion.Approx.ecalPt_norm_le_of_re
import Submission.Work.Implosion.Approx.modelDisp_bounds
import Submission.Work.Implosion.Approx.sum_inv_sq_le_of_mono

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx
open Complex
open Work.Implosion
open scoped BigOperators

lemma telescopes (f : ℕ → ℂ) (N : ℕ) :
    f N - f 0 + (N : ℂ) = ∑ k ∈ Finset.range N, (f (k+1) - f k + 1) := by
  induction N with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      push_cast
      ring


lemma sum_range_const_real (n : ℕ) (c : ℝ) : ∑ _k ∈ Finset.range n, c = (n:ℝ)*c := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma one_div_min_sq_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (min a b)^2 ≤ 1/a^2 + 1/b^2 := by
  rw [min_def]; split_ifs with hab
  · have h : (0:ℝ) < a^2 := by positivity
    have h' : (0:ℝ) < b^2 := by positivity
    have : 0 < 1/b^2 := by positivity
    linarith
  · have h : (0:ℝ) < a^2 := by positivity
    have h' : (0:ℝ) < b^2 := by positivity
    have : 0 < 1/a^2 := by positivity
    linarith

theorem approxEcal_transit (h : ℂ → ℂ) (h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A) (hb : ImplosionBounds h h1 A r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam R : ℝ) (a : ℂ) (u0 : ℂ) (n : ℕ), 0 < lam → a = (lam : ℂ) * I →
      (∀ k : ℕ, k ≤ n → GoodTransit a h lam R (modelOrbit a h k u0)) →
      (∀ k : ℕ, k ≤ n → ‖ecalPt a (modelOrbit a h k u0)‖ < r) →
      (∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          Complex.sinh (a * (modelOrbit a h k u0
              + (t : ℂ) * modelDisp a h (modelOrbit a h k u0))) / a ∈ Complex.slitPlane) →
      ‖approxEcal a (1 - h1) (modelOrbit a h n u0) - approxEcal a (1 - h1) u0 + n‖
        ≤ C * (1 / R + lam) := by
  obtain ⟨Cst, hCst0, hstep⟩ := approxEcal_step h h1 A r hA hb
  refine ⟨Cst * 32200 + 1, by positivity, ?_⟩
  intro lam R a u0 n hlam ha hGT hζr hslit

  subst ha
  set aa : ℂ := (lam : ℂ) * I with haa
  -- extract the GoodTransit data
  have key : ∀ k : ℕ, k ≤ n →
      (R ≤ (modelOrbit aa h k u0).re ∧ (modelOrbit aa h k u0).re ≤ Real.pi/lam - R) ∧ 4 ≤ R
      ∧ 4 * (‖ecalPt aa (modelOrbit aa h k u0)‖ + lam) ≤ 1
      ∧ ‖h (ecalPt aa (modelOrbit aa h k u0)) - 1‖ ≤ 1/2
      ∧ ‖h (ecalPt aa (modelOrbit aa h k u0))‖ ≤ 2
      ∧ Complex.sinh (aa * (modelOrbit aa h k u0)) / aa ∈ Complex.slitPlane := by
    intro k hk
    have hk' := hGT k hk
    simp only [GoodTransit, transitStrip, Set.mem_ofPred_eq] at hk'
    exact hk'
  have hstrip : ∀ k : ℕ, k ≤ n →
      R ≤ (modelOrbit aa h k u0).re ∧ (modelOrbit aa h k u0).re ≤ Real.pi/lam - R :=
    fun k hk => (key k hk).1
  have hR4 : 4 ≤ R := (key 0 (Nat.zero_le n)).2.1
  have hsmall : ∀ k : ℕ, k ≤ n → 4 * (‖ecalPt aa (modelOrbit aa h k u0)‖ + lam) ≤ 1 :=
    fun k hk => (key k hk).2.2.1
  have hh1 : ∀ k : ℕ, k ≤ n → ‖h (ecalPt aa (modelOrbit aa h k u0)) - 1‖ ≤ 1/2 :=
    fun k hk => (key k hk).2.2.2.1
  have hRpos : (0:ℝ) < R := by linarith
  -- step decrease
  have stepdec : ∀ k : ℕ, k < n →
      (modelOrbit aa h (k+1) u0).re ≤ (modelOrbit aa h k u0).re - 1/40 := by
    intro k hk
    have hk1 : k ≤ n := Nat.le_of_lt hk
    have hs' : ‖ecalPt aa (modelOrbit aa h k u0)‖ + lam ≤ 1/4 := by linarith [hsmall k hk1]
    have hbnd := modelDisp_bounds lam h (modelOrbit aa h k u0) hlam hs' (hh1 k hk1)
    have hsucc : modelOrbit aa h (k+1) u0
        = modelOrbit aa h k u0 + modelDisp aa h (modelOrbit aa h k u0) :=
      modelOrbit_succ aa h k u0
    rw [hsucc, Complex.add_re]
    linarith [hbnd.1]
  -- monotonicity in k
  have hmono : ∀ k : ℕ, k ≤ n → (modelOrbit aa h k u0).re ≤ (modelOrbit aa h 0 u0).re - (k:ℝ)/40 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ j ih =>
        intro hk
        have hj : j < n := Nat.lt_of_succ_le hk
        have hdec := stepdec j hj
        have ih' := ih (Nat.le_of_lt hj)
        push_cast
        linarith
  -- the number of steps is at most 40*pi/lam
  have hn : (n:ℝ) ≤ 40 * Real.pi / lam := by
    rw [mul_div_assoc]
    have hxn := (hstrip n le_rfl).1
    have hx0 := (hstrip 0 (Nat.zero_le n)).2
    have hm := hmono n le_rfl
    linarith
  have hnlam : (n:ℝ) * lam^2 ≤ 40 * Real.pi * lam := by
    have h1 : (n:ℝ) * lam^2 ≤ (40*Real.pi/lam) * lam^2 := by
      have hpos : (0:ℝ) ≤ lam^2 := sq_nonneg lam
      exact mul_le_mul_of_nonneg_right hn hpos
    have h2 : (40*Real.pi/lam) * lam^2 = 40*Real.pi*lam := by field_simp
    rw [h2] at h1; exact h1
  have hlampos : (0:ℝ) < lam := hlam

  -- ===== the main estimate =====
  -- telescoping the approximate Fatou coordinate
  have htel : approxEcal aa (1 - h1) (modelOrbit aa h n u0) - approxEcal aa (1 - h1) u0 + (n : ℂ)
      = ∑ k ∈ Finset.range n,
          (approxEcal aa (1 - h1) (modelOrbit aa h (k+1) u0)
            - approxEcal aa (1 - h1) (modelOrbit aa h k u0) + 1) := by
    simpa using telescopes (fun k => approxEcal aa (1 - h1) (modelOrbit aa h k u0)) n
  rw [htel]
  -- the per-step error bound
  have herr : ∀ k : ℕ, k < n →
      ‖approxEcal aa (1 - h1) (modelOrbit aa h (k+1) u0)
        - approxEcal aa (1 - h1) (modelOrbit aa h k u0) + 1‖
      ≤ Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2) := by
    intro k hk
    have hk1 : k ≤ n := Nat.le_of_lt hk
    have hw : modelOrbit aa h (k+1) u0
        = modelOrbit aa h k u0 + modelDisp aa h (modelOrbit aa h k u0) :=
      modelOrbit_succ aa h k u0
    have hres := hstep lam R aa hlam haa (modelOrbit aa h k u0) (hGT k hk1) (hζr k hk1)
      (by intro t ht; simpa [hw] using hslit k hk t ht)
    simpa [hw] using hres
  -- the sums
  have hSx0 : ∑ k ∈ Finset.range n, (1 / ((modelOrbit aa h k u0).re)^2)
      ≤ 1/R^2 + 1/((1/40)*R) := by
    refine le_trans ?_ (sum_inv_sq_le_of_mono (fun k => (modelOrbit aa h k u0).re) (1/40) R n
      (by norm_num) hRpos (Or.inl stepdec) (fun k hk => (hstrip k hk).1))
    rw [Finset.sum_range_succ]
    have : 0 ≤ 1 / ((modelOrbit aa h n u0).re)^2 := by
      have := (hstrip n le_rfl).1
      positivity
    linarith
  have hSy0 : ∑ k ∈ Finset.range n, (1 / (Real.pi/lam - (modelOrbit aa h k u0).re)^2)
      ≤ 1/R^2 + 1/((1/40)*R) := by
    refine le_trans ?_ (sum_inv_sq_le_of_mono (fun k => Real.pi/lam - (modelOrbit aa h k u0).re)
      (1/40) R n (by norm_num) hRpos
      (Or.inr (fun k hk => by have := stepdec k hk; linarith))
      (fun k hk => by have := (hstrip k hk).2; linarith))
    rw [Finset.sum_range_succ]
    have : 0 ≤ 1 / (Real.pi/lam - (modelOrbit aa h n u0).re)^2 := by
      have hx := (hstrip n le_rfl).2
      have hpos : 0 < Real.pi/lam - (modelOrbit aa h n u0).re := by linarith
      positivity
    linarith
  -- sum of 1/d_k^2, d_k the pointwise minimum
  have hSdk : ∑ k ∈ Finset.range n,
        1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
      ≤ 2 * (1/R^2 + 1/((1/40)*R)) := by
    have hterm : ∀ k ∈ Finset.range n,
        1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        ≤ 1 / ((modelOrbit aa h k u0).re)^2
          + 1 / (Real.pi/lam - (modelOrbit aa h k u0).re)^2 := by
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      have hk1 : k ≤ n := Nat.le_of_lt hk'
      have ha1 := (hstrip k hk1).1
      have ha2 := (hstrip k hk1).2
      exact one_div_min_sq_le _ _ (lt_of_lt_of_le hRpos ha1) (by linarith)
    have hh := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib] at hh
    linarith
  -- sum of |zeta|^2 via the strip bound
  have hSz : ∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2
      ≤ ∑ k ∈ Finset.range n,
          (10 * (lam + 1/min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re)))^2 := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hk1 : k ≤ n := Nat.le_of_lt hk'
    have ha1 := (hstrip k hk1).1
    have ha2 := (hstrip k hk1).2
    have hb := ecalPt_norm_le_of_re lam (modelOrbit aa h k u0) hlam
      (lt_of_lt_of_le hRpos ha1) (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hSz2 : ∑ k ∈ Finset.range n,
          (10 * (lam + 1/min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re)))^2
      ≤ 10^2 * ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hk1 : k ≤ n := Nat.le_of_lt hk'
    have ha1 := (hstrip k hk1).1
    have ha2 := (hstrip k hk1).2
    have hx : 0 < (modelOrbit aa h k u0).re := lt_of_lt_of_le hRpos ha1
    have hy : 0 < Real.pi/lam - (modelOrbit aa h k u0).re := by linarith
    have h2 : 0 ≤ 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re) :=
      div_nonneg zero_le_one (le_of_lt (lt_min hx hy))
    have hpow : (1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        = 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2 := by
      rw [div_pow, one_pow]
    have key : (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        ≤ 2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
      nlinarith [sq_nonneg (lam - 1/min ((modelOrbit aa h k u0).re)
        (Real.pi/lam - (modelOrbit aa h k u0).re)), hpow]
    calc (10 * (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re)))^2
        = 10^2 * (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2 := by ring
      _ ≤ 10^2 * (2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)) :=
          mul_le_mul_of_nonneg_left key (by norm_num)
  have hSz3 : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
      ≤ 2 * ((n:ℝ) * lam^2 + ∑ k ∈ Finset.range n,
          1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
    have hsum : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
        = 2 * ((n:ℝ) * lam^2 + ∑ k ∈ Finset.range n,
          1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_range_const_real n (lam^2)]
    rw [hsum]
  have hSζ : ∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2
      ≤ 200 * ((n:ℝ) * lam^2 + 2 * (1/R^2 + 1/((1/40)*R))) := by
    have h1 : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
        ≤ 2 * ((n:ℝ) * lam^2 + 2 * (1/R^2 + 1/((1/40)*R))) := by
      linarith [hSz3, hSdk]
    linarith [hSz, hSz2, h1]
  -- put everything together
  have hmain : ‖∑ k ∈ Finset.range n,
        (approxEcal aa (1 - h1) (modelOrbit aa h (k+1) u0)
          - approxEcal aa (1 - h1) (modelOrbit aa h k u0) + 1)‖
      ≤ Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2)
          + (n:ℝ) * lam^2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ k ∈ Finset.range n,
          ‖approxEcal aa (1 - h1) (modelOrbit aa h (k+1) u0)
            - approxEcal aa (1 - h1) (modelOrbit aa h k u0) + 1‖
        ≤ ∑ k ∈ Finset.range n, Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2) :=
      Finset.sum_le_sum (fun k hk => herr k (Finset.mem_range.mp hk))
    have h2 : ∑ k ∈ Finset.range n, Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2)
        = Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2)
          + (n:ℝ) * lam^2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_range_const_real n (lam^2)]
    linarith [h1, h2.le, h2.ge]
  refine le_trans hmain ?_
  -- final arithmetic
  have hbnd : (∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2) + (n:ℝ) * lam^2
      ≤ 32200 * (1/R + lam) := by
    have hD : 1/R^2 + 1/((1/40)*R) ≤ 41 * (1/R) := by
      have h2 : 1/((1/40)*R) = 40*(1/R) := by field_simp
      have h3 : (1:ℝ)/R^2 ≤ 1/R := by
        have h4 : 1/R ≤ 1 := by
          rw [div_le_one hRpos]
          linarith
        have h5 : 0 ≤ 1/R := by positivity
        calc 1/R^2 = (1/R) * (1/R) := by ring
          _ ≤ 1 * (1/R) := mul_le_mul_of_nonneg_right h4 h5
          _ = 1/R := by ring
      rw [h2]
      linarith
    have h5 : 201 * ((n:ℝ) * lam^2) + 400 * (41 * (1/R))
        ≤ 32200 * (1/R + lam) := by
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have h6 : 0 ≤ lam := le_of_lt hlam
      have h7 : 0 ≤ 1/R := by positivity
      have h8 : (n:ℝ) * lam^2 ≤ 40 * Real.pi * lam := hnlam
      nlinarith [hpi, h6, h7, h8]
    linarith [hSζ, hD, h5]
  calc Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2) + (n:ℝ) * lam^2)
      ≤ Cst * (32200 * (1/R + lam)) := mul_le_mul_of_nonneg_left hbnd hCst0
    _ = (Cst * 32200) * (1/R + lam) := by ring
    _ ≤ (Cst * 32200 + 1) * (1/R + lam) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

end Work.Implosion.Approx
