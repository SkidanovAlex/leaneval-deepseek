import Mathlib
import Submission.Work.WilE4.CAD.gcd_cont_welloriented

namespace Work.WilE4.CAD

open Polynomial Filter
open scoped Topology

noncomputable section

/-- If the coefficients of a sequence of polynomials of bounded degree converge, then their
evaluation at a fixed point converges to the evaluation of the limit. -/
theorem tendsto_eval_of_tendsto_coeff {P : ℕ → Polynomial ℝ} {P₀ : Polynomial ℝ} {D : ℕ}
    (hD : ∀ n, (P n).natDegree ≤ D) (hD₀ : P₀.natDegree ≤ D)
    (h : ∀ k, Filter.Tendsto (fun n => (P n).coeff k) Filter.atTop (nhds (P₀.coeff k)))
    (w : ℝ) :
    Filter.Tendsto (fun n => (P n).eval w) Filter.atTop (nhds (P₀.eval w)) := by
  have hsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range (D + 1), (P n).coeff j * w ^ j) Filter.atTop
      (nhds (∑ j ∈ Finset.range (D + 1), P₀.coeff j * w ^ j)) :=
    tendsto_finsetSum _ (fun j _ => (h j).mul tendsto_const_nhds)
  have hgoal : P₀.eval w = ∑ j ∈ Finset.range (D + 1), P₀.coeff j * w ^ j :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD₀) w
  rw [hgoal]
  refine hsum.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hD n)) w).symm

/-- **Continuity of the gcd along a sequence contained in a degree-constant set.**

On the set `C` the degrees of `f`, `g` and of `gcd (f ·) (g ·)` are the constants `p`, `q`, `ν`.
This is enough to identify `gcd (f ·) (g ·)` on `C` with an explicitly continuous function:  the
proof is a case distinction on `ν` mirroring `gcd_cont_welloriented`, using only the *pointwise*
degree facts at the points of `C` (rather than an entire neighbourhood of `x₀`). -/
theorem gcd_coeff_tendsto_of_deg_const_on_C {m p q ν : ℕ}
    (f g : (Fin m → ℝ) → Polynomial ℝ) {C : Set (Fin m → ℝ)} {x₀ : Fin m → ℝ}
    (hx₀ : x₀ ∈ C) (u : ℕ → Fin m → ℝ) (huC : ∀ n, u n ∈ C)
    (hulim : Filter.Tendsto u Filter.atTop (nhds x₀))
    (hf : ∀ k, Continuous fun x => (f x).coeff k)
    (hg : ∀ k, Continuous fun x => (g x).coeff k)
    (hfne : ∀ x ∈ C, f x ≠ 0) (hgne : ∀ x ∈ C, g x ≠ 0)
    (hfdeg : ∀ x ∈ C, (f x).natDegree = p) (hgdeg : ∀ x ∈ C, (g x).natDegree = q)
    (hgcd : ∀ x ∈ C, (gcd (f x) (g x)).natDegree = ν) :
    ∀ k, Filter.Tendsto (fun n => (gcd (f (u n)) (g (u n))).coeff k) Filter.atTop
      (nhds ((gcd (f x₀) (g x₀)).coeff k)) := by
  classical
  -- `gcd (f x) (g x) ≠ 0` on `C`, since both `f x` and `g x` are non-zero there.
  have hgcdne : ∀ x ∈ C, gcd (f x) (g x) ≠ 0 := by
    intro x hx hzero
    exact hfne x hx ((gcd_eq_zero_iff (f x) (g x)).mp hzero).1
  -- It suffices to exhibit a continuous `G` agreeing with the gcd on `C`.
  have key : ∀ G : (Fin m → ℝ) → Polynomial ℝ,
      (∀ x ∈ C, gcd (f x) (g x) = G x) →
      (∀ k, ContinuousAt (fun x => (G x).coeff k) x₀) →
      ∀ k, Filter.Tendsto (fun n => (gcd (f (u n)) (g (u n))).coeff k) Filter.atTop
        (nhds ((gcd (f x₀) (g x₀)).coeff k)) := by
    intro G hG hGc k
    have hlim : Filter.Tendsto (fun n => (G (u n)).coeff k) Filter.atTop
        (nhds ((G x₀).coeff k)) := (hGc k).tendsto.comp hulim
    have hval : (G x₀).coeff k = (gcd (f x₀) (g x₀)).coeff k := by rw [← hG x₀ hx₀]
    have hfun : (fun n => (G (u n)).coeff k) =
        fun n => (gcd (f (u n)) (g (u n))).coeff k := by
      funext n; rw [hG (u n) (huC n)]
    rw [hfun, hval] at hlim
    exact hlim
  by_cases hν0 : ν = 0
  · -- `ν = 0`: the gcd is the constant `1`
    refine key (fun _ => 1) ?_ ?_
    · intro x hx
      refine eq_one_of_monic_natDegree_zero (monic_gcd_of_ne_zero (hgcdne x hx)) ?_
      rw [hgcd x hx, hν0]
    · intro k
      exact continuousAt_const
  · by_cases hνp : ν = p
    · -- `ν = p`: the gcd is the normalisation of `f`
      refine key (fun x => Polynomial.C (((f x).coeff p)⁻¹) * f x) ?_ ?_
      · intro x hx
        have hfx : f x ≠ 0 := hfne x hx
        have h1 : gcd (f x) (g x) = normalize (f x) :=
          eq_normalize_of_dvd_of_natDegree_eq (monic_gcd_of_ne_zero (hgcdne x hx)) hfx
            (gcd_dvd_left _ _) (by rw [hfdeg x hx, hgcd x hx, hνp])
        have h2 : normalize (f x) = Polynomial.C (((f x).coeff p)⁻¹) * f x := by
          rw [normalize_apply, coe_normUnit_of_ne_zero hfx, Polynomial.leadingCoeff,
            hfdeg x hx, mul_comm]
        rw [h1, h2]
      · intro k
        have hfun : (fun x => (Polynomial.C (((f x).coeff p)⁻¹) * f x).coeff k)
            = fun x => ((f x).coeff p)⁻¹ * (f x).coeff k := by
          funext x
          rw [Polynomial.coeff_C_mul]
        rw [hfun]
        have hxp : (f x₀).coeff p ≠ 0 := by
          rw [← hfdeg x₀ hx₀, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr (hfne x₀ hx₀)
        exact (((hf p).continuousAt).inv₀ hxp).mul ((hf k).continuousAt)
    · by_cases hνq : ν = q
      · -- `ν = q`: the gcd is the normalisation of `g`
        refine key (fun x => Polynomial.C (((g x).coeff q)⁻¹) * g x) ?_ ?_
        · intro x hx
          have hgx : g x ≠ 0 := hgne x hx
          have h1 : gcd (f x) (g x) = normalize (g x) :=
            eq_normalize_of_dvd_of_natDegree_eq (monic_gcd_of_ne_zero (hgcdne x hx)) hgx
              (gcd_dvd_right _ _) (by rw [hgdeg x hx, hgcd x hx, hνq])
          have h2 : normalize (g x) = Polynomial.C (((g x).coeff q)⁻¹) * g x := by
            rw [normalize_apply, coe_normUnit_of_ne_zero hgx, Polynomial.leadingCoeff,
              hgdeg x hx, mul_comm]
          rw [h1, h2]
        · intro k
          have hfun : (fun x => (Polynomial.C (((g x).coeff q)⁻¹) * g x).coeff k)
              = fun x => ((g x).coeff q)⁻¹ * (g x).coeff k := by
            funext x
            rw [Polynomial.coeff_C_mul]
          rw [hfun]
          have hxq : (g x₀).coeff q ≠ 0 := by
            rw [← hgdeg x₀ hx₀, Polynomial.coeff_natDegree]
            exact Polynomial.leadingCoeff_ne_zero.mpr (hgne x₀ hx₀)
          exact (((hg q).continuousAt).inv₀ hxq).mul ((hg k).continuousAt)
      · -- `ν < p` and `ν < q`: the gcd is read off from the Sylvester-type system
        have h0ne : gcd (f x₀) (g x₀) ≠ 0 := hgcdne x₀ hx₀
        have hνltp : ν < p := by
          by_contra hcon
          have hle : ν ≤ p := by
            obtain ⟨d, hd⟩ := gcd_dvd_left (f x₀) (g x₀)
            have hd0 : d ≠ 0 := by
              rintro rfl; rw [mul_zero] at hd; exact (hfne x₀ hx₀) hd
            have hmul := natDegree_mul (monic_gcd_of_ne_zero h0ne).ne_zero hd0
            rw [← hd, hgcd x₀ hx₀] at hmul
            have hfp := hfdeg x₀ hx₀
            omega
          exact hνp (le_antisymm hle (not_lt.mp hcon))
        have hνltq : ν < q := by
          by_contra hcon
          have hle : ν ≤ q := by
            obtain ⟨d, hd⟩ := gcd_dvd_right (f x₀) (g x₀)
            have hd0 : d ≠ 0 := by
              rintro rfl; rw [mul_zero] at hd; exact (hgne x₀ hx₀) hd
            have hmul := natDegree_mul (monic_gcd_of_ne_zero h0ne).ne_zero hd0
            rw [← hd, hgcd x₀ hx₀] at hmul
            have hgq := hgdeg x₀ hx₀
            omega
          exact hνq (le_antisymm hle (not_lt.mp hcon))
        refine key (fun x => ∑ j, Polynomial.C (sylY f g p q ν hνltq x j) *
            sylCol f g p q ν x j) ?_ ?_
        · intro x hx
          exact (sylY_spec (hfne x hx) (hgne x hx) (hfdeg x hx) (hgdeg x hx)
            (hgcd x hx) hνltp hνltq).symm
        · intro k
          exact continuousAt_coeff_sylW hf hg hνltq
            (sylMat_det_ne_zero (hfne x₀ hx₀) (hgne x₀ hx₀) (hfdeg x₀ hx₀)
              (hgdeg x₀ hx₀) (hgcd x₀ hx₀) hνltp hνltq) k

theorem gcd_eval_tendsto_of_deg_const {m p q ν : ℕ}
    (f g : (Fin m → ℝ) → Polynomial ℝ) {C : Set (Fin m → ℝ)} {x₀ : Fin m → ℝ}
    (hx₀ : x₀ ∈ C) (u : ℕ → Fin m → ℝ) (huC : ∀ n, u n ∈ C)
    (hulim : Filter.Tendsto u Filter.atTop (nhds x₀))
    (hf : ∀ k, Continuous fun x => (f x).coeff k)
    (hg : ∀ k, Continuous fun x => (g x).coeff k)
    (hfne : ∀ x ∈ C, f x ≠ 0) (hgne : ∀ x ∈ C, g x ≠ 0)
    (hfdeg : ∀ x ∈ C, (f x).natDegree = p) (hgdeg : ∀ x ∈ C, (g x).natDegree = q)
    (hgcd : ∀ x ∈ C, (gcd (f x) (g x)).natDegree = ν)
    (w : ℝ) :
    Filter.Tendsto (fun n => (gcd (f (u n)) (g (u n))).eval w) Filter.atTop
      (nhds ((gcd (f x₀) (g x₀)).eval w)) := by
  refine tendsto_eval_of_tendsto_coeff (P := fun n => gcd (f (u n)) (g (u n)))
    (P₀ := gcd (f x₀) (g x₀)) (D := ν) ?_ ?_ ?_ w
  · intro n; exact le_of_eq (hgcd (u n) (huC n))
  · exact le_of_eq (hgcd x₀ hx₀)
  · exact gcd_coeff_tendsto_of_deg_const_on_C f g hx₀ u huC hulim hf hg hfne hgne hfdeg hgdeg hgcd

end

end Work.WilE4.CAD
