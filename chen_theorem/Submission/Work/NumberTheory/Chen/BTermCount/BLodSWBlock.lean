import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.primeCharSumBound

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# A dyadic-block character sum (the `B`-term "small/large window block")

This file proves `BLodSWBlock`: for a fixed primitive non-principal Dirichlet
character `ψ` of modulus `r ≤ (log x)^C`, the `ψ`-twist of the `a`-coefficient of
a dyadic block `[Q_j, 2 Q_j)` (with `Q_j = blockStart M j`, `x^{1/14} ≤ M`),
cut down to the primes `q ≤ T`, is `O(Q_j / (log x)^A)`:

`‖∑_{q ≤ 2 Q_j} [q ≤ T] aCoeff M Y j q ψ(q)‖ ≤ 4 Q_j / (log x)^A`.

The mechanism is Siegel–Walfisz in the shape `primeCharSumBound`: the sum is
supported on primes of `[Q_j, 2 Q_j)` with `Q_j ≥ x^{1/14}`, so it is a
difference of the two shifted prime-character sums up to `U ≤ 2 Q_j - 1` and up
to `Q_j`, both of which lie in the range `[x^{1/14}, x]` of the Siegel–Walfisz
estimate.  The remaining `ψ(Q_j)` boundary term costs `1`, absorbed by the
eventual inequality `(log x)^A ≤ x^{1/14}`.

## Main auxiliary steps

* `sumIccFilter_sub`: `∑_{a ≤ q ≤ b} = ∑_{1 ≤ q ≤ b} - ∑_{1 ≤ q ≤ a-1}`
  (as sums over `P`-filtered ranges);
* `sumIccFilter_prime_succ_top`: `∑_{1 ≤ q ≤ Q} = ∑_{1 ≤ q ≤ Q-1} + [Q prime]·f Q`;
* `blockSum_eq'`: the `a`-coefficient sum over the dyadic block is exactly the
  prime sum over `[Q_j, min (2 Q_j - 1) (min T (Y-1))]`.
-/

/-- Splitting a `P`-filtered sum over `[a,b]` off the full sum over `[1,b]`:
the interval `[1, b]` is the disjoint union of `[1, a-1]` and `[a, b]`. -/
private lemma sumIccFilter_sub (F : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ q ∈ (Finset.Icc a b).filter P, F q)
      = (∑ q ∈ (Finset.Icc 1 b).filter P, F q)
        - (∑ q ∈ (Finset.Icc 1 (a - 1)).filter P, F q) := by
  set g : ℕ → ℂ := fun q => if P q then F q else 0 with hg
  have h1 : (∑ q ∈ (Finset.Icc a b).filter P, F q) = ∑ q ∈ Finset.Ico a (b + 1), g q := by
    rw [Finset.sum_filter, ← Finset.Ico_add_one_right_eq_Icc a b]
  have h2 : (∑ q ∈ (Finset.Icc 1 b).filter P, F q) = ∑ q ∈ Finset.Ico 1 (b + 1), g q := by
    rw [Finset.sum_filter, ← Finset.Ico_add_one_right_eq_Icc 1 b]
  have h3 : (∑ q ∈ (Finset.Icc 1 (a - 1)).filter P, F q) = ∑ q ∈ Finset.Ico 1 a, g q := by
    rw [Finset.sum_filter, ← Finset.Ico_add_one_right_eq_Icc 1 (a - 1), Nat.sub_add_cancel ha]
  have hcons := Finset.sum_Ico_consecutive g ha (by omega : a ≤ b + 1)
  rw [h1, h2, h3]
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hcons)

/-- Peeling the top index off a prime-filtered sum: for `1 ≤ Q`,
`∑_{q ≤ Q, q prime} F q = ∑_{q ≤ Q-1, q prime} F q + [Q prime] F Q`. -/
private lemma sumIccFilter_prime_succ_top (F : ℕ → ℂ) {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), F q)
      = (∑ q ∈ (Finset.Icc 1 (Q - 1)).filter (fun q => q.Prime), F q)
        + (if Q.Prime then F Q else 0) := by
  set g : ℕ → ℂ := fun q => if q.Prime then F q else 0 with hg
  have hb : (∑ q ∈ Finset.Icc 1 ((Q-1)+1), g q)
      = ∑ q ∈ Finset.Icc 1 (Q-1), g q + g ((Q-1)+1) :=
    Finset.sum_Icc_succ_top (by omega : 1 ≤ (Q-1)+1) g
  rw [Nat.sub_add_cancel hQ] at hb
  have e1 : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), F q)
      = ∑ q ∈ Finset.Icc 1 Q, g q := by
    rw [Finset.sum_filter]
  have e2 : (∑ q ∈ (Finset.Icc 1 (Q-1)).filter (fun q => q.Prime), F q)
      = ∑ q ∈ Finset.Icc 1 (Q-1), g q := by
    rw [Finset.sum_filter]
  rw [e1, e2, hb]

/-- The `a`-coefficient of the dyadic block `[Q, 2Q)` (`Q = blockStart M j`,
`M ≥ 1`) cut by `q ≤ T` is exactly the prime sum over
`[Q, min (2Q - 1) (min T (Y - 1))]`. -/
private lemma blockSum_eq' (M Y j T : ℕ) (F : ℕ → ℂ) (Q : ℕ)
    (hQ : Q = blockStart M j) (hQ1 : 1 ≤ Q) (hMQ : M ≤ Q) :
    (∑ q ∈ Finset.Icc 1 (2 * Q),
        (if q ≤ T then (1:ℂ) else 0) * aCoeff M Y j q * F q)
      = ∑ q ∈ (Finset.Icc Q (min (2 * Q - 1) (min T (Y - 1)))).filter
          (fun q => q.Prime), F q := by
  set U : ℕ := min (2 * Q - 1) (min T (Y - 1)) with hU
  have hU1 : U ≤ 2 * Q - 1 := by rw [hU]; exact min_le_left _ _
  have hUY : U ≤ Y - 1 := by rw [hU]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hUT : U ≤ T := by rw [hU]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hsub : (Finset.Icc Q U).filter (fun q => q.Prime) ⊆ Finset.Icc 1 (2 * Q) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [Finset.mem_Icc]
    obtain ⟨⟨hxa, hxb⟩, -⟩ := hx
    exact ⟨by omega, by omega⟩
  have hzero : ∀ x ∈ Finset.Icc 1 (2 * Q), x ∉ (Finset.Icc Q U).filter (fun q => q.Prime) →
      (if x ≤ T then (1:ℂ) else 0) * aCoeff M Y j x * F x = 0 := by
    intro x hx hxnot
    rw [Finset.mem_Icc] at hx
    have hxnot' : ¬(Q ≤ x ∧ x ≤ U ∧ x.Prime) := by
      intro h
      exact hxnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    by_contra hne
    have hxT : x ≤ T := by
      by_contra hxT
      exact hne (by simp [hxT])
    have hcoeff : aCoeff M Y j x ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; ring)
    have hcond : x.Prime ∧ M ≤ x ∧ x < Y ∧ Q ≤ x ∧ x < 2 * Q := by
      by_contra hc
      rw [hQ] at hc
      exact hcoeff (by unfold aCoeff; exact if_neg hc)
    obtain ⟨hprime, hMx, hxY, hQx, hx2Q⟩ := hcond
    have hxU : x ≤ U := by
      rw [hU]
      exact le_min (by omega) (le_min hxT (by omega))
    exact hxnot' ⟨hQx, hxU, hprime⟩
  have h1 := Finset.sum_subset hsub hzero
  have h2 : (∑ x ∈ (Finset.Icc Q U).filter (fun q => q.Prime),
      (if x ≤ T then (1:ℂ) else 0) * aCoeff M Y j x * F x)
      = ∑ x ∈ (Finset.Icc Q U).filter (fun q => q.Prime), F x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hQx, hxU⟩, hpx⟩ := hx
    have hxT : x ≤ T := le_trans hxU hUT
    have hltY : x < Y := by omega
    have hlt2Q : x < 2 * Q := by omega
    have hMQx : M ≤ x := le_trans hMQ hQx
    have : aCoeff M Y j x = 1 := by
      unfold aCoeff
      rw [← hQ]
      exact if_pos ⟨hpx, hMQx, hltY, hQx, hlt2Q⟩
    rw [this, if_pos hxT]; ring
  exact h1.symm.trans h2

theorem BLodSWBlock (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {r : ℕ}, 2 ≤ r → r ≤ ⌊(Real.log (x:ℝ))^C⌋₊ →
      ∀ (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ (M Y j T : ℕ), (x:ℝ)^((1:ℝ)/14) ≤ M → T ≤ x →
        ‖∑ q ∈ Finset.Icc 1 (2 * blockStart M j),
            (if q ≤ T then (1:ℂ) else 0) * aCoeff M Y j q * ψ ((q:ℕ) : ZMod r)‖
          ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A := by
  -- eventual inputs: Siegel–Walfisz, `x^{1/14} ≥ 1`, `(log x)^A ≥ 2`,
  -- and `(log x)^A ≤ x^{1/14}` (used to absorb the `+1` boundary term)
  have hlogle : ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x:ℝ))^A ≤ (x:ℝ)^((1:ℝ)/14) := by
    have h := eventually_nat_log_pow_mul_le_rpow A (1/14) hA (by norm_num) 1
    simpa using h
  have hlogpow : ∀ᶠ x : ℕ in Filter.atTop, (2:ℝ) ≤ (Real.log (x:ℝ))^A :=
    tendsto_natCast_atTop_atTop.eventually
      (((tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop).eventually_ge_atTop 2)
  filter_upwards [primeCharSumBound A C hA hC,
    eventually_const_le_nat_rpow (by norm_num : (0:ℝ) < 1/14) 1, hlogpow, hlogle]
    with x hSW hxpow hlp hll
  intro r hr2 hrC ψ hprim hne M Y j T hM hT
  set Q : ℕ := blockStart M j with hQ
  have hM1 : 1 ≤ M := by
    have h := le_trans hxpow hM
    exact_mod_cast h
  have hMQ : M ≤ Q := by
    rw [hQ]; unfold blockStart
    exact Nat.le_mul_of_pos_right M (Nat.two_pow_pos j)
  have hQ1 : 1 ≤ Q := le_trans hM1 hMQ
  have hLpos : (0:ℝ) < (Real.log (x:ℝ))^A := lt_of_lt_of_le (by norm_num) hlp
  have hQlam : (Real.log (x:ℝ))^A ≤ (Q:ℝ) :=
    le_trans hll (le_trans hM (by exact_mod_cast hMQ))
  obtain ⟨U, hU⟩ : ∃ U : ℕ, U = min (2 * Q - 1) (min T (Y - 1)) := ⟨_, rfl⟩
  have hUT : U ≤ T := by rw [hU]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hUle2Q : (U:ℝ) ≤ 2 * (Q:ℝ) := by
    have h : U ≤ 2 * Q := by rw [hU]; omega
    exact_mod_cast h
  -- the `a`-coefficient sum is the prime character sum over `[Q, U]`
  have hS : (∑ q ∈ Finset.Icc 1 (2 * Q),
        (if q ≤ T then (1:ℂ) else 0) * aCoeff M Y j q * ψ ((q:ℕ) : ZMod r))
      = ∑ q ∈ (Finset.Icc Q U).filter (fun q => q.Prime), ψ ((q:ℕ) : ZMod r) := by
    rw [hU]
    exact blockSum_eq' M Y j T (fun q => ψ ((q:ℕ) : ZMod r)) Q hQ hQ1 hMQ
  rw [hS]
  rcases le_or_gt Q U with hQU | hQUlt
  · -- the interval `[Q, U]` is nonempty, so `x^{1/14} ≤ Q ≤ U ≤ T ≤ x`
    have hQx : Q ≤ x := le_trans hQU (le_trans hUT hT)
    have hA : ‖∑ q ∈ (Finset.Icc 1 U).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
        ≤ (U:ℝ) / (Real.log (x:ℝ))^A := by
      have h := hSW hr2 hrC ψ hprim hne (U:ℝ)
        (le_trans hM (by exact_mod_cast (le_trans hMQ hQU)))
        (by exact_mod_cast (le_trans hUT hT))
      rwa [Nat.floor_natCast U] at h
    have hQ0 : ‖∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
        ≤ (Q:ℝ) / (Real.log (x:ℝ))^A := by
      have h := hSW hr2 hrC ψ hprim hne (Q:ℝ)
        (le_trans hM (by exact_mod_cast hMQ))
        (by exact_mod_cast hQx)
      rwa [Nat.floor_natCast Q] at h
    have hQm1 : ‖∑ q ∈ (Finset.Icc 1 (Q-1)).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
        ≤ (Q:ℝ) / (Real.log (x:ℝ))^A + 1 := by
      have hid := sumIccFilter_prime_succ_top (fun q => ψ ((q:ℕ) : ZMod r)) hQ1
      have hBC : (∑ q ∈ (Finset.Icc 1 (Q-1)).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r))
          = (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r))
            - (if Q.Prime then ψ ((Q:ℕ):ZMod r) else 0) := by
        rw [hid]; ring
      have h2 : ‖(if Q.Prime then ψ ((Q:ℕ):ZMod r) else 0)‖ ≤ 1 := by
        by_cases hq : Q.Prime
        · rw [if_pos hq]; exact DirichletCharacter.norm_le_one ψ ((Q:ℕ):ZMod r)
        · rw [if_neg hq]; simp
      calc ‖∑ q ∈ (Finset.Icc 1 (Q-1)).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
          = ‖(∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r))
              - (if Q.Prime then ψ ((Q:ℕ):ZMod r) else 0)‖ := by rw [hBC]
        _ ≤ ‖∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
              + ‖(if Q.Prime then ψ ((Q:ℕ):ZMod r) else 0)‖ := norm_sub_le _ _
        _ ≤ (Q:ℝ) / (Real.log (x:ℝ))^A + 1 := add_le_add hQ0 h2
    have hsplit := sumIccFilter_sub (fun q => ψ ((q:ℕ) : ZMod r)) (fun q => q.Prime) hQ1 hQU
    have hfinal : (U:ℝ) / (Real.log (x:ℝ))^A + ((Q:ℝ) / (Real.log (x:ℝ))^A + 1)
        ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
      rw [← mul_le_mul_iff_left₀ hLpos]
      have h1 : ((U:ℝ) / (Real.log (x:ℝ))^A + ((Q:ℝ) / (Real.log (x:ℝ))^A + 1))
            * (Real.log (x:ℝ))^A = (U:ℝ) + (Q:ℝ) + (Real.log (x:ℝ))^A := by
        field_simp
        ring
      have h2 : (4 * (Q:ℝ) / (Real.log (x:ℝ))^A) * (Real.log (x:ℝ))^A = 4 * (Q:ℝ) := by
        field_simp
      rw [h1, h2]
      linarith [hUle2Q, hQlam]
    calc ‖∑ q ∈ (Finset.Icc Q U).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
        ≤ ‖∑ q ∈ (Finset.Icc 1 U).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖
          + ‖∑ q ∈ (Finset.Icc 1 (Q-1)).filter (fun q => q.Prime), ψ ((q:ℕ):ZMod r)‖ := by
          rw [hsplit]; exact norm_sub_le _ _
      _ ≤ (U:ℝ) / (Real.log (x:ℝ))^A + ((Q:ℝ) / (Real.log (x:ℝ))^A + 1) := add_le_add hA hQm1
      _ ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := hfinal
  · -- `U < Q`: the interval is empty
    have hemp : Finset.Icc Q U = ∅ := Finset.Icc_eq_empty_of_lt hQUlt
    rw [hemp, Finset.filter_empty, Finset.sum_empty, norm_zero]
    exact div_nonneg (by positivity) hLpos.le

end Work.NumberTheory.Chen.BTermCount
