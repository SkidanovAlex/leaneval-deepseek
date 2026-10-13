-- Redirected copy of `Submission.Work.DSM2p.untilt_add_le` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_DigLeDefs

/-!
# Subadditivity of the value of an element of the tilt

`Work.DSM2p.untilt_add_le` : for a `p`-adically complete ring `R` (with `p` not a unit) and any
continuous valuation `v` of the unit ball of `R`, the function `nv v x = v (x^♯)` on the tilt
`PreTilt R p` satisfies the nonarchimedean triangle inequality

`nv v (a + b) ≤ max (nv v a) (nv v b)`.

This is the (footnote in Česnavičius–Scholze, *Purity for flat cohomology*, §2.2) fact that a
continuous valuation `|·|` on `A` defines a nonarchimedean valuation `x ↦ |x^♯|` on the tilt `A^♭`.
The underlying formula is

`(a + b)^♯ = lim_n (a_n^♯ + b_n^♯)^{p^n}`,   where `a_n = a^{1/p^n}` in the tilt,

the limit being `p`-adic; since `v` is continuous for the `p`-adic topology this gives the bound.

Formally, this is proved without ever mentioning the limit.  The two inputs are

* `PreTilt.teichmuller_sModEq` (Mathlib): the untilt of `x : PreTilt R p` is congruent to `y^{p^n}`
  modulo `p^{n+1}` for any lift `y ∈ R` of the `n`-th coefficient of `x`; and
* `SModEq.pow_pow_add_one` (Mathlib): the congruence `u ≡ u' [SMOD p]` upgrades to
  `u^{p^n} ≡ u'^{p^n} [SMOD p^{n+1}]`.

Combining them at `x = a_n + b_n` gives `(a + b)^♯ ≡ (a_n^♯ + b_n^♯)^{p^n} [SMOD p^{n+1}]`, while
`(a_n^♯)^{p^n} = a^♯` and `(b_n^♯)^{p^n} = b^♯` make the right hand side have `v`-value at most
`max (nv v a) (nv v b)`.  Since `p^{n+1}` has `v`-value tending to `0`, the claim follows.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.DSM2p

theorem untilt_add_le {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hball : IsUnitBall v Set.univ)
    (hv : ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v (p : R) ^ n < γ) (a b : PreTilt R p) :
    nv v (a + b) ≤ max (nv v a) (nv v b) := by
  rw [nv, nv, nv]
  refine le_of_not_gt ?_
  intro hcon
  -- If the conclusion failed, `nv v (a + b) ≠ 0`, so `v p ^ n < nv v (a+b)` for some `n`.
  have hu0 : v (PreTilt.untilt (a + b)) ≠ 0 := by
    intro h0; rw [h0] at hcon; exact absurd hcon (not_lt.mpr zero_le)
  obtain ⟨n, hn⟩ := hv (v (PreTilt.untilt (a + b))) hu0
  -- `(nv v (a^{1/p^n}))^{p^n} = nv v a`, and likewise for `b`.
  have hval : ∀ x : PreTilt R p,
      (v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] x))) ^ p ^ n
        = v (PreTilt.untilt x) := by
    intro x
    rw [show (v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] x))) ^ p ^ n
        = v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] x) ^ p ^ n)
        from (map_pow v _ _).symm,
      PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
  -- The `n`-th approximant `c = (a_n^♯ + b_n^♯)^{p^n}` has value at most `max (nv v a) (nv v b)`.
  have hc_le : v ((PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
      + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n)
      ≤ max (v (PreTilt.untilt a)) (v (PreTilt.untilt b)) := by
    rw [map_pow]
    have hmax : ∀ X Y : Γ₀, (max X Y) ^ p ^ n = max (X ^ p ^ n) (Y ^ p ^ n) := by
      intro X Y
      rcases le_total X Y with h | h
      · rw [max_eq_right h, max_eq_right (pow_le_pow_left' h (p ^ n))]
      · rw [max_eq_left h, max_eq_left (pow_le_pow_left' h (p ^ n))]
    calc v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
            + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n
        ≤ (max (v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)))
               (v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)))) ^ p ^ n :=
          pow_le_pow_left' (v.map_add_le_max' _ _) (p ^ n)
      _ = max ((v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a))) ^ p ^ n)
              ((v (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b))) ^ p ^ n) :=
          hmax _ _
      _ = max (v (PreTilt.untilt a)) (v (PreTilt.untilt b)) := by
          rw [hval a, hval b]
  -- Congruence of the untilt with the approximant modulo `p^{n+1}`.
  have hmem : PreTilt.untilt (a + b) -
      (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n
      ∈ Ideal.span {(p : R)} ^ (n + 1) := by
    -- `untilt (a_n + b_n) ≡ untilt a_n + untilt b_n` modulo `p`, because the untilt of an element
    -- of the tilt reduces to its `0`-th coefficient and the tilt addition is coordinatewise.
    have hcong : PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] (a + b)) ≡
        (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
          + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b))
        [SMOD Ideal.span {(p : R)}] := by
      rw [SModEq.sub_mem]
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [map_sub, map_add, PreTilt.mk_untilt_eq_coeff_zero,
        PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, sub_self]
    have h2 := SModEq.pow_pow_add_one (I := Ideal.span {(p : R)})
      (Ideal.mem_span_singleton_self (p : R)) hcong n
    rw [PreTilt.untilt_iterate_frobeniusEquiv_symm_pow (a + b) n] at h2
    exact SModEq.sub_mem.mp h2
  have hdiv : (p : R) ^ (n + 1) ∣ PreTilt.untilt (a + b) -
      (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n := by
    rw [Ideal.span_singleton_pow] at hmem
    rwa [Ideal.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hdiv
  -- The error term has value at most `v p ^ (n+1)`, which is `< nv v (a+b)`.
  have hvc : v (PreTilt.untilt (a + b) -
      (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n)
      ≤ v (p : R) ^ (n + 1) := by
    rw [ht, map_mul, map_pow]
    calc v (p : R) ^ (n + 1) * v t ≤ v (p : R) ^ (n + 1) * 1 :=
          mul_le_mul_right (hball t (Set.mem_univ t)) _
      _ = v (p : R) ^ (n + 1) := mul_one _
  have hsplit : v (PreTilt.untilt (a + b)) ≤
      max (v ((PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n))
          (v (PreTilt.untilt (a + b)
            - (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n)) := by
    have h := v.map_add_le_max' ((PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n)
      (PreTilt.untilt (a + b) - (PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] a)
        + PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm)^[n] b)) ^ p ^ n)
    rwa [add_sub_cancel] at h
  have hle : v (PreTilt.untilt (a + b)) ≤
      max (max (v (PreTilt.untilt a)) (v (PreTilt.untilt b))) (v (p : R) ^ (n + 1)) :=
    le_trans hsplit (max_le_max hc_le hvc)
  have hvp : v (p : R) ^ (n + 1) < v (PreTilt.untilt (a + b)) :=
    lt_of_le_of_lt (by
      calc v (p : R) ^ (n + 1) = v (p : R) ^ n * v (p : R) := by rw [pow_succ]
        _ ≤ v (p : R) ^ n * 1 := mul_le_mul_right (hball (p : R) (Set.mem_univ _)) _
        _ = v (p : R) ^ n := mul_one _) hn
  exact absurd hle (not_le.mpr (max_lt_iff.mpr ⟨hcon, hvp⟩))

end Work.DSM2p
