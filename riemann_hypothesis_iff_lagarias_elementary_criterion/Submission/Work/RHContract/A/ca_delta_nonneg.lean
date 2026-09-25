import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Δ = log N_ε − ψ(ξ(ε)) ≥ 0`

For a colossally abundant number `N_ε` with largest prime factor `ξ = ξ(ε) ≥ 1530`, the
excess `Δ := log N_ε − ψ(ξ)` is nonnegative.

Equivalently: `lcm(1,…,ξ)` divides `N_ε`, i.e. the CA exponent `a_p = ⌊μ(p,ε)⌋₊` of every
prime `p ≤ ξ` dominates the exponent `e_p = ⌊log ξ / log p⌋` of `p` in `lcm(1,…,ξ)`.

The key point is that the CA exponent is *not* merely monotone in `p` (which only gives
`a_p ≥ a_ξ ≥ 1`), but dominates the whole `log ξ / log p` scale: the ratio
`R(x) = (x^{1+ε}−1)/(x^{1+ε}−x) = 1 + (x−1)/(x^{1+ε}−x)` is *antitone* on `(1,∞)` (the
associated secant slope `(x^{1+ε}−1)/(x−1)` of the convex power function is increasing),
so for `p ≤ ξ`

`μ(p,ε) = log R(p)/log p ≥ log R(ξ)/log p ≥ log ξ / log p ≥ e_p`,

where `log R(ξ) ≥ log ξ` is exactly the statement `a_ξ ≥ 1` (`ξ` lies in the support).
-/

open scoped BigOperators

namespace Work.RHContract.A

/-- The ratio `(x^{1+ε}−1)/(x^{1+ε}−x)` is antitone on `(1,∞)`: for `1 < a ≤ b`,

  `(b^{1+ε}−1)/(b^{1+ε}−b) ≤ (a^{1+ε}−1)/(a^{1+ε}−a)`.

Indeed both quotients equal `1 + (x−1)/(x^{1+ε}−x)`, and clearing denominators the claim is
`(a^{1+ε}−1)/(a−1) ≤ (b^{1+ε}−1)/(b−1)`, which is the monotonicity of the secant slope of
the convex function `x ↦ x^{1+ε}` on `[0,∞)` (`ConvexOn.secant_mono_aux2`). -/
private lemma ratio_antitone (ε : ℝ) (hε : 0 < ε) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b ^ (1 + ε) - 1) / (b ^ (1 + ε) - b) ≤ (a ^ (1 + ε) - 1) / (a ^ (1 + ε) - a) := by
  rcases eq_or_lt_of_le hab with h | hlt
  · rw [← h]
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ (1 + ε)) :=
    convexOn_rpow (by linarith)
  have hsec := hconv.secant_mono_aux2 (x := 1) (y := a) (z := b)
      (by norm_num : (1 : ℝ) ∈ Set.Ici 0) (by simp only [Set.mem_Ici]; linarith) ha hlt
  have key : (a ^ (1 + ε) - 1) / (a - 1) ≤ (b ^ (1 + ε) - 1) / (b - 1) := by
    simpa using hsec
  have da : 0 < a ^ (1 + ε) - a := by
    have h1 : a < a ^ (1 + ε) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
      have h2 : 1 < a ^ ε := Real.one_lt_rpow ha hε
      nlinarith [ha]
    linarith
  have db : 0 < b ^ (1 + ε) - b := by
    have h1 : b < b ^ (1 + ε) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
      have h2 : 1 < b ^ ε := Real.one_lt_rpow hb hε
      nlinarith [hb]
    linarith
  have ha1 : 0 < a - 1 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have key2 : (a ^ (1 + ε) - 1) * (b - 1) ≤ (b ^ (1 + ε) - 1) * (a - 1) := by
    rw [div_le_div_iff₀ ha1 hb1] at key
    linarith [key]
  rw [div_le_div_iff₀ db da]
  nlinarith [key2]

theorem ca_delta_nonneg (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    0 ≤ Real.log (Work.RHPlan.caNumber ε) - Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) := by
  set ξ := Work.RHPlan.caXi ε with hξdef
  have hξreal : (1530 : ℝ) ≤ (ξ : ℝ) := by rw [hξdef]; exact hξ
  have hξ2 : 2 ≤ ξ := by exact_mod_cast (by linarith : (2 : ℝ) ≤ (ξ : ℝ))
  -- the support is nonempty, since `ξ ≥ 1530` and the sup of the empty set is `0`
  have hs : (Work.RHPlan.caSupport ε).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : ξ = 0 := by rw [hξdef, Work.RHPlan.caXi, h]; exact Finset.sup_empty
    rw [h0] at hξreal; norm_num at hξreal
  -- `ξ` is the maximal element of its support
  have hmem : ξ ∈ Work.RHPlan.caSupport ε := by
    have h1 : (Work.RHPlan.caSupport ε).sup id = (Work.RHPlan.caSupport ε).max' hs := by
      rw [← Finset.sup'_eq_sup hs id]
      rw [Finset.max'_eq_sup' (Work.RHPlan.caSupport ε) hs]
    rw [hξdef, Work.RHPlan.caXi, h1]
    exact Finset.max'_mem _ hs
  have hξprime : Nat.Prime ξ := by
    have h1 := (Finset.mem_filter.mp hmem).1
    exact (Finset.mem_filter.mp h1).2
  have hξexp : 1 ≤ ⌊Work.RHPlan.caMu ξ ε⌋₊ := (Finset.mem_filter.mp hmem).2
  have hξltX : ξ < Nat.ceil (Real.exp (2 / ε)) + 2 := by
    have h1 := (Finset.mem_filter.mp hmem).1
    exact Finset.mem_range.mp (Finset.mem_filter.mp h1).1
  -- the analytic core: for every prime `p ≤ ξ`, `e_p = ⌊log ξ/log p⌋ ≤ μ(p,ε)`
  have hcore : ∀ p : ℕ, Nat.Prime p → p ≤ ξ → (Nat.log p ξ : ℝ) ≤ Work.RHPlan.caMu p ε := by
    intro p hp hpξ
    have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hpξr : (p : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hpξ
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpr
    have hlogξ : 0 < Real.log (ξ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ξ))
    -- `1 ≤ μ(ξ,ε)`, because `ξ` lies in the support
    have hμ1 : (1 : ℝ) ≤ Work.RHPlan.caMu ξ ε := by
      have h0 : 0 ≤ Work.RHPlan.caMu ξ ε :=
        le_of_lt (Commons.NumberTheory.Robin.caMu_pos (p := ξ) (ε := ε) hξ2 hε)
      exact le_trans (by exact_mod_cast hξexp) (Nat.floor_le h0)
    -- hence `log ξ ≤ log R(ξ)`
    have hA : Real.log (ξ : ℝ) ≤
        Real.log (((ξ : ℝ) ^ (1 + ε) - 1) / ((ξ : ℝ) ^ (1 + ε) - (ξ : ℝ))) := by
      have h1 := hμ1
      rw [Work.RHPlan.caMu] at h1
      have h2 := (le_div_iff₀ hlogξ).mp h1
      simpa using h2
    -- antitone ratio: `R(ξ) ≤ R(p)`
    have hle_ratio : ((ξ : ℝ) ^ (1 + ε) - 1) / ((ξ : ℝ) ^ (1 + ε) - (ξ : ℝ)) ≤
        ((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ)) :=
      ratio_antitone ε hε hpr hpξr
    have hpos_ratio : 0 < ((ξ : ℝ) ^ (1 + ε) - 1) / ((ξ : ℝ) ^ (1 + ε) - (ξ : ℝ)) := by
      apply div_pos
      · have hlt : (1 : ℝ) < (ξ : ℝ) ^ (1 + ε) := by
          rw [Real.rpow_add (by linarith : (0 : ℝ) < (ξ : ℝ)), Real.rpow_one]
          have h2 : 1 < (ξ : ℝ) ^ ε :=
            Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < ξ)) hε
          nlinarith [hξreal]
        linarith
      · have hlt : (ξ : ℝ) < (ξ : ℝ) ^ (1 + ε) := by
          rw [Real.rpow_add (by linarith : (0 : ℝ) < (ξ : ℝ)), Real.rpow_one]
          have h2 : 1 < (ξ : ℝ) ^ ε :=
            Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < ξ)) hε
          nlinarith [hξreal]
        linarith
    have hB : Real.log (((ξ : ℝ) ^ (1 + ε) - 1) / ((ξ : ℝ) ^ (1 + ε) - (ξ : ℝ))) ≤
        Real.log (((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ))) :=
      Real.log_le_log hpos_ratio hle_ratio
    -- `e_p · log p = log(p^{e_p}) ≤ log ξ`
    have hpk : p ^ Nat.log p ξ ≤ ξ := Nat.pow_log_le_self p (by omega)
    have hpk' : ((p : ℝ)) ^ (Nat.log p ξ) ≤ (ξ : ℝ) := by exact_mod_cast hpk
    have hlog : (Nat.log p ξ : ℝ) * Real.log (p : ℝ) ≤ Real.log (ξ : ℝ) := by
      have h3 : Real.log ((p : ℝ) ^ (Nat.log p ξ)) ≤ Real.log (ξ : ℝ) :=
        Real.log_le_log (by positivity) hpk'
      rwa [Real.log_pow] at h3
    have hcomb : (Nat.log p ξ : ℝ) * Real.log (p : ℝ) ≤
        Real.log (((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ))) :=
      le_trans hlog (le_trans hA hB)
    rw [Work.RHPlan.caMu]
    exact (le_div_iff₀ hlogp).mpr hcomb
  -- `log N_ε` as a sum over the support
  have hlogN : Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) =
      ∑ p ∈ (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime,
        (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) * Real.log (p : ℝ) := by
    rw [Work.RHPlan.caNumber]
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p _
      rw [Nat.cast_pow, Real.log_pow]
      simp only [Work.RHPlan.caMu]
    · intro p hp
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact_mod_cast (pow_ne_zero _ hpp.pos.ne')
  -- `ψ(ξ)` as the corresponding sum over `primesLE ξ`
  have hpsi : Chebyshev.psi (ξ : ℝ) =
      ∑ p ∈ Nat.primesLE ξ, (Nat.log p ξ : ℝ) * Real.log (p : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Nat.floor_natCast]
    exact Chebyshev.psi_eq_sum_mul_log_prime ξ
  have hsub : Nat.primesLE ξ ⊆
      (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hpξ, hpp⟩ := hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hpξ hξltX), hpp⟩
  have step1 : ∑ p ∈ Nat.primesLE ξ, (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime,
          (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hpp.one_le))
  have step2 : ∑ p ∈ Nat.primesLE ξ, ((Nat.log p ξ : ℝ) * Real.log (p : ℝ))
      ≤ ∑ p ∈ Nat.primesLE ξ, (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hpξ, hpp⟩ := hp
    have h1 : (Nat.log p ξ : ℝ) ≤ (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) := by
      have := Nat.le_floor (hcore p hpp hpξ)
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right h1 (Real.log_nonneg (by exact_mod_cast hpp.one_le))
  have hfin : Chebyshev.psi (ξ : ℝ) ≤ Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
    rw [hpsi, hlogN]
    exact le_trans step2 step1
  linarith [hfin]

end Work.RHContract.A
