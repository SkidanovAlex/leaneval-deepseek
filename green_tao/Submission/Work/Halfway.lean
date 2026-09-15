import Mathlib

set_option linter.unusedSectionVars false

/-!
# Green–Tao Lemma 3.1 (the "halfway" lemma)

If `ν` is a pseudorandom `1`-bounded-below-ish weight, then so is `ν_{1/2} := (ν+1)/2`:
the linear forms (cube) condition survives with the same error, and the correlation condition
survives with the weight `τ' = K(1+τ)` and explicit moment bounds.

This is the device Green–Tao use (Lemma 3.1) to be able to assume `|F_j| ≤ ν` rather than
`|F_j| ≤ ν + 1` in Lemma 6.6 / Proposition 6.5: replacing `ν` by `(ν+1)/2` and halving the
`F_j` (the dual function `𝒟` being homogeneous of degree `2^d - 1`) turns the weaker bound into
the stronger one.
-/

open Finset
open scoped BigOperators

namespace GTTrans

/-- Convenient abbreviation for the cube shifts `ω · h`. -/
private lemma sum_ite_one_mul_eq {p : ℕ} [Fact p.Prime] {d : ℕ} (ω : Fin d → Bool)
    (h : Fin d → ZMod p) :
    (∑ j, (if ω j then (1 : ZMod p) else 0) * h j) = ∑ j, (if ω j then h j else 0) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp [hj]

/-- **Green–Tao Lemma 3.1, linear forms part.**  The `(d, d·2^d)`-cube linear forms condition
passes from `ν` to `(ν+1)/2` with the same error. -/
theorem cube_lfc_half {p : ℕ} [Fact p.Prime] {d : ℕ} (ν : ZMod p → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε) :
    ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A,
            ((ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) + 1) / 2) - 1| ≤ ε := by
  classical
  intro A hA hAne b
  set N : ℝ := (Fintype.card (Fin d → ZMod p) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  set u : (Fin d → Bool) → (Fin d → ZMod p) → ZMod p :=
    fun ω h => b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j with hu
  -- expand each factor
  have hfac : ∀ h : Fin d → ZMod p,
      (∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
        = ((2 : ℝ) ^ A.card)⁻¹ * ∏ ω ∈ A, (ν (u ω h) + 1) := by
    intro h
    rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [div_eq_inv_mul]
  have hexp : ∀ h : Fin d → ZMod p,
      (∏ ω ∈ A, (ν (u ω h) + 1)) = ∑ A' ∈ A.powerset, ∏ ω ∈ A', ν (u ω h) := by
    intro h
    have hswap : (∏ ω ∈ A, (ν (u ω h) + 1)) = ∏ ω ∈ A, (1 + ν (u ω h)) := by
      apply Finset.prod_congr rfl
      intro ω _
      ring
    rw [hswap, Finset.prod_one_add]
  -- the inner averages
  set g : Finset (Fin d → Bool) → ℝ :=
    fun A' => N⁻¹ * ∑ h : Fin d → ZMod p, ∏ ω ∈ A', ν (u ω h) with hg
  have hg_empty : g ∅ = 1 := by
    show N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ (∅ : Finset (Fin d → Bool)), ν (u ω h)) = 1
    simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
    rw [inv_mul_cancel₀ hNne]
  have hg_bound : ∀ A' ∈ A.powerset, |g A' - 1| ≤ ε := by
    intro A' hA'
    rw [Finset.mem_powerset] at hA'
    by_cases hAne' : A'.Nonempty
    · exact hLFC A' (hA'.trans hA) hAne' b
    · rw [Finset.not_nonempty_iff_eq_empty] at hAne'
      rw [hAne', hg_empty]
      simpa using hε
  -- rewrite the whole average as a `powerset` sum
  have hmain : N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
      = ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, g A' := by
    have e1 : ∀ h : Fin d → ZMod p,
        (∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
          = ((2 : ℝ) ^ A.card)⁻¹ * (∑ A' ∈ A.powerset, ∏ ω ∈ A', ν (u ω h)) := by
      intro h; rw [hfac h, hexp h]
    have e2 : ∑ A' ∈ A.powerset, g A'
        = N⁻¹ * ∑ A' ∈ A.powerset, ∑ h : Fin d → ZMod p, ∏ ω ∈ A', ν (u ω h) := by
      simp only [hg, Finset.mul_sum]
    rw [e2]
    simp only [e1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring
  have hcard2 : (0 : ℝ) < (2 : ℝ) ^ A.card := by positivity
  have hsum1 : ∑ A' ∈ A.powerset, (1 : ℝ) = (2 : ℝ) ^ A.card := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
    push_cast
    ring
  have hstep : N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ A, ((ν (u ω h)) + 1) / 2) - 1
      = ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, (g A' - 1) := by
    have hc : ((2 : ℝ) ^ A.card) ≠ 0 := ne_of_gt hcard2
    rw [hmain, Finset.sum_sub_distrib, hsum1, mul_sub, inv_mul_cancel₀ hc]
  rw [hstep, abs_mul, abs_of_pos (inv_pos.mpr hcard2)]
  calc ((2 : ℝ) ^ A.card)⁻¹ * |∑ A' ∈ A.powerset, (g A' - 1)|
      ≤ ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, |g A' - 1| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hg_bound) (by positivity)
    _ = ((2 : ℝ) ^ A.card)⁻¹ * ((2 : ℝ) ^ A.card * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
        push_cast
        ring
    _ = ε := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard2), one_mul]

/-- `(1 + x)^q ≤ 2^q (1 + x^q)` for `x ≥ 0`. -/
private lemma one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (q : ℕ) :
    (1 + x) ^ q ≤ 2 ^ q * (1 + x ^ q) := by
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 + x) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
    have h3 : (0 : ℝ) ≤ 2 ^ q := pow_nonneg (by norm_num) q
    have h4 : (0 : ℝ) ≤ x ^ q := pow_nonneg hx q
    nlinarith [h1, h3, h4]
  · have h1 : (1 + x) ^ q ≤ (2 * x) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
    have h2 : (2 * x) ^ q = 2 ^ q * x ^ q := by rw [mul_pow]
    have h3 : (0 : ℝ) ≤ 2 ^ q := pow_nonneg (by norm_num) q
    have h4 : (0 : ℝ) ≤ x ^ q := pow_nonneg hx q
    rw [h2] at h1
    nlinarith [h1, h3, h4]

/-- **Green–Tao Lemma 3.1, correlation part.**  The cube correlation condition passes from `ν`
to `(ν+1)/2` with the weight `τ' = (3/2)(1+ε)·(1+τ)`.  The hypothesis is stated for arbitrary
subsets `A` of the cube with `2 ≤ |A|` (this is the form in which the condition is used by
`weier_bound`); the singletons are covered by the mean bound `𝔼 ν ≤ 1 + ε`. -/
theorem cube_corr_half {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmeas : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ ε)
    {τ : ZMod p → ℝ} (hτ : ∀ x, 0 ≤ τ x) {Cm : ℕ → ℝ}
    (hmom : ∀ q : ℕ, 1 ≤ q → ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ Cm q)
    (hcorr : ∀ (A : Finset (Fin d → Bool)), 2 ≤ A.card → ∀ h : Fin d → ZMod p,
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
          ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) :
    ∃ Cm' : ℕ → ℝ, (∀ q, 0 ≤ Cm' q) ∧ ∃ τ' : ZMod p → ℝ, (∀ x, 0 ≤ τ' x) ∧
      (∀ q : ℕ, ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ' x) ^ q ≤ Cm' q) ∧
      ∀ h : Fin d → ZMod p,
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ∏ ω : Fin d → Bool,
            ((ν (y + ∑ i, (if ω i then h i else 0)) + 1) / 2)
          ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              τ' ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))) := by
  classical
  set mm : ℕ := 2 ^ d with hmm
  have hmm2 : 2 ≤ mm := by
    rw [hmm]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  set N : ℝ := (Fintype.card (ZMod p) : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : ZMod p)⟩)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  set K : ℝ := 3 * (1 + ε) / 2 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hcard_fun : (Fintype.card (Fin d → Bool) : ℕ) = mm := by
    rw [Fintype.card_fun, hmm]; simp
  refine ⟨fun q => K ^ q * 2 ^ q * (2 + |Cm q|), ?_, fun x => K * (1 + τ x), ?_, ?_, ?_⟩
  · intro q
    have h1 : (0 : ℝ) ≤ K ^ q := pow_nonneg hK0.le q
    have h2 : (0 : ℝ) ≤ 2 ^ q := pow_nonneg (by norm_num) q
    have h3 : (0 : ℝ) ≤ 2 + |Cm q| := by positivity
    positivity
  · intro x
    exact mul_nonneg hK0.le (by linarith [hτ x])
  · -- moment bound
    intro q
    have htaupow : N⁻¹ * (∑ x : ZMod p, τ x ^ q) ≤ 1 + |Cm q| := by
      rcases eq_or_ne q 0 with hq | hq
      · subst hq
        rw [show (∑ x : ZMod p, τ x ^ 0) = N from by
          simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          rw [hNdef]]
        rw [inv_mul_cancel₀ hNne]
        linarith [abs_nonneg (Cm 0)]
      · have h1 : N⁻¹ * (∑ x : ZMod p, τ x ^ q) ≤ Cm q := by
          rw [hNdef]; exact hmom q (Nat.pos_of_ne_zero hq)
        linarith [h1, le_abs_self (Cm q), abs_nonneg (Cm q)]
    have hpt : ∀ x : ZMod p, (K * (1 + τ x)) ^ q ≤ K ^ q * (2 ^ q * (1 + τ x ^ q)) := by
      intro x
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (one_add_pow_le (hτ x) q) (pow_nonneg hK0.le q)
    have hsum : (∑ x : ZMod p, (K * (1 + τ x)) ^ q)
        ≤ ∑ x : ZMod p, (K ^ q * (2 ^ q * (1 + τ x ^ q))) :=
      Finset.sum_le_sum fun x _ => hpt x
    have hexpand : (∑ x : ZMod p, (K ^ q * (2 ^ q * (1 + τ x ^ q))))
        = K ^ q * (2 ^ q * (N + ∑ x : ZMod p, τ x ^ q)) := by
      rw [show (∑ x : ZMod p, (K ^ q * (2 ^ q * (1 + τ x ^ q))))
          = K ^ q * ∑ x : ZMod p, (2 ^ q * (1 + τ x ^ q)) from by
        rw [Finset.mul_sum]]
      congr 1
      rw [show (∑ x : ZMod p, (2 ^ q * (1 + τ x ^ q)))
          = 2 ^ q * ∑ x : ZMod p, (1 + τ x ^ q) from by rw [Finset.mul_sum]]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        hNdef]
    have hsum' : (∑ x : ZMod p, (K * (1 + τ x)) ^ q)
        ≤ K ^ q * (2 ^ q * (N + ∑ x : ZMod p, τ x ^ q)) := by
      rw [← hexpand]; exact hsum
    calc N⁻¹ * (∑ x : ZMod p, (K * (1 + τ x)) ^ q)
        ≤ N⁻¹ * (K ^ q * (2 ^ q * (N + ∑ x : ZMod p, τ x ^ q))) :=
          mul_le_mul_of_nonneg_left hsum' (inv_nonneg.mpr hNpos.le)
      _ = K ^ q * 2 ^ q * (1 + N⁻¹ * (∑ x : ZMod p, τ x ^ q)) := by
          field_simp
      _ ≤ K ^ q * 2 ^ q * (2 + |Cm q|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [htaupow]
  · -- cube correlation
    intro h
    set u : (Fin d → Bool) → ZMod p := fun ω => ∑ i, (if ω i then h i else 0) with hu
    set S : ℝ := ∑ ω : Fin d → Bool,
      ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) with hS
    have hSnn : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun ω _ => Finset.sum_nonneg fun ω' _ => hτ _
    -- translation invariance of the singleton terms
    have hmean : N⁻¹ * (∑ y : ZMod p, ν y) ≤ 1 + ε := by
      have h1 := abs_le.mp hmeas
      rw [hNdef] at h1 ⊢
      linarith [h1.2]
    -- per-subset bound
    have hsub : ∀ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
        N⁻¹ * (∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω)) ≤ (1 + ε) + S := by
      intro A hA
      by_cases hAe : A = ∅
      · subst hAe
        rw [show (∑ y : ZMod p, ∏ ω ∈ (∅ : Finset (Fin d → Bool)), ν (y + u ω)) = N from by
          simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_one]
          rw [hNdef]]
        rw [inv_mul_cancel₀ hNne]
        linarith [hε, hSnn]
      · have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAe
        rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hAne)) with hc1 | hc2
        · -- singleton
          obtain ⟨ω0, rfl⟩ := Finset.card_eq_one.mp hc1.symm
          have htrans : (∑ y : ZMod p, ν (y + u ω0)) = ∑ y : ZMod p, ν y :=
            Equiv.sum_comp (Equiv.addRight (u ω0)) (fun y : ZMod p => ν y)
          have hprod : ∀ y : ZMod p,
              (∏ ω ∈ ({ω0} : Finset (Fin d → Bool)), ν (y + u ω)) = ν (y + u ω0) :=
            fun y => Finset.prod_singleton (fun ω => ν (y + u ω)) ω0
          simp only [hprod, htrans]
          linarith [hmean, hSnn]
        · -- at least two elements
          have hcorrA := hcorr A (by omega) h
          calc N⁻¹ * (∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω))
              ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) := hcorrA
            _ ≤ S := by
                rw [hS]
                refine Finset.sum_le_sum_of_subset_of_nonneg (fun ω _ => Finset.mem_univ ω)
                  (fun ω _ _ => Finset.sum_nonneg fun ω' _ => hτ _) |>.trans ?_
                refine Finset.sum_le_sum fun ω _ => ?_
                refine Finset.sum_le_sum_of_subset_of_nonneg (fun ω' hω' => ?_)
                  (fun ω' _ _ => hτ _)
                rw [Finset.mem_filter] at hω' ⊢
                exact ⟨Finset.mem_univ _, hω'.2⟩
            _ ≤ (1 + ε) + S := by linarith
    -- expansion
    have hexp : ∀ y : ZMod p, (∏ ω : Fin d → Bool, (ν (y + u ω) + 1))
        = ∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset, ∏ ω ∈ A, ν (y + u ω) := by
      intro y
      have hswap : (∏ ω : Fin d → Bool, (ν (y + u ω) + 1))
          = ∏ ω : Fin d → Bool, (1 + ν (y + u ω)) :=
        Finset.prod_congr rfl fun ω _ => by ring
      rw [hswap, Finset.prod_one_add]
    have hfac : ∀ y : ZMod p, (∏ ω : Fin d → Bool, ((ν (y + u ω)) + 1) / 2)
        = ((2 : ℝ) ^ mm)⁻¹ * (∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
            ∏ ω ∈ A, ν (y + u ω)) := by
      intro y
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hcard_fun, hexp y,
        div_eq_inv_mul]
    have hkey : N⁻¹ * (∑ y : ZMod p, ∏ ω : Fin d → Bool, ((ν (y + u ω)) + 1) / 2)
        = ((2 : ℝ) ^ mm)⁻¹ * ∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
            N⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω) := by
      have e1 : N⁻¹ * (∑ y : ZMod p, ∏ ω : Fin d → Bool, ((ν (y + u ω)) + 1) / 2)
          = N⁻¹ * ((2 : ℝ) ^ mm)⁻¹ * (∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
              ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω)) := by
        rw [show (∑ y : ZMod p, ∏ ω : Fin d → Bool, ((ν (y + u ω)) + 1) / 2)
            = ∑ y : ZMod p, ((2 : ℝ) ^ mm)⁻¹ * (∑ A ∈
                (Finset.univ : Finset (Fin d → Bool)).powerset, ∏ ω ∈ A, ν (y + u ω)) from
          Finset.sum_congr rfl fun y _ => hfac y]
        rw [← Finset.mul_sum, Finset.sum_comm]
        ring
      have e2 : ((2 : ℝ) ^ mm)⁻¹ * (∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
            N⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω))
          = ((2 : ℝ) ^ mm)⁻¹ * (N⁻¹ * (∑ A ∈
              (Finset.univ : Finset (Fin d → Bool)).powerset, ∑ y : ZMod p,
                ∏ ω ∈ A, ν (y + u ω))) := by
        simp only [Finset.mul_sum]
      rw [e1, e2]
      ring
    rw [hkey]
    have hpc : ((Finset.univ : Finset (Fin d → Bool)).powerset).card = 2 ^ mm := by
      rw [Finset.card_powerset, Finset.card_univ, hcard_fun]
    have hbound : (∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
          N⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω))
        ≤ 2 ^ mm * ((1 + ε) + S) := by
      calc _ ≤ ∑ _A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset, ((1 + ε) + S) :=
            Finset.sum_le_sum hsub
        _ = 2 ^ mm * ((1 + ε) + S) := by
            rw [Finset.sum_const, nsmul_eq_mul, hpc]
            push_cast
            ring
    have h2mm : (0 : ℝ) < (2 : ℝ) ^ mm := by positivity
    have hpair : (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          (K * (1 + τ (u ω' - u ω))))
        = K * ((Fintype.card (Fin d → Bool) : ℝ) * ((Fintype.card (Fin d → Bool) : ℝ) - 1))
          + K * S := by
      rw [hS]
      have hinner : ∀ ω : Fin d → Bool,
          (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), (K * (1 + τ (u ω' - u ω))))
            = K * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
              + K * (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
                  τ (u ω' - u ω)) := by
        intro ω
        have hc : ((Finset.univ.filter (fun ω' => ω ≠ ω')).card : ℝ)
            = (Fintype.card (Fin d → Bool) : ℝ) - 1 := by
          rw [show (Finset.univ.filter (fun ω' => ω ≠ ω'))
              = (Finset.univ : Finset (Fin d → Bool)).erase ω from by
                ext x; simp [Finset.mem_erase, eq_comm]]
          rw [Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ,
            Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨ω⟩)]
          push_cast
          ring
        rw [show (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              (K * (1 + τ (u ω' - u ω))))
            = ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
                (K + K * τ (u ω' - u ω)) from
          Finset.sum_congr rfl fun ω' _ => by ring]
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hc]
        have hcu : ((Finset.univ : Finset (Fin d → Bool)).card : ℝ)
            = (Fintype.card (Fin d → Bool) : ℝ) := by rw [Finset.card_univ]
        nlinarith [hcu]
      rw [Finset.sum_congr rfl (fun ω _ => hinner ω), Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      have hcu : ((Finset.univ : Finset (Fin d → Bool)).card : ℝ)
          = (Fintype.card (Fin d → Bool) : ℝ) := by rw [Finset.card_univ]
      rw [hcu]
      ring
    have hcard2R : (2 : ℝ) ≤ (Fintype.card (Fin d → Bool) : ℝ) := by
      rw [hcard_fun]; exact_mod_cast hmm2
    have hprod2 : (2 : ℝ) ≤ (Fintype.card (Fin d → Bool) : ℝ)
        * ((Fintype.card (Fin d → Bool) : ℝ) - 1) := by
      nlinarith [hcard2R]
    have hK2 : K * 2 ≤ K * ((Fintype.card (Fin d → Bool) : ℝ)
        * ((Fintype.card (Fin d → Bool) : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hprod2 hK0.le
    have hKex : K * 2 = 3 * (1 + ε) := by rw [hKdef]; ring
    have h1 : (1 + ε) + S ≤ K * 2 + K * S := by
      have : S ≤ K * S := by nlinarith [hK1, hSnn]
      rw [hKex]; linarith
    calc ((2 : ℝ) ^ mm)⁻¹ * (∑ A ∈ (Finset.univ : Finset (Fin d → Bool)).powerset,
          N⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω))
        ≤ ((2 : ℝ) ^ mm)⁻¹ * (2 ^ mm * ((1 + ε) + S)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (1 + ε) + S := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2mm), one_mul]
      _ ≤ K * 2 + K * S := h1
      _ ≤ K * ((Fintype.card (Fin d → Bool) : ℝ)
            * ((Fintype.card (Fin d → Bool) : ℝ) - 1)) + K * S := by linarith [hK2]
      _ = ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              (K * (1 + τ (u ω' - u ω))) := hpair.symm

end GTTrans
