import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Choose.Sum

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Auxiliary combinatorial bound: if `ν ≥ 0` has mean `≤ 1 + ε` and satisfies the cube
correlation condition for subsets of size `≥ 2` with weight `τ`, then the "halved" weight
`(ν+1)/2` satisfies the *full cube* correlation condition with weight `(1+ε) + τ` (in the
weak sense that the average of the full cube product is at most `(1+ε)` plus the off-diagonal
`τ`-sum over the cube). -/
private lemma cube_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {p : ℕ} [Fact p.Prime] (ν : ZMod p → ℝ) (τ : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x) {ε : ℝ} (hε : 0 ≤ ε) (F : Ω → ZMod p)
    (hmean : ∑ x : ZMod p, ν x ≤ (Fintype.card (ZMod p) : ℝ) * (1 + ε))
    (hcorr : ∀ A : Finset Ω, 2 ≤ A.card →
        (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + F ω)
          ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) :
    (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, ∏ ω : Ω, ((ν (y + F ω) + 1) / 2)
      ≤ (1 + ε) + ∑ ω : Ω, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) := by
  classical
  set N : ℝ := (Fintype.card (ZMod p) : ℝ) with hN
  set U : ℝ := ∑ ω : Ω, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) with hU
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hNpos : 0 < N := by rw [hN, ZMod.card p]; exact_mod_cast hp
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hNnn : (0 : ℝ) ≤ N := le_of_lt hNpos
  have hUnn : 0 ≤ U := by
    rw [hU]
    exact Finset.sum_nonneg (fun ω _ => Finset.sum_nonneg (fun ω' _ => hτ _))
  -- Step 1: pointwise expansion of the halved product as a sum over subsets
  have hpt : ∀ y : ZMod p, (∏ ω : Ω, ((ν (y + F ω) + 1) / 2))
      = (1/2 : ℝ) ^ (Fintype.card Ω) * ∑ S ∈ Finset.univ.powerset, ∏ ω ∈ S, ν (y + F ω) := by
    intro y
    rw [show (∏ ω : Ω, ((ν (y + F ω) + 1) / 2))
          = ∏ ω : Ω, ((ν (y + F ω) + 1) * (1/2 : ℝ)) from by
        apply Finset.prod_congr rfl; intro ω _; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_add_one Finset.univ]
    ring
  -- Step 2: sum over `y` and interchange the sums
  have hsum : ∑ y : ZMod p, (∏ ω : Ω, ((ν (y + F ω) + 1) / 2))
      = (1/2 : ℝ) ^ (Fintype.card Ω)
          * ∑ S ∈ Finset.univ.powerset, ∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω) := by
    have h1 : ∑ y : ZMod p, (∏ ω : Ω, ((ν (y + F ω) + 1) / 2))
        = ∑ y : ZMod p, (1/2 : ℝ) ^ (Fintype.card Ω)
            * (∑ S ∈ Finset.univ.powerset, ∏ ω ∈ S, ν (y + F ω)) :=
      Finset.sum_congr rfl (fun y _ => hpt y)
    rw [h1, ← Finset.mul_sum, Finset.sum_comm]
  -- Step 3: termwise bound over the powerset
  have hSbound : ∀ S ∈ Finset.univ.powerset,
      (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω)) ≤ N * (1 + ε) + N * U := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    by_cases h0 : S.card = 0
    · rw [Finset.card_eq_zero] at h0
      subst h0
      simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      nlinarith [hN, hε, hUnn, hNpos]
    · by_cases h1 : S.card = 1
      · rw [Finset.card_eq_one] at h1
        obtain ⟨a, rfl⟩ := h1
        simp only [Finset.prod_singleton]
        calc ∑ y : ZMod p, ν (y + F a) = ∑ y : ZMod p, ν y :=
              Equiv.sum_comp (Equiv.addRight (F a)) ν
          _ ≤ N * (1 + ε) := hmean
          _ ≤ N * (1 + ε) + N * U := le_add_of_nonneg_right (mul_nonneg hNnn hUnn)
      · have h2 : 2 ≤ S.card := by omega
        have hc := hcorr S h2
        have hNX : N * (N⁻¹ * (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω)))
            = ∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω) := by
          rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
        have hQU : (∑ ω ∈ S, ∑ ω' ∈ S.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) ≤ U := by
          rw [hU]
          calc (∑ ω ∈ S, ∑ ω' ∈ S.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω))
              ≤ ∑ ω ∈ S, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) := by
                apply Finset.sum_le_sum; intro ω _
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro ω' hω'
                  rw [Finset.mem_filter] at hω' ⊢
                  exact ⟨Finset.mem_univ _, hω'.2⟩
                · intro ω' _ _; exact hτ _
            _ ≤ ∑ ω : Ω, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hS
                intro ω _ _
                exact Finset.sum_nonneg (fun ω' _ => hτ _)
        calc (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω))
            = N * (N⁻¹ * (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω))) := hNX.symm
          _ ≤ N * (∑ ω ∈ S, ∑ ω' ∈ S.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) :=
              mul_le_mul_of_nonneg_left hc hNnn
          _ ≤ N * U := mul_le_mul_of_nonneg_left hQU hNnn
          _ ≤ N * (1 + ε) + N * U := le_add_of_nonneg_left (mul_nonneg hNnn (by linarith))
  have hbnd : ∑ S ∈ Finset.univ.powerset, (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω))
      ≤ ∑ S ∈ Finset.univ.powerset, (N * (1 + ε) + N * U) := Finset.sum_le_sum hSbound
  have hconst : ∑ S ∈ (Finset.univ : Finset Ω).powerset, (N * (1 + ε) + N * U)
      = (2 : ℝ) ^ (Fintype.card Ω) * (N * (1 + ε) + N * U) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Finset.card_univ, Nat.cast_pow]
    norm_num
  have hle1 : ∑ S ∈ Finset.univ.powerset, (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω))
      ≤ (2 : ℝ) ^ (Fintype.card Ω) * (N * (1 + ε) + N * U) := hbnd.trans hconst.le
  have hf1 : (1/2 : ℝ) ^ (Fintype.card Ω)
        * ∑ S ∈ Finset.univ.powerset, (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω))
      ≤ (1/2 : ℝ) ^ (Fintype.card Ω)
        * ((2 : ℝ) ^ (Fintype.card Ω) * (N * (1 + ε) + N * U)) :=
    mul_le_mul_of_nonneg_left hle1 (pow_nonneg (by norm_num) _)
  have hf2 : N⁻¹ * ((1/2 : ℝ) ^ (Fintype.card Ω)
        * ∑ S ∈ Finset.univ.powerset, (∑ y : ZMod p, ∏ ω ∈ S, ν (y + F ω)))
      ≤ N⁻¹ * ((1/2 : ℝ) ^ (Fintype.card Ω)
        * ((2 : ℝ) ^ (Fintype.card Ω) * (N * (1 + ε) + N * U))) :=
    mul_le_mul_of_nonneg_left hf1 (inv_nonneg.mpr hNnn)
  have hEq : N⁻¹ * ((1/2 : ℝ) ^ (Fintype.card Ω)
        * ((2 : ℝ) ^ (Fintype.card Ω) * (N * (1 + ε) + N * U))) = (1 + ε) + U := by
    have h2 : (1/2 : ℝ) ^ (Fintype.card Ω) * (2 : ℝ) ^ (Fintype.card Ω) = 1 := by
      rw [← mul_pow]; norm_num
    have hX : N * (1 + ε) + N * U = N * ((1 + ε) + U) := by ring
    rw [hX, ← mul_assoc ((1/2 : ℝ) ^ (Fintype.card Ω)) ((2 : ℝ) ^ (Fintype.card Ω)) (N * ((1 + ε) + U)),
        h2, one_mul, ← mul_assoc N⁻¹ N ((1 + ε) + U), inv_mul_cancel₀ hNne, one_mul]
  rw [hsum]
  exact hf2.trans (le_of_eq hEq)

/-- **Green–Tao Lemma 3.1, correlation part (cube form).**  The cube correlation condition
passes from `ν` to `ν' = (ν+1)/2` with the weight `τ' = (3/2)(1+ε)·(1+τ)`.  The hypothesis is
stated for arbitrary subsets `A` of the cube with `2 ≤ |A|` (this is the form used by
`weier_bound`); the singleton subsets are covered by the mean bound `𝔼 ν ≤ 1 + ε`.  The
conclusion has the shape required by `weier_bound`/`bohr_sigma_atom`, together with the moment
bounds for the new weight. -/
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
  set N : ℝ := (Fintype.card (ZMod p) : ℝ) with hN
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hNpos : 0 < N := by rw [hN, ZMod.card p]; exact_mod_cast hp
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hNnn : (0 : ℝ) ≤ N := le_of_lt hNpos
  -- nonnegativity of the moments of `τ`
  have hCm_nn : ∀ j, 1 ≤ j → 0 ≤ Cm j := by
    intro j hj
    have h := hmom j hj
    have h2 : (0 : ℝ) ≤ N⁻¹ * ∑ x, (τ x) ^ j :=
      mul_nonneg (inv_nonneg.mpr hNnn) (Finset.sum_nonneg (fun x _ => pow_nonneg (hτ x) j))
    linarith
  -- mean bound on `ν`
  have hmean : ∑ x : ZMod p, ν x ≤ N * (1 + ε) := by
    have h1 : N⁻¹ * ∑ x : ZMod p, ν x ≤ 1 + ε := by
      have := (abs_le.mp hmeas).2
      linarith
    have h2 : ∑ x : ZMod p, ν x = N * (N⁻¹ * ∑ x : ZMod p, ν x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hNnn
  refine ⟨fun q => ((3/2 : ℝ) * (1 + ε)) ^ q
        * (∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * (if j = 0 then 1 else Cm j)),
      ?_, fun x => ((3/2 : ℝ) * (1 + ε)) * (1 + τ x), ?_, ?_, ?_⟩
  · -- nonnegativity of `Cm'`
    intro q
    refine mul_nonneg (pow_nonneg (by linarith) q) (Finset.sum_nonneg ?_)
    intro j _
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    by_cases h : j = 0
    · simp [h]
    · simp only [h, if_false]
      exact hCm_nn j (Nat.one_le_iff_ne_zero.mpr h)
  · -- nonnegativity of `τ'`
    intro x
    have h1 : (0 : ℝ) ≤ (3/2) * (1 + ε) := by
      apply mul_nonneg (by norm_num); linarith
    have h2 : (0 : ℝ) ≤ 1 + τ x := by linarith [hτ x]
    exact mul_nonneg h1 h2
  · -- moment bounds for `τ'`
    intro q
    have hc_nn : (0 : ℝ) ≤ (3/2 : ℝ) * (1 + ε) := mul_nonneg (by norm_num) (by linarith)
    have hexp : ∀ x : ZMod p, (1 + τ x) ^ q
        = ∑ j ∈ Finset.range (q + 1), (τ x) ^ j * ((q.choose j : ℕ) : ℝ) := by
      intro x
      have h := add_pow (τ x) (1 : ℝ) q
      simp only [one_pow, mul_one] at h
      rw [add_comm] at h
      exact h
    have hsum2 : ∑ x : ZMod p, (1 + τ x) ^ q
        = ∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * ∑ x : ZMod p, (τ x) ^ j := by
      calc ∑ x : ZMod p, (1 + τ x) ^ q
          = ∑ x : ZMod p, ∑ j ∈ Finset.range (q + 1), (τ x) ^ j * ((q.choose j : ℕ) : ℝ) :=
              Finset.sum_congr rfl (fun x _ => hexp x)
        _ = ∑ j ∈ Finset.range (q + 1), ∑ x : ZMod p, (τ x) ^ j * ((q.choose j : ℕ) : ℝ) :=
              Finset.sum_comm
        _ = ∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * ∑ x : ZMod p, (τ x) ^ j := by
              apply Finset.sum_congr rfl; intro j _
              rw [← Finset.sum_mul, mul_comm]
    have hinner : N⁻¹ * ∑ x : ZMod p, (1 + τ x) ^ q
        ≤ ∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * (if j = 0 then 1 else Cm j) := by
      calc N⁻¹ * ∑ x : ZMod p, (1 + τ x) ^ q
          = N⁻¹ * ∑ j ∈ Finset.range (q + 1),
              ((q.choose j : ℕ) : ℝ) * ∑ x : ZMod p, (τ x) ^ j := by rw [hsum2]
        _ = ∑ j ∈ Finset.range (q + 1),
              ((q.choose j : ℕ) : ℝ) * (N⁻¹ * ∑ x : ZMod p, (τ x) ^ j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ ∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * (if j = 0 then 1 else Cm j) := by
              apply Finset.sum_le_sum; intro j _
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              by_cases h : j = 0
              · subst h
                have hz : (∑ x : ZMod p, (τ x) ^ 0) = N := by
                  rw [Finset.sum_congr rfl (fun x _ => pow_zero (τ x))]
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← hN]
                rw [hz, inv_mul_cancel₀ hNne]
                simp
              · simp only [h, if_false]
                exact hmom j (Nat.one_le_iff_ne_zero.mpr h)
    calc N⁻¹ * ∑ x : ZMod p, (((3/2 : ℝ) * (1 + ε)) * (1 + τ x)) ^ q
        = N⁻¹ * (((3/2 : ℝ) * (1 + ε)) ^ q * ∑ x : ZMod p, (1 + τ x) ^ q) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x _; rw [mul_pow]
      _ = ((3/2 : ℝ) * (1 + ε)) ^ q * (N⁻¹ * ∑ x : ZMod p, (1 + τ x) ^ q) := by ring
      _ ≤ ((3/2 : ℝ) * (1 + ε)) ^ q
            * (∑ j ∈ Finset.range (q + 1), ((q.choose j : ℕ) : ℝ) * (if j = 0 then 1 else Cm j)) :=
            mul_le_mul_of_nonneg_left hinner (pow_nonneg hc_nn q)
  · -- the main cube correlation bound
    intro h
    let F : (Fin d → Bool) → ZMod p := fun ω => ∑ i, (if ω i then h i else 0)
    have hmeanR : ∑ x : ZMod p, ν x ≤ (Fintype.card (ZMod p) : ℝ) * (1 + ε) := by
      rw [← hN]; exact hmean
    have hcorr' : ∀ A : Finset (Fin d → Bool), 2 ≤ A.card →
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + F ω)
          ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) := by
      intro A hA
      exact hcorr A hA h
    have hb := cube_bound ν τ hν hτ hε F hmeanR hcorr'
    have hb' : N⁻¹ * ∑ y : ZMod p, ∏ ω : Fin d → Bool, ((ν (y + F ω) + 1) / 2)
        ≤ (1 + ε) + ∑ ω : Fin d → Bool,
            ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) := by
      rw [hN]; exact hb
    -- cardinality facts
    have hd2 : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := by exact pow_le_pow_right₀ (by norm_num) hd
    have hcardpos : 1 ≤ Fintype.card (Fin d → Bool) := by
      have : 0 < Fintype.card (Fin d → Bool) :=
        Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
      omega
    have hcard_filt : ∀ ω : Fin d → Bool,
        ((Finset.univ.filter (fun ω' => ω ≠ ω')).card : ℝ)
          = (Fintype.card (Fin d → Bool) : ℝ) - 1 := by
      intro ω
      have he : Finset.univ.filter (fun ω' => ω ≠ ω') = Finset.univ.erase ω := by
        ext ω'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        exact ne_comm
      rw [he, Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ,
          Nat.cast_sub hcardpos, Nat.cast_one]
    have hcardd : (Fintype.card (Fin d → Bool) : ℝ) = (2 : ℝ) ^ d := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    -- exact evaluation of the right-hand side
    have hRHS : (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          ((3/2 : ℝ) * (1 + ε)) * (1 + τ (F ω' - F ω)))
        = ((3/2 : ℝ) * (1 + ε))
            * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1)
              + ∑ ω : Fin d → Bool,
                  ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
      have hinner : ∀ ω : Fin d → Bool,
          (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              ((3/2 : ℝ) * (1 + ε)) * (1 + τ (F ω' - F ω)))
            = ((3/2 : ℝ) * (1 + ε)) * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
              + ((3/2 : ℝ) * (1 + ε))
                  * (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
        intro ω
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
            hcard_filt ω, mul_add]
      have houter : (∑ ω : Fin d → Bool,
            (((3/2 : ℝ) * (1 + ε)) * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
              + ((3/2 : ℝ) * (1 + ε))
                  * (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω))))
          = ((3/2 : ℝ) * (1 + ε))
              * ((Fintype.card (Fin d → Bool) : ℝ) * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
                + ∑ ω : Fin d → Bool,
                    ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            ← Finset.mul_sum]
        ring
      calc (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              ((3/2 : ℝ) * (1 + ε)) * (1 + τ (F ω' - F ω)))
          = ∑ ω : Fin d → Bool,
              (((3/2 : ℝ) * (1 + ε)) * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
                + ((3/2 : ℝ) * (1 + ε))
                    * (∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω))) :=
              Finset.sum_congr rfl (fun ω _ => hinner ω)
        _ = ((3/2 : ℝ) * (1 + ε))
              * ((Fintype.card (Fin d → Bool) : ℝ) * ((Fintype.card (Fin d → Bool) : ℝ) - 1)
                + ∑ ω : Fin d → Bool,
                    ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := houter
        _ = ((3/2 : ℝ) * (1 + ε))
              * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1)
                + ∑ ω : Fin d → Bool,
                    ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
              rw [hcardd]
    -- final arithmetic comparison
    have hUnn2 : 0 ≤ ∑ ω : Fin d → Bool,
        ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω) :=
      Finset.sum_nonneg (fun ω _ => Finset.sum_nonneg (fun ω' _ => hτ _))
    have hn2 : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    have hfin : (1 + ε) + ∑ ω : Fin d → Bool,
          ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)
        ≤ ((3/2 : ℝ) * (1 + ε))
            * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1)
              + ∑ ω : Fin d → Bool,
                  ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
      have hPd : (2 : ℝ) ≤ (2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1) := by nlinarith [hn2]
      have hstep1 : (1 + ε) ≤ ((3/2 : ℝ) * (1 + ε)) * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1)) := by
        nlinarith [hε, hε1, hPd]
      have hstep2 : (∑ ω : Fin d → Bool,
            ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω))
          ≤ ((3/2 : ℝ) * (1 + ε))
              * (∑ ω : Fin d → Bool,
                  ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by
        nlinarith [hUnn2, hε]
      calc (1 + ε) + ∑ ω : Fin d → Bool,
              ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)
          ≤ ((3/2 : ℝ) * (1 + ε)) * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1))
              + ((3/2 : ℝ) * (1 + ε))
                * (∑ ω : Fin d → Bool,
                    ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) :=
              add_le_add hstep1 hstep2
        _ = ((3/2 : ℝ) * (1 + ε))
              * ((2 : ℝ) ^ d * ((2 : ℝ) ^ d - 1)
                + ∑ ω : Fin d → Bool,
                    ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'), τ (F ω' - F ω)) := by ring
    show N⁻¹ * ∑ y : ZMod p, ∏ ω : Fin d → Bool, ((ν (y + F ω) + 1) / 2)
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            (((3/2 : ℝ) * (1 + ε)) * (1 + τ (F ω' - F ω)))
    rw [hRHS]
    exact hb'.trans hfin

end Commons.Combinatorics.Transference