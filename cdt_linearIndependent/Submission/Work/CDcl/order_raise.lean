import Mathlib

/-!
# `Work.CDcl.order_raise`: raising the order of an inhomogeneous linear ODE

If a power series `G : ℚ⟦X⟧` satisfies a nontrivial linear differential equation
`∑_{k<5} D_k · G^{(k)} = c` with polynomial coefficients `D_k` and polynomial right-hand side `c`,
then `G⁗` is a `ℚ[X]`-combination of `G, G', G'', G'''` plus a polynomial: there are
`q ≠ 0`, `A : Fin 4 → ℚ[X]`, `c' : ℚ[X]` with `q · G⁗ = ∑_{k<4} A_k · G^{(k)} + c'`.

Let `m ≤ 4` be the order of the given operator (the largest `k` with `D k ≠ 0`).  Differentiating
the relation `∑_{k≤m} D_k G^{(k)} = c` once turns it into `∑_{k≤m+1} E_k G^{(k)} = c'` with
`E_{m+1} = D_m ≠ 0`: the order goes up by one while the leading coefficient `D_m ≠ 0` is preserved
(the terms of order `> m+1` stay absent because the original relation has none).  After `4 - m`
differentiations the relation has order `4` with leading coefficient `D_m ≠ 0`, and solving for
`G⁗` gives the claim.

The differentiation is packaged as an iteration on the coefficient sequence of the operator:
`opStep M d = (M d)' + M (d-1)` with the convention `M (-1) = 0`.  The two structural facts used are
`opStep^[j] D` vanishes at every index `> m + j` and equals `D m` at index `m + j`.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

/-! ## The operator machinery -/

/-- The `k`-th formal derivative of `G`. -/
def derivW (G : PowerSeries ℚ) (k : ℕ) : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ))^[k] G

/-- One step of the "iterated derivative" sequence: `d/dX (derivW G k) = derivW G (k+1)`. -/
lemma derivW_succ (G : PowerSeries ℚ) (k : ℕ) :
    derivW G (k+1) = PowerSeries.derivative (R := ℚ) (derivW G k) := by
  simp only [derivW, Function.iterate_succ_apply']

/-- The coefficient of the `(d-1)`-st derivative produced when differentiating an operator;
`shiftCoef M 0 = 0` so that no spurious `G⁽⁻¹⁾` term appears. -/
def shiftCoef (M : ℕ → Polynomial ℚ) (d : ℕ) : Polynomial ℚ := if d = 0 then 0 else M (d - 1)

lemma shiftCoef_apply (M : ℕ → Polynomial ℚ) (d : ℕ) :
    shiftCoef M d = if d = 0 then 0 else M (d - 1) := rfl

/-- One differentiation of an operator of order `≤ 4` (with vanishing `4`-th coefficient). -/
def stepCoef (M : ℕ → Polynomial ℚ) : ℕ → Polynomial ℚ := fun d => (M d).derivative + shiftCoef M d

lemma stepCoef_apply (M : ℕ → Polynomial ℚ) (d : ℕ) :
    stepCoef M d = (M d).derivative + shiftCoef M d := rfl

/-- The evaluation of an operator on `G`: `∑_{k<5} M k · G^{(k)}`. -/
def opSum (M : ℕ → Polynomial ℚ) (G : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range 5, (M k : PowerSeries ℚ) * derivW G k

lemma shiftCoef_zero (M : ℕ → Polynomial ℚ) : shiftCoef M 0 = 0 := rfl

lemma shiftCoef_succ (M : ℕ → Polynomial ℚ) (d : ℕ) : shiftCoef M (d+1) = M d := by
  rw [shiftCoef_apply]; simp

/-- The shift identity: `∑_{k<5} M k · G^{(k+1)} = ∑_{d<5} (shiftCoef M d) · G^{(d)} + M 4 · G^{(5)}`. -/
lemma sum_shift_aux (M : ℕ → Polynomial ℚ) (G : PowerSeries ℚ) :
    ∑ k ∈ Finset.range 5, (M k : PowerSeries ℚ) * derivW G (k+1)
      = (∑ e ∈ Finset.range 5, (shiftCoef M e : PowerSeries ℚ) * derivW G e)
        + (M 4 : PowerSeries ℚ) * derivW G 5 := by
  rw [Finset.sum_range_succ (fun k => (M k : PowerSeries ℚ) * derivW G (k+1)) 4]
  rw [Finset.sum_range_succ' (fun e => (shiftCoef M e : PowerSeries ℚ) * derivW G e) 4]
  simp only [shiftCoef_zero, shiftCoef_succ]
  simp

/-- Differentiation of the operator, in terms of the coefficient sequence. -/
lemma deriv_opSum (M : ℕ → Polynomial ℚ) (G : PowerSeries ℚ) (h4 : M 4 = 0) :
    PowerSeries.derivative (R := ℚ) (opSum M G) = opSum (stepCoef M) G := by
  unfold opSum
  rw [map_sum]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_coe, ← derivW_succ]
  rw [Finset.sum_add_distrib]
  rw [sum_shift_aux M G]
  have hM4 : (M 4 : PowerSeries ℚ) = 0 := by simp [h4]
  rw [hM4, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [stepCoef_apply]
  push_cast
  ring

/-! ## Padding a `Fin 5`-indexed coefficient sequence to `ℕ` -/

/-- `D` extended by zero beyond index `4`. -/
def padD (D : Fin 5 → Polynomial ℚ) (k : ℕ) : Polynomial ℚ :=
  if h : k < 5 then D ⟨k, h⟩ else 0

lemma padD_of_lt (D : Fin 5 → Polynomial ℚ) {k : ℕ} (h : k < 5) : padD D k = D ⟨k, h⟩ :=
  dif_pos h

lemma padD_val (D : Fin 5 → Polynomial ℚ) (k : Fin 5) : padD D k.val = D k := by
  rw [padD_of_lt D k.isLt]

/-- The order `m` of a nonzero operator: `D m ≠ 0` and `D k = 0` for `k > m`. -/
lemma exists_max_coeff_index (D : Fin 5 → Polynomial ℚ) (hD : D ≠ 0) :
    ∃ m : ℕ, m ≤ 4 ∧ padD D m ≠ 0 ∧ ∀ k, m < k → padD D k = 0 := by
  have hne : ∃ k : Fin 5, D k ≠ 0 := by
    by_contra hc
    refine hD (funext fun k => ?_)
    exact not_not.mp (not_exists.mp hc k)
  have hSne : (Finset.univ.filter (fun k : Fin 5 => D k ≠ 0)).Nonempty := by
    obtain ⟨k, hk⟩ := hne
    exact ⟨k, by simp [hk]⟩
  set S := Finset.univ.filter (fun k : Fin 5 => D k ≠ 0) with hSdef
  have hk0mem : S.max' hSne ∈ S := Finset.max'_mem S hSne
  have hk0ne : D (S.max' hSne) ≠ 0 := by
    have h2 : S.max' hSne ∈ Finset.univ.filter (fun k : Fin 5 => D k ≠ 0) := by
      rw [← hSdef]; exact hk0mem
    exact (Finset.mem_filter.mp h2).2
  refine ⟨(S.max' hSne).val, by omega, ?_, ?_⟩
  · rw [padD_of_lt D (S.max' hSne).isLt]
    exact hk0ne
  · intro k hk
    by_cases hk5 : k < 5
    · rw [padD_of_lt D hk5]
      by_contra hc
      have hmem : (⟨k, hk5⟩ : Fin 5) ∈ S := by
        rw [hSdef]; simp [hc]
      have hle : (⟨k, hk5⟩ : Fin 5) ≤ S.max' hSne := Finset.le_max' S _ hmem
      have hle' : k ≤ (S.max' hSne).val := hle
      omega
    · rw [padD, dif_neg hk5]

/-! ## Compatibility of the formal derivative with the embedding `ℚ[X] → ℚ⟦X⟧` -/

/-- `Polynomial.derivative` as a plain function, for iteration. -/
def pDer : Polynomial ℚ → Polynomial ℚ := fun p => p.derivative

lemma powser_iterate_derivative_coe (p : Polynomial ℚ) (j : ℕ) :
    (PowerSeries.derivative (R := ℚ))^[j] (p : PowerSeries ℚ)
      = ((pDer^[j] p : Polynomial ℚ) : PowerSeries ℚ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, PowerSeries.derivative_coe]
    congr 1
    exact (Function.iterate_succ_apply' pDer j p).symm

/-! ## The main lemma -/

theorem order_raise (G : PowerSeries ℚ) (D : Fin 5 → Polynomial ℚ) (c : Polynomial ℚ)
    (hD : D ≠ 0)
    (h : (∑ k : Fin 5, (D k : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[k] G)
        = (c : PowerSeries ℚ)) :
    ∃ (q : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) (c' : Polynomial ℚ), q ≠ 0 ∧
      (q : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[4] G
        = (∑ k : Fin 4, (A k : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[k] G)
          + (c' : PowerSeries ℚ) := by
  obtain ⟨m, hm4, hDnm, hDnzero⟩ := exists_max_coeff_index D hD
  -- the given relation, in `ℕ`-indexed form
  have hDn_eq : opSum (padD D) G = (c : PowerSeries ℚ) := by
    rw [← h]
    unfold opSum
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [derivW, padD_val]
  -- the two structural facts about `opStep^[j] D`
  have hAB : ∀ j : ℕ,
      (∀ d, m + j < d → ((stepCoef^[j]) (padD D)) d = 0)
        ∧ ((stepCoef^[j]) (padD D)) (m + j) = padD D m := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro d hd
        simp only [Function.iterate_zero_apply]
        exact hDnzero d (by simpa using hd)
      · simp
    | succ j ih =>
      obtain ⟨hAj, hBj⟩ := ih
      refine ⟨?_, ?_⟩
      · intro d hd
        have h1 : m + j < d := by omega
        have h2 : d ≠ 0 := by omega
        have h3 : m + j < d - 1 := by omega
        rw [Function.iterate_succ_apply', stepCoef_apply, hAj d h1, shiftCoef_apply, if_neg h2,
          hAj (d - 1) h3]
        simp
      · rw [Function.iterate_succ_apply', stepCoef_apply]
        have h1 : m + j < m + (j + 1) := by omega
        have h2 : m + (j + 1) ≠ 0 := by omega
        have h3 : m + (j + 1) - 1 = m + j := by omega
        rw [hAj (m + (j + 1)) h1, shiftCoef_apply, if_neg h2, h3, hBj]
        simp
  -- differentiating the relation `j ≤ 4 - m` times
  have hiter : ∀ j, j ≤ 4 - m →
      (PowerSeries.derivative (R := ℚ))^[j] (opSum (padD D) G) = opSum ((stepCoef^[j]) (padD D)) G := by
    intro j
    induction j with
    | zero => intro _; simp only [Function.iterate_zero_apply]
    | succ j ih =>
      intro hj
      have hj' : j ≤ 4 - m := by omega
      have h4 : ((stepCoef^[j]) (padD D)) 4 = 0 := (hAB j).1 4 (by omega)
      rw [Function.iterate_succ_apply', ih hj', deriv_opSum _ G h4, Function.iterate_succ_apply']
  have hLHS : (PowerSeries.derivative (R := ℚ))^[4 - m] (opSum (padD D) G)
      = ((pDer^[4-m] c : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [hDn_eq]
    exact powser_iterate_derivative_coe c (4 - m)
  have hsum : opSum ((stepCoef^[4-m]) (padD D)) G = ((pDer^[4-m] c : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [← hiter (4-m) le_rfl, hLHS]
  -- the leading coefficient after `4 - m` differentiations is `D m ≠ 0`
  have htop : ((stepCoef^[4-m]) (padD D)) 4 = padD D m := by
    have hh := (hAB (4 - m)).2
    rwa [Nat.add_sub_of_le hm4] at hh
  have hq : ((stepCoef^[4-m]) (padD D)) 4 ≠ 0 := by rw [htop]; exact hDnm
  refine ⟨((stepCoef^[4-m]) (padD D)) 4, fun k => -(((stepCoef^[4-m]) (padD D)) k.val),
    (pDer^[4-m] c), hq, ?_⟩
  change (((stepCoef^[4-m]) (padD D)) 4 : PowerSeries ℚ) * derivW G 4
      = (∑ k : Fin 4, ((-(((stepCoef^[4-m]) (padD D)) k.val) : Polynomial ℚ) : PowerSeries ℚ)
          * derivW G k.val)
        + ((pDer^[4-m] c : Polynomial ℚ) : PowerSeries ℚ)
  -- isolate the order-`4` coefficient in the differentiated relation
  have hsum2 : (((stepCoef^[4-m]) (padD D)) 4 : PowerSeries ℚ) * derivW G 4
      = ((pDer^[4-m] c : Polynomial ℚ) : PowerSeries ℚ)
        - ∑ k ∈ Finset.range 4, (((stepCoef^[4-m]) (padD D)) k : PowerSeries ℚ) * derivW G k := by
    have hh := hsum
    unfold opSum at hh
    rw [Finset.sum_range_succ] at hh
    rw [← hh]; abel
  have hsum3 : (((stepCoef^[4-m]) (padD D)) 4 : PowerSeries ℚ) * derivW G 4
      = ((pDer^[4-m] c : Polynomial ℚ) : PowerSeries ℚ)
        - ∑ k : Fin 4, (((stepCoef^[4-m]) (padD D)) k.val : PowerSeries ℚ) * derivW G k.val := by
    rw [hsum2, Finset.sum_range]
  rw [hsum3]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  abel

end Work.CDcl
