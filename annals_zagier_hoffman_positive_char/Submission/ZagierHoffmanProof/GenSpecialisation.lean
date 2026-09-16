import Submission.ZagierHoffmanProof.GenMZProperty

/-!
# Specialisation of `L`-series relations at the points `t = c^{q^j}` (generic value group)

Generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `Specialisation.lean`: the
**specialisation step** of the proof of Ngo Dac's Theorems B/D (paper §5, "Step 2"), the part of
the argument that happens *after* the Anderson–Brownawell–Papanikolas criterion has produced a
relation `∑_k B_k(t)·𝓛_k(t)·ω(t)^{w-w_k} = 0` with `B_k = P_k/Q_k ∈ K̄(t)`.

Clearing denominators turns it into an identity between super-entire series, so the ring
homomorphism `ε → K` can be applied to it (`specialise_sum_div`); specialising at `t = c^{q^j}` and
using the MZ property `𝓛_k(c^{q^j}) = (𝓛_k(c))^{q^j}` together with the vanishing `ω(c^{q^j}) = 0`
for `j ≥ 1` kills the terms of weight `< W` and leaves

  `∑_{k : w_k = W} B_k(c^{q^j})·(𝓛_k(c))^{q^j} = 0`

(`step2_specialisation_gen`).

## Main results

* `GSuperEntire.polynomial`, `evalSeriesGen_polynomial`.
* `specialise_sum_div_gen` — clearing denominators and evaluating.
* ★★★ `step2_specialisation_gen` — the specialisation of the paper's relation at `c^{q^j}`.
* `pow_q_orbit_injective`, `polynomial_eq_zero_of_eventually_eval_eq_zero_gen`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section poly

/-- A polynomial, viewed as a power series, is super-entire (generic value group and rate). -/
lemma GSuperEntire.polynomial {γ : Γ₀} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (p : Polynomial K) :
    GSuperEntire γ (p : PowerSeries K) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using GSuperEntire.C γ a
  | add p q hp hq => rw [Polynomial.coe_add]; exact hp.add hq
  | monomial n a _ =>
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact GSuperEntire.mul hγ1 (GSuperEntire.C γ a)
        (GSuperEntire.pow hγ1 (GSuperEntire.X hγ0) (n + 1))

/-- **Evaluation of a polynomial agrees with the polynomial evaluation** (generic value group). -/
lemma evalSeriesGen_polynomial (p : Polynomial K) (c : K) :
    evalSeriesGen (p : PowerSeries K) c = p.eval c := by
  have hmain : (∑' n : ℕ, (PowerSeries.coeff n (p : PowerSeries K)) * c ^ n)
      = ∑ n ∈ Finset.range (p.natDegree + 1),
          (PowerSeries.coeff n (p : PowerSeries K)) * c ^ n := by
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (fun n hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  rw [evalSeriesGen_def, hmain, Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Polynomial.coeff_coe])

end poly

/-- The weight `s_1 + ⋯ + s_r` attached to a tuple of `L`-series data. -/
def lseriesWeightGen (L : List (ℕ × PowerSeries K)) : ℕ := (L.map Prod.fst).sum

lemma evalSeriesGen_zero (c : K) : evalSeriesGen (0 : PowerSeries K) c = 0 := by
  simp [evalSeriesGen_def]

/-- **Clearing denominators and evaluating** (generic value group). -/
theorem specialise_sum_div_gen {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P Q : ι → Polynomial K) (S : ι → PowerSeries K) (c : K)
    (hS : ∀ i ∈ s, GSuperEntire γ (S i)) (hQ : ∀ i ∈ s, (Q i).eval c ≠ 0)
    (h : ∑ i ∈ s, ((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i = 0) :
    ∑ i ∈ s, ((P i).eval c / (Q i).eval c) * evalSeriesGen (S i) c = 0 := by
  have hterm : ∀ i ∈ s,
      GSuperEntire γ (((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i) :=
    fun i hi => (GSuperEntire.polynomial hγ0 hγ.le _).mul hγ.le (hS i hi)
  have h1 : evalSeriesGen (∑ i ∈ s,
      ((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i) c = 0 := by
    rw [h, evalSeriesGen_zero]
  rw [evalSeriesGen_finset_sum hγ harch _ _ hterm c] at h1
  have h2 : ∑ i ∈ s, ((P i).eval c * ∏ j ∈ s.erase i, (Q j).eval c) * evalSeriesGen (S i) c = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [evalSeriesGen_mul hγ harch (GSuperEntire.polynomial hγ0 hγ.le _) (hS i hi) c,
      evalSeriesGen_polynomial, Polynomial.eval_mul, Polynomial.eval_prod]
  have h3 : (∏ i ∈ s, (Q i).eval c)
      * (∑ i ∈ s, ((P i).eval c / (Q i).eval c) * evalSeriesGen (S i) c) = 0 := by
    rw [Finset.mul_sum]
    rw [← h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_prod_erase s (fun i => (Q i).eval c) hi]
    have hq : (Q i).eval c ≠ 0 := hQ i hi
    field_simp
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (Finset.prod_ne_zero_iff.mpr hQ)
  · exact h4

section step2

/-- **Step 2 of the paper: specialising a relation between `L`-series at `t = c^{q^j}`** (generic
value group). -/
theorem step2_specialisation_gen {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (q : ℕ) [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K}
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : ι → List (ℕ × PowerSeries K))
    (hne : ∀ k ∈ s, L k ≠ [])
    (hL : ∀ k ∈ s, ∀ x ∈ L k, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ k ∈ s, ∀ x ∈ L k, GSuperEntire γ x.2)
    (hs : ∀ k ∈ s, ∀ x ∈ L k, 1 ≤ x.1)
    (P Q : ι → Polynomial K) (W : ℕ) (hW : ∀ k ∈ s, lseriesWeightGen (L k) ≤ W)
    {j : ℕ} (hj : 1 ≤ j) (hQc : ∀ k ∈ s, (Q k).eval (c ^ (q ^ j)) ≠ 0)
    (h : ∑ k ∈ s, ((P k * ∏ l ∈ s.erase k, Q l : Polynomial K) : PowerSeries K)
          * (atLrPaperGen q ω (L k) * ω ^ (W - lseriesWeightGen (L k))) = 0) :
    ∑ k ∈ s.filter (fun k => lseriesWeightGen (L k) = W),
        ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
          * (evalSeriesGen (atLrPaperGen q ω (L k)) c) ^ (q ^ j) = 0 := by
  have hS : ∀ k ∈ s, GSuperEntire γ
      (atLrPaperGen q ω (L k) * ω ^ (W - lseriesWeightGen (L k))) :=
    fun k hk => (gSuperEntire_atLrPaperGen hγ harch hq hω hωse (hL k hk) (hLse k hk)).mul
      hγ.le (hωse.pow hγ.le _)
  have hmain := specialise_sum_div_gen hγ0 hγ harch s P Q
    (fun k => atLrPaperGen q ω (L k) * ω ^ (W - lseriesWeightGen (L k))) (c ^ (q ^ j)) hS hQc h
  rw [Finset.sum_filter]
  have hkey : ∀ k ∈ s,
      (if lseriesWeightGen (L k) = W then
          ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
            * (evalSeriesGen (atLrPaperGen q ω (L k)) c) ^ (q ^ j)
        else 0)
      = ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
          * evalSeriesGen (atLrPaperGen q ω (L k) * ω ^ (W - lseriesWeightGen (L k)))
              (c ^ (q ^ j)) := by
    intro k hk
    by_cases hkw : lseriesWeightGen (L k) = W
    · rw [if_pos hkw,
        evalSeriesGen_mul hγ harch (gSuperEntire_atLrPaperGen hγ harch hq hω hωse (hL k hk)
          (hLse k hk)) (hωse.pow hγ.le _) _,
        evalSeriesGen_pow hγ harch hωse _ _, hkw, Nat.sub_self, pow_zero, mul_one,
        evalSeriesGen_atLrPaperGen_frobenius_pow_of_ne q hγ0 hγ harch hq hω hωse (hne k hk)
          (hL k hk) (hLse k hk) (hs k hk _ (List.getLast_mem (hne k hk))) hc j]
    · rw [if_neg hkw]
      have hlt : lseriesWeightGen (L k) < W := lt_of_le_of_ne (hW k hk) hkw
      rw [evalSeriesGen_mul hγ harch (gSuperEntire_atLrPaperGen hγ harch hq hω hωse (hL k hk)
          (hLse k hk)) (hωse.pow hγ.le _) _,
        evalSeriesGen_pow hγ harch hωse _ _, hc j hj,
        zero_pow (by omega : W - lseriesWeightGen (L k) ≠ 0), mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hkey]
  exact hmain

end step2

section orbit

/-- Along the Frobenius orbit of `θ` the valuations are pairwise distinct as soon as
`v θ ∉ {0, 1}` (the sequence `(v θ) ^ (q^j)` is strictly monotone). -/
lemma v_pow_q_orbit_ne {θ : K} (hθ0 : Valued.v θ ≠ 0) (hθ1 : Valued.v θ ≠ 1)
    {q : ℕ} (hq : 2 ≤ q) {i j : ℕ} (hij : i < j) :
    Valued.v (θ ^ (q ^ i)) ≠ Valued.v (θ ^ (q ^ j)) := by
  intro h
  rw [Valuation.map_pow, Valuation.map_pow] at h
  have hq_lt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  rcases lt_or_gt_of_ne (Ne.symm hθ1) with hgt | hlt
  · have h1 := pow_lt_pow_right₀ hgt hq_lt
    rw [h] at h1
    exact absurd h1 (lt_irrefl _)
  · have h1 := pow_lt_pow_right_of_lt_one₀ (zero_lt_of_ne_zero hθ0) hlt hq_lt
    rw [h] at h1
    exact absurd h1 (lt_irrefl _)

/-- The Frobenius orbit `j ↦ θ^{q^j}` is injective as soon as `v θ ∉ {0, 1}`. -/
lemma pow_q_orbit_injective {θ : K} (hθ0 : Valued.v θ ≠ 0) (hθ1 : Valued.v θ ≠ 1)
    {q : ℕ} (hq : 2 ≤ q) : Function.Injective fun j : ℕ => θ ^ (q ^ j) := by
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (congrArg Valued.v hij) (v_pow_q_orbit_ne hθ0 hθ1 hq h)
  · exact h
  · exact absurd (congrArg Valued.v hij).symm (v_pow_q_orbit_ne hθ0 hθ1 hq h)

/-- **A polynomial vanishing at `θ^{q^j}` for all large `j` is zero** (generic value group): the
Frobenius orbit of `θ` is infinite while a non-zero polynomial has finitely many roots. -/
theorem polynomial_eq_zero_of_eventually_eval_eq_zero_gen {θ : K} (hθ0 : Valued.v θ ≠ 0)
    (hθ1 : Valued.v θ ≠ 1) {q : ℕ} (hq : 2 ≤ q) {B : Polynomial K}
    (h : ∀ᶠ j : ℕ in Filter.atTop, B.eval (θ ^ (q ^ j)) = 0) : B = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have hinj : Function.Injective fun k : ℕ => θ ^ (q ^ (N + k)) := fun a b hab =>
    Nat.add_left_cancel (pow_q_orbit_injective hθ0 hθ1 hq hab)
  have hinf : Set.Infinite (Set.range fun k : ℕ => θ ^ (q ^ (N + k))) :=
    Set.infinite_range_of_injective hinj
  refine Polynomial.eq_zero_of_infinite_isRoot B ?_
  refine hinf.mono fun x hx => ?_
  obtain ⟨k, rfl⟩ := hx
  exact Polynomial.IsRoot.def.mpr (hN _ (Nat.le_add_right N k))

end orbit

end ZagierHoffmanPositiveChar
