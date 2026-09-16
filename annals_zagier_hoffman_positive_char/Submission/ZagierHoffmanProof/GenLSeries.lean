import Submission.ZagierHoffmanProof.GenEvalEntire
import Submission.ZagierHoffmanProof.FrobPowTsum
import Submission.Commons.Topology.InfiniteSum.tsum_shift_one

/-!
# The depth-one `L`-series over an arbitrary valued field

This is the generic version (arbitrary value group `Γ₀`, fixed small `γ`) of the depth-one
`L`-series chapter of `LSeries.lean`.  For a tuple datum `(s, Q)` and a "small" series `ω` (all of
whose coefficients lie in the maximal ideal of the Tate algebra, i.e. `GIsSmall γ ω`), the
depth-one `L`-series is

  `atL1Gen q ω s Q = ∑_{i ≥ 0} (ω^s Q)^{(i)}`,

and it satisfies the trivialisation recursion `L = ω^s Q + L^{(1)}`.

## Main results

* `GIsSmall` and its closure properties (`mul`, `pow_add_one`, `pow_mul`, `add`, `neg`).
* `atL1Gen` and `coeff_atL1Gen`.
* `summable_coeff_atL1Gen_term` — the defining family is coefficientwise summable.
* `atL1Gen_eq_mul_add_frobTwist` — the `L`-series recursion (the `r = 1` case of
  `Ψ^{(-1)} = ΦΨ`).
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- A power series all of whose coefficients have valuation at most the fixed small element `γ`:
the generic form of `IsSmall` (= the convergence condition (2.1) of the paper). -/
def GIsSmall (γ : Γ₀) (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ γ

section small

variable {γ : Γ₀} {f g : PowerSeries K}

lemma gIsSmall_zero (γ : Γ₀) : GIsSmall γ (0 : PowerSeries K) :=
  fun n => by rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v)]; exact zero_le

lemma GIsSmall.neg (hf : GIsSmall γ f) : GIsSmall γ (-f) := fun n => by
  rw [map_neg (PowerSeries.coeff n) f, Valuation.map_neg]; exact hf n

lemma GIsSmall.add (hf : GIsSmall γ f) (hg : GIsSmall γ g) : GIsSmall γ (f + g) := by
  intro n
  rw [map_add (PowerSeries.coeff n)]
  exact le_trans (Valuation.map_add_le_max' _ _ _) (max_le (hf n) (hg n))

lemma GIsSmall.sub (hf : GIsSmall γ f) (hg : GIsSmall γ g) : GIsSmall γ (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma GIsSmall.mul (hγ : γ ≤ 1) (hf : GIsSmall γ f) (hg : GIsSmall γ g) :
    GIsSmall γ (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (v := Valued.v) (g := γ) (fun p hp => ?_)
  rw [map_mul]
  calc Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
      ≤ γ * γ := mul_le_mul' (hf p.1) (hg p.2)
    _ ≤ γ * 1 := mul_le_mul_right hγ γ
    _ = γ := mul_one γ

lemma GIsSmall.pow_add_one (hγ : γ ≤ 1) (hf : GIsSmall γ f) (s : ℕ) :
    GIsSmall γ (f ^ (s + 1)) := by
  induction s with
  | zero => simpa using hf
  | succ s ih => rw [pow_succ]; exact ih.mul hγ hf

lemma GIsSmall.pow_mul (hγ : γ ≤ 1) (hf : GIsSmall γ f) (hg : GIsSmall γ g) (s : ℕ) :
    GIsSmall γ (f ^ s * g) := by
  cases s with
  | zero => simpa using hg
  | succ s => rw [pow_succ]; exact (hf.pow_add_one hγ s).mul hγ hg

end small

section Lseries

variable (q : ℕ) [FrobPow K q]

/-- The depth-one `L`-series `∑_{i ≥ 0} (ω^s Q)^{(i)}` (generic value group; the definition does
not involve the valuation). -/
noncomputable def atL1Gen (ω : PowerSeries K) (s : ℕ) (Q : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑' i : ℕ,
    PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))

lemma coeff_atL1Gen (ω : PowerSeries K) (s : ℕ) (Q : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (atL1Gen q ω s Q)
      = ∑' i : ℕ, PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q)) :=
  PowerSeries.coeff_mk n _

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The defining family of the depth-one `L`-series is coefficientwise summable, as soon as the
*factor* `ω^s · Q` is small: the valuation of the `i`-th term is bounded by `γ ^ (q ^ i)`, which
tends to `0` for `i → ∞`.

(Note the hypothesis is on the product `ω ^ s * Q`, not on `Q` alone: this is the form needed by
the applications, where `ω^s Q` is small because `ω` is, while `Q` itself need not be — e.g. the
constant `1` is not small.) -/
lemma summable_coeff_atL1Gen_term {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hq : 2 ≤ q) {ω : PowerSeries K} {Q : PowerSeries K} (s : ℕ)
    (hF : GIsSmall γ (ω ^ s * Q)) (n : ℕ) :
    Summable fun i : ℕ =>
      PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q)) := by
  have hsmall : Valued.v (PowerSeries.coeff n (ω ^ s * Q)) ≤ γ := hF n
  refine summable_of_v_tendsto_zero (fun ε hε => ?_)
  obtain ⟨N, hN⟩ := harch γ hγ ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
  rw [frobTwist_coeff, map_pow]
  have hi' : N ≤ q ^ i := le_trans hi (le_of_lt (Nat.lt_pow_self (n := i) (by omega : 1 < q)))
  calc (Valued.v (PowerSeries.coeff n (ω ^ s * Q))) ^ (q ^ i)
      ≤ γ ^ (q ^ i) := pow_le_pow_left' hsmall _
    _ ≤ γ ^ N := pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le hi'
    _ < ε := hN

/-- **The `L`-series recursion**: `L = ω^s Q + L^{(1)}` (the `r = 1` case of the rigid analytic
trivialisation relation `Ψ^{(-1)} = ΦΨ`).  The hypothesis is on the factor `ω ^ s * Q`. -/
theorem atL1Gen_eq_mul_add_frobTwist {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hq : 2 ≤ q) {ω : PowerSeries K} {Q : PowerSeries K} (s : ℕ)
    (hF : GIsSmall γ (ω ^ s * Q)) :
    atL1Gen q ω s Q = ω ^ s * Q + frobTwist (R := K) (p := q) 1 (atL1Gen q ω s Q) := by
  ext n
  have hsum := summable_coeff_atL1Gen_term q hγ harch hq s hF n
  have hstep : (∑' i : ℕ,
        (PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))) ^ (q ^ 1))
      = ∑' i : ℕ, PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + 1) (ω ^ s * Q)) := by
    refine tsum_congr (fun i => ?_)
    rw [frobTwist_coeff, frobTwist_coeff, ← pow_mul, pow_one, ← pow_succ]
  rw [coeff_atL1Gen, map_add (PowerSeries.coeff n), frobTwist_coeff, coeff_atL1Gen,
    ZagierHoffmanPositiveChar.tsum_pow_frobPow_general hsum 1, hstep,
    Commons.Topology.InfiniteSum.tsum_shift_one hsum]
  have h0 : PowerSeries.coeff n (frobTwist (R := K) (p := q) 0 (ω ^ s * Q))
      = PowerSeries.coeff n (ω ^ s * Q) := by
    rw [frobTwist_coeff, pow_zero, pow_one]
  rw [h0]
  ring

end Lseries

end ZagierHoffmanPositiveChar
