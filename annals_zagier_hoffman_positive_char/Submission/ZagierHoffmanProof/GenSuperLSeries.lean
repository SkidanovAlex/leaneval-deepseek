import Submission.ZagierHoffmanProof.GenLSeriesDepth

/-!
# Chang's Lemma 5.3.1 over an arbitrary value group

Generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `SuperLSeries.lean`: the
cutoff `L`-series `atLrcutGen q ω L N` of a small, super-entire datum is super-entire, with a
bound *uniform in the cutoff* `N`.

The proof is the same observation as in depth one: twisting a coefficient to its `q^k`-th power
decreases its valuation (the coefficients are small), so the twisted factors are dominated termwise
by the untwisted ones, and super-entireness is closed under products and infinite sums.

## Main results

* `gIsSmall_frobTwist_coeff_le`, `gIsSmall_frobTwist_coeff_le_self`.
* `coeff_twist_mul_le_gen`, `summable_twist_mul_gen`.
* `gSuperEntire_atLrcut_bound`, `gSuperEntire_atLrcut`, `gSuperEntire_atLrGen`,
  `gSuperEntire_atLrPaperGen`, `gSuperEntire_atLrGen_mul_pow`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section basic

variable {q : ℕ} [FrobPow K q] {γ : Γ₀}

/-- The coefficients of a Frobenius twist of a small series are bounded by `γ ^ (q^k)`. -/
lemma gIsSmall_frobTwist_coeff_le {F : PowerSeries K} (hF : GIsSmall γ F) (k m : ℕ) :
    Valued.v (PowerSeries.coeff m (frobTwist (R := K) (p := q) k F)) ≤ γ ^ (q ^ k) := by
  rw [frobTwist_coeff, map_pow]
  exact pow_le_pow_left' (hF m) _

/-- Twisting a small series decreases (weakly) every coefficient valuation. -/
lemma gIsSmall_frobTwist_coeff_le_self (hγ : γ < 1) {F : PowerSeries K} (hF : GIsSmall γ F)
    (k m : ℕ) :
    Valued.v (PowerSeries.coeff m (frobTwist (R := K) (p := q) k F))
      ≤ Valued.v (PowerSeries.coeff m F) := by
  rw [frobTwist_coeff, map_pow]
  refine le_trans (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ _)
    (le_trans (hF m) hγ.le) (Nat.one_le_pow k q (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := q))))) (le_of_eq (pow_one _))

end basic

section main

variable {q : ℕ} [FrobPow K q] {γ : Γ₀}

/-- The coefficient bound for a single term of the recursion. -/
lemma coeff_twist_mul_le_gen (hγ : γ < 1) {F : PowerSeries K} (hF : GIsSmall γ F) (M : ℕ)
    {aF : Γ₀} (haF : ∀ m : ℕ, Valued.v (PowerSeries.coeff m F) ≤ aF * γ ^ (M * m))
    {g : ℕ → PowerSeries K} {ar : Γ₀}
    (har : ∀ j m : ℕ, Valued.v (PowerSeries.coeff m (g j)) ≤ ar * γ ^ (M * m)) (N i n : ℕ) :
    Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) F * g i))
      ≤ (aF * ar) * γ ^ (M * n) := by
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p hp => ?_)
  rw [Valuation.map_mul]
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have h1 : Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F))
      ≤ aF * γ ^ (M * p.1) :=
    le_trans (gIsSmall_frobTwist_coeff_le_self (q := q) hγ hF (N + i) p.1) (haF p.1)
  calc Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F))
        * Valued.v (PowerSeries.coeff p.2 (g i))
      ≤ (aF * γ ^ (M * p.1)) * (ar * γ ^ (M * p.2)) := mul_le_mul' h1 (har i p.2)
    _ = (aF * ar) * γ ^ (M * n) := by
        rw [mul_mul_mul_comm aF (γ ^ (M * p.1)) ar (γ ^ (M * p.2)), ← pow_add,
          ← Nat.mul_add, hp']

/-- The defining family of the recursion is summable. -/
lemma summable_twist_mul_gen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {F : PowerSeries K} (hF : GIsSmall γ F) (M : ℕ)
    {g : ℕ → PowerSeries K} {ar : Γ₀}
    (har : ∀ j m : ℕ, Valued.v (PowerSeries.coeff m (g j)) ≤ ar * γ ^ (M * m)) (N n : ℕ) :
    Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) F * g i) := by
  refine summable_of_v_le_mul_gamma_pow (K := K) (q := q) (N := N) hγ harch hq (C := ar)
    (f := fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) F * g i)) (fun i => ?_)
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p hp => ?_)
  rw [Valuation.map_mul]
  have h1 := gIsSmall_frobTwist_coeff_le (q := q) hF (N + i) p.1
  have h2 : Valued.v (PowerSeries.coeff p.2 (g i)) ≤ ar := by
    refine le_trans (har i p.2) ?_
    simpa using mul_le_mul_right (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le
      (Nat.zero_le (M * p.2))) ar
  calc Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F))
        * Valued.v (PowerSeries.coeff p.2 (g i))
      ≤ γ ^ (q ^ (N + i)) * ar := mul_le_mul' h1 h2
    _ = ar * γ ^ (q ^ (N + i)) := mul_comm _ _

/-- **The uniform-in-the-cutoff super-entireness of the `L`-series.** -/
theorem gSuperEntire_atLrcut_bound (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω) (M : ℕ) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) →
      (∀ x ∈ L, GSuperEntire γ x.2) →
      ∃ a : Γ₀, ∀ (N n : ℕ),
        Valued.v (PowerSeries.coeff n (atLrcutGen q ω L N)) ≤ a * γ ^ (M * n) := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨1, fun N n => ?_⟩
    rw [atLrcutGen_nil, PowerSeries.coeff_one]
    by_cases h : n = 0
    · subst h
      rw [if_pos rfl, map_one, Nat.mul_zero, pow_zero, mul_one]
    · rw [if_neg h, map_zero]
      exact (zero_le : (0 : Γ₀) ≤ _)
  | cons a rest ih =>
    obtain ⟨s, Q⟩ := a
    intro hL hLse
    have hFsmall : GIsSmall γ (ω ^ s * Q) := hL (s, Q) (by simp)
    have hQse : GSuperEntire γ Q := hLse (s, Q) (by simp)
    have hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2) :=
      fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hrestse : ∀ x ∈ rest, GSuperEntire γ x.2 :=
      fun x hx => hLse x (List.mem_cons_of_mem _ hx)
    obtain ⟨ar, har⟩ := ih hrest hrestse
    obtain ⟨aF, haF⟩ := ((hωse.pow hγ.le s).mul hγ.le hQse) M
    refine ⟨aF * ar, fun N n => ?_⟩
    rw [atLrcutGen_cons, PowerSeries.coeff_mk]
    refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
      (summable_twist_mul_gen hγ harch hq hFsmall M (fun j m => har (N + j + 1) m) N n)
      (fun i => ?_)
    exact coeff_twist_mul_le_gen hγ hFsmall M haF (fun j m => har (N + j + 1) m) N i n

end main

section conclude

variable {q : ℕ} [FrobPow K q] {γ : Γ₀}

/-- **Chang's Lemma 5.3.1 for the cutoff `L`-series** (generic value group). -/
theorem gSuperEntire_atLrcut (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {L : List (ℕ × PowerSeries K)} (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (N : ℕ) :
    GSuperEntire γ (atLrcutGen q ω L N) := fun M =>
  let ⟨a, ha⟩ := gSuperEntire_atLrcut_bound hγ harch hq hω hωse M L hL hLse
  ⟨a, fun n => ha N n⟩

/-- **Chang's Lemma 5.3.1**: the `L`-series `𝓛(𝔰;Q) = atLrGen q ω L` is super-entire. -/
theorem gSuperEntire_atLrGen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {L : List (ℕ × PowerSeries K)} (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ L, GSuperEntire γ x.2) : GSuperEntire γ (atLrGen q ω L) :=
  gSuperEntire_atLrcut hγ harch hq hω hωse hL hLse 0

/-- Chang's `L`-series in the paper's ordering convention is super-entire. -/
theorem gSuperEntire_atLrPaperGen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {L : List (ℕ × PowerSeries K)} (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ L, GSuperEntire γ x.2) : GSuperEntire γ (atLrPaperGen q ω L) := by
  rw [atLrPaperGen]
  exact gSuperEntire_atLrGen hγ harch hq hω hωse (fun x hx => hL x (List.mem_reverse.mp hx))
    (fun x hx => hLse x (List.mem_reverse.mp hx))

/-- **The entries of the rigid analytic trivialisation matrix lie in `ε`** (generic value
group): the products `𝓛(𝔰_{≥j};Q)·Ω^{w - w_j}`. -/
theorem gSuperEntire_atLrGen_mul_pow (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {L : List (ℕ × PowerSeries K)} (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (s : ℕ) :
    GSuperEntire γ (atLrGen q ω L * ω ^ s) :=
  (gSuperEntire_atLrGen hγ harch hq hω hωse hL hLse).mul hγ.le (hωse.pow hγ.le s)

end conclude

end ZagierHoffmanPositiveChar
