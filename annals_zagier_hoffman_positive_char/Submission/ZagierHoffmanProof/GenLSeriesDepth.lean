import Submission.ZagierHoffmanProof.GenLSeriesFold
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general

/-!
# The depth-`r` `L`-series over an arbitrary value group

Generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `LSeriesDepth.lean`.  The
depth-`r` `L`-series of the paper is

  `L(s;Q) = ∑_{i₁ > ⋯ > i_r ≥ 0} (ω^{s_r}Q_r)^{(i_r)} … (ω^{s_1}Q_1)^{(i_1)}`,

built here as `atLrGen q ω L = atLrFoldGen q ω (fun _ => 1) L 0` with the "increasing index"
convention.

## Main definitions and results

* `atLrFoldGen`, `atLrcutGen`, `atLrGen` and the recursion `atLrFoldGen_cons`.
* `summable_of_v_le_gamma_pow` — the generic summability criterion.
* `coeff_atLrFoldGen_le_one`, `gIsSmall_atLrGen`.
* `frobTwist_atLrcutGen` — the twist–shift identity `L(N+k) = (L(N))^{(k)}`.
* `atLrcutGen_fold`, `atLrFoldGen_append`, `atLrcutGen_singleton`, `atLrGen_singleton`.
* The paper's convention `atLrPaperGen` and its recursion `atLrPaperGen_fold`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section depth

/-- The generic summability criterion: a family whose `i`-th term has valuation at most
`γ ^ (q ^ (N+i))` (with `γ < 1` and an archimedean value group) is summable. -/
lemma summable_of_v_le_gamma_pow {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} (hq : 2 ≤ q) {N : ℕ} {f : ℕ → K}
    (h : ∀ i : ℕ, Valued.v (f i) ≤ γ ^ (q ^ (N + i))) : Summable f := by
  refine summable_of_v_tendsto_zero (fun ε hε => ?_)
  obtain ⟨N', hN'⟩ := harch γ hγ ε hε
  refine Filter.eventually_atTop.mpr ⟨N', fun i hi => ?_⟩
  have hqi : N' ≤ q ^ (N + i) :=
    le_trans hi (le_trans (by omega : i ≤ N + i)
      (le_of_lt (Nat.lt_pow_self (n := N + i) (a := q) (by omega))))
  exact lt_of_le_of_lt (le_trans (h i)
    (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le hqi)) hN'

/-- The generic summability criterion with a multiplicative constant: a family whose `i`-th term
has valuation at most `C · γ ^ (q ^ (N+i))` (with `γ < 1` and an archimedean value group) is
summable. -/
lemma summable_of_v_le_mul_gamma_pow {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} (hq : 2 ≤ q) {N : ℕ} {C : Γ₀} {f : ℕ → K}
    (h : ∀ i : ℕ, Valued.v (f i) ≤ C * γ ^ (q ^ (N + i))) : Summable f := by
  rcases eq_or_ne C 0 with hC | hC
  · refine summable_of_v_tendsto_zero (fun ε hε => ?_)
    refine Filter.Eventually.of_forall (fun i => ?_)
    simp only [hC, zero_mul] at h
    exact lt_of_le_of_lt (h i) (zero_lt_of_ne_zero hε)
  · have hCpos : 0 < C := zero_lt_of_ne_zero hC
    refine summable_of_v_tendsto_zero (fun ε hε => ?_)
    obtain ⟨N', hN'⟩ := harch γ hγ (ε / C) (by simp [hε, hC])
    refine Filter.eventually_atTop.mpr ⟨N', fun i hi => ?_⟩
    have hqi : N' ≤ q ^ (N + i) :=
      le_trans hi (le_trans (by omega : i ≤ N + i)
        (le_of_lt (Nat.lt_pow_self (n := N + i) (a := q) (by omega))))
    refine lt_of_le_of_lt (h i) ?_
    calc C * γ ^ (q ^ (N + i)) ≤ C * γ ^ N' :=
          mul_le_mul_right (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le hqi) C
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hN' hCpos
      _ = ε := by rw [mul_comm, div_mul_cancel₀ ε hC]

/-- The coefficient of a product of power series is bounded by the product of any uniform bounds
on the coefficients of the factors (generic value group). -/
lemma coeff_mul_le_general (f g : PowerSeries K) {a b : Γ₀}
    (hf : ∀ m : ℕ, Valued.v (PowerSeries.coeff m f) ≤ a)
    (hg : ∀ m : ℕ, Valued.v (PowerSeries.coeff m g) ≤ b) (n : ℕ) :
    Valued.v (PowerSeries.coeff n (f * g)) ≤ a * b := by
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p _ => ?_)
  rw [map_mul]
  exact mul_le_mul' (hf p.1) (hg p.2)

/-- The cutoff depth-`p` `L`-series attached to the list `L = [(s₁,Q₁),…,(s_p,Q_p)]` and a tail
function `g`.  Semantically
`atLrFoldGen q ω g L N = ∑_{N ≤ i₁ < ⋯ < i_p} (∏_j (ω^{s_j}Q_j)^{(i_j)}) · g (i_p + 1)`. -/
noncomputable def atLrFoldGen (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (g : ℕ → PowerSeries K) :
    List (ℕ × PowerSeries K) → ℕ → PowerSeries K
  | [], N => g N
  | (s, Q) :: rest, N => PowerSeries.mk fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrFoldGen q ω g rest (N + i + 1))

/-- The `L`-series with cutoff `N` (generic value group). -/
noncomputable def atLrcutGen (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (N : ℕ) : PowerSeries K :=
  atLrFoldGen q ω (fun _ => 1) L N

/-- The depth-`p` `L`-series `atLrGen q ω L = atLrcutGen q ω L 0` (generic value group). -/
noncomputable def atLrGen (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : PowerSeries K :=
  atLrcutGen q ω L 0

@[simp] lemma atLrFoldGen_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (g : ℕ → PowerSeries K) (N : ℕ) :
    atLrFoldGen q ω g ([] : List (ℕ × PowerSeries K)) N = g N := rfl

@[simp] lemma atLrFoldGen_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (g : ℕ → PowerSeries K) (s : ℕ) (Q : PowerSeries K)
    (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    atLrFoldGen q ω g ((s, Q) :: rest) N = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrFoldGen q ω g rest (N + i + 1))) := rfl

@[simp] lemma atLrcutGen_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (N : ℕ) :
    atLrcutGen q ω ([] : List (ℕ × PowerSeries K)) N = 1 := rfl

@[simp] lemma atLrcutGen_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (s : ℕ)
    (Q : PowerSeries K) (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    atLrcutGen q ω ((s, Q) :: rest) N = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrcutGen q ω rest (N + i + 1))) := rfl

lemma atLrcutGen_zero (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : atLrcutGen q ω L 0 = atLrGen q ω L := rfl

/-- The coefficient valuations of the cutoff `L`-series are bounded by `1`, as long as the tail
function has this bound and all factors are small. -/
lemma coeff_atLrFoldGen_le_one {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    {g : ℕ → PowerSeries K} (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) → ∀ N n,
      Valued.v (PowerSeries.coeff n (atLrFoldGen q ω g L N)) ≤ 1 := by
  intro L
  induction L with
  | nil => intro _ N n; rw [atLrFoldGen_nil]; exact hg N n
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL N n
      have hF : GIsSmall γ (ω ^ s * Q) := hL (s, Q) (by simp)
      rw [atLrFoldGen_cons, PowerSeries.coeff_mk]
      have hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2) := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hterm : ∀ i : ℕ, Valued.v (PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrFoldGen q ω g rest (N + i + 1)))
          ≤ γ ^ (q ^ (N + i)) := by
        intro i
        have h := coeff_mul_le_general (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
          (atLrFoldGen q ω g rest (N + i + 1))
          (a := γ ^ (q ^ (N + i))) (b := 1)
          (fun m => ?_) (fun m => ih hrest (N + i + 1) m) n
        exact le_trans h (le_of_eq (mul_one _))
        rw [frobTwist_coeff, map_pow]
        exact pow_le_pow_left' (hF m) _
      refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
        (summable_of_v_le_gamma_pow (N := N) hγ harch hq hterm) (fun i => ?_)
      refine le_trans (hterm i) ?_
      calc γ ^ (q ^ (N + i)) ≤ γ ^ 1 :=
            pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le
              (Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) _))
        _ = γ := pow_one γ
        _ ≤ 1 := hγ.le

/-- The coefficient of the recursion step of the cutoff `L`-series is a summable family. -/
lemma summable_atLrFoldGen_cons {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    {g : ℕ → PowerSeries K} (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1)
    {s : ℕ} {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (rest : List (ℕ × PowerSeries K))
    (hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2)) (N n : ℕ) :
    Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrFoldGen q ω g rest (N + i + 1)) := by
  refine summable_of_v_le_gamma_pow (N := N) hγ harch hq (fun i => ?_)
  have h := coeff_mul_le_general (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
    (atLrFoldGen q ω g rest (N + i + 1))
    (a := γ ^ (q ^ (N + i))) (b := 1)
    (fun m => ?_) (fun m => coeff_atLrFoldGen_le_one hγ harch hq hω hg rest hrest (N + i + 1) m) n
  exact le_trans h (le_of_eq (mul_one _))
  rw [frobTwist_coeff, map_pow]
  exact pow_le_pow_left' (hF m) _

/-- The cutoff `L`-series of small factors is again a small series. -/
lemma gIsSmall_atLrFoldGen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    {g : ℕ → PowerSeries K} (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) → L ≠ [] → ∀ N,
      GIsSmall γ (atLrFoldGen q ω g L N) := by
  intro L
  induction L with
  | nil => intro _ hne; exact absurd rfl hne
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL _ N n
      have hF : GIsSmall γ (ω ^ s * Q) := hL (s, Q) (by simp)
      rw [atLrFoldGen_cons, PowerSeries.coeff_mk]
      have hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2) := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hterm : ∀ i : ℕ, Valued.v (PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrFoldGen q ω g rest (N + i + 1)))
          ≤ γ ^ (q ^ (N + i)) := by
        intro i
        have h := coeff_mul_le_general (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
          (atLrFoldGen q ω g rest (N + i + 1))
          (a := γ ^ (q ^ (N + i))) (b := 1)
          (fun m => ?_) (fun m => coeff_atLrFoldGen_le_one hγ harch hq hω hg rest hrest (N + i + 1) m) n
        exact le_trans h (le_of_eq (mul_one _))
        rw [frobTwist_coeff, map_pow]
        exact pow_le_pow_left' (hF m) _
      refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
        (summable_of_v_le_gamma_pow (N := N) hγ harch hq hterm) (fun i => ?_)
      exact le_trans (hterm i) (le_trans
        (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le
          (show 1 ≤ q ^ (N + i) from Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) _)))
        (le_of_eq (pow_one γ)))

/-- The constant series `1` has all coefficient valuations `≤ 1`. -/
lemma coeff_one_le_one_general (n : ℕ) :
    Valued.v (PowerSeries.coeff n (1 : PowerSeries K)) ≤ 1 := by
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · rw [map_one]
  · rw [map_zero]; exact zero_le_one' Γ₀

end depth

section cut

variable {γ : Γ₀} {q : ℕ} [FrobPow K q] {ω : PowerSeries K}

lemma coeff_atLrcutGen_le_one (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (N n : ℕ) : Valued.v (PowerSeries.coeff n (atLrcutGen q ω L N)) ≤ 1 :=
  coeff_atLrFoldGen_le_one hγ harch hq hω (g := fun _ => (1 : PowerSeries K))
    (fun _ n => coeff_one_le_one_general n) L hL N n

lemma gIsSmall_atLrcutGen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hne : L ≠ []) (N : ℕ) : GIsSmall γ (atLrcutGen q ω L N) :=
  gIsSmall_atLrFoldGen hγ harch hq hω (g := fun _ => (1 : PowerSeries K))
    (fun _ n => coeff_one_le_one_general n) L hL hne N

/-- The depth-`r` `L`-series of a nonempty list of small factors is small. -/
lemma gIsSmall_atLrGen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hne : L ≠ []) : GIsSmall γ (atLrGen q ω L) := by
  rw [atLrGen]
  exact gIsSmall_atLrcutGen hγ harch hq hω L hL hne 0

/-- **The twist–shift identity of the depth-`r` `L`-series**: `L(N+k) = (L(N))^{(k)}`. -/
theorem frobTwist_atLrcutGen (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) → ∀ (N k : ℕ),
      frobTwist (R := K) (p := q) k (atLrcutGen q ω L N) = atLrcutGen q ω L (N + k) := by
  intro L
  induction L with
  | nil =>
      intro _ N k
      rw [atLrcutGen_nil, atLrcutGen_nil]
      exact frobTwist_one k
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL N k
      have hF : GIsSmall γ (ω ^ s * Q) := hL (s, Q) (by simp)
      have hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2) := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      ext n
      have hsum : Summable fun i : ℕ => PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrcutGen q ω rest (N + i + 1)) :=
        summable_atLrFoldGen_cons hγ harch hq hω (g := fun _ => (1 : PowerSeries K))
          (fun _ n => coeff_one_le_one_general n) (s := s) hF rest hrest N n
      rw [frobTwist_coeff, atLrcutGen_cons, atLrcutGen_cons, PowerSeries.coeff_mk,
        PowerSeries.coeff_mk,
        ZagierHoffmanPositiveChar.tsum_pow_frobPow_general hsum k]
      refine tsum_congr (fun i => ?_)
      rw [← frobTwist_coeff k (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrcutGen q ω rest (N + i + 1)) n, frobTwist_mul, frobTwist_comp,
        ih hrest (N + i + 1) k]
      congr 2 <;> ring_nf

/-- **The `k`-fold decomposition of the `L`-series recursion**:
`L(N) = ∑_{i<k} M^{(N+i)}·L_{rest}(N+i+1) + L(N+k)`. -/
theorem atLrcutGen_fold (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (s : ℕ) {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q))
    (rest : List (ℕ × PowerSeries K)) (hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2)) (N k : ℕ) :
    atLrcutGen q ω ((s, Q) :: rest) N
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
          * atLrcutGen q ω rest (N + i + 1))
        + atLrcutGen q ω ((s, Q) :: rest) (N + k) := by
  ext n
  have hsum : Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrcutGen q ω rest (N + i + 1)) :=
    summable_atLrFoldGen_cons hγ harch hq hω (g := fun _ => (1 : PowerSeries K))
      (fun _ n => coeff_one_le_one_general n) (s := s) hF rest hrest N n
  rw [map_add (PowerSeries.coeff n), map_sum, atLrcutGen_cons, atLrcutGen_cons,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [← Summable.sum_add_tsum_nat_add (f := fun i : ℕ => PowerSeries.coeff n
    (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
      * atLrcutGen q ω rest (N + i + 1))) k hsum]
  congr 1
  refine tsum_congr (fun i => ?_)
  congr 1
  ring_nf

/-- Depth one of the general construction recovers the `L`-series `atL1Gen`. -/
theorem atLrcutGen_singleton (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (s : ℕ) {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (N : ℕ) :
    atLrcutGen q ω [(s, Q)] N = frobTwist (R := K) (p := q) N (atL1Gen q ω s Q) := by
  rw [frobTwist_atL1Gen hγ harch hq s N hF]
  ext n
  rw [atLrcutGen_cons, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine tsum_congr (fun i => ?_)
  rw [atLrcutGen_nil, mul_one]
  congr 2
  ring_nf

/-- The depth-one `L`-series of the general construction is `atL1Gen`. -/
theorem atLrGen_singleton (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (s : ℕ) {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) :
    atLrGen q ω [(s, Q)] = atL1Gen q ω s Q := by
  rw [atLrGen, atLrcutGen_singleton hγ harch hq hω s hF (N := 0), frobTwist_apply]
  ext n
  simp

end cut

section append

/-- **Associativity of the cutoff `L`-series construction** (generic value group). -/
theorem atLrFoldGen_append (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (g : ℕ → PowerSeries K)
    (L1 : List (ℕ × PowerSeries K)) :
    ∀ (L2 : List (ℕ × PowerSeries K)) (N : ℕ),
      atLrFoldGen q ω g (L1 ++ L2) N
        = atLrFoldGen q ω (fun i => atLrFoldGen q ω g L2 i) L1 N := by
  induction L1 with
  | nil => intro L2 N; rw [List.nil_append, atLrFoldGen_nil]
  | cons a L1' ih =>
      obtain ⟨s, Q⟩ := a
      intro L2 N
      rw [List.cons_append, atLrFoldGen_cons, atLrFoldGen_cons]
      congr 1 with n
      refine tsum_congr (fun i => ?_)
      rw [ih]

end append

section paperConvention

/-- Ngo Dac's `𝓛(s;Q)` (generic value group): the paper's order of the factors. -/
noncomputable def atLrPaperGen (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : PowerSeries K :=
  atLrGen q ω L.reverse

/-- The cutoff version of Ngo Dac's `𝓛(s;Q)` (generic value group). -/
noncomputable def atLrcutPaperGen (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (N : ℕ) : PowerSeries K :=
  atLrcutGen q ω L.reverse N

@[simp] lemma atLrPaperGen_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K) :
    atLrPaperGen q ω ([] : List (ℕ × PowerSeries K)) = 1 := rfl

lemma atLrcutPaperGen_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (s : ℕ) (Q : PowerSeries K) (N : ℕ) :
    atLrcutPaperGen q ω (L ++ [(s, Q)]) N
      = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
          PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrcutPaperGen q ω L (N + i + 1))) := by
  rw [atLrcutPaperGen, List.reverse_append, List.reverse_singleton, List.singleton_append,
    atLrcutGen_cons]
  rfl

/-- **The recursion of the paper's `𝓛(s;Q)`** (generic value group), peeling off the last factor. -/
theorem atLrPaperGen_fold {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (s : ℕ)
    {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (N k : ℕ) :
    atLrcutPaperGen q ω (L ++ [(s, Q)]) N
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
          * atLrcutPaperGen q ω L (N + i + 1))
        + atLrcutPaperGen q ω (L ++ [(s, Q)]) (N + k) := by
  rw [atLrcutPaperGen, List.reverse_append, List.reverse_singleton, List.singleton_append,
    atLrcutGen_fold hγ harch hq hω s hF L.reverse
      (fun x hx => hL x (List.mem_reverse.mp hx)) N k]
  simp only [atLrcutPaperGen, List.reverse_append, List.reverse_singleton, List.singleton_append]

lemma frobTwist_atLrcutPaperGen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (N k : ℕ) :
    frobTwist (R := K) (p := q) k (atLrcutPaperGen q ω L N) = atLrcutPaperGen q ω L (N + k) :=
  frobTwist_atLrcutGen hγ harch hq hω L.reverse
    (fun x hx => hL x (List.mem_reverse.mp hx)) N k

lemma gIsSmall_atLrPaperGen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hne : L ≠ []) :
    GIsSmall γ (atLrPaperGen q ω L) :=
  gIsSmall_atLrGen hγ harch hq hω L.reverse
    (fun x hx => hL x (List.mem_reverse.mp hx))
    (fun h => hne (List.reverse_eq_nil_iff.mp h))

/-- The depth-one case of the paper's `𝓛(s;Q)` is Chang's depth-one series. -/
theorem atLrPaperGen_singleton {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q) (hω : GIsSmall γ ω) (s : ℕ)
    {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) :
    atLrPaperGen q ω [(s, Q)] = atL1Gen q ω s Q := by
  rw [atLrPaperGen, List.reverse_singleton]
  exact atLrGen_singleton hγ harch hq hω s hF

end paperConvention

end ZagierHoffmanPositiveChar
