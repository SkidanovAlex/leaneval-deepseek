import Submission.ZagierHoffmanProof.LSeriesFold

/-!
# The depth-`r` `L`-series

This file develops the general depth-`r` `L`-series of Ngo Dac's paper (§2.2.1) (equivalently of
the Anderson–Brownawell–Papanikolas framework; the depth-one case is Chang's series)

  `L(s;Q) = ∑_{i₁ > ⋯ > i_r ≥ 0} (Ω^{s_r}Q_r)^{(i_r)} … (Ω^{s_1}Q_1)^{(i_1)}`,

where `Ω` is the period function, `Q_j` are polynomials and `f^{(i)}` is the coefficientwise
`q^i`-th power twist (our `frobTwist`).  Multiplication of power series is commutative, so only the
*set* of indices matters; we use the "increasing" convention and build the series out of a cutoff
function, which is the form in which the `t`-motive induction operates.

With `M_j = ω^{s_j}Q_j` define the cutoff series

  `atLrFold g L N = ∑_{N ≤ i₁ < ⋯ < i_p} (∏_j M_j^{(i_j)})·g(i_p + 1)`

for a list `L = [(s₁,Q₁),…,(s_p,Q_p)]` and a "tail" series-valued function `g`.  It is characterised
by `atLrFold g [] N = g N` and

  `atLrFold g ((s,Q) :: rest) N = ∑_{i ≥ 0} M^{(N+i)}·atLrFold g rest (N+i+1)`

(the `(N+i)` in the exponent is the cutoff bookkeeping: the first index of the tuple is `≥ N`).
The `L`-series itself is `atLr q ω L = atLrFold (fun _ => 1) L 0`.

## Main definitions and results

* `atLrFold q ω g L N` — the cutoff `L`-series with tail `g`.
* `atLrcut q ω L N`, `atLr q ω L` — the `L`-series with cutoff `N`, and at cutoff `0`.
* `atLrFold_cons` — the recursion.
* `coeff_atLrFold_le_one` — the coefficient bound `v ≤ 1`.
* `isSmall_atLrFold`, `isSmall_atLr` — the series of small factors is small.
* `summable_atLrFold_cons` — the coefficientwise summability of the recursion.
* `frobTwist_atLrcut` — the **twist–shift identity** `L(N+k) = (L(N))^{(k)}`.
* `atLrFold_fold` — the `k`-fold decomposition of the recursion.
* `atLrFold_append` — associativity of the construction (the matrix-product structure).
* `atLrcut_singleton`, `atLr_singleton` — depth one recovers `atL1`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K]

section depth

/-- The cutoff depth-`p` `L`-series attached to the list `L = [(s₁,Q₁),…,(s_p,Q_p)]` and a tail
function `g`.  Semantically
`atLrFold q ω g L N = ∑_{N ≤ i₁ < ⋯ < i_p} (∏_j (ω^{s_j}Q_j)^{(i_j)}) · g (i_p + 1)`. -/
noncomputable def atLrFold (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (g : ℕ → PowerSeries K) :
    List (ℕ × PowerSeries K) → ℕ → PowerSeries K
  | [], N => g N
  | (s, Q) :: rest, N => PowerSeries.mk fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrFold q ω g rest (N + i + 1))

/-- The `L`-series with cutoff `N`: `atLrcut q ω L N = ∑_{N ≤ i₁ < ⋯} ∏_j (ω^{s_j}Q_j)^{(i_j)}`. -/
noncomputable def atLrcut (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (N : ℕ) : PowerSeries K :=
  atLrFold q ω (fun _ => 1) L N

/-- The depth-`p` `L`-series `atLr q ω L = atLrcut q ω L 0`. -/
noncomputable def atLr (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : PowerSeries K :=
  atLrcut q ω L 0

@[simp] lemma atLrFold_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (g : ℕ → PowerSeries K) (N : ℕ) :
    atLrFold q ω g ([] : List (ℕ × PowerSeries K)) N = g N := rfl

@[simp] lemma atLrFold_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (g : ℕ → PowerSeries K) (s : ℕ) (Q : PowerSeries K)
    (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    atLrFold q ω g ((s, Q) :: rest) N = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrFold q ω g rest (N + i + 1))) := rfl

@[simp] lemma atLrcut_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (N : ℕ) :
    atLrcut q ω ([] : List (ℕ × PowerSeries K)) N = 1 := rfl

@[simp] lemma atLrcut_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (s : ℕ)
    (Q : PowerSeries K) (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    atLrcut q ω ((s, Q) :: rest) N = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrcut q ω rest (N + i + 1))) := rfl

lemma atLrcut_zero (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : atLrcut q ω L 0 = atLr q ω L := rfl

/-- A useful summability criterion: a family whose `i`-th term has valuation at most
`exp (-(q^(N+i)))` is summable. -/
lemma summable_of_exp_neg_pow {q : ℕ} (hq : 2 ≤ q) {N : ℕ} {f : ℕ → K}
    (h : ∀ i : ℕ, Valued.v (f i) ≤ WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ))) : Summable f := by
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun m => ?_)
  rw [Filter.eventually_atTop]
  refine ⟨max (m.natAbs + 1) 0, fun i hi => ?_⟩
  refine lt_of_le_of_lt (h i) (WithZero.exp_lt_exp.mpr ?_)
  have hm : (m : ℤ) ≤ (m.natAbs : ℤ) := Int.le_natAbs
  have h2 : (m.natAbs + 1 : ℤ) ≤ (i : ℤ) := by
    have : m.natAbs + 1 ≤ i := le_trans (le_max_left _ _) hi
    exact_mod_cast this
  have h3 : (i : ℤ) ≤ ((q ^ (N + i) : ℕ) : ℤ) := by
    have h1 : N + i < q ^ (N + i) := Nat.lt_pow_self (by omega : 1 < q)
    have h2' : (N + i : ℕ) ≤ ((q ^ (N + i) : ℕ)) := le_of_lt h1
    have : (i : ℤ) ≤ ((N + i : ℕ) : ℤ) := by omega
    exact le_trans this (by exact_mod_cast h2')
  omega

/-- The coefficient of a product of power series is bounded by the product of any uniform bounds
on the coefficients of the factors. -/
lemma coeff_mul_le (f g : PowerSeries K) {a b : ℤᵐ⁰}
    (hf : ∀ m : ℕ, Valued.v (PowerSeries.coeff m f) ≤ a)
    (hg : ∀ m : ℕ, Valued.v (PowerSeries.coeff m g) ≤ b) (n : ℕ) :
    Valued.v (PowerSeries.coeff n (f * g)) ≤ a * b := by
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p _ => ?_)
  rw [map_mul]
  exact mul_le_mul' (hf p.1) (hg p.2)

/-- The coefficient valuations of the cutoff `L`-series are bounded by `1`, as long as the tail
function has this bound and all factors are small. -/
lemma coeff_atLrFold_le_one {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K}
    (hω : IsSmall ω) {g : ℕ → PowerSeries K}
    (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, IsSmall x.2) → ∀ N n,
      Valued.v (PowerSeries.coeff n (atLrFold q ω g L N)) ≤ 1 := by
  intro L
  induction L with
  | nil => intro _ N n; rw [atLrFold_nil]; exact hg N n
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL N n
      have hQ : IsSmall Q := hL (s, Q) (by simp)
      rw [atLrFold_cons, PowerSeries.coeff_mk]
      have hrest : ∀ x ∈ rest, IsSmall x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hterm : ∀ i : ℕ, Valued.v (PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrFold q ω g rest (N + i + 1)))
          ≤ WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) := by
        intro i
        have h := coeff_mul_le (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
          (atLrFold q ω g rest (N + i + 1))
          (a := WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ))) (b := 1)
          (fun m => ?_) (fun m => ih hrest (N + i + 1) m) n
        exact le_trans h (le_of_eq (mul_one _))
        rw [frobTwist_coeff, map_pow]
        calc (Valued.v (PowerSeries.coeff m (ω ^ s * Q))) ^ (q ^ (N + i))
            ≤ (WithZero.exp (-1)) ^ (q ^ (N + i)) := pow_le_pow_left' (IsSmall.pow_mul hω hQ s m) _
          _ = WithZero.exp (-1 * (((q ^ (N + i) : ℕ)) : ℤ)) := expmul (-1) (q ^ (N + i))
          _ = WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) := by rw [neg_one_mul]
      refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
        (summable_of_exp_neg_pow (N := N) hq hterm) (fun i => ?_)
      refine le_trans (hterm i) ?_
      rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm]
      apply WithZero.exp_le_exp.mpr
      have h1 : 1 ≤ q ^ (N + i) := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) _)
      have h2 : (1 : ℤ) ≤ ((q ^ (N + i) : ℕ) : ℤ) := by exact_mod_cast h1
      omega

/-- The coefficient of the recursion step of the cutoff `L`-series is a summable family: the `i`-th
term has valuation at most `exp (-(q^(N+i)))`. -/
lemma summable_atLrFold_cons {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K}
    (hω : IsSmall ω) {g : ℕ → PowerSeries K}
    (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1)
    {s : ℕ} {Q : PowerSeries K} (hQ : IsSmall Q) (rest : List (ℕ × PowerSeries K))
    (hrest : ∀ x ∈ rest, IsSmall x.2) (N n : ℕ) :
    Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q) * atLrFold q ω g rest (N + i + 1)) := by
  refine summable_of_exp_neg_pow (N := N) hq (fun i => ?_)
  have h := coeff_mul_le (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
    (atLrFold q ω g rest (N + i + 1))
    (a := WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ))) (b := 1)
    (fun m => ?_) (fun m => coeff_atLrFold_le_one hq hω hg rest hrest (N + i + 1) m) n
  exact le_trans h (le_of_eq (mul_one _))
  rw [frobTwist_coeff, map_pow]
  calc (Valued.v (PowerSeries.coeff m (ω ^ s * Q))) ^ (q ^ (N + i))
      ≤ (WithZero.exp (-1)) ^ (q ^ (N + i)) := pow_le_pow_left' (IsSmall.pow_mul hω hQ s m) _
    _ = WithZero.exp (-1 * (((q ^ (N + i) : ℕ)) : ℤ)) := expmul (-1) (q ^ (N + i))
    _ = WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) := by rw [neg_one_mul]

/-- The cutoff `L`-series of small factors is again a small series. -/
lemma isSmall_atLrFold {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K}
    (hω : IsSmall ω) {g : ℕ → PowerSeries K}
    (hg : ∀ j n, Valued.v (PowerSeries.coeff n (g j)) ≤ 1) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, IsSmall x.2) → L ≠ [] → ∀ N,
      IsSmall (atLrFold q ω g L N) := by
  intro L
  induction L with
  | nil => intro _ hne; exact absurd rfl hne
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL _ N n
      have hQ : IsSmall Q := hL (s, Q) (by simp)
      rw [atLrFold_cons, PowerSeries.coeff_mk]
      have hrest : ∀ x ∈ rest, IsSmall x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hterm : ∀ i : ℕ, Valued.v (PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrFold q ω g rest (N + i + 1)))
          ≤ WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) := by
        intro i
        have h := coeff_mul_le (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q))
          (atLrFold q ω g rest (N + i + 1))
          (a := WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ))) (b := 1)
          (fun m => ?_) (fun m => coeff_atLrFold_le_one hq hω hg rest hrest (N + i + 1) m) n
        exact le_trans h (le_of_eq (mul_one _))
        rw [frobTwist_coeff, map_pow]
        calc (Valued.v (PowerSeries.coeff m (ω ^ s * Q))) ^ (q ^ (N + i))
            ≤ (WithZero.exp (-1)) ^ (q ^ (N + i)) := pow_le_pow_left' (IsSmall.pow_mul hω hQ s m) _
          _ = WithZero.exp (-1 * (((q ^ (N + i) : ℕ)) : ℤ)) := expmul (-1) (q ^ (N + i))
          _ = WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) := by rw [neg_one_mul]
      refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
        (summable_of_exp_neg_pow (N := N) hq hterm) (fun i => ?_)
      refine le_trans (hterm i) ?_
      apply WithZero.exp_le_exp.mpr
      have h1 : 1 ≤ q ^ (N + i) := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) _)
      have h2 : (1 : ℤ) ≤ ((q ^ (N + i) : ℕ) : ℤ) := by exact_mod_cast h1
      omega

/-- The constant series `1` has all coefficient valuations `≤ 1`. -/
lemma coeff_one_le_one (n : ℕ) :
    Valued.v (PowerSeries.coeff n (1 : PowerSeries K)) ≤ 1 := by
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · rw [map_one]
  · rw [map_zero]; exact bot_le

end depth

section cut

variable (q : ℕ) [FrobPow K q] (ω : PowerSeries K)

lemma coeff_atLrcut_le_one (hq : 2 ≤ q) (hω : IsSmall ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2) (N n : ℕ) :
    Valued.v (PowerSeries.coeff n (atLrcut q ω L N)) ≤ 1 :=
  coeff_atLrFold_le_one hq hω (g := fun _ => (1 : PowerSeries K))
    (fun _ n => coeff_one_le_one n) L hL N n

lemma isSmall_atLrcut (hq : 2 ≤ q) (hω : IsSmall ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2) (hne : L ≠ []) (N : ℕ) :
    IsSmall (atLrcut q ω L N) :=
  isSmall_atLrFold hq hω (g := fun _ => (1 : PowerSeries K))
    (fun _ n => coeff_one_le_one n) L hL hne N

/-- The depth-`r` `L`-series of a nonempty list of small factors is small. -/
lemma isSmall_atLr (hq : 2 ≤ q) (hω : IsSmall ω)
    (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2) (hne : L ≠ []) :
    IsSmall (atLr q ω L) := by
  rw [atLr]
  exact isSmall_atLrcut q ω hq hω L hL hne 0

/-- **The twist–shift identity of the depth-`r` `L`-series**: raising the cutoff by `k` is the same
as applying the `k`-th Frobenius twist to the series, i.e. `L(N+k) = (L(N))^{(k)}`. -/
theorem frobTwist_atLrcut (hq : 2 ≤ q) (hω : IsSmall ω) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, IsSmall x.2) → ∀ (N k : ℕ),
      frobTwist (R := K) (p := q) k (atLrcut q ω L N) = atLrcut q ω L (N + k) := by
  intro L
  induction L with
  | nil =>
      intro _ N k
      rw [atLrcut_nil, atLrcut_nil]
      exact frobTwist_one k
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro hL N k
      have hQ : IsSmall Q := hL (s, Q) (by simp)
      have hrest : ∀ x ∈ rest, IsSmall x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      ext n
      have hsum : Summable fun i : ℕ => PowerSeries.coeff n
          (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q) * atLrcut q ω rest (N + i + 1)) :=
        summable_atLrFold_cons (q := q) hq hω (g := fun _ => (1 : PowerSeries K))
          (fun _ n => coeff_one_le_one n) (s := s) hQ rest hrest N n
      rw [frobTwist_coeff, atLrcut_cons, atLrcut_cons, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        ZagierHoffmanPositiveChar.tsum_pow_frobPow hsum k]
      refine tsum_congr (fun i => ?_)
      rw [← frobTwist_coeff k (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
        * atLrcut q ω rest (N + i + 1)) n, frobTwist_mul, frobTwist_comp, ih hrest (N + i + 1) k]
      congr 2 <;> ring_nf

/-- **The `k`-fold decomposition of the `L`-series recursion**:
`L(N) = ∑_{i<k} M^{(N+i)}·L_{rest}(N+i+1) + L(N+k)`. -/
theorem atLrcut_fold (hq : 2 ≤ q) (hω : IsSmall ω) (s : ℕ) {Q : PowerSeries K} (hQ : IsSmall Q)
    (rest : List (ℕ × PowerSeries K)) (hrest : ∀ x ∈ rest, IsSmall x.2) (N k : ℕ) :
    atLrcut q ω ((s, Q) :: rest) N
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
          * atLrcut q ω rest (N + i + 1))
        + atLrcut q ω ((s, Q) :: rest) (N + k) := by
  ext n
  have hsum : Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q) * atLrcut q ω rest (N + i + 1)) :=
    summable_atLrFold_cons (q := q) hq hω (g := fun _ => (1 : PowerSeries K))
      (fun _ n => coeff_one_le_one n) (s := s) hQ rest hrest N n
  rw [map_add (PowerSeries.coeff n), map_sum, atLrcut_cons, atLrcut_cons, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  rw [← Summable.sum_add_tsum_nat_add (f := fun i : ℕ => PowerSeries.coeff n
    (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q) * atLrcut q ω rest (N + i + 1))) k hsum]
  congr 1
  refine tsum_congr (fun i => ?_)
  congr 1
  ring_nf

/-- Depth one of the general construction recovers the `L`-series `atL1`. -/
theorem atLrcut_singleton (hq : 2 ≤ q) (hω : IsSmall ω) (s : ℕ) {Q : PowerSeries K}
    (hQ : IsSmall Q) (N : ℕ) :
    atLrcut q ω [(s, Q)] N = frobTwist (R := K) (p := q) N (atL1 q ω s Q) := by
  rw [frobTwist_atL1 hq hω hQ s N]
  ext n
  rw [atLrcut_cons, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine tsum_congr (fun i => ?_)
  rw [atLrcut_nil, mul_one]
  congr 2
  ring_nf

/-- The depth-one `L`-series of the general construction is `atL1`. -/
theorem atLr_singleton (hq : 2 ≤ q) (hω : IsSmall ω) (s : ℕ) {Q : PowerSeries K}
    (hQ : IsSmall Q) : atLr q ω [(s, Q)] = atL1 q ω s Q := by
  rw [atLr, atLrcut_singleton (q := q) (ω := ω) (hq := hq) (hω := hω) (s := s) (hQ := hQ)
    (N := 0), frobTwist_apply]
  ext n
  simp

end cut

section append

/-- **Associativity of the cutoff `L`-series construction**: concatenating two blocks is the same
as replacing the tail of the first by the second (the matrix-product structure of the
rigid analytic trivialisation). -/
theorem atLrFold_append (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (g : ℕ → PowerSeries K)
    (L1 : List (ℕ × PowerSeries K)) :
    ∀ (L2 : List (ℕ × PowerSeries K)) (N : ℕ),
      atLrFold q ω g (L1 ++ L2) N
        = atLrFold q ω (fun i => atLrFold q ω g L2 i) L1 N := by
  induction L1 with
  | nil => intro L2 N; rw [List.nil_append, atLrFold_nil]
  | cons a L1' ih =>
      obtain ⟨s, Q⟩ := a
      intro L2 N
      rw [List.cons_append, atLrFold_cons, atLrFold_cons]
      congr 1 with n
      refine tsum_congr (fun i => ?_)
      rw [ih]

end append

section paperConvention

/-! ### The paper's convention

Ngo Dac (and Anderson–Brownawell–Papanikolas / Chang) order the index tuple *decreasingly* and
attach the largest index to `Q₁`:

  `𝓛(s;Q) = ∑_{i₁ > ⋯ > i_r ≥ 0} (Ω^{s_r}Q_r)^{(i_r)} ⋯ (Ω^{s_1}Q_1)^{(i_1)}`.

Because power series commute, this is the same as summing over *increasing* tuples with `Q₁` getting
the smallest index, i.e. it is our `atLr` applied to the **reversed** list.  We record this
convention explicitly (it is the one in which the entries of the trivialisation matrix `Ψ` are
organised, with the recursion peeling off the *last* tuple element). -/

/-- Ngo Dac's `𝓛(s;Q)`: the list of factors is read in the paper's order, i.e. the *first* pair of
the list carries the *largest* index. -/
noncomputable def atLrPaper (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) : PowerSeries K :=
  atLr q ω L.reverse

/-- The cutoff version of Ngo Dac's `𝓛(s;Q)`. -/
noncomputable def atLrcutPaper (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (N : ℕ) : PowerSeries K :=
  atLrcut q ω L.reverse N

@[simp] lemma atLrPaper_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K) :
    atLrPaper q ω ([] : List (ℕ × PowerSeries K)) = 1 := rfl

lemma atLrcutPaper_cons (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (s : ℕ) (Q : PowerSeries K) (N : ℕ) :
    atLrcutPaper q ω (L ++ [(s, Q)]) N
      = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
          PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
            * atLrcutPaper q ω L (N + i + 1))) := by
  rw [atLrcutPaper, List.reverse_append, List.reverse_singleton, List.singleton_append,
    atLrcut_cons]
  rfl

/-- **The recursion of the paper's `𝓛(s;Q)`**, peeling off the last factor: the series attached to
the tuple `(L, (s,Q))` is the last factor plus the `(1)`-twist of the whole series, times the
series of the initial segment.  This is the entry-wise form of the rigid analytic trivialisation
`Ψ = ΦΨ⁻¹` (equivalently `Ψ^{(-1)} = ΦΨ`). -/
theorem atLrPaper_fold (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q)
    (hω : IsSmall ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, IsSmall x.2) (s : ℕ) {Q : PowerSeries K} (hQ : IsSmall Q) (N k : ℕ) :
    atLrcutPaper q ω (L ++ [(s, Q)]) N
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
          * atLrcutPaper q ω L (N + i + 1))
        + atLrcutPaper q ω (L ++ [(s, Q)]) (N + k) := by
  rw [atLrcutPaper, List.reverse_append, List.reverse_singleton, List.singleton_append,
    atLrcut_fold (q := q) (ω := ω) hq hω s hQ L.reverse (fun x hx => hL x (List.mem_reverse.mp hx)) N k]
  simp only [atLrcutPaper, List.reverse_append, List.reverse_singleton, List.singleton_append]

lemma frobTwist_atLrcutPaper (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q)
    (hω : IsSmall ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, IsSmall x.2) (N k : ℕ) :
    frobTwist (R := K) (p := q) k (atLrcutPaper q ω L N) = atLrcutPaper q ω L (N + k) :=
  frobTwist_atLrcut (q := q) (ω := ω) hq hω L.reverse (fun x hx => hL x (List.mem_reverse.mp hx)) N k

lemma isSmall_atLrPaper (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q)
    (hω : IsSmall ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, IsSmall x.2) (hne : L ≠ []) : IsSmall (atLrPaper q ω L) :=
  isSmall_atLr (q := q) (ω := ω) hq hω L.reverse (fun x hx => hL x (List.mem_reverse.mp hx))
    (fun h => hne (List.reverse_eq_nil_iff.mp h))

/-- The depth-one case of the paper's `𝓛(s;Q)` is Chang's depth-one series. -/
theorem atLrPaper_singleton (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (hq : 2 ≤ q)
    (hω : IsSmall ω) (s : ℕ) {Q : PowerSeries K}
    (hQ : IsSmall Q) : atLrPaper q ω [(s, Q)] = atL1 q ω s Q := by
  rw [atLrPaper, List.reverse_singleton]
  exact atLr_singleton (q := q) (ω := ω) hq hω s hQ

end paperConvention

end ZagierHoffmanPositiveChar
