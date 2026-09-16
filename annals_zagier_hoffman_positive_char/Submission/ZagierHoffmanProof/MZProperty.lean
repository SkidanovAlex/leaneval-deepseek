import Submission.ZagierHoffmanProof.EvalEntire
import Submission.ZagierHoffmanProof.SuperLSeries
import Submission.ZagierHoffmanProof.SuperOmega
import Submission.ZagierHoffmanProof.OmegaD
import Submission.ZagierHoffmanProof.PeriodDatum

/-!
# Chang's MZ property of the `L`-series

Chang's series `𝓛(𝔰;Q)` (the entries of the rigid analytic trivialisation `Ψ` of the MZV dual
`t`-motive) satisfy the **MZ property**

  `𝓛(𝔰;Q)(θ^{q^j}) = (𝓛(𝓼;Q)(θ))^{q^j}`  for all `j ≥ 0`

(Chang, *Linear independence of monomials of multizeta values*, Lemma 5.3.5; also
Anderson–Brownawell–Papanikolas / CPY19 Prop. 2.3.3).  This is one of the two inputs of the
transcendental step of Ngo Dac's proof of Theorems B/D (the other being the ABP criterion itself):
it is used to specialise a `K̄(t)`-linear relation between `L`-series at the points `t = θ^{q^j}`
and read it as a `K̄`-linear relation between the values at `θ`, which the induction then kills.

The proof is entirely elementary once one has (a) multiplicativity of the evaluation map on `ε`
(`evalSeries_mul`) and (b) the **vanishing of the period function at its Frobenius orbit**
`Ω(θ^{q^k}) = 0` for `k ≥ 1`.  Indeed, the fold of the `L`-series

  `𝓛 = ∑_{i < j} (ω^sQ)^{(i)}·𝓛_rest(i+1) + 𝓛^{(j)}`

splits the value at `c^{q^j}` into the finitely many *low* terms — each of which contains the
factor `ω^s` evaluated at `c^{q^{j-i}}` with `j - i ≥ 1`, hence vanishes — and the `j`-fold twist
`𝓛^{(j)}`, whose value at `c^{q^j}` is `(𝓛(c))^{q^j}` by `evalSeries_frobTwist`.

## Main results

* `evalSeries_one_sub_C_mul_X` — evaluation of the partial-product factors.
* ★★★ `evalSeries_atOmega_frobenius_orbit` — `Ω(θ^{q^k}) = 0` for `k ≥ 1` (the "simple zero at
  `t = θ^{q^k}`" of the paper), and its normalised version
  `evalSeries_C_mul_atOmega_frobenius_orbit`.
* ★★★ `evalSeries_atLrcutPaper_frobenius_pow` — the MZ property for `𝓛` with a general small
  vanishing `ω` and a general vanishing point `c`.
* ★★★ `evalSeries_atL1_frobenius_pow` — the depth-one case (Chang's original series).
* ★★★ `evalSeries_atLrPaper_period_pow`, `evalSeries_atL1_period_pow` — the MZ property for the
  Anderson–Thakur period datum `Ω = μ·Ω̃`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Evaluation of one factor `1 - a t` of the partial products of the period function. -/
lemma evalSeries_one_sub_C_mul_X (a c : K) :
    evalSeries (1 - PowerSeries.C a * PowerSeries.X) c = 1 - a * c := by
  rw [evalSeries_sub SuperEntire.one ((SuperEntire.C a).mul SuperEntire.X) c,
    evalSeries_one, evalSeries_C_mul, evalSeries_X]

variable (q : ℕ) [FrobPow K q]

/-- **The period function vanishes at the Frobenius orbit of `θ`**: `Ω(θ^{q^k}) = 0` for `k ≥ 1`.

This is the formal version of the paper's observation that "the function `Ω` has a simple zero at
`t = θ^{q^k}` for `k ∈ ℕ`": the factor `i = k` of the telescoping identity
`Ω = (∏_{i ≤ k}(1 - t/θ^{q^i}))·Ω^{(k)}` vanishes at `t = θ^{q^k}`, and the second factor is
evaluated by the Frobenius-twist rule at `θ`. -/
theorem evalSeries_atOmega_frobenius_orbit (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    evalSeries (atOmega q θ) (θ ^ (q ^ k)) = 0 := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, map_zero] at hθ
    exact absurd hθ.symm (WithZero.exp_ne_zero)
  have hse : SuperEntire (atOmega q θ) := superEntire_atOmega q θ d hd hθ hq
  have hpart : SuperEntire (omPartial q θ k) := by
    rw [omPartial]
    refine SuperEntire.prod _ _ fun i _ => ?_
    exact SuperEntire.one.sub ((SuperEntire.C _).mul SuperEntire.X)
  have htw : SuperEntire (frobTwist (R := K) (p := q) k (atOmega q θ)) := hse.frobTwist k
  have hzero : evalSeries (omPartial q θ k) (θ ^ (q ^ k)) = 0 := by
    rw [omPartial]
    rw [evalSeries_prod _ _ (fun i _ =>
      SuperEntire.one.sub ((SuperEntire.C _).mul SuperEntire.X)) (θ ^ (q ^ k))]
    have hmem : k - 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    refine Finset.prod_eq_zero hmem ?_
    rw [evalSeries_one_sub_C_mul_X, omX]
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1, inv_mul_cancel₀ (pow_ne_zero _ hθ0), sub_self]
  rw [atOmega_eq_omPartial_mul_frobTwist_d q θ d hd hθ hq k, evalSeries_mul hpart htw,
    hzero, zero_mul]

/-- **The normalised period function `μ·Ω` vanishes at the Frobenius orbit of `θ`.** -/
theorem evalSeries_C_mul_atOmega_frobenius_orbit (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) (μ : K) {k : ℕ} (hk : 1 ≤ k) :
    evalSeries (PowerSeries.C μ * atOmega q θ) (θ ^ (q ^ k)) = 0 := by
  rw [evalSeries_C_mul, evalSeries_atOmega_frobenius_orbit q θ d hd hθ hq hk, mul_zero]

/-- **The MZ property of the `L`-series** (general depth): if the small series `ω` vanishes at the
Frobenius orbit of `c` (`ω(c^{q^k}) = 0` for `k ≥ 1`), then the `L`-series attached to
`(L, (s,Q))` satisfies `𝓛(c^{q^j}) = (𝓛(c))^{q^j}` for all `j`. -/
theorem evalSeries_atLrcutPaper_frobenius_pow (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2)
    (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K}
    (hQ : IsSmall Q) (hQse : SuperEntire Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeries (atLrcutPaper q ω (L ++ [(s, Q)]) 0) (c ^ (q ^ j))
      = (evalSeries (atLrcutPaper q ω (L ++ [(s, Q)]) 0) c) ^ (q ^ j) := by
  have hLrev : ∀ x ∈ L.reverse, IsSmall x.2 := fun x hx => hL x (List.mem_reverse.mp hx)
  have hLserev : ∀ x ∈ L.reverse, SuperEntire x.2 := fun x hx => hLse x (List.mem_reverse.mp hx)
  have hseRest : ∀ N, SuperEntire (atLrcutPaper q ω L N) := fun N =>
    superEntire_atLrcut q hq hω hωse hLrev hLserev N
  have hseSelf : SuperEntire (atLrcutPaper q ω (L ++ [(s, Q)]) 0) := by
    rw [atLrcutPaper, List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine superEntire_atLrcut q hq hω hωse ?_ ?_ 0
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hQ
      · exact hLrev x h
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hQse
      · exact hLserev x h
  have hGse : SuperEntire (ω ^ s * Q) := (hωse.pow s).mul hQse
  have hfold : atLrcutPaper q ω (L ++ [(s, Q)]) 0
      = (∑ i ∈ Finset.range j, frobTwist (R := K) (p := q) i (ω ^ s * Q)
          * atLrcutPaper q ω L (i + 1))
        + frobTwist (R := K) (p := q) j (atLrcutPaper q ω (L ++ [(s, Q)]) 0) := by
    have hLs : ∀ x ∈ L ++ [(s, Q)], IsSmall x.2 := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hL x h
      · simp only [List.mem_singleton] at h; rw [h]; exact hQ
    have h := atLrPaper_fold q ω hq hω L hL s hQ 0 j
    rw [← frobTwist_atLrcutPaper q ω hq hω (L ++ [(s, Q)]) hLs 0 j] at h
    simpa using h
  conv_lhs => rw [hfold]
  have hsumSE : SuperEntire (∑ i ∈ Finset.range j, frobTwist (R := K) (p := q) i (ω ^ s * Q)
      * atLrcutPaper q ω L (i + 1)) :=
    SuperEntire.sum _ _ (fun i _ => (hGse.frobTwist i).mul (hseRest (i + 1)))
  rw [evalSeries_add hsumSE (hseSelf.frobTwist j) (c ^ (q ^ j)),
    evalSeries_finset_sum _ _ (fun i _ => (hGse.frobTwist i).mul (hseRest (i + 1))) (c ^ (q ^ j)),
    evalSeries_frobTwist q hseSelf c j]
  have hzero : ∀ i ∈ Finset.range j,
      evalSeries (frobTwist (R := K) (p := q) i (ω ^ s * Q) * atLrcutPaper q ω L (i + 1))
        (c ^ (q ^ j)) = 0 := by
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    have hji : 1 ≤ j - i := by omega
    have hpow : c ^ (q ^ j) = (c ^ (q ^ (j - i))) ^ (q ^ i) := by
      rw [← pow_mul]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    rw [evalSeries_mul (hGse.frobTwist i) (hseRest (i + 1)) (c ^ (q ^ j)), hpow,
      evalSeries_frobTwist q hGse (c ^ (q ^ (j - i))) i,
      evalSeries_mul (hωse.pow s) hQse (c ^ (q ^ (j - i))),
      evalSeries_pow hωse s (c ^ (q ^ (j - i))), hc (j - i) hji]
    have h1 : (0 : K) ^ s = 0 := zero_pow (by omega : s ≠ 0)
    have h2 : (0 : K) ^ (q ^ i) = 0 := zero_pow (pow_ne_zero i (by omega : q ≠ 0))
    rw [h1, zero_mul, h2, zero_mul]
  rw [Finset.sum_eq_zero hzero, zero_add]

/-- **Chang's MZ property** for the depth-one `L`-series `𝓛(s;Q) = ∑_{i ≥ 0}(ω^sQ)^{(i)}`. -/
theorem evalSeries_atL1_frobenius_pow (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K} (hQ : IsSmall Q)
    (hQse : SuperEntire Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeries (atL1 q ω s Q) (c ^ (q ^ j)) = (evalSeries (atL1 q ω s Q) c) ^ (q ^ j) := by
  have h := evalSeries_atLrcutPaper_frobenius_pow (K := K) q hq hω hωse
    ([] : List (ℕ × PowerSeries K)) (by simp) (by simp) s hs hQ hQse hc j
  have e1 : atLrcutPaper q ω [(s, Q)] 0 = atL1 q ω s Q := by
    change atLrcut q ω ([(s, Q)] : List (ℕ × PowerSeries K)).reverse 0 = atL1 q ω s Q
    rw [List.reverse_singleton]
    exact atLr_singleton (q := q) (ω := ω) hq hω s hQ
  simp only [List.nil_append] at h
  rw [e1] at h
  exact h

/-- **The MZ property for the Anderson–Thakur period function**: for the period datum
`Ω = μ·Ω̃` (with `v μ ≤ exp (-1)`) the `L`-series in the paper's ordering convention satisfies
`𝓛(θ^{q^j}) = (𝓛(θ))^{q^j}`. -/
theorem evalSeries_atLrPaper_period_pow (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) {μ : K}
    (hμ : Valued.v μ ≤ WithZero.exp (-1)) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) (hs : 1 ≤ s)
    {Q : PowerSeries K} (hQ : IsSmall Q) (hQse : SuperEntire Q) (j : ℕ) :
    evalSeries (atLrPaper q (PowerSeries.C μ * atOmega q θ) (L ++ [(s, Q)])) (θ ^ (q ^ j))
      = (evalSeries (atLrPaper q (PowerSeries.C μ * atOmega q θ) (L ++ [(s, Q)])) θ) ^ (q ^ j) :=
  evalSeries_atLrcutPaper_frobenius_pow (K := K) q hq (isSmall_periodDatum q θ d hd hθ hq hμ)
    ((SuperEntire.C μ).mul (superEntire_atOmega q θ d hd hθ hq)) L hL hLse s hs hQ hQse
    (fun _ hk => evalSeries_C_mul_atOmega_frobenius_orbit q θ d hd hθ hq μ hk) j

/-- **The MZ property in the paper's ordering convention** (general small vanishing `ω`). -/
theorem evalSeries_atLrPaper_frobenius_pow (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2)
    (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K}
    (hQ : IsSmall Q) (hQse : SuperEntire Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeries (atLrPaper q ω (L ++ [(s, Q)])) (c ^ (q ^ j))
      = (evalSeries (atLrPaper q ω (L ++ [(s, Q)])) c) ^ (q ^ j) :=
  evalSeries_atLrcutPaper_frobenius_pow (K := K) q hq hω hωse L hL hLse s hs hQ hQse hc j

/-- **The MZ property for an arbitrary non-empty tuple** (the form used in the proof of Theorems
B/D, where the tuples of paper's set `I` are arbitrary prefixes).  Only the *last* entry of the
list (the one carrying the smallest index) needs a positive depth. -/
theorem evalSeries_atLrPaper_frobenius_pow_of_ne (hq : 2 ≤ q) {ω : PowerSeries K}
    (hω : IsSmall ω) (hωse : SuperEntire ω) {L : List (ℕ × PowerSeries K)} (hne : L ≠ [])
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2)
    (hs : 1 ≤ (L.getLast hne).1) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeries (atLrPaper q ω L) (c ^ (q ^ j)) = (evalSeries (atLrPaper q ω L) c) ^ (q ^ j) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  refine evalSeries_atLrPaper_frobenius_pow (K := K) q hq hω hωse L.dropLast ?_ ?_
    (L.getLast hne).1 hs ?_ ?_ hc j
  · intro x hx
    exact hL x (List.mem_of_mem_dropLast hx)
  · intro x hx
    exact hLse x (List.mem_of_mem_dropLast hx)
  · exact hL _ (List.getLast_mem hne)
  · exact hLse _ (List.getLast_mem hne)

/-- The `L`-series does not vanish at `θ^{q^j}` as soon as it does not vanish at `θ`
(this is the form in which the paper uses the MZ property: "`𝓛(𝔱;Q)(θ^{q^j})` is nonzero"). -/
theorem evalSeries_atLrPaper_ne_zero_pow (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) (L : List (ℕ × PowerSeries K)) (hL : ∀ x ∈ L, IsSmall x.2)
    (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K}
    (hQ : IsSmall Q) (hQse : SuperEntire Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0) (j : ℕ)
    (h : evalSeries (atLrPaper q ω (L ++ [(s, Q)])) c ≠ 0) :
    evalSeries (atLrPaper q ω (L ++ [(s, Q)])) (c ^ (q ^ j)) ≠ 0 := by
  rw [evalSeries_atLrPaper_frobenius_pow (K := K) q hq hω hωse L hL hLse s hs hQ hQse hc j]
  exact pow_ne_zero _ h

/-- The depth-one case of the MZ property for the period datum. -/
theorem evalSeries_atL1_period_pow (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) {μ : K}
    (hμ : Valued.v μ ≤ WithZero.exp (-1)) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K}
    (hQ : IsSmall Q) (hQse : SuperEntire Q) (j : ℕ) :
    evalSeries (atL1 q (PowerSeries.C μ * atOmega q θ) s Q) (θ ^ (q ^ j))
      = (evalSeries (atL1 q (PowerSeries.C μ * atOmega q θ) s Q) θ) ^ (q ^ j) :=
  evalSeries_atL1_frobenius_pow (K := K) q hq (isSmall_periodDatum q θ d hd hθ hq hμ)
    ((SuperEntire.C μ).mul (superEntire_atOmega q θ d hd hθ hq)) s hs hQ hQse
    (fun _ hk => evalSeries_C_mul_atOmega_frobenius_orbit q θ d hd hθ hq μ hk) j

end ZagierHoffmanPositiveChar
