import Submission.ZagierHoffmanProof.GenSuperLSeries

/-!
# Chang's MZ property over an arbitrary value group

Generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `MZProperty.lean`: if the small
super-entire series `ω` vanishes at the Frobenius orbit of the point `c` (`ω(c^(q^k)) = 0` for
`k ≥ 1`), then the `L`-series attached to any tuple satisfies the **MZ property**

  `𝓛(c^(q^j)) = (𝓛(c))^(q^j)`   for all `j ≥ 0`

(Chang, *Linear independence of monomials of multizeta values*, Lemma 5.3.5; also
Anderson–Brownawell–Papanikolas / CPY19 Prop. 2.3.3).

The instantiation `ω = μ·Ω̃`, `c = θ` (the Anderson–Thakur period datum) is proved separately
(`GenPeriodDatum`/`GenOmega`); here we prove the statement in the abstract form in which the
specialisation step of the paper uses it.

## Main results

* `evalSeriesGen_one_sub_C_mul_X` — evaluation of a partial-product factor.
* ★★★ `evalSeriesGen_atLrcutPaperGen_frobenius_pow` — the MZ property (general depth and cutoff).
* ★★★ `evalSeriesGen_atL1Gen_frobenius_pow` — the depth-one case (Chang's original series).
* ★★ `evalSeriesGen_atLrPaperGen_frobenius_pow_of_ne` — arbitrary non-empty tuples.
* ★★ `evalSeriesGen_atLrPaperGen_ne_zero_pow` — the non-vanishing form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Evaluation of one factor `1 - a t` of the partial products of the period function. -/
lemma evalSeriesGen_one_sub_C_mul_X {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (a c : K) :
    evalSeriesGen (1 - PowerSeries.C a * PowerSeries.X) c = 1 - a * c := by
  rw [evalSeriesGen_sub hγ harch (GSuperEntire.one γ)
      ((GSuperEntire.C γ a).mul hγ.le (GSuperEntire.X hγ0)) c,
    evalSeriesGen_one, evalSeriesGen_C_mul, evalSeriesGen_X]

variable (q : ℕ) [FrobPow K q]

/-- **The MZ property of the `L`-series** (general depth, generic value group). -/
theorem evalSeriesGen_atLrcutPaperGen_frobenius_pow {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (s : ℕ) (hs : 1 ≤ s)
    {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (hQse : GSuperEntire γ Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeriesGen (atLrcutPaperGen q ω (L ++ [(s, Q)]) 0) (c ^ (q ^ j))
      = (evalSeriesGen (atLrcutPaperGen q ω (L ++ [(s, Q)]) 0) c) ^ (q ^ j) := by
  have hLrev : ∀ x ∈ L.reverse, GIsSmall γ (ω ^ x.1 * x.2) :=
    fun x hx => hL x (List.mem_reverse.mp hx)
  have hLserev : ∀ x ∈ L.reverse, GSuperEntire γ x.2 :=
    fun x hx => hLse x (List.mem_reverse.mp hx)
  have hseRest : ∀ N, GSuperEntire γ (atLrcutPaperGen q ω L N) := fun N =>
    gSuperEntire_atLrcut hγ harch hq hω hωse hLrev hLserev N
  have hseSelf : GSuperEntire γ (atLrcutPaperGen q ω (L ++ [(s, Q)]) 0) := by
    rw [atLrcutPaperGen, List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine gSuperEntire_atLrcut hγ harch hq hω hωse ?_ ?_ 0
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hF
      · exact hLrev x h
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hQse
      · exact hLserev x h
  have hGse : GSuperEntire γ (ω ^ s * Q) := (hωse.pow hγ.le s).mul hγ.le hQse
  have hfold : atLrcutPaperGen q ω (L ++ [(s, Q)]) 0
      = (∑ i ∈ Finset.range j, frobTwist (R := K) (p := q) i (ω ^ s * Q)
          * atLrcutPaperGen q ω L (i + 1))
        + frobTwist (R := K) (p := q) j (atLrcutPaperGen q ω (L ++ [(s, Q)]) 0) := by
    have hLs : ∀ x ∈ L ++ [(s, Q)], GIsSmall γ (ω ^ x.1 * x.2) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hL x h
      · simp only [List.mem_singleton] at h; rw [h]; exact hF
    have h := atLrPaperGen_fold hγ harch q ω hq hω L hL s hF 0 j
    rw [← frobTwist_atLrcutPaperGen hγ harch q ω hq hω (L ++ [(s, Q)]) hLs 0 j] at h
    simpa using h
  conv_lhs => rw [hfold]
  have hsumSE : GSuperEntire γ (∑ i ∈ Finset.range j,
      frobTwist (R := K) (p := q) i (ω ^ s * Q) * atLrcutPaperGen q ω L (i + 1)) :=
    GSuperEntire.sum hγ.le _ _ (fun i _ => (hGse.frobTwist hγ.le i).mul hγ.le (hseRest (i + 1)))
  rw [evalSeriesGen_add hγ harch hsumSE (hseSelf.frobTwist hγ.le j) (c ^ (q ^ j)),
    evalSeriesGen_finset_sum hγ harch _ _
      (fun i _ => (hGse.frobTwist hγ.le i).mul hγ.le (hseRest (i + 1))) (c ^ (q ^ j)),
    evalSeriesGen_frobTwist hγ harch q hseSelf c j]
  have hzero : ∀ i ∈ Finset.range j,
      evalSeriesGen (frobTwist (R := K) (p := q) i (ω ^ s * Q)
        * atLrcutPaperGen q ω L (i + 1)) (c ^ (q ^ j)) = 0 := by
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    have hji : 1 ≤ j - i := by omega
    have hpow : c ^ (q ^ j) = (c ^ (q ^ (j - i))) ^ (q ^ i) := by
      rw [← pow_mul]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    rw [evalSeriesGen_mul hγ harch (hGse.frobTwist hγ.le i) (hseRest (i + 1)) (c ^ (q ^ j)),
      hpow, evalSeriesGen_frobTwist hγ harch q hGse (c ^ (q ^ (j - i))) i,
      evalSeriesGen_mul hγ harch (hωse.pow hγ.le s) hQse (c ^ (q ^ (j - i))),
      evalSeriesGen_pow hγ harch hωse s (c ^ (q ^ (j - i))), hc (j - i) hji]
    have h1 : (0 : K) ^ s = 0 := zero_pow (by omega : s ≠ 0)
    have h2 : (0 : K) ^ (q ^ i) = 0 := zero_pow (pow_ne_zero i (by omega : q ≠ 0))
    rw [h1, zero_mul, h2, zero_mul]
  rw [Finset.sum_eq_zero hzero, zero_add]

/-- **Chang's MZ property** for the depth-one `L`-series. -/
theorem evalSeriesGen_atL1Gen_frobenius_pow {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (s : ℕ) (hs : 1 ≤ s) {Q : PowerSeries K}
    (hF : GIsSmall γ (ω ^ s * Q)) (hQse : GSuperEntire γ Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeriesGen (atL1Gen q ω s Q) (c ^ (q ^ j))
      = (evalSeriesGen (atL1Gen q ω s Q) c) ^ (q ^ j) := by
  have h := evalSeriesGen_atLrcutPaperGen_frobenius_pow q hγ0 hγ harch hq hω hωse
    ([] : List (ℕ × PowerSeries K)) (by simp) (by simp) s hs hF hQse hc j
  have e1 : atLrcutPaperGen q ω [(s, Q)] 0 = atL1Gen q ω s Q := by
    change atLrcutGen q ω ([(s, Q)] : List (ℕ × PowerSeries K)).reverse 0 = atL1Gen q ω s Q
    rw [List.reverse_singleton]
    exact atLrGen_singleton hγ harch hq hω s hF
  simp only [List.nil_append] at h
  rw [e1] at h
  exact h

/-- **The MZ property in the paper's ordering convention** (general small vanishing `ω`). -/
theorem evalSeriesGen_atLrPaperGen_frobenius_pow {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (s : ℕ) (hs : 1 ≤ s)
    {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (hQse : GSuperEntire γ Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeriesGen (atLrPaperGen q ω (L ++ [(s, Q)])) (c ^ (q ^ j))
      = (evalSeriesGen (atLrPaperGen q ω (L ++ [(s, Q)])) c) ^ (q ^ j) :=
  evalSeriesGen_atLrcutPaperGen_frobenius_pow q hγ0 hγ harch hq hω hωse L hL hLse s hs
    hF hQse hc j

/-- **The MZ property for an arbitrary non-empty tuple**: only the *last* entry of the list (the
one carrying the smallest index) needs a positive depth. -/
theorem evalSeriesGen_atLrPaperGen_frobenius_pow_of_ne {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) {L : List (ℕ × PowerSeries K)} (hne : L ≠ [])
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hLse : ∀ x ∈ L, GSuperEntire γ x.2)
    (hs : 1 ≤ (L.getLast hne).1) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0) (j : ℕ) :
    evalSeriesGen (atLrPaperGen q ω L) (c ^ (q ^ j))
      = (evalSeriesGen (atLrPaperGen q ω L) c) ^ (q ^ j) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  refine evalSeriesGen_atLrPaperGen_frobenius_pow q hγ0 hγ harch hq hω hωse L.dropLast ?_ ?_
    (L.getLast hne).1 hs ?_ ?_ hc j
  · intro x hx
    exact hL x (List.mem_of_mem_dropLast hx)
  · intro x hx
    exact hLse x (List.mem_of_mem_dropLast hx)
  · exact hL _ (List.getLast_mem hne)
  · exact hLse _ (List.getLast_mem hne)

/-- The non-vanishing form of the MZ property. -/
theorem evalSeriesGen_atLrPaperGen_ne_zero_pow {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (L : List (ℕ × PowerSeries K))
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (s : ℕ) (hs : 1 ≤ s)
    {Q : PowerSeries K} (hF : GIsSmall γ (ω ^ s * Q)) (hQse : GSuperEntire γ Q) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω (c ^ (q ^ k)) = 0) (j : ℕ)
    (h : evalSeriesGen (atLrPaperGen q ω (L ++ [(s, Q)])) c ≠ 0) :
    evalSeriesGen (atLrPaperGen q ω (L ++ [(s, Q)])) (c ^ (q ^ j)) ≠ 0 := by
  rw [evalSeriesGen_atLrPaperGen_frobenius_pow q hγ0 hγ harch hq hω hωse L hL hLse s hs
    hF hQse hc j]
  exact pow_ne_zero _ h

end ZagierHoffmanPositiveChar
