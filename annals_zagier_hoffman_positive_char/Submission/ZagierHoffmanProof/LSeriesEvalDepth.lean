import Submission.ZagierHoffmanProof.EvalDepthBound
import Submission.ZagierHoffmanProof.TmMotive
import Submission.Commons.Topology.Algebra.Valued.summable_pair_of_two_estimates_const

/-!
# The evaluation of the depth-`r` `L`-series at a point (C1 of the ζ_A ↔ CMPL bridge)

The paper's `L`-series is

  `𝓛(𝔰;Q) = ∑_{i₁ > ⋯ > iᵣ ≥ 0} (Ω^{sᵣ}Qᵣ)^{(iᵣ)} ⋯ (Ω^{s₁}Q₁)^{(i₁)}`

and the workspace computes it coefficientwise as `atLrPaperGen q ω (tmCoe t)`.  Its value at a point
`θ` is therefore a *nested* sum of the values of the Frobenius twists:

  `(𝓛(𝔰;Q))(θ) = ∑'_{i₁} (𝓛(𝔰_{>1};Q_{>1}) cut) ⋯`,

which is exactly the depth-`r` generalisation of `LSeriesEval.evalSeriesGen_atL1Gen`.  We prove it
here, with the joint summability of the double family

  `(n,i) ↦ coeff n (A_i·B_i)·θⁿ`,  `A_i = (ω^{s}Q)^{(N+i)}`,  `B_i = (the truncated tail)`,

discharged by `EvalDepthBound`'s two estimates and the two-parameter summability criterion
`Commons.Topology.Algebra.Valued.summable_pair_of_two_estimates_const`.

## Main results

* `evalSeriesGen_mk_tsum` — the interchange of the coefficientwise `tsum` with the value `tsum`.
* `evalIter` — the iterated value of the nested `L`-series.
* ★★ `summable_coeff_frobTwist_mul_tail` — the joint summability.
* ★★★ `evalSeriesGen_atLrcutGen` — **the depth-`r` evaluation**:
  `evalSeriesGen (atLrcutGen q ω L N) θ = evalIter θ q ω L N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology
open SummationFilter

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-! ## §1. The interchange of the two `tsum`s -/

/-- **The interchange of the coefficientwise `tsum` with the value `tsum`**: if the double family
`(n,i) ↦ coeff n (f i)·cⁿ` is summable, then the value at `c` of the coefficientwise sum
`∑' i, f i` is the sum of the values. -/
theorem evalSeriesGen_mk_tsum {f : ℕ → PowerSeries K} {c : K}
    (hsum : Summable fun p : ℕ × ℕ => PowerSeries.coeff p.1 (f p.2) * c ^ p.1) :
    evalSeriesGen (PowerSeries.mk fun n => ∑' i, PowerSeries.coeff n (f i)) c
      = ∑' i, evalSeriesGen (f i) c := by
  have h1 : evalSeriesGen (PowerSeries.mk fun n => ∑' i, PowerSeries.coeff n (f i)) c
      = ∑' n, (∑' i, PowerSeries.coeff n (f i)) * c ^ n := by
    rw [evalSeriesGen_def]
    simp only [PowerSeries.coeff_mk]
  have h2 : ∀ n, (∑' i, PowerSeries.coeff n (f i)) * c ^ n
      = ∑' i, PowerSeries.coeff n (f i) * c ^ n := by
    intro n
    rw [tsum_mul_right]
  rw [h1]
  rw [show (∑' n, (∑' i, PowerSeries.coeff n (f i)) * c ^ n)
      = ∑' n, ∑' i, PowerSeries.coeff n (f i) * c ^ n from tsum_congr h2]
  rw [← Summable.tsum_comm (f := fun n i => PowerSeries.coeff n (f i) * c ^ n) hsum]
  refine tsum_congr fun i => ?_
  rw [evalSeriesGen_def]

/-! ## §2. The iterated value of the nested `L`-series -/

/-- The iterated value of the nested `L`-series, peeling the first factor with the outermost sum:
`evalIter θ q ω [(s₁,Q₁),(s₂,Q₂),…] N` is the value of the `L`-series built from the factors
`ω^{s₁}Q₁, ω^{s₂}Q₂, …` with the outermost twist index `N + i`. -/
noncomputable def evalIter (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K) :
    List (ℕ × PowerSeries K) → ℕ → K
  | [], _ => 1
  | (s, Q) :: rest, N => ∑' i : ℕ,
      evalSeriesGen (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)) θ
        * evalIter θ q ω rest (N + i + 1)

@[simp] lemma evalIter_nil (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (N : ℕ) :
    evalIter θ q ω ([] : List (ℕ × PowerSeries K)) N = 1 := rfl

lemma evalIter_cons (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (s : ℕ) (Q : PowerSeries K) (rest : List (ℕ × PowerSeries K)) (N : ℕ) :
    evalIter θ q ω ((s, Q) :: rest) N = ∑' i : ℕ,
      evalSeriesGen (frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)) θ
        * evalIter θ q ω rest (N + i + 1) := rfl

/-! ## §3. The joint summability of the double family -/

/-- **The joint summability of `(n,i) ↦ coeff n ((ω^sQ)^{(N+i)}·tail_i)·θⁿ`.**

The `n`-direction uses the super-entireness of `ω^sQ` (via `v_coeff_frobTwist_mul_le_super`), the
`i`-direction the smallness of `ω^sQ` (via `v_coeff_frobTwist_mul_le_small`), and the two are
combined by `summable_pair_of_two_estimates_const`. -/
lemma summable_coeff_frobTwist_mul_tail
    {γ : Γ₀} (hγ : γ < 1) (hγ0 : γ ≠ 0) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {F : PowerSeries K} {θ : K}
    (hF : GIsSmall γ F) (hFse : GSuperEntire γ F)
    {B : ℕ → PowerSeries K} {M : ℕ} (hM1 : 1 ≤ M) (hδ : γ ^ M * Valued.v θ < 1)
    {b : Γ₀} (hb0 : b ≠ 0)
    (hb : ∀ i k, Valued.v (PowerSeries.coeff k (B i)) ≤ b * γ ^ (M * k)) (N : ℕ) :
    Summable fun p : ℕ × ℕ => PowerSeries.coeff p.1
      (frobTwist (R := K) (p := q) (N + p.2) F * B p.2) * θ ^ p.1 := by
  classical
  obtain ⟨aF, haF⟩ := hFse M
  have hF' : ∀ j, Valued.v (PowerSeries.coeff j F) ≤ min γ (aF * γ ^ (M * j)) :=
    fun j => le_min (hF j) (haF j)
  -- the threshold `J` with `aF * γ^(M*J) ≤ γ`
  have hJ : ∃ J : ℕ, aF * γ ^ (M * J) ≤ γ := by
    rcases eq_or_ne aF 0 with h | h
    · exact ⟨0, by rw [h, zero_mul]; exact zero_le⟩
    · obtain ⟨J, hJ⟩ := harch (γ ^ M)
        (pow_lt_one₀ (zero_le) hγ (by omega)) (γ / aF) (div_ne_zero hγ0 h)
      refine ⟨J, ?_⟩
      have h2 : aF * γ ^ (M * J) < aF * (γ / aF) := by
        rw [pow_mul]
        exact mul_lt_mul_of_pos_left hJ (lt_of_le_of_ne (zero_le) (Ne.symm h))
      rw [mul_comm aF (γ / aF), div_mul_cancel₀ γ h] at h2
      exact le_of_lt h2
  obtain ⟨J, hJ⟩ := hJ
  -- the constants
  have hM1' : (1 : ℕ) ≤ M := hM1
  have hpowpos : (0 : Γ₀) < γ ^ (M * (J - 1)) :=
    pow_pos (lt_of_le_of_ne (zero_le) (Ne.symm hγ0)) _
  have hmax0 : max aF (γ * (γ ^ (M * (J - 1)))⁻¹) ≠ 0 := by
    intro h
    have h1 : γ * (γ ^ (M * (J - 1)))⁻¹ ≤ (0 : Γ₀) := by
      have := le_max_right aF (γ * (γ ^ (M * (J - 1)))⁻¹)
      rw [h] at this
      exact this
    have h2 : (0 : Γ₀) < γ * (γ ^ (M * (J - 1)))⁻¹ :=
      mul_pos (lt_of_le_of_ne (zero_le) (Ne.symm hγ0)) (inv_pos.mpr hpowpos)
    exact absurd h1 (not_le.mpr h2)
  refine Commons.Topology.Algebra.Valued.summable_pair_of_two_estimates_const
    (K := K) (q := q) (C := b * max aF (γ * (γ ^ (M * (J - 1)))⁻¹))
    (C₂ := b) (δ := γ ^ M * Valued.v θ) (γ := γ) (θv := Valued.v θ)
    hq hδ hγ (mul_ne_zero hb0 hmax0) hb0 harch (fun p => ?_) (fun p => ?_)
  · -- the `n`-direction: the super-entireness estimate
    have hsuper := v_coeff_frobTwist_mul_le_super (K := K) (q := q) (F := F) (B := B p.2)
      (a := aF) (b := b) (M := M) (J := J) hγ hγ0 (by omega) hM1 hF' (hb p.2) hJ (N + p.2) p.1
    have hval : Valued.v (PowerSeries.coeff p.1
        (frobTwist (R := K) (p := q) (N + p.2) F * B p.2) * θ ^ p.1)
        = Valued.v (PowerSeries.coeff p.1
          (frobTwist (R := K) (p := q) (N + p.2) F * B p.2)) * (Valued.v θ) ^ p.1 := by
      rw [map_mul, map_pow]
    rw [hval]
    refine le_trans (mul_le_mul_of_nonneg_right hsuper (zero_le)) ?_
    rw [mul_pow, ← pow_mul, mul_assoc]
  · -- the `i`-direction: the smallness estimate
    have hsmall := v_coeff_frobTwist_mul_le_small (K := K) (q := q) (F := F) (B := B p.2)
      (γ := γ) (b := b) (hF) (fun k => le_trans (hb p.2 k)
        (by simpa using mul_le_mul_right (pow_le_one₀ (zero_le) hγ.le) b)) (N + p.2) p.1
    have hle : γ ^ (q ^ (N + p.2)) ≤ γ ^ (q ^ p.2) :=
      pow_le_pow_of_le_one (zero_le) hγ.le (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
    have hval : Valued.v (PowerSeries.coeff p.1
        (frobTwist (R := K) (p := q) (N + p.2) F * B p.2) * θ ^ p.1)
        = Valued.v (PowerSeries.coeff p.1
          (frobTwist (R := K) (p := q) (N + p.2) F * B p.2)) * (Valued.v θ) ^ p.1 := by
      rw [map_mul, map_pow]
    rw [hval]
    calc Valued.v (PowerSeries.coeff p.1
            (frobTwist (R := K) (p := q) (N + p.2) F * B p.2)) * (Valued.v θ) ^ p.1
        ≤ (γ ^ (q ^ (N + p.2)) * b) * (Valued.v θ) ^ p.1 :=
          mul_le_mul_of_nonneg_right hsmall (zero_le)
      _ ≤ (γ ^ (q ^ p.2) * b) * (Valued.v θ) ^ p.1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (zero_le)) (zero_le)
      _ = b * γ ^ (q ^ p.2) * (Valued.v θ) ^ p.1 := by rw [mul_comm (γ ^ (q ^ p.2)) b]

/-! ## §4. Super-entireness of the truncated `L`-series, in every cutoff -/

/-- The truncated `L`-series is super-entire for **every** cutoff (including the empty list, where
it is `1`). -/
lemma gSuperEntire_atLrcutGen_all {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2)) (hLse : ∀ x ∈ L, GSuperEntire γ x.2) (N : ℕ) :
    GSuperEntire γ (atLrcutGen q ω L N) := by
  rcases L with _ | ⟨a, rest⟩
  · rw [atLrcutGen_nil]; exact GSuperEntire.one γ
  · obtain ⟨s, Q⟩ := a
    exact gSuperEntire_atLrcut hγ harch hq hω hωse hL hLse N

/-! ## §5. The depth-`r` evaluation -/

/-- The `cons` step of the evaluation. -/
lemma evalSeriesGen_atLrcutGen_cons
    {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) {q : ℕ} [FrobPow K q]
    {ω : PowerSeries K} {s : ℕ} {Q : PowerSeries K} {rest : List (ℕ × PowerSeries K)}
    (N : ℕ) (θ : K)
    (hseF : GSuperEntire γ (ω ^ s * Q))
    (hseB : ∀ i, GSuperEntire γ (atLrcutGen q ω rest (N + i + 1)))
    (hsum : Summable fun p : ℕ × ℕ => PowerSeries.coeff p.1
        (frobTwist (R := K) (p := q) (N + p.2) (ω ^ s * Q)
          * atLrcutGen q ω rest (N + p.2 + 1)) * θ ^ p.1)
    (ih : ∀ i, evalSeriesGen (atLrcutGen q ω rest (N + i + 1)) θ
        = evalIter θ q ω rest (N + i + 1)) :
    evalSeriesGen (atLrcutGen q ω ((s, Q) :: rest) N) θ
      = evalIter θ q ω ((s, Q) :: rest) N := by
  rw [atLrcutGen_cons]
  rw [evalSeriesGen_mk_tsum (f := fun i => frobTwist (R := K) (p := q) (N + i) (ω ^ s * Q)
      * atLrcutGen q ω rest (N + i + 1)) hsum]
  rw [evalIter_cons]
  refine tsum_congr fun i => ?_
  rw [evalSeriesGen_mul hγ harch (hseF.frobTwist hγ.le (N + i)) (hseB i) θ, ih i]

/-- **★★★ The depth-`r` evaluation of the `L`-series**: the nested `tsum` defining the value
interchanges, giving the iterated value `evalIter`. -/
theorem evalSeriesGen_atLrcutGen
    {γ : Γ₀} (hγ : γ < 1) (hγ0 : γ ≠ 0) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ L, GSuperEntire γ x.2) {θ : K}
    {M : ℕ} (hM1 : 1 ≤ M) (hδ : γ ^ M * Valued.v θ < 1) (N : ℕ) :
    evalSeriesGen (atLrcutGen q ω L N) θ = evalIter θ q ω L N := by
  induction L generalizing N with
  | nil => rw [atLrcutGen_nil, evalSeriesGen_one, evalIter_nil]
  | cons a rest ih =>
    obtain ⟨s, Q⟩ := a
    have hF : GIsSmall γ (ω ^ s * Q) := hL (s, Q) (by simp)
    have hFse : GSuperEntire γ (ω ^ s * Q) :=
      (hωse.pow hγ.le s).mul hγ.le (hLse (s, Q) (by simp))
    have hrest : ∀ x ∈ rest, GIsSmall γ (ω ^ x.1 * x.2) :=
      fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hrestse : ∀ x ∈ rest, GSuperEntire γ x.2 :=
      fun x hx => hLse x (List.mem_cons_of_mem _ hx)
    -- the uniform super-entire bound for the tail
    obtain ⟨b₀, hb₀⟩ := gSuperEntire_atLrcut_bound hγ harch hq hω hωse M rest hrest hrestse
    have hseB : ∀ i : ℕ, GSuperEntire γ (atLrcutGen q ω rest (N + i + 1)) := fun i =>
      gSuperEntire_atLrcutGen_all hγ harch hq hω hωse hrest hrestse (N + i + 1)
    have hbnd : ∀ (i k : ℕ), Valued.v (PowerSeries.coeff k (atLrcutGen q ω rest (N + i + 1)))
        ≤ max b₀ 1 * γ ^ (M * k) := by
      intro i k
      refine le_trans (hb₀ (N + i + 1) k) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left b₀ 1) (zero_le)
    have hsum : Summable fun p : ℕ × ℕ => PowerSeries.coeff p.1
        (frobTwist (R := K) (p := q) (N + p.2) (ω ^ s * Q)
          * atLrcutGen q ω rest (N + p.2 + 1)) * θ ^ p.1 :=
      summable_coeff_frobTwist_mul_tail hγ hγ0 harch hq hF hFse hM1 hδ
        (b := max b₀ 1)
        (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right b₀ 1))) hbnd N
    have hih : ∀ i : ℕ, evalSeriesGen (atLrcutGen q ω rest (N + i + 1)) θ
        = evalIter θ q ω rest (N + i + 1) := fun i => ih hrest hrestse (N + i + 1)
    exact evalSeriesGen_atLrcutGen_cons hγ harch N θ hFse hseB hsum hih

/-! ## §6. The evaluation of `tmL` -/

/-- **The evaluation of the `t`-motive's `L`-series `𝓛(𝔰;Q) = tmL q ω t`** at a point `θ`, as the
iterated value `evalIter` of the reversed tuple. -/
theorem evalSeriesGen_tmL
    {γ : Γ₀} (hγ : γ < 1) (hγ0 : γ ≠ 0) (harch : GammaArchimedean Γ₀)
    {q : ℕ} [FrobPow K q] (hq : 2 ≤ q) {ω : PowerSeries K} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) {t : List (ℕ × Polynomial K)}
    (hL : ∀ x ∈ tmCoe (K := K) t, GIsSmall γ (ω ^ x.1 * x.2))
    (hLse : ∀ x ∈ tmCoe (K := K) t, GSuperEntire γ x.2) {θ : K}
    {M : ℕ} (hM1 : 1 ≤ M) (hδ : γ ^ M * Valued.v θ < 1) :
    evalSeriesGen (tmL q ω t) θ = evalIter θ q ω (tmCoe (K := K) t).reverse 0 := by
  have h := evalSeriesGen_atLrcutGen hγ hγ0 harch hq hω hωse
    (L := (tmCoe (K := K) t).reverse) (fun x hx => hL x (List.mem_reverse.mp hx))
    (fun x hx => hLse x (List.mem_reverse.mp hx)) hM1 hδ 0
  simpa [tmL, atLrPaperGen, atLrGen] using h

end ZagierHoffmanPositiveChar
