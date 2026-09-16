import Submission.ZagierHoffmanProof.GenEntire
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanRing
import Submission.ZagierHoffmanProof.FrobPowTsum

/-!
# Evaluation of super-entire series over an arbitrary valued field

This is the generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `EvalEntire.lean`: a
super-entire series converges at *every* point `c ∈ K` (its coefficients decay faster than any
power of `γ`, and `γ` is small enough — this is the archimedean hypothesis on the value group), so
that

  `evalSeriesGen f c = ∑' n, aₙ · cⁿ`

defines an evaluation map on the ring `ε` of super-entire series.  Evaluation is multiplicative
and converts the Frobenius twist into a power,

  `evalSeriesGen (f^{(k)}) (c^{q^k}) = (evalSeriesGen f c)^{q^k}`,

which is the form in which Chang's MZ property is used.

The value group of `C_∞` is `ℚ`, which satisfies the archimedean hypothesis
`GammaArchimedean Γ₀ := ∀ a < 1, ∀ ε ≠ 0, ∃ n, a ^ n < ε` used below.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology
open SummationFilter

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- The archimedean property of the value group, in the form needed for the convergence of
super-entire series at every point.  It holds for the value group `ℚ` of `C_∞`. -/
def GammaArchimedean (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] : Prop :=
  ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ n : ℕ, a ^ n < ε

/-- **The evaluation of a power series at a point of `K`**: `∑ aₙ cⁿ` (convergence is not part of
the definition; the lemmas below require `GSuperEntire`). -/
noncomputable def evalSeriesGen (f : PowerSeries K) (c : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * c ^ n

lemma evalSeriesGen_def (f : PowerSeries K) (c : K) :
    evalSeriesGen f c = ∑' n : ℕ, PowerSeries.coeff n f * c ^ n := rfl

section summable

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- In a complete nonarchimedean valued field, a sequence whose valuations tend to `0` is
summable. -/
lemma summable_of_v_tendsto_zero {f : ℕ → K}
    (h : ∀ ε : Γ₀, ε ≠ 0 → ∀ᶠ n in atTop, Valued.v (f n) < ε) : Summable f := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, -, hγU⟩ := (Valued.hasBasis_nhds_zero K Γ₀).mem_iff.mp hU
  have hemb : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h0 =>
    Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_injective (by rw [h0, map_zero]))
  filter_upwards [h _ hemb] with n hn
  refine hγU (show Valued.v.restrict (f n) < (γ : _) from ?_)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact hn

/-- **The defining family of the evaluation of a super-entire series is summable.** -/
theorem GSuperEntire.summable_eval {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {f : PowerSeries K} (hf : GSuperEntire γ f) (c : K) :
    Summable fun n : ℕ => PowerSeries.coeff n f * c ^ n := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine (summable_of_ne_finset_zero (s := {0}) ?_)
    intro n hn
    rw [Finset.mem_singleton] at hn
    rw [zero_pow (by omega : n ≠ 0), mul_zero]
  · have hc0 : Valued.v c ≠ 0 := by simpa using hc
    have hinv0 : (Valued.v c)⁻¹ ≠ 0 := inv_ne_zero hc0
    obtain ⟨M, hM⟩ := harch γ hγ (Valued.v c)⁻¹ hinv0
    obtain ⟨a, ha⟩ := hf M
    have hb1 : γ ^ M * Valued.v c < 1 := by
      have hlt := mul_lt_mul_of_pos_right hM (zero_lt_of_ne_zero hc0)
      rwa [inv_mul_cancel₀ hc0] at hlt
    refine summable_of_v_tendsto_zero fun ε hε => ?_
    rcases eq_or_ne a 0 with ha0 | ha0
    · refine Filter.Eventually.of_forall fun n => ?_
      have h1 : Valued.v (PowerSeries.coeff n f) ≤ (0 : Γ₀) := by
        have h' := ha n
        rw [ha0] at h'
        simpa using h'
      have h2 : Valued.v (PowerSeries.coeff n f * c ^ n) ≤ (0 : Γ₀) := by
        rw [map_mul, map_pow]
        exact le_trans (mul_le_mul_left h1 _) (le_of_eq (zero_mul _))
      exact lt_of_le_of_lt h2 (zero_lt_of_ne_zero hε)
    · have hapos : 0 < a := zero_lt_of_ne_zero ha0
      obtain ⟨n₀, hn₀⟩ := harch (γ ^ M * Valued.v c) hb1 (ε / a) (by simp [hε, ha0])
      refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
      have hbound : Valued.v (PowerSeries.coeff n f * c ^ n)
          ≤ a * (γ ^ M * Valued.v c) ^ n := by
        rw [map_mul, map_pow]
        refine le_trans (mul_le_mul' (ha n) le_rfl) ?_
        rw [mul_pow, ← pow_mul]
        exact le_of_eq (mul_assoc a (γ ^ (M * n)) ((Valued.v c) ^ n))
      refine lt_of_le_of_lt hbound ?_
      calc a * (γ ^ M * Valued.v c) ^ n
          ≤ a * (γ ^ M * Valued.v c) ^ n₀ :=
            mul_le_mul_right (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ _) hb1.le hn) _
        _ < a * (ε / a) := mul_lt_mul_of_pos_left hn₀ hapos
        _ = ε := by rw [mul_comm, div_mul_cancel₀ ε ha0]

end summable

section eval

variable [CompleteSpace K] [NonarchimedeanAddGroup K] {γ : Γ₀}

/-- Evaluation of a constant. -/
@[simp] lemma evalSeriesGen_C (a c : K) : evalSeriesGen (PowerSeries.C a) c = a := by
  rw [evalSeriesGen_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) 0
    (fun n hn => by rw [PowerSeries.coeff_C, if_neg hn, zero_mul])]
  rw [PowerSeries.coeff_C, if_pos rfl, pow_zero, mul_one]

/-- Evaluation of `t`. -/
@[simp] lemma evalSeriesGen_X (c : K) : evalSeriesGen (PowerSeries.X : PowerSeries K) c = c := by
  rw [evalSeriesGen_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) 1]
  · rw [PowerSeries.coeff_X, if_pos rfl, pow_one, one_mul]
  · intro n hn
    rw [PowerSeries.coeff_X, if_neg hn, zero_mul]

/-- Evaluation of a monomial. -/
@[simp] lemma evalSeriesGen_monomial (a c : K) (n : ℕ) :
    evalSeriesGen (PowerSeries.monomial n a) c = a * c ^ n := by
  rw [evalSeriesGen_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) n
    (fun m hm => by rw [PowerSeries.coeff_monomial, if_neg hm, zero_mul])]
  rw [PowerSeries.coeff_monomial, if_pos rfl]

/-- Evaluation of `1`. -/
@[simp] lemma evalSeriesGen_one (c : K) : evalSeriesGen (1 : PowerSeries K) c = 1 := by
  rw [show (1 : PowerSeries K) = PowerSeries.C 1 from (map_one PowerSeries.C).symm]
  exact evalSeriesGen_C 1 c

/-- Evaluation is additive on super-entire series. -/
lemma evalSeriesGen_add (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {f g : PowerSeries K} (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) (c : K) :
    evalSeriesGen (f + g) c = evalSeriesGen f c + evalSeriesGen g c := by
  rw [evalSeriesGen_def, evalSeriesGen_def, evalSeriesGen_def]
  rw [show (fun n : ℕ => PowerSeries.coeff n (f + g) * c ^ n)
      = fun n : ℕ => (PowerSeries.coeff n f * c ^ n + PowerSeries.coeff n g * c ^ n) from
    funext fun n => by rw [map_add (PowerSeries.coeff n), add_mul]]
  exact ((hf.summable_eval hγ harch c).tsum_add (hg.summable_eval hγ harch c))

/-- Evaluation is compatible with negation. -/
@[simp] lemma evalSeriesGen_neg (f : PowerSeries K) (c : K) :
    evalSeriesGen (-f) c = -evalSeriesGen f c := by
  rw [evalSeriesGen_def, evalSeriesGen_def, ← tsum_neg]
  exact tsum_congr fun n => by rw [map_neg (PowerSeries.coeff n), neg_mul]

/-- Evaluation is compatible with subtraction. -/
lemma evalSeriesGen_sub (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {f g : PowerSeries K} (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) (c : K) :
    evalSeriesGen (f - g) c = evalSeriesGen f c - evalSeriesGen g c := by
  rw [sub_eq_add_neg, evalSeriesGen_add hγ harch hf hg.neg, evalSeriesGen_neg, sub_eq_add_neg]

/-- Evaluation of a `K`-multiple. -/
lemma evalSeriesGen_C_mul (a : K) (f : PowerSeries K) (c : K) :
    evalSeriesGen (PowerSeries.C a * f) c = a * evalSeriesGen f c := by
  rw [evalSeriesGen_def, evalSeriesGen_def, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_C_mul, mul_assoc]

/-- Evaluation of a finite sum. -/
lemma evalSeriesGen_finset_sum (hγ : γ < 1) (harch : GammaArchimedean Γ₀) {ι : Type*}
    (s : Finset ι) (g : ι → PowerSeries K)
    (hg : ∀ i ∈ s, GSuperEntire γ (g i)) (c : K) :
    evalSeriesGen (∑ i ∈ s, g i) c = ∑ i ∈ s, evalSeriesGen (g i) c := by
  classical
  induction s using Finset.induction with
  | empty => simp [evalSeriesGen_def]
  | insert a s ha ih =>
    have hga : GSuperEntire γ (g a) := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, GSuperEntire γ (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalSeriesGen_add hγ harch hga (GSuperEntire.sum hγ.le s g hs) c, ih hs]

lemma evalSeriesGen_natCast (n : ℕ) (c : K) :
    evalSeriesGen (n : PowerSeries K) c = (n : K) := by
  have hCN : (n : PowerSeries K) = PowerSeries.C (n : K) := by
    rw [← map_natCast (PowerSeries.C : K →+* PowerSeries K) n]
  rw [hCN, evalSeriesGen_C]

end eval

section twist

variable [CompleteSpace K] [NonarchimedeanAddGroup K] {γ : Γ₀}

/-- **Evaluation converts the Frobenius twist into a power**:
`(f^{(k)})(c^(q^k)) = (f(c))^(q^k)`. -/
theorem evalSeriesGen_frobTwist (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (q : ℕ) [FrobPow K q] {f : PowerSeries K} (hf : GSuperEntire γ f) (c : K) (k : ℕ) :
    evalSeriesGen (frobTwist (R := K) (p := q) k f) (c ^ (q ^ k))
      = (evalSeriesGen f c) ^ (q ^ k) := by
  have hsum := hf.summable_eval hγ harch c
  have hpt : (∑' n : ℕ, (PowerSeries.coeff n f * c ^ n) ^ (q ^ k))
      = (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) ^ (q ^ k) :=
    (ZagierHoffmanPositiveChar.tsum_pow_frobPow_general hsum k).symm
  rw [evalSeriesGen_def, evalSeriesGen_def, ← hpt]
  refine tsum_congr fun n => ?_
  rw [frobTwist_coeff, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

end twist

section mul

variable [CompleteSpace K] [NonarchimedeanAddGroup K] {γ : Γ₀}

/-- **Evaluation is multiplicative** on super-entire series: `(f·g)(c) = f(c)·g(c)`. -/
theorem evalSeriesGen_mul (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {f g : PowerSeries K} (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) (c : K) :
    evalSeriesGen (f * g) c = evalSeriesGen f c * evalSeriesGen g c := by
  haveI : NonarchimedeanRing K := Commons.Topology.Algebra.Valued.nonarchimedeanRing
  have hf' : Summable fun n : ℕ => PowerSeries.coeff n f * c ^ n := hf.summable_eval hγ harch c
  have hg' : Summable fun n : ℕ => PowerSeries.coeff n g * c ^ n := hg.summable_eval hγ harch c
  have hprod : Summable fun p : ℕ × ℕ =>
      (PowerSeries.coeff p.1 f * c ^ p.1) * (PowerSeries.coeff p.2 g * c ^ p.2) :=
    Summable.mul_of_nonarchimedean
      (f := fun n => PowerSeries.coeff n f * c ^ n)
      (g := fun n => PowerSeries.coeff n g * c ^ n) hf' hg'
  have hcauchy : (∑' n : ℕ, PowerSeries.coeff n f * c ^ n)
        * (∑' n : ℕ, PowerSeries.coeff n g * c ^ n)
      = ∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (PowerSeries.coeff kl.1 f * c ^ kl.1) * (PowerSeries.coeff kl.2 g * c ^ kl.2) :=
    hf'.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg' hprod
  simp only [evalSeriesGen_def]
  rw [hcauchy]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

/-- Evaluation is compatible with powers. -/
theorem evalSeriesGen_pow (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {f : PowerSeries K} (hf : GSuperEntire γ f) (n : ℕ) (c : K) :
    evalSeriesGen (f ^ n) c = (evalSeriesGen f c) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, evalSeriesGen_one]
  | succ k ih =>
      rw [pow_succ, pow_succ, evalSeriesGen_mul hγ harch (hf.pow hγ.le k) hf c, ih]

/-- Evaluation is compatible with finite products. -/
lemma evalSeriesGen_prod (hγ : γ < 1) (harch : GammaArchimedean Γ₀) {ι : Type*}
    (s : Finset ι) (g : ι → PowerSeries K) (hg : ∀ i ∈ s, GSuperEntire γ (g i)) (c : K) :
    evalSeriesGen (∏ i ∈ s, g i) c = ∏ i ∈ s, evalSeriesGen (g i) c := by
  classical
  induction s using Finset.induction with
  | empty => simp [evalSeriesGen_one]
  | insert a s ha ih =>
    have hga : GSuperEntire γ (g a) := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, GSuperEntire γ (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalSeriesGen_mul hγ harch hga (GSuperEntire.prod hγ.le s g hs) c, ih hs]

end mul

end ZagierHoffmanPositiveChar
