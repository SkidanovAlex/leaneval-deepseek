import Mathlib
import Submission.DS.Coro3UB

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

namespace Submission.DS

/-- The Finset of denominators `q` with `q ≤ n`. -/
noncomputable def leDenFinset (n : ℕ) : Finset ℕ+ :=
  ((Finset.range (n + 1)).filter (fun m : ℕ => 0 < m)).attach.image (fun m =>
    ⟨m.1, (Finset.mem_filter.mp m.2).2⟩)

lemma mem_leDenFinset (n : ℕ) (q : ℕ+) : q ∈ leDenFinset n ↔ (q : ℕ) ≤ n := by
  classical
  unfold leDenFinset
  constructor
  · intro hq
    rcases (Finset.mem_image.mp hq) with ⟨m, hm, hmq⟩
    have hmem : m.1 ∈ Finset.range (n + 1) := (Finset.mem_filter.mp m.2).1
    have hmle : m.1 ≤ n := by
      have hlt : m.1 < n + 1 := Finset.mem_range.mp hmem
      omega
    have hqval : m.1 = (q : ℕ) := by
      have := congrArg PNat.val hmq
      simpa using this
    omega
  · intro hq
    let m : {x : ℕ // x ∈ (Finset.range (n + 1)).filter (fun m : ℕ => 0 < m)} :=
      ⟨(q : ℕ), by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_range.mpr (by have h1 := hq; omega)
        · exact q.2⟩
    refine Finset.mem_image.mpr ⟨m, Finset.mem_attach (s := (Finset.range (n + 1)).filter (fun m : ℕ => 0 < m)) m, ?_⟩
    apply Subtype.ext
    dsimp [m]
    rfl

/-- The map `n ↦ {q | q ≤ n}` tends to `atTop` on Finsets. -/
lemma tendsto_leDenFinset : Tendsto (fun n : ℕ => (leDenFinset n : Finset ℕ+)) atTop atTop := by
  classical
  rw [Filter.tendsto_def]
  intro s hs
  rcases (Filter.mem_atTop_sets.mp hs) with ⟨a, ha⟩
  rw [Filter.mem_atTop_sets]
  refine ⟨a.sup (fun q : ℕ+ => (q : ℕ)), ?_⟩
  intro n hn
  exact ha (leDenFinset n) (by
    intro q hq
    exact (mem_leDenFinset n q).2 (le_trans (Finset.le_sup hq) hn))

/-- Sum of `f` over denominators `q ≥ n+1`. -/
noncomputable def tailSum (f : ℕ+ → ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)}, ((f q : NNReal) : ℝ≥0∞)

/-- Tails of a summable nonneg series (as ENNReal sums) tend to zero. -/
lemma tailSum_tendsto_zero (f : ℕ+ → ℝ≥0) (hf : Summable f) :
    Tendsto (fun n : ℕ => tailSum f n) atTop (𝓝 0) := by
  classical
  have htot : (∑' q : ℕ+, ((f q : NNReal) : ℝ≥0∞)) ≠ ∞ := by
    rw [ENNReal.tsum_coe_ne_top_iff_summable]
    exact hf
  have hmain := ENNReal.tendsto_tsum_compl_atTop_zero (α := ℕ+) htot
  have hc : Tendsto (fun n : ℕ =>
      ∑' b : {x : ℕ+ // x ∉ leDenFinset n}, ((f b : NNReal) : ℝ≥0∞)) atTop (𝓝 0) :=
    hmain.comp tendsto_leDenFinset
  have heq : (fun n : ℕ =>
      ∑' b : {x : ℕ+ // x ∉ leDenFinset n}, ((f b : NNReal) : ℝ≥0∞)) = fun n : ℕ => tailSum f n := by
    funext n
    symm
    -- sums over {x // x ∉ leDenFinset n} equal sums over {q // n+1 ≤ q}
    let e : {x : ℕ+ // x ∉ leDenFinset n} ≃ {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)} :=
      ⟨fun x => ⟨x.1, by
          have hq : ¬ (x.1 : ℕ) ≤ n := by
            intro h
            exact x.2 ((mem_leDenFinset n x.1).2 h)
          omega⟩,
       fun q => ⟨q.1, by
          intro h
          have hle : (q.1 : ℕ) ≤ n := (mem_leDenFinset n q.1).1 h
          omega⟩,
       by intro x; apply Subtype.ext; rfl,
       by intro q; apply Subtype.ext; rfl⟩
    simpa [e, tailSum] using ((Equiv.tsum_eq e (f := fun q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)} =>
      ((f q : NNReal) : ℝ≥0∞))).symm)
  simpa [heq] using hc

/-- The a-fibres of the cover pairs: `a ∈ [0,q]`, coprime to `q`. -/
abbrev CovFib (q : ℕ+) : Type :=
  {a : ℕ // a ∈ (Finset.Icc 0 (q : ℕ)).filter (fun a : ℕ => Nat.Coprime a (q : ℕ))}

instance covFib_fintype (q : ℕ+) : Fintype (CovFib q) := by
  dsimp [CovFib]
  infer_instance

/-- The sigma type of cover pairs at level `n`. -/
def CovSigma (n : ℕ) : Type := Σ q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)}, CovFib q.1

instance covSigma_countable (n : ℕ) : Countable (CovSigma n) := by
  unfold CovSigma
  infer_instance

/-- Fibre cardinality bound: at most `φ(q) + 1` numerators for denominator `q`. -/
lemma covFib_card_le (q : ℕ+) : Fintype.card (CovFib q) ≤ φ q + 1 := by
  classical
  dsimp [CovFib]
  rw [Fintype.card_coe]
  simpa [Nat.coprime_comm] using (card_coprime_Icc_zero_le (q : ℕ))

/-- The per-level ENNReal cover sum over pairs is at most the `(φ+1)`-weighted
tail sum over denominators. -/
lemma covSigma_sum_le_tail (G : ℕ+ → ℝ≥0∞) (n : ℕ) :
    (∑' p : CovSigma n, G p.1.1) ≤
      ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
        (((φ q + 1 : ℕ) : ℝ≥0∞) * G q.1) := by
  classical
  change (∑' p : (Σ q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)}, CovFib q.1), G p.1.1) ≤
    ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
      (((φ q + 1 : ℕ) : ℝ≥0∞) * G q.1)
  rw [ENNReal.tsum_sigma']
  refine ENNReal.tsum_le_tsum (fun q => ?_)
  have hinner : (∑' a : CovFib q.1, G q.1) ≤ (((φ q.1 + 1 : ℕ) : ℝ≥0∞) * G q.1) := by
    rw [tsum_fintype]
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul' (by exact_mod_cast covFib_card_le q.1) le_rfl
  simpa using hinner

/-- The natural map from the sigma type to the pair subtype. -/
def covPairOfSigma {n : ℕ} (p : CovSigma n) : CovPairs n :=
  ⟨(p.1.1, p.2.1), ⟨p.1.2, (Finset.mem_filter.mp p.2.2).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp p.2.2).1).2⟩⟩

/-- `x ∈ 𝒜 ψ` lies in the sigma-cover, for every `n`. -/
lemma mem_covSigma_iUnion (ψ : ℕ+ → ℝ≥0) {x : ℝ} (hx : x ∈ 𝒜 ψ)
    (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) (n : ℕ) :
    x ∈ ⋃ p : CovSigma n, ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ) := by
  rw [A_eq_Icc_inter_limsup] at hx
  rcases hx with ⟨hx01, hxlim⟩
  have hinf : ({q : ℕ+ | x ∈ Acopr ψ q}).Infinite := by
    simpa [limsupDenoms] using hxlim
  rcases (infinite_iff_forall_ge {q : ℕ+ | x ∈ Acopr ψ q}).1 hinf (n + 1) with ⟨q, hq, hqge⟩
  have hxq : x ∈ Acopr ψ q := hq
  rcases hxq with ⟨a, hc, hineq⟩
  have hale : a ≤ (q : ℕ) := num_le_q_of_half_radius (hψ q) hx01.2 hineq
  refine mem_iUnion.mpr ⟨⟨⟨q, hqge⟩, ⟨a, ?_⟩⟩, hineq⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le a, hale⟩, hc⟩

/-- Sigma-cover diameter bound at level `n`. -/
lemma covSigma_diam_eventually (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    ∀ᶠ n in atTop, ∀ p : CovSigma n,
      Metric.ediam ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  filter_upwards with n
  intro p
  let q : ℕ+ := p.1.1
  let a : ℕ := p.2.1
  have hqge : (n : ℕ) + 1 ≤ (q : ℕ) := by
    simpa [q] using p.1.2
  have hd0 : Metric.ediam ({y : ℝ | inequality_1_7 ψ y a q} : Set ℝ) ≤
      ENNReal.ofReal (2 * ((ψ q / q : NNReal) : ℝ)) := by
    have hh := ediam_covInterval_le ψ (covPairOfSigma p)
    simpa [q, a, covInterval, covPairOfSigma] using hh
  have hle1 : 2 * ((ψ q / q : NNReal) : ℝ) ≤ 1 / (q : ℝ) := by
    have hψR : (ψ q : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hψ q
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
    have hmain : (ψ q : ℝ) / (q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hψR (le_of_lt hqpos)
    have hmain2 : 2 * ((ψ q : ℝ) / (q : ℝ)) ≤ 1 / (q : ℝ) := by
      have hstep : 2 * ((1 / 2 : ℝ) / (q : ℝ)) = 1 / (q : ℝ) := by
        field_simp [hqpos.ne']
      calc
        2 * ((ψ q : ℝ) / (q : ℝ)) ≤ 2 * ((1 / 2 : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = 1 / (q : ℝ) := hstep
    simpa [NNReal.coe_div] using hmain2
  have hle2 : 1 / (q : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    have hden : ((n : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hqge
    exact one_div_le_one_div_of_le hpos hden
  have hmain2 : Metric.ediam ({y : ℝ | inequality_1_7 ψ y a q} : Set ℝ) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    hd0.trans (ENNReal.ofReal_le_ofReal (le_trans hle1 hle2))
  simpa [q, a] using hmain2

end Submission.DS
