/-
# The per-block Littlewood--Paley bound for the IW annuli (the `p >= 2` half of Lépingle's crux)

This file proves `Work.KMTAreas.A7Hi.bandSumSqRep`: for the annuli `Δ_i = T_{i+1} - T_i` of the
low-pass Ionescu--Wainger family `T_k = lpf ρ l m₀ k = kmtProj ρ l (-(m₀+k))` on the good major
arcs, and for an *arbitrary* finite set `I ⊆ ℕ` of scales, the partial sum over `I` is bounded in
`ℓᵖ(ℤ)`, `1 < p < ∞`, by the restricted band-pass square function over `I`, with a constant free
of the arithmetic height `l`, of `m₀` and of `I`:

`‖ Σ_{i∈I} (T_i − T_{i+1}) f ‖_{ℓᵖ}  ≤  C ‖ (Σ_{i∈I} |(T_i − T_{i+1}) f|²)^{1/2} ‖_{ℓᵖ}`.

This is the statement of the (stale) stub `Work.KMTAreas.A7G.bandSumSqFun` in the `lpf`
vocabulary, and it is the key missing input of the Men'shov/Lépingle chapter: together with the
proved `Work.KMTAreas.A7Hi.fkrInterchangeGen` (interchange of variational and Lebesgue norms) and
the elementary convexity `Σ_i a_i^{p/2} ≤ (Σ_i a_i)^{p/2}` for `p ≥ 2` it yields the chain-part
Lépingle crux `Work.KMTAreas.A7HiRep.chainPartSqFun` for `p ≥ 2`
(see `NOTES_A7G_maximalLowpass_SESSION.md` §2).

## The proof

The annuli are *banded-orthogonal*: `Δ_a ∘ Δ_b = 0` whenever `|a-b| ≥ 2` (but `Δ_a` is **not** a
projection and `Δ_a Δ_{a+1} ≠ 0`, since `kmtProj` is only approximately idempotent).  Hence, in the
pairing of `Σ_{i∈I}Δ_if` with a test function, the annuli only "talk" to their two neighbours, and
the classical Littlewood--Paley duality argument applies verbatim:

* `⟨Σ_{i∈I}Δ_if, g⟩ = Σ_{i∈I}⟨f, Δ_ig⟩` (self-adjointness of `Δ_i`, `annulus_inner_swap`);
* the banded structure turns `Δ_ig` into the sum of its three neighbours' projections;
* pointwise Cauchy--Schwarz in `i`, Hölder, and the *proved* forward square-function bound
  `Work.KMTAreas.A7Lpd.bandSquareUnif` at the dual exponent `p'` close the estimate.

Everything used is available in the tree (`A7Hi/AnnuliOrthogonal.lean`,
`A7Hi/nestingClean.lean`, `A7Lpd/bandSquareAll.lean`,
`Analysis/Interpolation/eLpNorm_eq_iSup_simpleFunc_integral.lean`).
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A7Lpd.bandSquareAll
import Submission.Work.KMTAreas.A7G.chainPartLowpass

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The increment of the low-pass family -/

/-- The increment of the low-pass family: `dInc ρ l m₀ k f = T_{k+1} f - T_k f`,
`T_k = lpf ρ l m₀ k`. -/
noncomputable def dInc (ρ : ℝ) (l m₀ k : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => lpf ρ l m₀ (k + 1) f x - lpf ρ l m₀ k f x

/-! ## Boundedness of the increments -/

/-! ## The banded annihilation `Δ_a ∘ Δ_b = 0` for `|a - b| ≥ 2` -/

/-! ## Self-adjointness of the increments for a *bounded* test function

`A7Hi.AnnuliOrthogonal.annulus_inner_swap` gives the conjugated self-adjointness of `Δ_k` when
*both* arguments are finitely supported.  The Littlewood--Paley argument below needs it with the test
function only *bounded* (the intermediate functions `Δ_j g` are band-limited but spread out), so we
generalize it here by the same double-sum computation. -/

/-- A finite sum of summable families is summable. -/
lemma summable_finset_sum' {ι : Type*} {s : Finset ι} {c : ι → ℤ → ℂ}
    (h : ∀ m ∈ s, Summable (c m)) : Summable (fun n : ℤ => ∑ m ∈ s, c m n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [summable_zero]
  | insert a s has ih =>
      have h1 : Summable (c a) := h a (Finset.mem_insert_self a s)
      have h2 : Summable (fun n : ℤ => ∑ m ∈ s, c m n) :=
        ih fun m hm => h m (Finset.mem_insert_of_mem hm)
      refine (h1.add h2).congr fun n => ?_
      simp only [Pi.add_apply, Finset.sum_insert has]

/-- **Summability of the pairing of an IW convolution with a bounded test function.** -/
lemma iwConv_summable_mul_star_bounded {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {f v : ℤ → ℂ}
    (hK : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖)
    (hf : (Function.support f).Finite) {B : ℝ} (hv : ∀ n : ℤ, ‖v n‖ ≤ B) :
    Summable fun n : ℤ => Work.Analysis.IWMultiplier.iwConv A Φ f n * star (v n) := by
  classical
  set K : ℤ → ℂ := fun j => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j with hKdef
  have hf0 : ∀ m : ℤ, m ∉ hf.toFinset → f m = 0 := fun m hm => by
    by_contra hne; exact hm (hf.mem_toFinset.mpr hne)
  have hKshift : ∀ m : ℤ, Summable fun n : ℤ => ‖K (n - m)‖ := by
    intro m
    have h2 : Summable fun j : ℤ => ‖K (j + (-m))‖ :=
      hK.comp_injective (add_left_injective (-m))
    simpa only [sub_eq_add_neg] using h2
  have hterm : ∀ m : ℤ, Summable fun n : ℤ => (K (n - m) * f m) * star (v n) := by
    intro m
    have hb : ∀ n : ℤ, ‖(K (n - m) * f m) * star (v n)‖
        ≤ ‖K (n - m)‖ * (‖f m‖ * max B 0) := by
      intro n
      rw [norm_mul, norm_mul, norm_star, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((hv n).trans (le_max_left _ _))
          (norm_nonneg _)) (norm_nonneg _)
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
      ((hKshift m).mul_right (‖f m‖ * max B 0)))
  have hsum : Summable fun n : ℤ => ∑ m ∈ hf.toFinset, (K (n - m) * f m) * star (v n) :=
    summable_finset_sum' fun m _ => hterm m
  refine hsum.congr fun n => ?_
  rw [Work.Analysis.IWMultiplier.iwConv_apply_eq_sum A Φ f hf.toFinset hf0 n, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by rw [smul_eq_mul]

/-! ## Linearity of `lpf` over finite sums, and the annulus expansion -/

/-- **Linearity of `lpf` over a finite sum of bounded functions** (via the linear extension
`Work.KMTAreas.A5.piHat`). -/
lemma lpf_sum {ρ : ℝ} {l m₀ : ℕ} (k : ℕ) {s : Finset ℕ} (a : ℕ → ℤ → ℂ) {B : ℝ}
    (ha : ∀ j ∈ s, ∀ y : ℤ, ‖a j y‖ ≤ B)
    (hsum : ∀ y : ℤ, ‖∑ j ∈ s, a j y‖ ≤ B) :
    lpf ρ l m₀ k (fun y : ℤ => ∑ j ∈ s, a j y)
      = fun y : ℤ => ∑ j ∈ s, lpf ρ l m₀ k (a j) y := by
  have h1 : lpf ρ l m₀ k (fun y : ℤ => ∑ j ∈ s, a j y)
      = Work.KMTAreas.A5.piHat ρ l (-(m₀ + k : ℤ)) (fun y : ℤ => ∑ j ∈ s, a j y) := by
    rw [show lpf ρ l m₀ k = Work.KMTContract.kmtProj ρ l (-(m₀ + k : ℤ)) from rfl,
      Work.KMTAreas.A5.piHat_of_bounded ρ l (-(m₀ + k : ℤ)) ⟨B, hsum⟩]
  have h2 : Work.KMTAreas.A5.piHat ρ l (-(m₀ + k : ℤ)) (fun y : ℤ => ∑ j ∈ s, a j y)
      = ∑ j ∈ s, Work.KMTAreas.A5.piHat ρ l (-(m₀ + k : ℤ)) (a j) := by
    have hfun : (fun y : ℤ => ∑ j ∈ s, a j y) = ∑ j ∈ s, a j := by
      funext y; rw [Finset.sum_apply]
    rw [hfun, map_sum]
  rw [h1, h2]
  funext y
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Work.KMTAreas.A5.piHat_of_bounded ρ l (-(m₀ + k : ℤ)) ⟨B, fun y => ha j hj y⟩]
  rfl

/-! ## Preparing the Cauchy--Schwarz step -/

/-- A finitely supported function is bounded. -/
lemma finsupp_bounded {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    ∃ B : ℝ, ∀ y : ℤ, ‖f y‖ ≤ B := by
  classical
  refine ⟨∑ y ∈ hf.toFinset, ‖f y‖, fun y => ?_⟩
  by_cases hy : y ∈ hf.toFinset
  · exact Finset.single_le_sum (fun i _ => norm_nonneg _) hy
  · have h0 : f y = 0 := by
      by_contra hne; exact hy (hf.mem_toFinset.mpr hne)
    rw [h0, norm_zero]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _

/-- The three-element index set of the neighbours of `i` below `K`. -/
def nbrs (i K : ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun j => j = i - 1 ∨ j = i ∨ j = i + 1)

/-- A bounded factor times a finitely supported function is summable. -/
lemma summable_finsupp_mul_bounded {f h : ℤ → ℂ} (hf : (Function.support f).Finite)
    {B : ℝ} (hh : ∀ x : ℤ, ‖h x‖ ≤ B) : Summable fun x : ℤ => f x * h x := by
  classical
  refine Summable.of_norm ?_
  exact summable_of_ne_finset_zero (s := hf.toFinset) fun x hx => by
    have h0 : f x = 0 := by by_contra hne; exact hx (hf.mem_toFinset.mpr hne)
    rw [h0, zero_mul, norm_zero]

/-! ## Cauchy--Schwarz for finite sums of `ℝ≥0∞` -/

/-- **Cauchy--Schwarz (`(2,2)` Hoelder) for finite sums of `ℝ≥0∞`**, obtained from
`ENNReal.lintegral_mul_le_Lp_mul_Lq` with the counting measure (the functions extended by `0`
outside `s`). -/
lemma ENNReal_finset_sum_mul_le {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (s : Finset ι) (a b : ι → ℝ≥0∞) :
    (∑ i ∈ s, a i * b i)
      ≤ (∑ i ∈ s, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑ i ∈ s, b i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    rw [Real.holderConjugate_iff]; norm_num
  set A : ι → ℝ≥0∞ := fun i => if i ∈ s then a i else 0 with hA
  set B : ι → ℝ≥0∞ := fun i => if i ∈ s then b i else 0 with hB
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ι)
    (p := (2 : ℝ)) (q := (2 : ℝ)) hconj (f := A) (g := B)
    (measurable_of_countable A).aemeasurable (measurable_of_countable B).aemeasurable
  have e1 : (∫⁻ i, (A * B) i ∂(Measure.count : Measure ι)) = ∑ i ∈ s, a i * b i := by
    rw [MeasureTheory.lintegral_countable']
    rw [show (∑' i : ι, (A * B) i * Measure.count {i}) = ∑' i : ι, (A * B) i from by
      refine tsum_congr fun i => by rw [MeasureTheory.Measure.count_singleton, mul_one]]
    rw [tsum_eq_sum (s := s) (fun i hi => ?_)]
    · exact Finset.sum_congr rfl fun i hi => by
        simp only [Pi.mul_apply, hA, hB, if_pos hi]
    · simp only [Pi.mul_apply, hA, hB, if_neg hi, zero_mul]
  have e2 : (∫⁻ i, A i ^ (2 : ℝ) ∂(Measure.count : Measure ι)) = ∑ i ∈ s, a i ^ (2 : ℝ) := by
    rw [MeasureTheory.lintegral_countable']
    rw [show (∑' i : ι, A i ^ (2:ℝ) * Measure.count {i}) = ∑' i : ι, A i ^ (2:ℝ) from by
      refine tsum_congr fun i => by rw [MeasureTheory.Measure.count_singleton, mul_one]]
    rw [tsum_eq_sum (s := s) (fun i hi => ?_)]
    · exact Finset.sum_congr rfl fun i hi => by simp only [hA, if_pos hi]
    · simp only [hA, if_neg hi, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  have e3 : (∫⁻ i, B i ^ (2 : ℝ) ∂(Measure.count : Measure ι)) = ∑ i ∈ s, b i ^ (2 : ℝ) := by
    rw [MeasureTheory.lintegral_countable']
    rw [show (∑' i : ι, B i ^ (2:ℝ) * Measure.count {i}) = ∑' i : ι, B i ^ (2:ℝ) from by
      refine tsum_congr fun i => by rw [MeasureTheory.Measure.count_singleton, mul_one]]
    rw [tsum_eq_sum (s := s) (fun i hi => ?_)]
    · exact Finset.sum_congr rfl fun i hi => by simp only [hB, if_pos hi]
    · simp only [hB, if_neg hi, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [e1, e2, e3] at h
  exact h


/-- At most three `i` have a given `j` among their neighbours. -/
lemma card_filter_nbrs_le (I : Finset ℕ) (j : ℕ) :
    ((I.filter (fun i => j = i - 1 ∨ j = i ∨ j = i + 1)).card : ℝ≥0∞) ≤ 3 := by
  classical
  have hsub : I.filter (fun i => j = i - 1 ∨ j = i ∨ j = i + 1)
      ⊆ ({j - 1, j, j + 1} : Finset ℕ) := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    obtain ⟨h1, h2 | h2 | h2⟩ := hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hcard : (I.filter (fun i => j = i - 1 ∨ j = i ∨ j = i + 1)).card
      ≤ ({j - 1, j, j + 1} : Finset ℕ).card := Finset.card_le_card hsub
  have h3 : ({j - 1, j, j + 1} : Finset ℕ).card ≤ 3 := by
    refine (Finset.card_insert_le (j - 1) _).trans ?_
    refine (Nat.add_le_add_right (Finset.card_insert_le j _) 1).trans ?_
    rw [Finset.card_singleton]
  calc ((I.filter (fun i => j = i - 1 ∨ j = i ∨ j = i + 1)).card : ℝ≥0∞)
      ≤ (({j - 1, j, j + 1} : Finset ℕ).card : ℝ≥0∞) := by exact_mod_cast hcard
    _ ≤ 3 := by exact_mod_cast h3

/-- **The overlap bound**: `Σ_{i∈I} Σ_{j ∈ nbrs i K} b_j² ≤ 3 Σ'_j b_j²` — each `j` occurs in at
most three of the sets `nbrs i K`. -/
lemma sum_nbrs_sq_le (I : Finset ℕ) (K : ℕ) (b : ℕ → ℝ≥0∞) :
    (∑ i ∈ I, ∑ j ∈ nbrs i K, b j ^ (2 : ℝ)) ≤ 3 * ∑' j : ℕ, b j ^ (2 : ℝ) := by
  classical
  have h1 : (∑ i ∈ I, ∑ j ∈ nbrs i K, b j ^ (2 : ℝ))
      = ∑ i ∈ I, ∑ j ∈ Finset.range K,
          (if j = i - 1 ∨ j = i ∨ j = i + 1 then b j ^ (2 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nbrs, Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  calc ∑ j ∈ Finset.range K, ∑ i ∈ I,
        (if j = i - 1 ∨ j = i ∨ j = i + 1 then b j ^ (2 : ℝ) else 0)
      = ∑ j ∈ Finset.range K, (b j ^ (2 : ℝ)) * ((I.filter (fun i =>
          j = i - 1 ∨ j = i ∨ j = i + 1)).card : ℝ≥0∞) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (∑ i ∈ I, (if j = i - 1 ∨ j = i ∨ j = i + 1 then b j ^ (2 : ℝ) else 0))
            = ∑ i ∈ I.filter (fun i => j = i - 1 ∨ j = i ∨ j = i + 1), b j ^ (2 : ℝ)
          from (Finset.sum_filter _ _).symm]
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ Finset.range K, (b j ^ (2 : ℝ)) * 3 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (card_filter_nbrs_le I j) bot_le
    _ ≤ 3 * ∑' j : ℕ, b j ^ (2 : ℝ) := by
        rw [show (∑ j ∈ Finset.range K, (b j ^ (2 : ℝ)) * 3)
            = 3 * ∑ j ∈ Finset.range K, b j ^ (2 : ℝ) from by
          rw [← Finset.sum_mul]; ring]
        exact mul_le_mul_of_nonneg_left (ENNReal.sum_le_tsum _) bot_le


/-- `9 ^ (1/2) = 3` in `ℝ≥0∞`. -/
lemma ENNReal_nine_rpow : (9 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 3 := by
  rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 from by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
  norm_num

/-- The cardinality of the neighbour set is at most three. -/
lemma card_nbrs_le (i K : ℕ) : (((nbrs i K).card : ℕ) : ℝ≥0∞) ≤ 3 := by
  classical
  have hsub : nbrs i K ⊆ ({i - 1, i, i + 1} : Finset ℕ) := by
    intro j hj
    simp only [nbrs, Finset.mem_filter] at hj
    obtain ⟨h1, h2 | h2 | h2⟩ := hj
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hcard : (nbrs i K).card ≤ ({i - 1, i, i + 1} : Finset ℕ).card := Finset.card_le_card hsub
  have h3 : ({i - 1, i, i + 1} : Finset ℕ).card ≤ 3 := by
    refine (Finset.card_insert_le (i - 1) _).trans ?_
    refine (Nat.add_le_add_right (Finset.card_insert_le i _) 1).trans ?_
    rw [Finset.card_singleton]
  exact_mod_cast hcard.trans h3

/-- **The pointwise Cauchy--Schwarz bound** for the banded neighbour structure:
`Σ_{i∈I} Σ_{j ∈ nbrs i K} a_i b_j ≤ 3 (Σ_{i∈I} a_i²)^{1/2} (Σ'_j b_j²)^{1/2}`. -/
lemma pointwise_cs_nbrs (I : Finset ℕ) (K : ℕ) (a b : ℕ → ℝ≥0∞) :
    (∑ i ∈ I, ∑ j ∈ nbrs i K, a i * b j)
      ≤ 3 * (∑ i ∈ I, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑' j : ℕ, b j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  -- the per-`i` bound on the neighbour sum
  have hci : ∀ i : ℕ, (∑ j ∈ nbrs i K, b j) ^ (2 : ℝ) ≤ 3 * ∑ j ∈ nbrs i K, b j ^ (2 : ℝ) := by
    intro i
    refine (ENNReal.rpow_sum_le_const_mul_sum_rpow (nbrs i K) b h2).trans ?_
    rw [show (2 : ℝ) - 1 = 1 from by norm_num, ENNReal.rpow_one]
    exact mul_le_mul_of_nonneg_right (card_nbrs_le i K) bot_le
  -- rewrite the double sum as a pairing of `a` with the neighbour sums
  have h1 : (∑ i ∈ I, ∑ j ∈ nbrs i K, a i * b j)
      = ∑ i ∈ I, a i * (∑ j ∈ nbrs i K, b j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [h1]
  refine (ENNReal_finset_sum_mul_le I a fun i => ∑ j ∈ nbrs i K, b j).trans ?_
  -- bound the `i`-square function
  have hsq : (∑ i ∈ I, (∑ j ∈ nbrs i K, b j) ^ (2 : ℝ)) ≤ 9 * ∑' j : ℕ, b j ^ (2 : ℝ) :=
    (Finset.sum_le_sum fun i _ => hci i).trans (by
      rw [show (∑ i ∈ I, 3 * ∑ j ∈ nbrs i K, b j ^ (2 : ℝ))
          = 3 * ∑ i ∈ I, ∑ j ∈ nbrs i K, b j ^ (2 : ℝ) from by
        rw [Finset.mul_sum]]
      calc 3 * ∑ i ∈ I, ∑ j ∈ nbrs i K, b j ^ (2 : ℝ)
          ≤ 3 * (3 * ∑' j : ℕ, b j ^ (2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_nbrs_sq_le I K b) bot_le
        _ = 9 * ∑' j : ℕ, b j ^ (2 : ℝ) := by ring)
  calc (∑ i ∈ I, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑ i ∈ I, (∑ j ∈ nbrs i K, b j) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∑ i ∈ I, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (9 * ∑' j : ℕ, b j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hsq (by norm_num)) bot_le
    _ = 3 * (∑ i ∈ I, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑' j : ℕ, b j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg 9 _ (by norm_num), ENNReal_nine_rpow]
        rw [← mul_assoc, mul_comm _ (3 : ℝ≥0∞), mul_assoc]


/-- The `Σ'`-to-`∫⁻` conversion for the counting measure on `ℤ`. -/
lemma tsum_eq_lintegral_count (u : ℤ → ℝ≥0∞) :
    (∑' x : ℤ, u x) = ∫⁻ x : ℤ, u x ∂Measure.count := by
  rw [MeasureTheory.lintegral_countable']
  refine tsum_congr fun x => ?_
  rw [MeasureTheory.Measure.count_singleton, mul_one]

/-- The partial sum of the increments over `I`. -/
def partSum (ρ : ℝ) (l m₀ : ℕ) (I : Finset ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑ i ∈ I, dInc ρ l m₀ i f x

/-- The restricted band-pass square function over `I`. -/
def partSq (ρ : ℝ) (l m₀ : ℕ) (I : Finset ℕ) (f : ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  fun x => (∑ i ∈ I, ‖dInc ρ l m₀ i f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- `sqFun` is the `Σ'`-square function of the increments. -/
lemma sqFun_eq_tsum_dInc (ρ : ℝ) (l m₀ : ℕ) (g : ℤ → ℂ) :
    Work.KMTAreas.A7Hi.sqFun ρ l m₀ g
      = fun x : ℤ => (∑' j : ℕ, ‖dInc ρ l m₀ j g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  funext x
  simp only [Work.KMTAreas.A7Hi.sqFun, dInc, Pi.sub_apply]

end

end Work.KMTAreas.A7Hi
