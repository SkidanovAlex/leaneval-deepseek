import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLComp.Hopf_inequality
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Core.hopf_cc_approx
import Submission.Work.EKLC6Core.hopf_cc_uniform
import Submission.Work.EKLC6Core.hopf_cesaro_bound

/-!
# `Work.EKLC6Core.hopf_saturate` — the Hopf argument (Pisa 7.20)

For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the diagonal map
`T = aDiag t ·`, every strictly `T`-invariant measurable set `C` admits a Borel set `C'` with
`μ (C Δ C') = 0` which is invariant under the whole stable horospherical subgroup
`Uminus t = G⁻(t)`, in the strong form `u • C' = C'` for all `u ∈ Uminus t`.

The proof is the classical Hopf argument, in the form of Pisa Lemma 7.20 / proof 7.21:

* pick continuous compactly supported `fₙ` with `∫ |fₙ - 1_C| ≤ 2^{-(n+3)}`
  (`hopf_cc_approx`), so `fₙ` is uniformly continuous for the `G`-action (`hopf_cc_uniform`);
* put `Aₙ = hopfSet T fₙ = {x | ∃ q ∈ ℚ, q > 1/2 ∧ ∀ᶠ k, q < birkA T fₙ k x}`; this set is
  `Uminus t`-invariant, since the Cesàro averages of `fₙ` at `x` and at `u • x` differ by
  `o(1)` along the flow (`hopf_cesaro_bound`, using that `aDiag t ⁿ u (aDiag t ⁿ)⁻¹ → 1`);
* the maximal ergodic inequality for `T` bounds `μ (C Δ Aₙ) ≤ 8 ∫ |fₙ - 1_C|` (`measure_hopfSet_diff`),
  where the pointwise ergodic theorem is used to discard the null set of non-convergence;
* finally `C' = limsup Aₙ` is Borel and `Uminus t`-invariant, and `μ (C Δ C') = 0` by
  Borel–Cantelli with the summable bounds above.
-/

open MeasureTheory Filter Topology
open scoped ENNReal symmDiff
open Work.EKLContract

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLComp.Birkhoff

/-! ## The Hopf set -/

/-- The set of points at which the Birkhoff averages of `f` along `T` are eventually above a
rational level `> 1/2`. -/
def hopfSet (T : X3 → X3) (f : X3 → ℝ) : Set X3 :=
  {x | ∃ q : ℚ, (1/2 : ℝ) < q ∧ ∀ᶠ k : ℕ in atTop, (q : ℝ) < birkA T f k x}

theorem hopf_birkA_measurable {T : X3 → X3} (hT : Measurable T) {f : X3 → ℝ} (hf : Measurable f)
    (k : ℕ) : Measurable (fun x => birkA T f k x) := by
  have h : (fun x => birkA T f k x) = fun x => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, f (T^[i] x) := by
    funext x; rw [birkA_def]
  rw [h]
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (hT.iterate i))).const_mul _

theorem measurableSet_hopfSet {T : X3 → X3} (hT : Measurable T) {f : X3 → ℝ}
    (hf : Measurable f) : MeasurableSet (hopfSet T f) := by
  have hmain : hopfSet T f = ⋃ q : {q : ℚ // (1/2 : ℝ) < (q : ℝ)},
      ⋃ N : ℕ, ⋂ k ∈ Set.Ici N, {x | ((q : ℚ) : ℝ) < birkA T f k x} := by
    ext x
    simp only [hopfSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici,
      Subtype.exists, exists_prop]
    constructor
    · rintro ⟨q, hq, hqk⟩
      obtain ⟨N, hN⟩ := eventually_atTop.mp hqk
      exact ⟨q, hq, N, fun k hk => hN k hk⟩
    · rintro ⟨q, hq, N, hN⟩
      exact ⟨q, hq, eventually_atTop.mpr ⟨N, fun k hk => hN k hk⟩⟩
  rw [hmain]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (hopf_birkA_measurable hT hf k)

/-! ## Invariance of the Hopf set under `Uminus t` -/

theorem smul_mem_hopfSet (t : Fin 3 → ℝ) {u : SL3} (hu : u ∈ Uminus t) {f : X3 → ℝ}
    (hf : ∀ ε > 0, ∃ W : Set SL3, IsOpen W ∧ (1 : SL3) ∈ W ∧
      ∀ v ∈ W, ∀ x : X3, |f (v • x) - f x| ≤ ε)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (x : X3) :
    x ∈ hopfSet (fun y : X3 => aDiag t • y) f →
      u • x ∈ hopfSet (fun y : X3 => aDiag t • y) f := by
  rintro ⟨q, hq, hqk⟩
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (show (1/2 : ℝ) < (q : ℝ) from hq)
  set ε : ℝ := ((q : ℝ) - (q' : ℝ)) / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  obtain ⟨K, hK⟩ := hopf_cesaro_bound t hu hf hB x hε
  refine ⟨q', hq'1, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hqk
  rw [eventually_atTop]
  refine ⟨max K N, fun k hk => ?_⟩
  have hk1 : K ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : N ≤ k := le_trans (le_max_right _ _) hk
  have h2 := hK k hk1
  have h1 := hN k hk2
  have habs := abs_le.mp h2
  have hqq' : (q' : ℝ) < (q : ℝ) - ε := by simp only [hεdef]; linarith
  linarith [habs.1, habs.2, h1]

theorem image_smul_hopfSet (t : Fin 3 → ℝ) {u : SL3} (hu : u ∈ Uminus t) {f : X3 → ℝ}
    (hf : ∀ ε > 0, ∃ W : Set SL3, IsOpen W ∧ (1 : SL3) ∈ W ∧
      ∀ v ∈ W, ∀ x : X3, |f (v • x) - f x| ≤ ε)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (fun x : X3 => u • x) '' hopfSet (fun y : X3 => aDiag t • y) f
      = hopfSet (fun y : X3 => aDiag t • y) f := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact smul_mem_hopfSet t hu hf hB x hx
  · intro y hy
    exact ⟨u⁻¹ • y, smul_mem_hopfSet t (inv_mem hu) hf hB y hy, smul_inv_smul u y⟩

/-! ## Birkhoff sums against the invariant indicator -/

theorem hopf_indicator_iterate_eq {T : X3 → X3} {C : Set X3} (hinv : T ⁻¹' C = C) (i : ℕ) (x : X3) :
    C.indicator (fun _ => (1:ℝ)) (T^[i] x) = C.indicator (fun _ => (1:ℝ)) x := by
  have hiff : ∀ y : X3, T y ∈ C ↔ y ∈ C := fun y => by
    have h : y ∈ T ⁻¹' C ↔ y ∈ C := by rw [hinv]
    simpa using h
  have hmem : T^[i] x ∈ C ↔ x ∈ C := by
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply']; exact (hiff _).trans ih
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]

theorem hopf_birkA_indicator_eq {T : X3 → X3} {C : Set X3} (hinv : T ⁻¹' C = C) {k : ℕ}
    (hk : k ≠ 0) (x : X3) :
    birkA T (C.indicator (fun _ => (1:ℝ))) k x = C.indicator (fun _ => (1:ℝ)) x := by
  rw [birkA_def]
  have hsum : (∑ i ∈ Finset.range k, C.indicator (fun _ => (1:ℝ)) (T^[i] x))
      = k • C.indicator (fun _ => (1:ℝ)) x := by
    rw [Finset.sum_congr rfl (fun i _ => hopf_indicator_iterate_eq hinv i x), Finset.sum_const,
      Finset.card_range]
  rw [hsum, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk), one_mul]

theorem hopf_birkA_sub_indicator {T : X3 → X3} {C : Set X3} (hinv : T ⁻¹' C = C) {f : X3 → ℝ}
    {k : ℕ} (hk : k ≠ 0) (x : X3) :
    birkA T (fun y => f y - C.indicator (fun _ => (1:ℝ)) y) k x
      = birkA T f k x - C.indicator (fun _ => (1:ℝ)) x := by
  rw [Work.EKLComp.birkA_sub, hopf_birkA_indicator_eq hinv hk x]

theorem hopf_birkhoffSum_eq_mul_birkA {T : X3 → X3} (F : X3 → ℝ) {k : ℕ} (hk : k ≠ 0) (x : X3) :
    birkhoffSum T F k x = (k : ℝ) * birkA T F k x := by
  rw [birkA_def, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), one_mul]
  rfl

theorem hopf_birkhoffSum_le_abs_sum {T : X3 → X3} (F : X3 → ℝ) (k : ℕ) (x : X3) :
    birkhoffSum T F k x ≤ birkhoffSum T (fun y => |F y|) k x := by
  simp only [birkhoffSum]
  exact Finset.sum_le_sum fun i _ => le_abs_self _

theorem abs_hopf_birkhoffSum_le_abs_sum {T : X3 → X3} (F : X3 → ℝ) (k : ℕ) (x : X3) :
    |birkhoffSum T F k x| ≤ birkhoffSum T (fun y => |F y|) k x := by
  simp only [birkhoffSum]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## The measure estimate -/

theorem measure_hopfSet_diff {T : X3 → X3} (hT : Measurable T)
    {μ : Measure X3} [IsProbabilityMeasure μ] (hmp : MeasurePreserving T μ μ)
    {C : Set X3} (hC : MeasurableSet C) (hinv : T ⁻¹' C = C)
    {f : X3 → ℝ} (hfmeas : Measurable f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    μ (C \ hopfSet T f) ≤
        ENNReal.ofReal (4 * ∫ x, |f x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) ∧
      μ (hopfSet T f \ C) ≤
        ENNReal.ofReal (4 * ∫ x, |f x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) := by
  set F : X3 → ℝ := fun x => f x - C.indicator (fun _ => (1:ℝ)) x with hFdef
  have hFmeas : Measurable F := hfmeas.sub (Measurable.indicator measurable_const hC)
  have hFbound : ∀ x, |F x| ≤ 1 := by
    intro x
    simp only [hFdef]
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx (fun _ => (1:ℝ)), abs_le]
      constructor <;> linarith [(hf01 x).1, (hf01 x).2]
    · rw [Set.indicator_of_notMem hx (fun _ => (1:ℝ)), abs_le]
      constructor <;> linarith [(hf01 x).1, (hf01 x).2]
  have hFint : Integrable F μ :=
    Integrable.of_bound hFmeas.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFbound x)
  have hfint : Integrable f μ :=
    Integrable.of_bound hfmeas.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]; exact (hf01 x).2)
  have hgint : Integrable (fun x => |F x|) μ := hFint.abs
  have hgnonneg : ∀ x, 0 ≤ |F x| := fun x => abs_nonneg _
  have hS_le : μ {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ) < birkhoffSum T (fun y => |F y|) k x}
      ≤ ENNReal.ofReal (4 * ∫ x, |F x| ∂μ) := by
    have h := Work.EKLComp.hopfIneq_maximal_weak_type μ T hmp (fun y => |F y|) hgint hgnonneg (1/4)
      (by norm_num)
    rwa [show (∫ x, |F x| ∂μ) / (1/4) = 4 * ∫ x, |F x| ∂μ from by ring] at h
  have hNF : μ {x | ¬ ∃ l : ℝ, Tendsto (fun k => birkA T f k x) atTop (𝓝 l)} = 0 := by
    have hb := Work.EKLComp.birkhoff_all μ T hmp f hfint
    rw [ae_iff] at hb
    refine measure_mono_null ?_ hb
    rintro x hx hc
    exact hx ⟨_, hc⟩
  have hsubA : hopfSet T f \ C ⊆
      {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ) < birkhoffSum T (fun y => |F y|) k x} := by
    rintro x ⟨hx, hxC⟩
    obtain ⟨q, hq, hqk⟩ := hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp hqk
    set k : ℕ := max N 1 with hkdef
    have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    have h1 : (q : ℝ) < birkA T f k x := hN k (le_max_left _ _)
    have h2 : birkA T F k x = birkA T f k x := by
      rw [hFdef, hopf_birkA_sub_indicator hinv hkne x, Set.indicator_of_notMem hxC (fun _ => (1:ℝ)),
        sub_zero]
    have h3 : (1/4 : ℝ) < birkA T F k x := by rw [h2]; linarith
    refine ⟨k, hkpos, ?_⟩
    have h4 : (1/4 : ℝ) * (k : ℝ) < birkhoffSum T F k x := by
      rw [hopf_birkhoffSum_eq_mul_birkA F hkne x]
      calc (1/4 : ℝ) * (k : ℝ) < birkA T F k x * (k : ℝ) :=
            mul_lt_mul_of_pos_right h3 (Nat.cast_pos.mpr hkpos)
        _ = (k : ℝ) * birkA T F k x := by ring
    exact lt_of_lt_of_le h4 (hopf_birkhoffSum_le_abs_sum F k x)
  have hsubB : C \ hopfSet T f ⊆
      {x | ¬ ∃ l : ℝ, Tendsto (fun k => birkA T f k x) atTop (𝓝 l)}
        ∪ {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ) < birkhoffSum T (fun y => |F y|) k x} := by
    rintro x ⟨hxC, hxnot⟩
    by_cases hlim : ∃ l : ℝ, Tendsto (fun k => birkA T f k x) atTop (𝓝 l)
    · right
      obtain ⟨l, hl⟩ := hlim
      have hlq : ∀ q : ℚ, (1/2 : ℝ) < (q : ℝ) → l ≤ (q : ℝ) := by
        intro q hq
        by_contra hcon
        push_neg at hcon
        have hev : ∀ᶠ k : ℕ in atTop, (q : ℝ) < birkA T f k x :=
          (tendsto_order.mp hl).1 (q : ℝ) hcon
        have hne : ¬ (∀ᶠ k : ℕ in atTop, (q : ℝ) < birkA T f k x) :=
          fun hc => hxnot ⟨q, hq, hc⟩
        rw [not_eventually] at hne
        obtain ⟨N, hN⟩ := eventually_atTop.mp hev
        obtain ⟨k, hkN, hkq⟩ := frequently_atTop.mp (hne.mono fun k hk => not_lt.mp hk) N
        exact absurd (hN k hkN) (not_lt.mpr hkq)
      have hl12 : l ≤ 1/2 := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
        linarith [hlq q hq1]
      have hconv : Tendsto (fun k : ℕ => birkA T F k x) atTop (𝓝 (l - 1)) := by
        refine Tendsto.congr' ?_ (hl.sub_const 1)
        filter_upwards [eventually_ge_atTop 1] with k hk
        rw [hFdef, hopf_birkA_sub_indicator hinv (Nat.one_le_iff_ne_zero.mp hk) x,
          Set.indicator_of_mem hxC (fun _ => (1:ℝ))]
      have hev : ∀ᶠ k : ℕ in atTop, birkA T F k x < -(1/4 : ℝ) :=
        (tendsto_order.mp hconv).2 (-(1/4)) (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      set k : ℕ := max N 1 with hkdef
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
      have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
      have h1 : birkA T F k x < -(1/4 : ℝ) := hN k (le_max_left _ _)
      refine ⟨k, hkpos, ?_⟩
      have h2 : (1/4 : ℝ) < |birkA T F k x| := by
        rw [abs_of_neg (by linarith)]; linarith
      have h3 : (1/4 : ℝ) * (k : ℝ) < |birkhoffSum T F k x| := by
        rw [hopf_birkhoffSum_eq_mul_birkA F hkne x, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
        calc (1/4 : ℝ) * (k : ℝ) = (k : ℝ) * (1/4) := by ring
          _ < (k : ℝ) * |birkA T F k x| :=
              mul_lt_mul_of_pos_left h2 (Nat.cast_pos.mpr hkpos)
      exact lt_of_lt_of_le h3 (abs_hopf_birkhoffSum_le_abs_sum F k x)
    · exact Or.inl hlim
  constructor
  · calc μ (C \ hopfSet T f)
        ≤ μ ({x | ¬ ∃ l : ℝ, Tendsto (fun k => birkA T f k x) atTop (𝓝 l)}
            ∪ {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ)
                < birkhoffSum T (fun y => |F y|) k x}) := measure_mono hsubB
      _ ≤ μ {x | ¬ ∃ l : ℝ, Tendsto (fun k => birkA T f k x) atTop (𝓝 l)}
            + μ {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ)
                < birkhoffSum T (fun y => |F y|) k x} := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (4 * ∫ x, |F x| ∂μ) := add_le_add (le_of_eq hNF) hS_le
      _ = ENNReal.ofReal (4 * ∫ x, |F x| ∂μ) := zero_add _
      _ = ENNReal.ofReal (4 * ∫ x, |f x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) := by rw [hFdef]
  · calc μ (hopfSet T f \ C)
        ≤ μ {x | ∃ k : ℕ, 0 < k ∧ (1/4 : ℝ) * (k : ℝ)
            < birkhoffSum T (fun y => |F y|) k x} := measure_mono hsubA
      _ ≤ ENNReal.ofReal (4 * ∫ x, |F x| ∂μ) := hS_le
      _ = ENNReal.ofReal (4 * ∫ x, |f x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) := by rw [hFdef]

/-- The symmetric difference of `C` with a limit superior is contained in the limit superior of
the symmetric differences. -/
theorem hopf_symmDiff_limsup_subset {α : Type*} (A : ℕ → Set α) (C : Set α) :
    symmDiff C (limsup A atTop) ⊆ limsup (fun n => symmDiff C (A n)) atTop := by
  intro y hy
  rw [mem_limsup_iff_frequently_mem]
  rcases Set.mem_symmDiff.mp hy with ⟨hC, hyC'⟩ | ⟨hyC, hC⟩
  · rw [mem_limsup_iff_frequently_mem, not_frequently] at hyC'
    exact (show ∀ᶠ n in atTop, y ∈ symmDiff C (A n) from by
      filter_upwards [hyC'] with n hn
      exact Set.mem_symmDiff.mpr (Or.inl ⟨hC, hn⟩)).frequently
  · rw [mem_limsup_iff_frequently_mem] at hyC
    exact hyC.mono fun n hn => Set.mem_symmDiff.mpr (Or.inr ⟨hn, hC⟩)

end Work.EKLC6Core

namespace Work.EKLC6Core

theorem hopf_saturate {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {C : Set Work.EKLContract.X3} (hC : MeasurableSet C)
    (hinv : (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' C = C) :
    ∃ C' : Set Work.EKLContract.X3, MeasurableSet C' ∧
      (∀ u : Work.EKLContract.SL3, u ∈ Work.EKLC6Core.Uminus t →
        (fun x : Work.EKLContract.X3 => u • x) '' C' = C') ∧
      μ (C \ C') = 0 ∧ μ (C' \ C) = 0 := by
  let T : X3 → X3 := fun x : X3 => aDiag t • x
  have hTmeas : Measurable T := (continuous_const_smul (aDiag t)).measurable
  have hchoice : ∀ n : ℕ, ∃ f : X3 → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∫ x, |f x - C.indicator (fun _ => (1:ℝ)) x| ∂μ ≤ (1/2 : ℝ) ^ (n + 3) :=
    fun n => hopf_cc_approx μ hC (by positivity)
  choose f hfcont hfcs hf01 hfapp using hchoice
  have hunif : ∀ n : ℕ, ∀ ε > 0, ∃ W : Set SL3, IsOpen W ∧ (1 : SL3) ∈ W ∧
      ∀ v ∈ W, ∀ x : X3, |f n (v • x) - f n x| ≤ ε :=
    fun n => hopf_cc_uniform (hfcont n) (hfcs n)
  have hbdd : ∀ n : ℕ, ∀ x : X3, |f n x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (hf01 n x).1]; exact (hf01 n x).2
  have hmeas : ∀ n : ℕ, MeasurableSet (hopfSet T (f n)) :=
    fun n => measurableSet_hopfSet hTmeas (hfcont n).measurable
  have hinv' : ∀ n : ℕ, ∀ u : SL3, u ∈ Uminus t →
      (fun x : X3 => u • x) '' hopfSet T (f n) = hopfSet T (f n) :=
    fun n u hu => image_smul_hopfSet t hu (hunif n) (hbdd n)
  have hclose : ∀ n : ℕ, μ (symmDiff C (hopfSet T (f n))) ≤ ENNReal.ofReal ((1/2 : ℝ) ^ n) := by
    intro n
    obtain ⟨h1, h2⟩ := measure_hopfSet_diff hTmeas hmp hC hinv (hfcont n).measurable (hf01 n)
    have h3 : ∫ x, |f n x - C.indicator (fun _ => (1:ℝ)) x| ∂μ ≤ (1/2 : ℝ) ^ (n+3) := hfapp n
    have h4 : 0 ≤ ∫ x, |f n x - C.indicator (fun _ => (1:ℝ)) x| ∂μ :=
      integral_nonneg fun x => abs_nonneg _
    have h5 : 0 ≤ (1/2 : ℝ) ^ (n + 3) := by positivity
    calc μ (symmDiff C (hopfSet T (f n)))
        ≤ μ (C \ hopfSet T (f n)) + μ (hopfSet T (f n) \ C) := by
          rw [Set.symmDiff_def]
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * ∫ x, |f n x - C.indicator (fun _ => (1:ℝ)) x| ∂μ)
            + ENNReal.ofReal (4 * ∫ x, |f n x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (8 * ∫ x, |f n x - C.indicator (fun _ => (1:ℝ)) x| ∂μ) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          ring_nf
      _ ≤ ENNReal.ofReal (8 * (1/2 : ℝ) ^ (n + 3)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal ((1/2 : ℝ) ^ n) := by
          congr 1
          rw [pow_add]
          ring
  have hsum : ∑' n : ℕ, μ (symmDiff C (hopfSet T (f n))) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hclose)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)),
      tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
    norm_num
  have hlimsup : μ (limsup (fun n => symmDiff C (hopfSet T (f n))) atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsum
  set C' : Set X3 := limsup (fun n => hopfSet T (f n)) atTop with hC'def
  have hC'meas : MeasurableSet C' := by
    rw [hC'def, Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => hmeas n
  have hC'inv : ∀ u : SL3, u ∈ Uminus t → (fun x : X3 => u • x) '' C' = C' := by
    intro u hu
    rw [hC'def]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_limsup_iff_frequently_mem] at hx ⊢
      refine hx.mono fun n hn => ?_
      show u • x ∈ hopfSet T (f n)
      rw [← hinv' n u hu]
      exact ⟨x, hn, rfl⟩
    · intro hy
      refine ⟨u⁻¹ • y, ?_, smul_inv_smul u y⟩
      rw [mem_limsup_iff_frequently_mem] at hy ⊢
      refine hy.mono fun n hn => ?_
      show u⁻¹ • y ∈ hopfSet T (f n)
      rw [← hinv' n u⁻¹ (inv_mem hu)]
      exact ⟨y, hn, rfl⟩
  have hC'diff : symmDiff C C' ⊆ limsup (fun n => symmDiff C (hopfSet T (f n))) atTop := by
    rw [hC'def]
    exact hopf_symmDiff_limsup_subset _ C
  refine ⟨C', hC'meas, hC'inv, ?_, ?_⟩
  · refine measure_mono_null (fun x hx => hC'diff ?_) hlimsup
    exact Set.mem_symmDiff.mpr (Or.inl ⟨hx.1, hx.2⟩)
  · refine measure_mono_null (fun x hx => hC'diff ?_) hlimsup
    exact Set.mem_symmDiff.mpr (Or.inr ⟨hx.1, hx.2⟩)

end Work.EKLC6Core

end
