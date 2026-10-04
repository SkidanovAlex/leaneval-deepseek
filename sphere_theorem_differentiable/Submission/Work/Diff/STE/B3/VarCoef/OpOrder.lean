import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.flatCut_CSqZ_le
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An "order calculus" for operators on the flat torus (`VarCoef` layer)

This file sets up the vocabulary for the flat commutation estimate
`Work.Diff.STE.B3.VarCoef.varLapPow_cut_comm_pairing`.

An **operator** `Op ι` is a function `((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ)`, i.e. an arbitrary map on the
space of functions on the unit torus.  The relevant ones (`mulOp`, `pdOp`, `cutOp`) are ℂ-linear on
smooth periodic functions and preserve them; the predicate `IsOrd d C T` records both of these
facts together with the *order* bound

  `CSqZ (t - d) (fourierCoeff (T f)) ≤ C * CSqZ t (fourierCoeff f)`   for every `t : ℤ`

on the weighted integer Sobolev scale `CSqZ`.  Orders are integers: `d = 2` for the
variable-coefficient Laplacian, `d = 1` for a partial derivative, `d = 0` for a multiplication or
the Friedrichs cutoff, and `d = -1` for the commutator `[M_m, S_ε]`, which *gains* a derivative.

The file contains (a) the closure properties of `IsOrd` (composition, sums, negation, monotonicity
in the order and in the constant) with *explicit* constants, so that all the estimates are
manifestly uniform in the cutoff parameter `ε`, and (b) the Leibniz identity for commutators of
compositions, which is what turns an order bound for `[T,D]` into one for `[T, D^k]`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Operators on the space of functions on the flat torus. -/
abbrev Op (ι : Type*) := ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ)

/-- Smooth `1`-periodic functions. -/
def SmoothPer (f : (ι → ℝ) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ Work.Diff.STE.Periodic1 f

/-- The pointwise description of a finite sum of functions. -/
theorem finset_sum_apply_eq {κ α β : Type*} [AddCommMonoid β] (s : Finset κ) (F : κ → α → β) :
    (∑ i ∈ s, F i : α → β) = fun x => ∑ i ∈ s, F i x := by
  funext x
  exact Finset.sum_apply x s F

/-- An operator sum applied to a function, pointwise. -/
theorem finset_sumOp_apply {κ : Type*} (s : Finset κ) (T : κ → Op ι)
    (f : (ι → ℝ) → ℂ) : (∑ i ∈ s, T i) f = fun x => ∑ i ∈ s, T i f x := by
  funext x
  rw [Finset.sum_apply, Finset.sum_apply]

/-- A finite sum of summable coefficient families is summable. -/
theorem Summable.finset_sum {κ : Type*} {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    [ContinuousAdd β] (s : Finset κ) (f : κ → (ι → ℤ) → β)
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun k => ∑ i ∈ s, f i k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (summable_zero : Summable (fun _ : ι → ℤ => (0 : β)))
  | insert a s ha ih =>
      have hstep : (fun k : ι → ℤ => ∑ i ∈ insert a s, f i k)
          = fun k : ι → ℤ => f a k + ∑ i ∈ s, f i k := by
        funext k
        rw [Finset.sum_insert ha]
      rw [hstep]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## 1. The class of test functions -/

theorem SmoothPer.contDiff {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    ContDiff ℝ (⊤ : ℕ∞) f := hf.1

theorem SmoothPer.periodic {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    Work.Diff.STE.Periodic1 f := hf.2

theorem SmoothPer.continuous {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) : Continuous f :=
  hf.1.continuous

theorem SmoothPer.zero : SmoothPer (0 : (ι → ℝ) → ℂ) :=
  ⟨contDiff_const, fun i x => rfl⟩

theorem SmoothPer.add {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f) (hg : SmoothPer g) :
    SmoothPer (f + g) :=
  ⟨hf.1.add hg.1, fun i x => by simp only [Pi.add_apply, hf.2 i x, hg.2 i x]⟩

theorem SmoothPer.neg {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) : SmoothPer (-f) :=
  ⟨hf.1.neg, fun i x => by simp only [Pi.neg_apply, hf.2 i x]⟩

theorem SmoothPer.sub {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f) (hg : SmoothPer g) :
    SmoothPer (f - g) :=
  ⟨hf.1.sub hg.1, fun i x => by simp only [Pi.sub_apply, hf.2 i x, hg.2 i x]⟩

theorem SmoothPer.smul (c : ℂ) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) : SmoothPer (c • f) :=
  ⟨hf.1.const_smul c, fun i x => by simp only [Pi.smul_apply, hf.2 i x]⟩

theorem SmoothPer.mul {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f) (hg : SmoothPer g) :
    SmoothPer (fun x => f x * g x) :=
  ⟨hf.1.mul hg.1, fun i x => by simp only [hf.2 i x, hg.2 i x]⟩

theorem SmoothPer.finset_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → ℝ) → ℂ)
    (h : ∀ i ∈ s, SmoothPer (F i)) : SmoothPer (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h : (fun x : ι → ℝ => ∑ i ∈ (∅ : Finset κ), F i x) = 0 := by
        funext x; simp
      rw [h]; exact SmoothPer.zero
  | insert a s ha ih =>
      have hstep : (fun x : ι → ℝ => ∑ i ∈ insert a s, F i x)
          = fun x : ι → ℝ => F a x + ∑ i ∈ s, F i x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hstep]
      exact SmoothPer.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Summability of the weighted Fourier mass at every integer exponent, for smooth `1`-periodic
functions (`Work.Diff.STE.B3.SymCalcStep8.flatCut_summable_zpow`, restated). -/
theorem SmoothPer.summable_CSqZ {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) (t : ℤ) :
    Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ t * ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) :=
  Work.Diff.STE.B3.SymCalcStep8.flatCut_summable_zpow f hf.1 hf.2 t

/-! ## 2. Linearity of `fourierCoeff` on continuous functions -/

/-- `fourierCoeff` is additive on continuous functions. -/
theorem fourierCoeff_add_of_continuous {f g : (ι → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    Work.Diff.STE.fourierCoeff (fun x => f x + g x)
      = fun k => Work.Diff.STE.fourierCoeff f k + Work.Diff.STE.fourierCoeff g k := by
  funext k
  have h1 : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => f x + g x - g x) k
      = Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => f x + g x) k
        - Work.Diff.STE.fourierCoeff g k :=
    Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ (hf.add hg) hg k
  have h2 : (fun x : ι → ℝ => f x + g x - g x) = f := by funext x; ring
  rw [h2] at h1
  rw [h1]
  abel

/-- `fourierCoeff` is additive over finite sums of continuous functions. -/
theorem fourierCoeff_finset_sum_of_continuous {κ : Type*} (s : Finset κ)
    (F : κ → (ι → ℝ) → ℂ) (hF : ∀ i ∈ s, Continuous (F i)) :
    Work.Diff.STE.fourierCoeff (fun x => ∑ i ∈ s, F i x)
      = fun k => ∑ i ∈ s, Work.Diff.STE.fourierCoeff (F i) k := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext k
      simp only [Finset.sum_empty, Work.Diff.STE.fourierCoeff]
      simp
  | insert a s ha ih =>
      have hsum_cont : Continuous (fun x : ι → ℝ => ∑ i ∈ s, F i x) :=
        continuous_finsetSum s fun i hi => hF i (Finset.mem_insert_of_mem hi)
      funext k
      have hstep : (fun x : ι → ℝ => ∑ i ∈ insert a s, F i x)
          = fun x : ι → ℝ => F a x + ∑ i ∈ s, F i x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hstep, fourierCoeff_add_of_continuous (hF a (Finset.mem_insert_self a s)) hsum_cont,
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]
      rw [Finset.sum_insert ha]

/-- `fourierCoeff` is compatible with negation on continuous functions. -/
theorem fourierCoeff_neg_of_continuous {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    Work.Diff.STE.fourierCoeff (fun x => -f x)
      = fun k => -Work.Diff.STE.fourierCoeff f k := by
  funext k
  have h1 : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => (0 : ℂ) - f x) k
      = Work.Diff.STE.fourierCoeff (0 : (ι → ℝ) → ℂ) k - Work.Diff.STE.fourierCoeff f k :=
    Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ continuous_const hf k
  have h2 : (fun x : ι → ℝ => (0 : ℂ) - f x) = fun x => -f x := by funext x; ring
  rw [h2] at h1
  have h3 : Work.Diff.STE.fourierCoeff (0 : (ι → ℝ) → ℂ) k = 0 := by
    simp only [Work.Diff.STE.fourierCoeff]
    simp
  rw [h1, h3, zero_sub]

/-- `fourierCoeff` is compatible with multiplication by a constant on continuous functions. -/
theorem fourierCoeff_const_mul_of_continuous (c : ℂ) {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    Work.Diff.STE.fourierCoeff (fun x => c * f x)
      = fun k => c * Work.Diff.STE.fourierCoeff f k := by
  funext k
  simp only [Work.Diff.STE.fourierCoeff]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ## 3. The weighted `ℓ²` scale: elementary inequalities -/

/-- `CSqZ` of a sum, with the trivial factor `2`. -/
theorem CSqZ_add_le (t : ℤ) (a b : (ι → ℤ) → ℂ)
    (ha : Summable fun k => (Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2)
    (hb : Summable fun k => (Work.Diff.STE.wt k) ^ t * ‖b k‖ ^ 2) :
    Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => a k + b k)
      ≤ 2 * (Work.Diff.STE.B3.SymCalcStep8.CSqZ t a
          + Work.Diff.STE.B3.SymCalcStep8.CSqZ t b) := by
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖a k + b k‖ ^ 2
      ≤ 2 * ((Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2
          + (Work.Diff.STE.wt k) ^ t * ‖b k‖ ^ 2) := by
    intro k
    have h1 : ‖a k + b k‖ ^ 2 ≤ 2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2) := by
      have h3 := pow_le_pow_left₀ (norm_nonneg (a k + b k)) (norm_add_le (a k) (b k)) 2
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k), norm_nonneg (b k)]
    have h2 : (0 : ℝ) ≤ (Work.Diff.STE.wt k) ^ t :=
      zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t
    calc (Work.Diff.STE.wt k) ^ t * ‖a k + b k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ t * (2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 * ((Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2
            + (Work.Diff.STE.wt k) ^ t * ‖b k‖ ^ 2) := by ring
  have hsumR : Summable (fun k : ι → ℤ => 2 * ((Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2
      + (Work.Diff.STE.wt k) ^ t * ‖b k‖ ^ 2)) := (ha.add hb).mul_left 2
  have hsumL : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t * ‖a k + b k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t) (sq_nonneg _))
      hpt hsumR
  calc Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => a k + b k)
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖a k + b k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, 2 * ((Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2
          + (Work.Diff.STE.wt k) ^ t * ‖b k‖ ^ 2) := Summable.tsum_le_tsum hpt hsumL hsumR
    _ = 2 * (Work.Diff.STE.B3.SymCalcStep8.CSqZ t a
          + Work.Diff.STE.B3.SymCalcStep8.CSqZ t b) := by
        rw [tsum_mul_left, Summable.tsum_add ha hb]
        rfl

/-- `CSqZ` is invariant under negation. -/
theorem CSqZ_neg (t : ℤ) (a : (ι → ℤ) → ℂ) :
    Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => -a k)
      = Work.Diff.STE.B3.SymCalcStep8.CSqZ t a := by
  simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ, norm_neg]

/-- `CSqZ` of a constant multiple: `‖z‖²` factors out. -/
theorem CSqZ_const_mul (t : ℤ) (z : ℂ) (a : (ι → ℤ) → ℂ) :
    Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => z * a k)
      = ‖z‖ ^ 2 * Work.Diff.STE.B3.SymCalcStep8.CSqZ t a := by
  simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ, norm_mul]
  rw [show (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t * (‖z‖ * ‖a k‖) ^ 2)
        = fun k : ι → ℤ => ‖z‖ ^ 2 * ((Work.Diff.STE.wt k) ^ t * ‖a k‖ ^ 2) by
      funext k; ring]
  rw [tsum_mul_left]

/-- The elementary rearrangement used in `CSqZ_finset_sum_le`. -/
theorem mul_mul_finset_sum {κ : Type*} (s : Finset κ) (w n : ℝ) (F : κ → ℝ) :
    w * (n * ∑ i ∈ s, F i) = n * ∑ i ∈ s, w * F i := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `CSqZ` of a finite sum of coefficient families. -/
theorem CSqZ_finset_sum_le {κ : Type*} (t : ℤ) (s : Finset κ) (c : κ → (ι → ℤ) → ℂ)
    (hs : ∀ i ∈ s, Summable fun k => (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2) :
    Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => ∑ i ∈ s, c i k)
      ≤ (s.card : ℝ) * ∑ i ∈ s, Work.Diff.STE.B3.SymCalcStep8.CSqZ t (c i) := by
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖∑ i ∈ s, c i k‖ ^ 2
      ≤ (s.card : ℝ) * ∑ i ∈ s, (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2 := by
    intro k
    have h1 : ‖∑ i ∈ s, c i k‖ ^ 2 ≤ (∑ i ∈ s, ‖c i k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    have h2 : (∑ i ∈ s, ‖c i k‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖c i k‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : (0 : ℝ) ≤ (Work.Diff.STE.wt k) ^ t :=
      zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t
    calc (Work.Diff.STE.wt k) ^ t * ‖∑ i ∈ s, c i k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ t * ((s.card : ℝ) * ∑ i ∈ s, ‖c i k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) h3
      _ = (s.card : ℝ) * ∑ i ∈ s, (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2 :=
          mul_mul_finset_sum s _ _ _
  have hsumR : Summable (fun k : ι → ℤ =>
      (s.card : ℝ) * ∑ i ∈ s, (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2) :=
    (Summable.finset_sum s (fun i k => (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2)
      (fun i hi => hs i hi)).mul_left _
  have hsumL : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t * ‖∑ i ∈ s, c i k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t) (sq_nonneg _))
      hpt hsumR
  calc Work.Diff.STE.B3.SymCalcStep8.CSqZ t (fun k => ∑ i ∈ s, c i k)
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖∑ i ∈ s, c i k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, (s.card : ℝ) * ∑ i ∈ s, (Work.Diff.STE.wt k) ^ t * ‖c i k‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hsumL hsumR
    _ = (s.card : ℝ) * ∑ i ∈ s, Work.Diff.STE.B3.SymCalcStep8.CSqZ t (c i) := by
        rw [tsum_mul_left, Summable.tsum_finsetSum (fun i hi => hs i hi)]
        rfl

/-! ## 4. Operators: preservation of smoothness and linearity -/

/-- An operator preserves smooth `1`-periodic functions. -/
def Preserves (T : Op ι) : Prop := ∀ f : (ι → ℝ) → ℂ, SmoothPer f → SmoothPer (T f)

theorem Preserves.id : Preserves (id : Op ι) := fun _ hf => hf

theorem Preserves.comp {T U : Op ι} (hT : Preserves T) (hU : Preserves U) :
    Preserves (fun f => T (U f)) := fun f hf => hT (U f) (hU f hf)

theorem Preserves.add {T U : Op ι} (hT : Preserves T) (hU : Preserves U) :
    Preserves (T + U) := fun f hf => by
  have h : (T + U) f = T f + U f := rfl
  rw [h]
  exact SmoothPer.add (hT f hf) (hU f hf)

theorem Preserves.finset_sum {κ : Type*} (s : Finset κ) (T : κ → Op ι)
    (h : ∀ i ∈ s, Preserves (T i)) : Preserves (∑ i ∈ s, T i) := fun f hf => by
  rw [finset_sumOp_apply]
  exact SmoothPer.finset_sum s (fun i => T i f) fun i hi => h i hi f hf

/-- An operator is additive and ℂ-homogeneous on smooth `1`-periodic functions. -/
structure LinSP (T : Op ι) : Prop where
  add : ∀ f g : (ι → ℝ) → ℂ, SmoothPer f → SmoothPer g → T (f + g) = T f + T g
  smul : ∀ (c : ℂ) (f : (ι → ℝ) → ℂ), SmoothPer f → T (c • f) = c • T f

theorem linSP_id : LinSP (id : Op ι) where
  add _ _ _ _ := rfl
  smul _ _ _ := rfl

theorem linSP_map_zero {T : Op ι} (h : LinSP T) : T 0 = 0 := by
  have h1 : T 0 = T 0 + T 0 := by simpa using h.add 0 0 SmoothPer.zero SmoothPer.zero
  have h2 : (0 : (ι → ℝ) → ℂ) = T 0 := by
    have h3 := congrArg (fun x : (ι → ℝ) → ℂ => x - T 0) h1
    simpa using h3
  exact h2.symm

theorem neg_one_smul_fun {g : (ι → ℝ) → ℂ} : (-1 : ℂ) • g = -g := by
  funext x
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, neg_one_mul]

theorem linSP_map_neg {T : Op ι} (h : LinSP T) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    T (-f) = -T f := by
  rw [← neg_one_smul_fun (g := f), h.smul (-1) f hf, neg_one_smul_fun (g := T f)]

theorem linSP_map_sub {T : Op ι} (h : LinSP T) {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f)
    (hg : SmoothPer g) : T (f - g) = T f - T g := by
  have h1 : f - g = f + (-g) := by funext x; ring
  rw [h1, h.add f (-g) hf (SmoothPer.neg hg), linSP_map_neg h hg]
  abel

theorem linSP_comp {T U : Op ι} (hT : LinSP T) (hU : LinSP U) (hUp : Preserves U) :
    LinSP (fun f => T (U f)) where
  add f g hf hg := by
    rw [hU.add f g hf hg, hT.add (U f) (U g) (hUp f hf) (hUp g hg)]
  smul c f hf := by
    rw [hU.smul c f hf, hT.smul c (U f) (hUp f hf)]

theorem linSP_add {T U : Op ι} (hT : LinSP T) (hU : LinSP U) : LinSP (T + U) where
  add f g hf hg := by
    have hL : (T + U) (f + g) = T (f + g) + U (f + g) := rfl
    have hR : (T + U) f + (T + U) g = (T f + U f) + (T g + U g) := rfl
    rw [hL, hR, hT.add f g hf hg, hU.add f g hf hg]
    abel
  smul c f hf := by
    have hL : (T + U) (c • f) = T (c • f) + U (c • f) := rfl
    have hR : c • (T + U) f = c • (T f + U f) := rfl
    rw [hL, hR, hT.smul c f hf, hU.smul c f hf, smul_add]

theorem linSP_neg {T : Op ι} (hT : LinSP T) : LinSP (-T) where
  add f g hf hg := by
    have hL : (-T) (f + g) = -(T (f + g)) := rfl
    have hR : (-T) f + (-T) g = -T f + -(T g) := rfl
    rw [hL, hR, hT.add f g hf hg]
    abel
  smul c f hf := by
    have hL : (-T) (c • f) = -(T (c • f)) := rfl
    have hR : c • (-T) f = c • (-(T f)) := rfl
    rw [hL, hR, hT.smul c f hf, smul_neg]

theorem linSP_sub {T U : Op ι} (hT : LinSP T) (hU : LinSP U) : LinSP (T - U) :=
  linSP_add hT (linSP_neg hU)

theorem linSP_finset_sum {κ : Type*} (s : Finset κ) (T : κ → Op ι)
    (h : ∀ i ∈ s, LinSP (T i)) : LinSP (∑ i ∈ s, T i) where
  add f g hf hg := by
    funext x
    rw [finset_sumOp_apply, finset_sumOp_apply, finset_sumOp_apply]
    simp only [Pi.add_apply]
    rw [Finset.sum_congr rfl (fun i hi => congrFun ((h i hi).add f g hf hg) x)]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  smul c f hf := by
    funext x
    rw [finset_sumOp_apply, finset_sumOp_apply]
    simp only [Pi.smul_apply]
    rw [Finset.sum_congr rfl (fun i hi => congrFun ((h i hi).smul c f hf) x)]
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]

/-! ## 5. The order predicate and its closure properties -/

/-- `IsOrd d C T`: the operator `T` preserves smooth `1`-periodic functions, is ℂ-linear on them,
and is of **order at most `d`** on the weighted integer Sobolev scale, with the *constant function*
`C : ℤ → ℝ` of the exponent:

`CSqZ (t - d) (fourierCoeff (T f)) ≤ C t * CSqZ t (fourierCoeff f)` for every `t : ℤ`.

The constant is allowed to depend on `t`, and it has to be: multiplication by a fixed smooth
function is bounded on `H^t` with a norm that grows with `|t|`.  The closure lemmas below keep
track of the resulting constant *functions*, and at the very end only the value at the single
relevant exponent is used. -/
structure IsOrd (d : ℤ) (C : ℤ → ℝ) (T : Op ι) : Prop where
  pres : Preserves T
  lin : LinSP T
  nonneg : ∀ t : ℤ, 0 ≤ C t
  bound : ∀ (t : ℤ) (f : (ι → ℝ) → ℂ), SmoothPer f →
    Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d) (Work.Diff.STE.fourierCoeff (T f))
      ≤ C t * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff f)

/-- Building an `IsOrd` certificate level by level: it suffices to produce, for each *single*
exponent `t`, a constant for the bound. -/
theorem isOrd_of_pointwise {d : ℤ} {T : Op ι} (hpres : Preserves T) (hlin : LinSP T)
    (h : ∀ t : ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (ι → ℝ) → ℂ, SmoothPer f →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d) (Work.Diff.STE.fourierCoeff (T f))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff f)) :
    ∃ C : ℤ → ℝ, IsOrd d C T := by
  choose C hC using h
  exact ⟨C, hpres, hlin, fun t => (hC t).1, fun t f hf => (hC t).2 f hf⟩

theorem IsOrd.mono_C {d : ℤ} {C C' : ℤ → ℝ} {T : Op ι} (h : IsOrd d C T)
    (hC : ∀ t, C t ≤ C' t) : IsOrd d C' T where
  pres := h.pres
  lin := h.lin
  nonneg := fun t => le_trans (h.nonneg t) (hC t)
  bound t f hf := (h.bound t f hf).trans
    (mul_le_mul_of_nonneg_right (hC t) (Work.Diff.STE.B3.SymCalcStep8.CSqZ_nonneg t _))

theorem IsOrd.mono_d {d d' : ℤ} {C : ℤ → ℝ} {T : Op ι} (h : IsOrd d' C T) (hd : d' ≤ d) :
    IsOrd d C T where
  pres := h.pres
  lin := h.lin
  nonneg := h.nonneg
  bound t f hf :=
    le_trans (Work.Diff.STE.B3.SymCalcStep8.CSqZ_mono (by omega) _
      (SmoothPer.summable_CSqZ (h.pres f hf) (t - d'))) (h.bound t f hf)

theorem IsOrd.comp {d₁ d₂ : ℤ} {C₁ C₂ : ℤ → ℝ} {T U : Op ι} (hT : IsOrd d₁ C₁ T)
    (hU : IsOrd d₂ C₂ U) :
    IsOrd (d₁ + d₂) (fun t => C₁ (t - d₂) * C₂ t) (fun f => T (U f)) where
  pres := Preserves.comp hT.pres hU.pres
  lin := linSP_comp hT.lin hU.lin hU.pres
  nonneg t := mul_nonneg (hT.nonneg _) (hU.nonneg _)
  bound t f hf := by
    have hUf : SmoothPer (U f) := hU.pres f hf
    have h1 := hT.bound (t - d₂) (U f) hUf
    have h2 := hU.bound t f hf
    have h3 : (t - d₂) - d₁ = t - (d₁ + d₂) := by ring
    calc Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - (d₁ + d₂))
          (Work.Diff.STE.fourierCoeff (T (U f)))
        = Work.Diff.STE.B3.SymCalcStep8.CSqZ ((t - d₂) - d₁)
            (Work.Diff.STE.fourierCoeff (T (U f))) := by rw [h3]
      _ ≤ C₁ (t - d₂) * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d₂)
            (Work.Diff.STE.fourierCoeff (U f)) := h1
      _ ≤ C₁ (t - d₂) * (C₂ t * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
            (Work.Diff.STE.fourierCoeff f)) := mul_le_mul_of_nonneg_left h2 (hT.nonneg _)
      _ = (C₁ (t - d₂) * C₂ t) * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
            (Work.Diff.STE.fourierCoeff f) := by ring

theorem IsOrd.add {d : ℤ} {C₁ C₂ : ℤ → ℝ} {T U : Op ι} (hT : IsOrd d C₁ T)
    (hU : IsOrd d C₂ U) : IsOrd d (fun t => 2 * (C₁ t + C₂ t)) (T + U) where
  pres := Preserves.add hT.pres hU.pres
  lin := linSP_add hT.lin hU.lin
  nonneg t := by have := hT.nonneg t; have := hU.nonneg t; linarith
  bound t f hf := by
    have h1 : (T + U) f = T f + U f := rfl
    have ha := hT.bound t f hf
    have hb := hU.bound t f hf
    have hsumm_a : Summable (fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ (t - d) * ‖Work.Diff.STE.fourierCoeff (T f) k‖ ^ 2) :=
      SmoothPer.summable_CSqZ (hT.pres f hf) (t - d)
    have hsumm_b : Summable (fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ (t - d) * ‖Work.Diff.STE.fourierCoeff (U f) k‖ ^ 2) :=
      SmoothPer.summable_CSqZ (hU.pres f hf) (t - d)
    have hcoef : Work.Diff.STE.fourierCoeff ((T + U) f)
        = fun k => Work.Diff.STE.fourierCoeff (T f) k
            + Work.Diff.STE.fourierCoeff (U f) k := by
      rw [h1]
      exact fourierCoeff_add_of_continuous (hT.pres f hf).continuous (hU.pres f hf).continuous
    rw [hcoef]
    calc Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d) (fun k =>
          Work.Diff.STE.fourierCoeff (T f) k + Work.Diff.STE.fourierCoeff (U f) k)
        ≤ 2 * (Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d) (Work.Diff.STE.fourierCoeff (T f))
            + Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d)
                (Work.Diff.STE.fourierCoeff (U f))) :=
          CSqZ_add_le (t - d) _ _ hsumm_a hsumm_b
      _ ≤ 2 * (C₁ t * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff f)
            + C₂ t * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
                (Work.Diff.STE.fourierCoeff f)) := by linarith [ha, hb]
      _ = (2 * (C₁ t + C₂ t)) * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
            (Work.Diff.STE.fourierCoeff f) := by ring

theorem IsOrd.neg {d : ℤ} {C : ℤ → ℝ} {T : Op ι} (h : IsOrd d C T) :
    IsOrd d C (-T) where
  pres := fun f hf => by
    have h1 : (-T) f = -(T f) := rfl
    rw [h1]; exact SmoothPer.neg (h.pres f hf)
  lin := linSP_neg h.lin
  nonneg := h.nonneg
  bound t f hf := by
    have h1 : (-T) f = -(T f) := rfl
    have hcoef : Work.Diff.STE.fourierCoeff ((-T) f)
        = fun k => -Work.Diff.STE.fourierCoeff (T f) k := by
      rw [h1]
      exact fourierCoeff_neg_of_continuous (h.pres f hf).continuous
    rw [hcoef, CSqZ_neg]
    exact h.bound t f hf

theorem IsOrd.sub {d : ℤ} {C₁ C₂ : ℤ → ℝ} {T U : Op ι} (hT : IsOrd d C₁ T)
    (hU : IsOrd d C₂ U) : IsOrd d (fun t => 2 * (C₁ t + C₂ t)) (T - U) :=
  IsOrd.add hT (IsOrd.neg hU)

theorem IsOrd.sum {κ : Type*} {d : ℤ} (s : Finset κ) (T : κ → Op ι) (C : κ → ℤ → ℝ)
    (h : ∀ i ∈ s, IsOrd d (C i) (T i)) :
    IsOrd d (fun t => (s.card : ℝ) * ∑ i ∈ s, C i t) (∑ i ∈ s, T i) where
  pres := Preserves.finset_sum s T fun i hi => (h i hi).pres
  lin := linSP_finset_sum s T fun i hi => (h i hi).lin
  nonneg t := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i hi => (h i hi).nonneg t)
  bound t f hf := by
    have hcoef : Work.Diff.STE.fourierCoeff ((∑ i ∈ s, T i) f)
        = fun k => ∑ i ∈ s, Work.Diff.STE.fourierCoeff (T i f) k := by
      rw [finset_sumOp_apply]
      exact fourierCoeff_finset_sum_of_continuous s (fun i => T i f)
        fun i hi => (h i hi).pres f hf |>.continuous
    have hsm : ∀ i ∈ s, Summable (fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ (t - d) * ‖Work.Diff.STE.fourierCoeff (T i f) k‖ ^ 2) :=
      fun i hi => SmoothPer.summable_CSqZ ((h i hi).pres f hf) (t - d)
    rw [hcoef]
    calc Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d)
          (fun k => ∑ i ∈ s, Work.Diff.STE.fourierCoeff (T i f) k)
        ≤ (s.card : ℝ) * ∑ i ∈ s,
            Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d)
              (Work.Diff.STE.fourierCoeff (T i f)) := CSqZ_finset_sum_le (t - d) s _ hsm
      _ ≤ (s.card : ℝ) * ((∑ i ∈ s, C i t) * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
            (Work.Diff.STE.fourierCoeff f)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          calc ∑ i ∈ s, Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - d)
                (Work.Diff.STE.fourierCoeff (T i f))
              ≤ ∑ i ∈ s, C i t * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
                  (Work.Diff.STE.fourierCoeff f) :=
                Finset.sum_le_sum fun i hi => (h i hi).bound t f hf
            _ = (∑ i ∈ s, C i t) * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
                  (Work.Diff.STE.fourierCoeff f) := by rw [Finset.sum_mul]
      _ = ((s.card : ℝ) * ∑ i ∈ s, C i t) * Work.Diff.STE.B3.SymCalcStep8.CSqZ t
            (Work.Diff.STE.fourierCoeff f) := by ring

theorem IsOrd.congr {d : ℤ} {C : ℤ → ℝ} {T U : Op ι} (h : IsOrd d C T)
    (hEq : ∀ f : (ι → ℝ) → ℂ, SmoothPer f → T f = U f) : IsOrd d C U where
  pres := fun f hf => by rw [← hEq f hf]; exact h.pres f hf
  lin := ⟨fun f g hf hg => by
      rw [← hEq (f + g) (SmoothPer.add hf hg), ← hEq f hf, ← hEq g hg, h.lin.add f g hf hg],
    fun c f hf => by rw [← hEq (c • f) (hf.smul c), ← hEq f hf, h.lin.smul c f hf]⟩
  nonneg := h.nonneg
  bound t f hf := by
    rw [← hEq f hf]
    exact h.bound t f hf

theorem IsOrd.id : IsOrd 0 (fun _ => 1) (id : Op ι) where
  pres := Preserves.id
  lin := linSP_id
  nonneg := fun _ => zero_le_one
  bound t f _ := by
    change Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - 0) (Work.Diff.STE.fourierCoeff f)
      ≤ 1 * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff f)
    rw [sub_zero, one_mul]

theorem IsOrd.zero : IsOrd 0 (fun _ => 0) (0 : Op ι) where
  pres := fun f hf => by
    have h : (0 : Op ι) f = 0 := rfl
    rw [h]; exact SmoothPer.zero
  lin := ⟨fun f g _ _ => by simp, fun c f _ => by simp⟩
  nonneg := fun _ => le_refl 0
  bound t f _ := by
    have h : Work.Diff.STE.fourierCoeff ((0 : Op ι) f) = 0 := by
      have h1 : (0 : Op ι) f = 0 := rfl
      rw [h1]
      funext k
      simp only [Work.Diff.STE.fourierCoeff]
      simp
    rw [h]
    simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ]
    simp

/-! ## 6. The concrete operators -/

/-- Multiplication by a real-valued function. -/
def mulOp (m : (ι → ℝ) → ℝ) : Op ι := fun f x => ((m x : ℝ) : ℂ) * f x

/-- The `i`-th partial derivative. -/
def pdOp (i : ι) : Op ι := fun f => Work.Diff.STE.pd i f

/-- The Friedrichs cutoff `S_ε = flatCut ρ ε`. -/
def cutOp (ρ : (ι → ℝ) → ℝ) (ε : ℝ) : Op ι :=
  fun f => Work.Diff.STE.B3.SymCalc.flatCut ρ ε f

/-- The variable-coefficient Laplacian `varLap A B` as an operator. -/
def varLapOp (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) : Op ι := fun f => varLap A B f

/-- Operator composition. -/
def compOp (T U : Op ι) : Op ι := fun f => T (U f)

/-- The commutator of two operators. -/
def commOp (T U : Op ι) : Op ι := fun f => T (U f) - U (T f)

@[simp] theorem compOp_apply (T U : Op ι) (f : (ι → ℝ) → ℂ) : compOp T U f = T (U f) := rfl

@[simp] theorem commOp_apply (T U : Op ι) (f : (ι → ℝ) → ℂ) :
    commOp T U f = T (U f) - U (T f) := rfl

/-- `[T, A + B] = [T,A] + [T,B]` when `T` is additive on smooth periodic functions. -/
theorem commOp_add_right_apply {T A B : Op ι} {f : (ι → ℝ) → ℂ} (hT : LinSP T)
    (hA : Preserves A) (hB : Preserves B) (hf : SmoothPer f) :
    commOp T (A + B) f = commOp T A f + commOp T B f := by
  have h2 : SmoothPer (A f) := hA f hf
  have h3 : SmoothPer (B f) := hB f hf
  simp only [commOp_apply, Pi.add_apply]
  rw [hT.add (A f) (B f) h2 h3]
  ring

/-- `[A + B, M] = [A,M] + [B,M]` when `M` is additive on smooth periodic functions. -/
theorem commOp_add_left_apply {A B M : Op ι} {f : (ι → ℝ) → ℂ} (hM : LinSP M)
    (hA : Preserves A) (hB : Preserves B) (hf : SmoothPer f) :
    commOp (A + B) M f = commOp A M f + commOp B M f := by
  have h2 : SmoothPer (A f) := hA f hf
  have h3 : SmoothPer (B f) := hB f hf
  simp only [commOp_apply, Pi.add_apply]
  rw [hM.add (A f) (B f) h2 h3]
  ring

/-- `[T, -A] = -[T,A]` when `T` is additive on smooth periodic functions. -/
theorem commOp_neg_right_apply {T A : Op ι} {f : (ι → ℝ) → ℂ} (hT : LinSP T)
    (hA : Preserves A) (hf : SmoothPer f) :
    commOp T (-A) f = -commOp T A f := by
  have h2 : SmoothPer (A f) := hA f hf
  simp only [commOp_apply, Pi.neg_apply]
  rw [linSP_map_neg hT h2]
  ring

/-- `[-A, M] = -[A,M]` when `M` is additive on smooth periodic functions. -/
theorem commOp_neg_left_apply {A M : Op ι} {f : (ι → ℝ) → ℂ} (hM : LinSP M)
    (hA : Preserves A) (hf : SmoothPer f) :
    commOp (-A) M f = -commOp A M f := by
  have h2 : SmoothPer (A f) := hA f hf
  simp only [commOp_apply, Pi.neg_apply]
  rw [linSP_map_neg hM h2]
  ring

/-- **Leibniz for commutators**: `[T, AB] = [T,A]B + A[T,B]`, evaluated at `f`. -/
theorem commOp_compOp_apply {T A B : Op ι} {f : (ι → ℝ) → ℂ} (hA : LinSP A)
    (hT : Preserves T) (hB : Preserves B) (hf : SmoothPer f) :
    commOp T (compOp A B) f = compOp (commOp T A) B f + compOp A (commOp T B) f := by
  have h1 : SmoothPer (T (B f)) := hT (B f) (hB f hf)
  have h2 : SmoothPer (B (T f)) := hB (T f) (hT f hf)
  simp only [commOp_apply, compOp_apply]
  rw [linSP_map_sub hA h1 h2]
  ring

/-- **Leibniz for commutators**, other order: `[AB, T] = A[B,T] + [A,T]B`, evaluated at `f`. -/
theorem compOp_commOp_apply {T A B : Op ι} {f : (ι → ℝ) → ℂ} (hA : LinSP A)
    (hT : Preserves T) (hB : Preserves B) (hf : SmoothPer f) :
    commOp (compOp A B) T f = compOp A (commOp B T) f + compOp (commOp A T) B f := by
  have h1 : SmoothPer (T (B f)) := hT (B f) (hB f hf)
  have h2 : SmoothPer (B (T f)) := hB (T f) (hT f hf)
  simp only [commOp_apply, compOp_apply]
  rw [linSP_map_sub hA h2 h1]
  ring

/-! ## 7. The commutator of two operators is of the sum of the orders -/

theorem IsOrd.comm {d₁ d₂ : ℤ} {C₁ C₂ : ℤ → ℝ} {T U : Op ι} (hT : IsOrd d₁ C₁ T)
    (hU : IsOrd d₂ C₂ U) :
    IsOrd (d₁ + d₂) (fun t => 2 * (C₁ (t - d₂) * C₂ t + C₂ (t - d₁) * C₁ t))
      (commOp T U) := by
  have h2 : IsOrd (d₁ + d₂) (fun t => C₂ (t - d₁) * C₁ t) (fun f => U (T f)) :=
    IsOrd.mono_d (IsOrd.comp hU hT) (by omega)
  refine IsOrd.congr (IsOrd.sub (IsOrd.comp hT hU) h2) (fun f _ => rfl)

end Work.Diff.STE.B3.VarCoef
