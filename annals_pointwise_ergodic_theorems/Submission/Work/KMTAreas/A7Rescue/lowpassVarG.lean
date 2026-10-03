/-
# The `g`-side low-pass lacunary variational estimate (paper (lin-2), `k₂ = 0`)

Statement of `Work.KMTAreas.A7Hi.lowpassVarG` / `Work.KMTAreas.A7G.lowpassVarG` /
`Work.KMTAreas.A7.mlb_lowpassVarG` (the `j₂ = 0`, `s₂ = -u` case of the paper's (lin-2)):

for `ρ ∈ (0,1]`, `r > 2`, `1 < p < ∞` and a `Λ`-lacunary family of scales `n ↦ N_n = ⌊a n⌋`,

  `‖ V^r_n (T^{≤l₂}_{φ̃_{N_n}} f) ‖_{ℓ^p(ℤ)} ≤ C (1 + l₂)² ‖f‖_{ℓ^p(ℤ)}`,

uniformly in the arithmetic height `l₂` and the narrowness level `k`, on the good major arcs
`GoodMajorArcs ρ Cρ l₂ k` with `k ≥ -d·logN N_n` (`d = P.natDegree`); here
`T^{≤l₂}_{φ̃_N} = Tle ρ l₂ (varphitildeN P.natDegree N 0) = kmtProj ρ l₂ (-(d·logN N))`.

## The route

The **whole** arithmetic content of this statement is the single *chain-part / square-function*
crux of the Ionescu–Wainger low-pass walk, and the reduction to it is **proved and
axiom-clean**: `Work.KMTAreas.A7Hi.lowpassVarGRepOfChainPartSqFunPos`
(`Submission/Work/KMTAreas/A7HiRep/assembly.lean`), whose ingredients are

* the telescoping `V^r(walk) ≤ ‖T_0 f‖ + 2·chainPart r (walk)`,
* the proved, height-free single-scale bound `A7.kmtProj_lp_bound_uniform`,
* the proved, height-free band square-function bound `A7Hi2.sqFunBound`, and
* the crux `A7HiRep.chainPartSqFunPos` at its extreme constant `Cρ₀ = 2`.

Everything except that one input is in the tree and axiom-clean, so this file adds exactly the
assembly; the crux itself is the workspace's canonical open node (see
`NOTES_A7HiRep_chainPartSqFunPosMemLp_SESSION*.md`), proved in the tree for the bounded height
regime `l₁ ≤ iwC0 ρ` (`A7HiRep.chainPartSqFunPosSmallHeight`) and for `l₁ = 0`
(`A7HiRep.chainPartZeroHeight`), and open in the deep regime `iwC0 ρ < l₁`
(`A7HiRep.chainPartSqFunPosMemLp_of_largeHeight`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7Rescue.headVarBound
import Submission.Work.KMTAreas.A7Rescue.clog_two_headLevel
import Submission.Work.KMTAreas.A7Rescue.PieceFam
import Submission.Port.Aesm

set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Rescue

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## A standalone contribution: the `eLpNorm` wrap of the weighted variational subadditivity

`A7/lowpassAlphaTransfer.lean` (`NOTES_A7_arithGain_variational.md`, L6 and its `eLpNorm` wrap)
needs the following two lemmas; the weighted subadditivity is there, but its `eLpNorm` wrap was
attempted and removed three times over API issues, so it is recorded here (where the
`Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal` name is imported) instead. -/

/-- **Weighted subadditivity of the variational norm.**  `V^r(Σ_i w_i • a_i) ≤ Σ_i ‖w_i‖ₑ·V^r(a_i)`
for `1 ≤ r`. -/
lemma variationalNorm_weighted_finset_sum_le {r : NNReal} (hr : 1 ≤ r) {ι : Type*}
    (s : Finset ι) (w : ι → ℂ) (a : ι → ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑ i ∈ s, w i • a i n)
      ≤ ∑ i ∈ s, ‖w i‖ₑ * PointwiseErgodicTheorems.variationalNorm r (a i) := by
  classical
  refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr s
    (fun i n => w i • a i n)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact (Submission.PointwiseErgodicTheorems.variationalNorm_smul hr (w i) (a i)).le

/-- **The `eLpNorm` wrap.**  If each of the finitely many families `T i` satisfies the `ℓᵖ`
variational estimate with the *same* constant `C`, and the weights satisfy `Σ_i ‖w i‖ ≤ C'`, then
the weighted sum does, with constant `C' * C`. -/
lemma eLpNorm_varEst_weighted_finset_sum {r : NNReal} (hr : 1 ≤ r) {p : ENNReal} (hp : 1 ≤ p)
    (hpt : p ≠ ⊤) {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (T : ι → ℕ → (ℤ → ℂ) → (ℤ → ℂ)) (C C' : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i ∈ s, ∀ g : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => T i n g x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count)
    (hw : ∑ i ∈ s, ‖w i‖ ≤ C') (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑ i ∈ s, w i • T i n g x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C' * C) * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  classical
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp (by simp)
  have hone : (1 : ℝ≥0∞) ≤ p := hp
  set E : ℝ≥0∞ := MeasureTheory.eLpNorm g p MeasureTheory.Measure.count with hE
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑ i ∈ s, w i • T i n g x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ s, ‖w i‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T i n g x)) p
          MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_mono_ennreal
      (fun x => variationalNorm_weighted_finset_sum_le hr s w (fun i n => T i n g x)) hp0 hpt
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ s, ‖w i‖ₑ *
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T i n g x)) p
        MeasureTheory.Measure.count
      ≤ ∑ i ∈ s, ‖w i‖ₑ * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T i n g x)) p
          MeasureTheory.Measure.count := by
    refine (Work.KMTAreas.A7.eLpNorm_finset_sum_le_ennreal s
      (fun i x => ‖w i‖ₑ * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => T i n g x)) hone hpt).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ‖w i‖ₑ)
      (ENNReal.coe_ne_top) hp0 hpt
  have hmul : MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ s, ‖w i‖ₑ *
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T i n g x)) p
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((∑ i ∈ s, ‖w i‖) * C) * E := by
    refine hsum.trans ?_
    calc ∑ i ∈ s, ‖w i‖ₑ * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T i n g x)) p
            MeasureTheory.Measure.count
        ≤ ∑ i ∈ s, ‖w i‖ₑ * (ENNReal.ofReal C * E) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hT i hi g) bot_le
      _ = ENNReal.ofReal ((∑ i ∈ s, ‖w i‖) * C) * E := by
          have hcoe : (∑ i ∈ s, ‖w i‖ₑ * ENNReal.ofReal C)
              = ENNReal.ofReal ((∑ i ∈ s, ‖w i‖) * C) := by
            have h1 : (∑ i ∈ s, ‖w i‖ₑ * ENNReal.ofReal C)
                = ∑ i ∈ s, ENNReal.ofReal (‖w i‖ * C) :=
              Finset.sum_congr rfl fun i _ => by
                rw [show ‖w i‖ₑ = ENNReal.ofReal ‖w i‖ from by simp,
                  ENNReal.ofReal_mul (norm_nonneg (w i))]
            rw [h1, ← ENNReal.ofReal_sum_of_nonneg
              (fun i _ => mul_nonneg (norm_nonneg (w i)) hC), ← Finset.sum_mul]
          rw [Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm), ← Finset.sum_mul, hcoe]
  exact hmono.trans (hmul.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw hC)) bot_le))

/-! ## Step 1: the object identification and the level map

The `g`-side bump at the bottom scale is the Ionescu–Wainger projection at the level
`-(d·logN N)`, and the level map of the lacunary family is monotone and on the good major arcs. -/

/-- **The `g`-side bump at the bottom scale is the IW projection at level `-(d·logN N)`**:
the definitional bridge of the whole file (`Tle_etaCut` composed with
`A7G.varphitildeN_zero_eq_etaCutG`). -/
theorem Tle_varphitildeN_zero_eq_kmtProj' (ρ : ℝ) (l d N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeN d N 0)
      = Work.KMTContract.kmtProj ρ l (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  rw [Work.KMTAreas.A7G.varphitildeN_zero_eq_etaCutG]
  rfl

/-- **The level of the walk**: the level of the IW projection at the scale `⌊a n⌋`. -/
noncomputable def walkLevel (d : ℕ) (a : ℕ → NNReal) (n : ℕ) : ℤ :=
  (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))

/-- A `Λ`-lacunary family with `Λ > 1` and `a n ≥ 1` is nondecreasing. -/
theorem monotone_of_lacunary {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by simpa using mul_le_mul_of_nonneg_right hΛ.le (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- The level of the walk is nondecreasing in `n`. -/
theorem walkLevel_mono {d : ℕ} {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone (walkLevel d a) :=
  fun _ _ hnm => mul_le_mul_of_nonneg_left
    (Work.Analysis.EndVar.logN_mono (Nat.floor_mono
      (monotone_of_lacunary hΛ ha ha1 hnm))) (Int.natCast_nonneg d)

/-- The level of the walk is nonnegative (so a `ℕ` level can be used below it). -/
theorem walkLevel_nonneg (d : ℕ) (a : ℕ → NNReal) (n : ℕ) : 0 ≤ walkLevel d a n :=
  mul_nonneg (Int.natCast_nonneg d) (Work.Analysis.EndVar.logN_nonneg _)

/-- The level of the walk is on the good major arcs, by monotonicity in the level. -/
theorem goodMajorArcs_walkLevel {ρ Cρ : ℝ} {l₂ : ℕ} {k : ℤ} {d : ℕ} {a : ℕ → NNReal}
    (hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k)
    (hk : ∀ n, -(walkLevel d a n) ≤ k) (n : ℕ) :
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ (-(walkLevel d a n)) :=
  Work.KMTAreas.A7G.goodMajorArcs_mono_scale (k := k) (k' := -(walkLevel d a n)) (hk n) hgood

/-! ## Step 3: the lacunary tail, from the proved `TailHyp` -/

/-- **The lacunary tail.**  Any monotone reindexing of the levels `≥ C₀ + 1` of the single-height
walk has the `V^r`-bound, with `TailHyp`'s own constants: the reindexed family is a monotone
sub-family of the consecutive tail walk of `Work.KMTAreas.A7G.tailVarBound`, and reading a family
along a monotone index map does not increase its variational norm
(`A7.variationalNorm_comp_mono_le`). -/
theorem tailPiece_le_of_tailHyp (ρ : ℝ) (r : NNReal) (p : ℝ) (hp : 0 < p)
    (hTail : Work.KMTAreas.A7G.TailHyp ρ r p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l m₀ C₀ : ℕ) (L : ℕ → ℕ), Monotone L → (∀ n, C₀ + 1 ≤ L n) →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ → m₀ ≤ C₀ →
      ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L n) f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hmain⟩ := hTail
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l m₀ C₀ L hL hC0 hgood hnar hm0 f
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L n) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L n) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x) := by
    intro x
    have hφ : Monotone (fun n : ℕ => L n - (C₀ + 1)) :=
      fun a b hab => Nat.sub_le_sub_right (hL hab) _
    have hcomp := Work.KMTAreas.A7.variationalNorm_comp_mono_le
      (r := r) (u := fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
        - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x) hφ
    simpa only [Nat.add_sub_cancel' (hC0 _)] using hcomp
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L n) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L n) f x))
      (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top
  exact hstep.trans (hmain l m₀ C₀ hgood hnar hm0 f)

/-- **The height telescoping.**  The IW projection of height `l` is the sum of the height-`0`
projection and the `l` single-height increments, whence `V^r` of the walk of height `l` is bounded
by the sum of the `V^r`'s of the `l + 1` pieces (subadditivity, `A7.variationalNorm_finset_sum_le`). -/
theorem variationalNorm_kmtProj_le_sum (ρ : ℝ) (l : ℕ) (r : NNReal) (hr : 1 ≤ r)
    (m : ℕ → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n => Work.KMTContract.kmtProj ρ l (m n) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun n => Work.KMTContract.kmtProj ρ 0 (m n) f x)
        + ∑ i ∈ Finset.range l, PointwiseErgodicTheorems.variationalNorm r
            (fun n => Work.KMTContract.kmtProj ρ (i + 1) (m n) f x
              - Work.KMTContract.kmtProj ρ i (m n) f x) := by
  classical
  set A : ℕ → ℕ → ℂ := fun i n => Work.KMTContract.kmtProj ρ i (m n) f x with hA
  have htel' : ∀ n, (∑ i ∈ Finset.range l, (A (i + 1) n - A i n)) = A l n - A 0 n := by
    intro n
    induction l with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have htel : (fun n => A l n) = fun n => A 0 n + ∑ i ∈ Finset.range l, (A (i + 1) n - A i n) := by
    funext n
    rw [htel' n]
    ring
  rw [htel]
  refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr _ _).trans ?_
  refine add_le_add le_rfl ?_
  exact Work.KMTAreas.A7.variationalNorm_finset_sum_le hr (Finset.range l)
    (fun j n => A (j + 1) n - A j n)

/-! ## Step 4: the head/tail split at the first level exceeding the threshold -/

/-- **The head/tail split of a monotone family at `n₀ := Nat.find (∃ k, C₀ < Lt k)`.**

With `n₀` the first index at which the (monotone) level family `Lt` exceeds the threshold `C₀`, the
variational norm of any family `a` is bounded by that of the *padded head* `a ∘ min·n₀` (which is
constant `a n₀` from `n₀` on) and that of the *shifted tail* `a ∘ (n₀+·)`; the head indices are
exactly those with `Lt k ≤ C₀`, so `headVarBound` applies to the further padded family
`Lt ∘ min·(n₀-1)` with `N := C₀`. -/
theorem exists_first_exceed_split {r : NNReal} (hr : 1 ≤ r) (a : ℕ → ℂ) {Lt : ℕ → ℕ}
    (hLt : Monotone Lt) {C₀ : ℕ} (h : ∃ k, C₀ < Lt k) :
    ∃ n₀ : ℕ, (∀ k, k < n₀ → Lt k ≤ C₀) ∧ C₀ < Lt n₀ ∧ (∀ k, n₀ ≤ k → C₀ + 1 ≤ Lt k) ∧
      PointwiseErgodicTheorems.variationalNorm r a
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k n₀))
          + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k)) := by
  refine ⟨Nat.find h, fun k hk => ?_, Nat.find_spec h, fun k hk => ?_, ?_⟩
  · by_contra hc
    exact Nat.find_min h hk (not_le.mp hc)
  · have hle : Lt (Nat.find h) ≤ Lt k := hLt hk
    have := Nat.find_spec h
    omega
  · exact Work.KMTAreas.A7Rescue.variationalNorm_le_pad_add_shift hr a (Nat.find h)

/-- **In the complementary case the whole family is in the head**: if no level exceeds `C₀`, then
`Lt k ≤ C₀` for every `k`. -/
theorem forall_le_of_not_exists_gt {Lt : ℕ → ℕ} {C₀ : ℕ} (h : ¬∃ k, C₀ < Lt k) :
    ∀ k, Lt k ≤ C₀ := fun k => not_lt.mp (fun hk => h ⟨k, hk⟩)

/-- `iwQl ρ l` is nondecreasing in the arithmetic height `l`. -/
theorem iwQl_mono' {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l l' : ℕ} (h : l ≤ l') :
    Work.Analysis.IonescuWainger.iwQl ρ l ≤ Work.Analysis.IonescuWainger.iwQl ρ l' := by
  have hdvd : Work.Analysis.IonescuWainger.iwQl ρ l ∣ Work.Analysis.IonescuWainger.iwQl ρ l' := by
    rw [Work.Analysis.IonescuWainger.iwQl]
    refine Finset.lcm_dvd fun q hq => ?_
    rw [Work.Analysis.IonescuWainger.iwQl]
    exact Finset.dvd_lcm (Work.Analysis.IonescuWainger.iwP_mono hρ hρ1 h hq)
  exact Nat.le_of_dvd Work.Analysis.IonescuWainger.iwQl_pos hdvd

/-- The `ℝ≥0∞`-valued `eLpNorm` of `‖g‖ₑ` is the `eLpNorm` of `g`. -/
lemma eLpNorm_enorm_eq' {g : ℤ → ℂ} {q : ENNReal} (h0 : q ≠ 0) (ht : q ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g q MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-! ## Step 5: the assembly, and its arithmetic

The walk is decomposed into the head piece and the `l₂` single-height increments, each of which has
already been bounded on `ℓᵖ`; the two facts below turn that into the final estimate.  `hwalk` is a
*pointwise* bound of the variational norm of the walk by the sum of the variational norms of the
pieces; subadditivity of `eLpNorm` on `ℝ≥0∞`-valued functions
(`A7.eLpNorm_mono_ennreal`/`_add_le_ennreal`/`_finset_sum_le_ennreal`) and the finite-sum arithmetic
give the `ℓᵖ` bound. -/

/-- **The assembly of the walk estimate.**  If a nonnegative function `F` is pointwise bounded by a
head term `u` plus the sum of `l₂` terms `v i`, and `u`, `v i` satisfy `ℓᵖ` bounds with constants
`C_plain` and `B`, then `F` satisfies the `ℓᵖ` bound with constant `C_plain + l₂·B`. -/
lemma eLpNorm_le_of_pieces {p : ENNReal} {l₂ : ℕ}
    (F u : ℤ → ℝ≥0∞) (v : ℕ → ℤ → ℝ≥0∞) (f : ℤ → ℂ) (C_plain B C : ℝ)
    (hCp : 0 ≤ C_plain) (hB : 0 ≤ B) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hrec : ∀ x : ℤ, F x ≤ u x + ∑ i ∈ Finset.range l₂, v i x)
    (h0 : MeasureTheory.eLpNorm u p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C_plain * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hE : ∀ i ∈ Finset.range l₂, MeasureTheory.eLpNorm (v i) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hconst : C_plain + (l₂ : ℝ) * B ≤ C * (1 + (l₂ : ℝ)) ^ 2) :
    MeasureTheory.eLpNorm F p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hmono : MeasureTheory.eLpNorm F p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (u + fun x : ℤ => ∑ i ∈ Finset.range l₂, v i x)
        p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_mono_ennreal (fun x => hrec x) hp0 hpt
  have hadd : MeasureTheory.eLpNorm (u + fun x : ℤ => ∑ i ∈ Finset.range l₂, v i x)
        p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm u p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ Finset.range l₂, v i x)
          p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_add_le_ennreal
      (u := u) (v := fun x : ℤ => ∑ i ∈ Finset.range l₂, v i x) hp hpt
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ Finset.range l₂, v i x)
      p MeasureTheory.Measure.count
      ≤ ∑ i ∈ Finset.range l₂, MeasureTheory.eLpNorm (v i) p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_finset_sum_le_ennreal (Finset.range l₂) v hp hpt
  have hE' : ∑ i ∈ Finset.range l₂, MeasureTheory.eLpNorm (v i) p MeasureTheory.Measure.count
      ≤ ∑ i ∈ Finset.range l₂, ENNReal.ofReal B *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    Finset.sum_le_sum fun i hi => hE i hi
  have hfold : ∑ i ∈ Finset.range l₂, ENNReal.ofReal B *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      = ENNReal.ofReal ((l₂ : ℝ) * B) *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast l₂, ← mul_assoc,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg l₂)]
  have hfin : ENNReal.ofReal C_plain * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal ((l₂ : ℝ) * B) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst) bot_le
  have hchain : MeasureTheory.eLpNorm F p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C_plain * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ∑ i ∈ Finset.range l₂, ENNReal.ofReal B *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    hmono.trans (hadd.trans (add_le_add h0 (hsum.trans hE')))
  rw [hfold] at hchain
  exact hchain.trans hfin

/-- **The arithmetic of the final constant.**  With `B` the constant of the head pieces
(`C_head · (log₂ N + 1) + C_tail + 12·C₁`) and `log₂ N ≤ K(l₂+1)`, the total
`C_plain + l₂·B` is bounded by `((K+3)·(max ⋯ + 1))·(1 + l₂)²`. -/
lemma const_ineq {l₂ K : ℕ} {Cp Ch Ct C1 : ℝ} (h1 : 0 < Cp) (h2 : 0 < Ch) (h3 : 0 < Ct)
    (h4 : 0 < C1) :
    Cp + (l₂ : ℝ) * (Ch * ((K : ℝ) * ((l₂ : ℝ) + 1) + 1) + Ct + 12 * C1)
      ≤ ((K : ℝ) + 3) * (max (max Cp Ch) (Ct + 12 * C1) + 1) * (1 + (l₂ : ℝ)) ^ 2 := by
  set Ac : ℝ := max (max Cp Ch) (Ct + 12 * C1) with hAc
  have hAc0 : 0 < Ac := by
    rw [hAc]
    exact lt_of_lt_of_le h2 (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCp : Cp ≤ Ac := by rw [hAc]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCh : Ch ≤ Ac := by rw [hAc]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCt : Ct + 12 * C1 ≤ Ac := by rw [hAc]; exact le_max_right _ _
  have hl2 : (0 : ℝ) ≤ (l₂ : ℝ) := Nat.cast_nonneg l₂
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hx : (0 : ℝ) ≤ (K : ℝ) * ((l₂ : ℝ) + 1) + 1 := by positivity
  have hKl2 : (0 : ℝ) ≤ (K : ℝ) * (l₂ : ℝ) := mul_nonneg hK hl2
  have hstep : Ch * ((K : ℝ) * ((l₂ : ℝ) + 1) + 1) + Ct + 12 * C1
      ≤ Ac * ((K : ℝ) * ((l₂ : ℝ) + 1) + 2) := by
    have ha := mul_le_mul_of_nonneg_right hCh hx
    nlinarith [ha, hCt]
  have hfac : 1 + (l₂ : ℝ) * ((K : ℝ) * ((l₂ : ℝ) + 1) + 2)
      ≤ ((K : ℝ) + 3) * (1 + (l₂ : ℝ)) ^ 2 := by
    nlinarith [hKl2, hl2, hK, sq_nonneg (l₂ : ℝ), sq_nonneg ((l₂ : ℝ) + 1)]
  have hmain : Ac * (1 + (l₂ : ℝ) * ((K : ℝ) * ((l₂ : ℝ) + 1) + 2)) + (Cp - Ac)
      ≤ (Ac + 1) * (1 + (l₂ : ℝ)) ^ 2 * ((K : ℝ) + 3) := by
    have hfac2 : Ac * (1 + (l₂ : ℝ) * ((K : ℝ) * ((l₂ : ℝ) + 1) + 2))
        ≤ Ac * (((K : ℝ) + 3) * (1 + (l₂ : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hfac hAc0.le
    have hq : (0 : ℝ) ≤ (1 + (l₂ : ℝ)) ^ 2 * ((K : ℝ) + 3) := by positivity
    nlinarith [hfac2, hCp, hq, sq_nonneg (1 + (l₂ : ℝ)), sq_nonneg ((l₂ : ℝ))]
  calc Cp + (l₂ : ℝ) * (Ch * ((K : ℝ) * ((l₂ : ℝ) + 1) + 1) + Ct + 12 * C1)
      ≤ Ac * (1 + (l₂ : ℝ) * ((K : ℝ) * ((l₂ : ℝ) + 1) + 2)) + (Cp - Ac) := by
        nlinarith [hstep]
    _ ≤ (Ac + 1) * (1 + (l₂ : ℝ)) ^ 2 * ((K : ℝ) + 3) := hmain
    _ = ((K : ℝ) + 3) * (max (max Cp Ch) (Ct + 12 * C1) + 1) * (1 + (l₂ : ℝ)) ^ 2 := by
        rw [← hAc]; ring

/-- **The `g`-side low-pass lacunary variational estimate** (paper (lin-2), `k₂ = 0`). -/
theorem lowpassVarG (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
          (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((P.natDegree : ℤ) *
            Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 r hr p hp hptop Λ hΛ
  have hd : 1 ≤ P.natDegree := le_trans (by norm_num) hdeg
  have hp_ne : p ≠ ⊤ := ne_of_lt hptop
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) hp_ne
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_ne).mpr hp
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp_ne
  -- the four sources of constants
  obtain ⟨C_plain, hC_plain, hPlain⟩ :=
    Work.KMTAreas.A7G.plainBumpVarG P.natDegree hd ρ Λ hΛ r hr p hp hptop
  obtain ⟨Cρ_head, hCρ_head, C_head, hC_head, hHead⟩ :=
    Work.KMTAreas.A7Rescue.headVarBound ρ hρ hρ1 r hr p hp hptop
  obtain ⟨Cρ_tail, hCρ_tail, C_tail, hC_tail, hTail⟩ :=
    Work.KMTAreas.A7Rescue.tailPiece_le_of_tailHyp ρ r p.toReal hp0
      (Work.KMTAreas.A7G.tailVarBound ρ hρ hρ1 r hr p.toReal hp1)
  obtain ⟨Cρ_1, hCρ_1, C_1, hC_1, hB1⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  set D : ℝ := max (max Cρ_head (max Cρ_tail Cρ_1)) 1 with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDh : Cρ_head ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hDt : Cρ_tail ≤ D := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hD1 : Cρ_1 ≤ D := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨K, hK⟩ := Work.KMTAreas.A7Rescue.clog_two_headLevel ρ hρ hρ1 D hDpos
  -- the final constant absorbs the `log₂` of the head window level, which is `≤ K (l₂ + 1)`;
  -- `K` comes from `clog_two_headLevel` and must therefore appear in `C`
  refine ⟨D + 4, by positivity,
    ((K : ℝ) + 3) * (max (max C_plain C_head) (C_tail + 12 * C_1) + 1), by positivity, ?_⟩
  intro k l₂ a ha ha1 f hgood hk
  -- `GoodMajorArcs` is monotone in the constant
  have hGAm : ∀ {C₁ C₂ : ℝ}, C₂ ≤ C₁ → ∀ {l : ℕ} {k : ℤ},
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₁ l k →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₂ l k := by
    intro C₁ C₂ h l' k' hk'
    have hkR : (k' : ℝ) ≤ -C₁ * (2 : ℝ) ^ (ρ * (l' : ℝ)) := hk'
    have hx : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l' : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hmul : -C₁ * (2 : ℝ) ^ (ρ * (l' : ℝ)) ≤ -C₂ * (2 : ℝ) ^ (ρ * (l' : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hx
    exact le_trans hkR hmul
  -- the level map of the lacunary family
  set Mn : ℕ → ℕ := fun n => (walkLevel P.natDegree a n).toNat with hMndef
  have hMnZ : ∀ n, (Mn n : ℤ) = walkLevel P.natDegree a n :=
    fun n => Int.toNat_of_nonneg (walkLevel_nonneg _ _ _)
  have hMnmono : Monotone Mn :=
    fun m n hmn => Int.toNat_le_toNat (walkLevel_mono (d := P.natDegree) hΛ ha ha1 hmn)
  have hlevel : ∀ n, Work.Analysis.IonescuWainger.GoodMajorArcs ρ (D + 4) l₂ (-(Mn n : ℤ)) := by
    intro n
    have h := goodMajorArcs_walkLevel (d := P.natDegree) (a := a) (Cρ := D + 4) hgood hk n
    rwa [← hMnZ n] at h
  have hlevR : ∀ n, (D + 4) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (Mn n : ℝ) := by
    intro n
    have h := hlevel n
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at h
    push_cast at h
    linarith
  -- the base level and the head/tail threshold
  set m₀ : ℕ := ⌈D * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌉₊ with hm₀def
  set C₀ : ℕ := ⌈D * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌉₊ +
    Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₂) + 4 with hC₀def
  have hx1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₂ : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hceilD : ((⌈D * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌉₊ : ℕ) : ℝ) ≤
      (D + 4) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := by
    have h1 : ((⌈D * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌉₊ : ℕ) : ℝ) <
        D * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : D * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 ≤
        (D + 4) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := by nlinarith [hx1]
    linarith
  have hm₀le : ∀ n, m₀ ≤ Mn n := by
    intro n
    have h3 : (m₀ : ℝ) ≤ (Mn n : ℝ) := by
      rw [hm₀def]
      exact le_trans hceilD (hlevR n)
    exact_mod_cast h3
  have hm₀C₀ : m₀ ≤ C₀ := by
    simp only [hm₀def, hC₀def]; omega
  have h3Q : 3 * Work.Analysis.IonescuWainger.iwQl ρ l₂ < 2 ^ C₀ := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
      (3 * Work.Analysis.IonescuWainger.iwQl ρ l₂)
    simp only [hC₀def] at h ⊢
    calc 3 * Work.Analysis.IonescuWainger.iwQl ρ l₂
        < 2 ^ (Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₂) + 1) := h
      _ ≤ 2 ^ (⌈D * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌉₊ +
            Nat.log 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₂) + 4) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the base is large enough for every lemma's own arc constant
  have hbase : ∀ {Cρ' : ℝ}, Cρ' ≤ D → ∀ l : ℕ, l ≤ l₂ →
      Cρ' * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (m₀ : ℝ) := by
    intro Cρ' hCρ' l hl
    have h2 : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
      nlinarith [hρ]
    have hfloor : D * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (m₀ : ℝ) := by
      rw [hm₀def]; exact Nat.le_ceil _
    calc Cρ' * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ D * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
          mul_le_mul_of_nonneg_right hCρ'
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ D * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := mul_le_mul_of_nonneg_left h2 hDpos.le
      _ ≤ (m₀ : ℝ) := hfloor
  -- the level above the base, and the `lpf` form of the walk
  set Lt : ℕ → ℕ := fun n => Mn n - m₀ with hLtdef
  have hMn_eq : ∀ n, Mn n = m₀ + Lt n := by
    intro n
    rw [hLtdef]
    exact (Nat.add_sub_cancel' (hm₀le n)).symm
  have hLtmono : Monotone Lt := fun a b hab => Nat.sub_le_sub_right (hMnmono hab) _
  have hid : ∀ (l : ℕ) (n : ℕ), Work.KMTContract.kmtProj ρ l (-(Mn n : ℤ)) f
      = Work.KMTAreas.A7Hi.lpf ρ l m₀ (Lt n) f := by
    intro l n
    simp only [Work.KMTAreas.A7Hi.lpf]
    rw [hMn_eq n]
    push_cast
    ring
  have hidx : ∀ (l : ℕ) (n : ℕ) (x : ℤ), Work.KMTContract.kmtProj ρ l (-(Mn n : ℤ)) f x
      = Work.KMTAreas.A7Hi.lpf ρ l m₀ (Lt n) f x :=
    fun l n x => congrFun (hid l n) x
  -- the walk, decomposed into its `l₂ + 1` single-height pieces
  have hwalk : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x)
        + ∑ i ∈ Finset.range l₂, PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
              - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x) := by
    intro x
    have hleft : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x
        = Work.KMTContract.kmtProj ρ l₂ (-(Mn n : ℤ)) f x := by
      intro n
      rw [Tle_varphitildeN_zero_eq_kmtProj', hMnZ n]
      rfl
    have hA : PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)
        = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l₂ (-(Mn n : ℤ)) f x) :=
      congrArg _ (funext hleft)
    have hs : ∀ i : ℕ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ (i + 1) (-(Mn n : ℤ)) f x
            - Work.KMTContract.kmtProj ρ i (-(Mn n : ℤ)) f x)
        = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
            - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x) := by
      intro i
      refine congrArg _ (funext fun n => ?_)
      rw [hidx (i + 1) n x, hidx i n x]
    have hzero : PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ 0 (-(Mn n : ℤ)) f x)
        = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x) :=
      congrArg _ (funext fun n => hidx 0 n x)
    have hB : PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ 0 (-(Mn n : ℤ)) f x)
          + ∑ i ∈ Finset.range l₂, PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTContract.kmtProj ρ (i + 1) (-(Mn n : ℤ)) f x
                - Work.KMTContract.kmtProj ρ i (-(Mn n : ℤ)) f x)
        = PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x)
          + ∑ i ∈ Finset.range l₂, PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
                - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x) := by
      rw [hzero, Finset.sum_congr rfl (fun i _ => hs i)]
    have hle := variationalNorm_kmtProj_le_sum ρ l₂ r (le_trans (by norm_num) (le_of_lt hr))
      (fun n => -(Mn n : ℤ)) f x
    exact (le_of_eq hA).trans (hle.trans (le_of_eq hB))
  -- the `i = 0` piece: the arithmetic-free low-pass walk, bounded unconditionally
  have hleftx : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f
      = Work.KMTContract.kmtProj ρ 0 (-(Mn n : ℤ)) f := by
    intro n
    rw [Tle_varphitildeN_zero_eq_kmtProj' ρ 0 P.natDegree (Nat.floor (a n)), hMnZ n]
    rfl
  have hleft0 : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f
      = Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f :=
    fun n => (hleftx n).trans (hid 0 n)
  have hEst0 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C_plain * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hcong : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x) :=
      funext fun x => congrArg _ (funext fun n => (congrFun (hleft0 n) x).symm)
    rw [hcong]
    exact hPlain a ha ha1 f
  -- the level-indexed piece family, hoisted before the case split so that every sub-case (and the
  -- goal restatement) can speak in the short term `A i k x`
  set A : ℕ → ℕ → ℤ → ℂ := pieceFam ρ m₀ Lt f with hAdef
  have hAfst : ∀ (i : ℕ) (k : ℕ) (x : ℤ), A i k x
      = Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt k) f x
        - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt k) f x := by
    intro i k x
    rw [hAdef]
    rfl
  -- the arithmetic of the final constant: `log₂ (C₀ + 1) ≤ K (l₂ + 1)`, whence the assembled
  -- constant `C_plain + l₂ · B` is bounded by `((K + 3)(max · + 1))(1 + l₂)²`
  have hclogN : Nat.clog 2 (C₀ + 1) ≤ K * (l₂ + 1) := by
    refine (Nat.clog_mono_right 2 (by omega : C₀ + 1 ≤ 2 * C₀ + 1)).trans ?_
    rw [hC₀def]
    exact hK l₂
  have hclog : (Nat.clog 2 (C₀ + 1) : ℝ) ≤ (K : ℝ) * ((l₂ : ℝ) + 1) := by
    have h : ((Nat.clog 2 (C₀ + 1) : ℕ) : ℝ) ≤ ((K * (l₂ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hclogN
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hconst : C_plain + (l₂ : ℝ) *
        (C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1)
      ≤ ((K : ℝ) + 3) * (max (max C_plain C_head) (C_tail + 12 * C_1) + 1)
        * (1 + (l₂ : ℝ)) ^ 2 := by
    have hBB : C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1
        ≤ C_head * ((K : ℝ) * ((l₂ : ℝ) + 1) + 1) + C_tail + 12 * C_1 := by
      have h : (Nat.clog 2 (C₀ + 1) : ℝ) + 1 ≤ (K : ℝ) * ((l₂ : ℝ) + 1) + 1 := by
        linarith [hclog]
      have hb := mul_le_mul_of_nonneg_left h hC_head.le
      linarith
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hBB (Nat.cast_nonneg l₂))).trans ?_
    exact const_ineq hC_plain hC_head hC_tail hC_1
  -- the head/tail split of the levels of the lacunary family
  by_cases hsplit : ∃ k, C₀ < Lt k
  · -- ###### SPLIT BRANCH ######
    -- the first level above the threshold, and the two pieces it produces
    set n₀ : ℕ := Nat.find hsplit with hn₀def
    have hn₀lt : ∀ k, k < n₀ → Lt k ≤ C₀ := by
      intro k hk
      by_contra hc
      exact Nat.find_min hsplit hk (not_le.mp hc)
    have hn₀gt : C₀ < Lt n₀ := Nat.find_spec hsplit
    have hn₀tail : ∀ k, n₀ ≤ k → C₀ + 1 ≤ Lt k := by
      intro k hk
      have h1 : Lt n₀ ≤ Lt k := hLtmono hk
      omega
    have htailmono : Monotone (fun k : ℕ => Lt (n₀ + k)) :=
      fun a b hab => hLtmono (by omega)
    have htaille : ∀ k : ℕ, C₀ + 1 ≤ Lt (n₀ + k) :=
      fun k => hn₀tail _ (by omega)
    by_cases hn₀0 : n₀ = 0
    · -- the threshold is already exceeded at the very first level: the whole family is a tail
      have hall : ∀ k : ℕ, C₀ + 1 ≤ Lt k := by
        intro k
        refine hn₀tail k ?_
        omega
      have hEst : ∀ i ∈ Finset.range l₂,
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
                - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        intro i hi
        have hi2 : i + 1 ≤ l₂ := by have := Finset.mem_range.mp hi; omega
        have harc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_tail (i + 1) (-(m₀ : ℤ)) := by
          have h := hbase hDt (i + 1) hi2
          have h' : Cρ_tail * (2 : ℝ) ^ (ρ * ((i : ℝ) + 1)) ≤ (m₀ : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one] using h
          rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
          simpa only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_mul]
            using neg_le_neg h'
        have hw : 3 * Work.Analysis.IonescuWainger.iwQl ρ (i + 1) < 2 ^ C₀ :=
          lt_of_le_of_lt (Nat.mul_le_mul_left 3 (iwQl_mono' hρ hρ1 hi2)) h3Q
        have h1 := hTail (i + 1) m₀ C₀ Lt hLtmono hall harc hw hm₀C₀ f
        rw [hpe] at h1
        refine h1.trans ?_
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        nlinarith [hC_head.le, hC_tail.le, hC_1.le]
      exact Work.KMTAreas.A7Rescue.eLpNorm_le_of_pieces
        (F := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
        (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x))
        (v := fun i : ℕ => fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
            - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
        (f := f)
        (C_plain := C_plain)
        (B := C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1)
        (C := ((K : ℝ) + 3) * (max (max C_plain C_head) (C_tail + 12 * C_1) + 1))
        (by positivity) (by positivity) (le_of_lt hp) (ne_of_lt hptop)
        hwalk hEst0 hEst hconst
    · have hn₀pos : 1 ≤ n₀ := by omega
      have hpadmono : Monotone (fun k : ℕ => Lt (min k (n₀ - 1))) :=
        fun a b hab => hLtmono (min_le_min_right _ hab)
      have hpadle : ∀ k : ℕ, Lt (min k (n₀ - 1)) ≤ C₀ := by
        intro k
        refine hn₀lt _ ?_
        have h1 : min k (n₀ - 1) ≤ n₀ - 1 := min_le_right _ _
        omega
      -- the first link: the pad decomposition, pointwise in `x` and in the piece index `i`
      have hpt : ∀ (i : ℕ) (x : ℤ),
          PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => A i k x)
            ≤ PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => A i (min k (n₀ - 1)) x)
              + PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => A i (n₀ + k) x)
              + 3 * ‖A i n₀ x - A i (n₀ - 1) x‖ₑ := by
        intro i x
        have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
        exact Work.KMTAreas.A7Rescue.piecePadDecomp' r hr1 ρ m₀ n₀ Lt f hn₀pos i x
      have hEst : ∀ i ∈ Finset.range l₂,
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
                - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        intro i hi
        have hi2 : i + 1 ≤ l₂ := by have := Finset.mem_range.mp hi; omega
        have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
        have harcH : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_head (i + 1) (-(m₀ : ℤ)) := by
          have h := hbase hDh (i + 1) hi2
          have h' : Cρ_head * (2 : ℝ) ^ (ρ * ((i : ℝ) + 1)) ≤ (m₀ : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one] using h
          rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
          simpa only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_mul]
            using neg_le_neg h'
        have harcT : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_tail (i + 1) (-(m₀ : ℤ)) := by
          have h := hbase hDt (i + 1) hi2
          have h' : Cρ_tail * (2 : ℝ) ^ (ρ * ((i : ℝ) + 1)) ≤ (m₀ : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one] using h
          rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
          simpa only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_mul]
            using neg_le_neg h'
        have hw : 3 * Work.Analysis.IonescuWainger.iwQl ρ (i + 1) < 2 ^ C₀ :=
          lt_of_le_of_lt (Nat.mul_le_mul_left 3 (iwQl_mono' hρ hρ1 hi2)) h3Q
        -- the head bound (a direct level-map application of `hHead`)
        have hHead3 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => A i (min k (n₀ - 1)) x)) p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1)) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          hHead (i + 1) m₀ C₀ (fun k : ℕ => Lt (min k (n₀ - 1))) hpadmono hpadle harcH f
        -- the tail bound (a direct level-map application of `hTail`, after `hpe`)
        have hTail3 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => A i (n₀ + k) x)) p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C_tail * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          have h := hTail (i + 1) m₀ C₀ (fun k : ℕ => Lt (n₀ + k)) htailmono htaille
            harcT hw hm₀C₀ f
          rw [hpe] at h
          exact h
        -- the single-scale bound for one `lpf` at a level `k ≤ C₀`
        have hSingle : ∀ (l : ℕ) (k : ℕ), l ≤ l₂ →
            MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x‖ₑ)
                (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal C_1 *
                  MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
          intro l k hl
          have harc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_1 l
              (-(((m₀ : ℤ) + (k : ℤ)))) := by
            have h := hbase hD1 l hl
            rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
            push_cast
            have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
            nlinarith [h, hk]
          have h' := hB1 l (-(((m₀ : ℤ) + (k : ℤ)))) harc f
          rw [eLpNorm_enorm_eq' (g := fun x : ℤ => Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x)
            (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
          simpa only [Work.KMTAreas.A7Hi.lpf] using h'
        -- the boundary term is a four-term combination of single-scale pieces
        have hsplit : ∀ x : ℤ, A i n₀ x - A i (n₀ - 1) x
            = (Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x
                - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x)
              - (Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x
                - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x) := by
          intro x
          rw [hAfst i n₀ x, hAfst i (n₀ - 1) x]
        have hC : MeasureTheory.eLpNorm (fun x : ℤ => 3 * ‖A i n₀ x - A i (n₀ - 1) x‖ₑ)
            p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (12 * C_1) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          -- the four single-scale bounds
          have h1 := hSingle (i + 1) (Lt n₀) hi2
          have h2 := hSingle i (Lt n₀) (by omega)
          have h3 := hSingle (i + 1) (Lt (n₀ - 1)) hi2
          have h4 := hSingle i (Lt (n₀ - 1)) (by omega)
          -- the pointwise triangle inequality for the four-term combination
          have hnorm : ∀ x : ℤ, ‖A i n₀ x - A i (n₀ - 1) x‖ₑ
              ≤ ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ := by
            intro x
            rw [hsplit x]
            calc ‖(Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x
                    - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x)
                  - (Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x
                    - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x)‖ₑ
                ≤ ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x
                    - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ
                  + ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x
                    - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ := enorm_sub_le
              _ ≤ (‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                    + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ)
                  + (‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ
                    + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ) :=
                  add_le_add enorm_sub_le enorm_sub_le
              _ = ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                    + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ
                    + ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ
                    + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ := by ac_rfl
          -- move to the four-term sum, split it, and apply the four bounds
          have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
            (μ := MeasureTheory.Measure.count) (q := ENNReal.ofReal p.toReal) hnorm
            (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
          have hsplit4 : MeasureTheory.eLpNorm (fun x : ℤ =>
                ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                  + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ
                  + ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ
                  + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ)
                (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
              ≤ (ENNReal.ofReal C_1 + ENNReal.ofReal C_1 + ENNReal.ofReal C_1 + ENNReal.ofReal C_1)
                  * MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
            have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p.toReal := by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
            have hqt : ENNReal.ofReal p.toReal ≠ ⊤ := ENNReal.ofReal_ne_top
            refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
              (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ)
              (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt (n₀ - 1)) f x‖ₑ)
              hq1 hqt).trans ?_
            refine (add_le_add (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
              (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ
                + ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ)
              (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt (n₀ - 1)) f x‖ₑ)
              hq1 hqt) le_rfl).trans ?_
            refine (add_le_add (add_le_add (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
              (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n₀) f x‖ₑ)
              (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n₀) f x‖ₑ)
              hq1 hqt) le_rfl) le_rfl).trans ?_
            refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans ?_
            rw [← add_mul, ← add_mul, ← add_mul]
          -- pull out the factor `3` and compare exponents
          have hthree : MeasureTheory.eLpNorm (fun x : ℤ => (3 : ℝ≥0∞) * ‖A i n₀ x - A i (n₀ - 1) x‖ₑ)
              (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
              = (3 : ℝ≥0∞) * MeasureTheory.eLpNorm
                  (fun x : ℤ => ‖A i n₀ x - A i (n₀ - 1) x‖ₑ)
                  (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
            Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (3 : ℝ≥0∞))
              (by norm_num) (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
          have hscalar : (3 : ℝ≥0∞) * (ENNReal.ofReal C_1 + ENNReal.ofReal C_1
                + ENNReal.ofReal C_1 + ENNReal.ofReal C_1) = ENNReal.ofReal (12 * C_1) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
            congr 1
            ring
          rw [← hpe, hthree]
          have hchain : (3 : ℝ≥0∞) * MeasureTheory.eLpNorm
                (fun x : ℤ => ‖A i n₀ x - A i (n₀ - 1) x‖ₑ)
                (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal (12 * C_1) *
                  MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
            (mul_le_mul_of_nonneg_left (hmono.trans hsplit4)
              (by norm_num : (0 : ℝ≥0∞) ≤ 3)).trans
              (le_of_eq (by rw [← mul_assoc, hscalar]))
          exact hchain
        -- case 3, final combination: monotonicity of `eLpNorm` on `hpt`, then the three bounds
        refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal (μ := MeasureTheory.Measure.count)
          (q := p) (fun x : ℤ => hpt i x)
          (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)).trans ?_
        refine ((Work.KMTAreas.A7.eLpNorm_add_le_ennreal
          (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => A i (min k (n₀ - 1)) x)
            + PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => A i (n₀ + k) x))
          (v := fun x : ℤ => (3 : ℝ≥0∞) * ‖A i n₀ x - A i (n₀ - 1) x‖ₑ)
          (le_of_lt hp) (ne_of_lt hptop)).trans ?_)
        refine ((add_le_add (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
          (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => A i (min k (n₀ - 1)) x))
          (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => A i (n₀ + k) x))
          (le_of_lt hp) (ne_of_lt hptop)) le_rfl).trans ?_)
        refine ((add_le_add (add_le_add hHead3 hTail3) hC).trans ?_)
        rw [← add_mul, ← add_mul,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact Work.KMTAreas.A7Rescue.eLpNorm_le_of_pieces
        (F := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
        (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x))
        (v := fun i : ℕ => fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
            - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
        (f := f)
        (C_plain := C_plain)
        (B := C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1)
        (C := ((K : ℝ) + 3) * (max (max C_plain C_head) (C_tail + 12 * C_1) + 1))
        (by positivity) (by positivity) (le_of_lt hp) (ne_of_lt hptop)
        hwalk hEst0 hEst hconst
  · -- ###### NO-SPLIT BRANCH: every level lies in the head ######
    have hLtleC₀ : ∀ k, Lt k ≤ C₀ := forall_le_of_not_exists_gt hsplit
    have hEst : ∀ i ∈ Finset.range l₂,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
              - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      intro i hi
      have hi2 : i + 1 ≤ l₂ := by have := Finset.mem_range.mp hi; omega
      have harc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_head (i + 1) (-(m₀ : ℤ)) := by
        have h := hbase hDh (i + 1) hi2
        have h' : Cρ_head * (2 : ℝ) ^ (ρ * ((i : ℝ) + 1)) ≤ (m₀ : ℝ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using h
        rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
        simpa only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_mul]
          using neg_le_neg h'
      refine (hHead (i + 1) m₀ C₀ Lt hLtmono hLtleC₀ harc f).trans ?_
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      nlinarith [hC_head.le, hC_tail.le, hC_1.le]
    exact Work.KMTAreas.A7Rescue.eLpNorm_le_of_pieces
      (F := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
      (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (Lt n) f x))
      (v := fun i : ℕ => fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt n) f x
          - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt n) f x))
      (f := f)
      (C_plain := C_plain)
      (B := C_head * ((Nat.clog 2 (C₀ + 1) : ℝ) + 1) + C_tail + 12 * C_1)
      (C := ((K : ℝ) + 3) * (max (max C_plain C_head) (C_tail + 12 * C_1) + 1))
      (by positivity) (by positivity) (le_of_lt hp) (ne_of_lt hptop)
      hwalk hEst0 hEst hconst

end Work.KMTAreas.A7Rescue
