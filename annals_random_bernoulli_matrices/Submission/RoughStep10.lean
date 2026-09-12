import Mathlib
import Submission.Sec3Tower
import Submission.RoughDecay
import Submission.RoughDecay2
import Submission.RoughProduct
import Submission.Admissible
import Submission.RoughAssembly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Step 10 — descendant containment into the sumset `D`

Finishes Proposition `p: rough decay` in counting form.  This module
implements the parts announced as "Step 10" of the rough-decay assembly:

(a) the containment lemma: the root `t₀ = W.t 0` of a walk whose top value
    exceeds `θ := 1/(N√n)` lies in the sumset
    `D := {s | θ < f s} + Σ_j (A_j ∪ {0} + A_j ∪ {0})`
    (origin symmetry of each `A_j` required);
(b) a finite `D0` with `D ⊆ D0` and a cardinality bound
    `|D0| ≤ N√n·(4ℓ·r + 1)` for a radius bound `A_j ⊆ Icc (−r) r`;
(c) the discharge of `RoughAssembly.event_count_le`'s `hCover` hypothesis,
    giving the counting-form rough-decay theorem.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Measure

namespace Submission.RoughStep10

attribute [local instance] Classical.propDecidable

open Submission.Sec3
open Submission.Sec3Tower
open Submission.IntFun
open Submission.RoughDecay
open Submission.RoughDecay2
open Submission.RoughProduct
open Submission.Admissible
open Submission.RoughAssembly
open Submission.ProdCount

/-! ## 1. Full-level identity and the weighted-average lemma -/

/-- The full-level averaged function equals the plain average over `x`
(the `pre` restriction at the top is the identity). -/
lemma flvl_full_eq_avgF {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} (x : Fin ℓ → ℤ) :
    flvl f p x ℓ (Nat.le_refl ℓ) = avgF f p ℓ x := by
  funext t
  dsimp [flvl, avgF, subSum, pre]

/-- If the weighted average `avgF f p ℓ x t` exceeds `θ`, then some subset
`B` contributes an atom `f (t + subSum x B) > θ`. -/
lemma exists_subset_large_of_avgF_gt {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval}
    {x : Fin ℓ → ℤ} {t : ℤ} {θ : ℝ} (hθ : 0 < θ) (hgt : θ < avgF f p ℓ x t) :
    ∃ B : Finset (Fin ℓ),
      B ∈ (Finset.univ : Finset (Fin ℓ)).powerset ∧ θ < f (t + subSum x B) := by
  classical
  let s : Finset (Finset (Fin ℓ)) := (Finset.univ : Finset (Fin ℓ)).powerset
  by_contra hnot
  have hle : ∀ B : Finset (Fin ℓ), B ∈ s → f (t + subSum x B) ≤ θ := by
    intro B hB
    by_contra h
    exact hnot ⟨B, hB, lt_of_not_ge h⟩
  have hsum_le : (∑ B ∈ s, wB ℓ p B * f (t + subSum x B)) ≤ θ := by
    calc
      (∑ B ∈ s, wB ℓ p B * f (t + subSum x B))
          ≤ ∑ B ∈ s, wB ℓ p B * θ := by
            apply Finset.sum_le_sum
            intro B hB
            exact mul_le_mul_of_nonneg_left (hle B hB) (wB_nonneg ℓ p B)
      _ = (∑ B ∈ s, wB ℓ p B) * θ := by
            rw [Finset.sum_mul]
      _ = θ := by
            rw [sum_wB_eq_one ℓ p]
            simp
  have hgt' : θ < (∑ B ∈ s, wB ℓ p B * f (t + subSum x B)) := by
    simpa [s, avgF] using hgt
  linarith

/-- Full-level variant via `flvl`. -/
lemma exists_subset_large_of_flvl_gt {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval}
    {x : Fin ℓ → ℤ} {t : ℤ} {θ : ℝ} (hθ : 0 < θ)
    (hgt : θ < flvl f p x ℓ (Nat.le_refl ℓ) t) :
    ∃ B : Finset (Fin ℓ),
      B ∈ (Finset.univ : Finset (Fin ℓ)).powerset ∧ θ < f (t + subSum x B) := by
  have hgt' : θ < avgF f p ℓ x t := by
    rw [flvl_full_eq_avgF (f := f) (p := p) x] at hgt
    exact hgt
  exact exists_subset_large_of_avgF_gt (f := f) (p := p) (x := x) (t := t) hθ hgt'

/-! ## 2. The sumset `D` and containment of the walk root -/

/-- Membership in the sumset
`D := {s | θ < f s} + Σ_j (A_j ∪ {0} + A_j ∪ {0})`:
`t = s + Σ_j (z₁ j) + Σ_j (z₂ j)` with each `zᵢ j ∈ A_j` or `zᵢ j = 0`. -/
def Dmem {ℓ : ℕ} (f : ℤ → ℝ) (θ : ℝ) (A : Fin ℓ → Finset ℤ) (t : ℤ) : Prop :=
  ∃ s : ℤ, θ < f s ∧ ∃ z₁ z₂ : Fin ℓ → ℤ,
    (∀ j : Fin ℓ, z₁ j ∈ A j ∨ z₁ j = 0) ∧
    (∀ j : Fin ℓ, z₂ j ∈ A j ∨ z₂ j = 0) ∧
      t = s + (∑ j : Fin ℓ, z₁ j) + (∑ j : Fin ℓ, z₂ j)

/-- `subSum x B` as a full sum with an indicator. -/
lemma subSum_eq_indicator_sum {ℓ : ℕ} (x : Fin ℓ → ℤ) (B : Finset (Fin ℓ)) :
    subSum x B = ∑ j : Fin ℓ, (if j ∈ B then x j else 0) := by
  classical
  dsimp [subSum]
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun j : Fin ℓ => j ∈ B) (f := x)]
  congr 1
  ext j
  simp

/-- Per-coordinate identity: `(v − 1_B)·x = v·x − 1_B·x`. -/
lemma coeff_mul_sub_eq {ℓ : ℕ} (x : Fin ℓ → ℤ) (v : Fin ℓ → ℤ) (B : Finset (Fin ℓ))
    (j : Fin ℓ) :
    (v j - (if j ∈ B then 1 else 0)) * x j = v j * x j - (if j ∈ B then x j else 0) := by
  classical
  by_cases h : j ∈ B <;> simp [h] <;> ring

/-- The walk root decomposes as `root = s₀ + Σ_j (v_j − 1_B(j))·x_j` where
`s₀ := top + subSum x B` is the large atom found by the weighted-average step. -/
lemma root_decomp {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (B : Finset (Fin ℓ)) :
    W.t 0 (Nat.zero_le ℓ) =
      (W.t ℓ (Nat.le_refl ℓ) + subSum x B) +
        (∑ j : Fin ℓ, (walkV W j - (if j ∈ B then 1 else 0)) * x j) := by
  classical
  let v : Fin ℓ → ℤ := walkV W
  let t₀ : ℤ := W.t 0 (Nat.zero_le ℓ)
  let tp : ℤ := W.t ℓ (Nat.le_refl ℓ)
  have hdesc : W.t ℓ (Nat.le_refl ℓ) =
      descPoint x v t₀ ℓ (Nat.le_refl ℓ) := t_eq_descPoint W ℓ (Nat.le_refl ℓ)
  have hmain : t₀ = tp + (∑ j : Fin ℓ, v j * x j) := by
    dsimp [t₀, tp]
    dsimp [descPoint] at hdesc
    have hdesc' : tp = t₀ - (∑ j : Fin ℓ, v j * x j) := by
      simpa using hdesc
    omega
  have hsub : subSum x B = ∑ j : Fin ℓ, (if j ∈ B then x j else 0) := subSum_eq_indicator_sum x B
  have hcoeff : (∑ j : Fin ℓ, (v j - (if j ∈ B then 1 else 0)) * x j) =
      (∑ j : Fin ℓ, v j * x j) - subSum x B := by
    rw [hsub]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact (coeff_mul_sub_eq x v B j)
  calc
    W.t 0 (Nat.zero_le ℓ) = tp + (∑ j : Fin ℓ, v j * x j) := by
          dsimp [tp]
          exact hmain
    _ = (tp + subSum x B) + ((∑ j : Fin ℓ, v j * x j) - subSum x B) := by omega
    _ = (tp + subSum x B) + (∑ j : Fin ℓ, (v j - (if j ∈ B then 1 else 0)) * x j) := by
          rw [hcoeff]

/-- Membership of each `(v_j − 1_B(j))·x_j` in `A_j` or zero (the `x_j` atom
from `hx`, the `−x_j` atom from origin symmetry). -/
lemma coeff_x_mem_single {ℓ : ℕ} {A : Fin ℓ → Finset ℤ} {x v : Fin ℓ → ℤ}
    (hx : ∀ j : Fin ℓ, x j ∈ A j)
    (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j)
    (hv : ∀ j : Fin ℓ, v j = 0 ∨ v j = 1) (B : Finset (Fin ℓ)) (j : Fin ℓ) :
    (v j - (if j ∈ B then 1 else 0)) * x j ∈ A j ∨
      (v j - (if j ∈ B then 1 else 0)) * x j = 0 := by
  classical
  rcases hv j with h0 | h1
  · by_cases hB : j ∈ B
    · left
      have ht : (v j - (if j ∈ B then 1 else 0)) * x j = -x j := by
        rw [h0, if_pos hB]
        ring
      rw [ht]
      exact hsym j (x j) (hx j)
    · right
      have ht : (v j - (if j ∈ B then 1 else 0)) * x j = 0 := by
        rw [h0, if_neg hB]
        simp
      rw [ht]
  · by_cases hB : j ∈ B
    · right
      have ht : (v j - (if j ∈ B then 1 else 0)) * x j = 0 := by
        rw [h1, if_pos hB]
        ring
      rw [ht]
    · left
      have ht : (v j - (if j ∈ B then 1 else 0)) * x j = x j := by
        rw [h1, if_neg hB]
        simp
      rw [ht]
      exact hx j

/-- THE containment: the root of a walk whose top value exceeds `θ` lies in
the sumset `D` (needs each coordinate `x j ∈ A j` and `A j` origin-symmetric). -/
lemma root_mem_D {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (A : Fin ℓ → Finset ℤ)
    (hx : ∀ j : Fin ℓ, x j ∈ A j)
    (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j)
    {θ : ℝ} (hθ : 0 < θ)
    (hbig : θ < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ))) :
    Dmem f θ A (W.t 0 (Nat.zero_le ℓ)) := by
  classical
  rcases exists_subset_large_of_flvl_gt (f := f) (p := p) (x := x)
      (t := W.t ℓ (Nat.le_refl ℓ)) hθ hbig with ⟨B, hBpow, hfB⟩
  let s₀ : ℤ := W.t ℓ (Nat.le_refl ℓ) + subSum x B
  have hfs : θ < f s₀ := by
    dsimp [s₀]
    exact hfB
  let v : Fin ℓ → ℤ := walkV W
  have hv : ∀ j : Fin ℓ, v j = 0 ∨ v j = 1 := by
    intro j
    exact walkV_mem (W := W) j
  let z₁ : Fin ℓ → ℤ := fun j => (v j - (if j ∈ B then 1 else 0)) * x j
  let z₂ : Fin ℓ → ℤ := fun _ => 0
  refine ⟨s₀, hfs, z₁, z₂, ?_, ?_, ?_⟩
  · intro j
    exact coeff_x_mem_single (A := A) (x := x) (v := v) hx hsym hv B j
  · intro j
    simp [z₂]
  · have hroot := root_decomp (W := W) (B := B)
    dsimp [z₁, z₂, s₀] at hroot ⊢
    simp
    exact hroot

/-- Anchor-explicit version of `descendant_nondecay`: from a single point
`t_ℓ` whose level-`ℓ` value is large one gets the backward walk from that very
point with at least `n·ηdec p ε` non-decaying levels. -/
theorem descendant_nondecay_at {p : unitInterval} (hp₀ : 0 < (p : ℝ))
    (hp₁ : (p : ℝ) ≤ 1 / 2) {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ))
    {L : ℝ} (hL0 : 0 < L) {N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n)
    {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {x : Fin ℓ → ℤ} (t_ℓ : ℤ)
    (ht_ℓ : flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ >
      max (L / ((N : ℝ) * Real.sqrt (n : ℝ)))
          (((1 - (p : ℝ) + ε) ^ ℓ) * esup f)) :
    ((ℓ : ℝ) - (decayUpTo (backward_chain f p x t_ℓ)
      (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
      ℓ (Nat.le_refl ℓ) : ℝ)) ≥ (n : ℝ) * ηdec p ε := by
  classical
  let W : BWalk f p x t_ℓ := backward_chain f p x t_ℓ
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  let a : ℝ := 1 - (p : ℝ) + ε
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  let u : ℕ := decayUpTo W T ℓ (Nat.le_refl ℓ)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    have h1 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    nlinarith [hε0]
  have hbpos : 0 < b := by
    dsimp [b]
    have h1 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
    nlinarith [hε0]
  have hba : b < a := by
    dsimp [a, b]
    linarith [hε0]
  have ha1 : a < 1 := by
    dsimp [a]
    linarith [hεp]
  have hWtop : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) =
      flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ := by
    dsimp [W]
    have hh := (backward_chain f p x t_ℓ).htop
    rw [hh]
  have hAt : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ :=
    lt_of_le_of_lt (le_max_left _ _) ht_ℓ
  have hBt : a ^ ℓ * esup f < flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ := by
    have hmax : (((1 - (p : ℝ) + ε) ^ ℓ) * esup f) <
        flvl f p x ℓ (Nat.le_refl ℓ) t_ℓ :=
      lt_of_le_of_lt (le_max_right _ _) ht_ℓ
    simpa [a] using hmax
  have hbig : ∀ (m : ℕ) (hm : m ≤ ℓ),
      T ≤ (ε / (2 * (p : ℝ))) * flvl f p x m hm (W.t m hm) := by
    intro m hm
    have hge := level_ge_top W m hm
    have hAtW : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
        flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
      simpa [hWtop.symm] using hAt
    have hLlt : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
        flvl f p x m hm (W.t m hm) :=
      lt_of_lt_of_le hAtW hge
    have hT : T = (ε / (2 * (p : ℝ))) * (L / ((N : ℝ) * Real.sqrt (n : ℝ))) := by
      dsimp [T, roughT]
      field_simp [show (N : ℝ) ≠ 0 by positivity,
        show Real.sqrt (n : ℝ) ≠ 0 by positivity,
        show (p : ℝ) ≠ 0 by positivity]
    have hmul : (ε / (2 * (p : ℝ))) * (L / ((N : ℝ) * Real.sqrt (n : ℝ))) <
        (ε / (2 * (p : ℝ))) * flvl f p x m hm (W.t m hm) :=
      mul_lt_mul_of_pos_left hLlt (by positivity)
    rw [hT]
    exact le_of_lt hmul
  have hchain := chain_value_bound W T hε0.le hp₀ hp₁ (by nlinarith) hfpos hbig
  have hchain' : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      b ^ u * flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) := by
    simpa [b, u] using hchain
  have hfl0 : flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) ≤ esup f := by
    have hz : flvl f p x 0 (Nat.zero_le ℓ) (W.t 0 (Nat.zero_le ℓ)) =
        f (W.t 0 (Nat.zero_le ℓ)) := flvl_zero (f := f) (p := p) (x := x)
          (W.t 0 (Nat.zero_le ℓ))
    rw [hz]
    exact le_esup hfpos hfsum (W.t 0 (Nat.zero_le ℓ))
  have hbigv : a ^ ℓ * esup f < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
    rwa [hWtop]
  have hbchain' : flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) ≤
      b ^ u * esup f := by
    exact le_trans hchain' (mul_le_mul_of_nonneg_left hfl0 (pow_nonneg hb0 u))
  have hesup0 : 0 < esup f := by
    have hposv : 0 < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
      have hn0 : 0 ≤ a ^ ℓ * esup f := by
        exact mul_nonneg (pow_nonneg (by dsimp [a]; nlinarith : 0 ≤ a) ℓ)
          (esup_nonneg hfpos hfsum)
      exact lt_of_le_of_lt hn0 hbigv
    have hge0 := level_ge_top W 0 (Nat.zero_le ℓ)
    exact lt_of_lt_of_le hposv (le_trans hge0 hfl0)
  have hpowlt : a ^ ℓ < b ^ u := by
    exact lt_of_mul_lt_mul_right (lt_of_lt_of_le hbigv hbchain') (le_of_lt hesup0)
  have hlog := Commons.Analysis.Real.log_geom_decay_steps hbpos hba ha1
    (by exact_mod_cast hn1) (by exact_mod_cast hℓge) hpowlt
  have hlt : (n : ℝ) * ηdec p ε < ((ℓ : ℝ) - (u : ℝ)) := by
    dsimp [ηdec, a, b] at hlog ⊢
    rw [← mul_div_assoc]
    exact hlog
  simpa [W, u, T] using (le_of_lt hlt)


/-! ## 3. From the event to a descendant triple with root in `D` -/

/-- The walk non-decay at level `m` is exactly the `levelCond` condition
(proof arguments are proof-irrelevant). -/
lemma levelCond_iff_ndec {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) (m : Fin ℓ) :
    levelCond f p T x (walkV W) (W.t 0 (Nat.zero_le ℓ)) m.val (m.isLt) ↔
      ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := by
  unfold levelCond
  rw [levelDecays_eq_descPoint (W := W) (T := T) (m := m.val) (Nat.succ_le_of_lt m.isLt)]

/-- Event ⟹ a descendant triple whose root lies in `D`
(`θ := 1/(N√n)`).  Needs `L ≥ 1` (so the top value exceeds `1/(N√n)`),
`x j ∈ A j` for every coordinate, and `A j` origin-symmetric. -/
lemma event_descendant_in_D {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) {L : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L)
    {N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) (hfmass : norm₁ f ≤ 1)
    {x : Fin ℓ → ℤ} {A : Fin ℓ → Finset ℤ}
    (hx : ∀ j : Fin ℓ, x j ∈ A j)
    (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j)
    (hbig : ∃ t : ℤ, flvl f p x ℓ (Nat.le_refl ℓ) t >
      max (L / ((N : ℝ) * Real.sqrt (n : ℝ))) (((1 - (p : ℝ) + ε) ^ ℓ) * esup f))
    {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ ηdec p ε) :
    ∃ t₀ : ℤ,
      Dmem f (1 / ((N : ℝ) * Real.sqrt (n : ℝ))) A t₀ ∧
      ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
        ∃ I : Finset (Fin ℓ),
          I.card = Nat.ceil (η * (n : ℝ)) ∧
          ∀ m ∈ I, levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) x v t₀ m.val (m.isLt) := by
  classical
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  let θ : ℝ := 1 / ((N : ℝ) * Real.sqrt (n : ℝ))
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  rcases hbig with ⟨t, ht⟩
  have hcnt := descendant_nondecay_at (p := p) hp₀ hp₁ (ε := ε) hε0 hεp (L := L) hL0
      (N := N) hN1 (n := n) hn1 (ℓ := ℓ) hℓge hℓle (f := f) hfpos hfsum hfmass (x := x) t ht
  let W : BWalk f p x t := backward_chain f p x t
  have hcnt' : (n : ℝ) * ηdec p ε ≤ (ℓ : ℝ) - (decayUpTo W T ℓ (Nat.le_refl ℓ) : ℝ) := by
    simpa [W, T, roughT] using hcnt
  have hWtop : max (L / ((N : ℝ) * Real.sqrt (n : ℝ)))
        (((1 - (p : ℝ) + ε) ^ ℓ) * esup f) <
      flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
    have htopW : W.t ℓ (Nat.le_refl ℓ) = t := by
      simpa [W] using (backward_chain f p x t).htop
    rwa [← htopW] at ht
  have hWθ : θ < flvl f p x ℓ (Nat.le_refl ℓ) (W.t ℓ (Nat.le_refl ℓ)) := by
    dsimp [θ]
    have hL' : (1 / ((N : ℝ) * Real.sqrt (n : ℝ))) ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
      apply div_le_div_of_nonneg_right hL1
      positivity
    have hmx : L / ((N : ℝ) * Real.sqrt (n : ℝ)) ≤
        max (L / ((N : ℝ) * Real.sqrt (n : ℝ)))
          (((1 - (p : ℝ) + ε) ^ ℓ) * esup f) := le_max_left _ _
    linarith
  have hroot : Dmem f θ A (W.t 0 (Nat.zero_le ℓ)) :=
    root_mem_D (W := W) (A := A) hx hsym hθ hWθ
  let t₀ : ℤ := W.t 0 (Nat.zero_le ℓ)
  let v : Fin ℓ → ℤ := walkV W
  rcases exists_levels_of_decayUpTo (W := W) (T := T) (ηdec := ηdec p ε) (η := η) hcnt' hηle with
    ⟨I, hIsub, hIcard, hIdec⟩
  refine ⟨t₀, ?_, v, ?_, I, hIcard, ?_⟩
  · -- D membership with θ-unfolded
    simpa [θ] using hroot
  · intro j
    exact walkV_mem (W := W) j
  · intro m hm
    have hnd : ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := hIdec m hm
    exact (levelCond_iff_ndec (W := W) (T := T) m).2 hnd

/-! ## 4. The finite superset `D0` of the possible roots -/

/-- The finite superset: roots of walks sit within `Finset.Icc (s±R)` of a
point `s` with `θ < f s`, so take the union of those windows. -/
def DFin (F : Finset ℤ) (R : ℕ) : Finset ℤ :=
  F.biUnion (fun s : ℤ => Finset.Icc (s - (R : ℤ)) (s + (R : ℤ)))

/-- Each window `Icc (s − R) (s + R)` has `2R + 1` points. -/
lemma Icc_window_card (s : ℤ) (R : ℕ) :
    (Finset.Icc (s - (R : ℤ)) (s + (R : ℤ))).card = 2 * R + 1 := by
  calc
    (Finset.Icc (s - (R : ℤ)) (s + (R : ℤ))).card = (s + (R : ℤ) + 1 - (s - (R : ℤ))).toNat := by
          rw [Int.card_Icc]
    _ = (2 * (R : ℤ) + 1).toNat := by
          congr 1
          ring
    _ = 2 * R + 1 := by
          have hnn : 0 ≤ 2 * (R : ℤ) + 1 := by positivity
          have hz := Int.toNat_of_nonneg hnn
          exact_mod_cast hz

/-- `DFin` cardinality bound: `|DFin F R| ≤ |F|·(2R+1)`. -/
lemma DFin_card_le (F : Finset ℤ) (R : ℕ) :
    ((DFin F R).card : ℝ) ≤ (F.card : ℝ) * ((2 * R + 1 : ℕ) : ℝ) := by
  classical
  have hleN : (DFin F R).card ≤ F.card * (2 * R + 1) := by
    have h := Finset.card_biUnion_le (s := F)
      (t := fun s : ℤ => Finset.Icc (s - (R : ℤ)) (s + (R : ℤ)))
    calc
      (DFin F R).card ≤ (∑ a ∈ F, (Finset.Icc (a - (R : ℤ)) (a + (R : ℤ))).card) := by
            dsimp [DFin]
            exact h
      _ = (2 * R + 1) * F.card := by
            calc
              (∑ a ∈ F, (Finset.Icc (a - (R : ℤ)) (a + (R : ℤ))).card)
                  = ∑ a ∈ F, (2 * R + 1) := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    exact Icc_window_card s R
              _ = (2 * R + 1) * F.card := by
                    simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_assoc, Nat.mul_comm]
      _ = F.card * (2 * R + 1) := by rw [Nat.mul_comm]
  exact_mod_cast hleN

/-- A window point belongs to `DFin`. -/
lemma mem_DFin_of_mem_window {F : Finset ℤ} (R : ℕ) {s t : ℤ}
    (hs : s ∈ F) (hwin : t ∈ Finset.Icc (s - (R : ℤ)) (s + (R : ℤ))) :
    t ∈ DFin F R := by
  exact Finset.mem_biUnion.mpr ⟨s, hs, hwin⟩

/-- Decomposition of a `Dmem` point: `t = s + δ` with `θ < f s` and
`|δ| ≤ 2ℓ·r` (each `A j` inside the radius `r`). -/
lemma Dmem_decomp_bound {ℓ : ℕ} {f : ℤ → ℝ} {θ : ℝ} {A : Fin ℓ → Finset ℤ}
    {t : ℤ} (hD : Dmem f θ A t) (r : ℕ)
    (hr : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ (r : ℤ)) :
    ∃ s : ℤ, θ < f s ∧ t ∈ Finset.Icc (s - ((2 * ℓ * r : ℕ) : ℤ)) (s + ((2 * ℓ * r : ℕ) : ℤ)) := by
  classical
  rcases hD with ⟨s, hs, z₁, z₂, hz1, hz2, ht⟩
  have hsum : (∑ j : Fin ℓ, z₁ j) + (∑ j : Fin ℓ, z₂ j) = ∑ j : Fin ℓ, (z₁ j + z₂ j) := by
    rw [Finset.sum_add_distrib]
  have hc : ∀ j : Fin ℓ, |z₁ j + z₂ j| ≤ (2 * (r : ℤ)) := by
    intro j
    have hz1b : |z₁ j| ≤ (r : ℤ) := by
      rcases hz1 j with h | h
      · exact hr j (z₁ j) h
      · rw [h]
        simp
    have hz2b : |z₂ j| ≤ (r : ℤ) := by
      rcases hz2 j with h | h
      · exact hr j (z₂ j) h
      · rw [h]
        simp
    calc
      |z₁ j + z₂ j| ≤ |z₁ j| + |z₂ j| := abs_add_le (z₁ j) (z₂ j)
      _ ≤ (r : ℤ) + (r : ℤ) := by linarith
      _ = 2 * (r : ℤ) := by ring
  have hbound : |(∑ j : Fin ℓ, (z₁ j + z₂ j))| ≤ ((2 * ℓ * r : ℕ) : ℤ) := by
    calc
      |(∑ j : Fin ℓ, (z₁ j + z₂ j))| ≤ (∑ j : Fin ℓ, |z₁ j + z₂ j|) := by
            exact Finset.abs_sum_le_sum_abs (fun j : Fin ℓ => z₁ j + z₂ j) Finset.univ
      _ ≤ (∑ j : Fin ℓ, (2 : ℤ) * (r : ℤ)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hc j
      _ = (2 * (ℓ : ℤ)) * (r : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp
            ring_nf
      _ = ((2 * ℓ * r : ℕ) : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_mul]
            norm_num
  refine ⟨s, hs, ?_⟩
  have htδ : t - s = (∑ j : Fin ℓ, z₁ j) + (∑ j : Fin ℓ, z₂ j) := by omega
  have hz : |t - s| ≤ ((2 * ℓ * r : ℕ) : ℤ) := by
    rw [htδ, hsum]
    exact hbound
  rw [Finset.mem_Icc]
  constructor
  · have h1 := (abs_le.mp hz).1
    omega
  · have h2 := (abs_le.mp hz).2
    omega

/-- Roots of walks (points of `Dmem`) lie inside the finite `DFin` window-set
over the (finite) set of large points of `f`. -/
lemma Dmem_mem_DFin {ℓ : ℕ} {f : ℤ → ℝ} {θ : ℝ} {A : Fin ℓ → Finset ℤ}
    {t : ℤ} (hD : Dmem f θ A t) (r : ℕ)
    (hr : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ (r : ℤ))
    {F : Finset ℤ} (hF : ∀ s : ℤ, θ < f s → s ∈ F) :
    t ∈ DFin F (2 * ℓ * r) := by
  classical
  rcases Dmem_decomp_bound hD r hr with ⟨s, hs, hwin⟩
  exact mem_DFin_of_mem_window (F := F) (R := 2 * ℓ * r) (hF s hs) hwin

/-! ## 5. Discharging the `hCover` hypothesis of `RoughAssembly.event_count_le` -/

/-- The set of points where `f` exceeds `θ` (finite), as a Finset. -/
noncomputable def Fbig (f : ℤ → ℝ) (θ : ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) (hθ : 0 < θ) : Finset ℤ :=
  (finite_above hfpos hfsum hθ).toFinset

/-- Every large point of `f` belongs to `Fbig`. -/
lemma mem_Fbig {f : ℤ → ℝ} {θ : ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) (hθ : 0 < θ) {s : ℤ} (hs : θ < f s) :
    s ∈ Fbig f θ hfpos hfsum hθ := by
  dsimp [Fbig]
  exact (Set.Finite.mem_toFinset (finite_above hfpos hfsum hθ)).2 hs

/-- Every event point yields a descendant triple with root in the finite
window-set `DFin (Fbig f θ) (2ℓ·nN)` (paper's `D ⊆ D0`).  `hθ` is
`0 < 1/(N√n)`. -/
lemma hCover_rough {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) {L : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L)
    {N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) (hfmass : norm₁ f ≤ 1)
    {A : Fin ℓ → Finset ℤ}
    (hrad : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
    (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j)
    {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ ηdec p ε) :
    ∀ x ∈ prodFinset ℓ A, eventPred f p L (N : ℝ) (n : ℝ) ε x →
      ∃ t₀ ∈ DFin (Fbig f (1 / ((N : ℝ) * Real.sqrt (n : ℝ))) hfpos hfsum (by positivity))
            (2 * ℓ * (n * N)),
        ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
          ∃ I : Finset (Fin ℓ),
            I.card = Nat.ceil (η * (n : ℝ)) ∧
            ∀ m ∈ I, levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) x v t₀ m.val (m.isLt) := by
  classical
  intro x hx hEv
  have hxj : ∀ j : Fin ℓ, x j ∈ A j := (mem_prodFinset A x).1 hx
  rcases event_descendant_in_D hp₀ hp₁ hε0 hεp hL0 hL1 hN1 hn1 hℓge hℓle hfpos hfsum hfmass
      hxj hsym hEv hη hηle with ⟨t₀, ht₀D, v, hv, I, hIcard, hIcond⟩
  refine ⟨t₀, ?_, v, hv, I, hIcard, hIcond⟩
  -- t₀ ∈ DFin (Fbig ...) (2·ℓ·(n·N))
  exact Dmem_mem_DFin (A := A) ht₀D (n * N)
      (by
        intro j a ha
        simpa using hrad j a ha)
      (by
        intro s hs
        exact mem_Fbig hfpos hfsum (by positivity : 0 < 1 / ((N : ℝ) * Real.sqrt (n : ℝ))) (s := s) hs)


/-! ## 6. The canonical root window-set `D0` and its size -/

/-- `0 < 1/(N√n)` for `N, n ≥ 1`. -/
lemma theta_pos (N n : ℕ) (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) :
    0 < 1 / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
  have hNℝ : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN1)
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  positivity

/-- `|Fbig f θ| ≤ ‖f‖₁/θ`. -/
lemma Fbig_card_le {f : ℤ → ℝ} {θ : ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) (hθ : 0 < θ) :
    ((Fbig f θ hfpos hfsum hθ).card : ℝ) ≤ norm₁ f / θ := by
  classical
  have hfin : Set.Finite {t : ℤ | θ < f t} := finite_above hfpos hfsum hθ
  have hncard : (({t : ℤ | θ < f t}).ncard : ℝ) ≤ norm₁ f / θ :=
    ncard_above_le hfpos hfsum hθ
  have hc := Set.ncard_eq_toFinset_card (s := {t : ℤ | θ < f t}) hfin
  have hcard : (Fbig f θ hfpos hfsum hθ).card = ({t : ℤ | θ < f t}).ncard := by
    dsimp [Fbig]
    exact hc.symm
  rw [hcard]
  exact hncard

/-- The canonical window-set around the large points of `f`, radius
`2·ℓ·(n·N)`. -/
noncomputable def D0rd {ℓ N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) (f : ℤ → ℝ)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) : Finset ℤ :=
  DFin (Fbig f (1 / ((N : ℝ) * Real.sqrt (n : ℝ))) hfpos hfsum (theta_pos N n hN1 hn1))
    (2 * ℓ * (n * N))

/-- Cardinality bound for `D0rd`: `|D0| ≤ (N√n)·(4ℓnN + 1)` for `‖f‖₁ ≤ 1`. -/
lemma D0rd_card_le {ℓ N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) {f : ℤ → ℝ}
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) (hfmass : norm₁ f ≤ 1) :
    ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ) ≤
      ((N : ℝ) * Real.sqrt (n : ℝ)) * ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by
  classical
  dsimp [D0rd]
  let θ : ℝ := 1 / ((N : ℝ) * Real.sqrt (n : ℝ))
  have hθ : 0 < θ := theta_pos N n hN1 hn1
  have hF : ((Fbig f θ hfpos hfsum hθ).card : ℝ) ≤ (N : ℝ) * Real.sqrt (n : ℝ) := by
    have hb := Fbig_card_le hfpos hfsum hθ
    have hden : norm₁ f / θ = norm₁ f * ((N : ℝ) * Real.sqrt (n : ℝ)) := by
      dsimp [θ]
      field_simp [show (N : ℝ) ≠ 0 by positivity,
        show Real.sqrt (n : ℝ) ≠ 0 by positivity]
    have hsq : 0 ≤ (N : ℝ) * Real.sqrt (n : ℝ) := by positivity
    calc
      ((Fbig f θ hfpos hfsum hθ).card : ℝ) ≤ norm₁ f / θ := hb
      _ = norm₁ f * ((N : ℝ) * Real.sqrt (n : ℝ)) := hden
      _ = ((N : ℝ) * Real.sqrt (n : ℝ)) * norm₁ f := by ring
      _ ≤ ((N : ℝ) * Real.sqrt (n : ℝ)) * 1 := by
            exact mul_le_mul_of_nonneg_left hfmass hsq
      _ = (N : ℝ) * Real.sqrt (n : ℝ) := by ring
  have hDF := DFin_card_le (Fbig f θ hfpos hfsum hθ) (2 * ℓ * (n * N))
  have hw : ((2 * (2 * ℓ * (n * N)) + 1 : ℕ) : ℝ) ≤ ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by
    have hE : ((2 * (2 * ℓ * (n * N)) + 1 : ℕ) : ℝ) = ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by
      norm_num
      ring_nf
    exact le_of_eq hE
  have hwinpos : 0 ≤ ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by positivity
  calc
    ((DFin (Fbig f θ hfpos hfsum hθ) (2 * ℓ * (n * N))).card : ℝ)
        ≤ ((Fbig f θ hfpos hfsum hθ).card : ℝ) *
            ((2 * (2 * ℓ * (n * N)) + 1 : ℕ) : ℝ) := hDF
    _ ≤ ((Fbig f θ hfpos hfsum hθ).card : ℝ) * ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by
          have hFc0 : 0 ≤ ((Fbig f θ hfpos hfsum hθ).card : ℝ) := by
            exact_mod_cast (Nat.zero_le (Fbig f θ hfpos hfsum hθ).card)
          exact mul_le_mul_of_nonneg_left hw hFc0
    _ ≤ ((N : ℝ) * Real.sqrt (n : ℝ)) * ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hF hwinpos

/-! ## 7. The counting-form rough-decay bound -/

/-- Counting form of Proposition `p: rough decay` (union bound over the
descendant triples): for a tuple length `ℓ ∈ [n/2, n]`, an `(N,n,δ)`-admissible
family `A` of origin-symmetric, radius-`nN` coordinate sets, the number of
tuples `x ∈ A₁×…×A_ℓ` at whose level-`ℓ` average is large
(`> max(L/(N√n), (1−p+ε)^ℓ·‖f‖∞)`) is at most
`|D0|·2^ℓ·C(ℓ,⌈ηn⌉)·q^{⌈ηn⌉−⌈δ₀n⌉}·∏|A_j|` with `D0` the canonical window
set and `q := 2p(Cq₁+Cq₂)/(εL√(δ₀p))`.  `hq1 : q ≤ 1` and `hL1` are the
"`L` large enough" hypotheses. -/
theorem rough_decay_counting {n : ℕ} (hn1 : 1 ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδle : δ₀ ≤ δ) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) {L : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L)
    {N : ℕ} (hN1 : 1 ≤ N) {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ ηdec p ε)
    {A : Fin ℓ → Finset ℤ} (hAdm : Admissible N n ℓ δ A)
    (hrad : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
    (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j)
    (Cq₁ : ℝ) (hCq₁pos : 0 < Cq₁) (Cq₂ : ℝ) (hCq₂pos : 0 < Cq₂)
    (hPer₁ : perStepProp Cq₁) (hPer₂ : twoArmProp Cq₂)
    (hq1 : ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤ 1) :
    ((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        eventPred f p L (N : ℝ) (n : ℝ) ε x)).card ≤
      ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ) * (2 : ℝ) ^ ℓ *
        ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
        (((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ^
          ((Nat.ceil (η * (n : ℝ))) - (Nat.ceil (δ₀ * (n : ℝ))))) *
        (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  let D0 : Finset ℤ := D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum
  have hcov : ∀ x ∈ prodFinset ℓ A, eventPred f p L (N : ℝ) (n : ℝ) ε x →
      ∃ t₀ ∈ D0, ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
        ∃ I : Finset (Fin ℓ), I.card = Nat.ceil (η * (n : ℝ)) ∧
          ∀ m ∈ I, levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) x v t₀ m.val (m.isLt) := by
    intro x hx hEv
    have hcr := hCover_rough hp₀ hp₁ hε0 hεp hL0 hL1 hN1 hn1 hℓge hℓle hfpos hfsum hfmass
      hrad hsym hη hηle x hx hEv
    simpa [D0, D0rd] using hcr
  have hmain := event_count_le hn1 hδ₀ hδle hslack hp₀ hp₁ hε0 hεp hL0 hN1 hℓge hℓle
    hfpos hfsum hfmass hη hηle hAdm (D0 := D0) Cq₁ hCq₁pos Cq₂ hCq₂pos hPer₁ hPer₂ hq1 hcov
  simpa [D0, D0rd] using hmain

end Submission.RoughStep10
