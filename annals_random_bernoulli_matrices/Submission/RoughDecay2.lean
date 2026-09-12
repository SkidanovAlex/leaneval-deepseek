import Mathlib
import Submission.Sec3Tower
import Submission.RoughDecay
import Submission.ProdCount

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Proposition p:rough decay — part 2 (counting layer, infrastructure)

On top of `Submission.RoughDecay` (per-step Markov bounds) and
`Submission.Sec3Tower` (the deterministic descendant containment
`descendant_nondecay`) this module develops the counting layer of Proposition
`p: rough decay`.  Part 1 (this file) contains the deterministic bridge:

- the `descPoint` (prefix descendant): `t_m := t₀ − Σ_{j<m} v_j·x_j`,
- the extraction of the {0,1}-pattern `v` from a `BWalk` (the walk's level-`m`
  point equals the descendant `descPoint x v (W.t 0) m`, so the walk's
  deterministic decay levels are exactly the non-decay levels of the
  prefix-descendant sequence),
- the set of non-decaying levels of a walk and its cardinality,
- picking a subset `I` of `⌈ηn⌉` non-decaying levels.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Measure

namespace Submission.RoughDecay2

attribute [local instance] Classical.propDecidable

open Submission.Sec3Tower
open Submission.Sec3
open Submission.RoughDecay
open Submission.IntFun

/-! ## 1. Prefix descendants -/

/-- The prefix-descendant point at level `m` of a sequence with pattern `v`:
`t_m := t₀ − Σ_{j<m} v_j·x_j`.  (Depends only on the first `m` coordinates.) -/
def descPoint {ℓ : ℕ} (x : Fin ℓ → ℤ) (v : Fin ℓ → ℤ) (t₀ : ℤ) (m : ℕ)
    (hm : m ≤ ℓ) : ℤ :=
  t₀ - ∑ j : Fin m, v (Fin.castLE hm j) * x (Fin.castLE hm j)

/-- The level-0 descendant is the root. -/
lemma descPoint_zero {ℓ : ℕ} (x : Fin ℓ → ℤ) (v : Fin ℓ → ℤ) (t₀ : ℤ) :
    descPoint x v t₀ 0 (Nat.zero_le ℓ) = t₀ := by
  simp [descPoint]

/-- One-step recursion: adding coordinate `m`. -/
lemma descPoint_succ {ℓ : ℕ} (x : Fin ℓ → ℤ) (v : Fin ℓ → ℤ) (t₀ : ℤ)
    {m : ℕ} (hm : m + 1 ≤ ℓ) :
    descPoint x v t₀ (m + 1) hm =
      descPoint x v t₀ m (Nat.le_trans (Nat.le_succ m) hm) -
        v ⟨m, Nat.lt_of_succ_le hm⟩ * x ⟨m, Nat.lt_of_succ_le hm⟩ := by
  dsimp [descPoint]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.castLE]
  ring_nf

/-! ## 2. Extracting the pattern from a backward walk -/

/-- The pattern `v ∈ {0,1}^ℓ` of a walk: `v_j = 1` iff the walk's step at level
`j` added `x_j` (so `W.t j = W.t (j+1) + x_j`). -/
def walkV {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) : Fin ℓ → ℤ :=
  fun j =>
    if W.t j.val (Nat.le_of_lt j.isLt) =
        W.t (j.val + 1) (Nat.succ_le_of_lt j.isLt) + x j then 1 else 0

/-- Each pattern value is `0` or `1`. -/
lemma walkV_mem {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (j : Fin ℓ) :
    walkV W j = 0 ∨ walkV W j = 1 := by
  classical
  unfold walkV
  by_cases h : W.t j.val (Nat.le_of_lt j.isLt) =
      W.t (j.val + 1) (Nat.succ_le_of_lt j.isLt) + x j
  · right; simp [h]
  · left; simp [h]

/-- The walk step at level `m`: `W.t m = W.t (m+1) + v_m·x_m`. -/
lemma walkV_rel {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) {m : ℕ} (hm1 : m + 1 ≤ ℓ) :
    W.t m (Nat.le_trans (Nat.le_succ m) hm1) =
      W.t (m + 1) hm1 + walkV W ⟨m, Nat.lt_of_succ_le hm1⟩ * x ⟨m, Nat.lt_of_succ_le hm1⟩ := by
  classical
  have hrel := W.hrel m hm1
  have h1 : W.t m (Nat.le_trans (Nat.le_succ m) hm1) =
      W.t m (Nat.le_of_lt (Nat.lt_of_succ_le hm1)) := W.t_irrel
  have h2 : W.t (m + 1) hm1 = W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) := W.t_irrel
  rcases hrel with hl | hr
  · -- added
    have hl' : W.t m (Nat.le_of_lt (Nat.lt_of_succ_le hm1)) =
        W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) + x ⟨m, Nat.lt_of_succ_le hm1⟩ := by
      simpa using hl
    have hv : walkV W ⟨m, Nat.lt_of_succ_le hm1⟩ = 1 := by
      unfold walkV
      simp [hl']
    rw [hv]
    rw [← h1, ← h2]
    simpa using hl
  · -- not added (W.t m = W.t (m+1)); then v_m = 1 only if x_m = 0
    have hr' : W.t m (Nat.le_of_lt (Nat.lt_of_succ_le hm1)) =
        W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) := by
      simpa using hr
    by_cases hx : x ⟨m, Nat.lt_of_succ_le hm1⟩ = 0
    · have hv : walkV W ⟨m, Nat.lt_of_succ_le hm1⟩ = 1 := by
        unfold walkV
        simp [hx, hr']
      rw [hv]
      rw [← h1, ← h2]
      simp [hr, hx]
    · have hv : walkV W ⟨m, Nat.lt_of_succ_le hm1⟩ = 0 := by
        unfold walkV
        have hcond : ¬ W.t m (Nat.le_of_lt (Nat.lt_of_succ_le hm1)) =
            W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)) + x ⟨m, Nat.lt_of_succ_le hm1⟩ := by
          intro hc
          apply hx
          omega
        simp [hcond]
      rw [hv]
      rw [← h1, ← h2]
      simp [hr]

/-- The walk's level-`m` point is the prefix descendant of its root `W.t 0`
with pattern `walkV W`. -/
lemma t_eq_descPoint {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (m : ℕ) (hm : m ≤ ℓ) :
    W.t m hm = descPoint x (walkV W) (W.t 0 (Nat.zero_le ℓ)) m hm := by
  classical
  induction m with
  | zero =>
      rw [descPoint_zero]
  | succ m ih =>
      have hstep := walkV_rel (W := W) (m := m) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm))
      have hprevm : m ≤ ℓ := Nat.le_trans (Nat.le_succ m) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm))
      have hrel' : W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm)) =
          W.t m hprevm - walkV W ⟨m, Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm))⟩ *
            x ⟨m, Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm))⟩ := by
        have h1 : W.t m (Nat.le_trans (Nat.le_succ m) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm))) =
            W.t m hprevm := W.t_irrel
        have h2 : W.t (m + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm)) = W.t (m + 1) hm := W.t_irrel
        have hs : W.t m hprevm =
            W.t (m + 1) hm + walkV W ⟨m, Nat.lt_of_succ_le hm⟩ * x ⟨m, Nat.lt_of_succ_le hm⟩ := by
          simpa [h1, h2] using hstep
        omega
      rw [hrel']
      rw [descPoint_succ]
      simpa using ih hprevm

/-- The level-`m` decay test of a walk, expressed at the descendant point. -/
lemma levelDecays_eq_descPoint {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) {m : ℕ} (hm1 : m + 1 ≤ ℓ) :
    levelDecays W T m hm1 ↔
      decaysAt (flvl f p x m (Nat.le_trans (Nat.le_succ m) hm1))
        (x ⟨m, Nat.lt_of_succ_le hm1⟩) T
        (descPoint x (walkV W) (W.t 0 (Nat.zero_le ℓ)) m (Nat.le_trans (Nat.le_succ m) hm1)) := by
  have hw : W.t m (Nat.le_trans (Nat.le_succ m) hm1) =
      descPoint x (walkV W) (W.t 0 (Nat.zero_le ℓ)) m (Nat.le_trans (Nat.le_succ m) hm1) :=
    t_eq_descPoint W m (Nat.le_trans (Nat.le_succ m) hm1)
  unfold levelDecays
  rw [hw]

/-! ## 3. The set of non-decaying levels -/

/-- The set of non-decaying levels of a walk (`m : Fin ℓ` ↔ level `m`). -/
def ndecFinset {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) : Finset (Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ)).filter (fun m : Fin ℓ =>
    ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt))

/-- The set of decaying levels of a walk. -/
def decFinset {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) : Finset (Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ)).filter (fun m : Fin ℓ =>
    levelDecays W T m.val (Nat.succ_le_of_lt m.isLt))

/-- A level belongs to `ndecFinset` iff it does not decay. -/
lemma mem_ndecFinset {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) (m : Fin ℓ) :
    m ∈ ndecFinset W T ↔ ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := by
  classical
  simp [ndecFinset]

/-- The decay test is independent of the choice of proof that `m+1 ≤ ℓ`. -/
lemma levelDecays_proof_irrel {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) {m : ℕ} {hm1 hm1' : m + 1 ≤ ℓ} :
    levelDecays W T m hm1 = levelDecays W T m hm1' := by
  simp [levelDecays, decaysAt]

/-- Decay indicator at a level, for the recursion identity of `decayUpTo`. -/
noncomputable def decIndOf {ℓ k : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) (hk : k ≤ ℓ) (m : Fin k) : ℕ :=
  if levelDecays W T m.val (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le m.isLt hk)) then 1 else 0

/-- `decayUpTo` counts the decaying levels (recursion identity as a sum). -/
lemma decayUpTo_eq_sum {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) :
    decayUpTo W T ℓ (Nat.le_refl ℓ) = ∑ m : Fin ℓ, decIndOf W T (Nat.le_refl ℓ) m := by
  classical
  have gen : ∀ (k : ℕ) (hk : k ≤ ℓ), decayUpTo W T k hk = ∑ m : Fin k, decIndOf W T hk m := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp [decayUpTo, decIndOf]
    | succ k ih =>
        intro hk1
        have hrec : decayUpTo W T (k + 1) hk1 =
            decayUpTo W T k (Nat.le_trans (Nat.le_succ k) hk1) +
              (if levelDecays W T k hk1 then 1 else 0) := by
          simp [decayUpTo]
        rw [hrec]
        rw [Fin.sum_univ_castSucc]
        have hsum' : (∑ m : Fin k, decIndOf W T hk1 (m.castSucc)) =
            (∑ m : Fin k, decIndOf W T (Nat.le_trans (Nat.le_succ k) hk1) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          unfold decIndOf
          apply congr_arg (fun b : Prop => if b then 1 else 0)
          apply levelDecays_proof_irrel
        rw [hsum']
        rw [ih (Nat.le_trans (Nat.le_succ k) hk1)]
        have hlast : decIndOf W T hk1 (Fin.last k) =
            (if levelDecays W T k hk1 then 1 else 0) := by
          unfold decIndOf
          apply congr_arg (fun b : Prop => if b then 1 else 0)
          apply levelDecays_proof_irrel
        rw [hlast]
  exact gen ℓ (Nat.le_refl ℓ)

/-- The set of decaying levels has cardinality `decayUpTo W T ℓ`. -/
lemma decFinset_card_eq {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) :
    (decFinset W T).card = decayUpTo W T ℓ (Nat.le_refl ℓ) := by
  classical
  rw [decayUpTo_eq_sum (W := W) (T := T)]
  unfold decFinset decIndOf
  rw [Finset.card_filter]

/-- `decayUpTo` never exceeds the number of levels. -/
lemma decayUpTo_le {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) (m : ℕ) (hm : m ≤ ℓ) :
    decayUpTo W T m hm ≤ m := by
  classical
  induction m with
  | zero => simp [decayUpTo]
  | succ m ih =>
      have hrec : decayUpTo W T (m + 1) hm =
          decayUpTo W T m (Nat.le_trans (Nat.le_succ m) hm) +
            (if levelDecays W T m hm then 1 else 0) := by
        simp [decayUpTo]
      rw [hrec]
      have h1 : decayUpTo W T m (Nat.le_trans (Nat.le_succ m) hm) ≤ m := ih (Nat.le_trans (Nat.le_succ m) hm)
      have hd : (if levelDecays W T m hm then 1 else 0) ≤ 1 := by
        by_cases h : levelDecays W T m hm
        · simp [h]
        · simp [h]
      omega

/-- The number of non-decaying levels equals `ℓ − decayUpTo W T ℓ`. -/
lemma ndecFinset_card {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) :
    (ndecFinset W T).card = ℓ - decayUpTo W T ℓ (Nat.le_refl ℓ) := by
  classical
  let p : Fin ℓ → Prop := fun m => levelDecays W T m.val (Nat.succ_le_of_lt m.isLt)
  have hdec_le : decayUpTo W T ℓ (Nat.le_refl ℓ) ≤ ℓ := decayUpTo_le W T ℓ (Nat.le_refl ℓ)
  have h1 : (ndecFinset W T).card = ∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (if ¬ p m then 1 else 0) := by
    dsimp [ndecFinset, p]
    rw [Finset.card_filter]
  have h2 : (decFinset W T).card = ∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (if p m then 1 else 0) := by
    dsimp [decFinset, p]
    rw [Finset.card_filter]
  have hones : (∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (1 : ℕ)) = ℓ := by
    rw [← Finset.card_eq_sum_ones (s := (Finset.univ : Finset (Fin ℓ)))]
    simp
  have hsum1 : (∑ m ∈ (Finset.univ : Finset (Fin ℓ)), ((if ¬ p m then 1 else 0) + (if p m then 1 else 0))) = ℓ := by
    calc
      (∑ m ∈ (Finset.univ : Finset (Fin ℓ)), ((if ¬ p m then 1 else 0) + (if p m then 1 else 0)))
          = ∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases h : p m
            · simp [h]
            · simp [h]
      _ = ℓ := hones
  have hs : (∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (if ¬ p m then 1 else 0)) +
      (∑ m ∈ (Finset.univ : Finset (Fin ℓ)), (if p m then 1 else 0)) = ℓ := by
    rw [← Finset.sum_add_distrib]
    exact hsum1
  have hpart : (ndecFinset W T).card + (decFinset W T).card = ℓ := by
    rw [h1, h2]
    exact hs
  have hdec : (decFinset W T).card = decayUpTo W T ℓ (Nat.le_refl ℓ) := decFinset_card_eq (W := W) (T := T)
  have hsum : (ndecFinset W T).card + decayUpTo W T ℓ (Nat.le_refl ℓ) = ℓ := by
    rwa [hdec] at hpart
  exact ((Nat.sub_eq_iff_eq_add hdec_le).2 hsum.symm).symm

/-! ## 4. Choosing `⌈ηn⌉` non-decaying levels -/

/-- From `n·ηdec ≤ #(non-decaying levels)` and `η ≤ ηdec` one can select a
subset of exactly `⌈η·n⌉` non-decaying levels. -/
lemma exists_levels_nondecay {ℓ n : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) {ηdec η : ℝ}
    (hcnt : (n : ℝ) * ηdec ≤ (ndecFinset W T).card)
    (hηle : η ≤ ηdec) :
    ∃ I : Finset (Fin ℓ), I ⊆ ndecFinset W T ∧
      I.card = Nat.ceil (η * (n : ℝ)) ∧
      ∀ m ∈ I, ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := by
  classical
  have hc : η * (n : ℝ) ≤ (ndecFinset W T).card := by
    calc
      η * (n : ℝ) ≤ ηdec * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hηle (by positivity : 0 ≤ (n : ℝ))
      _ = (n : ℝ) * ηdec := by ring
      _ ≤ (ndecFinset W T).card := hcnt
  have hceil : Nat.ceil (η * (n : ℝ)) ≤ (ndecFinset W T).card := by
    exact Nat.ceil_le.mpr hc
  rcases Finset.exists_subset_card_eq (s := ndecFinset W T) hceil with ⟨I, hI, hcard⟩
  refine ⟨I, hI, hcard, ?_⟩
  intro m hm
  exact (mem_ndecFinset W T m).1 (hI hm)

/-- From the descendant-nondecay count (a walk has at least `n·ηdec`
non-decaying levels) and `η ≤ ηdec` one can pick the level subset `I`.  This is
the version of `exists_levels_nondecay` expressed via the walk's own `ℓ −
decayUpTo` bound (matching `descendant_nondecay`'s conclusion). -/
lemma exists_levels_of_decayUpTo {ℓ n : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin ℓ → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top) (T : ℝ) {ηdec η : ℝ}
    (hcnt : (n : ℝ) * ηdec ≤ (ℓ : ℝ) - (decayUpTo W T ℓ (Nat.le_refl ℓ) : ℝ))
    (hηle : η ≤ ηdec) :
    ∃ I : Finset (Fin ℓ), I ⊆ ndecFinset W T ∧
      I.card = Nat.ceil (η * (n : ℝ)) ∧
      ∀ m ∈ I, ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := by
  have hle : decayUpTo W T ℓ (Nat.le_refl ℓ) ≤ ℓ := decayUpTo_le W T ℓ (Nat.le_refl ℓ)
  have hconv : (ndecFinset W T).card = ℓ - decayUpTo W T ℓ (Nat.le_refl ℓ) := ndecFinset_card (W := W) (T := T)
  have hcnt' : (n : ℝ) * ηdec ≤ (ndecFinset W T).card := by
    have hr : ((ndecFinset W T).card : ℝ) = (ℓ : ℝ) - (decayUpTo W T ℓ (Nat.le_refl ℓ) : ℝ) := by
      rw [hconv]
      exact Nat.cast_sub hle
    rwa [← hr] at hcnt
  exact exists_levels_nondecay (W := W) (T := T) (ηdec := ηdec) (η := η) hcnt' hηle

/-! ## 5. From the event to a descendant triple -/

/-- The decay threshold `T := εL / (2pN√n)` used throughout the proof of
Proposition `p: rough decay` (and by `descendant_nondecay`). -/
def roughT (ε L N n : ℝ) (p : ℝ) : ℝ :=
  (ε * L) / (2 * p * N * Real.sqrt n)

/-- If `‖avgF f p ℓ x‖∞` exceeds both thresholds, then there is a root `t₀`,
a pattern `v ∈ {0,1}^ℓ` and a set `I` of `⌈ηn⌉` levels such that all levels
`m ∈ I` do not decay along the prefix descendant sequence
`t_m := t₀ − Σ_{j<m} v_j·x_j`. -/
lemma event_descendant {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) {L : ℝ} (hL0 : 0 < L)
    {N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) (hfmass : norm₁ f ≤ 1)
    {x : Fin ℓ → ℤ}
    (hbig : ∃ t : ℤ, flvl f p x ℓ (Nat.le_refl ℓ) t >
      max (L / ((N : ℝ) * Real.sqrt (n : ℝ))) (((1 - (p : ℝ) + ε) ^ ℓ) * esup f))
    {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ ηdec p ε) :
    ∃ t₀ : ℤ, ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
      ∃ I : Finset (Fin ℓ),
        I.card = Nat.ceil (η * (n : ℝ)) ∧
        ∀ m ∈ I, ¬ decaysAt
            (flvl f p x m.val (Nat.le_trans (Nat.le_succ m.val) (Nat.succ_le_of_lt m.isLt)))
            (x ⟨m.val, Nat.lt_of_succ_le (Nat.succ_le_of_lt m.isLt)⟩)
            (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
            (descPoint x v t₀ m.val (Nat.le_trans (Nat.le_succ m.val) (Nat.succ_le_of_lt m.isLt))) := by
  classical
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  rcases descendant_nondecay (p := p) hp₀ hp₁ (ε := ε) hε0 hεp (L := L) hL0
      (N := N) hN1 (n := n) hn1 (ℓ := ℓ) hℓge hℓle (f := f) hfpos hfsum hfmass (x := x)
      (by exact hbig) with ⟨t_top, W, hcnt⟩
  have hcnt' : (n : ℝ) * ηdec p ε ≤ (ℓ : ℝ) - (decayUpTo W T ℓ (Nat.le_refl ℓ) : ℝ) := by
    -- hcnt has T unfolded; match definitionally
    simpa [T, roughT] using hcnt
  rcases exists_levels_of_decayUpTo (W := W) (T := T) (ηdec := ηdec p ε) (η := η) hcnt' hηle with
    ⟨I, hIsub, hIcard, hIdec⟩
  let t₀ : ℤ := W.t 0 (Nat.zero_le ℓ)
  let v : Fin ℓ → ℤ := walkV W
  refine ⟨t₀, v, ?_, I, hIcard, ?_⟩
  · intro j
    exact walkV_mem (W := W) j
  · intro m hm
    -- m ∈ I ⟹ ¬ levelDecays at level m.val
    have hnd : ¬ levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := hIdec m hm
    have heq : decaysAt
        (flvl f p x m.val (Nat.le_trans (Nat.le_succ m.val) (Nat.succ_le_of_lt m.isLt)))
        (x ⟨m.val, Nat.lt_of_succ_le (Nat.succ_le_of_lt m.isLt)⟩) T
        (descPoint x (walkV W) (W.t 0 (Nat.zero_le ℓ)) m.val
          (Nat.le_trans (Nat.le_succ m.val) (Nat.succ_le_of_lt m.isLt))) ↔
        levelDecays W T m.val (Nat.succ_le_of_lt m.isLt) := by
      exact (levelDecays_eq_descPoint (W := W) (T := T) (m := m.val) (Nat.succ_le_of_lt m.isLt)).symm
    intro hbad
    exact hnd (heq.1 hbad)


/-! ## 6. Scale-free per-level count bounds -/

/-- Scale-free version of `RoughDecay.step_nondecay_count_le`: with the decay
threshold `T := εL/(2pN√n)`, the number of `t ∈ Icc c d` at which the fixed
point `u` does not decay is at most the interval length times
`2p·Cq/(εL·√(δ₀p))` (independent of `n`, `N`). -/
theorem perStep_count_le_scaleFree : ∃ Cq : ℝ, 0 < Cq ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
          ∀ (c d u : ℤ) (hlen : (N : ℤ) ≤ (d : ℤ) - c + 1) {ε L : ℝ}
            (hε0 : 0 < ε) (hL0 : 0 < L),
            (((Finset.Icc c d).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
              (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
              ((d : ℝ) - (c : ℝ) + 1) *
                ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
  rcases RoughDecay.step_nondecay_count_le with ⟨Cq, hCqpos, hCq⟩
  refine ⟨Cq, hCqpos, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 m f hfpos hfsum hfmass z S hScard hSbig c d u hlen ε L hε0 hL0
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  have hT : 0 < T := by
    dsimp [T, roughT]
    positivity
  have hmain := hCq hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig c d u hlen (T := T) hT
  have hsqrt : Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) =
      Real.sqrt (n : ℝ) * Real.sqrt (δ₀ * (p : ℝ)) := by
    rw [show δ₀ * (n : ℝ) * (p : ℝ) = (n : ℝ) * (δ₀ * (p : ℝ)) by ring]
    exact Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ)) (δ₀ * (p : ℝ))
  have hNnz : (N : ℝ) ≠ 0 := by positivity
  have hεnz : ε ≠ 0 := ne_of_gt hε0
  have hLnz : L ≠ 0 := ne_of_gt hL0
  have hpnz : (p : ℝ) ≠ 0 := ne_of_gt hp₀
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsqrtdp : Real.sqrt (δ₀ * (p : ℝ)) ≠ 0 := by positivity
  calc
    (((Finset.Icc c d).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t T u)).card : ℝ)
        ≤ Cq * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
            (Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) * T) := by
          simpa [T] using hmain
    _ = ((d : ℝ) - (c : ℝ) + 1) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          dsimp [T, roughT]
          rw [hsqrt]
          field_simp [hNnz, hεnz, hLnz, hpnz, hsqrtn, hsqrtdp]

/-- Two-arm (union of two disjoint integer intervals, each of length ≥ N)
scale-free count bound: the number of points of the union at which the fixed
point `u` does not decay is at most the sum of the two interval lengths times
`2p·Cq/(εL·√(δ₀p))`. -/
theorem twoArm_count_le_scaleFree : ∃ Cq : ℝ, 0 < Cq ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
          ∀ (c₁ d₁ c₂ d₂ u : ℤ)
            (hlen₁ : (N : ℤ) ≤ (d₁ : ℤ) - c₁ + 1)
            (hlen₂ : (N : ℤ) ≤ (d₂ : ℤ) - c₂ + 1) {ε L : ℝ}
            (hε0 : 0 < ε) (hL0 : 0 < L),
            ((((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun t : ℤ =>
              ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
              (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
                ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
  rcases perStep_count_le_scaleFree with ⟨Cq, hCqpos, hCq⟩
  refine ⟨Cq, hCqpos, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 m f hfpos hfsum hfmass z S hScard hSbig
      c₁ d₁ c₂ d₂ u hlen₁ hlen₂ ε L hε0 hL0
  let q' : ℝ := (2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))
  have h1 := hCq hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig c₁ d₁ u hlen₁ hε0 hL0
  have h2 := hCq hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig c₂ d₂ u hlen₂ hε0 hL0
  -- filter over union is union of filters
  have hfilter : ((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun t : ℤ =>
        ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u) =
      (Finset.Icc c₁ d₁).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
          (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u) ∪
        (Finset.Icc c₂ d₂).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
          (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u) := by
    rw [Finset.filter_union]
  calc
    ((((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun t : ℤ =>
          ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ)
        ≤ ((((Finset.Icc c₁ d₁).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
              (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card +
            ((Finset.Icc c₂ d₂).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
              (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℕ) : ℝ) := by
          rw [hfilter]
          exact_mod_cast (Finset.card_union_le (s := (Finset.Icc c₁ d₁).filter (fun t : ℤ =>
            ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u))
            (t := (Finset.Icc c₂ d₂).filter (fun t : ℤ =>
            ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)))
    _ = ((((Finset.Icc c₁ d₁).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
            (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) +
          (((Finset.Icc c₂ d₂).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
            (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ)) := by
          norm_num
    _ ≤ (((d₁ : ℝ) - (c₁ : ℝ) + 1) * q' + ((d₂ : ℝ) - (c₂ : ℝ) + 1) * q') := by
          have h1' : ((((Finset.Icc c₁ d₁).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
              (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
              ((d₁ : ℝ) - (c₁ : ℝ) + 1) * q') := by
            dsimp [q']
            simpa using h1
          have h2' : ((((Finset.Icc c₂ d₂).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
              (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
              ((d₂ : ℝ) - (c₂ : ℝ) + 1) * q') := by
            dsimp [q']
            simpa using h2
          exact add_le_add h1' h2'
    _ = (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) * q' := by
          ring
    _ = (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          rfl


/-! ## 7. Prefix invariance of the level conditions (product-count recursion) -/

/-- Restricting the first `ℓ` coordinates of a length-`ℓ+1` tuple, the level-`m`
averaged function (`m ≤ ℓ`) is unchanged. -/
lemma flvl_eq_of_restrict {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (ℓ + 1) → ℤ}
    {m : ℕ} (hm : m ≤ ℓ) :
    flvl f p (Submission.ProdCount.restrict x) m hm =
      flvl f p x m (Nat.le_trans hm (Nat.le_succ ℓ)) := by
  have hpre : pre (Submission.ProdCount.restrict x) m hm =
      pre x m (Nat.le_trans hm (Nat.le_succ ℓ)) := by
    funext j
    dsimp [pre, Submission.ProdCount.restrict]
  funext t
  dsimp [flvl]
  rw [hpre]

/-- Restricting the first `ℓ` coordinates of a length-`ℓ+1` tuple, the level-`m`
descendant point (`m ≤ ℓ`) is unchanged. -/
lemma descPoint_eq_of_restrict {ℓ : ℕ} (x v : Fin (ℓ + 1) → ℤ) (t₀ : ℤ)
    {m : ℕ} (hm : m ≤ ℓ) :
    descPoint (Submission.ProdCount.restrict x) (Submission.ProdCount.restrict v) t₀ m hm =
      descPoint x v t₀ m (Nat.le_trans hm (Nat.le_succ ℓ)) := by
  dsimp [descPoint]
  have hsum : (∑ j : Fin m,
        (Submission.ProdCount.restrict v) (Fin.castLE hm j) * (Submission.ProdCount.restrict x) (Fin.castLE hm j)) =
      (∑ j : Fin m,
        v (Fin.castLE (Nat.le_trans hm (Nat.le_succ ℓ)) j) * x (Fin.castLE (Nat.le_trans hm (Nat.le_succ ℓ)) j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hv : (Submission.ProdCount.restrict v) (Fin.castLE hm j) =
        v (Fin.castLE (Nat.le_trans hm (Nat.le_succ ℓ)) j) := by
      dsimp [Submission.ProdCount.restrict]
    have hx : (Submission.ProdCount.restrict x) (Fin.castLE hm j) =
        x (Fin.castLE (Nat.le_trans hm (Nat.le_succ ℓ)) j) := by
      dsimp [Submission.ProdCount.restrict]
    rw [hv, hx]
  rw [hsum]

/-- The level-`m` decay test on a length-`ℓ+1` tuple agrees with the test on
its restriction to the first `ℓ` coordinates (the test only involves
coordinates up to `m < ℓ`). -/
lemma cond_eq_of_restrict {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x v : Fin (ℓ + 1) → ℤ}
    {t₀ : ℤ} (T : ℝ) {m : ℕ} (hm : m < ℓ) :
    decaysAt (flvl f p (Submission.ProdCount.restrict x) m (Nat.le_of_lt hm))
        ((Submission.ProdCount.restrict x) ⟨m, hm⟩) T
        (descPoint (Submission.ProdCount.restrict x) (Submission.ProdCount.restrict v) t₀ m (Nat.le_of_lt hm)) ↔
      decaysAt (flvl f p x m (Nat.le_trans (Nat.le_of_lt hm) (Nat.le_succ ℓ)))
        (x ⟨m, Nat.lt_trans hm (Nat.lt_succ_self ℓ)⟩) T
        (descPoint x v t₀ m (Nat.le_trans (Nat.le_of_lt hm) (Nat.le_succ ℓ))) := by
  have hF : flvl f p (Submission.ProdCount.restrict x) m (Nat.le_of_lt hm) =
      flvl f p x m (Nat.le_trans (Nat.le_of_lt hm) (Nat.le_succ ℓ)) :=
    flvl_eq_of_restrict (hm := Nat.le_of_lt hm)
  have hd : descPoint (Submission.ProdCount.restrict x) (Submission.ProdCount.restrict v) t₀ m (Nat.le_of_lt hm) =
      descPoint x v t₀ m (Nat.le_trans (Nat.le_of_lt hm) (Nat.le_succ ℓ)) :=
    descPoint_eq_of_restrict x v t₀ (Nat.le_of_lt hm)
  have hcoord : (Submission.ProdCount.restrict x) ⟨m, hm⟩ =
      x ⟨m, Nat.lt_trans hm (Nat.lt_succ_self ℓ)⟩ := by
    dsimp [Submission.ProdCount.restrict]
  unfold decaysAt
  constructor <;> intro h
  · rcases h with ⟨h1, h2⟩
    constructor
    · rw [← hF, ← hcoord, ← hd]
      exact h1
    · rw [← hF, ← hcoord, ← hd]
      exact h2
  · rcases h with ⟨h1, h2⟩
    constructor
    · rw [hF, hcoord, hd]
      exact h1
    · rw [hF, hcoord, hd]
      exact h2


/-! ## 8. The level condition as a function of the tuple length -/

/-- The non-decay condition at level `m < K` for a tuple of length `K`:
the level-`m` averaged function does not decay at the descendant point. -/
def levelCond {K : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ)
    (x : Fin K → ℤ) (v : Fin K → ℤ) (t₀ : ℤ) (m : ℕ) (hm : m < K) : Prop :=
  ¬ decaysAt (flvl f p x m (Nat.le_of_lt hm)) (x ⟨m, hm⟩) T
      (descPoint x v t₀ m (Nat.le_of_lt hm))

/-- The level-`m < ℓ` condition on a length-`ℓ+1` tuple equals the condition
on its `ℓ`-prefix. -/
lemma levelCond_eq_of_restrict {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval}
    {x v : Fin (ℓ + 1) → ℤ} {t₀ : ℤ} (T : ℝ) {m : ℕ} (hm : m < ℓ) :
    levelCond f p T (Submission.ProdCount.restrict x) (Submission.ProdCount.restrict v) t₀ m hm ↔
      levelCond f p T x v t₀ m (Nat.lt_trans hm (Nat.lt_succ_self ℓ)) := by
  change ¬ decaysAt (flvl f p (Submission.ProdCount.restrict x) m (Nat.le_of_lt hm))
        ((Submission.ProdCount.restrict x) ⟨m, hm⟩) T
        (descPoint (Submission.ProdCount.restrict x) (Submission.ProdCount.restrict v) t₀ m (Nat.le_of_lt hm)) ↔
      ¬ decaysAt (flvl f p x m (Nat.le_of_lt (Nat.lt_trans hm (Nat.lt_succ_self ℓ))))
        (x ⟨m, Nat.lt_trans hm (Nat.lt_succ_self ℓ)⟩) T
        (descPoint x v t₀ m (Nat.le_of_lt (Nat.lt_trans hm (Nat.lt_succ_self ℓ))))
  apply not_iff_not.mpr
  have hc := cond_eq_of_restrict (f := f) (p := p) (x := x) (v := v) (t₀ := t₀) (T := T) (hm := hm)
  simpa using hc


/-! ## 9. Shared-constant forms of the per-step bounds -/

/-- The scale-free per-step bound with an explicit constant `Cq`: for every
single-interval input the non-decay count is at most
`len · 2p·Cq/(εL√(δ₀p))`.  This is the content of
`perStep_count_le_scaleFree` with the `∃Cq`-quantifier moved out (so that one
`Cq` can be shared across all levels and all triples). -/
def perStepProp (Cq : ℝ) : Prop :=
  ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
    (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
    ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
      ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
        (hfmass : norm₁ f ≤ 1),
      ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
        (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
        (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
        ∀ (c d u : ℤ) (hlen : (N : ℤ) ≤ (d : ℤ) - c + 1) {ε L : ℝ}
          (hε0 : 0 < ε) (hL0 : 0 < L),
          (((Finset.Icc c d).filter (fun t : ℤ => ¬ decaysAt (avgF f p m z) t
            (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
            ((d : ℝ) - (c : ℝ) + 1) *
              ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))

/-- The scale-free two-arm per-step bound with an explicit constant `Cq`. -/
def twoArmProp (Cq : ℝ) : Prop :=
  ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
    (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
    ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
      ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
        (hfmass : norm₁ f ≤ 1),
      ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
        (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
        (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
        ∀ (c₁ d₁ c₂ d₂ u : ℤ)
          (hlen₁ : (N : ℤ) ≤ (d₁ : ℤ) - c₁ + 1)
          (hlen₂ : (N : ℤ) ≤ (d₂ : ℤ) - c₂ + 1) {ε L : ℝ}
          (hε0 : 0 < ε) (hL0 : 0 < L),
          ((((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun t : ℤ =>
            ¬ decaysAt (avgF f p m z) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) u)).card : ℝ) ≤
            (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
              ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))

/-- The single-interval scale-free bound in shared-constant form. -/
theorem exists_perStepProp : ∃ Cq : ℝ, 0 < Cq ∧ perStepProp Cq := by
  rcases perStep_count_le_scaleFree with ⟨Cq, hCqpos, hCq⟩
  exact ⟨Cq, hCqpos, by unfold perStepProp; exact hCq⟩

/-- The two-arm scale-free bound in shared-constant form. -/
theorem exists_twoArmProp : ∃ Cq : ℝ, 0 < Cq ∧ twoArmProp Cq := by
  rcases twoArm_count_le_scaleFree with ⟨Cq, hCqpos, hCq⟩
  exact ⟨Cq, hCqpos, by unfold twoArmProp; exact hCq⟩

end Submission.RoughDecay2
