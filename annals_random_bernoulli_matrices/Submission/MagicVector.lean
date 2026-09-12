import Mathlib
import Submission.Sec3Core
import Submission.SlabBridge
import Submission.Commons.Analysis.Real.abs_sub_le_two_mul_split
import Submission.Commons.Algebra.BigOperators.three_sets_intersection_nonempty

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Lemma l: magic vector (Tikhomirov 2020, "Proof of Theorem A")

The randomized-rounding lemma: if the small-ball probabilities of the random
Bernoulli(`p`) sum `Σᵢ bᵢyᵢ` are bounded by `L·t` for all `t ≥ √n`, then one
can find an integer vector `y'` (a "rounded" version of `y`) with

* `‖y − y'‖∞ ≤ 1` (so rounding does not move too much),
* the same linear small-ball bound (with a universal constant),
* concentration at `√n` preserved up to a universal factor,
* `|Σᵢ yᵢ − Σᵢ y'ᵢ| ≤ C·√n`.

The rounding variables are `ξᵢ := ⌊yᵢ⌋ + εᵢ` with `εᵢ ∈ {0,1}` independent,
`P(εᵢ = 1) = {yᵢ} := yᵢ − ⌊yᵢ⌋` (the fractional part), so `E ξᵢ = yᵢ` and
`Var ξᵢ = θᵢ(1−θᵢ) ≤ 1/4`.  All probability/expectation arguments are finite
sums over the `2ⁿ` rounding patterns (the "weight-sum route"): the Bernoulli
mass of a subset-family is `Σ_B wB(n,p,B)` and the rounding mass of a pattern
family is `Σ_E wR(y,E)` where `wR(y,E) := ∏ᵢ (θᵢ if i∈E else 1−θᵢ)`.
-/

open scoped BigOperators ENNReal
open Submission.Sec3
open Submission.Threshold
open Submission.ThresholdMeas
open Submission.SlabBridge
attribute [local instance] Classical.propDecidable

namespace Submission.MagicVector

/-- fractional part of a real (in `[0,1)`). -/
def th (y : ℝ) : ℝ := Int.fract y

/-- complement `1 − θᵢ ∈ (0,1]`. -/
def sig (y : ℝ) : ℝ := 1 - Int.fract y

lemma th_nonneg (y : ℝ) : 0 ≤ th y := by
  dsimp [th]
  exact Int.fract_nonneg y

lemma th_lt_one (y : ℝ) : th y < 1 := by
  dsimp [th]
  exact Int.fract_lt_one y

lemma sig_pos (y : ℝ) : 0 < sig y := by
  dsimp [sig]
  linarith [Int.fract_lt_one y]

lemma sig_nonneg (y : ℝ) : 0 ≤ sig y := le_of_lt (sig_pos y)

lemma th_add_sig (y : ℝ) : th y + sig y = 1 := by
  dsimp [sig, th]
  ring

/-- rounding-pattern weight: product over coordinates. -/
def wR {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) : ℝ :=
  ∏ i : Fin n, (if i ∈ E then th (y i) else sig (y i))

/-- rounded integer vector determined by the rounding pattern `E`. -/
def roundY {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) : Fin n → ℤ :=
  fun i => Int.floor (y i) + if i ∈ E then 1 else 0

/-- the rounding pattern's real value at coordinate `i`. -/
def roundYr {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) (i : Fin n) : ℝ :=
  ((roundY y E i : ℤ) : ℝ)

/-- real subset-sum over a subset `B`. -/
def rSub {n : ℕ} (y : Fin n → ℝ) (B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ B, y i

/-- generic powerset-sum of a coordinate-factorized product. -/
lemma sum_powerset_prod_ite {α : Type*} [DecidableEq α] (s : Finset α)
    (fa fb : α → ℝ) :
    (∑ t ∈ s.powerset, ∏ i ∈ s, (if i ∈ t then fa i else fb i)) =
      ∏ i ∈ s, (fa i + fb i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x s' hxs ih
    have hfac1 : ∀ t : Finset α, t ∈ s'.powerset →
        (∏ i ∈ insert x s', (if i ∈ t then fa i else fb i)) =
          fb x * (∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by
      intro t ht
      have hnot : x ∉ t := by
        intro hmem
        have hsub : t ⊆ s' := (Finset.mem_powerset.mp ht)
        exact hxs (hsub hmem)
      calc
        (∏ i ∈ insert x s', (if i ∈ t then fa i else fb i))
            = (if x ∈ t then fa x else fb x) * (∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by
                rw [Finset.prod_insert hxs]
        _ = fb x * (∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by simp [hnot]
    have hfac2 : ∀ t : Finset α, t ∈ s'.powerset →
        (∏ i ∈ insert x s', (if i ∈ insert x t then fa i else fb i)) =
          fa x * (∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by
      intro t ht
      calc
        (∏ i ∈ insert x s', (if i ∈ insert x t then fa i else fb i))
            = (if x ∈ insert x t then fa x else fb x) * (∏ i ∈ s', (if i ∈ insert x t then fa i else fb i)) := by
                rw [Finset.prod_insert hxs]
        _ = fa x * (∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by
                have hfac0 : (if x ∈ insert x t then fa x else fb x) = fa x := by simp
                rw [hfac0]
                apply congrArg (fun c : ℝ => fa x * c)
                apply Finset.prod_congr rfl
                intro i hi
                have hix : i ≠ x := by
                  intro h
                  exact hxs (by simpa [h] using hi)
                by_cases ht0 : i ∈ t
                · simp [Finset.mem_insert, ht0, hix]
                · simp [Finset.mem_insert, ht0, hix]
    calc
      (∑ t ∈ (insert x s').powerset, ∏ i ∈ insert x s', (if i ∈ t then fa i else fb i))
          = (∑ t ∈ s'.powerset, ∏ i ∈ insert x s', (if i ∈ t then fa i else fb i)) +
              (∑ t ∈ s'.powerset, ∏ i ∈ insert x s', (if i ∈ insert x t then fa i else fb i)) := by
                rw [Finset.sum_powerset_insert hxs]
      _ = (∑ t ∈ s'.powerset, fb x * (∏ i ∈ s', (if i ∈ t then fa i else fb i))) +
              (∑ t ∈ s'.powerset, fa x * (∏ i ∈ s', (if i ∈ t then fa i else fb i))) := by
                congr 1 <;> apply Finset.sum_congr rfl <;> intro t ht
                · exact hfac1 t ht
                · exact hfac2 t ht
      _ = fb x * (∑ t ∈ s'.powerset, ∏ i ∈ s', (if i ∈ t then fa i else fb i)) +
              fa x * (∑ t ∈ s'.powerset, ∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by
                rw [Finset.mul_sum, Finset.mul_sum]
      _ = (fa x + fb x) * (∑ t ∈ s'.powerset, ∏ i ∈ s', (if i ∈ t then fa i else fb i)) := by ring
      _ = (fa x + fb x) * (∏ i ∈ s', (fa i + fb i)) := by rw [ih]
      _ = ∏ i ∈ insert x s', (fa i + fb i) := by
                rw [Finset.prod_insert hxs]

/-- the rounding weights are non-negative. -/
lemma wR_nonneg {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) : 0 ≤ wR y E := by
  dsimp [wR]
  apply Finset.prod_nonneg
  intro i hi
  by_cases hE : i ∈ E
  · simp [hE, th_nonneg]
  · simp [hE, sig_nonneg]

/-- the rounding weights sum to one. -/
lemma sum_wR_eq_one {n : ℕ} (y : Fin n → ℝ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) = 1 := by
  classical
  have h := sum_powerset_prod_ite (s := (Finset.univ : Finset (Fin n)))
    (fa := fun i : Fin n => th (y i)) (fb := fun i : Fin n => sig (y i))
  have hw : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) =
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i : Fin n, (if i ∈ E then th (y i) else sig (y i)) := by
    apply Finset.sum_congr rfl
    intro E hE
    rfl
  rw [hw, h]
  calc
    (∏ i : Fin n, (th (y i) + sig (y i))) = ∏ i : Fin n, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact th_add_sig (y i)
    _ = 1 := by
      rw [Finset.prod_const]
      simp


/-- powerset-sum restricted to subsets containing `a`: the factor `fa a` splits
off, and the coordinates of `s.erase a` close to `fa i + fb i`. -/
lemma sum_powerset_prod_ite_mem {α : Type*} [DecidableEq α] (s : Finset α)
    (fa fb : α → ℝ) {a : α} (has : a ∈ s) :
    (∑ t ∈ (s.powerset.filter (fun t => a ∈ t)),
        ∏ i ∈ s, (if i ∈ t then fa i else fb i)) =
      fa a * ∏ i ∈ s.erase a, (fa i + fb i) := by
  classical
  let s' : Finset α := s.erase a
  have hsplit : s = insert a s' := by
    dsimp [s']
    rw [Finset.insert_erase has]
  have hEq : s.powerset.filter (fun t => a ∈ t) =
      Finset.image (fun t : Finset α => insert a t) s'.powerset := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨htpow, hmem⟩
      rw [Finset.mem_image]
      refine ⟨t.erase a, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_erase] at hx
        have hts : t ⊆ s := (Finset.mem_powerset.mp htpow)
        rw [Finset.mem_erase]
        exact ⟨hx.1, hts hx.2⟩
      · rw [Finset.insert_erase hmem]
    · intro t ht
      rw [Finset.mem_image] at ht
      rcases ht with ⟨t₀, ht₀, ht0eq⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro x hx
        rw [← ht0eq] at hx
        rcases (Finset.mem_insert.mp hx) with hxa | hxt
        · simp [hxa, has]
        · have hx2 : x ∈ s.erase a := (Finset.mem_powerset.mp ht₀) hxt
          rw [Finset.mem_erase] at hx2
          exact hx2.2
      · rw [← ht0eq]
        simp
  have hInjOn : Set.InjOn (fun t : Finset α => insert a t) (↑s'.powerset) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have ht₁p : t₁ ⊆ s' := (Finset.mem_powerset.mp (by simpa using ht₁))
    have ht₂p : t₂ ⊆ s' := (Finset.mem_powerset.mp (by simpa using ht₂))
    have heq' : insert a t₁ = insert a t₂ := by simpa using heq
    apply Finset.ext
    intro x
    constructor
    · intro hx₁
      have hne : x ≠ a := (Finset.mem_erase.mp (ht₁p hx₁)).1
      have hx : x ∈ insert a t₂ := by
        rw [← heq']
        exact Finset.mem_insert.mpr (Or.inr hx₁)
      rcases (Finset.mem_insert.mp hx) with hxa | hx₂
      · exact False.elim (hne hxa)
      · exact hx₂
    · intro hx₂
      have hne : x ≠ a := (Finset.mem_erase.mp (ht₂p hx₂)).1
      have hx : x ∈ insert a t₁ := by
        rw [heq']
        exact Finset.mem_insert.mpr (Or.inr hx₂)
      rcases (Finset.mem_insert.mp hx) with hxa | hx₁
      · exact False.elim (hne hxa)
      · exact hx₁
  rw [hEq, Finset.sum_image hInjOn]
  have hinner : ∀ t₀ : Finset α, t₀ ∈ s'.powerset →
      (∏ i ∈ s, (if i ∈ insert a t₀ then fa i else fb i)) =
        fa a * (∏ i ∈ s', (if i ∈ t₀ then fa i else fb i)) := by
    intro t₀ ht₀
    have hnot : a ∉ s' := by dsimp [s']; simp
    calc
      (∏ i ∈ s, (if i ∈ insert a t₀ then fa i else fb i))
          = (∏ i ∈ insert a s', (if i ∈ insert a t₀ then fa i else fb i)) := by rw [hsplit]
      _ = (if a ∈ insert a t₀ then fa a else fb a) *
            (∏ i ∈ s', (if i ∈ insert a t₀ then fa i else fb i)) := by
            rw [Finset.prod_insert hnot]
      _ = fa a * (∏ i ∈ s', (if i ∈ t₀ then fa i else fb i)) := by
            have hfac0 : (if a ∈ insert a t₀ then fa a else fb a) = fa a := by simp
            rw [hfac0]
            apply congrArg (fun c : ℝ => fa a * c)
            apply Finset.prod_congr rfl
            intro i hi
            have hia : i ≠ a := by
              intro h
              have h1 : i ∈ s' := hi
              rw [h] at h1
              exact (Finset.mem_erase.mp h1).1 rfl
            by_cases ht0 : i ∈ t₀
            · simp [Finset.mem_insert, ht0, hia]
            · simp [Finset.mem_insert, ht0, hia]
  calc
    (∑ t₀ ∈ s'.powerset, ∏ i ∈ s, (if i ∈ insert a t₀ then fa i else fb i))
        = ∑ t₀ ∈ s'.powerset, fa a * (∏ i ∈ s', (if i ∈ t₀ then fa i else fb i)) := by
            apply Finset.sum_congr rfl
            intro t₀ ht₀
            exact hinner t₀ ht₀
    _ = fa a * (∑ t₀ ∈ s'.powerset, ∏ i ∈ s', (if i ∈ t₀ then fa i else fb i)) := by
            rw [Finset.mul_sum]
    _ = fa a * (∏ i ∈ s', (fa i + fb i)) := by
            rw [sum_powerset_prod_ite s' fa fb]
    _ = fa a * ∏ i ∈ s.erase a, (fa i + fb i) := by rfl


/-- rounding mass of the event `i ∈ E` equals the fractional part `θᵢ`. -/
lemma wR_mem_sum {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∈ E)), wR y E) =
      th (y i) := by
  classical
  have h := sum_powerset_prod_ite_mem (s := (Finset.univ : Finset (Fin n)))
    (fa := fun j : Fin n => th (y j)) (fb := fun j : Fin n => sig (y j))
    (a := i) (Finset.mem_univ i)
  have hw : (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∈ E)), wR y E) =
      ∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∈ E)),
        ∏ j : Fin n, (if j ∈ E then th (y j) else sig (y j)) := by
    apply Finset.sum_congr rfl
    intro E hE
    rfl
  rw [hw, h]
  calc
    th (y i) * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (th (y j) + sig (y j)))
        = th (y i) * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 : ℝ)) := by
            apply congrArg (fun c : ℝ => th (y i) * c)
            apply Finset.prod_congr rfl
            intro j hj
            exact th_add_sig (y j)
    _ = th (y i) := by
            rw [Finset.prod_const]
            simp

/-- rounding mass of the event `i ∉ E` equals `1 − θᵢ`. -/
lemma wR_notMem_sum {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∉ E)), wR y E) =
      sig (y i) := by
  classical
  have htotal : (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∈ E)), wR y E) +
      (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∉ E)), wR y E) =
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : i ∈ E
    · simp [h]
    · simp [h]
  calc
    (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∉ E)), wR y E)
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) -
            (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => i ∈ E)), wR y E) := by
            linarith
    _ = 1 - th (y i) := by
            rw [sum_wR_eq_one, wR_mem_sum]
    _ = sig (y i) := by
            dsimp [sig, th]


/-- substitution: summing over the subsets containing `a` equals summing over
subsets of `s.erase a` after inserting `a`. -/
lemma sum_powerset_filter_mem_image {α : Type*} [DecidableEq α] (s : Finset α)
    {a : α} (has : a ∈ s) (f : Finset α → ℝ) :
    (∑ t ∈ (s.powerset.filter (fun t : Finset α => a ∈ t)), f t) =
      ∑ t₀ ∈ (s.erase a).powerset, f (insert a t₀) := by
  classical
  have hEq : s.powerset.filter (fun t : Finset α => a ∈ t) =
      Finset.image (fun t₀ : Finset α => insert a t₀) (s.erase a).powerset := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨htpow, hmem⟩
      rw [Finset.mem_image]
      refine ⟨t.erase a, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_erase] at hx
        have hts : t ⊆ s := (Finset.mem_powerset.mp htpow)
        rw [Finset.mem_erase]
        exact ⟨hx.1, hts hx.2⟩
      · rw [Finset.insert_erase hmem]
    · intro t ht
      rw [Finset.mem_image] at ht
      rcases ht with ⟨t₀, ht₀, ht0eq⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro x hx
        rw [← ht0eq] at hx
        rcases (Finset.mem_insert.mp hx) with hxa | hxt
        · rw [hxa]
          exact has
        · have hx2 : x ∈ s.erase a := (Finset.mem_powerset.mp ht₀) hxt
          exact (Finset.mem_erase.mp hx2).2
      · rw [← ht0eq]
        simp
  have hInj : Set.InjOn (fun t₀ : Finset α => insert a t₀) (↑((s.erase a).powerset)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have ht₁p : t₁ ⊆ s.erase a := (Finset.mem_powerset.mp ht₁)
    have ht₂p : t₂ ⊆ s.erase a := (Finset.mem_powerset.mp ht₂)
    have heq' : insert a t₁ = insert a t₂ := by simpa using heq
    apply Finset.ext
    intro x
    constructor
    · intro hx₁
      have hne : x ≠ a := (Finset.mem_erase.mp (ht₁p hx₁)).1
      have hx : x ∈ insert a t₂ := by
        rw [← heq']
        exact Finset.mem_insert.mpr (Or.inr hx₁)
      rcases (Finset.mem_insert.mp hx) with hxa | hx₂
      · exact False.elim (hne hxa)
      · exact hx₂
    · intro hx₂
      have hne : x ≠ a := (Finset.mem_erase.mp (ht₂p hx₂)).1
      have hx : x ∈ insert a t₁ := by
        rw [heq']
        exact Finset.mem_insert.mpr (Or.inr hx₂)
      rcases (Finset.mem_insert.mp hx) with hxa | hx₁
      · exact False.elim (hne hxa)
      · exact hx₁
  rw [hEq, Finset.sum_image hInj]


/-- the rounding weight of `insert i T` factors as `θᵢ` times the product over
the coordinates other than `i`. -/
lemma wR_insert_factor {n : ℕ} (y : Fin n → ℝ) (i : Fin n) (T : Finset (Fin n)) :
    wR y (insert i T) =
      th (y i) * (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        (if l ∈ T then th (y l) else sig (y l))) := by
  classical
  have hErase : i ∉ (Finset.univ : Finset (Fin n)).erase i := by
    intro h
    rw [Finset.mem_erase] at h
    exact h.1 rfl
  let g : Fin n → ℝ := fun l => (if l ∈ insert i T then th (y l) else sig (y l))
  calc
    wR y (insert i T) = ∏ l : Fin n, g l := by
      dsimp [wR, g]
    _ = (∏ l ∈ insert i ((Finset.univ : Finset (Fin n)).erase i), g l) := by
            rw [Finset.insert_erase (Finset.mem_univ i)]
    _ = g i * (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, g l) := by
            rw [Finset.prod_insert hErase]
    _ = th (y i) * (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, g l) := by
            have hfac : g i = th (y i) := by
              dsimp [g]
              simp
            rw [hfac]
    _ = th (y i) * (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
          (if l ∈ T then th (y l) else sig (y l))) := by
            apply congrArg (fun c : ℝ => th (y i) * c)
            dsimp [g]
            apply Finset.prod_congr rfl
            intro l hl
            have hne : l ≠ i := (Finset.mem_erase.mp hl).1
            by_cases hT : l ∈ T
            · have : l ∈ insert i T := by
                rw [Finset.mem_insert]
                exact Or.inr hT
              simp [hT, this]
            · have hnot : l ∉ insert i T := by
                intro h
                rcases (Finset.mem_insert.mp h) with hli | hT'
                · exact hne hli
                · exact hT hT'
              simp [hT, hnot]


/-- rounding mass of the event `i ∈ E ∧ j ∈ E` equals `θᵢ·θⱼ` for `i ≠ j`. -/
lemma wR_mem2_sum {n : ℕ} (y : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun E => i ∈ E ∧ j ∈ E)), wR y E) = th (y i) * th (y j) := by
  classical
  have hErase : i ∉ (Finset.univ : Finset (Fin n)).erase i := by
    intro h
    rw [Finset.mem_erase] at h
    exact h.1 rfl
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  -- express the double-pinned sum as: substitute at i, then the leftover j∈T
  -- requirement reduces to a single-pinned sum over the erase.
  calc
    (∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun E => i ∈ E ∧ j ∈ E)), wR y E)
        = ∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
            (fun E => i ∈ E)), (if j ∈ E then wR y E else 0) := by
            -- filter over a conjunction = filter iterated; sum_filter toggles
            have hf1 : ((Finset.univ : Finset (Fin n)).powerset.filter
                  (fun E : Finset (Fin n) => i ∈ E ∧ j ∈ E)) =
                ((Finset.univ : Finset (Fin n)).powerset.filter
                  (fun E : Finset (Fin n) => i ∈ E)).filter
                  (fun E : Finset (Fin n) => j ∈ E) := by
              apply Finset.ext
              intro E
              simp [and_assoc, and_left_comm, and_comm]
            rw [hf1, Finset.sum_filter]
    _ = ∑ T ∈ ((Finset.univ : Finset (Fin n)).erase i).powerset,
          (if j ∈ insert i T then wR y (insert i T) else 0) := by
            rw [sum_powerset_filter_mem_image (s := (Finset.univ : Finset (Fin n)))
              (a := i) (Finset.mem_univ i)
              (f := fun E : Finset (Fin n) => if j ∈ E then wR y E else 0)]
    _ = ∑ T ∈ ((Finset.univ : Finset (Fin n)).erase i).powerset,
          (if j ∈ T then wR y (insert i T) else 0) := by
            apply Finset.sum_congr rfl
            intro T hT
            by_cases h : j ∈ T
            · have : j ∈ insert i T := by
                rw [Finset.mem_insert]
                exact Or.inr h
              simp [h, this]
            · have hnot : j ∉ insert i T := by
                intro hj
                rcases (Finset.mem_insert.mp hj) with hji' | hT'
                · exact hji hji'
                · exact h hT'
              simp [h, hnot]
    _ = ∑ T ∈ (((Finset.univ : Finset (Fin n)).erase i).powerset.filter
          (fun T => j ∈ T)), wR y (insert i T) := by
            rw [Finset.sum_filter]
    _ = ∑ T ∈ (((Finset.univ : Finset (Fin n)).erase i).powerset.filter
          (fun T => j ∈ T)), th (y i) *
            (∏ l ∈ ((Finset.univ : Finset (Fin n)).erase i),
              (if l ∈ T then th (y l) else sig (y l))) := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [wR_insert_factor]
    _ = th (y i) * (∑ T ∈ (((Finset.univ : Finset (Fin n)).erase i).powerset.filter
          (fun T => j ∈ T)),
            ∏ l ∈ ((Finset.univ : Finset (Fin n)).erase i),
              (if l ∈ T then th (y l) else sig (y l))) := by
            rw [Finset.mul_sum]
    _ = th (y i) * th (y j) := by
            -- the inner sum is the single-pinned product sum over s := univ.erase i
            have hmemj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
              rw [Finset.mem_erase]
              exact ⟨hji, Finset.mem_univ j⟩
            have hmem := sum_powerset_prod_ite_mem
              (s := (Finset.univ : Finset (Fin n)).erase i)
              (fa := fun l : Fin n => th (y l)) (fb := fun l : Fin n => sig (y l))
              (a := j) hmemj
            have hsum1 : (∑ T ∈ (((Finset.univ : Finset (Fin n)).erase i).powerset.filter
                  (fun T : Finset (Fin n) => j ∈ T)),
                    ∏ l ∈ ((Finset.univ : Finset (Fin n)).erase i),
                      (if l ∈ T then th (y l) else sig (y l))) = th (y j) := by
              rw [hmem]
              calc
                th (y j) * (∏ l ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j,
                    (th (y l) + sig (y l))) = th (y j) * (∏ l ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, (1 : ℝ)) := by
                        apply congrArg (fun c : ℝ => th (y j) * c)
                        apply Finset.prod_congr rfl
                        intro l hl
                        exact th_add_sig (y l)
                _ = th (y j) := by
                        rw [Finset.prod_const]
                        simp
            rw [hsum1]


/-- splitting: the `wR`-weighted sum of a two-valued (by membership of `i`)
expression equals `c·θᵢ + d·(1−θᵢ)`. -/
lemma wR_sum_ite_mem {n : ℕ} (y : Fin n → ℝ) (i : Fin n) (c d : ℝ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if i ∈ E then c else d)) =
      c * th (y i) + d * sig (y i) := by
  classical
  let A : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powerset.filter (fun E : Finset (Fin n) => i ∈ E))
  let B : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powerset.filter (fun E : Finset (Fin n) => i ∉ E))
  have hcov : (Finset.univ : Finset (Fin n)).powerset = A ∪ B := by
    apply Finset.ext
    intro E
    by_cases hE : i ∈ E <;> simp [A, B, hE]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro E hE1 hE2
    have h1 : i ∈ E := (Finset.mem_filter.mp hE1).2
    have h2 : i ∉ E := (Finset.mem_filter.mp hE2).2
    exact h2 h1
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (if i ∈ E then c else d))
        = (∑ E ∈ A, wR y E * (if i ∈ E then c else d)) +
          (∑ E ∈ B, wR y E * (if i ∈ E then c else d)) := by
            rw [hcov, Finset.sum_union hdisj]
    _ = (∑ E ∈ A, wR y E * c) + (∑ E ∈ B, wR y E * d) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro E hE
              have h1 : i ∈ E := (Finset.mem_filter.mp hE).2
              simp [h1]
            · apply Finset.sum_congr rfl
              intro E hE
              have h1 : i ∉ E := (Finset.mem_filter.mp hE).2
              simp [h1]
    _ = c * th (y i) + d * sig (y i) := by
            have h1 : (∑ E ∈ A, wR y E * c) = c * th (y i) := by
              dsimp [A]
              rw [← Finset.sum_mul]
              rw [wR_mem_sum]
              ring
            have h2 : (∑ E ∈ B, wR y E * d) = d * sig (y i) := by
              dsimp [B]
              rw [← Finset.sum_mul]
              rw [wR_notMem_sum]
              ring
            rw [h1, h2]

/-- diagonal second moment: `E[(θᵢ − εᵢ)²] = θᵢ(1−θᵢ)`. -/
lemma wR_diag_sq_sum {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (th (y i) - (if i ∈ E then 1 else 0)) ^ 2) = th (y i) * sig (y i) := by
  classical
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (th (y i) - (if i ∈ E then 1 else 0)) ^ 2)
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if i ∈ E then (1 - th (y i)) ^ 2 else (th (y i)) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro E hE
            congr 1
            by_cases h : i ∈ E
            · have hsq : (th (y i) - 1) ^ 2 = (1 - th (y i)) ^ 2 := by ring
              simpa [h] using hsq
            · simp [h]
    _ = (1 - th (y i)) ^ 2 * th (y i) + (th (y i)) ^ 2 * sig (y i) := by
            rw [wR_sum_ite_mem y i ((1 - th (y i)) ^ 2) ((th (y i)) ^ 2)]
    _ = th (y i) * sig (y i) := by
            have hsig : sig (y i) = 1 - th (y i) := by
              dsimp [sig, th]
            rw [hsig]
            ring_nf




/-- off-diagonal second moments vanish: for `i ≠ j`,
`E[(θᵢ − εᵢ)(θⱼ − εⱼ)] = 0`. -/
lemma wR_cross_sum {n : ℕ} (y : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * ((th (y i) - (if i ∈ E then 1 else 0)) *
          (th (y j) - (if j ∈ E then 1 else 0)))) = 0 := by
  classical
  let a : ℝ := th (y i)
  let b : ℝ := th (y j)
  have hpt : ∀ E : Finset (Fin n),
      ((th (y i) - (if i ∈ E then 1 else 0)) * (th (y j) - (if j ∈ E then 1 else 0))) =
        a * b - a * (if j ∈ E then 1 else 0) - b * (if i ∈ E then 1 else 0) +
          (if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0) := by
    intro E
    dsimp [a, b]
    ring
  have h1 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (a * b)) = a * b := by
    rw [← Finset.sum_mul]
    rw [sum_wR_eq_one]
    ring
  have h2 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * (a * (if j ∈ E then 1 else 0))) = a * b := by
    have hε : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if j ∈ E then 1 else 0)) = b := by
      rw [wR_sum_ite_mem y j 1 0]
      dsimp [b]
      ring
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (a * (if j ∈ E then 1 else 0)))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              (wR y E * (if j ∈ E then 1 else 0)) * a := by
              apply Finset.sum_congr rfl
              intro E hE
              ring
      _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if j ∈ E then 1 else 0)) * a := by
            rw [← Finset.sum_mul]
      _ = a * b := by
            rw [hε]
            ring
  have h3 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * (b * (if i ∈ E then 1 else 0))) = a * b := by
    have hε : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if i ∈ E then 1 else 0)) = a := by
      rw [wR_sum_ite_mem y i 1 0]
      dsimp [a]
      ring
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (b * (if i ∈ E then 1 else 0)))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              (wR y E * (if i ∈ E then 1 else 0)) * b := by
              apply Finset.sum_congr rfl
              intro E hE
              ring
      _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if i ∈ E then 1 else 0)) * b := by
            rw [← Finset.sum_mul]
      _ = a * b := by
            rw [hε]
  have h4 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * ((if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0))) = a * b := by
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * ((if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0)))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              (if (i ∈ E ∧ j ∈ E) then wR y E else 0) := by
              apply Finset.sum_congr rfl
              intro E hE
              by_cases h : i ∈ E ∧ j ∈ E
              · rcases h with ⟨hi, hj⟩
                simp [hi, hj]
              · by_cases hi : i ∈ E <;> by_cases hj : j ∈ E <;> simp [hi, hj, h]
      _ = ∑ E ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
            (fun E => i ∈ E ∧ j ∈ E)), wR y E := by
            rw [← Finset.sum_filter]
      _ = a * b := by
            have hmem := wR_mem2_sum (y := y) (i := i) (j := j) hij
            dsimp [a, b] at hmem ⊢
            exact hmem
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * ((th (y i) - (if i ∈ E then 1 else 0)) * (th (y j) - (if j ∈ E then 1 else 0))))
        = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (a * b - a * (if j ∈ E then 1 else 0) - b * (if i ∈ E then 1 else 0) +
              (if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro E hE
            rw [hpt E]
    _ = a * b - a * b - a * b + a * b := by
            have hlin : ∀ E : Finset (Fin n),
                wR y E * (a * b - a * (if j ∈ E then 1 else 0) - b * (if i ∈ E then 1 else 0) +
                  (if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0)) =
                  wR y E * (a * b) - wR y E * (a * (if j ∈ E then 1 else 0)) -
                    wR y E * (b * (if i ∈ E then 1 else 0)) +
                      wR y E * ((if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0)) := by
              intro E
              ring
            calc
              (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                  wR y E * (a * b - a * (if j ∈ E then 1 else 0) - b * (if i ∈ E then 1 else 0) +
                    (if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0)))
                  = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      (wR y E * (a * b) - wR y E * (a * (if j ∈ E then 1 else 0)) -
                        wR y E * (b * (if i ∈ E then 1 else 0)) +
                          wR y E * ((if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0))) := by
                      apply Finset.sum_congr rfl
                      intro E hE
                      exact hlin E
              _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (a * b)) -
                  (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    wR y E * (a * (if j ∈ E then 1 else 0))) -
                  (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    wR y E * (b * (if i ∈ E then 1 else 0))) +
                  (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    wR y E * ((if i ∈ E then 1 else 0) * (if j ∈ E then 1 else 0))) := by
                      rw [Finset.sum_add_distrib]
                      rw [Finset.sum_sub_distrib]
                      rw [Finset.sum_sub_distrib]
              _ = a * b - a * b - a * b + a * b := by
                      rw [h1, h2, h3, h4]
    _ = 0 := by ring


/-- the full rounding variance identity:
`E_ξ[(Σ_{i∈B}(θᵢ − εᵢ))²] = Σ_{i∈B} θᵢ·(1−θᵢ)`. -/
lemma round_sq_sum_eq {n : ℕ} (y : Fin n → ℝ) (B : Finset (Fin n)) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ i ∈ B, (th (y i) - (if i ∈ E then 1 else 0))) ^ 2) =
      ∑ i ∈ B, th (y i) * sig (y i) := by
  classical
  let d : Fin n → Finset (Fin n) → ℝ := fun i E => th (y i) - (if i ∈ E then 1 else 0)
  have hsq : ∀ E : Finset (Fin n),
      (∑ i ∈ B, d i E) ^ 2 = ∑ i ∈ B, ∑ j ∈ B, (d i E) * (d j E) := by
    intro E
    rw [pow_two]
    exact Finset.sum_mul_sum B B (fun i => d i E) (fun j => d j E)
  have hsw : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ i ∈ B, d i E) ^ 2) =
      ∑ p ∈ B ×ˢ B, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (d p.1 E * d p.2 E) := by
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (∑ i ∈ B, d i E) ^ 2)
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              wR y E * (∑ i ∈ B, ∑ j ∈ B, (d i E) * (d j E)) := by
              apply Finset.sum_congr rfl
              intro E hE
              rw [hsq E]
      _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            (∑ i ∈ B, ∑ j ∈ B, wR y E * ((d i E) * (d j E))) := by
            apply Finset.sum_congr rfl
            intro E hE
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            ∑ p ∈ B ×ˢ B, wR y E * (d p.1 E * d p.2 E) := by
            apply Finset.sum_congr rfl
            intro E hE
            rw [← Finset.sum_product B B (fun p : Fin n × Fin n => wR y E * (d p.1 E * d p.2 E))]
      _ = ∑ p ∈ B ×ˢ B, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (d p.1 E * d p.2 E) := by
            rw [Finset.sum_comm]
  let f : Fin n × Fin n → ℝ := fun p =>
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (d p.1 E * d p.2 E)
  have hcov : B ×ˢ B = B.diag ∪ B.offDiag := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      rw [Finset.mem_product] at hp
      rcases hp with ⟨hp1, hp2⟩
      rw [Finset.mem_union]
      by_cases heq : p.1 = p.2
      · left
        rw [Finset.mem_diag]
        exact ⟨hp1, heq⟩
      · right
        rw [Finset.mem_offDiag]
        exact ⟨hp1, hp2, heq⟩
    · intro hp
      rw [Finset.mem_union] at hp
      rcases hp with hp1 | hp2
      · rw [Finset.mem_diag] at hp1
        rw [Finset.mem_product]
        exact ⟨hp1.1, by rw [← hp1.2]; exact hp1.1⟩
      · rw [Finset.mem_offDiag] at hp2
        rw [Finset.mem_product]
        exact ⟨hp2.1, hp2.2.1⟩
  have hdiag : ∀ p : Fin n × Fin n, p ∈ B.diag → f p = th (y p.1) * sig (y p.1) := by
    intro p hp
    rw [Finset.mem_diag] at hp
    rcases hp with ⟨hi, heq⟩
    dsimp [f]
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (d p.1 E * d p.2 E))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (d p.1 E * d p.1 E) := by
            rw [heq]
      _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (d p.1 E) ^ 2 := by
            apply Finset.sum_congr rfl
            intro E hE
            ring
      _ = th (y p.1) * sig (y p.1) := by
            dsimp [d]
            exact wR_diag_sq_sum y p.1
  have hdiag2 : (∑ p ∈ B.diag, f p) = ∑ i ∈ B, th (y i) * sig (y i) := by
    have himg : B.diag = Finset.image (fun i : Fin n => (i, i)) B := by
      apply Finset.ext
      intro p
      rw [Finset.mem_diag]
      rw [Finset.mem_image]
      constructor
      · intro hp
        rcases hp with ⟨hi, heq⟩
        refine ⟨p.1, hi, ?_⟩
        apply Prod.ext <;> simp [heq]
      · intro hp
        rcases hp with ⟨i, hi, rfl⟩
        exact ⟨hi, rfl⟩
    have hinj : Set.InjOn (fun i : Fin n => (i, i)) (↑B) := by
      intro i hi j hj h
      exact congrArg Prod.fst h
    rw [himg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    exact hdiag (i, i) (by rw [Finset.mem_diag]; exact ⟨hi, rfl⟩)
  have hoff : (∑ p ∈ B.offDiag, f p) = 0 := by
    have hval : ∀ p : Fin n × Fin n, p ∈ B.offDiag → f p = 0 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      rcases hp with ⟨h1, h2, hne⟩
      dsimp [f, d]
      exact wR_cross_sum (y := y) (i := p.1) (j := p.2) hne
    calc
      (∑ p ∈ B.offDiag, f p) = ∑ p ∈ B.offDiag, (0 : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hval p hp
      _ = 0 := by
            rw [Finset.sum_const]
            simp
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ i ∈ B, (th (y i) - (if i ∈ E then 1 else 0))) ^ 2)
        = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (∑ i ∈ B, d i E) ^ 2 := by
            rfl
    _ = ∑ p ∈ B ×ˢ B, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (d p.1 E * d p.2 E) := hsw
    _ = (∑ p ∈ B.diag, f p) + (∑ p ∈ B.offDiag, f p) := by
            rw [hcov]
            rw [Finset.sum_union (Finset.disjoint_diag_offDiag B)]
    _ = ∑ i ∈ B, th (y i) * sig (y i) := by
            rw [hdiag2, hoff]
            ring


/-- `θ·(1−θ) ≤ 1/4` for the fractional part `θ ∈ [0,1)`. -/
lemma th_sig_le_quarter (y : ℝ) : th y * sig y ≤ 1 / 4 := by
  dsimp [th, sig]
  nlinarith [sq_nonneg (Int.fract y - (1 : ℝ) / 2)]

/-- the rounding variance is at most `n/4`. -/
lemma round_sq_sum_le_n {n : ℕ} (y : Fin n → ℝ) (B : Finset (Fin n)) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ i ∈ B, (th (y i) - (if i ∈ E then 1 else 0))) ^ 2) ≤ (n : ℝ) / 4 := by
  classical
  rw [round_sq_sum_eq]
  calc
    (∑ i ∈ B, th (y i) * sig (y i)) ≤ ∑ i ∈ B, (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact th_sig_le_quarter (y i)
    _ = (B.card : ℝ) / 4 := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      field_simp
    _ ≤ (n : ℝ) / 4 := by
      have hc : B.card ≤ n := by
        have hsub : B ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ B
        have h1 := Finset.card_le_card hsub
        simpa using h1
      have hcR : (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
      exact div_le_div_of_nonneg_right hcR (by norm_num : (0 : ℝ) ≤ 4)

/-- **Chebyshev**: the rounding mass of `{|Σ_{i∈B}(yᵢ − ξᵢ)| > w}` is at most
`n/(4w²)`. -/
lemma rounding_tail_le {n : ℕ} (y : Fin n → ℝ) (B : Finset (Fin n)) {w : ℝ} (hw : 0 < w) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if w < |∑ i ∈ B, (y i - roundYr y E i)| then 1 else 0)) ≤
      (n : ℝ) / (4 * w ^ 2) := by
  classical
  have hw2pos : 0 < w ^ 2 := by positivity
  let Z : Finset (Fin n) → ℝ := fun E => ∑ i ∈ B, (y i - roundYr y E i)
  have hid : ∀ i : Fin n, ∀ E : Finset (Fin n),
      (y i - roundYr y E i) = th (y i) - (if i ∈ E then 1 else 0) := by
    intro i E
    have hcast : roundYr y E i = (Int.floor (y i) : ℝ) + (if i ∈ E then 1 else 0) := by
      dsimp [roundYr, roundY]
      rw [Int.cast_add]
      by_cases hE : i ∈ E <;> simp [hE]
    have hfract : y i - (Int.floor (y i) : ℝ) = Int.fract (y i) := by rfl
    have hyi : y i = (Int.floor (y i) : ℝ) + Int.fract (y i) := by
      have hfr : Int.fract (y i) = y i - (Int.floor (y i) : ℝ) := by rfl
      rw [hfr]
      ring
    calc
      y i - roundYr y E i
          = y i - ((Int.floor (y i) : ℝ) + (if i ∈ E then 1 else 0)) := by rw [hcast]
      _ = (y i - (Int.floor (y i) : ℝ)) - (if i ∈ E then 1 else 0) := by ring
      _ = Int.fract (y i) - (if i ∈ E then 1 else 0) := by rw [hfract]
      _ = th (y i) - (if i ∈ E then 1 else 0) := by rfl
  have hpt : ∀ E : Finset (Fin n),
      (if w < |Z E| then 1 else 0) ≤ (Z E) ^ 2 / w ^ 2 := by
    intro E
    by_cases hE0 : w < |Z E|
    · simp [hE0]
      have hz2 : w ^ 2 < (Z E) ^ 2 := by
        have hwz' : |w| < |Z E| := by simpa [abs_of_pos hw] using hE0
        exact (sq_lt_sq).mpr hwz'
      have hdiv : 1 < (Z E) ^ 2 / w ^ 2 := by
        exact (lt_div_iff₀ hw2pos).mpr (by simpa using hz2)
      exact le_of_lt hdiv
    · simp [hE0]
      have hsq0 : 0 ≤ (Z E) ^ 2 := sq_nonneg _
      positivity
  have hZvar : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (Z E) ^ 2) ≤
      (n : ℝ) / 4 := by
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (Z E) ^ 2)
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              wR y E * (∑ i ∈ B, (th (y i) - (if i ∈ E then 1 else 0))) ^ 2 := by
              apply Finset.sum_congr rfl
              intro E hE
              have hZE : Z E = (∑ i ∈ B, (th (y i) - (if i ∈ E then 1 else 0))) := by
                dsimp [Z]
                apply Finset.sum_congr rfl
                intro i hi
                exact hid i E
              rw [hZE]
      _ ≤ (n : ℝ) / 4 := round_sq_sum_le_n y B
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if w < |∑ i ∈ B, (y i - roundYr y E i)| then 1 else 0))
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (if w < |Z E| then 1 else 0)) := by
            rfl
    _ ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * ((Z E) ^ 2 / w ^ 2)) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (Z E) ^ 2) / w ^ 2 := by
            calc
              (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * ((Z E) ^ 2 / w ^ 2))
                  = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      (wR y E * (Z E) ^ 2) / w ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro E hE
                      ring
              _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    wR y E * (Z E) ^ 2) / w ^ 2 := by
                      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / 4) / w ^ 2 := by
            exact div_le_div_of_nonneg_right hZvar (le_of_lt hw2pos)
    _ = (n : ℝ) / (4 * w ^ 2) := by ring


/-! ## Event masses (paper Lemma l:magic vector, step (iii))

Patterns `B ⊆ Fin n` are the 1-sets of the Bernoulli vector `b`.  `bMass p T`
is the Bernoulli mass of a family `T` of patterns.  `Sgt a z lam` is the
"large-value" family `{B : a < |Σ_{i∈B} zᵢ − λ|}` (i.e. `S(a)` in the paper);
`slabB z lam R` is its complement `{B : |Σ_{i∈B} zᵢ − λ| ≤ R}`.  The rounding
pattern `E` determines the rounded coefficients `roundYr y E`, and
`S̃(a,E) := Sgt a (roundYr y E) lam` is the corresponding random family. -/

/-- subset-sum of the rounded coefficients over `B`. -/
def rSubR {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) (B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ B, roundYr y E i

/-- membership in the "large value" family `{B : a < |Σ_{i∈B} zᵢ − λ|}`. -/
def SgtMem {n : ℕ} (a : ℝ) (z : Fin n → ℝ) (lam : ℝ) (B : Finset (Fin n)) : Prop :=
  a < |rSub z B - lam|

/-- the large-value family `S(a)`. -/
noncomputable def Sgt {n : ℕ} (a : ℝ) (z : Fin n → ℝ) (lam : ℝ) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter (fun B => SgtMem a z lam B)

/-- the slab family `{B : |Σ_{i∈B} zᵢ − λ| ≤ R}` (complement of `Sgt R`). -/
noncomputable def slabB {n : ℕ} (z : Fin n → ℝ) (lam : ℝ) (R : ℝ) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter (fun B => |rSub z B - lam| ≤ R)

/-- Bernoulli mass of a pattern family. -/
def bMass {n : ℕ} (p : unitInterval) (T : Finset (Finset (Fin n))) : ℝ :=
  ∑ B ∈ T, wB n p B

/-- Bernoulli mass is non-negative. -/
lemma bMass_nonneg {n : ℕ} (p : unitInterval) (T : Finset (Finset (Fin n))) :
    0 ≤ bMass p T := by
  dsimp [bMass]
  exact Finset.sum_nonneg (fun B hB => wB_nonneg n p B)

/-- `bMass` of a disjoint union is the sum of the masses. -/
lemma bMass_union {n : ℕ} (p : unitInterval) {T₁ T₂ : Finset (Finset (Fin n))}
    (h : Disjoint T₁ T₂) : bMass p (T₁ ∪ T₂) = bMass p T₁ + bMass p T₂ := by
  dsimp [bMass]
  rw [Finset.sum_union h]

/-- `bMass` is monotone under inclusion. -/
lemma bMass_mono {n : ℕ} (p : unitInterval) {T₁ T₂ : Finset (Finset (Fin n))}
    (h : T₁ ⊆ T₂) : bMass p T₁ ≤ bMass p T₂ := by
  dsimp [bMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (by intro B hB hnot; exact wB_nonneg n p B)

/-- the large-value and slab families partition the powerset (for `a ≥ 0` the
two conditions `a < |·|` and `|·| ≤ a` are complementary). -/
lemma sgt_slab_cover {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (z : Fin n → ℝ) (lam : ℝ) :
    Sgt a z lam ∪ slabB z lam a = (Finset.univ : Finset (Fin n)).powerset := by
  classical
  apply Finset.Subset.antisymm
  · intro B hB
    rw [Finset.mem_union] at hB
    rcases hB with hB1 | hB2
    · exact (Finset.mem_filter.mp hB1).1
    · exact (Finset.mem_filter.mp hB2).1
  · intro B hB
    rw [Finset.mem_union]
    by_cases h : a < |rSub z B - lam|
    · left
      rw [Sgt, Finset.mem_filter]
      exact ⟨hB, h⟩
    · right
      rw [slabB, Finset.mem_filter]
      exact ⟨hB, le_of_not_gt h⟩

/-- the large-value and slab families are disjoint. -/
lemma sgt_slab_disjoint {n : ℕ} {a : ℝ} (z : Fin n → ℝ) (lam : ℝ) :
    Disjoint (Sgt a z lam) (slabB z lam a) := by
  classical
  rw [Finset.disjoint_left]
  intro B hB1 hB2
  have h1 : a < |rSub z B - lam| := (Finset.mem_filter.mp hB1).2
  have h2 : |rSub z B - lam| ≤ a := (Finset.mem_filter.mp hB2).2
  exact (not_lt_of_ge h2) h1


/-- per-pattern Chebyshev: for `B ∈ S(2t)` (i.e. `2t < |Σ_B y − λ|`), the
rounding mass of `{E : B ∉ S̃(t,E)}` is at most `n/(4t²)`. -/
lemma rounded_mass_tail_pt {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) {t : ℝ} (ht : 0 < t)
    {B : Finset (Fin n)} (hB : B ∈ Sgt (2 * t) y lam) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then 1 else 0)) ≤
      (n : ℝ) / (4 * t ^ 2) := by
  classical
  have hpt : ∀ E : Finset (Fin n),
      (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then (1 : ℝ) else 0) ≤
        (if t < |∑ i ∈ B, (y i - roundYr y E i)| then (1 : ℝ) else 0) := by
    intro E
    by_cases hNot : ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B
    · have h1 : (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then (1 : ℝ) else 0) = 1 := by
        rw [if_pos hNot]
      rw [h1]
      have hsub : |rSubR y E B - lam| ≤ t := by
        dsimp [SgtMem] at hNot
        have hNot' : ¬ t < |rSub (fun i : Fin n => roundYr y E i) B - lam| := hNot
        have hle : |rSub (fun i : Fin n => roundYr y E i) B - lam| ≤ t := le_of_not_gt hNot'
        have hconv : |rSub (fun i : Fin n => roundYr y E i) B - lam| = |rSubR y E B - lam| := by
          rfl
        rwa [hconv] at hle
      have hBig : 2 * t < |rSub y B - lam| := by
        have hmem := (Finset.mem_filter.mp hB).2
        dsimp [SgtMem] at hmem
        exact hmem
      have htri : t < |rSubR y E B - rSub y B| := by
        have htri0 : |rSub y B - lam| ≤ |rSubR y E B - rSub y B| + |rSubR y E B - lam| := by
          have h1 := abs_add_le (rSub y B - rSubR y E B) (rSubR y E B - lam)
          have hsum : (rSub y B - rSubR y E B) + (rSubR y E B - lam) = rSub y B - lam := by ring
          have h2 : |rSub y B - lam| ≤ |rSub y B - rSubR y E B| + |rSubR y E B - lam| := by
            simpa [hsum] using h1
          have hrew : |rSub y B - rSubR y E B| = |rSubR y E B - rSub y B| := by
            exact abs_sub_comm (rSub y B) (rSubR y E B)
          rw [hrew] at h2
          exact h2
        nlinarith [hBig, htri0, hsub]
      have hrel : |∑ i ∈ B, (y i - roundYr y E i)| = |rSubR y E B - rSub y B| := by
        have hneg : (∑ i ∈ B, (roundYr y E i - y i)) = -(∑ i ∈ B, (y i - roundYr y E i)) := by
          calc
            (∑ i ∈ B, (roundYr y E i - y i)) = ∑ i ∈ B, (-(y i - roundYr y E i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = -(∑ i ∈ B, (y i - roundYr y E i)) := by rw [Finset.sum_neg_distrib]
        have hsum : (∑ i ∈ B, (roundYr y E i - y i)) = rSubR y E B - rSub y B := by
          dsimp [rSubR, rSub]
          rw [Finset.sum_sub_distrib]
        have hrel0 : |∑ i ∈ B, (roundYr y E i - y i)| = |rSubR y E B - rSub y B| := by
          rw [hsum]
        calc
          |∑ i ∈ B, (y i - roundYr y E i)| = |-(∑ i ∈ B, (y i - roundYr y E i))| := by rw [abs_neg]
          _ = |∑ i ∈ B, (roundYr y E i - y i)| := by rw [← hneg]
          _ = |rSubR y E B - rSub y B| := hrel0
      have hgoal : t < |∑ i ∈ B, (y i - roundYr y E i)| := by
        rwa [← hrel] at htri
      rw [if_pos hgoal]
    · have hS : SgtMem t (fun i : Fin n => roundYr y E i) lam B := by exact (not_not.mp hNot)
      have h1 : (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then (1 : ℝ) else 0) = 0 := by
        rw [if_neg hNot]
      rw [h1]
      by_cases hbig : t < |∑ i ∈ B, (y i - roundYr y E i)|
      · rw [if_pos hbig]
        norm_num
      · rw [if_neg hbig]
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then 1 else 0))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if t < |∑ i ∈ B, (y i - roundYr y E i)| then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ ≤ (n : ℝ) / (4 * t ^ 2) := rounding_tail_le y B ht


/-- the total Bernoulli mass of all patterns is one. -/
lemma bMass_total_eq_one {n : ℕ} (p : unitInterval) :
    bMass p ((Finset.univ : Finset (Fin n)).powerset) = 1 := by
  dsimp [bMass]
  exact sum_wB_eq_one n p

/-- **telescoping substrate**: the rounding-expectation of the mass of
`S(2t) ∖ S̃(t)` is at most `n/(4t²)·μ(S(2t))`. -/
lemma rounded_mass_diff_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p ((Sgt (2 * t) y lam).filter
          (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)))) ≤
      (n : ℝ) / (4 * t ^ 2) * bMass p (Sgt (2 * t) y lam) := by
  classical
  let c : ℝ := (n : ℝ) / (4 * t ^ 2)
  let D : Finset (Finset (Fin n)) := Sgt (2 * t) y lam
  let P : Finset (Fin n) → Finset (Fin n) → Prop :=
    fun E B => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B
  have hD : D = Sgt (2 * t) y lam := rfl
  have hS1 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B)))) =
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro E hE
    dsimp [bMass]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases h : P E B <;> simp [h]
  have hS2 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) := by
    rw [Finset.sum_comm]
  have hS3 : (∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    ring
  have hS4 : (∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) ≤ ∑ B ∈ D, wB n p B * c := by
    apply Finset.sum_le_sum
    intro B hB
    exact mul_le_mul_of_nonneg_left (rounded_mass_tail_pt y lam ht (B := B) (by simpa [D] using hB)) (wB_nonneg n p B)
  have hS5 : (∑ B ∈ D, wB n p B * c) = c * bMass p D := by
    dsimp [bMass]
    rw [← Finset.sum_mul]
    dsimp [c]
    ring
  have hmainD : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B)))) ≤ c * bMass p D := by
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B))))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0) := hS1
      _ = ∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * wB n p B * (if P E B then 1 else 0) := hS2
      _ = ∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if P E B then 1 else 0)) := hS3
      _ ≤ ∑ B ∈ D, wB n p B * c := hS4
      _ = c * bMass p D := hS5
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p ((Sgt (2 * t) y lam).filter
          (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B))))
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B)))) := by
            rfl
    _ ≤ c * bMass p D := hmainD
    _ = c * bMass p (Sgt (2 * t) y lam) := by
            rw [hD]


/-- positive part: `max(0, μ_t(ỹ^E) − μ_{2t}(y)) ≤ μ(S(2t) ∖ S̃(t,E))`. -/
lemma rounded_pospart_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) (E : Finset (Fin n)) :
    max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
        bMass p (slabB y lam (2 * t))) ≤
      bMass p ((Sgt (2 * t) y lam).filter
        (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)) := by
  classical
  let Tt : Finset (Finset (Fin n)) := slabB (fun i : Fin n => roundYr y E i) lam t
  let St1 : Finset (Finset (Fin n)) := Sgt t (fun i : Fin n => roundYr y E i) lam
  let T : Finset (Finset (Fin n)) := slabB y lam (2 * t)
  let St : Finset (Finset (Fin n)) := Sgt (2 * t) y lam
  let Diff : Finset (Finset (Fin n)) := St.filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)
  have hSt : bMass p St = 1 - bMass p T := by
    have hdisj := sgt_slab_disjoint (z := y) (lam := lam) (a := 2 * t)
    have htotal := bMass_total_eq_one (n := n) p
    have hsplit := bMass_union p hdisj
    have h1 : bMass p (Sgt (2 * t) y lam ∪ slabB y lam (2 * t)) = bMass p St + bMass p T := by
      dsimp [St, T]
      exact hsplit
    have h2 : bMass p (Sgt (2 * t) y lam ∪ slabB y lam (2 * t)) = 1 := by
      have h2t : 0 ≤ 2 * t := by nlinarith [ht]
      rw [sgt_slab_cover (a := 2 * t) h2t y lam]
      exact htotal
    dsimp [St, T]
    linarith
  have hTt : bMass p Tt = 1 - bMass p St1 := by
    have hdisj := sgt_slab_disjoint (z := fun i : Fin n => roundYr y E i) (lam := lam) (a := t)
    have htotal := bMass_total_eq_one (n := n) p
    have hsplit := bMass_union p hdisj
    have h1 : bMass p (Sgt t (fun i : Fin n => roundYr y E i) lam ∪ slabB (fun i : Fin n => roundYr y E i) lam t) =
        bMass p St1 + bMass p Tt := by
      dsimp [St1, Tt]
      exact hsplit
    have h2 : bMass p (Sgt t (fun i : Fin n => roundYr y E i) lam ∪ slabB (fun i : Fin n => roundYr y E i) lam t) = 1 := by
      rw [sgt_slab_cover (a := t) (le_of_lt ht) (fun i : Fin n => roundYr y E i) lam]
      exact htotal
    dsimp [St1, Tt]
    linarith
  have hdiff : bMass p Tt - bMass p T = bMass p St - bMass p St1 := by
    rw [hTt, hSt]
    ring
  have hle1 : bMass p St - bMass p St1 ≤ bMass p Diff := by
    dsimp [Diff]
    have hStD : bMass p St = bMass p (St.filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)) +
        bMass p (St.filter (fun B : Finset (Fin n) => SgtMem t (fun i : Fin n => roundYr y E i) lam B)) := by
      dsimp [bMass]
      calc
        (∑ B ∈ St, wB n p B)
            = (∑ B ∈ St, (if ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B then wB n p B else 0)) +
              (∑ B ∈ St, (if SgtMem t (fun i : Fin n => roundYr y E i) lam B then wB n p B else 0)) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro B hB
                by_cases hP : SgtMem t (fun i : Fin n => roundYr y E i) lam B <;> simp [hP]
        _ = (∑ B ∈ St.filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B), wB n p B) +
            (∑ B ∈ St.filter (fun B : Finset (Fin n) => SgtMem t (fun i : Fin n => roundYr y E i) lam B), wB n p B) := by
              rw [← Finset.sum_filter, ← Finset.sum_filter]
    have hIle : bMass p (St.filter (fun B : Finset (Fin n) => SgtMem t (fun i : Fin n => roundYr y E i) lam B)) ≤ bMass p St1 := by
      have hsubI : St.filter (fun B : Finset (Fin n) => SgtMem t (fun i : Fin n => roundYr y E i) lam B) ⊆ St1 := by
        intro B hB
        rw [Finset.mem_filter] at hB
        rcases hB with ⟨hBSt, hBP⟩
        dsimp [St] at hBSt
        rw [Sgt, Finset.mem_filter] at hBSt
        dsimp [St1]
        rw [Sgt, Finset.mem_filter]
        exact ⟨hBSt.1, hBP⟩
      exact bMass_mono p hsubI
    nlinarith
  have hpos0 : 0 ≤ bMass p Diff := bMass_nonneg p Diff
  have hdiffle : bMass p Tt - bMass p T ≤ bMass p Diff := by
    rw [hdiff]
    exact hle1
  exact max_le hpos0 hdiffle

/-- expectation of the positive part: `E_ξ max(0, μ_t(ỹ) − μ_{2t}(y)) ≤ n/(4t²)`. -/
lemma rounded_pospart_E_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
          bMass p (slabB y lam (2 * t)))) ≤
      (n : ℝ) / (4 * t ^ 2) := by
  classical
  let c : ℝ := (n : ℝ) / (4 * t ^ 2)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have h1 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have h2 : 0 ≤ 4 * t ^ 2 := by positivity
    exact div_nonneg h1 h2
  have hpt : ∀ E : Finset (Fin n),
      max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) - bMass p (slabB y lam (2 * t))) ≤
        bMass p ((Sgt (2 * t) y lam).filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)) := by
    intro E
    exact rounded_pospart_le p y lam ht E
  have hsum : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) - bMass p (slabB y lam (2 * t)))) ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * bMass p ((Sgt (2 * t) y lam).filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B))) := by
    apply Finset.sum_le_sum
    intro E hE
    exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
  have hb : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * bMass p ((Sgt (2 * t) y lam).filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B))) ≤
      c * bMass p (Sgt (2 * t) y lam) := by
    have hmd := rounded_mass_diff_le p y lam ht
    dsimp [c]
    exact hmd
  have hμ1 : bMass p (Sgt (2 * t) y lam) ≤ 1 := by
    have hsub : Sgt (2 * t) y lam ⊆ (Finset.univ : Finset (Fin n)).powerset := by
      intro B hB
      exact (Finset.mem_filter.mp hB).1
    have hle := bMass_mono p hsub
    rwa [bMass_total_eq_one] at hle
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) - bMass p (slabB y lam (2 * t))))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * bMass p ((Sgt (2 * t) y lam).filter (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B))) := hsum
    _ ≤ c * bMass p (Sgt (2 * t) y lam) := hb
    _ ≤ c := by
            have hle := mul_le_mul_of_nonneg_left hμ1 hc0
            simpa using hle
    _ = (n : ℝ) / (4 * t ^ 2) := by
            dsimp [c]


/-- Markov for the rounding weights: `E_ξ[1_{a < f}] ≤ E_ξ[f]/a` for nonneg
`f` and `a > 0`. -/
lemma wR_markov {n : ℕ} (y : Fin n → ℝ) (f : Finset (Fin n) → ℝ) {a : ℝ} (ha : 0 < a)
    (hf : ∀ E : Finset (Fin n), 0 ≤ f E) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if a < f E then 1 else 0)) ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * f E) / a := by
  classical
  have hpt : ∀ E : Finset (Fin n),
      (if a < f E then 1 else 0) ≤ f E / a := by
    intro E
    by_cases hE0 : a < f E
    · simp [hE0]
      have hdiv : 1 ≤ f E / a := by
        exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using (le_of_lt hE0))
      exact hdiv
    · simp [hE0]
      have hpos : 0 ≤ f E / a := by
        exact div_nonneg (hf E) (le_of_lt ha)
      exact hpos
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (if a < f E then 1 else 0))
        ≤ ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (f E / a) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * f E) / a := by
            calc
              (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * (f E / a))
                  = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, (wR y E * f E) / a := by
                      apply Finset.sum_congr rfl
                      intro E hE
                      ring
              _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * f E) / a := by
                      rw [Finset.sum_div]

/-- the dyadic level `t_k := 2^k·√n`. -/
def level (n k : ℕ) : ℝ := (2 : ℝ) ^ k * Real.sqrt (n : ℝ)

/-- the positive-part functional at scale `s`. -/
def posMass {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    (E : Finset (Fin n)) (s : ℝ) : ℝ :=
  max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam s) -
      bMass p (slabB y lam (2 * s)))

/-- the positive part is non-negative. -/
lemma posMass_nonneg {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    (E : Finset (Fin n)) (s : ℝ) : 0 ≤ posMass p y lam E s := by
  dsimp [posMass]
  exact le_max_left (a := (0 : ℝ))
    (b := (bMass p (slabB (fun i : Fin n => roundYr y E i) lam s) - bMass p (slabB y lam (2 * s))))

/-- per-level Markov bound for the bad event `B_k := {8L·t_k < pos(t_k,·)}`
(raw post-Markov form). -/
lemma level_bad_prob_raw {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL : 0 < L) (hn : 1 ≤ n) (k : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if 8 * L * level n k < posMass p y lam E (level n k) then 1 else 0)) ≤
      (n : ℝ) / (4 * (level n k) ^ 2) / (8 * L * level n k) := by
  classical
  let t : ℝ := level n k
  have ht0 : 0 < t := by
    dsimp [t, level]
    have h2 : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    positivity
  have hE : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
        bMass p (slabB y lam (2 * t)))) ≤ (n : ℝ) / (4 * t ^ 2) := by
    exact rounded_pospart_E_le p y lam ht0
  have hMarkov : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * (if 8 * L * t < max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
          bMass p (slabB y lam (2 * t))) then 1 else 0)) ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
          bMass p (slabB y lam (2 * t)))) / (8 * L * t) := by
    exact wR_markov y (fun E : Finset (Fin n) => max 0
      (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) - bMass p (slabB y lam (2 * t))))
      (a := 8 * L * t) (by positivity) (by intro E; exact posMass_nonneg p y lam E t)
  have hpos8 : 0 ≤ 8 * L * t := by positivity
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if 8 * L * level n k < posMass p y lam E (level n k) then 1 else 0))
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if 8 * L * t < max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
                bMass p (slabB y lam (2 * t))) then 1 else 0)) := by
            rfl
    _ ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
            bMass p (slabB y lam (2 * t)))) / (8 * L * t) := hMarkov
    _ ≤ (n : ℝ) / (4 * t ^ 2) / (8 * L * t) := by
            exact div_le_div_of_nonneg_right hE hpos8
    _ = (n : ℝ) / (4 * (level n k) ^ 2) / (8 * L * level n k) := by rfl

/-- closed-form per-level bound: `P(B_k) ≤ (1/(32L√n))·(1/8)^k`. -/
lemma level_bad_prob {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL : 0 < L) (hn : 1 ≤ n) (k : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if 8 * L * level n k < posMass p y lam E (level n k) then 1 else 0)) ≤
      (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
  classical
  let t : ℝ := level n k
  have ht0 : 0 < t := by
    dsimp [t, level]
    have h2 : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    positivity
  have hraw := level_bad_prob_raw p y lam hL hn k
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrtnz : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt
  have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
  have h8k : (8 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have htk3 : t ^ 3 = (8 : ℝ) ^ k * Real.sqrt (n : ℝ) ^ 3 := by
    dsimp [t, level]
    rw [mul_pow]
    have h1 : ((2 : ℝ) ^ k) ^ 3 = (8 : ℝ) ^ k := by
      calc
        ((2 : ℝ) ^ k) ^ 3 = (2 : ℝ) ^ (k * 3) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (3 * k) := by congr 1; rw [mul_comm]
        _ = ((2 : ℝ) ^ 3) ^ k := by rw [pow_mul]
        _ = (8 : ℝ) ^ k := by norm_num
    rw [h1]
  have hsq3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ^ 3 = (Real.sqrt (n : ℝ) ^ 2) * Real.sqrt (n : ℝ) := by ring_nf
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
        rw [Real.sq_sqrt (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ (n : ℝ))]
  have hEq : (n : ℝ) / (4 * t ^ 2) / (8 * L * t) =
      (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
    calc
      (n : ℝ) / (4 * t ^ 2) / (8 * L * t)
          = (n : ℝ) / (32 * L * t ^ 3) := by
            field_simp [ht0.ne', hL.ne']
            norm_num
      _ = (n : ℝ) / (32 * L * ((8 : ℝ) ^ k * Real.sqrt (n : ℝ) ^ 3)) := by
            rw [htk3]
      _ = (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
            rw [hsq3]
            field_simp [hnz, hsqrtnz, hL.ne', h8k]
            have hmul : (1 : ℝ) = (8 : ℝ) ^ k * ((1 / 8 : ℝ) ^ k) := by
              rw [← mul_pow]
              norm_num
            exact hmul
  exact le_trans hraw (le_of_eq hEq)

lemma geom8_sum_le {K : ℕ} : (∑ k ∈ Finset.range K, ((1 / 8 : ℝ) ^ k)) ≤ 8 / 7 := by
  classical
  have hgeo := geom_sum_eq (x := (1 / 8 : ℝ)) (by norm_num : (1 / 8 : ℝ) ≠ 1) K
  have hval : ((1 / 8 : ℝ) ^ K - 1) / ((1 / 8 : ℝ) - 1) = (8 / 7) * (1 - (1 / 8 : ℝ) ^ K) := by
    field_simp
    ring
  calc
    (∑ k ∈ Finset.range K, ((1 / 8 : ℝ) ^ k)) = ((1 / 8 : ℝ) ^ K - 1) / ((1 / 8 : ℝ) - 1) := hgeo
    _ = (8 / 7) * (1 - (1 / 8 : ℝ) ^ K) := hval
    _ ≤ (8 / 7) * 1 := by
            have hpos8 : (0 : ℝ) ≤ 8 / 7 := by norm_num
            have hle1 : 1 - (1 / 8 : ℝ) ^ K ≤ 1 := by
              have hnon : 0 ≤ (1 / 8 : ℝ) ^ K := pow_nonneg (by norm_num) K
              nlinarith
            exact mul_le_mul_of_nonneg_left hle1 hpos8
    _ = 8 / 7 := by ring

/-- the truncated bad event for E1 has rounding mass at most `1/28`. -/
lemma e1K_bad_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L) (hn : 1 ≤ n) (K : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧
            8 * L * level n k < posMass p y lam E (level n k) then 1 else 0)) ≤
      (1 : ℝ) / 28 := by
  classical
  let Bad : ℕ → Finset (Fin n) → Prop := fun k E =>
    8 * L * level n k < posMass p y lam E (level n k)
  have hpt : ∀ E : Finset (Fin n),
      (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) ≤
        ∑ k ∈ Finset.range K, (if Bad k E then (1 : ℝ) else 0) := by
    intro E
    by_cases hE : ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E
    · have h1 : (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) = 1 := by
        rw [if_pos hE]
      rw [h1]
      rcases hE with ⟨k, hk, hbad⟩
      have hnonneg : ∀ j : ℕ, j ∈ Finset.range K → 0 ≤ (if Bad j E then (1 : ℝ) else 0) := by
        intro j hj
        by_cases hj0 : Bad j E <;> simp [hj0]
      have h1le := Finset.single_le_sum (s := Finset.range K) hnonneg hk
      have hfk : (if Bad k E then (1 : ℝ) else 0) = 1 := by
        simp [hbad]
      rwa [hfk] at h1le
    · have h1 : (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) = 0 := by
        rw [if_neg hE]
      rw [h1]
      exact Finset.sum_nonneg (by intro j hj; by_cases hj0 : Bad j E <;> simp [hj0])
  -- sum level bounds
  have hlevel : ∀ k : ℕ, k ∈ Finset.range K →
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if Bad k E then 1 else 0)) ≤
        (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
    intro k hk
    exact level_bad_prob p y lam hL0 hn k
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsum_le : (∑ k ∈ Finset.range K, (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k)) ≤
      (8 / 7) / (32 * L * Real.sqrt (n : ℝ)) := by
    calc
      (∑ k ∈ Finset.range K, (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k))
          = (1 / (32 * L * Real.sqrt (n : ℝ))) * (∑ k ∈ Finset.range K, ((1 / 8 : ℝ) ^ k)) := by
            rw [Finset.mul_sum]
      _ ≤ (1 / (32 * L * Real.sqrt (n : ℝ))) * (8 / 7) := by
            have hpos : 0 ≤ 1 / (32 * L * Real.sqrt (n : ℝ)) := by positivity
            exact mul_le_mul_of_nonneg_left geom8_sum_le hpos
      _ = (8 / 7) / (32 * L * Real.sqrt (n : ℝ)) := by ring
  have hfinal : (8 / 7) / (32 * L * Real.sqrt (n : ℝ)) ≤ (1 : ℝ) / 28 := by
    have hden : 0 < 32 * L * Real.sqrt (n : ℝ) := by positivity
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hm := Real.sqrt_le_sqrt (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ))
      rwa [Real.sqrt_one] at hm
    have hLsqrt : (1 : ℝ) ≤ L * Real.sqrt (n : ℝ) := by nlinarith [hL1, hsqrt1]
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (∑ k ∈ Finset.range K, (if Bad k E then 1 else 0))) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ = ∑ k ∈ Finset.range K,
          (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if Bad k E then 1 else 0)) := by
            rw [Finset.sum_comm]
            -- Σ_E (wR·Σ_k if) = Σ_E Σ_k (wR·if) then swap: first push wR into the inner sum per E:
            apply Finset.sum_congr rfl
            intro E hE
            rw [Finset.mul_sum]
    _ ≤ (∑ k ∈ Finset.range K, (1 / (32 * L * Real.sqrt (n : ℝ))) * ((1 / 8 : ℝ) ^ k)) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hlevel k hk
    _ ≤ (1 : ℝ) / 28 := le_trans hsum_le hfinal



/-- the E1K good event (no bad level below `K`) has rounding mass at least
`1 − 1/28` (hence `> 9/16`).  This is the bridge from `e1K_bad_le` to E1. -/
lemma e1K_good_mass {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L) (hn : 1 ≤ n) (K : ℕ) :
    (1 : ℝ) - 1 / 28 ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∀ k : ℕ, k ∈ Finset.range K →
            ¬ (8 * L * level n k < posMass p y lam E (level n k)) then 1 else 0)) := by
  classical
  let Bad : ℕ → Finset (Fin n) → Prop := fun k E =>
    8 * L * level n k < posMass p y lam E (level n k)
  have hbad := e1K_bad_le p y lam hL0 hL1 hn K
  have hpt : ∀ E : Finset (Fin n),
      (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then (1 : ℝ) else 0) =
        (1 : ℝ) - (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0) := by
    intro E
    by_cases hE : ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E
    · have hnot : ¬ ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E := by
        rcases hE with ⟨k, hk, hbadk⟩
        intro h
        exact h k hk hbadk
      rw [if_pos hE]
      rw [if_neg hnot]
      norm_num
    · have hfor : ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E := by
        intro k hk hbadk
        exact hE ⟨k, hk, hbadk⟩
      rw [if_neg hE]
      rw [if_pos hfor]
      norm_num
  calc
    (1 : ℝ) - 1 / 28 ≤ (1 : ℝ) -
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
            have hb : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) ≤ 1 / 28 := hbad
            linarith
    _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then 1 else 0)) := by
            calc
              (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                  wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0))
                  = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) -
                      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
                        rw [sum_wR_eq_one]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      (wR y E - wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
                        rw [← Finset.sum_sub_distrib]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      wR y E * (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro E hE
                        rw [hpt E]
                        ring


/-- slab mass is monotone in the radius. -/
lemma slab_mass_mono {n : ℕ} (p : unitInterval) (z : Fin n → ℝ) (lam : ℝ)
    {s s' : ℝ} (hs : s ≤ s') :
    bMass p (slabB z lam s) ≤ bMass p (slabB z lam s') := by
  classical
  apply bMass_mono
  intro B hB
  dsimp [slabB] at hB ⊢
  rw [Finset.mem_filter] at hB ⊢
  exact ⟨hB.1, le_trans hB.2 hs⟩

/-- single-level small-ball consequence: on the good event at level `t`
(`pos(t) ≤ 8Lt`) together with the hypothesis `μ_{2t}(y) ≤ 2Lt`,
`μ_t(ỹ^E) ≤ 10Lt`. -/
lemma good_level_small_ball {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L t : ℝ} (hL0 : 0 < L) {E : Finset (Fin n)}
    (hpos : max 0 (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
        bMass p (slabB y lam (2 * t))) ≤ 8 * L * t)
    (hsb : bMass p (slabB y lam (2 * t)) ≤ L * (2 * t)) :
    bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 10 * L * t := by
  classical
  have hdiff : bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) -
        bMass p (slabB y lam (2 * t)) ≤ 8 * L * t := by
    exact le_trans
      (le_max_right (a := 0)
        (bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) - bMass p (slabB y lam (2 * t))))
      hpos
  nlinarith [hdiff, hsb]


/-- **subset form of the telescoping substrate**: for any family `F ⊆ S(2t)`,
the rounding-expectation of the mass of `F ∖ S̃(t)` is at most
`(n/(4t²))·μ(F)`.  (Same proof as `rounded_mass_diff_le` with `D := F`;
used for the dyadic band `F := S(2^j t) ∖ S(2^{j+1} t)` in the E1 argument.) -/
lemma rounded_mass_subset_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) {F : Finset (Finset (Fin n))}
    (hF : F ⊆ Sgt (2 * t) y lam) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (F.filter
          (fun B : Finset (Fin n) => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B)))) ≤
      (n : ℝ) / (4 * t ^ 2) * bMass p F := by
  classical
  let c : ℝ := (n : ℝ) / (4 * t ^ 2)
  let P : Finset (Fin n) → Finset (Fin n) → Prop :=
    fun E B => ¬ SgtMem t (fun i : Fin n => roundYr y E i) lam B
  have hS1 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (F.filter (fun B : Finset (Fin n) => P E B)))) =
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ F, wR y E * wB n p B * (if P E B then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro E hE
    dsimp [bMass]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases h : P E B <;> simp [h]
  have hS2 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ F, wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ F, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) := by
    rw [Finset.sum_comm]
  have hS3 : (∑ B ∈ F, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ F, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    ring
  have hS4 : (∑ B ∈ F, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) ≤ ∑ B ∈ F, wB n p B * c := by
    apply Finset.sum_le_sum
    intro B hB
    exact mul_le_mul_of_nonneg_left
      (rounded_mass_tail_pt y lam ht (B := B) (hF hB)) (wB_nonneg n p B)
  have hS5 : (∑ B ∈ F, wB n p B * c) = c * bMass p F := by
    dsimp [bMass]
    rw [← Finset.sum_mul]
    dsimp [c]
    ring
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (F.filter (fun B : Finset (Fin n) => P E B))))
        = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            ∑ B ∈ F, wR y E * wB n p B * (if P E B then 1 else 0) := hS1
    _ = ∑ B ∈ F, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * wB n p B * (if P E B then 1 else 0) := hS2
    _ = ∑ B ∈ F, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if P E B then 1 else 0)) := hS3
    _ ≤ ∑ B ∈ F, wB n p B * c := hS4
    _ = c * bMass p F := hS5


/-- any slab family has Bernoulli mass at most one. -/
lemma bMass_le_one {n : ℕ} (p : unitInterval) (z : Fin n → ℝ) (lam : ℝ) (R : ℝ) :
    bMass p (slabB z lam R) ≤ 1 := by
  classical
  have hsub : slabB z lam R ⊆ (Finset.univ : Finset (Fin n)).powerset := by
    intro B hB
    dsimp [slabB] at hB
    exact (Finset.mem_filter.mp hB).1
  calc
    bMass p (slabB z lam R) ≤ bMass p ((Finset.univ : Finset (Fin n)).powerset) := bMass_mono p hsub
    _ = 1 := bMass_total_eq_one p

/-- the dyadic level `t_k := 2^k·√n` is at least `√n`. -/
lemma level_sq_ge {n : ℕ} (k : ℕ) : Real.sqrt (n : ℝ) ≤ level n k := by
  dsimp [level]
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (n := k) (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (n : ℝ))
  simpa using hm

/-- the dyadic level is positive (for `n ≥ 1`). -/
lemma level_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 0 < level n k := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  exact lt_of_lt_of_le hsqrt (level_sq_ge k)

/-- levels are monotone in the index. -/
lemma level_mono {n : ℕ} {k k' : ℕ} (hk : k ≤ k') : level n k ≤ level n k' := by
  dsimp [level]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
    (Real.sqrt_nonneg (n : ℝ))

/-- levels are strictly increasing in the index (for `n ≥ 1`). -/
lemma level_lt_level {n : ℕ} (hn : 1 ≤ n) {k k' : ℕ} (hk : k < k') :
    level n k < level n k' := by
  have hstep : ∀ m : ℕ, level n m < level n (m + 1) := by
    intro m
    dsimp [level]
    rw [pow_succ]
    have hpos : 0 < (2 : ℝ) ^ m * Real.sqrt (n : ℝ) := level_pos hn m
    nlinarith
  -- iterate: level k < level (k+1) ≤ ... ≤ level k'
  have hmono : level n (k + 1) ≤ level n k' := level_mono (n := n) (Nat.succ_le_iff.mpr hk)
  exact lt_of_lt_of_le (hstep k) hmono

/-- contrapositive of strict monotonicity: level-strict-inequality forces index
inequality. -/
lemma level_lt_of_lt {n : ℕ} (hn : 1 ≤ n) {k k' : ℕ} (h : level n k < level n k') :
    k < k' := by
  by_contra hnot
  have hk' : k' ≤ k := Nat.le_of_not_gt hnot
  have hmono : level n k' ≤ level n k := level_mono (n := n) hk'
  -- level k' ≤ level k, contradicts level k < level k'
  exact (not_lt_of_ge hmono) h

/-- any real number is eventually below some dyadic level. -/
lemma exists_level_gt {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ∃ k : ℕ, t < level n k := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hten : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, t / Real.sqrt (n : ℝ) < (2 : ℝ) ^ k :=
    hten (Filter.eventually_gt_atTop (t / Real.sqrt (n : ℝ)))
  rcases hev.exists with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  dsimp [level]
  have hm := (div_lt_iff₀ hsqrt).1 hk
  -- hm : t < (2:ℝ)^k * √n
  exact hm


/-- dyadic rounding of `t ≥ √n`: there is a level index `k ≥ 1` with
`t < t_k ≤ 2t` (so `t_k` is the smallest dyadic level strictly above `t`). -/
lemma dyadic_round_le_twice {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : Real.sqrt (n : ℝ) ≤ t) :
    ∃ k : ℕ, 1 ≤ k ∧ t < level n k ∧ level n k ≤ 2 * t := by
  classical
  have hkexist : ∃ k : ℕ, t < level n k := exists_level_gt hn t
  let k0 : ℕ := Nat.find hkexist
  have hk_gt : t < level n k0 := Nat.find_spec hkexist
  have hk_min : ∀ m : ℕ, t < level n m → k0 ≤ m := by
    intro m hm
    exact Nat.find_min' (p := fun k : ℕ => t < level n k) (H := hkexist) hm
  have hk1 : 1 ≤ k0 := by
    by_contra h0
    have hk0z : k0 = 0 := by omega
    have hbad : t < level n 0 := by simpa [hk0z] using hk_gt
    have h0v : level n 0 = Real.sqrt (n : ℝ) := by dsimp [level]; norm_num
    have hbad' : t < Real.sqrt (n : ℝ) := by rwa [h0v] at hbad
    exact (not_lt_of_ge ht) hbad'
  have hk2 : level n k0 ≤ 2 * t := by
    have hnot_prev : ¬ t < level n (k0 - 1) := by
      intro hp
      have hle := hk_min (k0 - 1) hp
      have hle' : k0 ≤ k0 - 1 → False := by omega
      exact hle' hle
    have hprev : level n (k0 - 1) ≤ t := le_of_not_gt hnot_prev
    have hk0succ : k0 = (k0 - 1) + 1 := by omega
    have hdouble : level n k0 = 2 * level n (k0 - 1) := by
      dsimp [level]
      have hsucc : (2 : ℝ) ^ k0 = (2 : ℝ) ^ ((k0 - 1) + 1) := by rw [← hk0succ]
      rw [hsucc, pow_succ]
      ring
    calc
      level n k0 = 2 * level n (k0 - 1) := hdouble
      _ ≤ 2 * t := by exact mul_le_mul_of_nonneg_left hprev (by norm_num)
  exact ⟨k0, hk1, hk_gt, hk2⟩

/-- **E1 sealing, small-ball consequence**: if the small-ball hypothesis holds at all
scales `s ≥ √n` and the rounding pattern `E` is good at all dyadic levels below `K`
(no `8L·t_k < pos(t_k)`), and `K` is high enough that `t_K ≥ 1/(10L)`, then the
rounded vector `ỹ^E` satisfies `μ_t(ỹ^E) ≤ 20L·t` for every `t ≥ √n`. -/
lemma e1K_good_small_ball {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    {K : ℕ} (hK : 1 / (10 * L) ≤ level n K)
    {E : Finset (Fin n)}
    (hgood : E ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
      (fun E => ∀ k : ℕ, k ∈ Finset.range K →
        ¬ (8 * L * level n k < posMass p y lam E (level n k)))) :
    ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 20 * L * t := by
  classical
  intro t ht
  by_cases hbig : 1 / (20 * L) ≤ t
  · -- trivial: μ_t ≤ 1 ≤ 20Lt
    have htriv : bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 1 :=
      bMass_le_one p (fun i : Fin n => roundYr y E i) lam t
    have hge1 : (1 : ℝ) ≤ 20 * L * t := by
      have hne : (20 * L) ≠ 0 := by positivity
      have hm := mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ 20 * L)
      -- hm : (20L)·(1/(20L)) ≤ (20L)·t
      have h1le : (1 : ℝ) ≤ (20 * L) * t := by
        calc
          (1 : ℝ) = (20 * L) * (1 / (20 * L)) := by field_simp [hne]
          _ ≤ (20 * L) * t := mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ 20 * L)
      simpa using h1le
    exact le_trans htriv hge1
  · -- dyadic: t < 1/(20L); round t up to t_k
    have htlt : t < 1 / (20 * L) := lt_of_not_ge hbig
    rcases dyadic_round_le_twice (n := n) hn ht with ⟨k0, hk1, hk_gt, htk2⟩
    have h2t : 2 * t < 1 / (10 * L) := by
      have hb : 2 * t < 2 * (1 / (20 * L)) := mul_lt_mul_of_pos_left htlt (by norm_num)
      have hb' : 2 * (1 / (20 * L)) = 1 / (10 * L) := by
        have hne : (20 * L) ≠ 0 := by positivity
        field_simp [hne]
        ring
      rwa [hb'] at hb
    have hlt10 : level n k0 < 1 / (10 * L) := lt_of_le_of_lt htk2 h2t
    have hk_ltK : k0 < K := level_lt_of_lt hn (lt_of_lt_of_le hlt10 hK)
    have hgood2 : ∀ k : ℕ, k ∈ Finset.range K →
        ¬ (8 * L * level n k < posMass p y lam E (level n k)) := by
      rw [Finset.mem_filter] at hgood
      exact hgood.2
    have hposle : posMass p y lam E (level n k0) ≤ 8 * L * level n k0 :=
      le_of_not_gt (hgood2 k0 (Finset.mem_range.mpr hk_ltK))
    have hmono1 : bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤
        bMass p (slabB (fun i : Fin n => roundYr y E i) lam (level n k0)) :=
      slab_mass_mono p (fun i : Fin n => roundYr y E i) lam (le_of_lt hk_gt)
    have hdiff : bMass p (slabB (fun i : Fin n => roundYr y E i) lam (level n k0)) -
          bMass p (slabB y lam (2 * level n k0)) ≤
        posMass p y lam E (level n k0) := by
      dsimp [posMass]
      exact le_max_right (a := (0 : ℝ))
        (b := (bMass p (slabB (fun i : Fin n => roundYr y E i) lam (level n k0)) -
          bMass p (slabB y lam (2 * level n k0))))
    have h1le : bMass p (slabB (fun i : Fin n => roundYr y E i) lam (level n k0)) ≤
        bMass p (slabB y lam (2 * level n k0)) + 8 * L * level n k0 := by
      nlinarith [hdiff, hposle]
    have hsb2 : bMass p (slabB y lam (2 * level n k0)) ≤ L * (2 * level n k0) := by
      have hsq : Real.sqrt (n : ℝ) ≤ 2 * level n k0 := by
        have h1 := level_sq_ge (n := n) k0
        have h2 : (0 : ℝ) ≤ level n k0 := le_of_lt (level_pos hn k0)
        nlinarith
      exact hsb (2 * level n k0) hsq
    have h10le : bMass p (slabB (fun i : Fin n => roundYr y E i) lam (level n k0)) ≤
        10 * L * level n k0 := by
      nlinarith [h1le, hsb2]
    have hLt : 10 * L * level n k0 ≤ 20 * L * t := by
      have h1 : (10 * L) * level n k0 ≤ (10 * L) * (2 * t) :=
        mul_le_mul_of_nonneg_left htk2 (by positivity : 0 ≤ 10 * L)
      have h2 : (10 * L) * (2 * t) = 20 * L * t := by ring
      rwa [h2] at h1
    exact le_trans hmono1 (le_trans h10le hLt)



/-- ℓ₁-type norm of the vector. -/
def ynAbs {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ i : Fin n, |y i|

/-- `|rSub y B − λ|` is bounded by `Σ|yᵢ| + |λ|`. -/
lemma rSub_abs_le_ynAbs {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (B : Finset (Fin n)) :
    |rSub y B - lam| ≤ ynAbs y + |lam| := by
  dsimp [rSub]
  have h1' : |(∑ i ∈ B, y i) - lam| ≤ |(∑ i ∈ B, y i)| + |lam| := by
    have h1 := abs_add_le (∑ i ∈ B, y i) (-lam)
    have hrew : (∑ i ∈ B, y i) + (-lam) = (∑ i ∈ B, y i) - lam := by ring
    simpa [hrew] using h1
  have h2 : |(∑ i ∈ B, y i)| ≤ ∑ i ∈ B, |y i| :=
    Finset.abs_sum_le_sum_abs (fun i : Fin n => y i) B
  have h3 : (∑ i ∈ B, |y i|) ≤ ∑ i : Fin n, |y i| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (by intro i hi hnot; exact abs_nonneg (y i))
  calc
    |(∑ i ∈ B, y i) - lam| ≤ |(∑ i ∈ B, y i)| + |lam| := h1'
    _ ≤ (∑ i ∈ B, |y i|) + |lam| := by exact add_le_add_left h2 |lam|
    _ ≤ (∑ i : Fin n, |y i|) + |lam| := by exact add_le_add_left h3 |lam|
    _ = ynAbs y + |lam| := rfl

/-- `Sgt w` is empty when `w` exceeds all possible sums. -/
lemma Sgt_empty_of_gt {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (w : ℝ)
    (h : ∀ B : Finset (Fin n), |rSub y B - lam| < w) :
    Sgt w y lam = ∅ := by
  classical
  have hcov : ∀ B : Finset (Fin n), B ∉ Sgt w y lam := by
    intro B hB
    have hw : w < |rSub y B - lam| := by
      dsimp [Sgt] at hB
      exact (Finset.mem_filter.mp hB).2
    exact (not_lt_of_ge (le_of_lt (h B))) hw
  exact Finset.eq_empty_iff_forall_notMem.mpr hcov

/-- the dyadic band `S(2^{k+1}t) ∖ S(2^{k+2}t)`. -/
def band {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (t : ℝ) (k : ℕ) : Finset (Finset (Fin n)) :=
  (Sgt ((2 : ℝ) ^ (k + 1) * t) y lam) \ (Sgt ((2 : ℝ) ^ (k + 2) * t) y lam)

/-- band is inside `S(2^{k+1}t)`. -/
lemma band_subset_Sgt {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (t : ℝ) (k : ℕ) :
    band y lam t k ⊆ Sgt ((2 : ℝ) ^ (k + 1) * t) y lam := by
  intro B hB
  dsimp [band] at hB
  exact (Finset.mem_sdiff.mp hB).1

/-- `2 · 2^k = 2^{k+1}` as reals. -/
lemma pow_two_mul {k : ℕ} : (2 : ℝ) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
  rw [pow_succ]
  ring

/-- `2^{k+2} = 2^{k+1} · 2`. -/
lemma pow_two_succ {k : ℕ} : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]


/-- `bMass` is subadditive over binary unions. -/
lemma bMass_union_le {n : ℕ} (p : unitInterval) {T₁ T₂ : Finset (Finset (Fin n))} :
    bMass p (T₁ ∪ T₂) ≤ bMass p T₁ + bMass p T₂ := by
  classical
  have hd : Disjoint T₁ (T₂ \ T₁) := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    exact (Finset.mem_sdiff.mp hB2).2 hB1
  have hunion : T₁ ∪ (T₂ \ T₁) = T₁ ∪ T₂ := by
    ext B
    by_cases hB1 : B ∈ T₁ <;> simp [Finset.mem_sdiff, hB1]
  calc
    bMass p (T₁ ∪ T₂) = bMass p (T₁ ∪ (T₂ \ T₁)) := by rw [hunion]
    _ = bMass p T₁ + bMass p (T₂ \ T₁) := by
        dsimp [bMass]
        rw [Finset.sum_union hd]
    _ ≤ bMass p T₁ + bMass p T₂ := by
        have hmono : bMass p (T₂ \ T₁) ≤ bMass p T₂ :=
          bMass_mono p (by intro B hB; exact (Finset.mem_sdiff.mp hB).1)
        exact add_le_add_right hmono (bMass p T₁)

/-- `bMass` is subadditive over finite unions. -/
lemma bMass_biUnion_le {n : ℕ} (p : unitInterval) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (T : ι → Finset (Finset (Fin n))) :
    bMass p (s.biUnion T) ≤ ∑ i ∈ s, bMass p (T i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · dsimp [bMass]
    simp
  · intro a s' has ih
    calc
      bMass p ((insert a s').biUnion T) = bMass p (T a ∪ s'.biUnion T) := by
        rw [Finset.biUnion_insert]
      _ ≤ bMass p (T a) + bMass p (s'.biUnion T) := bMass_union_le p
      _ ≤ ∑ i ∈ insert a s', bMass p (T i) := by
        have h1 : bMass p (T a) + bMass p (s'.biUnion T) ≤ bMass p (T a) + (∑ i ∈ s', bMass p (T i)) := by
          exact add_le_add_right ih (bMass p (T a))
        have h2 : bMass p (T a) + (∑ i ∈ s', bMass p (T i)) = ∑ i ∈ insert a s', bMass p (T i) := by
          rw [Finset.sum_insert has]
        rwa [h2] at h1

/-- dyadic-band index: if `2t < r < 2^J t` (J ≥ 2) then `r` lies in the band
`(2^{k+1}t, 2^{k+2}t]` for some `k < J−1`. -/
lemma exists_band_idx {t r : ℝ} (ht : 0 < t) {J : ℕ} (hJ : 2 ≤ J)
    (hlo : 2 * t < r) (hhi : r < (2 : ℝ) ^ J * t) :
    ∃ k : ℕ, k < J - 1 ∧ (2 : ℝ) ^ (k + 1) * t < r ∧ r ≤ (2 : ℝ) ^ (k + 2) * t := by
  classical
  let p : ℕ → Prop := fun m => r ≤ (2 : ℝ) ^ (m + 2) * t
  have hex : ∃ m : ℕ, p m := by
    refine ⟨J, ?_⟩
    dsimp [p]
    have hmono : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 2) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hmul := mul_le_mul_of_nonneg_right hmono (le_of_lt ht)
    exact le_of_lt (lt_of_lt_of_le hhi hmul)
  let k : ℕ := Nat.find hex
  have hk_mem : r ≤ (2 : ℝ) ^ (k + 2) * t := Nat.find_spec hex
  have hk_min : ∀ m : ℕ, p m → k ≤ m := by
    intro m hm
    exact Nat.find_min' (p := p) (H := hex) hm
  have hk_low : (2 : ℝ) ^ (k + 1) * t < r := by
    by_cases hk0 : k = 0
    · have hkz : k = 0 := hk0
      calc
        (2 : ℝ) ^ (k + 1) * t = (2 : ℝ) ^ (0 + 1) * t := by rw [hkz]
        _ = 2 * t := by norm_num
        _ < r := hlo
    · have hk1 : 1 ≤ k := by omega
      have hnot : ¬ p (k - 1) := by
        intro hp
        have hle := hk_min (k - 1) hp
        have hle' : k ≤ k - 1 → False := by omega
        exact hle' hle
      have hnorm : (2 : ℝ) ^ ((k - 1) + 2) * t = (2 : ℝ) ^ (k + 1) * t := by
        congr 1
        have hkadd : (k - 1) + 2 = k + 1 := by omega
        rw [hkadd]
      have hnot' : ¬ r ≤ (2 : ℝ) ^ (k + 1) * t := by
        simpa [p, hnorm] using hnot
      exact lt_of_not_ge hnot'
  have hklt : k < J - 1 := by
    by_contra hnot
    have hJk : J - 1 ≤ k := Nat.le_of_not_gt hnot
    have hJk1 : J ≤ k + 1 := by omega
    have hmono : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJk1
    have hmul := mul_le_mul_of_nonneg_right hmono (le_of_lt ht)
    have hle : (2 : ℝ) ^ J * t ≤ (2 : ℝ) ^ (k + 1) * t := hmul
    have hc : (2 : ℝ) ^ J * t < r := lt_of_le_of_lt hle hk_low
    exact (not_lt_of_ge (le_of_lt hhi)) hc
  exact ⟨k, hklt, hk_low, hk_mem⟩


/-- **pointwise band decomposition**: the positive part `posMass(t)` is at most the
sum over dyadic bands (below level `J`) of the mass of the band part outside
`S̃(2^k t)`.  Requires that `S(2^J t)` is empty (all sums below `2^J t`). -/
lemma pospart_le_band_sum {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) (J : ℕ) (hJ : 2 ≤ J)
    (hbig : ∀ B : Finset (Fin n), |rSub y B - lam| < (2 : ℝ) ^ J * t)
    (E : Finset (Fin n)) :
    posMass p y lam E t ≤
      ∑ k ∈ Finset.range (J - 1),
        bMass p ((band y lam t k).filter
          (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
            (fun i : Fin n => roundYr y E i) lam B)) := by
  classical
  let coefs : Fin n → ℝ := fun i : Fin n => roundYr y E i
  let Ak : ℕ → Finset (Finset (Fin n)) := fun k =>
    (band y lam t k).filter (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t) coefs lam B)
  let Diff : Finset (Finset (Fin n)) := (Sgt (2 * t) y lam).filter
      (fun B : Finset (Fin n) => ¬ SgtMem t coefs lam B)
  have hset : Diff ⊆ (Finset.range (J - 1)).biUnion Ak := by
    intro B hB
    rw [Finset.mem_biUnion]
    have hD1 : B ∈ Sgt (2 * t) y lam := (Finset.mem_filter.mp hB).1
    have hD2 : ¬ SgtMem t coefs lam B := (Finset.mem_filter.mp hB).2
    have hlo : 2 * t < |rSub y B - lam| := by
      dsimp [Sgt] at hD1
      exact (Finset.mem_filter.mp hD1).2
    have hhi : |rSub y B - lam| < (2 : ℝ) ^ J * t := hbig B
    rcases exists_band_idx (t := t) (r := |rSub y B - lam|) ht hJ hlo hhi with ⟨k, hklt, hklow, hkmem⟩
    refine ⟨k, Finset.mem_range.mpr hklt, ?_⟩
    dsimp [Ak]
    rw [Finset.mem_filter]
    constructor
    · dsimp [band]
      rw [Finset.mem_sdiff]
      constructor
      · dsimp [Sgt]
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hD1).1, hklow⟩
      · intro hB2
        dsimp [Sgt] at hB2
        have hBig2 : (2 : ℝ) ^ (k + 2) * t < |rSub y B - lam| := (Finset.mem_filter.mp hB2).2
        exact (not_lt_of_ge hkmem) hBig2
    · have hle_t : |rSub coefs B - lam| ≤ t := by
        dsimp [SgtMem] at hD2
        exact le_of_not_gt hD2
      have ht2 : t ≤ (2 : ℝ) ^ k * t := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (n := k) (by norm_num)
        have hm := mul_le_mul_of_nonneg_right h2 (le_of_lt ht)
        simpa using hm
      intro hS
      dsimp [SgtMem] at hS
      have hcon : |rSub coefs B - lam| ≤ (2 : ℝ) ^ k * t := le_trans hle_t ht2
      exact (not_lt_of_ge hcon) hS
  have hb1 : bMass p Diff ≤ bMass p ((Finset.range (J - 1)).biUnion Ak) := bMass_mono p hset
  have hb2 : bMass p ((Finset.range (J - 1)).biUnion Ak) ≤ ∑ k ∈ Finset.range (J - 1), bMass p (Ak k) :=
    bMass_biUnion_le p (Finset.range (J - 1)) Ak
  have hfinal : posMass p y lam E t ≤ ∑ k ∈ Finset.range (J - 1), bMass p (Ak k) := by
    calc
      posMass p y lam E t ≤ bMass p Diff := by
        exact rounded_pospart_le p y lam ht E
      _ ≤ bMass p ((Finset.range (J - 1)).biUnion Ak) := bMass_mono p hset
      _ ≤ ∑ k ∈ Finset.range (J - 1), bMass p (Ak k) := bMass_biUnion_le p (Finset.range (J - 1)) Ak
  simpa [Ak, coefs] using hfinal


/-- band lies in the slab of radius `2^{k+2}t` (for `t > 0`). -/
lemma band_mem_slab {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (t : ℝ) (k : ℕ) (B : Finset (Fin n))
    (hB : B ∈ band y lam t k) : B ∈ slabB y lam ((2 : ℝ) ^ (k + 2) * t) := by
  classical
  dsimp [band] at hB
  have h1 : B ∈ Sgt ((2 : ℝ) ^ (k + 1) * t) y lam := (Finset.mem_sdiff.mp hB).1
  have h2 : B ∉ Sgt ((2 : ℝ) ^ (k + 2) * t) y lam := (Finset.mem_sdiff.mp hB).2
  have hpow : B ∈ (Finset.univ : Finset (Fin n)).powerset := by
    dsimp [Sgt] at h1
    exact (Finset.mem_filter.mp h1).1
  have hnot : ¬ SgtMem ((2 : ℝ) ^ (k + 2) * t) y lam B := by
    intro hS
    apply h2
    dsimp [Sgt]
    rw [Finset.mem_filter]
    exact ⟨hpow, hS⟩
  have hbig : |rSub y B - lam| ≤ (2 : ℝ) ^ (k + 2) * t := by
    dsimp [SgtMem] at hnot
    exact le_of_not_gt hnot
  dsimp [slabB]
  rw [Finset.mem_filter]
  exact ⟨hpow, hbig⟩

/-- band mass is at most the slab mass at radius `2^{k+2}t`. -/
lemma band_mass_le_slab {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ) (t : ℝ) (k : ℕ) :
    bMass p (band y lam t k) ≤ bMass p (slabB y lam ((2 : ℝ) ^ (k + 2) * t)) := by
  exact bMass_mono p (by intro B hB; exact band_mem_slab y lam t k B hB)

/-- `2 · 2^k · t = 2^{k+1} · t`. -/
lemma two_mul_pow_t {t : ℝ} (k : ℕ) : 2 * ((2 : ℝ) ^ k * t) = (2 : ℝ) ^ (k + 1) * t := by
  rw [pow_succ]
  ring

/-- band is inside `S(2 · 2^k t)`. -/
lemma band_subset_Sgt_two {n : ℕ} (y : Fin n → ℝ) (lam : ℝ) (t : ℝ) (k : ℕ) :
    band y lam t k ⊆ Sgt (2 * ((2 : ℝ) ^ k * t)) y lam := by
  intro B hB
  have h1 : B ∈ Sgt ((2 : ℝ) ^ (k + 1) * t) y lam := band_subset_Sgt y lam t k hB
  rwa [two_mul_pow_t]

/-- geometric partial sum of `(1/2)^k`. -/
lemma geom_half_le_two {M : ℕ} : (∑ k ∈ Finset.range M, ((1 / 2 : ℝ) ^ k)) ≤ 2 := by
  classical
  have hgeo := geom_sum_eq (x := (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≠ 1) M
  have hval : ((1 / 2 : ℝ) ^ M - 1) / ((1 / 2 : ℝ) - 1) = 2 * (1 - (1 / 2 : ℝ) ^ M) := by
    field_simp
    ring
  calc
    (∑ k ∈ Finset.range M, ((1 / 2 : ℝ) ^ k)) = ((1 / 2 : ℝ) ^ M - 1) / ((1 / 2 : ℝ) - 1) := hgeo
    _ = 2 * (1 - (1 / 2 : ℝ) ^ M) := hval
    _ ≤ 2 * 1 := by
            have hle1 : 1 - (1 / 2 : ℝ) ^ M ≤ 1 := by
              have hnon : 0 ≤ (1 / 2 : ℝ) ^ M := pow_nonneg (by norm_num) M
              nlinarith
            exact mul_le_mul_of_nonneg_left hle1 (by norm_num)
    _ = 2 := by ring

/-- per-band expectation bound via the subset telescope. -/
lemma band_expect_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p ((band y lam t k).filter
          (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t) (fun i : Fin n => roundYr y E i) lam B)))) ≤
      (n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2) * bMass p (band y lam t k) := by
  classical
  have hw0 : 0 < (2 : ℝ) ^ k * t := mul_pos (pow_pos (by norm_num) k) ht
  exact rounded_mass_subset_le p y lam (t := (2 : ℝ) ^ k * t) hw0 (F := band y lam t k)
    (band_subset_Sgt_two y lam t k)


/-- any positive threshold is eventually below `2^J · t`. -/
lemma exists_two_pow_mul_gt {t : ℝ} (ht0 : 0 < t) (c : ℝ) :
    ∃ J : ℕ, c < (2 : ℝ) ^ J * t := by
  have hten : Filter.Tendsto (fun J : ℕ => (2 : ℝ) ^ J) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ J : ℕ in Filter.atTop, c / t < (2 : ℝ) ^ J :=
    hten (Filter.eventually_gt_atTop (c / t))
  rcases hev.exists with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  have hm := (div_lt_iff₀ ht0).1 hJ
  exact hm

/-- per-band coefficient × slab bound equals the `(nL/t)·(1/2)^k` term. -/
lemma band_term_eq {n : ℕ} {L t : ℝ} (hL0 : 0 < L) (ht0 : 0 < t) (k : ℕ) :
    (n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2) * (L * ((2 : ℝ) ^ (k + 2) * t)) =
      (n : ℝ) * L / t * (1 / 2 : ℝ) ^ k := by
  have h2nz : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have ht0n : t ≠ 0 := ne_of_gt ht0
  have hL0n : L ≠ 0 := ne_of_gt hL0
  field_simp [h2nz, ht0n, hL0n]
  have hk2 : (2 : ℝ) ^ (k * 2) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
    rw [show k * 2 = k + k by omega, pow_add]
  have hmul : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hpowadd' : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * 4 := by
    rw [pow_add]
    norm_num
  have hpow2 : ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ (k * 2) := by rw [pow_mul]
  rw [hpowadd', hpow2, hk2]
  calc
    ↑n * (2 ^ k * 4) = ↑n * 4 * (2 : ℝ) ^ k := by ring
    _ = (↑n * 4 * (2 : ℝ) ^ k) * 1 := by rw [mul_one]
    _ = (↑n * 4 * (2 : ℝ) ^ k) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by rw [hmul]
    _ = ↑n * 4 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) * (1 / 2 : ℝ) ^ k := by ring

/-- **E1 band expectation bound**: `E_ξ[pos(t)] ≤ 2Ln/t` (valid for all `t ≥ √n`,
L-arbitrary).  This is the input that makes the per-level Markov bound L-free. -/
lemma dyadic_pospart_E_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    {t : ℝ} (ht0 : 0 < t) (hts : Real.sqrt (n : ℝ) ≤ t) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t) ≤
      2 * L * (n : ℝ) / t := by
  classical
  let D : ℝ := ynAbs y + |lam|
  have hex : ∃ J0 : ℕ, D < (2 : ℝ) ^ J0 * t := exists_two_pow_mul_gt ht0 D
  let J0 : ℕ := Nat.find hex
  let J : ℕ := max 2 J0
  have hJge : 2 ≤ J := by dsimp [J]; exact le_max_left (a := 2) (b := J0)
  have hJ0leJ : J0 ≤ J := by dsimp [J]; exact le_max_right (a := 2) (b := J0)
  have hJ0spec : D < (2 : ℝ) ^ J0 * t := Nat.find_spec hex
  have hJbig : ∀ B : Finset (Fin n), |rSub y B - lam| < (2 : ℝ) ^ J * t := by
    intro B
    have hB1 : |rSub y B - lam| ≤ D := by dsimp [D]; exact rSub_abs_le_ynAbs y lam B
    have hmono : (2 : ℝ) ^ J0 * t ≤ (2 : ℝ) ^ J * t := by
      have hp : (2 : ℝ) ^ J0 ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ0leJ
      exact mul_le_mul_of_nonneg_right hp (le_of_lt ht0)
    exact lt_of_lt_of_le (lt_of_le_of_lt hB1 hJ0spec) hmono
  -- (1) per-E pointwise then sum:
  have hstep1 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t) ≤
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ k ∈ Finset.range (J - 1),
          bMass p ((band y lam t k).filter
            (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
              (fun i : Fin n => roundYr y E i) lam B))) := by
    apply Finset.sum_le_sum
    intro E hE
    exact mul_le_mul_of_nonneg_left (pospart_le_band_sum p y lam ht0 J hJge hJbig E) (wR_nonneg y E)
  -- (2) swap:
  have hstep2 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (∑ k ∈ Finset.range (J - 1),
          bMass p ((band y lam t k).filter
            (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
              (fun i : Fin n => roundYr y E i) lam B)))) =
      ∑ k ∈ Finset.range (J - 1),
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (bMass p ((band y lam t k).filter
            (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
              (fun i : Fin n => roundYr y E i) lam B)))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  -- (3) per-k via rounded_mass_subset_le:
  have hstep3 : (∑ k ∈ Finset.range (J - 1),
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (bMass p ((band y lam t k).filter
            (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
              (fun i : Fin n => roundYr y E i) lam B))))) ≤
      ∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * bMass p (band y lam t k) := by
    apply Finset.sum_le_sum
    intro k hk
    exact band_expect_le p y lam ht0 k
  -- (4) per-k slab & hsb:
  have hstep4 : (∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * bMass p (band y lam t k)) ≤
      ∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * (L * ((2 : ℝ) ^ (k + 2) * t)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hb1 : bMass p (band y lam t k) ≤ bMass p (slabB y lam ((2 : ℝ) ^ (k + 2) * t)) :=
      band_mass_le_slab p y lam t k
    have hb2 : bMass p (slabB y lam ((2 : ℝ) ^ (k + 2) * t)) ≤ L * ((2 : ℝ) ^ (k + 2) * t) := by
      have hle : Real.sqrt (n : ℝ) ≤ (2 : ℝ) ^ (k + 2) * t := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := one_le_pow₀ (n := k + 2) (by norm_num)
        have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt ht0)
        -- 1·t ≤ 2^{k+2}·t and √n ≤ t ≤ ...
        have hchain : Real.sqrt (n : ℝ) ≤ t := hts
        have htle : t ≤ (2 : ℝ) ^ (k + 2) * t := by simpa using hm
        exact le_trans hchain htle
      exact hsb ((2 : ℝ) ^ (k + 2) * t) hle
    have hc0 : 0 ≤ (n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2) := by
      have h1 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have h2 : 0 < 4 * ((2 : ℝ) ^ k * t) ^ 2 := by positivity
      exact div_nonneg h1 h2.le
    exact mul_le_mul_of_nonneg_left (le_trans hb1 hb2) hc0
  -- (5)+(6) termwise ≤ and geometric:
  have hstep5 : (∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * (L * ((2 : ℝ) ^ (k + 2) * t))) ≤
      (n : ℝ) * L / t * (∑ k ∈ Finset.range (J - 1), ((1 / 2 : ℝ) ^ k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact le_of_eq (band_term_eq (n := n) hL0 ht0 k)
  have hstep6 : (n : ℝ) * L / t * (∑ k ∈ Finset.range (J - 1), ((1 / 2 : ℝ) ^ k)) ≤ 2 * L * (n : ℝ) / t := by
    have hg := geom_half_le_two (M := J - 1)
    have hc : 0 ≤ (n : ℝ) * L / t := by
      have h1 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have h2 : 0 < L := hL0
      have h3 : 0 < t := ht0
      positivity
    have hm := mul_le_mul_of_nonneg_left hg hc
    -- (nL/t)·2 ≤ 2·nL/t: ring-normalize:
    have hring : (n : ℝ) * L / t * 2 = 2 * L * (n : ℝ) / t := by ring
    rwa [hring] at hm
  -- assemble:
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t)
        ≤ ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (∑ k ∈ Finset.range (J - 1),
              bMass p ((band y lam t k).filter
                (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
                  (fun i : Fin n => roundYr y E i) lam B))) := hstep1
    _ = ∑ k ∈ Finset.range (J - 1),
          (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (bMass p ((band y lam t k).filter
              (fun B : Finset (Fin n) => ¬ SgtMem ((2 : ℝ) ^ k * t)
                (fun i : Fin n => roundYr y E i) lam B)))) := hstep2
    _ ≤ ∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * bMass p (band y lam t k) := hstep3
    _ ≤ ∑ k ∈ Finset.range (J - 1), ((n : ℝ) / (4 * ((2 : ℝ) ^ k * t) ^ 2)) * (L * ((2 : ℝ) ^ (k + 2) * t)) := hstep4
    _ ≤ (n : ℝ) * L / t * (∑ k ∈ Finset.range (J - 1), ((1 / 2 : ℝ) ^ k)) := hstep5
    _ ≤ 2 * L * (n : ℝ) / t := hstep6



/-- geometric partial sum of `(1/4)^k`. -/
lemma geom4_sum_le {K : ℕ} : (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) ^ k)) ≤ 4 / 3 := by
  classical
  have hgeo := geom_sum_eq (x := (1 / 4 : ℝ)) (by norm_num : (1 / 4 : ℝ) ≠ 1) K
  have hval : ((1 / 4 : ℝ) ^ K - 1) / ((1 / 4 : ℝ) - 1) = (4 / 3) * (1 - (1 / 4 : ℝ) ^ K) := by
    field_simp
    ring
  calc
    (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) ^ k)) = ((1 / 4 : ℝ) ^ K - 1) / ((1 / 4 : ℝ) - 1) := hgeo
    _ = (4 / 3) * (1 - (1 / 4 : ℝ) ^ K) := hval
    _ ≤ (4 / 3) * 1 := by
            have hpos : (0 : ℝ) ≤ 4 / 3 := by norm_num
            have hle1 : 1 - (1 / 4 : ℝ) ^ K ≤ 1 := by
              have hnon : 0 ≤ (1 / 4 : ℝ) ^ K := pow_nonneg (by norm_num) K
              nlinarith
            exact mul_le_mul_of_nonneg_left hle1 hpos
    _ = 4 / 3 := by ring

/-- **L-free per-level bound**: `P(pos(t_k) ≥ 8L t_k) ≤ (1/4)·(1/4)^k`
(no `L ≥ 1` hypothesis — this is what the small-`L` magic-vector application needs). -/
lemma level_bad_prob_free {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    (k : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if 8 * L * level n k < posMass p y lam E (level n k) then 1 else 0)) ≤
      (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k) := by
  classical
  let t : ℝ := level n k
  have ht0 : 0 < t := by dsimp [t]; exact level_pos hn k
  have htS : Real.sqrt (n : ℝ) ≤ t := by dsimp [t]; exact level_sq_ge k
  have hE : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t) ≤
      2 * L * (n : ℝ) / t := dyadic_pospart_E_le p y lam hL0 hn hsb ht0 htS
  have hMarkov : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
      wR y E * (if 8 * L * t < posMass p y lam E t then 1 else 0)) ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t) / (8 * L * t) := by
    exact wR_markov y (fun E : Finset (Fin n) => posMass p y lam E t) (a := 8 * L * t)
      (by positivity) (by intro E; exact posMass_nonneg p y lam E t)
  have hposden : 0 ≤ 8 * L * t := by positivity
  have hprod : (2 * L * (n : ℝ) / t) / (8 * L * t) = (n : ℝ) / (4 * t ^ 2) := by
    have hLne : L ≠ 0 := ne_of_gt hL0
    have htne : t ≠ 0 := ne_of_gt ht0
    field_simp [hLne, htne]
    ring
  have hEq : (n : ℝ) / (4 * t ^ 2) = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k) := by
    dsimp [t, level]
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
    have h2nz : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    field_simp [hsqrt, hnz, h2nz]
    have hsq2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by exact_mod_cast (Nat.zero_le n))
    rw [hsq2]
    have hmul : ((2 : ℝ) ^ k) ^ 2 * (1 / 4 : ℝ) ^ k = 1 := by
      rw [← pow_mul]
      rw [show k * 2 = 2 * k by omega]
      rw [pow_mul]
      norm_num
      rw [← mul_pow]
      norm_num
    nlinarith [hmul]
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if 8 * L * level n k < posMass p y lam E (level n k) then 1 else 0))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if 8 * L * t < posMass p y lam E t then 1 else 0)) := by
            rfl
    _ ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * posMass p y lam E t) / (8 * L * t) := hMarkov
    _ ≤ (2 * L * (n : ℝ) / t) / (8 * L * t) := by
            exact div_le_div_of_nonneg_right hE hposden
    _ = (n : ℝ) / (4 * t ^ 2) := hprod
    _ = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k) := hEq


/-- the truncated bad event for E1 has rounding mass at most `1/3`
(no `L ≥ 1` needed — L-free per-level bounds). -/
lemma e1K_bad_free_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    (K : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧
            8 * L * level n k < posMass p y lam E (level n k) then 1 else 0)) ≤
      (1 : ℝ) / 3 := by
  classical
  let Bad : ℕ → Finset (Fin n) → Prop := fun k E =>
    8 * L * level n k < posMass p y lam E (level n k)
  have hpt : ∀ E : Finset (Fin n),
      (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) ≤
        ∑ k ∈ Finset.range K, (if Bad k E then (1 : ℝ) else 0) := by
    intro E
    by_cases hE : ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E
    · have h1 : (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) = 1 := by
        rw [if_pos hE]
      rw [h1]
      rcases hE with ⟨k, hk, hbad⟩
      have hnonneg : ∀ j : ℕ, j ∈ Finset.range K → 0 ≤ (if Bad j E then (1 : ℝ) else 0) := by
        intro j hj
        by_cases hj0 : Bad j E <;> simp [hj0]
      have h1le := Finset.single_le_sum (s := Finset.range K) hnonneg hk
      have hfk : (if Bad k E then (1 : ℝ) else 0) = 1 := by
        simp [hbad]
      rwa [hfk] at h1le
    · have h1 : (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then (1 : ℝ) else 0) = 0 := by
        rw [if_neg hE]
      rw [h1]
      exact Finset.sum_nonneg (by intro j hj; by_cases hj0 : Bad j E <;> simp [hj0])
  -- sum level bounds
  have hlevel : ∀ k : ℕ, k ∈ Finset.range K →
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if Bad k E then 1 else 0)) ≤
        (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k) := by
    intro k hk
    exact level_bad_prob_free p y lam hL0 hn hsb k
  have hsum_le : (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k))) ≤ (1 : ℝ) / 3 := by
    calc
      (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k)))
          = (1 / 4 : ℝ) * (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) ^ k)) := by
            rw [Finset.mul_sum]
      _ ≤ (1 / 4 : ℝ) * (4 / 3) := by
            have hpos : 0 ≤ (1 / 4 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left geom4_sum_le hpos
      _ = 1 / 3 := by norm_num
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (∑ k ∈ Finset.range K, (if Bad k E then 1 else 0))) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ = ∑ k ∈ Finset.range K,
          (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if Bad k E then 1 else 0)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro E hE
            rw [Finset.mul_sum]
    _ ≤ (∑ k ∈ Finset.range K, ((1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k))) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hlevel k hk
    _ ≤ (1 : ℝ) / 3 := hsum_le

/-- the E1K good event (no bad level below `K`) has rounding mass at least
`1 − 1/3 = 2/3` — for EVERY `L > 0` (no `L ≥ 1`). -/
lemma e1K_good_free_mass {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    (K : ℕ) :
    (1 : ℝ) - 1 / 3 ≤
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∀ k : ℕ, k ∈ Finset.range K →
            ¬ (8 * L * level n k < posMass p y lam E (level n k)) then 1 else 0)) := by
  classical
  let Bad : ℕ → Finset (Fin n) → Prop := fun k E =>
    8 * L * level n k < posMass p y lam E (level n k)
  have hbad := e1K_bad_free_le p y lam hL0 hn hsb K
  have hpt : ∀ E : Finset (Fin n),
      (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then (1 : ℝ) else 0) =
        (1 : ℝ) - (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0) := by
    intro E
    by_cases hE : ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E
    · have hnot : ¬ ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E := by
        rcases hE with ⟨k, hk, hbadk⟩
        intro h
        exact h k hk hbadk
      rw [if_pos hE]
      rw [if_neg hnot]
      norm_num
    · have hfor : ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E := by
        intro k hk hbadk
        exact hE ⟨k, hk, hbadk⟩
      rw [if_neg hE]
      rw [if_pos hfor]
      norm_num
  calc
    (1 : ℝ) - 1 / 3 ≤ (1 : ℝ) -
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
            linarith [hbad]
    _ = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then 1 else 0)) := by
            calc
              (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                  wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0))
                  = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) -
                      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                        wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
                        rw [sum_wR_eq_one]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      (wR y E - wR y E * (if ∃ k : ℕ, k ∈ Finset.range K ∧ Bad k E then 1 else 0)) := by
                        rw [← Finset.sum_sub_distrib]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      wR y E * (if ∀ k : ℕ, k ∈ Finset.range K → ¬ Bad k E then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro E hE
                        rw [hpt E]
                        ring


/-! ## `K_lv` — the E1 truncation index and the sealed E1 event family

`K_lv hn L` is the least level index with `t_K ≥ 1/(10L)`.  On the event
`E1K_good` (good at all dyadic levels below `K_lv`) the rounded vector has
small-ball `μ_t(ỹ^E) ≤ 20Lt` for every `t ≥ √n` (any `L > 0`), and the
rounding mass of `E1K_good` is at least `2/3`.  These two facts (mass, and the
pointwise small-ball property on every member) are exactly what the E2/E3
intersection argument feeds on. -/

/-- the least level index with `t_K ≥ 1/(10L)` (i.e. `1/(10L) < t_K`). -/
noncomputable def K_lv {n : ℕ} (hn : 1 ≤ n) (L : ℝ) : ℕ :=
  Nat.find (exists_level_gt hn (1 / (10 * L)))

/-- `K_lv` reaches `1/(10L)`: `1/(10L) ≤ t_{K_lv}`. -/
lemma K_lv_spec {n : ℕ} (hn : 1 ≤ n) (L : ℝ) :
    1 / (10 * L) ≤ level n (K_lv hn L) := by
  classical
  have h := Nat.find_spec (exists_level_gt hn (1 / (10 * L)))
  exact le_of_lt h

/-- `K_lv` is the *least* level index reaching `1/(10L)`. -/
lemma K_lv_min {n : ℕ} (hn : 1 ≤ n) (L : ℝ) :
    ∀ m : ℕ, 1 / (10 * L) < level n m → K_lv hn L ≤ m := by
  classical
  intro m hm
  exact Nat.find_min' (p := fun k : ℕ => 1 / (10 * L) < level n k)
    (H := exists_level_gt hn (1 / (10 * L))) hm

/-- the E1K good event at `K := K_lv`: no bad dyadic level below `K_lv`. -/
noncomputable def E1K_good {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    (L : ℝ) (hn : 1 ≤ n) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter
    (fun E : Finset (Fin n) => ∀ k : ℕ, k ∈ Finset.range (K_lv hn L) →
      ¬ (8 * L * level n k < posMass p y lam E (level n k)))

/-- membership in `E1K_good`. -/
lemma E1K_good_mem {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    (L : ℝ) (hn : 1 ≤ n) (E : Finset (Fin n)) :
    E ∈ E1K_good p y lam L hn ↔
      E ∈ ((Finset.univ : Finset (Fin n)).powerset) ∧
      ∀ k : ℕ, k ∈ Finset.range (K_lv hn L) →
        ¬ (8 * L * level n k < posMass p y lam E (level n k)) := by
  classical
  dsimp [E1K_good]
  rw [Finset.mem_filter]

/-- **E1 mass**: the rounding mass of `E1K_good` is at least `2/3` (any `L > 0`). -/
lemma E1K_mass_ge {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s) :
    (2 : ℝ) / 3 ≤ ∑ E ∈ E1K_good p y lam L hn, wR y E := by
  classical
  have h := e1K_good_free_mass p y lam hL0 hn hsb (K_lv hn L)
  -- h : 1 − 1/3 ≤ Σ_E wR·1[∀k ∈ range(K_lv): ¬ bad]
  have hconv : (∑ E ∈ E1K_good p y lam L hn, wR y E) =
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if ∀ k : ℕ, k ∈ Finset.range (K_lv hn L) →
            ¬ (8 * L * level n k < posMass p y lam E (level n k)) then 1 else 0)) := by
    dsimp [E1K_good]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases hg : ∀ k : ℕ, k ∈ Finset.range (K_lv hn L) →
        ¬ (8 * L * level n k < posMass p y lam E (level n k)) <;> simp [hg]
  have h2 : (1 : ℝ) - 1 / 3 = (2 : ℝ) / 3 := by norm_num
  rwa [hconv, ← h2]

/-- **E1 small-ball property**: on every `E ∈ E1K_good` the rounded vector
satisfies `μ_t(ỹ^E) ≤ 20Lt` for all `t ≥ √n`. -/
lemma E1K_small_ball {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    {E : Finset (Fin n)} (hE : E ∈ E1K_good p y lam L hn) :
    ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 20 * L * t := by
  classical
  have hgood : E ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
      (fun E => ∀ k : ℕ, k ∈ Finset.range (K_lv hn L) →
        ¬ (8 * L * level n k < posMass p y lam E (level n k))) := by
    simpa [E1K_good] using hE
  exact e1K_good_small_ball p y lam hL0 hn hsb (K_lv_spec hn L) hgood


/-! ## E2 — cf-preservation (paper lines ~1720–1780)

Fix a center `lamP` (the E2 argument; in the magic-vector proof it will be chosen
with `A := mass of y's √n-slab at lamP` comparable to `cf(y, √n)`).  Let
`A E`-independent = `bMass(slabB y lamP √n)`.  For `B` in that slab, the rounding
of `Σ_B y` moves by at most a Chebyshev tail at radius `√n`:
`P_ξ(B ∉ S̃(2√n))`-complement-style `P_ξ(B ∈ S̃_{lamP}(2√n)) ≤ 1/4`.  Hence
`E[X] ≤ (1/4)A` where `X_E := mass of {B ∈ slab(√n): B ∈ S̃_{lamP}(2√n,ỹ^E)}`, and
Markov gives the E2-good event (mass ≥ 2/3) on which the remaining slab mass
`A − X_E ≥ (3/4)A` is carried by `ỹ`'s `2√n`-slab at `lamP`. -/

/-- per-B Chebyshev for E2: for `B` in `y`'s `√n`-slab at `lamP`, the rounding
mass of `{E : B ∈ S̃_{lamP}(2√n,ỹ^E)}` is at most `1/4`. -/
lemma E2_perB_tail_le {n : ℕ} (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n)
    {B : Finset (Fin n)} (hB : B ∈ slabB y lamP (Real.sqrt (n : ℝ))) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
          then 1 else 0)) ≤ (1 : ℝ) / 4 := by
  classical
  have hsqrt0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hpt : ∀ E : Finset (Fin n),
      (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B then (1 : ℝ) else 0) ≤
        (if Real.sqrt (n : ℝ) < |∑ i ∈ B, (y i - roundYr y E i)| then (1 : ℝ) else 0) := by
    intro E
    by_cases hS : SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
    · have h1 : (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B then (1 : ℝ) else 0) = 1 := by
        rw [if_pos hS]
      rw [h1]
      have hsub : |rSub y B - lamP| ≤ Real.sqrt (n : ℝ) := by
        dsimp [slabB] at hB
        exact (Finset.mem_filter.mp hB).2
      have hBig : 2 * Real.sqrt (n : ℝ) < |rSub (fun i : Fin n => roundYr y E i) B - lamP| := by
        dsimp [SgtMem] at hS
        exact hS
      have htri : Real.sqrt (n : ℝ) < |∑ i ∈ B, (y i - roundYr y E i)| := by
        have htri0 : |rSub (fun i : Fin n => roundYr y E i) B - lamP| ≤
            |rSub y B - lamP| + |∑ i ∈ B, (y i - roundYr y E i)| := by
          have h1 := abs_add_le (rSub (fun i : Fin n => roundYr y E i) B - rSub y B) (rSub y B - lamP)
          have hsum : (rSub (fun i : Fin n => roundYr y E i) B - rSub y B) + (rSub y B - lamP) =
              rSub (fun i : Fin n => roundYr y E i) B - lamP := by ring
          have h2 : |rSub (fun i : Fin n => roundYr y E i) B - lamP| ≤
              |rSub (fun i : Fin n => roundYr y E i) B - rSub y B| + |rSub y B - lamP| := by
            simpa [hsum] using h1
          have hrew : |rSub (fun i : Fin n => roundYr y E i) B - rSub y B| =
              |∑ i ∈ B, (y i - roundYr y E i)| := by
            dsimp [rSub]
            rw [abs_sub_comm]
            congr 1
            rw [Finset.sum_sub_distrib]
          simpa [hrew, add_comm] using h2
        nlinarith [htri0, hsub, hBig]
      have hw : Real.sqrt (n : ℝ) < |∑ i ∈ B, (y i - roundYr y E i)| := htri
      rw [if_pos hw]
    · have h1 : (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B then (1 : ℝ) else 0) = 0 := by
        rw [if_neg hS]
      rw [h1]
      by_cases hw : Real.sqrt (n : ℝ) < |∑ i ∈ B, (y i - roundYr y E i)|
      · rw [if_pos hw]
        norm_num
      · rw [if_neg hw]
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
          then 1 else 0))
        ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if Real.sqrt (n : ℝ) < |∑ i ∈ B, (y i - roundYr y E i)| then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro E hE
            exact mul_le_mul_of_nonneg_left (hpt E) (wR_nonneg y E)
    _ ≤ (n : ℝ) / (4 * (Real.sqrt (n : ℝ)) ^ 2) := rounding_tail_le y B hsqrt0
    _ = 1 / 4 := by
            have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
              Real.sq_sqrt (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ (n : ℝ))
            rw [hsq]
            field_simp


/-- **E2 expectation bound**: `E[X] ≤ (1/4)·A` where `A` is the mass of `y`'s
`√n`-slab at `lamP` and `X_E` the mass of its part lost by `ỹ^E` at scale `2√n`. -/
lemma E2_expect_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
          (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
            (fun i : Fin n => roundYr y E i) lamP B)))) ≤
      (1 / 4 : ℝ) * bMass p (slabB y lamP (Real.sqrt (n : ℝ))) := by
  classical
  let D : Finset (Finset (Fin n)) := slabB y lamP (Real.sqrt (n : ℝ))
  let P : Finset (Fin n) → Finset (Fin n) → Prop :=
    fun E B => SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
  have hS1 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B)))) =
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro E hE
    dsimp [bMass]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases h : P E B <;> simp [h]
  have hS2 : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) := by
    rw [Finset.sum_comm]
  have hS3 : (∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * wB n p B * (if P E B then 1 else 0)) =
      (∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    ring
  have hS4 : (∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if P E B then 1 else 0))) ≤ ∑ B ∈ D, wB n p B * (1 / 4) := by
    apply Finset.sum_le_sum
    intro B hB
    exact mul_le_mul_of_nonneg_left (E2_perB_tail_le y lamP hn (B := B) (by simpa [D] using hB))
      (wB_nonneg n p B)
  have hS5 : (∑ B ∈ D, wB n p B * (1 / 4)) = (1 / 4 : ℝ) * bMass p D := by
    dsimp [bMass]
    rw [← Finset.sum_mul]
    ring
  have hmain : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B)))) ≤ (1 / 4 : ℝ) * bMass p D := by
    calc
      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (bMass p (D.filter (fun B : Finset (Fin n) => P E B))))
          = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
              ∑ B ∈ D, wR y E * wB n p B * (if P E B then 1 else 0) := hS1
      _ = ∑ B ∈ D, ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * wB n p B * (if P E B then 1 else 0) := hS2
      _ = ∑ B ∈ D, wB n p B * (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if P E B then 1 else 0)) := hS3
      _ ≤ ∑ B ∈ D, wB n p B * (1 / 4) := hS4
      _ = (1 / 4 : ℝ) * bMass p D := hS5
  simpa [D] using hmain

/-- the E2 good event at center `lamP`: the mass lost by `ỹ^E` at scale `2√n`
(still within `y`'s `√n`-slab) is at most `(3/4)·A`. -/
noncomputable def E2_good {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ)
    (hn : 1 ≤ n) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter
    (fun E : Finset (Fin n) =>
      bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
        (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
          (fun i : Fin n => roundYr y E i) lamP B)) ≤
        (3 / 4 : ℝ) * bMass p (slabB y lamP (Real.sqrt (n : ℝ))))

/-- membership in `E2_good`. -/
lemma E2_good_mem {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n)
    (E : Finset (Fin n)) :
    E ∈ E2_good p y lamP hn ↔
      E ∈ ((Finset.univ : Finset (Fin n)).powerset) ∧
      bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
        (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
          (fun i : Fin n => roundYr y E i) lamP B)) ≤
        (3 / 4 : ℝ) * bMass p (slabB y lamP (Real.sqrt (n : ℝ))) := by
  classical
  dsimp [E2_good]
  rw [Finset.mem_filter]

/-- `X_E ≤ A` always (the lost part is inside the slab). -/
lemma E2_X_le_A {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n)
    (E : Finset (Fin n)) :
    bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
        (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
          (fun i : Fin n => roundYr y E i) lamP B)) ≤
      bMass p (slabB y lamP (Real.sqrt (n : ℝ))) := by
  classical
  exact bMass_mono p (Finset.filter_subset _ _)

/-- **E2 mass**: the rounding mass of `E2_good` is at least `2/3`. -/
lemma E2_mass_ge {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n) :
    (2 : ℝ) / 3 ≤ ∑ E ∈ E2_good p y lamP hn, wR y E := by
  classical
  let A : ℝ := bMass p (slabB y lamP (Real.sqrt (n : ℝ)))
  let X : Finset (Fin n) → ℝ := fun E =>
    bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
      (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
        (fun i : Fin n => roundYr y E i) lamP B))
  have hA0 : 0 ≤ A := by dsimp [A]; exact bMass_nonneg p _
  by_cases hAeq : A = 0
  · -- everything is good
    have hAll : ∀ E : Finset (Fin n), E ∈ (Finset.univ : Finset (Fin n)).powerset →
        X E ≤ (3 / 4 : ℝ) * A := by
      intro E hE
      have hx0 := E2_X_le_A p y lamP hn E
      have hAeq' : bMass p (slabB y lamP (Real.sqrt (n : ℝ))) = 0 := by
        simpa [A] using hAeq
      have hx1 : bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
          (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
            (fun i : Fin n => roundYr y E i) lamP B)) ≤ (3 / 4 : ℝ) * A := by
        rw [hAeq]
        have hx0' : bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
            (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
              (fun i : Fin n => roundYr y E i) lamP B)) ≤ 0 := by
          rwa [hAeq'] at hx0
        norm_num at hx0' ⊢
        exact hx0'
      dsimp [X]
      exact hx1
    have hsum : (∑ E ∈ E2_good p y lamP hn, wR y E) = 1 := by
      -- E2_good = whole powerset: mass = 1
      have hset : E2_good p y lamP hn = (Finset.univ : Finset (Fin n)).powerset := by
        apply Finset.Subset.antisymm
        · intro E hE
          dsimp [E2_good] at hE
          exact (Finset.mem_filter.mp hE).1
        · intro E hE
          dsimp [E2_good]
          rw [Finset.mem_filter]
          exact ⟨hE, hAll E hE⟩
      rw [hset]
      exact sum_wR_eq_one y
    rw [hsum]
    norm_num
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (by intro h; exact hAeq h.symm)
    -- Markov
    have hMarkov : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0)) ≤
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * X E) / ((3 / 4 : ℝ) * A) := by
      exact wR_markov y X (a := (3 / 4 : ℝ) * A) (by positivity)
        (by intro E; dsimp [X]; exact bMass_nonneg p _)
    have hEsum : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * X E) ≤
        (1 / 4 : ℝ) * A := by
      dsimp [X, A]
      exact E2_expect_le p y lamP hn
    have hbad : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0)) ≤ 1 / 3 := by
      have hposd : 0 ≤ (3 / 4 : ℝ) * A := by positivity
      have hdiv : ((1 / 4 : ℝ) * A) / ((3 / 4 : ℝ) * A) = 1 / 3 := by
        have hAn : A ≠ 0 := hAeq
        field_simp [hAn]
      calc
        (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0))
            ≤ (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E * X E) / ((3 / 4 : ℝ) * A) := hMarkov
        _ ≤ ((1 / 4 : ℝ) * A) / ((3 / 4 : ℝ) * A) := by
            exact div_le_div_of_nonneg_right hEsum hposd
        _ = 1 / 3 := hdiv
    -- complement dance: mass(good) = 1 − P(bad) ≥ 1 − 1/3 = 2/3
    have hpt : ∀ E : Finset (Fin n),
        (if X E ≤ (3 / 4 : ℝ) * A then (1 : ℝ) else 0) =
          (1 : ℝ) - (if (3 / 4 : ℝ) * A < X E then 1 else 0) := by
      intro E
      by_cases hle : X E ≤ (3 / 4 : ℝ) * A
      · have hnot : ¬ (3 / 4 : ℝ) * A < X E := not_lt_of_ge hle
        rw [if_pos hle, if_neg hnot]
        norm_num
      · have hgt : (3 / 4 : ℝ) * A < X E := lt_of_not_ge hle
        rw [if_neg hle, if_pos hgt]
        norm_num
    calc
      (2 : ℝ) / 3 ≤ (1 : ℝ) - 1 / 3 := by norm_num
      _ ≤ (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0)) := by
            linarith [hbad]
      _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if X E ≤ (3 / 4 : ℝ) * A then 1 else 0) := by
            calc
              (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                  wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0))
                  = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) -
                      (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                        wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0)) := by
                        rw [sum_wR_eq_one]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      (wR y E - wR y E * (if (3 / 4 : ℝ) * A < X E then 1 else 0)) := by
                        rw [← Finset.sum_sub_distrib]
              _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      wR y E * (if X E ≤ (3 / 4 : ℝ) * A then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro E hE
                        rw [hpt E]
                        ring
      _ = ∑ E ∈ E2_good p y lamP hn, wR y E := by
            dsimp [E2_good]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro E hE
            by_cases hg : X E ≤ (3 / 4 : ℝ) * A
            · rw [if_pos hg, if_pos hg]
              ring
            · rw [if_neg hg, if_neg hg]
              ring


/-- **E2 cf-preservation substrate**: on `E ∈ E2_good` the `2√n`-slab of `ỹ^E` at
`lamP` carries at least `(1/4)·A` of the mass. -/
lemma E2_cf_substrate {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ) (hn : 1 ≤ n)
    {E : Finset (Fin n)} (hE : E ∈ E2_good p y lamP hn) :
    (1 / 4 : ℝ) * bMass p (slabB y lamP (Real.sqrt (n : ℝ))) ≤
      bMass p (slabB (fun i : Fin n => roundYr y E i) lamP (2 * Real.sqrt (n : ℝ))) := by
  classical
  let A : ℝ := bMass p (slabB y lamP (Real.sqrt (n : ℝ)))
  let X : ℝ := bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
      (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
        (fun i : Fin n => roundYr y E i) lamP B))
  let R : ℝ := bMass p ((slabB y lamP (Real.sqrt (n : ℝ))).filter
      (fun B : Finset (Fin n) => ¬ SgtMem (2 * Real.sqrt (n : ℝ))
        (fun i : Fin n => roundYr y E i) lamP B))
  have hX : X ≤ (3 / 4 : ℝ) * A := by
    have hmem := E2_good_mem p y lamP hn E
    exact (hmem.mp hE).2
  have hA_eq : A = X + R := by
    dsimp [A, X, R]
    dsimp [bMass]
    calc
      (∑ B ∈ slabB y lamP (Real.sqrt (n : ℝ)), wB n p B)
          = (∑ B ∈ slabB y lamP (Real.sqrt (n : ℝ)),
              ((if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
                then wB n p B else 0) +
              (if ¬ SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
                then wB n p B else 0))) := by
            apply Finset.sum_congr rfl
            intro B hB
            by_cases hS : SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B <;> simp [hS]
      _ = (∑ B ∈ slabB y lamP (Real.sqrt (n : ℝ)),
              (if SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
                then wB n p B else 0)) +
          (∑ B ∈ slabB y lamP (Real.sqrt (n : ℝ)),
              (if ¬ SgtMem (2 * Real.sqrt (n : ℝ)) (fun i : Fin n => roundYr y E i) lamP B
                then wB n p B else 0)) := by
            rw [← Finset.sum_add_distrib]
      _ = (∑ B ∈ (slabB y lamP (Real.sqrt (n : ℝ))).filter
              (fun B : Finset (Fin n) => SgtMem (2 * Real.sqrt (n : ℝ))
                (fun i : Fin n => roundYr y E i) lamP B), wB n p B) +
          (∑ B ∈ (slabB y lamP (Real.sqrt (n : ℝ))).filter
              (fun B : Finset (Fin n) => ¬ SgtMem (2 * Real.sqrt (n : ℝ))
                (fun i : Fin n => roundYr y E i) lamP B), wB n p B) := by
            rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hmono : R ≤ bMass p (slabB (fun i : Fin n => roundYr y E i) lamP (2 * Real.sqrt (n : ℝ))) := by
    dsimp [R]
    apply bMass_mono
    intro B hB
    rw [Finset.mem_filter] at hB
    rcases hB with ⟨hBslab, hBnot⟩
    dsimp [slabB]
    rw [Finset.mem_filter]
    constructor
    · dsimp [slabB] at hBslab
      exact (Finset.mem_filter.mp hBslab).1
    · dsimp [SgtMem] at hBnot
      exact le_of_not_gt hBnot
  have hge : (1 / 4 : ℝ) * A ≤ bMass p (slabB (fun i : Fin n => roundYr y E i) lamP
      (2 * Real.sqrt (n : ℝ))) := by
    have hX0 : 0 ≤ X := by dsimp [X]; exact bMass_nonneg p _
    have hR0 : 0 ≤ R := by dsimp [R]; exact bMass_nonneg p _
    have hA0 : 0 ≤ A := by dsimp [A]; exact bMass_nonneg p _
    -- from hA_eq and hX: A − X = R; (1/4)A ≤ A − X
    nlinarith [hA_eq, hX, hmono]
  simpa [A] using hge


/-! ## E3 — total-sum bound (paper lines ~1780–1790)

The variance of `Σᵢ(yᵢ − ξᵢ)` is at most `n/4` (coordinate independence), so
Chebyshev at `√(12n/11)` gives `P_ξ(|Σᵢ(yᵢ − ξᵢ)| > √(12n/11)) ≤ 11/48`; the
E3-good event (mass ≥ 37/48) carries property (4): `|Σᵢyᵢ − Σᵢξᵢ| ≤ √(12n/11)`. -/

/-- E3 tail: `P_ξ(|Σᵢ(yᵢ − ξᵢ)| > √(12n/11)) ≤ 11/48`. -/
lemma E3_tail_le {n : ℕ} (y : Fin n → ℝ) (hn : 1 ≤ n) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) <
            |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| then 1 else 0)) ≤
      (11 : ℝ) / 48 := by
  classical
  let w : ℝ := Real.sqrt ((12 : ℝ) * (n : ℝ) / 11)
  have hw0 : 0 < w := by
    dsimp [w]
    apply Real.sqrt_pos.2
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have h := rounding_tail_le y (Finset.univ : Finset (Fin n)) hw0
  have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
  have hEq : (n : ℝ) / (4 * w ^ 2) = (11 : ℝ) / 48 := by
    dsimp [w]
    have hsq : (Real.sqrt ((12 : ℝ) * (n : ℝ) / 11)) ^ 2 = (12 : ℝ) * (n : ℝ) / 11 :=
      Real.sq_sqrt (by positivity)
    rw [hsq]
    field_simp [hnz]
    ring
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
        wR y E * (if Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) <
            |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| then 1 else 0))
        = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
            wR y E * (if w <
              |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| then 1 else 0)) := by
            rfl
    _ ≤ (n : ℝ) / (4 * w ^ 2) := h
    _ = (11 : ℝ) / 48 := hEq

/-- the E3 good event: the total rounding error is at most `√(12n/11)`. -/
noncomputable def E3_good {n : ℕ} (y : Fin n → ℝ) (hn : 1 ≤ n) : Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powerset).filter
    (fun E : Finset (Fin n) =>
      |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| ≤
        Real.sqrt ((12 : ℝ) * (n : ℝ) / 11))

/-- membership in `E3_good`. -/
lemma E3_good_mem {n : ℕ} (y : Fin n → ℝ) (hn : 1 ≤ n) (E : Finset (Fin n)) :
    E ∈ E3_good y hn ↔
      E ∈ ((Finset.univ : Finset (Fin n)).powerset) ∧
      |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| ≤
        Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := by
  classical
  dsimp [E3_good]
  rw [Finset.mem_filter]

/-- **E3 mass**: the rounding mass of `E3_good` is at least `37/48`. -/
lemma E3_mass_ge {n : ℕ} (y : Fin n → ℝ) (hn : 1 ≤ n) :
    (37 : ℝ) / 48 ≤ ∑ E ∈ E3_good y hn, wR y E := by
  classical
  let Bad : Finset (Fin n) → Prop := fun E =>
    Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) <
      |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)|
  have hbad := E3_tail_le y hn
  have hpt : ∀ E : Finset (Fin n),
      (if ¬ Bad E then (1 : ℝ) else 0) = (1 : ℝ) - (if Bad E then 1 else 0) := by
    intro E
    by_cases hB : Bad E
    · have hnot : ¬ ¬ Bad E := by exact not_not.mpr hB
      rw [if_neg hnot, if_pos hB]
      norm_num
    · rw [if_pos hB]
      rw [if_neg hB]
      norm_num
  calc
    (37 : ℝ) / 48 ≤ (1 : ℝ) - 11 / 48 := by norm_num
    _ ≤ (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if Bad E then 1 else 0)) := by
          linarith [hbad]
    _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
          wR y E * (if ¬ Bad E then 1 else 0) := by
          calc
            (1 : ℝ) - (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                wR y E * (if Bad E then 1 else 0))
                = (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset, wR y E) -
                    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                      wR y E * (if Bad E then 1 else 0)) := by
                      rw [sum_wR_eq_one]
            _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    (wR y E - wR y E * (if Bad E then 1 else 0)) := by
                      rw [← Finset.sum_sub_distrib]
            _ = ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset,
                    wR y E * (if ¬ Bad E then 1 else 0) := by
                      apply Finset.sum_congr rfl
                      intro E hE
                      rw [hpt E]
                      ring
    _ = ∑ E ∈ E3_good y hn, wR y E := by
          have hset : E3_good y hn =
              ((Finset.univ : Finset (Fin n)).powerset).filter (fun E : Finset (Fin n) => ¬ Bad E) := by
            apply Finset.Subset.antisymm
            · intro E hE
              dsimp [E3_good] at hE
              rw [Finset.mem_filter] at hE
              rw [Finset.mem_filter]
              exact ⟨hE.1, (by intro hb; exact (not_lt_of_ge hE.2) hb)⟩
            · intro E hE
              dsimp [E3_good]
              rw [Finset.mem_filter] at hE
              rw [Finset.mem_filter]
              exact ⟨hE.1, (by simpa [Bad] using hE.2)⟩
          rw [hset, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro E hE
          by_cases hg : ¬ Bad E <;> simp [hg]

/-- **E3 sum bound**: on `E ∈ E3_good`, `|Σᵢyᵢ − Σᵢξᵢ| ≤ √(12n/11)`. -/
lemma E3_sum_bound {n : ℕ} (y : Fin n → ℝ) (hn : 1 ≤ n)
    {E : Finset (Fin n)} (hE : E ∈ E3_good y hn) :
    |(∑ i ∈ (Finset.univ : Finset (Fin n)), y i) -
        (∑ i ∈ (Finset.univ : Finset (Fin n)), roundYr y E i)| ≤
      Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := by
  classical
  have hmem := E3_good_mem y hn E
  have hle : |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| ≤
      Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := (hmem.mp hE).2
  have hconv : |(∑ i ∈ (Finset.univ : Finset (Fin n)), y i) -
        (∑ i ∈ (Finset.univ : Finset (Fin n)), roundYr y E i)| =
      |∑ i ∈ (Finset.univ : Finset (Fin n)), (y i - roundYr y E i)| := by
    congr 1
    rw [← Finset.sum_sub_distrib]
  rwa [hconv]


/-! ## magic-vector property (1) — the rounding is a 1-Lipschitz integer approximation

For the candidate `y′ := roundY y E` (integer-valued), every coordinate moves by at
most one: `|yᵢ − roundYr y E i| ≤ 1`. -/

/-- coordinate rounding residual identity: `yᵢ − ξᵢ = θᵢ − 1_{i∈E}` (fractional part
minus the rounding bit). -/
lemma round_fract_id {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) (i : Fin n) :
    y i - roundYr y E i = th (y i) - (if i ∈ E then 1 else 0) := by
  have hcast : roundYr y E i = (Int.floor (y i) : ℝ) + (if i ∈ E then 1 else 0) := by
    dsimp [roundYr, roundY]
    rw [Int.cast_add]
    by_cases hE : i ∈ E <;> simp [hE]
  calc
    y i - roundYr y E i = y i - ((Int.floor (y i) : ℝ) + (if i ∈ E then 1 else 0)) := by
      rw [hcast]
    _ = (y i - (Int.floor (y i) : ℝ)) - (if i ∈ E then 1 else 0) := by ring
    _ = th (y i) - (if i ∈ E then 1 else 0) := by
      dsimp [th]

/-- **property (1)**: `|yᵢ − (roundY y E i : ℝ)| ≤ 1` for every coordinate. -/
lemma round_coord_le_one {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) (i : Fin n) :
    |y i - roundYr y E i| ≤ 1 := by
  rw [round_fract_id]
  by_cases hE : i ∈ E
  · have hth0 : 0 ≤ th (y i) := th_nonneg (y i)
    have hth1 : th (y i) < 1 := th_lt_one (y i)
    rw [if_pos hE]
    have hnonpos : th (y i) - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  · have hth0 : 0 ≤ th (y i) := th_nonneg (y i)
    have hth1 : th (y i) < 1 := th_lt_one (y i)
    rw [if_neg hE]
    rw [sub_zero]
    rw [abs_of_nonneg hth0]
    linarith

/-- `roundY y E` is integer-valued (as a real-coefficient vector it is the rounding). -/
lemma roundY_int_val {n : ℕ} (y : Fin n → ℝ) (E : Finset (Fin n)) (i : Fin n) :
    roundYr y E i = ((roundY y E i : ℤ) : ℝ) := by
  rfl


/-- **two-slab cover**: a `2√n`-slab at `lamP` is contained in the union of the
two `√n`-slabs centered at `lamP − √n` and `lamP + √n`. -/
lemma slab_mass_two_le {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ)
    (hn : 1 ≤ n) :
    bMass p (slabB y lamP (2 * Real.sqrt (n : ℝ))) ≤
      bMass p (slabB y (lamP - Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) +
      bMass p (slabB y (lamP + Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) := by
  classical
  let r : ℝ := Real.sqrt (n : ℝ)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg (n : ℝ)
  have hcov : slabB y lamP (2 * r) ⊆
      (slabB y (lamP - r) r) ∪ (slabB y (lamP + r) r) := by
    intro B hB
    dsimp [slabB] at hB
    have hB1 : B ∈ (Finset.univ : Finset (Fin n)).powerset := (Finset.mem_filter.mp hB).1
    have hB2 : |rSub y B - lamP| ≤ 2 * r := (Finset.mem_filter.mp hB).2
    rcases Commons.Analysis.Real.abs_sub_le_two_mul_split hr0 hB2 with hlt | hgt
    · rw [Finset.mem_union]
      left
      dsimp [slabB]
      rw [Finset.mem_filter]
      exact ⟨hB1, hlt⟩
    · rw [Finset.mem_union]
      right
      dsimp [slabB]
      rw [Finset.mem_filter]
      exact ⟨hB1, hgt⟩
  have hmono := bMass_mono p hcov
  have hle := bMass_union_le p (T₁ := slabB y (lamP - r) r) (T₂ := slabB y (lamP + r) r)
  -- bMass(union) ≤ bMass(T1) + bMass(T2)
  calc
    bMass p (slabB y lamP (2 * Real.sqrt (n : ℝ)))
        = bMass p (slabB y lamP (2 * r)) := rfl
    _ ≤ bMass p ((slabB y (lamP - r) r) ∪ (slabB y (lamP + r) r)) := hmono
    _ ≤ bMass p (slabB y (lamP - r) r) + bMass p (slabB y (lamP + r) r) := hle
    _ = bMass p (slabB y (lamP - Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) +
        bMass p (slabB y (lamP + Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) := rfl


/-! ## λ′-choice: the real slab-mass supremum `W(y)` and its approximating center

`W(y) := sSup over lam of bMass(slabB y lam √n)` — the real-mass analogue of the
Lévy concentration function at scale `√n`.  For the magic-vector property (3) we
need a center `lam` whose slab mass is within a universal factor of `W(y)`
(`exists_lam_approx`, `exists_lam_half` below, driven through `lt_csSup`-style
`exists_lt_of_lt_csSup`). -/

/-- the real supremum over centers of the `√n`-slab mass. -/
noncomputable def cfRealW {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ)))))

/-- the slab mass at any center lies in the range-set of `cfRealW`. -/
lemma cfW_mem_range {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ) :
    bMass p (slabB y lam (Real.sqrt (n : ℝ))) ∈
      Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ)))) :=
  ⟨lam, rfl⟩

/-- the range-set of slab masses is bounded above by `1`. -/
lemma cfW_bddAbove {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) :
    BddAbove (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ))))) := by
  refine ⟨1, ?_⟩
  intro a ha
  rcases ha with ⟨lam, rfl⟩
  exact bMass_le_one p y lam (Real.sqrt (n : ℝ))

/-- the range-set is nonempty. -/
lemma cfW_nonempty {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) :
    (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ))))).Nonempty := by
  refine ⟨bMass p (slabB y 0 (Real.sqrt (n : ℝ))), ⟨0, rfl⟩⟩

/-- every slab mass is at most the supremum `W(y)`. -/
lemma m_le_cfW {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ) :
    bMass p (slabB y lam (Real.sqrt (n : ℝ))) ≤ cfRealW p y := by
  dsimp [cfRealW]
  exact le_csSup (cfW_bddAbove p y) (cfW_mem_range p y lam)

/-- `W(y) ≤ 1`. -/
lemma cfW_le_one {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) : cfRealW p y ≤ 1 := by
  dsimp [cfRealW]
  exact csSup_le (cfW_nonempty p y) (by
    intro a ha
    rcases ha with ⟨lam, rfl⟩
    exact bMass_le_one p y lam (Real.sqrt (n : ℝ)))

/-- `W(y) ≥ 0`. -/
lemma cfW_nonneg {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) : 0 ≤ cfRealW p y := by
  exact le_trans (bMass_nonneg p (slabB y 0 (Real.sqrt (n : ℝ)))) (m_le_cfW p y 0)

/-- **λ′-choice**: some center has slab mass within `1/16` of `W(y)` from below. -/
lemma exists_lam_approx {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) :
    ∃ lam : ℝ, cfRealW p y - 1 / 16 < bMass p (slabB y lam (Real.sqrt (n : ℝ))) ∧
      bMass p (slabB y lam (Real.sqrt (n : ℝ))) ≤ cfRealW p y := by
  have hlt : cfRealW p y - 1 / 16 <
      sSup (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ))))) := by
    dsimp [cfRealW]
    linarith
  rcases exists_lt_of_lt_csSup (cfW_nonempty p y) hlt with ⟨a, ha, hgt⟩
  rcases ha with ⟨lam, rfl⟩
  exact ⟨lam, hgt, m_le_cfW p y lam⟩

/-- half-mass version (for `W(y) > 0`): some center has mass `> W(y)/2`. -/
lemma exists_lam_half {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (hW : 0 < cfRealW p y) :
    ∃ lam : ℝ, cfRealW p y / 2 < bMass p (slabB y lam (Real.sqrt (n : ℝ))) ∧
      bMass p (slabB y lam (Real.sqrt (n : ℝ))) ≤ cfRealW p y := by
  have hlt : cfRealW p y / 2 <
      sSup (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ))))) := by
    have hW' : 0 < sSup (Set.range (fun lam : ℝ => bMass p (slabB y lam (Real.sqrt (n : ℝ))))) := by
      simpa [cfRealW] using hW
    dsimp [cfRealW]
    linarith
  rcases exists_lt_of_lt_csSup (cfW_nonempty p y) hlt with ⟨a, ha, hgt⟩
  rcases ha with ⟨lam, rfl⟩
  exact ⟨lam, hgt, m_le_cfW p y lam⟩


/-! ## real-coefficient slab measure identity

For ANY real coefficient vector `x`, the canonical Bernoulli mass of the slab
event `{|Σᵢ ωᵢxᵢ − lam| ≤ R}` is `ofReal` of the subset-weight sum
`bMass(slabB x lam R)`.  (The integer-vector version is SlabBridge's
`slab_real_eq_weight`; here `rSub` replaces `Sec3.subSum` + `cast_subSum`, so
the subset-sum steps close by `rfl`.) -/

/-- slab ∩ support = disjoint union of the good-atom singletons (real x). -/
lemma slab_inter_support_eq_union_real {n : ℕ} (x : Fin n → ℝ) (lam R : ℝ) :
    slabEvent x lam R ∩ supportSet
      = ⋃ B ∈ slabB x lam R, ({indVec B} : Set (Fin n → ℝ)) := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hE, hsup⟩
    let B : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1)
    have hωB : ω = indVec B := indVec_support_eq hsup
    have hSig : (∑ i : Fin n, ω i * x i) = rSub x B := by
      have h1 := sum_weight_eq_indVec hsup x
      dsimp [rSub]
      simpa [B] using h1
    have hBabs : |rSub x B - lam| ≤ R := by
      dsimp [slabEvent] at hE
      rwa [hSig] at hE
    have hBmem : B ∈ slabB x lam R := by
      dsimp [slabB]
      rw [Finset.mem_filter]
      exact ⟨by simp [B], hBabs⟩
    exact Set.mem_biUnion hBmem (Set.mem_singleton_iff.mpr hωB)
  · intro hω
    have hm : ∃ B : Finset (Fin n), B ∈ slabB x lam R ∧ ω ∈ ({indVec B} : Set (Fin n → ℝ)) := by
      simpa using hω
    rcases hm with ⟨B, hBmem, hωB⟩
    have hEq : ω = indVec B := Set.mem_singleton_iff.mp hωB
    constructor
    · have hgood : |rSub x B - lam| ≤ R := (Finset.mem_filter.mp hBmem).2
      have hSig : (∑ i : Fin n, indVec B i * x i) = rSub x B := by
        calc
          (∑ i : Fin n, indVec B i * x i) = ∑ i ∈ B, x i := indVec_weighted_sum_eq x B
          _ = rSub x B := rfl
      rw [hEq]
      dsimp [slabEvent]
      rwa [hSig]
    · rw [hEq]
      exact indVec_mem_support B

/-- **real-coefficient slab measure identity**:
`berP (slabEvent x lam R) = ofReal (bMass p (slabB x lam R))`. -/
lemma berP_real_slab_eq {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam R : ℝ) :
    berP (n := n) p (slabEvent x lam R) =
      ENNReal.ofReal (bMass p (slabB x lam R)) := by
  classical
  have hEmeas : MeasurableSet (slabEvent x lam R) := measurable_slabEvent x lam R
  have hEq := measure_slab_eq_inter_support p hEmeas
  have hEq2 := slab_inter_support_eq_union_real x lam R
  rw [hEq, hEq2]
  rw [MeasureTheory.measure_biUnion_finset (s := slabB x lam R)
    (f := fun B : Finset (Fin n) => ({indVec B} : Set (Fin n → ℝ)))
    (pairwiseDisjoint_indVec (slabB x lam R))
    (hm := by intro B hB; exact measurableSet_singleton (indVec B))]
  have hval : ∀ B : Finset (Fin n), B ∈ slabB x lam R →
      berP (n := n) p ({indVec B} : Set (Fin n → ℝ)) = ENNReal.ofReal (wB n p B) := by
    intro B hB
    have htop : berP (n := n) p ({indVec B} : Set (Fin n → ℝ)) ≠ ⊤ :=
      MeasureTheory.measure_ne_top (berP (n := n) p) ({indVec B} : Set (Fin n → ℝ))
    rw [← ENNReal.ofReal_toReal htop]
    congr 1
    exact berP_real_indVec p B
  have hsum : (∑ B ∈ slabB x lam R, ENNReal.ofReal (wB n p B)) =
      ENNReal.ofReal (∑ B ∈ slabB x lam R, wB n p B) := by
    classical
    have hnon : ∀ B : Finset (Fin n), 0 ≤ wB n p B := by
      intro B
      exact wB_nonneg n p B
    refine Finset.induction_on (slabB x lam R) ?_ ?_
    · simp
    · intro a s' has ih
      calc
        (∑ B ∈ insert a s', ENNReal.ofReal (wB n p B))
            = ENNReal.ofReal (wB n p a) + (∑ B ∈ s', ENNReal.ofReal (wB n p B)) := by
              rw [Finset.sum_insert has]
        _ = ENNReal.ofReal (wB n p a) + ENNReal.ofReal (∑ B ∈ s', wB n p B) := by
              rw [ih]
        _ = ENNReal.ofReal (wB n p a + ∑ B ∈ s', wB n p B) := by
              rw [ENNReal.ofReal_add (hnon a) (Finset.sum_nonneg (fun B hB => hnon B))]
        _ = ENNReal.ofReal (∑ B ∈ insert a s', wB n p B) := by
              rw [Finset.sum_insert has]

  calc
    (∑ B ∈ slabB x lam R, berP (n := n) p ({indVec B} : Set (Fin n → ℝ)))
        = ∑ B ∈ slabB x lam R, ENNReal.ofReal (wB n p B) := by
          apply Finset.sum_congr rfl
          intro B hB
          exact hval B hB
    _ = ENNReal.ofReal (∑ B ∈ slabB x lam R, wB n p B) := hsum
    _ = ENNReal.ofReal (bMass p (slabB x lam R)) := by
          dsimp [bMass]


/-- **lower one-sided bound**: every `√n`-slab mass of `x` is at most the
Lévy concentration `cfP p x √n`. -/
lemma ofReal_bMass_le_cfP {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam : ℝ) :
    ENNReal.ofReal (bMass p (slabB x lam (Real.sqrt (n : ℝ)))) ≤
      cfP p x (Real.sqrt (n : ℝ)) := by
  classical
  have hme := berP_real_slab_eq p x lam (Real.sqrt (n : ℝ))
  rw [← hme]
  unfold cfP
  exact Submission.Helpers.le_levyConcentration (berP (n := n) p) (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i)
    (Real.sqrt (n : ℝ)) lam

/-- **upper one-sided bound**: `cfP p y √n ≤ ofReal(W(y))` where
`W(y) := cfRealW p y` is the real supremum over centers. -/
lemma cfP_le_ofReal_cfW {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) :
    cfP p y (Real.sqrt (n : ℝ)) ≤ ENNReal.ofReal (cfRealW p y) := by
  classical
  unfold cfP
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  intro a ha
  rcases ha with ⟨l, rfl⟩
  change berP (n := n) p (slabEvent y l (Real.sqrt (n : ℝ))) ≤
    ENNReal.ofReal (cfRealW p y)
  rw [berP_real_slab_eq]
  exact ENNReal.ofReal_le_ofReal (m_le_cfW p y l)


/-! ## property-(3) chain: real `cfP` bounds from the two-slab cover and `E2`

These real-valued lemmas carry the core of the final magic-vector property (3). -/

/-- every `√n`-slab mass is at most the real `cfP` value. -/
lemma bMass_le_cfP_toReal {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam : ℝ) :
    bMass p (slabB x lam (Real.sqrt (n : ℝ))) ≤ (cfP p x (Real.sqrt (n : ℝ))).toReal := by
  classical
  have h := ofReal_bMass_le_cfP p x lam
  have htop : cfP p x (Real.sqrt (n : ℝ)) ≠ ⊤ := by
    have hle1 : cfP p x (Real.sqrt (n : ℝ)) ≤ (1 : ℝ≥0∞) := by
      unfold cfP
      exact Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
        (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) (Real.sqrt (n : ℝ))
    exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hle1
  have hm := ENNReal.toReal_mono htop h
  have hm0 : 0 ≤ bMass p (slabB x lam (Real.sqrt (n : ℝ))) := bMass_nonneg p _
  rwa [ENNReal.toReal_ofReal hm0] at hm

/-- the two-√n-slab mass of any `x` is at most twice the real `cfP` value. -/
lemma two_slab_cfP_real_le {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lamP : ℝ)
    (hn : 1 ≤ n) :
    bMass p (slabB x lamP (2 * Real.sqrt (n : ℝ))) ≤
      2 * (cfP p x (Real.sqrt (n : ℝ))).toReal := by
  classical
  have hsplit := slab_mass_two_le p x lamP hn
  have h1 : bMass p (slabB x (lamP - Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) ≤
      (cfP p x (Real.sqrt (n : ℝ))).toReal :=
    bMass_le_cfP_toReal p x (lamP - Real.sqrt (n : ℝ))
  have h2 : bMass p (slabB x (lamP + Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) ≤
      (cfP p x (Real.sqrt (n : ℝ))).toReal :=
    bMass_le_cfP_toReal p x (lamP + Real.sqrt (n : ℝ))
  have hc0 : 0 ≤ (cfP p x (Real.sqrt (n : ℝ))).toReal := ENNReal.toReal_nonneg
  nlinarith

/-- **E2 → real cfP lower bound**: on `E2_good` at `lamP`, the rounded vector
`ỹ^E` has concentration at least `(1/8)·A` (real), `A :=` the slab mass of `y`. -/
lemma E2_cfP_real_bound {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lamP : ℝ)
    (hn : 1 ≤ n) {E : Finset (Fin n)} (hE : E ∈ E2_good p y lamP hn) :
    (1 / 8 : ℝ) * bMass p (slabB y lamP (Real.sqrt (n : ℝ))) ≤
      (cfP p (fun i : Fin n => roundYr y E i) (Real.sqrt (n : ℝ))).toReal := by
  classical
  have hsub := E2_cf_substrate p y lamP hn hE
  -- (1/4)A ≤ bMass(slabB y'coefs lamP (2√n))
  have htwo := two_slab_cfP_real_le p (fun i : Fin n => roundYr y E i) lamP hn
  have hc0 : 0 ≤ (cfP p (fun i : Fin n => roundYr y E i) (Real.sqrt (n : ℝ))).toReal :=
    ENNReal.toReal_nonneg
  nlinarith

/-- if `W(y) = 0` then the whole concentration `cfP p y √n` vanishes. -/
lemma cfP_eq_zero_of_cfW_eq_zero {n : ℕ} (p : unitInterval) (y : Fin n → ℝ)
    (hW : cfRealW p y = 0) :
    cfP p y (Real.sqrt (n : ℝ)) = 0 := by
  classical
  have h := cfP_le_ofReal_cfW p y
  rw [hW] at h
  have h0 : ENNReal.ofReal (0 : ℝ) = 0 := by simp
  rw [h0] at h
  exact le_antisymm h bot_le


/-- **existential rounding pattern**: some `E` lies in `E1K_good ∩ E2_good(lamP)
∩ E3_good` (masses 2/3, 2/3, 37/48 clear 2). -/
lemma exists_E1E2E3 {n : ℕ} (p : unitInterval) (y : Fin n → ℝ) (lam : ℝ)
    {L : ℝ} (hL0 : 0 < L) (hn : 1 ≤ n)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s)
    (lamP : ℝ) :
    ∃ E : Finset (Fin n), E ∈ E1K_good p y lam L hn ∧ E ∈ E2_good p y lamP hn ∧
      E ∈ E3_good y hn := by
  classical
  let U : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  let A : Finset (Finset (Fin n)) := E1K_good p y lam L hn
  let B : Finset (Finset (Fin n)) := E2_good p y lamP hn
  let C : Finset (Finset (Fin n)) := E3_good y hn
  have hA_sub : A ⊆ U := by
    dsimp [A, U, E1K_good]
    exact Finset.filter_subset _ _
  have hB_sub : B ⊆ U := by
    dsimp [B, U, E2_good]
    exact Finset.filter_subset _ _
  have hC_sub : C ⊆ U := by
    dsimp [C, U, E3_good]
    exact Finset.filter_subset _ _
  have hm1 : (2 : ℝ) / 3 ≤ ∑ E ∈ A, wR y E := by
    dsimp [A]
    exact E1K_mass_ge p y lam hL0 hn hsb
  have hm2 : (2 : ℝ) / 3 ≤ ∑ E ∈ B, wR y E := by
    dsimp [B]
    exact E2_mass_ge p y lamP hn
  have hm3 : (37 : ℝ) / 48 ≤ ∑ E ∈ C, wR y E := by
    dsimp [C]
    exact E3_mass_ge y hn
  have hsum : 2 < (∑ E ∈ A, wR y E) + (∑ E ∈ B, wR y E) + (∑ E ∈ C, wR y E) := by
    nlinarith
  rcases Commons.Algebra.BigOperators.three_sets_intersection_nonempty U (wR y)
    (by intro x hx; exact wR_nonneg y x) (sum_wR_eq_one y) A B C hA_sub hB_sub hC_sub hsum
    with ⟨E, hEA, hEB, hEC⟩
  exact ⟨E, hEA, hEB, hEC⟩


/-! ## `magic_vector` — Lemma l: magic vector (Tikhomirov 2020)

Weight-sum (canonical-space) form: if the Bernoulli(`p`) small-ball probabilities
of the (real) vector `y` satisfy `μ_s(y) ≤ Ls` for all `s ≥ √n`, then there is an
integer vector `y′` with:  (1) `‖y − y′‖∞ ≤ 1`;  (2) the same small-ball bound
with slope `20L`;  (3) concentration at `√n` preserved: real `cfP(y′) ≥
(1/16)·real cfP(y)`;  (4) `|Σy − Σy′| ≤ √(12n/11)`. -/
theorem magic_vector {n : ℕ} (p : unitInterval) (hn : 1 ≤ n)
    (y : Fin n → ℝ) (lam : ℝ) {L : ℝ} (hL0 : 0 < L)
    (hsb : ∀ s : ℝ, Real.sqrt (n : ℝ) ≤ s → bMass p (slabB y lam s) ≤ L * s) :
    ∃ y' : Fin n → ℤ,
      (∀ i : Fin n, |y i - (y' i : ℝ)| ≤ 1) ∧
      (∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
        bMass p (slabB (fun i : Fin n => (y' i : ℝ)) lam t) ≤ 20 * L * t) ∧
      ((1 / 16 : ℝ) * (cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ))).toReal ≤
        (cfP p (fun i : Fin n => (y' i : ℝ)) (Real.sqrt (n : ℝ))).toReal) ∧
      |(∑ i : Fin n, y i) - (∑ i : Fin n, (y' i : ℝ))| ≤
        Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := by
  classical
  by_cases hW0 : cfRealW p y = 0
  · -- cfP(y) = 0: pick any lamP, any E ∈ E1∩E2∩E3
    rcases exists_E1E2E3 p y lam hL0 hn hsb 0 with ⟨E, hE1, hE2, hE3⟩
    let y' : Fin n → ℤ := roundY y E
    refine ⟨y', ?_, ?_, ?_, ?_⟩
    · intro i
      simpa [y', roundYr] using (round_coord_le_one y E i)
    · intro t ht
      have hsb' : bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 20 * L * t :=
        E1K_small_ball p y lam hL0 hn hsb hE1 t ht
      simpa [y', roundYr] using hsb'
    · have hcf0 : cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ)) = 0 :=
        cfP_eq_zero_of_cfW_eq_zero p y hW0
      rw [hcf0]
      simp
    · have hb := E3_sum_bound y hn hE3
      simpa [y', roundYr] using hb
  · -- main case: W(y) > 0
    have hWpos : 0 < cfRealW p y := lt_of_le_of_ne (cfW_nonneg p y) (by intro h; exact hW0 h.symm)
    rcases exists_lam_half p y hWpos with ⟨lamP, hbig, hle⟩
    rcases exists_E1E2E3 p y lam hL0 hn hsb lamP with ⟨E, hE1, hE2, hE3⟩
    let y' : Fin n → ℤ := roundY y E
    let A : ℝ := bMass p (slabB y lamP (Real.sqrt (n : ℝ)))
    refine ⟨y', ?_, ?_, ?_, ?_⟩
    · intro i
      simpa [y', roundYr] using (round_coord_le_one y E i)
    · intro t ht
      have hsb' : bMass p (slabB (fun i : Fin n => roundYr y E i) lam t) ≤ 20 * L * t :=
        E1K_small_ball p y lam hL0 hn hsb hE1 t ht
      simpa [y', roundYr] using hsb'
    · -- (3) real cfP preservation
      have hA0 : 0 ≤ A := by dsimp [A]; exact bMass_nonneg p _
      have hcfW : (cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ))).toReal ≤ cfRealW p y := by
        have h := cfP_le_ofReal_cfW p y
        have htop : cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ)) ≠ ⊤ := by
          have hle1 : cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ)) ≤ (1 : ℝ≥0∞) := by
            unfold cfP
            exact Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
              (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * y i) (Real.sqrt (n : ℝ))
          exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hle1
        have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        rwa [ENNReal.toReal_ofReal (cfW_nonneg p y)] at hto
      have hW2A : cfRealW p y ≤ 2 * A := by
        have hbig' : cfRealW p y / 2 < A := by
          simpa [A] using hbig
        dsimp [A]
        nlinarith
      have hc : (cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ))).toReal ≤ 2 * A := by
        nlinarith
      have hlb : (1 / 8 : ℝ) * A ≤
          (cfP p (fun i : Fin n => (roundY y E i : ℝ)) (Real.sqrt (n : ℝ))).toReal := by
        have hb := E2_cfP_real_bound p y lamP hn hE2
        simpa [roundYr] using hb
      have hreal : (1 / 16 : ℝ) * (cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ))).toReal ≤
          (cfP p (fun i : Fin n => (y' i : ℝ)) (Real.sqrt (n : ℝ))).toReal := by
        dsimp [y']
        have h1 : (1 / 16 : ℝ) * (cfP p (fun i : Fin n => y i) (Real.sqrt (n : ℝ))).toReal ≤
            (1 / 8 : ℝ) * A := by nlinarith
        exact le_trans h1 hlb
      simpa [y', roundYr] using hreal
    · have hb := E3_sum_bound y hn hE3
      simpa [y', roundYr] using hb


/-! ## spv-layer infrastructure: slab scaling and general-scale slope bounds -/

/-- slab masses rescale: `μ_{c·x}(c·λ′, c·R) = μ_x(λ′, R)` for `c > 0`. -/
lemma bMass_slab_scale {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    (lam' R : ℝ) :
    bMass p (slabB (fun i : Fin n => c * x i) (c * lam') (c * R)) =
      bMass p (slabB x lam' R) := by
  classical
  have hiff : ∀ B : Finset (Fin n),
      |rSub (fun i : Fin n => c * x i) B - c * lam'| ≤ c * R ↔
        |rSub x B - lam'| ≤ R := by
    intro B
    have hr : rSub (fun i : Fin n => c * x i) B = c * rSub x B := by
      dsimp [rSub]
      rw [Finset.mul_sum]
    have hfac : |c * rSub x B - c * lam'| = c * |rSub x B - lam'| := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
    constructor
    · intro h
      rw [hr] at h
      rw [hfac] at h
      exact le_of_mul_le_mul_left h hc
    · intro h
      rw [hr, hfac]
      exact mul_le_mul_of_nonneg_left h (le_of_lt hc)
  have hset : slabB (fun i : Fin n => c * x i) (c * lam') (c * R) = slabB x lam' R := by
    ext B
    dsimp [slabB]
    rw [Finset.mem_filter]
    rw [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨hp, hc0⟩
      exact ⟨hp, (hiff B).mp hc0⟩
    · intro h
      rcases h with ⟨hp, hc0⟩
      exact ⟨hp, (hiff B).mpr hc0⟩
  dsimp [bMass]
  rw [hset]

/-- general-scale lower bound: `ofReal(bMass(slabB x lam u)) ≤ cfP p x u`. -/
lemma ofReal_bMass_le_cfP' {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam u : ℝ) :
    ENNReal.ofReal (bMass p (slabB x lam u)) ≤ cfP p x u := by
  classical
  have hme := berP_real_slab_eq p x lam u
  rw [← hme]
  unfold cfP
  exact Submission.Helpers.le_levyConcentration (berP (n := n) p)
    (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) u lam

/-- general-scale: every `u`-slab mass is at most the real `cfP` value at `u`. -/
lemma bMass_le_cfP_toReal' {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam u : ℝ) :
    bMass p (slabB x lam u) ≤ (cfP p x u).toReal := by
  classical
  have h := ofReal_bMass_le_cfP' p x lam u
  have htop : cfP p x u ≠ ⊤ := by
    have hle1 : cfP p x u ≤ (1 : ℝ≥0∞) := by
      unfold cfP
      exact Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
        (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) u
    exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hle1
  have hm := ENNReal.toReal_mono htop h
  have hm0 : 0 ≤ bMass p (slabB x lam u) := bMass_nonneg p _
  rwa [ENNReal.toReal_ofReal hm0] at hm

/-- **slope bound**: if `cfP p x u ≤ ofReal(L·u)` (e.g. `u` above the threshold)
then every `u`-slab mass of `x` is at most `L·u`. -/
lemma bMass_le_of_cfP_le {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (lam u L : ℝ)
    (hL0 : 0 ≤ L * u)
    (hcf : cfP p x u ≤ ENNReal.ofReal (L * u)) :
    bMass p (slabB x lam u) ≤ L * u := by
  classical
  have h1 : bMass p (slabB x lam u) ≤ (cfP p x u).toReal := bMass_le_cfP_toReal' p x lam u
  have h2 : (cfP p x u).toReal ≤ L * u := by
    have htop : cfP p x u ≠ ⊤ := by
      have hle1 : cfP p x u ≤ (1 : ℝ≥0∞) := by
        unfold cfP
        exact Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
          (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) u
      exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hle1
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcf
    rwa [ENNReal.toReal_ofReal hL0] at hto
  exact le_trans h1 h2


/-! ## spv small-ball hypothesis (first brick)

For `c > 0` and the shifted center `lam₀ := −s·c·Σxᵢ`, the slab mass of
`c·x` at `lam₀` equals the slab mass of `x` at the scaled center/radius:
`μ_{c·x}(−s·c·Σx, t) = μ_x(−s·Σx, t/c)`.  With `c := √n/th` this is the
identity that turns the threshold slope bound on `x` into the small-ball
hypothesis on `y := (√n/th)·x`. -/
lemma spv_slab_scale {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {c s : ℝ}
    (hc : 0 < c) (t : ℝ) :
    bMass p (slabB (fun i : Fin n => c * x i)
        (-s * c * (∑ i : Fin n, x i)) t) =
      bMass p (slabB x (-s * (∑ i : Fin n, x i)) (t / c)) := by
  classical
  have h := bMass_slab_scale p x hc (-s * (∑ i : Fin n, x i)) (t / c)
  rw [← h]
  have hring : (-s * c * (∑ i : Fin n, x i)) = c * (-s * (∑ i : Fin n, x i)) := by ring
  rw [hring]
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hc1 : c * (t / c) = t := by field_simp [hc0]
  rw [hc1]

lemma y_smallBall_slope {n : ℕ} (p : unitInterval) (hn : 1 ≤ n) (x : Fin n → ℝ)
    {L s : ℝ} (hL1 : 1 ≤ L) (hp : (p : ℝ) < 1) :
    ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      bMass p (slabB (fun i : Fin n => (Real.sqrt (n : ℝ) / threshold p x L) * x i)
        (-s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / threshold p x L) * x i)) t) ≤
        2 * L * threshold p x L / Real.sqrt (n : ℝ) * t := by
  intro t ht
  let th : ℝ := threshold p x L
  let c : ℝ := Real.sqrt (n : ℝ) / th
  let y : Fin n → ℝ := fun i => c * x i
  change bMass p (slabB y (-s * (∑ i : Fin n, y i)) t) ≤
      ((2 * L * th) / Real.sqrt (n : ℝ)) * t
  have hL0 : 0 < L := by nlinarith
  have hth : 0 < th := by
    dsimp [th]
    exact threshold_pos p x hp hL0
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrt
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt
  have hth_ne : th ≠ 0 := ne_of_gt hth
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos hsqrt hth
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hysum : (∑ i : Fin n, y i) = c * (∑ i : Fin n, x i) := by
    dsimp [y]
    rw [← Finset.mul_sum]
  have hlam : -s * (∑ i : Fin n, y i) = -s * c * (∑ i : Fin n, x i) := by
    rw [hysum]
    ring
  have hy_eq : y = fun i : Fin n => c * x i := by
    funext i
    rfl
  -- slope bound in the sharp (L·th/√n) form, valid for radii strictly above √n
  have hslope : ∀ t0 : ℝ, Real.sqrt (n : ℝ) < t0 →
      bMass p (slabB y (-s * (∑ i : Fin n, y i)) t0) ≤
        (L * th / Real.sqrt (n : ℝ)) * t0 := by
    intro t0 ht0
    have ht0pos : 0 < t0 := lt_trans hsqrt ht0
    let u : ℝ := t0 * th / Real.sqrt (n : ℝ)
    have hu0 : 0 < u := by
      dsimp [u]
      exact div_pos (mul_pos ht0pos hth) hsqrt
    have huc : t0 / c = u := by
      dsimp [u, c]
      field_simp [hth_ne, hsqrt_ne]
    have hth_lt_u : th < u := by
      dsimp [u]
      rw [lt_div_iff₀ hsqrt]
      calc
        th * Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * th := by ring
        _ < t0 * th := mul_lt_mul_of_pos_right ht0 hth
    have hcf : cfP (n := n) p x u ≤ ENNReal.ofReal (L * u) :=
      cfP_le_slope_of_threshold hL1 hu0 hth_lt_u
    have hb_mass : bMass p (slabB x (-s * (∑ i : Fin n, x i)) u) ≤ L * u :=
      bMass_le_of_cfP_le p x (-s * (∑ i : Fin n, x i)) u L
        (mul_nonneg (le_of_lt hL0) (le_of_lt hu0)) hcf
    calc
      bMass p (slabB y (-s * (∑ i : Fin n, y i)) t0)
          = bMass p (slabB (fun i : Fin n => c * x i) (-s * c * (∑ i : Fin n, x i)) t0) := by
              rw [hlam]
      _ = bMass p (slabB x (-s * (∑ i : Fin n, x i)) (t0 / c)) := by
              exact spv_slab_scale (p := p) (x := x) (c := c) (s := s) hc t0
      _ = bMass p (slabB x (-s * (∑ i : Fin n, x i)) u) := by rw [huc]
      _ ≤ L * u := hb_mass
      _ = (L * th / Real.sqrt (n : ℝ)) * t0 := by
              dsimp [u]
              field_simp [hsqrt_ne]
  -- two cases: t is within the initial window or beyond
  by_cases ht2 : t ≤ 2 * Real.sqrt (n : ℝ)
  · -- t ∈ [√n, 2√n]: monotone up to 2√n, then use the slope bound there
    have hsq2 : Real.sqrt (n : ℝ) < 2 * Real.sqrt (n : ℝ) := by nlinarith
    have hb2 : bMass p (slabB y (-s * (∑ i : Fin n, y i)) t) ≤
        bMass p (slabB y (-s * (∑ i : Fin n, y i)) (2 * Real.sqrt (n : ℝ))) :=
      slab_mass_mono p y (-s * (∑ i : Fin n, y i)) ht2
    have hsl2 : bMass p (slabB y (-s * (∑ i : Fin n, y i)) (2 * Real.sqrt (n : ℝ))) ≤
        (L * th / Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) := hslope (2 * Real.sqrt (n : ℝ)) hsq2
    have htail : 2 * L * th ≤ ((2 * L * th) / Real.sqrt (n : ℝ)) * t := by
      have hmm := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ (2 * L * th) / Real.sqrt (n : ℝ))
      calc
        2 * L * th = Real.sqrt (n : ℝ) * ((2 * L * th) / Real.sqrt (n : ℝ)) := by
          field_simp [hsqrt_ne]
        _ ≤ t * ((2 * L * th) / Real.sqrt (n : ℝ)) := hmm
        _ = ((2 * L * th) / Real.sqrt (n : ℝ)) * t := by ring
    calc
      bMass p (slabB y (-s * (∑ i : Fin n, y i)) t)
          ≤ bMass p (slabB y (-s * (∑ i : Fin n, y i)) (2 * Real.sqrt (n : ℝ))) := hb2
      _ ≤ (L * th / Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) := hsl2
      _ = 2 * L * th := by
              field_simp [hsqrt_ne]
      _ ≤ ((2 * L * th) / Real.sqrt (n : ℝ)) * t := htail
  · -- 2√n < t: direct slope bound
    have hbig : Real.sqrt (n : ℝ) < t := by
      have h1 : Real.sqrt (n : ℝ) < 2 * Real.sqrt (n : ℝ) := by nlinarith
      exact lt_trans h1 (lt_of_not_ge ht2)
    have hb : bMass p (slabB y (-s * (∑ i : Fin n, y i)) t) ≤
        (L * th / Real.sqrt (n : ℝ)) * t := hslope t hbig
    have htpos : 0 < t := lt_trans hsqrt hbig
    have hfac : L * th / Real.sqrt (n : ℝ) ≤ (2 * L * th) / Real.sqrt (n : ℝ) := by
      have h1 : L * th ≤ 2 * L * th := by
        nlinarith [mul_nonneg (le_of_lt hL0) (le_of_lt hth)]
      exact div_le_div_of_nonneg_right h1 hsqrt0
    calc
      bMass p (slabB y (-s * (∑ i : Fin n, y i)) t) ≤
          (L * th / Real.sqrt (n : ℝ)) * t := hb
      _ ≤ ((2 * L * th) / Real.sqrt (n : ℝ)) * t :=
              mul_le_mul_of_nonneg_right hfac (le_of_lt htpos)

theorem magic_spv {n : ℕ} (p : unitInterval) (hn : 1 ≤ n) (x : Fin n → ℝ)
    {L shift : ℝ} (hL1 : 1 ≤ L) (hp : (p : ℝ) < 1) :
    ∃ spv : Fin n → ℤ,
      (∀ i : Fin n, |(Real.sqrt (n : ℝ) / threshold p x L) * x i - (spv i : ℝ)| ≤ 1) ∧
      (∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
        bMass p (slabB (fun i : Fin n => (spv i : ℝ))
          (-shift * (∑ i : Fin n, (Real.sqrt (n : ℝ) / threshold p x L) * x i)) t) ≤
          (40 * L * threshold p x L / Real.sqrt (n : ℝ)) * t) ∧
      ((1 / 32 : ℝ) * (L * threshold p x L) ≤
        (cfP p (fun i : Fin n => (spv i : ℝ)) (Real.sqrt (n : ℝ))).toReal) ∧
      |(∑ i : Fin n, (Real.sqrt (n : ℝ) / threshold p x L) * x i) -
        (∑ i : Fin n, (spv i : ℝ))| ≤ Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := by
  classical
  let th : ℝ := threshold p x L
  let y : Fin n → ℝ := fun i => (Real.sqrt (n : ℝ) / th) * x i
  let lam : ℝ := -shift * (∑ i : Fin n, y i)
  have hL0 : 0 < L := by nlinarith
  have hth : 0 < th := by
    dsimp [th]
    exact threshold_pos p x hp hL0
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmag0 : 0 < 2 * L * th / Real.sqrt (n : ℝ) := by positivity
  have hsb : ∀ u : ℝ, Real.sqrt (n : ℝ) ≤ u →
      bMass p (slabB y lam u) ≤ (2 * L * th / Real.sqrt (n : ℝ)) * u := by
    intro u hu
    have h1 := y_smallBall_slope (n := n) p hn x (L := L) (s := shift) hL1 hp u hu
    simpa [th, y, lam] using h1
  rcases magic_vector p hn y lam (L := 2 * L * th / Real.sqrt (n : ℝ)) hmag0 hsb with
    ⟨spv, h1, h2, h3, h4⟩
  refine ⟨spv, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [th, y] using h1 i
  · intro t ht
    have hh := h2 t ht
    have hfac : 20 * (2 * L * th / Real.sqrt (n : ℝ)) * t =
        (40 * L * th / Real.sqrt (n : ℝ)) * t := by ring
    have hh' : bMass p (slabB (fun i : Fin n => (spv i : ℝ)) lam t) ≤
        (40 * L * th / Real.sqrt (n : ℝ)) * t := by
      rwa [hfac] at hh
    simpa [th, y, lam] using hh'
  · have hlow0 : (1 / 2 : ℝ) * (L * th) ≤ (cfP p x th).toReal := by
      dsimp [th]
      exact cfP_threshold_lower p x hL0 hp
    have hscale : cfP p y (Real.sqrt (n : ℝ)) = cfP p x th := by
      dsimp [y, th]
      exact cfP_scale_threshold p x hn hL0 hp
    have hlow1 : (1 / 2 : ℝ) * (L * th) ≤ (cfP p y (Real.sqrt (n : ℝ))).toReal := by
      rwa [← hscale] at hlow0
    have hlow : (1 / 32 : ℝ) * (L * th) ≤
        (1 / 16 : ℝ) * (cfP p y (Real.sqrt (n : ℝ))).toReal := by
      nlinarith [hlow1]
    have hc' : (1 / 32 : ℝ) * (L * th) ≤
        (cfP p (fun i : Fin n => (spv i : ℝ)) (Real.sqrt (n : ℝ))).toReal := by
      exact le_trans hlow h3
    simpa [th] using hc'
  · simpa [th, y] using h4

end Submission.MagicVector

end
