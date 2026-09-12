import Mathlib
import Submission.Sec3Core
import Submission.Ell2Greedy

open Submission.Sec3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement (Tikhomirov 2020, Section 3, `prop: refinement`): spine

Deterministic core of `Prop refinement` (paper lines ~1221–1405).  This module
contains the function-level facts (independent of the randomness of `X_i`):

- `avgF` is convex-combination averaging: nonnegativity, sup-norm bound,
  preservation of the `N`-interval mass bound and of `ratioLip`;
- `Lemma l:aux 07395875092835` (`avgF_spike_shrink`): if `0 ≤ f ≤ 2H` and every
  `N`-interval contains at most `μN` points with `f ≥ H`, then every `N`-interval
  contains at most `μN/(√2−1)` points where the averaged function is `≥ √2H`.

Everything is deterministic (over the shifts `x : Fin ℓ → ℤ`); probability
enters only at the export layer (counting over tuples).

The `N`-interval `I₀(lo) := Icc lo (lo+N−1)` is `Ell2Greedy.I0`.
-/

namespace Submission.Refine

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- The number of points of the `N`-interval at `lo` where `H ≤ f`. -/
def spikeCnt (f : ℤ → ℝ) (H : ℝ) (lo : ℤ) (N : ℕ) : ℕ :=
  ((Ell2Greedy.I0 lo N).filter (fun t : ℤ => H ≤ f t)).card

/-- Spike counts of a translated function equal spike counts of the original
function on the translated interval. -/
lemma spikeCnt_add (f : ℤ → ℝ) (H : ℝ) (lo d : ℤ) (N : ℕ) :
    spikeCnt (fun t : ℤ => f (t + d)) H lo N = spikeCnt f H (lo + d) N := by
  classical
  let A : Finset ℤ := (Ell2Greedy.I0 lo N).filter (fun t : ℤ => H ≤ f (t + d))
  let B : Finset ℤ := (Ell2Greedy.I0 (lo + d) N).filter (fun s : ℤ => H ≤ f s)
  let g : ℤ → ℤ := fun t => t + d
  have hinj : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    omega
  have hAB : B = A.image g := by
    ext s
    constructor
    · intro hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_image]
      refine ⟨s - d, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · dsimp [A, Ell2Greedy.I0]
          rw [Finset.mem_Icc]
          have hs1 : s ∈ Ell2Greedy.I0 (lo + d) N := hs.1
          rw [Ell2Greedy.mem_I0] at hs1
          constructor <;> omega
        · have hsd : s = (s - d) + d := by omega
          rw [← hsd]
          exact hs.2
      · dsimp [g]
        omega
    · intro hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨t, ht, hst⟩
      rw [Finset.mem_filter]
      constructor
      · dsimp [B, Ell2Greedy.I0]
        rw [Finset.mem_Icc]
        have ht1 := (Finset.mem_filter.mp ht).1
        dsimp [A, Ell2Greedy.I0] at ht1
        rw [Finset.mem_Icc] at ht1
        dsimp [g] at hst
        subst s
        constructor <;> omega
      · have ht2 := (Finset.mem_filter.mp ht).2
        dsimp [g] at hst
        subst s
        exact ht2
  calc
    spikeCnt (fun t : ℤ => f (t + d)) H lo N
        = A.card := by rfl
    _ = (A.image g).card := by
          rw [Finset.card_image_of_injective A hinj]
    _ = B.card := by rw [hAB]
    _ = spikeCnt f H (lo + d) N := by rfl

/-- pointwise two-level bound: `f ≤ 2H` implies `f ≤ H·(1 + 1[H ≤ f])`. -/
lemma f_le_H_add_ind {f : ℤ → ℝ} {H : ℝ} (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
    (s : ℤ) : f s ≤ H * (1 + (if H ≤ f s then 1 else 0)) := by
  by_cases h : H ≤ f s
  · have hfs := hfsup s
    simp [h]
    nlinarith
  · simp [h]
    linarith [lt_of_not_ge h]

/-- The indicator-sum `P t` over subsets: probability (with weights `wB`) that
`f ≥ H` at the shifted point `t + d_B`. -/
def hitSum (f : ℤ → ℝ) (p : unitInterval) (H : ℝ) (ℓ : ℕ) (x : Fin ℓ → ℤ)
    (t : ℤ) : ℝ :=
  ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
    wB ℓ p B * (if H ≤ f (t + subSum x B) then 1 else 0)

/-- `hitSum` is nonnegative. -/
lemma hitSum_nonneg {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (t : ℤ) : 0 ≤ hitSum f p H ℓ x t := by
  dsimp [hitSum]
  apply Finset.sum_nonneg
  intro B hB
  by_cases h : H ≤ f (t + subSum x B)
  · simp [h]
    exact wB_nonneg ℓ p B
  · simp [h]

/-- upper bound on the average by `H·(1 + hitSum)` — the core estimate of
`Lemma l:aux 07395875092835`. -/
lemma avgF_le_H_add_hit {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (hfsup : ∀ t : ℤ, f t ≤ 2 * H) (t : ℤ) :
    avgF f p ℓ x t ≤ H * (1 + hitSum f p H ℓ x t) := by
  dsimp [avgF, hitSum]
  have hterm : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * f (t + subSum x B) ≤
        wB ℓ p B * (H * (1 + (if H ≤ f (t + subSum x B) then 1 else 0))) := by
    intro B hB
    exact mul_le_mul_of_nonneg_left (by
      by_cases h : H ≤ f (t + subSum x B)
      · simp [h]
        nlinarith [hfsup (t + subSum x B)]
      · simp [h]
        linarith [lt_of_not_ge h]) (wB_nonneg ℓ p B)
  have hsum := Finset.sum_le_sum hterm
  have hfac : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * (H * (1 + (if H ≤ f (t + subSum x B) then 1 else 0)))) =
      H * (1 + ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * (if H ≤ f (t + subSum x B) then 1 else 0)) := by
    calc
      (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * (H * (1 + (if H ≤ f (t + subSum x B) then 1 else 0))))
          = (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
              H * (wB ℓ p B * (1 + (if H ≤ f (t + subSum x B) then 1 else 0)))) := by
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ = H * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
              wB ℓ p B * (1 + (if H ≤ f (t + subSum x B) then 1 else 0))) := by
            rw [Finset.mul_sum]
      _ = H * ((∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) +
            (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
              wB ℓ p B * (if H ≤ f (t + subSum x B) then 1 else 0))) := by
            congr 1
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ = H * (1 + ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * (if H ≤ f (t + subSum x B) then 1 else 0)) := by
            have hw : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) = 1 :=
              sum_wB_eq_one ℓ p
            rw [hw]
  rw [hfac] at hsum
  exact hsum

/-- `√2 − 1 > 0`. -/
lemma sqrt2_sub_one_pos : 0 < Real.sqrt 2 - 1 := by
  have h : 1 < Real.sqrt 2 := by
    have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    simpa using hs
  linarith

/-- The count (as a real) of the points of `I₀ lo N` satisfying a decidable
predicate equals the indicator sum over the interval. -/
lemma sum_boole_I0 {N : ℕ} (lo : ℤ) (p : ℤ → Prop) [DecidablePred p] :
    (((Ell2Greedy.I0 lo N).filter p).card : ℝ) =
      ∑ t ∈ Ell2Greedy.I0 lo N, (if p t then (1 : ℝ) else 0) := by
  classical
  exact (Finset.sum_boole (p := p) (s := Ell2Greedy.I0 lo N)).symm

/-- `Lemma l:aux 07395875092835` (spike shrink): on every `N`-interval, the
number of points where the averaged function is `≥ √2H` is at most
`μN/(√2−1)`. -/
theorem avgF_spike_shrink {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N ℓ : ℕ}
    {x : Fin ℓ → ℤ}
    (hH0 : 0 < H) (hN1 : 1 ≤ N)
    (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
    (hsp : ∀ (lo : ℤ), (spikeCnt f H lo N : ℝ) ≤ μ * (N : ℝ)) :
    ∀ lo : ℤ,
      (spikeCnt (avgF f p ℓ x) (Real.sqrt 2 * H) lo N : ℝ) ≤
        μ * (N : ℝ) / (Real.sqrt 2 - 1) := by
  classical
  intro lo
  let A : Finset ℤ := Ell2Greedy.I0 lo N
  let w : ℝ := Real.sqrt 2 - 1
  have hw0 : 0 < w := by
    dsimp [w]
    exact sqrt2_sub_one_pos
  let big : ℤ → Prop := fun t => Real.sqrt 2 * H ≤ avgF f p ℓ x t
  -- every big point has hitSum at least `√2 − 1`:
  have hbig_lt : ∀ t : ℤ, big t → w ≤ hitSum f p H ℓ x t := by
    intro t ht
    have hu := avgF_le_H_add_hit (f := f) (p := p) (H := H) (ℓ := ℓ) (x := x) hfsup t
    have hle : H * Real.sqrt 2 ≤ H * (1 + hitSum f p H ℓ x t) := by
      nlinarith [ht, hu]
    have hdiv : Real.sqrt 2 ≤ 1 + hitSum f p H ℓ x t :=
      le_of_mul_le_mul_left hle hH0
    dsimp [w]
    nlinarith [hdiv]
  -- per-point indicator bound
  have hpts : ∀ t ∈ A, (if big t then (1 : ℝ) else 0) ≤ hitSum f p H ℓ x t / w := by
    intro t ht
    by_cases hb : big t
    · simp [hb]
      exact (le_div_iff₀ hw0).2 (by simpa using hbig_lt t hb)
    · simp [hb]
      exact div_nonneg (hitSum_nonneg (f := f) (p := p) (H := H) (ℓ := ℓ) (x := x) t)
        (le_of_lt hw0)
  have hpts_sum : (∑ t ∈ A, (if big t then (1 : ℝ) else 0)) ≤
      ∑ t ∈ A, hitSum f p H ℓ x t / w := by
    exact Finset.sum_le_sum (s := A) (fun t ht => hpts t ht)
  have hsum_div : (∑ t ∈ A, hitSum f p H ℓ x t / w) =
      (∑ t ∈ A, hitSum f p H ℓ x t) / w := by
    rw [Finset.sum_div]
  -- swap the two sums over `P_t`
  have hswap : (∑ t ∈ A, hitSum f p H ℓ x t) =
      ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * (∑ t ∈ A, (if H ≤ f (t + subSum x B) then 1 else 0)) := by
    dsimp [hitSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.mul_sum]
  -- per-subset: the inner count is a spike count of a translate, hence ≤ μN
  have hcnt_le : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * (∑ t ∈ A, (if H ≤ f (t + subSum x B) then 1 else 0)) ≤
        wB ℓ p B * (μ * (N : ℝ)) := by
    intro B hB
    exact mul_le_mul_of_nonneg_left (by
      have hinner : (∑ t ∈ A, (if H ≤ f (t + subSum x B) then 1 else 0)) =
          (spikeCnt f H (lo + subSum x B) N : ℝ) := by
        calc
          (∑ t ∈ A, (if H ≤ f (t + subSum x B) then 1 else 0))
              = (spikeCnt (fun t : ℤ => f (t + subSum x B)) H lo N : ℝ) := by
                dsimp [A]
                rw [← sum_boole_I0 lo (fun t : ℤ => H ≤ f (t + subSum x B))]
                rfl
          _ = (spikeCnt f H (lo + subSum x B) N : ℝ) := by
                exact_mod_cast spikeCnt_add (f := f) (H := H) (lo := lo) (d := subSum x B) (N := N)
      rw [hinner]
      exact hsp (lo + subSum x B)) (wB_nonneg ℓ p B)
  have hsum_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ℓ)).powerset) hcnt_le
  have hfacN : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * (μ * (N : ℝ))) = μ * (N : ℝ) := by
    calc
      (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * (μ * (N : ℝ)))
          = (μ * (N : ℝ)) * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ = μ * (N : ℝ) := by
            rw [sum_wB_eq_one ℓ p]
            ring
  have hPt_le : (∑ t ∈ A, hitSum f p H ℓ x t) ≤ μ * (N : ℝ) := by
    calc
      (∑ t ∈ A, hitSum f p H ℓ x t)
          = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
              wB ℓ p B * (∑ t ∈ A, (if H ≤ f (t + subSum x B) then 1 else 0)) := hswap
      _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * (μ * (N : ℝ)) := hsum_le
      _ = μ * (N : ℝ) := hfacN
  -- the count of big points:
  have hsc : (spikeCnt (avgF f p ℓ x) (Real.sqrt 2 * H) lo N : ℝ) =
      ∑ t ∈ A, (if big t then (1 : ℝ) else 0) := by
    rw [show (spikeCnt (avgF f p ℓ x) (Real.sqrt 2 * H) lo N : ℝ) =
        (((Ell2Greedy.I0 lo N).filter big).card : ℝ) by rfl]
    dsimp [A]
    exact sum_boole_I0 lo big
  calc
    (spikeCnt (avgF f p ℓ x) (Real.sqrt 2 * H) lo N : ℝ)
        = ∑ t ∈ A, (if big t then (1 : ℝ) else 0) := hsc
    _ ≤ ∑ t ∈ A, hitSum f p H ℓ x t / w := hpts_sum
    _ = (∑ t ∈ A, hitSum f p H ℓ x t) / w := hsum_div
    _ ≤ μ * (N : ℝ) / w := by
          exact div_le_div_of_nonneg_right hPt_le (le_of_lt hw0)
    _ = μ * (N : ℝ) / (Real.sqrt 2 - 1) := by
          dsimp [w]

/-- window sums of a translated function equal window sums of the original
function over the translated window (bijection `t ↦ t+d`). -/
lemma sum_translate_window_I0 {f : ℤ → ℝ} (a d : ℤ) (N : ℕ) :
    (∑ t ∈ Ell2Greedy.I0 a N, f (t + d)) = ∑ t ∈ Ell2Greedy.I0 (a + d) N, f t := by
  classical
  let g : ℤ → ℤ := fun t => t + d
  have hinj : Function.Injective g := by
    intro x y h
    dsimp [g] at h
    omega
  have himage : (Ell2Greedy.I0 a N).image g = Ell2Greedy.I0 (a + d) N := by
    ext s
    constructor
    · intro hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨t, ht, hst⟩
      dsimp [g] at hst
      rw [← hst]
      dsimp [Ell2Greedy.I0]
      rw [Finset.mem_Icc]
      have ht' : a ≤ t ∧ t ≤ a + (N : ℤ) - 1 := by
        dsimp [Ell2Greedy.I0] at ht
        exact Finset.mem_Icc.mp ht
      constructor <;> omega
    · intro hs
      dsimp [Ell2Greedy.I0] at hs
      rw [Finset.mem_Icc] at hs
      rw [Finset.mem_image]
      refine ⟨s - d, ?_, ?_⟩
      · dsimp [Ell2Greedy.I0]
        rw [Finset.mem_Icc]
        constructor <;> omega
      · dsimp [g]
        omega
  calc
    (∑ t ∈ Ell2Greedy.I0 a N, f (t + d))
        = ∑ t ∈ (Ell2Greedy.I0 a N).image g, f t := by
          rw [Finset.sum_image (g := g) (f := f) (s := Ell2Greedy.I0 a N) hinj.injOn]
    _ = ∑ t ∈ Ell2Greedy.I0 (a + d) N, f t := by
          rw [himage]

/-- the averaged function inherits the `N`-interval mass bound (translate-robust
hypothesis form). -/
lemma avgF_mass {f : ℤ → ℝ} {p : unitInterval} {M₀ : ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ} {N : ℕ}
    (hmass : ∀ (a d : ℤ), (∑ t ∈ Ell2Greedy.I0 a N, f (t + d)) ≤ M₀) :
    ∀ a : ℤ, (∑ t ∈ Ell2Greedy.I0 a N, avgF f p ℓ x t) ≤ M₀ := by
  classical
  intro a
  have hswap : (∑ t ∈ Ell2Greedy.I0 a N, avgF f p ℓ x t) =
      ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * (∑ t ∈ Ell2Greedy.I0 a N, f (t + subSum x B)) := by
    dsimp [avgF]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.mul_sum]
  have hbnd : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * (∑ t ∈ Ell2Greedy.I0 a N, f (t + subSum x B)) ≤
        wB ℓ p B * M₀ := by
    intro B hB
    exact mul_le_mul_of_nonneg_left (hmass a (subSum x B)) (wB_nonneg ℓ p B)
  have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ℓ)).powerset) hbnd
  have hfac : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * M₀) = M₀ := by
    calc
      (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * M₀)
          = M₀ * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ = M₀ := by
            rw [sum_wB_eq_one ℓ p]
            ring
  calc
    (∑ t ∈ Ell2Greedy.I0 a N, avgF f p ℓ x t)
        = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * (∑ t ∈ Ell2Greedy.I0 a N, f (t + subSum x B)) := hswap
    _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * M₀ := hle
    _ = M₀ := hfac

/-- the averaged function inherits the `N`-interval mass bound (plain form:
the mass bound holds for the function itself on every `N`-interval). -/
lemma avgF_mass_plain {f : ℤ → ℝ} {p : unitInterval} {M₀ : ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    {N : ℕ} (hmass : ∀ a : ℤ, (∑ t ∈ Ell2Greedy.I0 a N, f t) ≤ M₀) :
    ∀ a : ℤ, (∑ t ∈ Ell2Greedy.I0 a N, avgF f p ℓ x t) ≤ M₀ := by
  intro a
  exact avgF_mass (f := f) (p := p) (M₀ := M₀) (ℓ := ℓ) (x := x) (N := N)
    (fun a' d => by
      have htr := sum_translate_window_I0 (f := f) (a := a') (d := d) (N := N)
      -- Σ_{I0 a' N} f(t+d) = Σ_{I0 (a'+d) N} f
      rw [htr]
      exact hmass (a' + d)) a

/-- sup-norm bound: `f ≤ M` pointwise implies `avgF f p ℓ x ≤ M`. -/
lemma avgF_le_sup {f : ℤ → ℝ} {p : unitInterval} {M : ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (hfsup : ∀ t : ℤ, f t ≤ M) : ∀ t : ℤ, avgF f p ℓ x t ≤ M := by
  intro t
  dsimp [avgF]
  have hterm : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * f (t + subSum x B) ≤ wB ℓ p B * M := by
    intro B hB
    exact mul_le_mul_of_nonneg_left (hfsup (t + subSum x B)) (wB_nonneg ℓ p B)
  have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ℓ)).powerset) hterm
  have hfac : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * M) = M := by
    calc
      (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * M)
          = M * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ = M := by
            rw [sum_wB_eq_one ℓ p]
            ring
  rw [hfac] at hle
  exact hle

/-- a convex combination of two numbers bounded by `2H` which reaches the
level `(√2·p + 2(1−p))·H` (with `p ≤ 1/2`) forces both numbers to be at
least `√2·H` (phase-2 core step of Prop refinement). -/
lemma two_sides_of_high {A B H p : ℝ} (hA : A ≤ 2 * H) (hB : B ≤ 2 * H)
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2)
    (hh : (Real.sqrt 2 * p + 2 * (1 - p)) * H ≤ (1 - p) * A + p * B) :
    Real.sqrt 2 * H ≤ A ∧ Real.sqrt 2 * H ≤ B := by
  constructor
  · by_contra hnot
    have hlt : A < Real.sqrt 2 * H := lt_of_not_ge hnot
    have hmix : (1 - p) * A + p * B < (1 - p) * (Real.sqrt 2 * H) + p * (2 * H) := by
      -- A < √2H and B ≤ 2H, (1−p), p > 0
      have h1 : (1 - p) * A < (1 - p) * (Real.sqrt 2 * H) := by
        exact mul_lt_mul_of_pos_left hlt (by linarith)
      have h2 : p * B ≤ p * (2 * H) := by
        exact mul_le_mul_of_nonneg_left hB (le_of_lt hp0)
      linarith
    have hred : (1 - p) * (Real.sqrt 2 * H) + p * (2 * H) ≤
        (Real.sqrt 2 * p + 2 * (1 - p)) * H := by
      have hc : Real.sqrt 2 * (1 - p) + 2 * p ≤ Real.sqrt 2 * p + 2 * (1 - p) := by
        nlinarith [hp1]
      nlinarith
    nlinarith [hh, hmix, hred]
  · by_contra hnot
    have hlt : B < Real.sqrt 2 * H := lt_of_not_ge hnot
    have hmix : (1 - p) * A + p * B < (1 - p) * (2 * H) + p * (Real.sqrt 2 * H) := by
      have h1 : (1 - p) * A ≤ (1 - p) * (2 * H) := by
        exact mul_le_mul_of_nonneg_left hA (by linarith)
      have h2 : p * B < p * (Real.sqrt 2 * H) := by
        exact mul_lt_mul_of_pos_left hlt hp0
      linarith
    have hred : (1 - p) * (2 * H) + p * (Real.sqrt 2 * H) =
        (Real.sqrt 2 * p + 2 * (1 - p)) * H := by ring
    nlinarith [hh, hmix, hred]

/-- a convex combination of two quantities bounded by `M` is bounded by `M`
(pointwise version of the sup-norm non-increase of the mixing steps). -/
lemma mix_le_of_le {A B M p : ℝ} (hA : A ≤ M) (hB : B ≤ M)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (1 - p) * A + p * B ≤ M := by
  have h1 : (1 - p) * A ≤ (1 - p) * M := by
    exact mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : p * B ≤ p * M := by
    exact mul_le_mul_of_nonneg_left hB hp0
  nlinarith

end Submission.Refine


