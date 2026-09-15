import Mathlib
import Submission.Work.LCFGvN
import Submission.Commons.Combinatorics.Additive.AP.sum_phiC_cover
import Submission.Commons.Combinatorics.Additive.Gowers.Jw_last_phiC
import Submission.Commons.Combinatorics.Additive.Gowers.Jw_zero_phiC
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The `p`-uniform generalised von Neumann theorem for an arbitrary shift set

This file generalises `Submission/Work/LCFGvN.lean` from the reparametrisation `phiZ`
(shift set `{0,1,…,k-1}` of indices `0,1,…,k-1`) to the general reparametrisation

`phiC c i y = ∑_t (1 - c i * (c (t+1))⁻¹) * y t`

for an injective `c : Fin k → ZMod p` with `c 0 = 0`.  This is what allows the *arbitrary index*
form of the generalised von Neumann theorem: applying the theorem below with the shift family
`c m = σ m - σ 0` (for a permutation `σ` with `σ 0 = j`) bounds the standard arithmetic-progression
sum in terms of `‖f j‖_{U^{k-1}}`.
-/

open Finset
open scoped BigOperators
open GVNW
open GVNgen
open Commons.NumberTheory.Sieve
open Commons.Combinatorics.Transference

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-! ## The `c`-weighted vertex arguments -/

/-- The `c`-weighted `σ`: `∑_j ω_j h_j` (written in a form which is definitionally equal to
the `ZMod p`-linear expression appearing in `sum_phiC_cover`). -/
noncomputable def wsigC {n : ℕ} (ω : Fin n → Bool) (h : Fin n → ZMod p) : ZMod p :=
  ∑ j, (if ω j then (1 : ZMod p) else 0) * h j

lemma wsigC_eq_wsig {n : ℕ} (ω : Fin n → Bool) (h : Fin n → ZMod p) :
    wsigC ω h = wsig ω h := by
  rw [wsigC, wsig]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp [hj]

/-- The `c`-weighted `τ`: `∑_j ω_j h_j / c_{j+1}`. -/
noncomputable def wtauC (k : ℕ) (c : Fin k → ZMod p) (ω : Fin (k-1) → Bool)
    (h : Fin (k-1) → ZMod p) : ZMod p :=
  ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
    * (c ⟨j.val + 1, by have := j.isLt; omega⟩)⁻¹

/-- The argument of the `i`-th half-weight of the `c`-weighted cube. -/
noncomputable def wArgC (k : ℕ) (c : Fin k → ZMod p) (x s : ZMod p) (h : Fin (k-1) → ZMod p)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : ZMod p :=
  x + wsigC ω h - c ⟨1 + i.val, by have := i.isLt; omega⟩ * (s + wtauC k c ω h)

/-- The unpaired `ν`-weight of the `c`-weighted cube. -/
noncomputable def wVsqC (k : ℕ) (c : Fin k → ZMod p) (ν : ZMod p → ℝ) (x s : ZMod p)
    (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, ∏ i : Fin (k-1), Real.sqrt (ν (wArgC k c x s h i ω))

/-- The paired `ν`-weight of the `c`-weighted cube. -/
noncomputable def wVC (k : ℕ) (c : Fin k → ZMod p) (ν : ZMod p → ℝ) (x s : ZMod p)
    (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ i : Fin (k-1), ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
    ν (wArgC k c x s h i ω)

/-- The `ω`-th vertex weight of the `c`-weighted cube. -/
noncomputable def wvtxC (k : ℕ) (c : Fin k → ZMod p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (x s : ZMod p) (h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) : ℝ :=
  g (x + wsigC ω h) * ∏ i : Fin (k-1), Real.sqrt (ν (wArgC k c x s h i ω))

/-- The `c`-weighted cube sum. -/
noncomputable def wcubeZC (k : ℕ) (c : Fin k → ZMod p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) : ℝ :=
  ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
    ∏ ω : Fin (k-1) → Bool, wvtxC k c g ν x s h ω

/-- The cube weight of the `c`-weighted cube. -/
noncomputable def wAC (k : ℕ) (ν : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, ν (x + wsigC ω h)

/-- The unweighted cube. -/
noncomputable def wGC (k : ℕ) (g : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, g (x + wsigC ω h)

/-- The averaged `ν`-weight `W(x,h) = 𝔼_s V(x,s,h)` of the `c`-weighted cube. -/
noncomputable def wWC (k : ℕ) (c : Fin k → ZMod p) (ν : ZMod p → ℝ) (x : ZMod p)
    (h : Fin (k-1) → ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ s : ZMod p, wVC k c ν x s h

/-! ## The pairing and the reduction to the averaged weight -/

/-- Expansion of `wArgC` as a linear combination of the digits of `ω`. -/
lemma wArgC_eq (k : ℕ) (c : Fin k → ZMod p) (x s : ZMod p) (h : Fin (k-1) → ZMod p)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    wArgC k c x s h i ω = x - c ⟨1 + i.val, by have := i.isLt; omega⟩ * s +
      ∑ j : Fin (k-1), ((if ω j then (1 : ZMod p) else 0) * h j)
        * (1 - c ⟨1 + i.val, by have := i.isLt; omega⟩
            * (c ⟨j.val + 1, by have := j.isLt; omega⟩)⁻¹) := by
  have h1 : wArgC k c x s h i ω = x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
      - c ⟨1 + i.val, by have := i.isLt; omega⟩
        * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
            * (c ⟨j.val + 1, by have := j.isLt; omega⟩)⁻¹) := by
    rw [wArgC, wsigC, wtauC]
  rw [h1, mul_add, Finset.mul_sum, sub_add_eq_sub_sub]
  rw [show x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
        - c ⟨1 + i.val, by have := i.isLt; omega⟩ * s
        - ∑ j : Fin (k-1), c ⟨1 + i.val, by have := i.isLt; omega⟩
              * (((if ω j then (1 : ZMod p) else 0) * h j)
                  * (c ⟨j.val + 1, by have := j.isLt; omega⟩)⁻¹)
      = (x - c ⟨1 + i.val, by have := i.isLt; omega⟩ * s)
        + (∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
          - ∑ j : Fin (k-1), c ⟨1 + i.val, by have := i.isLt; omega⟩
              * (((if ω j then (1 : ZMod p) else 0) * h j)
                  * (c ⟨j.val + 1, by have := j.isLt; omega⟩)⁻¹)) from by ring]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The `j = i` coefficient in `wArgC_eq` vanishes. -/
lemma wArgC_coeff_self (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (i : Fin (k-1)) :
    (1 : ZMod p) - c ⟨1 + i.val, by have := i.isLt; omega⟩
      * (c ⟨i.val + 1, by have := i.isLt; omega⟩)⁻¹ = 0 := by
  have hidx : (⟨1 + i.val, by have := i.isLt; omega⟩ : Fin k)
      = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hidx, sub_eq_zero]
  refine (mul_inv_cancel₀ (fun h => ?_)).symm
  have h0 : c ⟨i.val + 1, by have := i.isLt; omega⟩ = c ⟨0, hk⟩ := by rw [hc0, h]
  have h1 := hc h0
  simp at h1

lemma wArgC_update (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (x s : ZMod p) (h : Fin (k-1) → ZMod p) (i : Fin (k-1))
    (ω : Fin (k-1) → Bool) (b : Bool) :
    wArgC k c x s h i (Function.update ω i b) = wArgC k c x s h i ω := by
  rw [wArgC_eq, wArgC_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, wArgC_coeff_self k hk c hc hc0, mul_zero, mul_zero]
  · rw [Function.update_of_ne hj]

/-- **The square-root pairing** for the `c`-weighted cube. -/
lemma wVsqC_eq_wVC (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (x s : ZMod p) (h : Fin (k-1) → ZMod p) : wVsqC k c ν x s h = wVC k c ν x s h := by
  rw [wVsqC, wVC, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [prod_univ_bool_update i (fun ω => Real.sqrt (ν (wArgC k c x s h i ω)))
    (fun ω => by rw [wArgC_update k hk c hc hc0])]
  apply Finset.prod_congr rfl
  intro ω _
  rw [Real.sq_sqrt (hν _)]

/-- The product of the vertex weights factors into the cube of `g` and the `ν`-weight. -/
lemma prod_wvtxC (k : ℕ) (c : Fin k → ZMod p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (x s : ZMod p) (h : Fin (k-1) → ZMod p) :
    (∏ ω : Fin (k-1) → Bool, wvtxC k c g ν x s h ω)
      = (∏ ω : Fin (k-1) → Bool, g (x + wsigC ω h)) * wVsqC k c ν x s h := by
  have hpt : ∀ ω : Fin (k-1) → Bool, wvtxC k c g ν x s h ω
      = g (x + wsigC ω h) * ∏ i : Fin (k-1), Real.sqrt (ν (wArgC k c x s h i ω)) := fun _ => rfl
  rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_mul_distrib, wVsqC]

lemma wGC_abs_le_wAC (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ ν x)
    (x : ZMod p) (h : Fin (k-1) → ZMod p) : |wGC k g x h| ≤ wAC k ν x h := by
  rw [wGC, wAC, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro ω _; exact abs_nonneg _
  · intro ω _; exact hg _

/-- **The `c`-weighted cube in terms of the averaged weight `wWC`.** -/
lemma wcubeZC_eq (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x) :
    wcubeZC k c g ν = (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
      wGC k g x h * wWC k c ν x h := by
  have hpne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [wcubeZC]
  simp only [wGC, wWC]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  have hstep : ∀ s : ZMod p, (∏ ω : Fin (k-1) → Bool, wvtxC k c g ν x s h ω)
      = (∏ ω : Fin (k-1) → Bool, g (x + wsigC ω h)) * wVC k c ν x s h := by
    intro s; rw [prod_wvtxC, wVsqC_eq_wVC k hk c hc hc0 ν hν]
  rw [Finset.sum_congr rfl (fun s _ => hstep s), ← Finset.mul_sum]
  have harith : (p : ℝ) * ((∏ ω : Fin (k-1) → Bool, g (x + wsigC ω h))
        * ((p : ℝ)⁻¹ * ∑ s : ZMod p, wVC k c ν x s h))
      = (∏ ω : Fin (k-1) → Bool, g (x + wsigC ω h)) * ∑ s : ZMod p, wVC k c ν x s h := by
    field_simp
  linarith [harith]

lemma cubeSum_eq_sum_wGC (k : ℕ) (g : ZMod p → ℝ) :
    cubeSum (k-1) g = ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h := by
  rw [cubeSum]
  apply Finset.sum_congr rfl; intro h _
  apply Finset.sum_congr rfl; intro x _
  apply Finset.prod_congr rfl; intro ω _
  congr 1
  rw [wsigC_eq_wsig, wsig]

/-- **The `c`-weighted cube minus the unweighted cube.** -/
lemma wcubeZC_sub (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x) :
    wcubeZC k c g ν - (p : ℝ) * cubeSum (k-1) g
      = (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          wGC k g x h * (wWC k c ν x h - 1) := by
  rw [cubeSum_eq_sum_wGC, wcubeZC_eq k hk c hc hc0 g ν hν]
  have h1 : (p : ℝ) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h * wWC k c ν x h)
      - (p : ℝ) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h)
      = (p : ℝ) * ((∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h * wWC k c ν x h)
        - ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h) := by ring
  rw [h1, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro h _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

/-- **Green–Tao Lemma 5.4 for the `c`-weighted cube, quantitative form.** -/
lemma wcubeZC_close (k : ℕ) (hk : 0 < k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, hk⟩ = 0) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hg : ∀ x, |g x| ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h
        ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k c ν x h - 1)^2 ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ)) :
    |wcubeZC k c g ν - (p : ℝ) * cubeSum (k-1) g|
      ≤ (p : ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
          * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))) := by
  have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  have hA0nonneg : 0 ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h := by
    apply Finset.sum_nonneg; intro h _
    apply Finset.sum_nonneg; intro x _
    rw [wAC]
    exact Finset.prod_nonneg (fun ω _ => hν _)
  have hA2nonneg : 0 ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
      wAC k ν x h * (wWC k c ν x h - 1)^2 := by
    apply Finset.sum_nonneg; intro h _
    apply Finset.sum_nonneg; intro x _
    exact mul_nonneg (by rw [wAC]; exact Finset.prod_nonneg (fun ω _ => hν _)) (sq_nonneg _)
  have hR : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        |wGC k g x h * (wWC k c ν x h - 1)|)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p,
          |wGC k g q.2 q.1 * (wWC k c ν q.2 q.1 - 1)| :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      |wGC k g q.2 q.1 * (wWC k c ν q.2 q.1 - 1)|)).symm
  have hF : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k c ν x h - 1)^2)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p,
          wAC k ν q.2 q.1 * (wWC k c ν q.2 q.1 - 1)^2 :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      wAC k ν q.2 q.1 * (wWC k c ν q.2 q.1 - 1)^2)).symm
  have hG : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p, wAC k ν q.2 q.1 :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      wAC k ν q.2 q.1)).symm
  have hcs : (∑ q : (Fin (k-1) → ZMod p) × ZMod p,
        |wGC k g q.2 q.1 * (wWC k c ν q.2 q.1 - 1)|)^2
      ≤ (∑ q : (Fin (k-1) → ZMod p) × ZMod p,
            wAC k ν q.2 q.1 * (wWC k c ν q.2 q.1 - 1)^2)
        * ∑ q : (Fin (k-1) → ZMod p) × ZMod p, wAC k ν q.2 q.1 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset ((Fin (k-1) → ZMod p) × ZMod p))
      (r := fun q => |wGC k g q.2 q.1 * (wWC k c ν q.2 q.1 - 1)|)
      (f := fun q => wAC k ν q.2 q.1 * (wWC k c ν q.2 q.1 - 1)^2)
      (g := fun q => wAC k ν q.2 q.1) ?_ ?_ ?_
    · intro q _
      exact mul_nonneg (by rw [wAC]; exact Finset.prod_nonneg (fun ω _ => hν _)) (sq_nonneg _)
    · intro q _
      rw [wAC]; exact Finset.prod_nonneg (fun ω _ => hν _)
    · intro q _
      have h1 : |wGC k g q.2 q.1| ≤ wAC k ν q.2 q.1 := wGC_abs_le_wAC k g ν hg q.2 q.1
      have h2 : wGC k g q.2 q.1 ^ 2 ≤ wAC k ν q.2 q.1 ^ 2 := by
        calc wGC k g q.2 q.1 ^ 2 = |wGC k g q.2 q.1| ^ 2 := (sq_abs _).symm
          _ ≤ wAC k ν q.2 q.1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc |wGC k g q.2 q.1 * (wWC k c ν q.2 q.1 - 1)| ^ 2
          = wGC k g q.2 q.1 ^ 2 * (wWC k c ν q.2 q.1 - 1) ^ 2 := by
            rw [abs_mul, mul_pow]; simp only [sq_abs]
        _ ≤ wAC k ν q.2 q.1 ^ 2 * (wWC k c ν q.2 q.1 - 1) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = wAC k ν q.2 q.1 * (wWC k c ν q.2 q.1 - 1) ^ 2 * wAC k ν q.2 q.1 := by ring
  have hmain : |wcubeZC k c g ν - (p : ℝ) * cubeSum (k-1) g|
      ≤ (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          |wGC k g x h * (wWC k c ν x h - 1)| := by
    rw [wcubeZC_sub k hk c hc hc0 g ν hν, abs_mul, abs_of_nonneg hp0]
    apply mul_le_mul_of_nonneg_left _ hp0
    calc |∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wGC k g x h * (wWC k c ν x h - 1)|
        ≤ ∑ h : Fin (k-1) → ZMod p, |∑ x : ZMod p, wGC k g x h * (wWC k c ν x h - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
            |wGC k g x h * (wWC k c ν x h - 1)| :=
          Finset.sum_le_sum (fun h _ => Finset.abs_sum_le_sum_abs _ _)
  have hsqrt : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        |wGC k g x h * (wWC k c ν x h - 1)|)
      ≤ Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
        * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ)) := by
    have hcs' : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          |wGC k g x h * (wWC k c ν x h - 1)|)^2
        ≤ (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
              wAC k ν x h * (wWC k c ν x h - 1)^2)
          * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h := by
      rw [hR, hF, hG]; exact hcs
    refine le_trans (Real.le_sqrt_of_sq_le hcs') ?_
    rw [Real.sqrt_mul hA2nonneg]
    exact mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hA0)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact le_trans hmain (mul_le_mul_of_nonneg_left hsqrt hp0)


/-! ## The independence of `phiC c` from the peeled coordinate -/

/-- The reparametrisation `phiC c` (inline form), used throughout as `GVNW.Jw`'s `φ`. -/
noncomputable def phiC (k : ℕ) (c : Fin k → ZMod p) : Fin k → (Fin (k-1) → ZMod p) → ZMod p :=
  fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t

lemma phiC_apply (k : ℕ) (c : Fin k → ZMod p) (i : Fin k) (y : Fin (k-1) → ZMod p) :
    phiC (p := p) k c i y
      = ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t := rfl

lemma phiC_update (k : ℕ) (hk : 1 ≤ k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, by omega⟩ = 0) (m : ℕ) (hm : m + 2 ≤ k)
    (y : Fin (k-1) → ZMod p) (b : ZMod p) :
    phiC (p := p) k c ⟨m+1, by omega⟩ (Function.update y ⟨m, by omega⟩ b)
      = phiC (p := p) k c ⟨m+1, by omega⟩ y := by
  have hmk : m < k - 1 := by omega
  rw [phiC_apply, phiC_apply, ← sub_eq_zero]
  rw [show (∑ t : Fin (k-1), (1 - c ⟨m+1, by omega⟩
          * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * Function.update y ⟨m, hmk⟩ b t)
      - ∑ t : Fin (k-1), (1 - c ⟨m+1, by omega⟩
          * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t
      = ∑ t : Fin (k-1), (1 - c ⟨m+1, by omega⟩
          * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * (Function.update y ⟨m, hmk⟩ b t - y t)
      from by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t _
        ring]
  rw [Finset.sum_eq_zero]
  intro t _
  by_cases ht : t = ⟨m, hmk⟩
  · have htval : t.val = m := by rw [ht]
    have hidx : (⟨t.val + 1, by have := t.isLt; omega⟩ : Fin k) = ⟨m+1, by omega⟩ := by
      apply Fin.ext
      show t.val + 1 = m + 1
      rw [htval]
    have hcne : c ⟨m+1, by omega⟩ ≠ 0 := by
      intro h
      have h0 : (⟨m+1, by omega⟩ : Fin k) = ⟨0, by omega⟩ := hc (by rw [hc0, h])
      simp at h0
    have hz : (1 : ZMod p) - c ⟨m+1, by omega⟩
        * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹ = 0 := by
      rw [hidx, sub_eq_zero]
      exact (mul_inv_cancel₀ hcne).symm
    rw [hz, zero_mul]
  · have hupd : Function.update y ⟨m, hmk⟩ b t = y t := Function.update_of_ne ht b y
    rw [hupd, sub_self (y t), mul_zero]

/-- `phiC c ⟨m+1⟩` does not depend on the `m`-th coordinate. -/
lemma phiC_app_cons (k : ℕ) (hk : 1 ≤ k) (c : Fin k → ZMod p) (hc : Function.Injective c)
    (hc0 : c ⟨0, by omega⟩ = 0) (m : ℕ) (hm : m + 2 ≤ k)
    (u : Fin m → ZMod p) (z z' : ZMod p) (w : Fin (k-1-(m+1)) → ZMod p) :
    phiC (p := p) k c ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
      = phiC (p := p) k c ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w) := by
  have hmk : m < k - 1 := by omega
  have hy : app k (m+1) (by omega) (Fin.snoc u z) w
      = Function.update (app k (m+1) (by omega) (Fin.snoc u z') w) ⟨m, hmk⟩ z := by
    funext j
    by_cases hj : j = ⟨m, hmk⟩
    · subst hj
      rw [Function.update_self, app_apply, dif_pos (show m < m + 1 by omega)]
      rw [show (⟨m, by omega⟩ : Fin (m+1)) = Fin.last m from Fin.ext rfl]
      exact Fin.snoc_last (α := fun _ : Fin (m+1) => ZMod p) z u
    · rw [Function.update_of_ne hj]
      by_cases hlt : j.val < m + 1
      · rw [app_apply, app_apply, dif_pos hlt, dif_pos hlt]
        have hjm : j.val < m := by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
          · exact h
          · exact absurd (Fin.ext h) hj
        rw [show (⟨j.val, hlt⟩ : Fin (m+1)) = Fin.castSucc ⟨j.val, hjm⟩ from Fin.ext rfl,
          Fin.snoc_castSucc (α := fun _ : Fin (m+1) => ZMod p),
          Fin.snoc_castSucc (α := fun _ : Fin (m+1) => ZMod p)]
      · rw [app_apply, app_apply, dif_neg hlt, dif_neg hlt]
  rw [hy]
  exact phiC_update k hk c hc hc0 m hm _ z


/-! ## The generalised von Neumann theorem for the shift family `c` -/

/-- **The `p`-uniform generalised von Neumann theorem for the shift family `c`.** -/
theorem gvn_puniform_shift_of_averages {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    {ν : ZMod p → ℝ} (hνpos : ∀ x, 0 < ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hGvN : ∀ (f : Fin k → ZMod p → ℝ),
        GVNW.Jw (ZMod p) k (phiC (p:=p) k c) f ν 0 (by omega)
          = ((p:ℝ)^(k+1))⁻¹ * wcubeZC k c (f ⟨0, by omega⟩) ν)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h
        ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k c ν x h - 1)^2 ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
    (hPm : ∀ i ∈ Finset.range (k-1), Pm (ZMod p) k (phiC (p:=p) k c) ν i ≤ 1 + ε) :
    ∀ (f : Fin k → ZMod p → ℝ), (∀ i x, |f i x| ≤ ν x)
      → ∀ γ : ℝ, 0 ≤ γ → Unorm (k-1) (f ⟨0, by omega⟩) ≤ γ
      → |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r)|
        ≤ (p:ℝ)^2 * 16 * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  intro f hf γ hγ hU
  have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpne : (p:ℝ) ≠ 0 := ne_of_gt hppos
  have hν0 : ∀ x, 0 ≤ ν x := fun x => le_of_lt (hνpos x)
  set N : ℕ := 2 ^ (k-1) with hNdef
  have hNpos : (0:ℝ) < (N:ℝ) := by rw [hNdef]; positivity
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by rw [hNdef]; exact_mod_cast Nat.one_le_two_pow
  set U : ℝ := Unorm (k-1) (f ⟨0, by omega⟩) with hUdef
  have hU0 : 0 ≤ U := by rw [hUdef]; exact Unorm_nonneg _ (by omega) _
  set q : ℝ := (((2^k : ℕ)) : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, inv_le_one₀ (by positivity)]; exact_mod_cast Nat.one_le_two_pow
  -- the weighted Cauchy–Schwarz chain
  have hphieq : (phiC (p:=p) k c) = (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) := rfl
  rw [hphieq] at hGvN hPm
  have hchain := Jw_pow_le (X := ZMod p) (k := k) (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) f ν hf hνpos
    (fun m hm u z z' w => phiC_app_cons k (by omega) c hc hc0 m hm u z z' w) (by omega) (k-1) (by omega)
  rw [Commons.Combinatorics.Additive.Gowers.Jw_last_phiC (p:=p) hk hkp c hc hc0 f ν,
    hGvN f] at hchain
  -- `hchain : (p^{-2} A)^N ≤ (p^{-(k+1)} W) * PP`
  set A : ℝ := ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r) with hAdef
  set W : ℝ := wcubeZC k c (f ⟨0, by omega⟩) ν with hWdef
  set PP : ℝ := ∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) ν i)^(2^i) with hPPdef
  have hApow : 0 ≤ A^(2^(k-1)) := by
    obtain ⟨m, hm⟩ : ∃ m, 2^(k-1) = 2 * m :=
      ⟨2^(k-2), by rw [show 2^(k-1) = 2^(k-2+1) from by congr 1; omega, pow_succ]; ring⟩
    rw [hm, pow_mul]
    exact pow_nonneg (sq_nonneg A) m
  have hL : (((p:ℝ)^2)⁻¹ * A)^(2^(k-1)) = ((p:ℝ)^(2^k))⁻¹ * |A|^(2^(k-1)) := by
    rw [mul_pow, inv_pow, ← pow_mul, ← abs_pow, abs_of_nonneg hApow,
      show 2 * 2^(k-1) = 2^k from by rw [← pow_succ', Nat.sub_add_cancel (by omega)]]
  rw [hL] at hchain
  have hp2 : (0:ℝ) < (p:ℝ)^(2^k) := pow_pos hppos _
  have hmain1 : |A|^(2^(k-1))
      ≤ (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * PP) := by
    have h := mul_le_mul_of_nonneg_left hchain (le_of_lt hp2)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp2), one_mul] at h
  have hle : k + 1 ≤ 2^k := by
    have hlt := Nat.lt_two_pow_self (n := k)
    omega
  have hrw : (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * PP)
      = ((p:ℝ)^(2^k - (k+1)) * W) * PP := by
    rw [show (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * PP)
        = ((p:ℝ)^(2^k) * ((p:ℝ)^(k+1))⁻¹ * W) * PP from by ring]
    rw [show (p:ℝ)^(2^k) * ((p:ℝ)^(k+1))⁻¹ = (p:ℝ)^(2^k - (k+1)) from by
      rw [pow_sub₀ (p:ℝ) hpne hle]]
  rw [hrw] at hmain1
  rw [show 2^k - (k+1) = 2^k - k - 1 from by omega] at hmain1
  -- the cube comparison
  have hclose := wcubeZC_close k (by omega) c hc hc0 (f ⟨0, by omega⟩) ν hν0
    (fun x => hf _ x) hε0 hA0 hA2
  have hwc : wcubeZC k c (f ⟨0, by omega⟩) ν
      ≤ (p:ℝ) * cubeSum (k-1) (f ⟨0, by omega⟩)
        + (p:ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
            * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))) := by
    have h := abs_le.mp hclose
    linarith [h.2]
  have hcube : cubeSum (k-1) (f ⟨0, by omega⟩) = U ^ N * (p:ℝ)^k := by
    have hUp := Unorm_pow (G := ZMod p) (k-1) (by omega) (f ⟨0, by omega⟩)
    rw [ZMod.card, show k - 1 + 1 = k from by omega] at hUp
    rw [← hUdef, ← hNdef] at hUp
    rw [hUp, div_mul_cancel₀ _ (by positivity : ((p:ℝ)^k) ≠ 0)]
  have hPbound : PP ≤ (1 + ε) ^ (N - 1) := by
    rw [hPPdef]
    calc (∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) ν i)^(2^i))
        ≤ ∏ i ∈ Finset.range (k-1), (1 + ε)^(2^i) :=
          Finset.prod_le_prod
            (fun i _ => pow_nonneg (Pm_nonneg (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) ν hνpos i) _)
            (fun i hi => pow_le_pow_left₀ (Pm_nonneg (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) ν hνpos i) (hPm i hi) _)
      _ = (1 + ε) ^ (∑ i ∈ Finset.range (k-1), 2^i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = (1 + ε) ^ (N - 1) := by rw [hNdef, sum_range_two_pow]
  have hP0 : 0 ≤ PP := by
    rw [hPPdef]
    exact Finset.prod_nonneg (fun i _ =>
      pow_nonneg (Pm_nonneg (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val + 1, by have := t.isLt; omega⟩)⁻¹) * y t) ν hνpos i) _)
  have hpk : (p:ℝ)^(k-1) * (p:ℝ) = (p:ℝ)^k := by
    rw [← pow_succ, show k - 1 + 1 = k from by omega]
  have hS : Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ)) * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
      = (p:ℝ)^k * Real.sqrt (4 * ε * (1 + ε)) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))]
    rw [show 4 * ε * (p:ℝ)^(k-1) * (p:ℝ) * ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
        = (4 * ε * (1 + ε)) * ((p:ℝ)^k)^2 from by rw [← hpk]; ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * ε * (1 + ε)),
      Real.sqrt_sq (pow_nonneg hp0 k)]
    ring
  have hstep1 : |A| ^ N ≤ ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1)) := by
    rw [hAdef] at hmain1
    refine le_trans hmain1 ?_
    refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hwc (by positivity)) hPbound
      hP0 ?_) (le_of_eq ?_)
    · have hc0 : 0 ≤ cubeSum (k-1) (f ⟨0, by omega⟩) := cubeSum_nonneg (k-1) (by omega) _
      have hs0 : 0 ≤ Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
          * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      positivity
    rw [hWdef] at *
    rw [hcube, hS]
    rw [show (p:ℝ) * (U^N * (p:ℝ)^k) = (p:ℝ)^(k+1) * U^N from by rw [pow_succ]; ring,
      show (p:ℝ) * ((p:ℝ)^k * Real.sqrt (4*ε*(1+ε)))
          = (p:ℝ)^(k+1) * Real.sqrt (4*ε*(1+ε)) from by rw [pow_succ]; ring]
    have ha : (2^k - k - 1) + (k+1) = 2^k := by
      rw [Nat.sub_sub, Nat.sub_add_cancel (by have := Nat.lt_two_pow_self (n := k); omega)]
    have hpoweq : ((p:ℝ)^2)^N = (p:ℝ)^(2^k) := by
      rw [hNdef, ← pow_mul]
      congr 1
      conv_rhs => rw [show k = (k-1) + 1 from by omega, pow_succ]
      ring
    calc (p:ℝ)^(2^k-k-1) * ((p:ℝ)^(k+1) * U^N + (p:ℝ)^(k+1) * Real.sqrt (4*ε*(1+ε)))
            * (1+ε)^(N-1)
          = ((p:ℝ)^(2^k-k-1) * (p:ℝ)^(k+1)) * (U^N + Real.sqrt (4*ε*(1+ε)))
              * (1+ε)^(N-1) := by ring
        _ = (p:ℝ)^(2^k) * (U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1) := by
            rw [← pow_add, ha]
        _ = ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1)) := by
            rw [hpoweq]; ring
  -- the exponent `ε^{2^{-k}}` and `√ε`
  have hsqrtε : ε ^ (q * (N:ℝ)) = Real.sqrt ε := by
    have h2kn : q * (N:ℝ) = (2:ℝ)⁻¹ := by
      rw [hq, mul_comm, ← div_eq_mul_inv]
      simp only [hNdef, Nat.cast_pow, Nat.cast_ofNat]
      rw [show (2:ℝ)^k = (2:ℝ)^(k-1) * 2 from by
          calc (2:ℝ)^k = (2:ℝ)^((k-1)+1) := by
                congr 1
                omega
            _ = (2:ℝ)^(k-1) * 2 := pow_succ (2:ℝ) (k-1),
        ← div_div, div_self (by positivity : (2:ℝ)^(k-1) ≠ 0)]
      norm_num
    rw [h2kn, Real.sqrt_eq_rpow, show (2:ℝ)⁻¹ = 1/2 from by norm_num]
  have hεq0 : 0 ≤ ε ^ q := Real.rpow_nonneg hε0 q
  have hεqN : (ε ^ q) ^ N = Real.sqrt ε := by
    have h' : (ε ^ q) ^ N = ε ^ (q * (N:ℝ)) := by
      rw [← Real.rpow_natCast (ε ^ q) N]
      exact (Real.rpow_mul hε0 q (N:ℝ)).symm
    rw [h', hsqrtε]
  have hsqrt8 : Real.sqrt (4 * ε * (1 + ε)) ≤ 8 * Real.sqrt ε := by
    have h1 : (4 * ε * (1 + ε) : ℝ) ≤ (8 * Real.sqrt ε)^2 := by
      rw [mul_pow, Real.sq_sqrt hε0]; nlinarith [hε1, hε0]
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [Real.sqrt_sq (by positivity)]
  have h8N : (8:ℝ) ≤ 8^N := by
    calc (8:ℝ) = 8^1 := (pow_one 8).symm
      _ ≤ 8^N := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hN1 : (1:ℕ) ≤ N)
  have hεq_le : Real.sqrt (4 * ε * (1 + ε)) ≤ (8 * ε ^ q)^N := by
    rw [mul_pow]
    calc Real.sqrt (4 * ε * (1 + ε)) ≤ 8 * Real.sqrt ε := hsqrt8
      _ = 8 * (ε ^ q)^N := by rw [hεqN]
      _ ≤ 8^N * (ε ^ q)^N := mul_le_mul_of_nonneg_right h8N (pow_nonneg hεq0 N)
  have hsum : U^N + Real.sqrt (4 * ε * (1 + ε)) ≤ (8 * (γ + ε ^ q))^N := by
    have h1 : U^N ≤ (8 * γ)^N :=
      le_trans (pow_le_pow_left₀ hU0 hU N) (pow_le_pow_left₀ hγ (by linarith) N)
    refine le_trans (add_le_add h1 hεq_le) ?_
    rw [show (8 * (γ + ε ^ q)) = 8 * γ + 8 * ε ^ q from by ring]
    exact add_pow_ge_of_nonneg (by positivity) (by positivity) (by exact_mod_cast hN1)
  have hfac : (1 + ε)^(N - 1) ≤ 2^N := by
    refine le_trans (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + ε) (Nat.sub_le _ _)) ?_
    exact pow_le_pow_left₀ (by linarith) (by linarith) N
  have hfinal : ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1))
      ≤ ((p:ℝ)^2 * 16 * (γ + ε^q))^N := by
    have h1 : (U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1) ≤ (8 * (γ + ε^q))^N * 2^N :=
      mul_le_mul hsum hfac (by positivity) (by positivity)
    have h2 : (8 * (γ + ε ^ q))^N * 2^N = (16:ℝ)^N * (γ + ε ^ q)^N := by
      rw [← mul_pow (8 * (γ + ε ^ q)) 2 N, ← mul_pow (16:ℝ) (γ + ε ^ q) N]
      congr 1
      ring
    calc ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1))
        ≤ ((p:ℝ)^2)^N * ((8 * (γ + ε^q))^N * 2^N) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((p:ℝ)^2)^N * ((16:ℝ)^N * (γ + ε^q)^N) := by rw [h2]
      _ = ((p:ℝ)^2 * 16 * (γ + ε^q))^N := by rw [mul_pow, mul_pow]; ring
  have hZ : |A| ^ N ≤ ((p:ℝ)^2 * 16 * (γ + ε^q))^N := le_trans hstep1 hfinal
  have hN0 : N ≠ 0 := by
    have : 1 ≤ N := by exact_mod_cast hN1
    omega
  rw [hAdef]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) hN0).mp hZ


/-- **The `p`-uniform generalised von Neumann theorem for the shift family `c`**, with the
endpoint of the weighted Cauchy–Schwarz chain discharged. -/
theorem gvn_puniform_shift {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    {ν : ZMod p → ℝ} (hνpos : ∀ x, 0 < ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h
        ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k c ν x h - 1)^2 ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
    (hPm : ∀ i ∈ Finset.range (k-1), Pm (ZMod p) k (phiC (p:=p) k c) ν i ≤ 1 + ε) :
    ∀ (f : Fin k → ZMod p → ℝ), (∀ i x, |f i x| ≤ ν x)
      → ∀ γ : ℝ, 0 ≤ γ → Unorm (k-1) (f ⟨0, by omega⟩) ≤ γ
      → |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r)|
        ≤ (p:ℝ)^2 * 16 * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  refine gvn_puniform_shift_of_averages hk hkp c hc hc0 hνpos hε0 hε1 ?_ hA0 hA2 hPm
  intro f
  rw [show (phiC (p:=p) k c)
      = fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by have := t.isLt; omega⟩)⁻¹) * y t
      from rfl]
  rw [Commons.Combinatorics.Additive.Gowers.Jw_zero_phiC (p:=p) hk hkp c hc hc0 f ν]
  show ((p:ℝ)^(k+1))⁻¹ * wcubeZC k c (f ⟨0, by omega⟩) ν = _
  rw [wcubeZC]

/-- **The `p`-uniform generalised von Neumann theorem with the Gowers-uniform factor in an
arbitrary position.**  For any permutation `σ : Fin k ≃ Fin k` the standard `k`-term
arithmetic-progression sum is bounded by `p² · 16 · (‖f (σ 0)‖_{U^{k-1}} + ε^{2^{-k}})`. -/
theorem gvn_puniform_kept {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) {ν : ZMod p → ℝ}
    (hνpos : ∀ x, 0 < ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (σ : Fin k ≃ Fin k) (hk0 : 0 < k)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h
        ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k (fun m => (((σ m).val : ℕ) : ZMod p)
            - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) ν x h - 1)^2
          ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
    (hPm : ∀ i ∈ Finset.range (k-1),
        Pm (ZMod p) k (phiC (p:=p) k (fun m => (((σ m).val : ℕ) : ZMod p)
            - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p))) ν i ≤ 1 + ε)
    (f : Fin k → ZMod p → ℝ) (hf : ∀ i x, |f i x| ≤ ν x) (γ : ℝ) (hγ : 0 ≤ γ)
    (hU : Unorm (k-1) (f (σ ⟨0, hk0⟩)) ≤ γ) :
    |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r)|
      ≤ (p:ℝ)^2 * 16 * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  classical
  set c : Fin k → ZMod p := fun m => (((σ m).val : ℕ) : ZMod p) - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)
    with hcdef
  set F : Fin k → ZMod p → ℝ := fun m => f (σ m) with hFdef
  have hc0 : c ⟨0, hk0⟩ = 0 := by
    simp only [hcdef]; ring
  have hc : Function.Injective c := by
    intro a b hab
    simp only [hcdef] at hab
    have h1 : (((σ a).val : ℕ) : ZMod p) = (((σ b).val : ℕ) : ZMod p) := by
      have h := sub_eq_sub_iff_add_eq_add.mp hab
      simpa using h
    have h2 : (σ a).val = (σ b).val := by
      have ha : (σ a).val < p := by have := (σ a).isLt; omega
      have hb : (σ b).val < p := by have := (σ b).isLt; omega
      have hh := congrArg ZMod.val h1
      rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hh
      exact hh
    exact σ.injective (Fin.ext h2)
  have hF : ∀ i x, |F i x| ≤ ν x := fun i x => hf _ x
  have hFU : Unorm (k-1) (F ⟨0, by omega⟩) ≤ γ := hU
  have h1 : ∀ (x r : ZMod p), (∏ m : Fin k, F m (x + c m * r))
      = ∏ i : Fin k, f i (x + (((i : ℕ) : ZMod p) - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) * r) := by
    intro x r
    refine Fintype.prod_equiv σ (fun m => F m (x + c m * r))
      (fun i => f i (x + (((i : ℕ) : ZMod p) - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) * r)) ?_
    intro m
    simp only [hFdef, hcdef]
  have h2 : ∀ r : ZMod p, (∑ x : ZMod p,
        ∏ i : Fin k, f i (x + (((i : ℕ) : ZMod p) - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) * r))
      = ∑ x : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r) := by
    intro r
    refine Finset.sum_bij (fun x _ => x - ((((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) * r) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_univ _
    · intro x₁ _ x₂ _ h; simpa using h
    · intro y _; exact ⟨y + ((((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) * r, Finset.mem_univ _, by ring⟩
    · intro x _
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
  have hL : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r))
      = ∑ r : ZMod p, ∑ x : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r) :=
    Finset.sum_comm
  have hR : (∑ x : ZMod p, ∑ r : ZMod p, ∏ m : Fin k, F m (x + c m * r))
      = ∑ r : ZMod p, ∑ x : ZMod p, ∏ m : Fin k, F m (x + c m * r) :=
    Finset.sum_comm
  have hmain := gvn_puniform_shift hk hkp c hc hc0 hνpos hε0 hε1 hA0 hA2 hPm F hF γ hγ hFU
  have hsum : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r))
      = ∑ x : ZMod p, ∑ r : ZMod p, ∏ m : Fin k, F m (x + c m * r) := by
    rw [hL, hR]
    apply Finset.sum_congr rfl; intro r _
    rw [← h2 r]
    apply Finset.sum_congr rfl; intro x _
    exact (h1 x r).symm
  rw [hsum]
  exact hmain

end GTTrans
