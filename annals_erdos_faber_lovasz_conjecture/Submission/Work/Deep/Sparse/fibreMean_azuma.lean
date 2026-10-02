/-
# Concentration around the fibre mean: McDiarmid's inequality for the uniform colouring

The uniform colouring `f : V → Fin k` (`colSpace`, `Submission/Work/Deep/Sparse/ProbBasic.lean`)
is a product measure, and for a finite set `A` of vertices the *fibre mean*

`fibreMean A Y f`  (`Submission/Work/Deep/Sparse/SliceDefs.lean`)

is the average of `Y` over all recolourings of the `A`-coordinates of `f`, i.e. the conditional
expectation of `Y` given the colours outside `A`.

`Work.Deep.Sparse.azuma_finSpace` proves McDiarmid's bounded-differences inequality around the
*global* mean `(colSpace k).expect Y`.  The present module proves the sharper *fibrewise* form
needed by the concentration proof of the naive colouring procedure: if changing the colour of a
vertex `u ∈ A` moves `Y` by at most `c u`, then

`Pr[ t < |Y f - fibreMean A Y f| ] ≤ 2 exp(-2t² / ∑_{u ∈ A} c u²)`.

The proof is the standard one and has two ingredients.

* **Fibrewise Azuma.**  Fixing the colours outside `A` and redrawing the colours on `A`
  uniformly, `A ↦ Y (graft A · f)` satisfies the hypotheses of `azuma_finSpace` on the smaller
  sample space `↥A → Fin k`, with the same variance proxy `∑_{u ∈ A} c u²` (`key` below).
  Note that no Lipschitz hypothesis on the vertices outside `A` is needed: `fibreMean` absorbs
  whatever `Y` does there.
* **Disintegration.**  Averaging the fibrewise bound over the outside colours.  The identity
  `prob_disintegrate` expresses the probability of an event as the weighted average of its
  conditional probabilities over the fibres: drawing `f : V → Fin k` uniformly and then redrawing
  its `A`-coordinates is the same as drawing `f` uniformly.  Formally, the map
  `(f₀, g) ↦ (graft A g f₀, f₀|_A)` is an involution of `(V → Fin k) × (↥A → Fin k)`
  (`disintSwap`), which transports the sum over `(f₀, g)` of the indicator of the event
  `graft A g f₀ ∈ EE` to the sum over `(h, gA)` of the indicator of `h ∈ EE`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.azuma_finSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators
open Classical

namespace Work.Deep.Sparse

/-! ## 1. Grafting one's own restriction, and the fibre-swap involution -/

section Basic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Grafting onto `f` the restriction of `f` to `A` returns `f`. -/
lemma graft_restrict_self {k : ℕ} (A : Finset V) (f : V → Fin k) :
    graft A (fun a : ↥A => f a.val) f = f := by
  funext u
  by_cases h : u ∈ A
  · rw [graft_apply_of_mem _ _ h]
  · rw [graft_apply_of_notMem _ _ h]

/-- The restriction of a grafted colouring to `A` is the grafted family. -/
lemma graft_restrict_eq {k : ℕ} (A : Finset V) (g : ↥A → Fin k) (f : V → Fin k) :
    (fun a : ↥A => (graft A g f) a.val) = g := by
  funext a; rw [graft_apply_of_mem _ _ a.2]

/-- Grafting `f`'s own restriction onto `graft A g f` returns `f`. -/
lemma graft_self_graft {k : ℕ} (A : Finset V) (g : ↥A → Fin k) (f : V → Fin k) :
    graft A (fun a : ↥A => f a.val) (graft A g f) = f := by
  rw [graft_graft, graft_restrict_self]

/-- The involution of `(V → Fin k) × (↥A → Fin k)` which replaces the `A`-coordinates of the
first component by the second, recording the old `A`-coordinates in the second slot. -/
noncomputable def disintSwap {k : ℕ} (A : Finset V) :
    ((V → Fin k) × (↥A → Fin k)) ≃ ((V → Fin k) × (↥A → Fin k)) where
  toFun p := (graft A p.2 p.1, fun a : ↥A => p.1 a.val)
  invFun p := (graft A p.2 p.1, fun a : ↥A => p.1 a.val)
  left_inv p := by
    show (graft A (fun a : ↥A => p.1 a.val) (graft A p.2 p.1),
        (fun a : ↥A => (graft A p.2 p.1) a.val)) = p
    rw [graft_self_graft, graft_restrict_eq]
  right_inv p := by
    show (graft A (fun a : ↥A => p.1 a.val) (graft A p.2 p.1),
        (fun a : ↥A => (graft A p.2 p.1) a.val)) = p
    rw [graft_self_graft, graft_restrict_eq]

end Basic

/-! ## 2. Disintegrating the uniform colouring over the fibres -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)]

/-- The probability of an event under the uniform colouring is the sum of the constant weights
of its points. -/
theorem prob_eq_sum_ite (EE : Set (V → Fin k)) :
    (colSpace (V := V) k).prob EE
      = ∑ f : V → Fin k, (if f ∈ EE then (Fintype.card (V → Fin k) : ℝ)⁻¹ else 0) := by
  rw [FinSpace.prob]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : f ∈ EE
  · rw [Set.indicator_of_mem h, if_pos h, colSpace_mass]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- **Disintegration of the uniform colouring over the fibres of the restriction to `Aᶜ`.**

Drawing `f : V → Fin k` uniformly and then redrawing its colours on `A` is the same as drawing
`f` uniformly, so the probability of an event is the average of its conditional probabilities in
the fibres: `Pr[EE] = ∑ f₀, Pr[f₀] · Pr[graft A g f₀ ∈ EE]` (the second draw being uniform on
`↥A → Fin k`). -/
theorem prob_disintegrate (A : Finset V) [Nonempty (↥A → Fin k)] (EE : Set (V → Fin k)) :
    (colSpace (V := V) k).prob EE
      = ∑ f₀ : V → Fin k, (colSpace (V := V) k).mass f₀ *
          (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | graft A g f₀ ∈ EE} := by
  have hMne : (Fintype.card (↥A → Fin k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  -- Both sides as explicit sums over the constant weights.
  have h1 : (∑ f₀ : V → Fin k, (colSpace (V := V) k).mass f₀ *
        (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | graft A g f₀ ∈ EE})
      = ∑ p : (V → Fin k) × (↥A → Fin k),
          (if graft A p.2 p.1 ∈ EE
            then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹
            else 0) := by
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f₀ _ => ?_
    rw [prob_eq_sum_ite (V := ↥A) {g : ↥A → Fin k | graft A g f₀ ∈ EE},
      show (colSpace (V := V) k).mass f₀ = (Fintype.card (V → Fin k) : ℝ)⁻¹ from by
        rw [colSpace_mass], Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : graft A g f₀ ∈ EE <;> simp [hg]
  -- The swap of the two draws is a bijection of the index set.
  have h2 : (∑ p : (V → Fin k) × (↥A → Fin k),
          (if graft A p.2 p.1 ∈ EE
            then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹
            else 0))
      = ∑ q : (V → Fin k) × (↥A → Fin k),
          (if q.1 ∈ EE
            then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹
            else 0) :=
    Fintype.sum_equiv (disintSwap A)
      (fun p : (V → Fin k) × (↥A → Fin k) =>
        (if graft A p.2 p.1 ∈ EE
          then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹ else 0))
      (fun q : (V → Fin k) × (↥A → Fin k) =>
        (if q.1 ∈ EE
          then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹ else 0))
      (fun p => rfl)
  -- Summing the constant weight `M⁻¹` over the `M` redrawings cancels it.
  have h3 : (∑ q : (V → Fin k) × (↥A → Fin k),
          (if q.1 ∈ EE
            then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹
            else 0))
      = ∑ f : V → Fin k, (if f ∈ EE then (Fintype.card (V → Fin k) : ℝ)⁻¹ else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ => ?_
    show (∑ _y : ↥A → Fin k, (if h ∈ EE
          then (Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹
          else 0)) = (if h ∈ EE then (Fintype.card (V → Fin k) : ℝ)⁻¹ else 0)
    by_cases hh : h ∈ EE
    · rw [if_pos hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, if_pos hh]
      calc (Fintype.card (↥A → Fin k) : ℝ)
            * ((Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (↥A → Fin k) : ℝ)⁻¹)
          = (Fintype.card (V → Fin k) : ℝ)⁻¹
            * ((Fintype.card (↥A → Fin k) : ℝ) * (Fintype.card (↥A → Fin k) : ℝ)⁻¹) := by
            ring
        _ = (Fintype.card (V → Fin k) : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hMne, mul_one]
    · rw [if_neg hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, if_neg hh]
      ring
  calc (colSpace (V := V) k).prob EE
      = ∑ f : V → Fin k, (if f ∈ EE then (Fintype.card (V → Fin k) : ℝ)⁻¹ else 0) :=
        prob_eq_sum_ite EE
    _ = _ := h3.symm
    _ = _ := h2.symm
    _ = _ := h1.symm

end Main

/-! ## 3. The fibrewise bounded-differences inequality -/

/-- **McDiarmid's inequality around the fibre mean.**  If changing the colour of a vertex
`u ∈ A` moves `Y` by at most `c u ≥ 0`, then `Y` is concentrated around the mean of `Y` over
the fibre through the current colouring: for `t ≥ 0`,
`Pr[ t < |Y f - fibreMean A Y f| ] ≤ 2 exp(-2t² / ∑_{u ∈ A} c u²)`.

The vertices outside `A` need no Lipschitz hypothesis: the fibre mean absorbs the dependence
of `Y` on them. -/
theorem fibreMean_azuma {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)] (A : Finset V) (Y : (V → Fin k) → ℝ)
    (c : V → ℝ) (hc : ∀ u ∈ A, 0 ≤ c u)
    (hlip : ∀ u ∈ A, ∀ (f : V → Fin k) (x : Fin k),
      |Y (Function.update f u x) - Y f| ≤ c u) :
    ∀ t : ℝ, 0 ≤ t →
      (colSpace (V := V) k).prob {f : V → Fin k | t < |Y f - fibreMean A Y f|}
        ≤ 2 * Real.exp (-(2 * t ^ 2) / ∑ u ∈ A, (c u) ^ 2) := by
  intro t ht
  -- The fibre `↥A → Fin k` is nonempty (restrict any colouring of `V`).
  haveI hneA : Nonempty (↥A → Fin k) :=
    ⟨fun a => (Classical.arbitrary (V → Fin k)) a.val⟩
  -- **Fibrewise Azuma.**  Fixing the colours outside `A`, the redrawing of the colours on `A`
  -- is a uniform colouring of `↥A`, to which `azuma_finSpace` applies.
  have key : ∀ f₀ : V → Fin k,
      (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | t < |Y (graft A g f₀) - fibreMean A Y f₀|}
        ≤ 2 * Real.exp (-(2 * t ^ 2) / ∑ u ∈ A, (c u) ^ 2) := by
    intro f₀
    have hX : (colSpace (V := ↥A) k).expect (fun g : ↥A → Fin k => Y (graft A g f₀))
        = fibreMean A Y f₀ := by
      rw [FinSpace.expect, colSpace_mass, ← Finset.mul_sum, fibreMean, one_div,
        card_colSpace, Fintype.card_coe, Nat.cast_pow]
    have hzip := azuma_finSpace (V := ↥A) (k := k)
      (X := fun g : ↥A → Fin k => Y (graft A g f₀))
      (c := fun a : ↥A => c a.val) (fun a => hc a.val a.2)
      (fun a g x => by
        have h1 : Y (graft A (Function.update g a x) f₀)
            = Y (Function.update (graft A g f₀) a.val x) := by rw [graft_update]
        rw [h1]
        exact hlip a.val a.2 (graft A g f₀) x) t ht
    rw [hX] at hzip
    rw [Finset.sum_coe_sort A (fun u => (c u) ^ 2)] at hzip
    exact hzip
  -- **Disintegration and averaging.**
  rw [prob_disintegrate A {f : V → Fin k | t < |Y f - fibreMean A Y f|}]
  calc (∑ f₀ : V → Fin k, (colSpace (V := V) k).mass f₀ *
        (colSpace (V := ↥A) k).prob
          {g : ↥A → Fin k | t < |Y (graft A g f₀) - fibreMean A Y (graft A g f₀)|})
      = ∑ f₀ : V → Fin k, (colSpace (V := V) k).mass f₀ *
        (colSpace (V := ↥A) k).prob
          {g : ↥A → Fin k | t < |Y (graft A g f₀) - fibreMean A Y f₀|} := by
        refine Finset.sum_congr rfl fun f₀ _ => ?_
        have hs : {g : ↥A → Fin k | t < |Y (graft A g f₀) - fibreMean A Y (graft A g f₀)|}
            = {g : ↥A → Fin k | t < |Y (graft A g f₀) - fibreMean A Y f₀|} := by
          ext g
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, fibreMean_graft]
        rw [hs]
    _ ≤ ∑ f₀ : V → Fin k, (colSpace (V := V) k).mass f₀ *
          (2 * Real.exp (-(2 * t ^ 2) / ∑ u ∈ A, (c u) ^ 2)) :=
        Finset.sum_le_sum fun f₀ _ =>
          mul_le_mul_of_nonneg_left (key f₀) (FinSpace.mass_nonneg _ _)
    _ = 2 * Real.exp (-(2 * t ^ 2) / ∑ u ∈ A, (c u) ^ 2) := by
        rw [← Finset.sum_mul, FinSpace.mass_sum, one_mul]

end Work.Deep.Sparse
