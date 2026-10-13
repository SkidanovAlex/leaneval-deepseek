/-
  WilC4/crit_unif : uniform finiteness of the fibres of a parameter-free `LRc`-definable
  family `B ⊆ ℝ^{k+1}` all of whose fibres are finite.

  `WilkiesDesign.CG.OMinModels` (o-minimality of every model of `TR`) yields, through the
  ultraproduct argument of `unifFinite_of_omin`, a uniform bound `N` on the number of
  order-convex components of the fibres of *every* parametric `LRc`-formula
  (`exists_alt_bound`).  For a *finite* set `S ⊆ ℝ`, having no alternating chain of length `N`
  (`AltChain N S`) is equivalent to `|S| ≤ N` (`encard_le_of_not_altChain`): if `S` had `N + 1`
  elements, its `N + 1` smallest points would be separated by their midpoints, which lie outside
  `S`.  Combining the two statements gives a uniform bound on the cardinalities of the fibres of
  `B`.

  The only bookkeeping is turning the parameter-free definability of `B` into a formula with `k`
  parameters and one variable: `Set.definable_iff_exists_formula_sum` gives a formula whose free
  variables are `↥∅ ⊕ Fin (k+1)` (the `↥∅` summand is empty), and `flattenVar k` relabels the
  coordinate `0` to the single variable and the coordinate `i+1` to the parameter `i`.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.exists_cover_of_not_altChain
import Submission.Work.WilC4.encard_le_of_not_altChain

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- Relabelling the `k + 1` free variables of a parameter-free `LRc`-formula into "`k` parameters
plus one variable": the coordinate `0` becomes the variable, the coordinate `i + 1` becomes the
parameter `i`.  (The `↥∅` summand of the source is empty, so its image is irrelevant.) -/
def flattenVar (k : ℕ) : (↥(∅ : Set ℝ) ⊕ Fin (k + 1)) → (Fin k ⊕ Fin 1) :=
  Sum.elim (fun _ => (Sum.inr 0 : Fin k ⊕ Fin 1))
    (Fin.cons (Sum.inr 0) (fun i : Fin k => (Sum.inl i : Fin k ⊕ Fin 1)))

@[simp] lemma flattenVar_inl (k : ℕ) (a : ↥(∅ : Set ℝ)) :
    flattenVar k (Sum.inl a) = (Sum.inr 0 : Fin k ⊕ Fin 1) := by
  simp [flattenVar]

@[simp] lemma flattenVar_inr_zero (k : ℕ) :
    flattenVar k (Sum.inr (0 : Fin (k + 1))) = (Sum.inr 0 : Fin k ⊕ Fin 1) := by
  simp [flattenVar]

@[simp] lemma flattenVar_inr_succ (k : ℕ) (i : Fin k) :
    flattenVar k (Sum.inr (Fin.succ i)) = (Sum.inl i : Fin k ⊕ Fin 1) := by
  simp [flattenVar]

/-- Composing a variable assignment `(c, t)` with the relabelling gives the assignment
`Fin.cons t c`. -/
lemma comp_flattenVar {k : ℕ} (c : Fin k → ℝ) (t : ℝ) :
    (Sum.elim c (fun _ : Fin 1 => t)) ∘ flattenVar k =
      Sum.elim (Subtype.val : ↥(∅ : Set ℝ) → ℝ) (Fin.cons t c) := by
  funext x
  rcases x with a | j
  · exact (Set.notMem_empty a.1 a.2).elim
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp

/-- Relabelling a parameter-free `LRc`-formula through `flattenVar k`: the fibre of the relabelled
formula at the parameter `c` is the set of `t` with `Fin.cons t c ∈ B`. -/
lemma relabel_realize {k : ℕ} {B : Set (Fin (k + 1) → ℝ)}
    {φ : LRc.Formula (↥(∅ : Set ℝ) ⊕ Fin (k + 1))}
    (hφ : B = {v | φ.Realize (Sum.elim (Subtype.val : ↥(∅ : Set ℝ) → ℝ) v)})
    (c : Fin k → ℝ) (t : ℝ) :
    (Formula.relabel (flattenVar k) φ).Realize (Sum.elim c (fun _ : Fin 1 => t)) ↔
      Fin.cons t c ∈ B := by
  have hmem : Fin.cons t c ∈ B ↔
      φ.Realize (Sum.elim (Subtype.val : ↥(∅ : Set ℝ) → ℝ) (Fin.cons t c)) := by
    rw [hφ]; simp
  have key : (Formula.relabel (flattenVar k) φ).Realize (Sum.elim c (fun _ : Fin 1 => t)) =
      φ.Realize (Sum.elim (Subtype.val : ↥(∅ : Set ℝ) → ℝ) (Fin.cons t c)) := by
    simp only [Formula.realize_relabel, comp_flattenVar]
  rw [key]
  exact hmem.symm

theorem crit_unif {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels) (B : Set (Fin (k + 1) → ℝ))
    (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (hfin : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.Finite) :
    ∃ N : ℕ, ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N := by
  obtain ⟨φ, hφ⟩ := (Set.definable_iff_exists_formula_sum (L := WilkiesDesign.CG.LRc)).mp hB
  obtain ⟨N, hN⟩ := exists_alt_bound hOM (Formula.relabel (flattenVar k) φ)
  refine ⟨N, fun c => ?_⟩
  have hset : {x : ℝ | Fin.cons x c ∈ B} =
      {t : ℝ | (Formula.relabel (flattenVar k) φ).Realize (Sum.elim c (fun _ : Fin 1 => t))} :=
    Set.ext fun t => (relabel_realize hφ c t).symm
  rw [hset]
  exact encard_le_of_not_altChain (hset ▸ hfin c) (hN c)

end Work.WilC4
