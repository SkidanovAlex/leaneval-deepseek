import Mathlib
import Submission.Work.WilC4.InvFamDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-!
  `HalfB B₀ = B₀ ∪ {v | Fin.cons (2 * v 0) (fun i => v i.succ) ∈ B₀}` is the union of `B₀`
  with the pullback of `B₀` along the map `v ↦ Fin.cons (2 * v 0) (v ∘ Fin.succ)`.

  Both pieces are `∅`-definable in `LRc`: the first by hypothesis, the second because the pullback
  of a definable set along a definable map is definable (`Set.Definable.preimage_map`).  The map is
  definable because each of its coordinates is: the zeroth coordinate is `v 0 + v 0` (a term of the
  ring part of `LRc`, equal to `2 * v 0`), and the remaining coordinates are projections.
-/

/-- The addition symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev halfB_lrcAdd : LRc.Functions 2 := Sum.inl (Sum.inl FirstOrder.Ring.addFunc)

/-- The `LRc`-term `v i + v i` realizes to `v i + v i`. -/
theorem halfB_realize_addTerm {α : Type*} (v : α → ℝ) (i : α) :
    (Term.func halfB_lrcAdd (![Term.var i, Term.var i] : Fin 2 → LRc.Term α)).realize v =
      v i + v i := by
  rw [Term.realize_func]
  have h : (fun k : Fin 2 => Term.realize v
      ((![Term.var i, Term.var i] : Fin 2 → LRc.Term α) k)) = ![v i, v i] := by
    funext k; fin_cases k <;> rfl
  rw [h]; rfl

/-- The doubling map `v ↦ 2 * v 0` is a `∅`-definable function on `Fin (k+1) → ℝ`. -/
theorem halfB_definableFun_two_mul {k : ℕ} :
    (∅ : Set ℝ).DefinableFun LRc (fun v : Fin (k + 1) → ℝ => 2 * v 0) := by
  have h := Term.definableFun_realize (L := LRc) (M := ℝ) (α := Fin (k + 1))
    (Term.func halfB_lrcAdd
      (![Term.var (0 : Fin (k + 1)), Term.var (0 : Fin (k + 1))] :
        Fin 2 → LRc.Term (Fin (k + 1))))
  have heq : (Term.func halfB_lrcAdd
      (![Term.var (0 : Fin (k + 1)), Term.var (0 : Fin (k + 1))] :
        Fin 2 → LRc.Term (Fin (k + 1)))).realize
      = (fun v : Fin (k + 1) → ℝ => 2 * v 0) := by
    funext v
    rw [halfB_realize_addTerm]
    exact (two_mul (v 0)).symm
  rwa [heq] at h

/-- The map `v ↦ Fin.cons (2 * v 0) (v ∘ Fin.succ)` is a `∅`-definable map. -/
theorem halfB_definableMap_scale {k : ℕ} :
    (∅ : Set ℝ).DefinableMap LRc
      (fun v : Fin (k + 1) → ℝ => Fin.cons (2 * v 0) (fun i : Fin k => v i.succ)) := by
  intro i
  refine Fin.cases (motive := fun i => (∅ : Set ℝ).DefinableFun LRc
      (fun v : Fin (k + 1) → ℝ =>
        (Fin.cons (2 * v 0) (fun i : Fin k => v i.succ) : Fin (k + 1) → ℝ) i)) ?_ ?_ i
  · simpa using halfB_definableFun_two_mul (k := k)
  · intro j
    have h : (fun v : Fin (k + 1) → ℝ =>
        (Fin.cons (2 * v 0) (fun i : Fin k => v i.succ) : Fin (k + 1) → ℝ) (Fin.succ j)) =
        (fun v : Fin (k + 1) → ℝ => v j.succ) := by
      funext v; rw [Fin.cons_succ]
    rw [h]
    exact Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := j.succ)

theorem halfB_definable_b {k : ℕ} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.HalfB B₀) := by
  have hpre : (∅ : Set ℝ).Definable LRc
      ((fun v : Fin (k + 1) → ℝ => Fin.cons (2 * v 0) (fun i : Fin k => v i.succ)) ⁻¹' B₀) :=
    hB₀.preimage_map (halfB_definableMap_scale (k := k))
  have h : (∅ : Set ℝ).Definable LRc (HalfB B₀) := by
    rw [HalfB]
    exact hB₀.union hpre
  exact h

end Work.WilC4
