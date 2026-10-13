/-
  WilVP : `Work.WilVP.ZeroFam Y` is `∅`-definable when `Y` is.

  `ZeroFam Y = {v : Fin (k+1) → ℝ | ∃ y, Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧ y = 0}`
  is, up to the substitution `y = 0`, the projection of `Y ∩ {z | z 1 = 0}` along the
  coordinate deletion `z ↦ z ∘ zfF k`, where `zfF k : Fin (k+1) → Fin (k+2)` skips the value `1`
  (the value coordinate) and maps `0 ↦ 0`, `j+1 ↦ j+2`.

  We realise this with `Set.Definable.exists_of_finite` in the ambient context
  `(Fin (k+1) ⊕ Fin 1) → ℝ` (`Fin (k+1)` = the free coordinates `(x, c)`, `Fin 1` = the quantified
  value coordinate `y`): the set

    `zfW k Y = {u | (u ∘ zfF k) ∈ Y} ∩ {u | u (Sum.inr 0) = 0}`

  is `∅`-definable (a preimage of `Y` along the finite relabelling `zfF k` intersected with the
  `∅`-definable condition "coordinate `Sum.inr 0` equals `0`", the constant `0` being an `LRc`-term
  built from `FirstOrder.Ring.zeroFunc`), and the finite existential quantifier over `Fin 1`
  produces exactly `ZeroFam Y` (via `zfComp`, which computes `Sum.elim v u ∘ zfF k`).
-/
import Mathlib
import Submission.Work.WilVP.Defs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilVP

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The constant `0` as an `LRc`-term -/

/-- The zero symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev lrcZero : LRc.Functions 0 := Sum.inl (Sum.inl FirstOrder.Ring.zeroFunc)

/-- The `LRc`-term representing the constant `0` on `ℝ`. -/
theorem realize_zeroTerm {α : Type*} (v : α → ℝ) :
    (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α)).realize v = (0 : ℝ) := by
  rw [Term.realize_func]
  have h : (fun k : Fin 0 => Term.realize v
      ((finZeroElim : Fin 0 → LRc.Term α) k)) = ![] := by
    funext k; exact k.elim0
  rw [h]; rfl

/-- The constant function `v ↦ 0` is a `∅`-definable function. -/
theorem definableFun_zero {α : Type*} :
    (∅ : Set ℝ).DefinableFun LRc (fun _ : α → ℝ => (0 : ℝ)) := by
  have h := FirstOrder.Language.Term.definableFun_realize (L := LRc) (M := ℝ) (α := α)
    (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α))
  rw [show (fun _ : α → ℝ => (0 : ℝ)) = fun v =>
      (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α)).realize v from
    funext (fun v => (realize_zeroTerm v).symm)]
  exact h

/-- The relation `v i = 0` is `∅`-definable. -/
theorem definable_eq_zero {α : Type*} (i : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i = 0} :=
  (Set.DefinableFun.proj LRc (i := i)).ofPred_eq (definableFun_zero (α := α))

/-! ## 2. The coordinate relabelling `Fin (k+2) → Fin (k+1) ⊕ Fin 1` avoiding the value slot -/

/-- The coordinate slots of `Y` in the ambient context `Fin (k+1) ⊕ Fin 1` for the tuple
`Fin.cons (v 0) (Fin.cons y (Fin.tail v))`: `0 ↦ v 0`, `1 ↦ y`, `j+2 ↦ v (j+1)`. -/
def zfF (k : ℕ) : Fin (k + 2) → Fin (k + 1) ⊕ Fin 1 :=
  Fin.cases (Sum.inl 0) (Fin.cases (Sum.inr 0) (fun j : Fin k => Sum.inl j.succ))

/-- The relabelling `zfF` computes the `Fin.cons`-tuple `(v 0, u 0, Fin.tail v)`. -/
theorem zfComp {k : ℕ} (v : Fin (k + 1) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim v u) ∘ (zfF k) = Fin.cons (v 0) (Fin.cons (u 0) (Fin.tail v)) := by
  funext i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · simp [zfF]
  · simp only [Function.comp_apply, zfF, Fin.cases_succ]
    refine Fin.cases ?_ (fun j => ?_) i₁ <;> simp [Fin.tail]

/-- The defining clauses of `ZeroFam`, read in the ambient context `(Fin (k+1) ⊕ Fin 1) → ℝ`
instead of the context `Fin (k+1) → ℝ` of `ZeroFam` itself. -/
def zfW (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set ((Fin (k + 1) ⊕ Fin 1) → ℝ) :=
  {u | (u ∘ zfF k) ∈ Y} ∩ {u | u (Sum.inr 0) = 0}

/-! ## 3. The zero family is definable -/

/-- The zero family `Work.WilVP.ZeroFam Y = {(x,c) | ∃ y, (x,y,c) ∈ Y ∧ y = 0}` is `∅`-definable
when `Y` is: same projection as `Work.WilVP.domFam_definable`, intersected with the definable
condition that the quantified value coordinate equals `0`. -/
theorem zeroFam_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilVP.ZeroFam Y) := by
  -- the ambient clause set is `∅`-definable
  have hS : (∅ : Set ℝ).Definable LRc (zfW k Y) := by
    rw [zfW]
    exact (Set.Definable.preimage_comp (zfF k) hY).inter (definable_eq_zero (Sum.inr 0))
  -- quantify the single extra coordinate `y` away
  have hex := Set.Definable.exists_of_finite (A := (∅ : Set ℝ)) (L := LRc)
    (α := Fin (k + 1)) (β := Fin 1) hS
  -- the projection is exactly `ZeroFam Y`
  have hset : {v : Fin (k + 1) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ zfW k Y} =
      Work.WilVP.ZeroFam Y := by
    ext v
    simp only [ZeroFam, zfW, Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inr]
    constructor
    · rintro ⟨u, h1u, h2u⟩
      exact ⟨u 0, by rwa [← zfComp (k := k) v u], h2u⟩
    · rintro ⟨y, hy, hy0⟩
      refine ⟨fun _ => y, ?_, ?_⟩
      · rw [zfComp (k := k) v (fun _ : Fin 1 => y)]
        simpa using hy
      · simpa using hy0
  rw [hset] at hex
  exact hex

end Work.WilVP
