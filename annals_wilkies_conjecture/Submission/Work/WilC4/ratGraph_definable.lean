/-
  WilC4/ratGraph_definable : the graph of the doubling ratio of a `∅`-definable family of graphs is
  `∅`-definable.

  `Route.RatGraph Y` (`Submission/Work/WilC4/ULPMRoute.lean`) is the family of graphs whose fibre
  over `(x, c)` describes the doubling ratio `w = f_c(2x)/f_c(x)` of the fibre `f_c` of `Y`:

    `v ∈ RatGraph Y ↔ ∃ y y', Fin.cons (v 0) (Fin.cons y c) ∈ Y ∧ y ≠ 0 ∧
                              Fin.cons (2 * v 0) (Fin.cons y' c) ∈ Y ∧ v 1 * y = y'`,
  with `c := fun j : Fin k => v j.succ.succ`.

  The proof is a definability computation.  Writing `α := Fin (k+2) ⊕ Fin 3`, the existential
  variables `y, y', 2 * v 0` are placed in the `Fin 3` block of the ambient type `α → ℝ`, and the
  three reindexings

  * `u ↦ (u ∘ rgF₁ k) ∈ Y`      (`y` in the value slot, `v 0` in the `x` slot),
  * `u ↦ (u ∘ rgF₂ k) ∈ Y`      (`y'` in the value slot, `2 * v 0` in the `x` slot),
  * `u ↦ u (inr 0) ≠ 0`, `u (inr 2) = 2 * u (inl 0)`, `u (inl 1) * u (inr 0) = u (inr 1)`

  are `∅`-definable, and `Set.Definable.exists_of_finite` quantifies `u : Fin 3 → ℝ` away.

  The atoms used are: preimages of a definable set along a coordinate relabelling
  (`Set.Definable.preimage_comp`), and the polynomial relations `≠ 0`, `= 2 * ·` and `· * · = ·`,
  which are obtained from the `LRc`-terms for the ring operations (`Ring.mulFunc`, `Ring.addFunc`,
  `Ring.zeroFunc` transported into `LRc = (ring ⊕ rexpL)[[ℝ]]`) via
  `FirstOrder.Language.Term.definableFun_realize` and `Set.DefinableFun.ofPred_eq`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The ring symbols of `LRc` and their semantics on `ℝ` -/

/-- The multiplication symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev lrcMul : LRc.Functions 2 := Sum.inl (Sum.inl FirstOrder.Ring.mulFunc)

/-- The addition symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev lrcAdd : LRc.Functions 2 := Sum.inl (Sum.inl FirstOrder.Ring.addFunc)

/-- The zero symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev lrcZero : LRc.Functions 0 := Sum.inl (Sum.inl FirstOrder.Ring.zeroFunc)

/-- The `LRc`-term representing the product `v i * v j` on `ℝ`. -/
theorem realize_mulTerm {α : Type*} (v : α → ℝ) (i j : α) :
    (Term.func lrcMul (![Term.var i, Term.var j] : Fin 2 → LRc.Term α)).realize v = v i * v j := by
  rw [Term.realize_func]
  have h : (fun k : Fin 2 => Term.realize v
      ((![Term.var i, Term.var j] : Fin 2 → LRc.Term α) k)) = ![v i, v j] := by
    funext k; fin_cases k <;> rfl
  rw [h]; rfl

/-- The `LRc`-term representing the sum `v i + v j` on `ℝ`. -/
theorem realize_addTerm {α : Type*} (v : α → ℝ) (i j : α) :
    (Term.func lrcAdd (![Term.var i, Term.var j] : Fin 2 → LRc.Term α)).realize v = v i + v j := by
  rw [Term.realize_func]
  have h : (fun k : Fin 2 => Term.realize v
      ((![Term.var i, Term.var j] : Fin 2 → LRc.Term α) k)) = ![v i, v j] := by
    funext k; fin_cases k <;> rfl
  rw [h]; rfl

/-- The `LRc`-term representing the constant `0` on `ℝ`. -/
theorem realize_zeroTerm {α : Type*} (v : α → ℝ) :
    (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α)).realize v = (0 : ℝ) := by
  rw [Term.realize_func]
  have h : (fun k : Fin 0 => Term.realize v
      ((finZeroElim : Fin 0 → LRc.Term α) k)) = ![] := by
    funext k; exact k.elim0
  rw [h]; rfl

/-! ## 2. The atomic definable relations -/

/-- The product `v ↦ v i * v j` is a `∅`-definable function. -/
theorem definableFun_mul {α : Type*} (i j : α) :
    (∅ : Set ℝ).DefinableFun LRc (fun v : α → ℝ => v i * v j) := by
  have h := FirstOrder.Language.Term.definableFun_realize (L := LRc) (M := ℝ) (α := α)
    (Term.func lrcMul (![Term.var i, Term.var j] : Fin 2 → LRc.Term α))
  rw [show (fun v : α → ℝ => v i * v j) = fun v =>
      (Term.func lrcMul (![Term.var i, Term.var j] : Fin 2 → LRc.Term α)).realize v from
    funext (fun v => (realize_mulTerm v i j).symm)]
  exact h

/-- The sum `v ↦ v i + v j` is a `∅`-definable function. -/
theorem definableFun_add {α : Type*} (i j : α) :
    (∅ : Set ℝ).DefinableFun LRc (fun v : α → ℝ => v i + v j) := by
  have h := FirstOrder.Language.Term.definableFun_realize (L := LRc) (M := ℝ) (α := α)
    (Term.func lrcAdd (![Term.var i, Term.var j] : Fin 2 → LRc.Term α))
  rw [show (fun v : α → ℝ => v i + v j) = fun v =>
      (Term.func lrcAdd (![Term.var i, Term.var j] : Fin 2 → LRc.Term α)).realize v from
    funext (fun v => (realize_addTerm v i j).symm)]
  exact h

/-- The constant function `v ↦ 0` is a `∅`-definable function. -/
theorem definableFun_zero {α : Type*} :
    (∅ : Set ℝ).DefinableFun LRc (fun _ : α → ℝ => (0 : ℝ)) := by
  have h := FirstOrder.Language.Term.definableFun_realize (L := LRc) (M := ℝ) (α := α)
    (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α))
  rw [show (fun _ : α → ℝ => (0 : ℝ)) = fun v =>
      (Term.func lrcZero (finZeroElim : Fin 0 → LRc.Term α)).realize v from
    funext (fun v => (realize_zeroTerm v).symm)]
  exact h

/-- The relation `v i * v j = v l` is `∅`-definable. -/
theorem definable_mul_eq {α : Type*} (i j l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i * v j = v l} :=
  (definableFun_mul i j).ofPred_eq (Set.DefinableFun.proj LRc)

/-- The relation `v i + v j = v l` is `∅`-definable. -/
theorem definable_add_eq {α : Type*} (i j l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i + v j = v l} :=
  (definableFun_add i j).ofPred_eq (Set.DefinableFun.proj LRc)

/-- The relation `v i ≠ 0` is `∅`-definable. -/
theorem definable_ne_zero {α : Type*} (i : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i ≠ 0} := by
  have h := ((Set.DefinableFun.proj LRc (i := i)).ofPred_eq
    (definableFun_zero (α := α))).compl
  convert h using 1
  ext v
  simp

/-- The relation `v l = 2 * v i` is `∅`-definable. -/
theorem definable_two_mul {α : Type*} (i l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v l = 2 * v i} := by
  have h := definable_add_eq i i l
  convert h using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro hv <;> linarith

/-! ## 3. The two reindexings carrying the coordinates of `Y` into the ambient context -/

/-- The coordinate slots of `Y` in the ambient context `Fin (k+2) ⊕ Fin 3`, for the `Gr`-tuple
`Fin.cons (v 0) (Fin.cons u y)`: `0 ↦ v 0`, `1 ↦ y`, `j + 2 ↦ v (j + 2)`. -/
def rgF₁ (k : ℕ) : Fin (k + 2) → Fin (k + 2) ⊕ Fin 3 :=
  Fin.cases (Sum.inl 0) (Fin.cases (Sum.inr 0) (fun j : Fin k => Sum.inl j.succ.succ))

/-- The coordinate slots of `Y` in the ambient context `Fin (k+2) ⊕ Fin 3`, for the `Gr`-tuple
`Fin.cons u x (Fin.cons u y' c)`: `0 ↦ u x`, `1 ↦ y'`, `j + 2 ↦ v (j + 2)`. -/
def rgF₂ (k : ℕ) : Fin (k + 2) → Fin (k + 2) ⊕ Fin 3 :=
  Fin.cases (Sum.inr 2) (Fin.cases (Sum.inr 1) (fun j : Fin k => Sum.inl j.succ.succ))

/-- The first reindexing computes the `Fin.cons`-tuple `(v 0, u 0, c)`. -/
theorem rgCompF₁ {k : ℕ} (v : Fin (k + 2) → ℝ) (u : Fin 3 → ℝ) :
    (Sum.elim v u) ∘ (rgF₁ k) =
      Fin.cons (v 0) (Fin.cons (u 0) (fun j : Fin k => v j.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · simp [rgF₁]
  · simp only [Function.comp_apply, rgF₁, Fin.cases_succ]
    refine Fin.cases ?_ (fun j => ?_) i₁ <;> simp

/-- The second reindexing computes the `Fin.cons`-tuple `(u 2, u 1, c)`. -/
theorem rgCompF₂ {k : ℕ} (v : Fin (k + 2) → ℝ) (u : Fin 3 → ℝ) :
    (Sum.elim v u) ∘ (rgF₂ k) =
      Fin.cons (u 2) (Fin.cons (u 1) (fun j : Fin k => v j.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · simp [rgF₂]
  · simp only [Function.comp_apply, rgF₂, Fin.cases_succ]
    refine Fin.cases ?_ (fun j => ?_) i₁ <;> simp

/-- The defining clauses of `Route.RatGraph`, read in the ambient context
`(Fin (k+2) ⊕ Fin 3) → ℝ` instead of the context `Fin (k+2) → ℝ` of `RatGraph` itself. -/
def rgW (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set ((Fin (k + 2) ⊕ Fin 3) → ℝ) :=
  {u | (u ∘ rgF₁ k) ∈ Y} ∩ {u | (u ∘ rgF₂ k) ∈ Y} ∩ {u | u (Sum.inr 0) ≠ 0} ∩
    {u | u (Sum.inr 2) = 2 * u (Sum.inl 0)} ∩
    {u | u (Sum.inl 1) * u (Sum.inr 0) = u (Sum.inr 1)}

/-- The graph of the doubling ratio of a `∅`-definable family of graphs is `∅`-definable. -/
theorem ratGraph_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Route.RatGraph Y) := by
  -- each defining clause of `rgW` is `∅`-definable
  have hS : (∅ : Set ℝ).Definable LRc (rgW k Y) := by
    rw [rgW]
    exact ((((Set.Definable.preimage_comp (rgF₁ k) hY).inter
      (Set.Definable.preimage_comp (rgF₂ k) hY)).inter
      (definable_ne_zero (Sum.inr 0))).inter
      (definable_two_mul (Sum.inl 0) (Sum.inr 2))).inter
      (definable_mul_eq (Sum.inl 1) (Sum.inr 0) (Sum.inr 1))
  -- quantify the three extra variables away
  have hex := Set.Definable.exists_of_finite (A := (∅ : Set ℝ)) (L := LRc)
    (α := Fin (k + 2)) (β := Fin 3) hS
  -- the projection is exactly `RatGraph Y`
  have hset : {v : Fin (k + 2) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ rgW k Y} =
      Work.WilC4.Route.RatGraph Y := by
    ext v
    simp only [Work.WilC4.Route.RatGraph, Set.mem_ofPred_eq, rgW, Set.mem_inter_iff,
      Sum.elim_inl, Sum.elim_inr]
    constructor
    · -- a witness `u` for the clauses gives `y := u 0`, `y' := u 1`
      rintro ⟨u, ⟨⟨⟨⟨h1u, h2u⟩, h3u⟩, h4u⟩, h5u⟩⟩
      refine ⟨u 0, u 1, ?_, h3u, ?_, h5u⟩
      · change Fin.cons (v 0) (Fin.cons (u 0) (fun j : Fin k => v j.succ.succ)) ∈ Y
        rw [← rgCompF₁ (k := k) v u]
        exact h1u
      · change Fin.cons (2 * v 0) (Fin.cons (u 1) (fun j : Fin k => v j.succ.succ)) ∈ Y
        rw [← h4u, ← rgCompF₂ (k := k) v u]
        exact h2u
    · -- conversely `(y, y', 2 * v 0)` is a witness
      rintro ⟨y, y', hy, hy0, hy', hwy⟩
      refine ⟨![y, y', 2 * v 0], ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩
      · have key := rgCompF₁ (k := k) v ![y, y', 2 * v 0]
        rw [key]
        exact hy
      · have key := rgCompF₂ (k := k) v ![y, y', 2 * v 0]
        rw [key]
        exact hy'
      · simpa using hy0
      · simp
      · exact hwy
  rw [hset] at hex
  exact hex

end Work.WilC4
