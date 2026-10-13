/-
  WilC4/realULPMGood : from `Route.ModelULPM ℝ` to the *first-order* form `ULPMGood`, for a
  single fixed parameter-free formula `φ`.

  `Route.ModelULPM ℝ` produces, for every `∅`-definable family of graphs `Y ⊆ ℝ^{k+2}` that *is*
  a family of graphs, a constant `N > 0`, a finite set `Qs` of exponents and an `∅`-definable
  breakpoint family `B`.  The statement consumed downstream (`ULPMGood`, `WilC4/ULPMSyntax.lean`)
  is exactly this at a fixed `LRc`-formula `φ` *defining* the family, with the graph hypothesis
  turned into an implication (as it must be, since the formula `φ` alone need not define a family
  of graphs), the definable `B` replaced by a *formula* `ψ` defining it, and the finite set `Qs`
  enumerated by a function `qs : Fin Nq → ℚ` (again, a finite set is not a first-order object).

  Two conversions do the work.

  * The graph part.  A formula can only be tested against the *totally defined* family `Y_φ`, so we
    apply `ModelULPM` to the `∅`-definable "graph part"
    `Z = {v | (graphPart k φ).Realize v}`, where `graphPart k φ` is `φ ∧ ∀ y', φ(x,y') → y' = y`.
    Under the graph hypothesis the fibres of `Z` and of `Y_φ` agree (`graphPart_iff_of_graph`), so
    every conclusion for `Z` is one for `Y_φ`; the graph property of `Z` itself is
    `graphPart_cons` (`hy.2 y' hy'.1`).
  * The finite set / the definable set.  `Set.empty_definable_iff` turns `(∅ : Set ℝ).Definable` of
    `B` into a formula `ψ` with `B = {v | ψ.Realize v}` (`upsiVal_eq` converts `ψ.Realize (Fin.cons b c)`
    into `upsiVal k ψ ℝ c b`), and `exists_finset_enum` enumerates a `Finset ℚ` by a map out of
    `Fin Qs.card`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMSyntax
import Submission.Work.WilC4.ULPMDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize)

/-! ## 1. Converting between the `Fin.cons` and `Fin.cases` presentations -/

/-- The map putting the coordinate `y` (index `1`) into the *bounded* slot `Sum.inr 0` and keeping
the other coordinates in `Sum.inl`.  Used to write "the value at `x` is unique" as a formula. -/
def uniqVar (k : ℕ) : Fin (k + 2) → Fin (k + 2) ⊕ Fin 1 :=
  Fin.cases (Sum.inl 0) (Fin.cases (Sum.inr 0) (fun j : Fin k => Sum.inl j.succ.succ))

/-- Composing a `Sum.elim`-tuple with `uniqVar k` replaces the `y`-coordinate by the bound
variable. -/
theorem comp_uniqVar {k : ℕ} {N : Type} (v : Fin (k + 2) → N) (u : Fin 1 → N) :
    (Sum.elim v u) ∘ uniqVar k =
      Fin.cons (v 0) (Fin.cons (u 0) (fun j : Fin k => v j.succ.succ)) := by
  funext t
  induction t using Fin.cases with
  | zero => rfl
  | succ t =>
      induction t using Fin.cases with
      | zero => rfl
      | succ j => rfl

/-- `Fin.cons` and `Fin.cases` agree. -/
theorem cons_cases_eq {k : ℕ} {M : Type} (x y : M) (c : Fin k → M) :
    (Fin.cons x (Fin.cons y c) : Fin (k + 2) → M) = Fin.cases x (Fin.cases y c) := by
  funext t
  induction t using Fin.cases with
  | zero => rfl
  | succ t =>
      induction t using Fin.cases with
      | zero => rfl
      | succ j => rfl

/-- `Fin.cons` and `Fin.cases` agree (one coordinate). -/
theorem cons_cases_eq' {k : ℕ} {M : Type} (x : M) (c : Fin k → M) :
    (Fin.cons x c : Fin (k + 1) → M) = Fin.cases x c := by
  funext t
  induction t using Fin.cases with
  | zero => rfl
  | succ t => rfl

/-! ## 2. The graph part of `φ` -/

/-- `graphPart k φ` is `φ(x,y) ∧ ∀ y', φ(x,y') → y' = y`: the graph part of the family defined
by `φ`.  It is `∅`-definable as soon as `φ` is, and (unlike `φ`) it defines a family of graphs. -/
def graphPart (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (Fin (k + 2)) :=
  φ ⊓ Formula.iAlls (Fin 1)
    ((Formula.relabel (uniqVar k) φ) ⟹
      (liftR ![(Sum.inl (1 : Fin (k + 2)) : Fin (k + 2) ⊕ Fin 1), Sum.inr 0] eqAtom))

theorem graphPart_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (v : Fin (k + 2) → M) :
    (graphPart k φ).Realize v ↔
      φ.Realize v ∧ ∀ y' : M,
        φ.Realize (Fin.cons (v 0) (Fin.cons y' (fun j : Fin k => v j.succ.succ))) → y' = v 1 := by
  rw [graphPart, Formula.realize_inf, Formula.realize_iAlls]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun y' hy' => ?_⟩
    have h := h2 (fun _ : Fin 1 => y')
    simp only [Formula.realize_imp, Formula.realize_relabel, comp_uniqVar, eqAtom_lift,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact (h (by simpa using hy')).symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u => ?_⟩
    simp only [Formula.realize_imp, Formula.realize_relabel, comp_uniqVar, eqAtom_lift,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact fun hφ => (h2 (u 0) (by simpa using hφ)).symm

/-- Membership in the graph part at a tuple `(x, y, c)`. -/
theorem graphPart_cons {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (c : Fin k → M) (x y : M) :
    (graphPart k φ).Realize (Fin.cons x (Fin.cons y c)) ↔
      φ.Realize (Fin.cons x (Fin.cons y c)) ∧
        ∀ y' : M, φ.Realize (Fin.cons x (Fin.cons y' c)) → y' = y := by
  rw [graphPart_realize]
  have h0 : (Fin.cons x (Fin.cons y c) : Fin (k + 2) → M) 0 = x := rfl
  have h1 : (Fin.cons x (Fin.cons y c) : Fin (k + 2) → M) 1 = y := rfl
  have hs : (fun j : Fin k => (Fin.cons x (Fin.cons y c) : Fin (k + 2) → M) j.succ.succ) = c := by
    funext j; rfl
  rw [h0, h1, hs]

/-- Under the graph hypothesis on `φ`, the `x`-fibres of the graph part and of `φ` agree. -/
theorem graphPart_iff_of_graph {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (hgr : ∀ (c : Fin k → M) (x y y' : M), φ.Realize (Fin.cons x (Fin.cons y c)) →
      φ.Realize (Fin.cons x (Fin.cons y' c)) → y = y')
    (c : Fin k → M) (x y : M) :
    (graphPart k φ).Realize (Fin.cons x (Fin.cons y c)) ↔ φ.Realize (Fin.cons x (Fin.cons y c)) := by
  rw [graphPart_cons]
  exact ⟨fun h => h.1, fun h => ⟨h, fun y' hy' => hgr c x y' y hy' h⟩⟩

/-! ## 3. `uphiVal`/`upsiVal` are the `Fin.cons` presentation -/

theorem uphiVal_eq {M : Type} [LRc.Structure M] (k : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (c : Fin k → M) (x y : M) :
    uphiVal k φ M c x y ↔ φ.Realize (Fin.cons x (Fin.cons y c)) := by
  simp only [uphiVal, cons_cases_eq]

theorem upsiVal_eq {M : Type} [LRc.Structure M] (k : ℕ) (ψ : LRc.Formula (Fin (k + 1)))
    (c : Fin k → M) (b : M) :
    upsiVal k ψ M c b ↔ ψ.Realize (Fin.cons b c) := by
  simp only [upsiVal, cons_cases_eq']

/-! ## 4. Enumerating a finite set of rationals -/

/-- Any `Finset ℚ` is the image of a map out of `Fin Qs.card`. -/
theorem exists_finset_enum (Qs : Finset ℚ) :
    ∃ (Nq : ℕ) (qs : Fin Nq → ℚ), ∀ q ∈ Qs, ∃ i, qs i = q :=
  ⟨Qs.card, fun i => (Qs.equivFin.symm i).1, fun q hq => ⟨Qs.equivFin ⟨q, hq⟩, by simp⟩⟩

/-! ## 5. The statement -/

theorem realULPMGood {k : ℕ} (h : Work.WilC4.Route.ModelULPM ℝ) (φ : WilkiesDesign.CG.LRc.Formula (Fin (k + 2))) :
    ∃ (N Nq : ℕ) (qs : Fin Nq → ℚ) (ψ : WilkiesDesign.CG.LRc.Formula (Fin (k + 1))),
      0 < N ∧ Work.WilC4.ULPMGood k N Nq φ ψ qs ℝ := by
  let Z : Set (Fin (k + 2) → ℝ) := {v | (graphPart k φ).Realize v}
  have hZdef : (∅ : Set ℝ).Definable LRc Z :=
    Set.empty_definable_iff.mpr ⟨graphPart k φ, rfl⟩
  have hZgraph : ∀ (c : Fin k → ℝ) (x y y' : ℝ),
      Fin.cons x (Fin.cons y c) ∈ Z → Fin.cons x (Fin.cons y' c) ∈ Z → y = y' := by
    intro c x y y' hy hy'
    simp only [Z, Set.mem_ofPred_eq, graphPart_cons] at hy hy'
    exact (hy.2 y' hy'.1).symm
  obtain ⟨N, hN, Qs, B, hBdef, hB⟩ := h k Z hZdef hZgraph
  obtain ⟨ψ, hψ⟩ := Set.empty_definable_iff.mp hBdef
  obtain ⟨Nq, qs, hqs⟩ := exists_finset_enum Qs
  refine ⟨N, Nq, qs, ψ, hN, ?_⟩
  intro hgraph
  have hgr : ∀ (c : Fin k → ℝ) (x y y' : ℝ), φ.Realize (Fin.cons x (Fin.cons y c)) →
      φ.Realize (Fin.cons x (Fin.cons y' c)) → y = y' := fun c x y y' hy hy' =>
    hgraph c x y y' ((uphiVal_eq k φ c x y).2 hy) ((uphiVal_eq k φ c x y').2 hy')
  intro c
  have hmem : ∀ b : ℝ, Fin.cons b c ∈ B ↔ upsiVal k ψ ℝ c b := by
    intro b
    simp only [hψ, Set.mem_ofPred_eq, upsiVal_eq]
  constructor
  · have hset : {x : ℝ | upsiVal k ψ ℝ c x} = {x : ℝ | Fin.cons x c ∈ B} := by
      ext x; exact (hmem x).symm
    rw [hset]; exact (hB c).1
  · intro x₁ x₂ hx1 hx2 hss
    have hss' : Route.SameSide N {x : ℝ | Fin.cons x c ∈ B} x₁ x₂ :=
      fun b hb => hss b ((hmem b).1 hb)
    obtain ⟨hdom, happrox⟩ := (hB c).2 x₁ x₂ hx1 hx2 hss'
    constructor
    · have e1 : (∃ y : ℝ, uphiVal k φ ℝ c x₁ y) ↔
          ∃ y : ℝ, (graphPart k φ).Realize (Fin.cons x₁ (Fin.cons y c)) :=
        (exists_congr fun y => uphiVal_eq k φ c x₁ y).trans
          (exists_congr fun y => (graphPart_iff_of_graph (M := ℝ) k φ hgr c x₁ y).symm)
      have e2 : (∃ y : ℝ, uphiVal k φ ℝ c x₂ y) ↔
          ∃ y : ℝ, (graphPart k φ).Realize (Fin.cons x₂ (Fin.cons y c)) :=
        (exists_congr fun y => uphiVal_eq k φ c x₂ y).trans
          (exists_congr fun y => (graphPart_iff_of_graph (M := ℝ) k φ hgr c x₂ y).symm)
      rw [e1, e2]
      simpa only [Z, Set.mem_ofPred_eq] using hdom
    · intro y₁ y₂ hy₁ hy₂
      have hy₁' : φ.Realize (Fin.cons x₁ (Fin.cons y₁ c)) := (uphiVal_eq k φ c x₁ y₁).1 hy₁
      have hy₂' : φ.Realize (Fin.cons x₂ (Fin.cons y₂ c)) := (uphiVal_eq k φ c x₂ y₂).1 hy₂
      have hZ₁ : Fin.cons x₁ (Fin.cons y₁ c) ∈ Z := by
        simp only [Z, Set.mem_ofPred_eq]
        exact (graphPart_iff_of_graph (M := ℝ) k φ hgr c x₁ y₁).2 hy₁'
      have hZ₂ : Fin.cons x₂ (Fin.cons y₂ c) ∈ Z := by
        simp only [Z, Set.mem_ofPred_eq]
        exact (graphPart_iff_of_graph (M := ℝ) k φ hgr c x₂ y₂).2 hy₂'
      obtain ⟨q, hq, t₁, t₂, h1, h2, h3, h4⟩ := happrox y₁ y₂ hZ₁ hZ₂
      obtain ⟨i, hi⟩ := hqs q hq
      exact ⟨i, t₁, t₂, by rwa [hi], by rwa [hi], h3, h4⟩

end Work.WilC4
