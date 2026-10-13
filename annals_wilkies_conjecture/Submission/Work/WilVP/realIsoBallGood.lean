/-
  WilVP `realIsoBallGood`.

  `Work.WilVP.IsoBallProp ℝ` is the *geometric* iso-ball statement: every `∅`-definable family
  of graphs with bounded fibres admits `N > 0` and a `∅`-definable `P` with the uniform
  iso-ball property.  `Work.WilVP.IsoBallGood` is the *syntactic* content of the same
  statement for a fixed parameter-free formula `φ` (the family) and `ψ` (the set `P`), with the
  graph and bounded-fibre hypotheses turned into implications.

  This file performs the one formal step between the two: instantiate `IsoBallProp ℝ` at the set
  `Y = {v | φ.Realize v}` (whose `∅`-definability is `Set.empty_definable_iff`) and turn the
  `∅`-definable set `P` it produces into a formula `ψ` (again `Set.empty_definable_iff`).

  Two bookkeeping details.  First, `IsoBallProp` consumes its two hypotheses as arguments,
  while `IsoBallGood` must produce a *single* `(N, ψ)` valid for all parameter values, so the
  construction is split on whether the hypotheses hold: if they do, `h` supplies the data; if
  they do not, any pair (here `1` and `⊥`) works, since the implication is then vacuous.
  Second, `uphiVal`/`upsiVal` present the arguments as `Fin.cases` while the geometric statements
  use `Fin.cons`; the two presentations are bridged by `cons_eq_cases`.
-/
import Mathlib
import Submission.Work.WilVP.IsoBallSyntax
import Submission.Work.WilVP.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language
open Work.WilC4 (uphiVal upsiVal)

namespace Work.WilVP

/-! ## 1. The `Fin.cons` / `Fin.cases` bridge -/

/-- `Fin.cons` and `Fin.cases` agree, two coordinates. -/
theorem cons_eq_cases {k : ℕ} {M : Type} (x y : M) (c : Fin k → M) :
    (Fin.cons x (Fin.cons y c) : Fin (k + 2) → M) = Fin.cases x (Fin.cases y c) := by
  funext t
  induction t using Fin.cases with
  | zero => rfl
  | succ t =>
      induction t using Fin.cases with
      | zero => rfl
      | succ j => rfl

/-- `Fin.cons` and `Fin.cases` agree, one coordinate. -/
theorem cons_eq_cases_one {k : ℕ} {M : Type} (x : M) (c : Fin k → M) :
    (Fin.cons x c : Fin (k + 1) → M) = Fin.cases x c := by
  funext t
  induction t using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- `uphiVal` in the `Fin.cons` presentation. -/
theorem uphiVal_cons_iff {M : Type} [LRc.Structure M] (k : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (c : Fin k → M) (x y : M) :
    uphiVal k φ M c x y ↔ φ.Realize (Fin.cons x (Fin.cons y c)) := by
  simp only [uphiVal, cons_eq_cases]

/-- `upsiVal` in the `Fin.cons` presentation. -/
theorem upsiVal_cons_iff {M : Type} [LRc.Structure M] (k : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (c : Fin k → M) (b : M) :
    upsiVal k ψ M c b ↔ ψ.Realize (Fin.cons b c) := by
  simp only [upsiVal, cons_eq_cases_one]

/-! ## 2. From the geometric statement to the syntactic one -/

theorem realIsoBallGood {k : ℕ} (h : Work.WilVP.IsoBallProp ℝ)
    (φ : WilkiesDesign.CG.LRc.Formula (Fin (k + 2))) :
    ∃ (N : ℕ) (ψ : WilkiesDesign.CG.LRc.Formula (Fin (k + 1))),
      0 < N ∧ Work.WilVP.IsoBallGood k N φ ψ ℝ := by
  classical
  -- the `∅`-definable family defined by `φ`
  let Y : Set (Fin (k + 2) → ℝ) := {v | φ.Realize v}
  have hYdef : (∅ : Set ℝ).Definable LRc Y := Set.empty_definable_iff.mpr ⟨φ, rfl⟩
  -- the two hypotheses of `IsoBallProp`; they must be *decided* because the output `(N, ψ)`
  -- is produced before the hypotheses of `IsoBallGood` are introduced
  by_cases hhyp : (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') ∧
      (∀ c : Fin k → ℝ, ∃ R : ℝ, ∀ x y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → |x| ≤ R)
  · obtain ⟨hgr, hbdd⟩ := hhyp
    -- the geometric statement at `Y`
    obtain ⟨N, hN, P, hPdef, hP⟩ := h k Y hYdef hgr hbdd
    -- the `∅`-definable set `P` is defined by a formula `ψ`
    obtain ⟨ψ, hψ⟩ := Set.empty_definable_iff.mp hPdef
    refine ⟨N, ψ, hN, ?_⟩
    intro _hgrI _hbddI c
    constructor
    · -- the cardinality clause
      have hset : {x : ℝ | upsiVal k ψ ℝ c x} = {x : ℝ | Fin.cons x c ∈ P} := by
        ext x
        simp only [Set.mem_ofPred_eq, upsiVal_cons_iff, hψ]
      rw [hset]
      exact (hP c).1
    · -- the iso clause
      intro x y₀ y hxy₀ hy₀ne hball
      have htransfer : ∀ p : ℝ, Fin.cons p c ∈ P → upsiVal k ψ ℝ c p := by
        intro p hp
        simpa only [upsiVal_cons_iff, hψ, Set.mem_ofPred_eq] using hp
      have hxy₀Y : Fin.cons x (Fin.cons y₀ c) ∈ Y :=
        (uphiVal_cons_iff k φ c x y₀).1 hxy₀
      obtain ⟨y₁, hy₁, hb1, hb2⟩ :=
        (hP c).2 x y₀ y hxy₀Y hy₀ne (fun p hp => hball p (htransfer p hp))
      exact ⟨y₁, (uphiVal_cons_iff k φ c y y₁).2 hy₁, hb1, hb2⟩
  · -- the hypotheses fail: the implication is vacuous, any `(N, ψ)` works
    refine ⟨1, (⊥ : LRc.Formula (Fin (k + 1))), one_pos, ?_⟩
    intro hgrI hbddI
    exact absurd ⟨fun c x y y' h1 h2 => hgrI c x y y'
        ((uphiVal_cons_iff k φ c x y).2 h1) ((uphiVal_cons_iff k φ c x y').2 h2),
      fun c => by
        obtain ⟨R, hR⟩ := hbddI c
        exact ⟨R, fun x y hxy => hR x y ((uphiVal_cons_iff k φ c x y).2 hxy)⟩⟩ hhyp

end Work.WilVP
