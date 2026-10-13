/-
  Area C2 (WilC2): a `T`-definable partial function whose value at `b` is `a`, given that the
  singleton `{a}` is definable over `insert b T`.

  From `Work.WilC2.exists_relabel_two` we get a formula `Φ` in the variables `Fin n ⊕ Fin 2` and
  parameters `c ∈ T` whose fibre over `b` is `{a}`.  Moving the `y`-slot into the parameter block
  gives a parametric family to which the definable choice principle
  `Work.WilC2.definable_choice_fibre` applies; the resulting `ψ` selects a unique point on every
  non-empty fibre.  The relation

  `R y x  :=  ψ(y,x) ∧ Φ(y,x)`

  is `T`-definable, has fibre `{a}` over `b`, and is a partial function.  Only two pure variable
  renamings are needed.
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.exists_relabel_two
import Submission.Work.WilC2.definable_choice_fibre

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc TR rexpL)

/-- The relabelling turning an `n`-parameter family of binary relations into an `(n+1)`-parameter
family of unary relations: the second variable slot becomes the last parameter slot. -/
def rhoFam {n : ℕ} : Fin n ⊕ Fin 2 → Fin (n + 1) ⊕ Fin 1
  | Sum.inl i => Sum.inl (Fin.castSucc i)
  | Sum.inr k => if k.val = 0 then Sum.inl (Fin.last n) else Sum.inr 0

/-- The inverse relabelling: the last parameter slot becomes the `y`-variable. -/
def rhoBack {n : ℕ} : Fin (n + 1) ⊕ Fin 1 → Fin n ⊕ Fin 2
  | Sum.inl i => Fin.lastCases (Sum.inr 0) (fun j => Sum.inl j) i
  | Sum.inr _ => Sum.inr 1

lemma rhoFam_inl {n : ℕ} (i : Fin n) :
    rhoFam (n := n) (Sum.inl i) = Sum.inl (Fin.castSucc i) := rfl

lemma rhoFam_zero {n : ℕ} : rhoFam (n := n) (Sum.inr (0 : Fin 2)) = Sum.inl (Fin.last n) := by
  simp [rhoFam]

lemma rhoFam_one {n : ℕ} : rhoFam (n := n) (Sum.inr (1 : Fin 2)) = Sum.inr (0 : Fin 1) := by
  simp [rhoFam]

lemma rhoBack_inr {n : ℕ} (k : Fin 1) : rhoBack (n := n) (Sum.inr k) = Sum.inr (1 : Fin 2) := rfl

lemma rhoBack_last {n : ℕ} :
    rhoBack (n := n) (Sum.inl (Fin.last n)) = Sum.inr (0 : Fin 2) := by
  simp [rhoBack]

lemma rhoBack_castSucc {n : ℕ} (j : Fin n) :
    rhoBack (n := n) (Sum.inl (Fin.castSucc j)) = Sum.inl j := by
  simp [rhoBack]

/-- Realisation of the relabelled formula in the family form. -/
lemma rhoFam_realize {M : Type} [LRc.Structure M] {n : ℕ}
    (Φ : LRc.Formula (Fin n ⊕ Fin 2)) (c : Fin n → M) (y x : M) :
    (Φ.relabel (rhoFam (n := n))).Realize (Sum.elim (Fin.snoc c y) (fun _ => x)) ↔
      Φ.Realize (Sum.elim c ![y, x]) := by
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (fun f => Φ.Realize f) ?_)
  funext w
  rcases w with i | k
  · simp [Function.comp_apply, rhoFam_inl, Fin.snoc_castSucc]
  · fin_cases k <;>
      simp [Function.comp_apply, rhoFam_zero, rhoFam_one, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Realisation of the relabelled formula in the original two-variable form. -/
lemma rhoBack_realize {M : Type} [LRc.Structure M] {n : ℕ}
    (ψ : LRc.Formula (Fin (n + 1) ⊕ Fin 1)) (c : Fin n → M) (y x : M) :
    (ψ.relabel (rhoBack (n := n))).Realize (Sum.elim c ![y, x]) ↔
      ψ.Realize (Sum.elim (Fin.snoc c y) (fun _ => x)) := by
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (fun f => ψ.Realize f) ?_)
  funext w
  rcases w with i | k
  · induction i using Fin.lastCases with
    | last => simp [Function.comp_apply, rhoBack_last]
    | cast j => simp [Function.comp_apply, rhoBack_castSucc, Fin.snoc_castSucc]
  · simp only [Function.comp_apply, rhoBack_inr]
    fin_cases k
    simp [Matrix.cons_val_fin_one]

/-- **A `T`-definable partial function with value `a` at `b`.** -/
theorem exists_relabel_graph_aux
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X → RExpExist X)
    (hUF : UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ TR] {T : Set M} {a b : M}
    (h : (insert b T).Definable LRc {v : Fin 1 → M | v 0 ∈ ({a} : Set M)}) :
    ∃ R : M → M → Prop,
      T.Definable LRc {v : Fin 2 → M | R (v 0) (v 1)} ∧
      (∀ x : M, R b x ↔ x = a) ∧
      (∀ y x x' : M, R y x → R y x' → x = x') := by
  classical
  obtain ⟨n, Φ, c, hc, hΦ⟩ := exists_relabel_two (M := M) h
  obtain ⟨ψ, hψ⟩ := definable_choice_fibre (M := M) hR hC0 hUF (Φ.relabel (rhoFam (n := n)))
  let ΨF : LRc.Formula (Fin n ⊕ Fin 2) := (ψ.relabel (rhoBack (n := n))) ⊓ Φ
  have hbridge : ∀ y x : M, ΨF.Realize (Sum.elim c ![y, x]) ↔
      ((ψ.relabel (rhoBack (n := n))).Realize (Sum.elim c ![y, x]) ∧
        Φ.Realize (Sum.elim c ![y, x])) := by
    intro y x
    simp only [ΨF, Formula.realize_inf]
  -- the choice point over `b` is `a`, and it satisfies `ψ`
  obtain ⟨u₀, ⟨hu₀ψ, hu₀Φ⟩, hu₀uniq⟩ :=
    hψ (Fin.snoc c b) ⟨a, (rhoFam_realize Φ c b a).mpr ((hΦ a).mpr rfl)⟩
  have hu₀ : u₀ = a := (hΦ u₀).mp ((rhoFam_realize Φ c b u₀).mp hu₀Φ)
  have hψba : (ψ.relabel (rhoBack (n := n))).Realize (Sum.elim c ![b, a]) := by
    rw [rhoBack_realize, ← hu₀]
    exact hu₀ψ
  refine ⟨fun y x => ΨF.Realize (Sum.elim c ![y, x]), ?_, ?_, ?_⟩
  · -- `T`-definability
    have hdef := definable_of_param_formula (A := T) (L := LRc) (N := M) (γ := Fin n) (α := Fin 2)
      c hc ΨF
    have hfun : ∀ v : Fin 2 → M, Sum.elim c v = Sum.elim c ![v 0, v 1] := by
      intro v
      congr 1
      funext i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hset : {v : Fin 2 → M | ΨF.Realize (Sum.elim c v)} =
        {v : Fin 2 → M | ΨF.Realize (Sum.elim c ![v 0, v 1])} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      rw [hfun v]
    rw [hset] at hdef
    exact hdef
  · -- the fibre over `b` is `{a}`
    intro x
    change ΨF.Realize (Sum.elim c ![b, x]) ↔ x = a
    rw [hbridge]
    constructor
    · intro hx
      exact (hΦ x).mp hx.2
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [hx]
        exact hψba
      · rw [hx]
        exact (hΦ a).mpr rfl
  · -- the graph property
    intro y x x' hx hx'
    rw [hbridge] at hx hx'
    have hxΦ : Φ.Realize (Sum.elim c ![y, x]) := hx.2
    have hx'Φ : Φ.Realize (Sum.elim c ![y, x']) := hx'.2
    have hne : ∃ u : M, (Φ.relabel (rhoFam (n := n))).Realize
        (Sum.elim (Fin.snoc c y) (fun _ => u)) :=
      ⟨x, (rhoFam_realize Φ c y x).mpr hxΦ⟩
    obtain ⟨u, -, hu⟩ := hψ (Fin.snoc c y) hne
    have h1 : x = u :=
      hu x ⟨(rhoBack_realize ψ c y x).mp hx.1, (rhoFam_realize Φ c y x).mpr hxΦ⟩
    have h2 : x' = u :=
      hu x' ⟨(rhoBack_realize ψ c y x').mp hx'.1, (rhoFam_realize Φ c y x').mpr hx'Φ⟩
    rw [h1, h2]

end Work.WilC2
