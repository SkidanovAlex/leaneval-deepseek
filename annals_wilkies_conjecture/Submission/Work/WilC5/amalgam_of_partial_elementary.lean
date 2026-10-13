import Mathlib
import Submission.Work.WilC5.ExistsSaturated
import Submission.Work.WilC5.extends_of_elementary_sat
import Submission.Work.WilC5.ExtSatAux
import Submission.Work.WilC5.ExtSatChain
import Submission.Work.WilC5.extends_elemOn_sat
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC5

/-- **Partial elementarity on `Fin`-indexed tuples implies partial elementarity on
arbitrary index sets.**

A hypothesis of the form "for every `n` and every `n`-tuple `a` from `A`, the formula `φ`
holds of `a` in `M` iff it holds of `σ ∘ a` in `N`" is stated for formulas with free
variables indexed by `Fin n` (the shape produced by `ElementaryEmbedding`).  Here we show
that it implies the same equivalence for formulas whose free variables are indexed by the
whole parameter set `A`.  The proof restricts `φ` to the (finite) set of free variables it
actually uses (`BoundedFormula.freeVarFinset`), enumerates that set by `Fin`, and applies
the hypothesis. -/
theorem realize_iff_of_fin {L : FirstOrder.Language.{0, 0}} {M N : Type}
    [L.Structure M] [L.Structure N] {A : Set M} (σ : A → N)
    (hσ : ∀ {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → A),
      (φ.Realize (fun i => (a i : M)) ↔ φ.Realize (fun i => (σ (a i) : N)))) :
    ∀ (φ : L.Formula A), (φ.Realize (Subtype.val : A → M) ↔ φ.Realize σ) := by
  intro φ
  classical
  set s : Finset A := φ.freeVarFinset with hs
  set f : ↥s ≃ Fin s.card := Finset.equivFin s with hf
  let ψ : L.Formula (Fin s.card) := φ.restrictFreeVar (⇑f)
  have hψ : ∀ {P : Type} [L.Structure P] (w : Fin s.card → P) (w' : A → P),
      (∀ a : ↥s, w (f a) = w' ↑a) → (ψ.Realize w ↔ φ.Realize w') := by
    intro P _ w w' hw
    have hb := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := ⇑f) (v := w)
        (xs := fun i : Fin 0 => i.elim0) w' (by rintro ⟨a, ha⟩; exact hw ⟨a, ha⟩)
    exact (formulaRealize_iff_bounded ψ w).symm.trans (hb.trans (formulaRealize_iff_bounded φ w'))
  have h1 : ψ.Realize (fun i => (((f.symm i : ↥s) : A) : M))
      ↔ φ.Realize (Subtype.val : A → M) :=
    hψ (fun i => (((f.symm i : ↥s) : A) : M)) (Subtype.val : A → M)
      (fun a => by rw [Equiv.symm_apply_apply])
  have h2 : ψ.Realize (fun i => σ ((f.symm i : ↥s) : A)) ↔ φ.Realize σ :=
    hψ (fun i => σ ((f.symm i : ↥s) : A)) σ
      (fun a => by rw [Equiv.symm_apply_apply])
  exact h1.symm.trans ((hσ ψ (fun i => ((f.symm i : ↥s) : A))).trans h2)

theorem amalgam_of_partial_elementary {K L : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc L]
    (hK : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc K _ WilkiesDesign.CG.TR)
    (hL : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc L _ WilkiesDesign.CG.TR)
    {A : Set K} (hA : Work.WilC2.Dcl A ⊆ A) (σ : A → L)
    (hσ : ∀ {n : ℕ} (φ : WilkiesDesign.CG.LRc.Formula (Fin n)) (a : Fin n → A),
      (φ.Realize (fun i => (a i : K)) ↔ φ.Realize (fun i => (σ (a i) : L)))) :
    ∃ (N : Type) (instN : FirstOrder.Language.Structure WilkiesDesign.CG.LRc N)
      (hN : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc N instN WilkiesDesign.CG.TR)
      (f : @FirstOrder.Language.ElementaryEmbedding WilkiesDesign.CG.LRc K N _ instN)
      (g : @FirstOrder.Language.ElementaryEmbedding WilkiesDesign.CG.LRc L N _ instN),
      ∀ a : A, f a = g (σ a) := by
  classical
  -- A saturated elementary extension `N` of `K`, saturated far beyond `|L|`.
  set κ : Cardinal.{0} := Order.succ (Cardinal.mk L) with hκdef
  have hκ : Cardinal.mk L < κ := Order.lt_succ_iff.mpr le_rfl
  obtain ⟨N, instN, f, hsat⟩ := ExistsSaturated (L := WilkiesDesign.CG.LRc) K κ
  -- The name of `A` inside `N`, and the partial map `τ₀ : f '' A → L` inverse to `σ`.
  let gk : A → N := fun a => (f (a : K) : N)
  let B₀ : Set N := Set.range gk
  let e : A ≃ B₀ :=
    { toFun := fun a => ⟨gk a, ⟨a, rfl⟩⟩
      invFun := fun y => Classical.choose y.2
      left_inv := fun a => Subtype.ext (f.injective (by
        have h := Classical.choose_spec (show gk a ∈ Set.range gk from ⟨a, rfl⟩)
        simpa [gk] using h))
      right_inv := fun y => Subtype.ext (Classical.choose_spec y.2) }
  let τ₀ : B₀ → L := fun y => σ (e.symm y)
  -- `τ₀` is elementary: this is `hσ`, transferred along the elementary embedding `f`.
  have hτ₀ : Work.WilC5.ElemOn (L := WilkiesDesign.CG.LRc) B₀ τ₀ := by
    have hred := realize_iff_of_fin (L := WilkiesDesign.CG.LRc) σ hσ
    intro φ
    let φ' : WilkiesDesign.CG.LRc.Formula A := φ.relabel (⇑e.symm)
    have hA' : φ'.Realize gk ↔ φ.Realize (Subtype.val : B₀ → N) := by
      have hfn : (gk ∘ (⇑e.symm) : B₀ → N) = (Subtype.val : B₀ → N) := by
        funext y
        change (f ((e.symm y : A) : K) : N) = (y : N)
        exact congrArg Subtype.val (e.apply_symm_apply y)
      rw [show φ' = φ.relabel (⇑e.symm) from rfl, Formula.realize_relabel, hfn]
    have hB' : φ'.Realize gk ↔ φ'.Realize (Subtype.val : A → K) := by
      have h := f.map_formula φ' (Subtype.val : A → K)
      simpa [Function.comp_def, gk] using h
    have hC' : φ'.Realize (Subtype.val : A → K) ↔ φ'.Realize σ := hred φ'
    have hD' : φ'.Realize σ ↔ φ.Realize τ₀ := by
      have hfn : (σ ∘ (⇑e.symm) : B₀ → L) = τ₀ := rfl
      rw [show φ' = φ.relabel (⇑e.symm) from rfl, Formula.realize_relabel, hfn]
    exact hA'.symm.trans (hB'.trans (hC'.trans hD'))
  -- Extend `τ₀` to the inverse of an elementary embedding of `L` into `N`.
  obtain ⟨B', hBB, τ', hτ', hagree, g, hg⟩ := extends_elemOn_sat hτ₀ κ hκ hsat
  refine ⟨N, instN, (f.theory_model_iff WilkiesDesign.CG.TR).mp hK, f, g, ?_⟩
  intro a
  -- `e a` and `g (σ a)` have the same `τ'`-value `σ a`, so they are equal.
  obtain ⟨h, hh⟩ := hg (σ a)
  have hea : (e a : N) ∈ B' := hBB (e a).2
  have h2 : τ' ⟨(e a : N), hea⟩ = σ a := by
    rw [hagree (e a)]
    simp only [τ₀]
    rw [Equiv.symm_apply_apply]
  have : (⟨(g (σ a) : N), h⟩ : B') = ⟨(e a : N), hea⟩ :=
    elemOn_injective hτ' (hh.trans h2.symm)
  exact (congrArg Subtype.val this).symm

end Work.WilC5
