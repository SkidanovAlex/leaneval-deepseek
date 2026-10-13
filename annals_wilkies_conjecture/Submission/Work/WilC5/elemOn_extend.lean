/-
  WilC5 — the one-point extension step for the construction of an elementary embedding of a
  substructure into a saturated structure.

  Given a partial elementary map `τ : B → M` (`B ⊆ N`), a cardinal `κ > |B|` and a `κ`-saturated
  structure `N`, and a point `m ∈ M` which is not a value of `τ`, we adjoin a point `n ∈ N \ B`
  with `τ' n = m` and prove that `τ'` is again elementary.

  The proof is the classical one: let
  `P = { ψ : L.Formula (B ⊕ Fin 1) | M ⊨ ψ(τ b̄, m) }` be the type of `m` over `B`.  It is finitely
  satisfiable in `N`: finitely many members are conjoined into a single formula, which is then
  existentially quantified in the single free variable and transported across the elementary map
  `τ`.  `κ`-saturation (in the form `IsSaturated`, which is stated exactly in the
  `L.Formula (A ⊕ Fin 1)` presentation) yields a realization `x : Fin 1 → N`.  Since the type
  contains the formulas `x ≠ b` for every parameter, the point `x 0` is outside `B`; and since the
  type is *complete* (it is closed under negation), `x 0` and `m` satisfy the same formulas over
  `B`.  Relabelling a formula over `insert (x 0) B` along the bijection
  `insertSum B (x 0) : ↥(insert (x 0) B) → B ⊕ Fin 1` then transfers this to elementarity of
  `τ' = PEM.extendFun τ (x 0) m` on `insert (x 0) B`.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ElemOnExtAux
import Submission.Work.WilC5.finSat_of_elemOn

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

theorem elemOn_extend {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]
    {B : Set N} {τ : B → M} (h : @ElemOn L M N _ _ B τ)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk B < κ) (hsat : @IsSaturated L N _ κ)
    (m : M) (hm : m ∉ Set.range τ) :
    ∃ n : N, n ∉ B ∧ @ElemOn L M N _ _ (insert n B) (PEM.extendFun τ n m) := by
  classical
  -- the type of `m` over the parameters `B`, as a set of formulas of `L[[B]]` with one free slot
  set w : B ⊕ Fin 1 → M := Sum.elim τ (fun _ : Fin 1 => m) with hw
  set P : Set (L.Formula (B ⊕ Fin 1)) := {ψ | ψ.Realize w} with hPdef
  have hPmem : ∀ ψ : L.Formula (B ⊕ Fin 1), ψ ∈ P ↔ ψ.Realize w := by
    intro ψ
    simp only [hPdef, Set.mem_ofPred_eq]
  -- every finite fragment of the type is satisfiable in `N`
  have hp_fin : ∀ F : Finset (L.Formula (B ⊕ Fin 1)), (∀ ψ ∈ F, ψ ∈ P) →
      ∃ x : Fin 1 → N, ∀ ψ ∈ F,
        @BoundedFormula.Realize L N _ (B ⊕ Fin 1) 0 ψ (Sum.elim (Subtype.val : B → N) x)
          (fun i : Fin 0 => i.elim0) := by
    intro F hF
    obtain ⟨x, hx⟩ := finSat_of_elemOn h m F (fun ψ hψ => (hPmem ψ).mp (hF ψ hψ))
    exact ⟨x, fun ψ hψ =>
      (formulaRealize_iff_bounded ψ (Sum.elim (Subtype.val : B → N) x)).mp (hx ψ hψ)⟩
  -- `κ`-saturation realizes the type
  obtain ⟨x, hx⟩ := hsat B hκ P hp_fin
  have hx' : ∀ ψ : L.Formula (B ⊕ Fin 1), ψ.Realize w →
      ψ.Realize (Sum.elim (Subtype.val : B → N) x) := fun ψ hψ =>
    (formulaRealize_iff_bounded ψ (Sum.elim (Subtype.val : B → N) x)).mp
      (hx ψ ((hPmem ψ).mpr hψ))
  -- the type is complete: it is closed under negation
  have htype : ∀ ψ : L.Formula (B ⊕ Fin 1),
      ψ.Realize w ↔ ψ.Realize (Sum.elim (Subtype.val : B → N) x) := by
    intro ψ
    refine ⟨hx' ψ, fun hN => ?_⟩
    by_contra hM
    have hnot : ψ.not.Realize w := by rw [Formula.realize_not]; exact hM
    have h2 := hx' ψ.not hnot
    rw [Formula.realize_not] at h2
    exact h2 hN
  refine ⟨x 0, ?_, ?_⟩
  · -- `x 0` is not one of the parameters, because the type says so
    intro hmem
    have hb : (((Term.equal (Term.var (Sum.inr 0))
        (Term.var (Sum.inl (⟨x 0, hmem⟩ : B)))) : L.Formula (B ⊕ Fin 1))).not.Realize w := by
      simp only [Formula.realize_not, Formula.realize_equal, Term.realize_var, hw, Sum.elim_inr,
        Sum.elim_inl]
      exact fun hc => hm (Set.mem_range.mpr ⟨⟨x 0, hmem⟩, hc.symm⟩)
    have hbN := (htype _).mp hb
    rw [Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var] at hbN
    rw [Sum.elim_inr, Sum.elim_inl] at hbN
    exact hbN rfl
  · -- the relabelling argument: `x 0` and `m` have the same type over `B`
    intro φ
    let g : ↥(insert (x 0) B) → B ⊕ Fin 1 := insertSum B (x 0)
    have ha1 : (Sum.elim (Subtype.val : B → N) x) ∘ g =
        (Subtype.val : ↥(insert (x 0) B) → N) := by
      show (Sum.elim (Subtype.val : B → N) x) ∘ insertSum B (x 0) =
        (Subtype.val : ↥(insert (x 0) B) → N)
      funext y
      rw [Function.comp_apply]
      by_cases hy : (y : N) ∈ B
      · simp only [insertSum_apply_of_mem y hy, Sum.elim_inl]
      · simp only [insertSum_apply_of_not_mem y hy, Sum.elim_inr]
        exact (eq_of_mem_insert_of_not_mem hy).symm
    have ha2 : (Sum.elim τ (fun _ : Fin 1 => m)) ∘ g = PEM.extendFun τ (x 0) m := by
      show (Sum.elim τ (fun _ : Fin 1 => m)) ∘ insertSum B (x 0) = PEM.extendFun τ (x 0) m
      exact extendFun_eq_comp τ m
    have h1 : (φ.relabel g).Realize (Sum.elim (Subtype.val : B → N) x) ↔
        φ.Realize (Subtype.val : ↥(insert (x 0) B) → N) := by
      rw [Formula.realize_relabel]
      exact iff_of_eq (congrArg (fun v : ↥(insert (x 0) B) → N => φ.Realize v) ha1)
    have h2 : (φ.relabel g).Realize w ↔ φ.Realize (PEM.extendFun τ (x 0) m) := by
      rw [hw, Formula.realize_relabel]
      exact iff_of_eq (congrArg (fun v : ↥(insert (x 0) B) → M => φ.Realize v) ha2)
    exact h1.symm.trans ((htype (φ.relabel g)).symm.trans h2)

end Work.WilC5
