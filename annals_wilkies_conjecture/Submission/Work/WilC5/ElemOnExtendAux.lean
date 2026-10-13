import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-- `Formula.Realize` in the `BoundedFormula` form used by `IsSaturated`. -/
theorem formula_realize_eq {L : FirstOrder.Language} {M : Type} [L.Structure M] {α : Type}
    (φ : L.Formula α) (v : α → M) :
    (@Formula.Realize L M _ α φ v) ↔
      @BoundedFormula.Realize L M _ α 0 φ v (fun i : Fin 0 => i.elim0) := by
  unfold Formula.Realize
  exact iff_of_eq (congrArg (fun u : Fin 0 → M => @BoundedFormula.Realize L M _ α 0 φ v u)
    (show (default : Fin 0 → M) = (fun i : Fin 0 => i.elim0) from by
      funext i
      exact i.elim0))

/-- `IsSaturated`, restated with `Formula.Realize` (the form used by `ElemOn`). -/
theorem IsSaturated.formula {L : FirstOrder.Language} {M : Type} [L.Structure M] {κ : Cardinal.{0}}
    (hsat : @IsSaturated L M _ κ) (A : Set M) (hA : Cardinal.mk A < κ)
    (p : Set (L.Formula (A ⊕ Fin 1)))
    (hp : ∀ F : Finset (L.Formula (A ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p) →
      ∃ x : Fin 1 → M, ∀ φ ∈ F, @Formula.Realize L M _ (A ⊕ Fin 1) φ (Sum.elim Subtype.val x)) :
    ∃ x : Fin 1 → M, ∀ φ ∈ p, @Formula.Realize L M _ (A ⊕ Fin 1) φ (Sum.elim Subtype.val x) := by
  obtain ⟨x, hx⟩ := hsat A hA p (fun F hF => by
    obtain ⟨y, hy⟩ := hp F hF
    exact ⟨y, fun φ hφ => (formula_realize_eq φ (Sum.elim (Subtype.val : A → M) y)).mp (hy φ hφ)⟩)
  exact ⟨x, fun φ hφ => (formula_realize_eq φ (Sum.elim (Subtype.val : A → M) x)).mpr (hx φ hφ)⟩

/-- **One-point extension of a partial elementary map.**  If `τ : B → M` is elementary, `N` is
`κ`-saturated with `|B| < κ` and `m ∈ M` is not a value of `τ`, then there is `n ∈ N \ B` such
that adjoining `n ↦ m` to `τ` is again elementary. -/
theorem elemOn_extend_of_sat {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M} (h : @ElemOn L M N _ _ B τ)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk B < κ) (hsat : @Work.WilC5.IsSaturated L N _ κ)
    (m : M) (hm : m ∉ Set.range τ) :
    ∃ n : N, n ∉ B ∧ @ElemOn L M N _ _ (insert n B) (PEM.extendFun τ n m) := by
  classical
  set w : B ⊕ Fin 1 → M := Sum.elim τ (fun _ : Fin 1 => m) with hw
  -- the type of `m` over `B`, together with the constraints "different from the parameters"
  let q : Set (L.Formula (B ⊕ Fin 1)) :=
    {ψ | @Formula.Realize L M _ (B ⊕ Fin 1) ψ w} ∪
    {ψ | ∃ b : B, ψ = (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl b))).not}
  have hneqM : ∀ b : B, @Formula.Realize L M _ (B ⊕ Fin 1)
      (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl b))).not w := by
    intro b
    rw [Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var]
    simp only [hw, Sum.elim_inr, Sum.elim_inl]
    exact fun hcon => hm ⟨b, hcon.symm⟩
  have hqM : ∀ ψ ∈ q, @Formula.Realize L M _ (B ⊕ Fin 1) ψ w := by
    intro ψ hψ
    rcases hψ with h1 | ⟨b, rfl⟩
    · exact h1
    · exact hneqM b
  -- every finite fragment of `q` is satisfiable in `N`
  have hfin : ∀ F : Finset (L.Formula (B ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ q) →
      ∃ x : Fin 1 → N, ∀ φ ∈ F,
        @Formula.Realize L N _ (B ⊕ Fin 1) φ (Sum.elim (Subtype.val : B → N) x) := by
    intro F hF
    haveI : Finite {φ : L.Formula (B ⊕ Fin 1) // φ ∈ F} := F.finite_toSet.to_subtype
    set Φ : L.Formula (B ⊕ Fin 1) :=
      BoundedFormula.iInf (fun ψ : {φ : L.Formula (B ⊕ Fin 1) // φ ∈ F} => ψ.1) with hΦ
    have hΦw : @Formula.Realize L M _ (B ⊕ Fin 1) Φ w := by
      rw [hΦ]
      exact (BoundedFormula.realize_iInf
        (f := fun ψ : {φ : L.Formula (B ⊕ Fin 1) // φ ∈ F} => ψ.1) (v := w) (v' := default)).mpr
        (fun ψ => hqM _ (hF _ ψ.2))
    have hEx : @Formula.Realize L M _ B (Φ.iExs (Fin 1)) τ := by
      refine (BoundedFormula.realize_iExs (φ := Φ) (γ := Fin 1) (v := τ) (v' := default)).mpr
        ⟨fun _ => m, ?_⟩
      rw [← hw]
      exact hΦw
    have hExN : @Formula.Realize L N _ B (Φ.iExs (Fin 1)) (Subtype.val : B → N) := (h _).mpr hEx
    obtain ⟨x, hx⟩ := (BoundedFormula.realize_iExs (φ := Φ) (γ := Fin 1)
      (v := (Subtype.val : B → N)) (v' := default)).mp hExN
    refine ⟨x, fun φ hφ => ?_⟩
    exact (BoundedFormula.realize_iInf
      (f := fun ψ : {φ : L.Formula (B ⊕ Fin 1) // φ ∈ F} => ψ.1)
      (v := Sum.elim (Subtype.val : B → N) x) (v' := default)).mp hx ⟨φ, hφ⟩
  obtain ⟨x, hx⟩ := hsat.formula B hκ q hfin
  refine ⟨x 0, ?_, ?_⟩
  · -- `x 0` is not a parameter
    intro hnB
    have hmem : (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl (⟨x 0, hnB⟩ : B)))).not ∈ q :=
      Set.mem_union_left _ (by
        show @Formula.Realize L M _ (B ⊕ Fin 1)
          (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl (⟨x 0, hnB⟩ : B)))).not w
        exact hneqM ⟨x 0, hnB⟩)
    have h1 : ¬ ((x 0 : N) = ((⟨x 0, hnB⟩ : B) : N)) := by
      have h2 := hx _ hmem
      rw [Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var] at h2
      simpa only [Sum.elim_inr, Sum.elim_inl] using h2
    exact h1 rfl
  · -- the extension is elementary
    set g : ↥(insert (x 0) B) → B ⊕ Fin 1 :=
      fun y => if h : (y : N) ∈ B then Sum.inl ⟨y.1, h⟩ else Sum.inr 0 with hg
    have hg_inl : ∀ (y : ↥(insert (x 0) B)) (h : (y : N) ∈ B),
        g y = Sum.inl (⟨y.1, h⟩ : B) := by
      intro y h
      show (if h' : (y : N) ∈ B then Sum.inl (⟨y.1, h'⟩ : B) else Sum.inr 0) =
        Sum.inl (⟨y.1, h⟩ : B)
      split_ifs <;> rfl
    have hg_inr : ∀ y : ↥(insert (x 0) B), (y : N) ∉ B → g y = Sum.inr 0 := by
      intro y h
      show (if h' : (y : N) ∈ B then Sum.inl (⟨y.1, h'⟩ : B) else Sum.inr 0) = Sum.inr 0
      split_ifs <;> rfl
    have ha1 : (Sum.elim (Subtype.val : B → N) x) ∘ g = (Subtype.val : ↥(insert (x 0) B) → N) := by
      funext y
      by_cases h : (y : N) ∈ B
      · rw [Function.comp_apply, hg_inl y h]
        simp only [Sum.elim_inl]
      · rw [Function.comp_apply, hg_inr y h]
        simp only [Sum.elim_inr]
        rcases Set.mem_insert_iff.mp y.2 with h' | h'
        · exact h'.symm
        · exact absurd h' h
    have ha2 : (Sum.elim τ (fun _ : Fin 1 => m)) ∘ g = PEM.extendFun τ (x 0) m := by
      funext y
      by_cases h : (y : N) ∈ B
      · rw [Function.comp_apply, hg_inl y h]
        simp only [Sum.elim_inl]
        exact (PEM.extendFun_apply_of_mem τ y h).symm
      · rw [Function.comp_apply, hg_inr y h]
        simp only [Sum.elim_inr]
        exact (PEM.extendFun_apply_of_not_mem τ y h).symm
    intro φ
    have hφ1 : (φ.relabel g).Realize (Sum.elim (Subtype.val : B → N) x) ↔
        φ.Realize (Subtype.val : ↥(insert (x 0) B) → N) := by
      rw [Formula.realize_relabel]
      exact iff_of_eq (congrArg (fun w' : ↥(insert (x 0) B) → N => φ.Realize w') ha1)
    have hφ2 : (φ.relabel g).Realize (Sum.elim τ (fun _ : Fin 1 => m)) ↔
        φ.Realize (PEM.extendFun τ (x 0) m) := by
      rw [Formula.realize_relabel]
      exact iff_of_eq (congrArg (fun w' : ↥(insert (x 0) B) → M => φ.Realize w') ha2)
    have hkey : (φ.relabel g).Realize (Sum.elim (Subtype.val : B → N) x) ↔
        (φ.relabel g).Realize (Sum.elim τ (fun _ : Fin 1 => m)) := by
      constructor
      · intro hN
        by_contra hM'
        have hnot : (φ.relabel g).not ∈ q := Set.mem_union_left _ (by
          show @Formula.Realize L M _ (B ⊕ Fin 1) (φ.relabel g).not w
          rw [Formula.realize_not]
          exact hM')
        have h2 := hx _ hnot
        rw [Formula.realize_not] at h2
        exact h2 hN
      · intro hM
        exact hx _ (Set.mem_union_left _ hM)
    exact hφ1.symm.trans (hkey.trans hφ2)

end Work.WilC5
