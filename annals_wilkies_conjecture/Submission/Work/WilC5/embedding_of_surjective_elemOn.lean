/-
  WilC5 — the inverse of a surjective partial elementary map is an embedding.

  Let `B ⊆ N`, `τ : B → M` be a *partial elementary map* (`ElemOn B τ`) which is surjective onto
  `M`, and let `σ : A ↪[L] N` be an `L`-embedding of the substructure `A ≤ M` whose range lies in
  `B` and on which `τ` is the inverse of `σ`.  Then `M` embeds into `N` in a way extending `σ`:
  namely the inverse of `τ`, which is well defined because `ElemOn` forces `τ` to be injective.

  The elementarity of `τ` (applied to the atomic formulas `f(x̄) = y` and `R(x̄)`) supplies
  preservation of function and relation symbols, the injectivity supplies injectivity of the map,
  and `hagree` supplies that the map extends `σ`.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false

open FirstOrder Language

namespace Work.WilC5

theorem embedding_of_surjective_elemOn {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {A : L.Substructure M} {σ : L.Embedding A N} {B : Set N} {τ : B → M}
    (h : @ElemOn L M N _ _ B τ) (hsurj : ∀ m : M, ∃ b : B, τ b = m)
    (hrange : Set.range σ ⊆ B) (hagree : ∀ a : A, ∀ hh : (σ a : N) ∈ B, τ ⟨σ a, hh⟩ = a) :
    ∃ g : L.Embedding M N, ∀ a : A, g a = σ a := by
  classical
  -- `τ` is injective, hence a bijection `B ≃ M`; `g` is its inverse, composed with `B ↪ N`.
  have hτinj : Function.Injective τ := elemOn_injective h
  let pre : M → B := fun m => Classical.choose (hsurj m)
  have hpre : ∀ m : M, τ (pre m) = m := fun m => Classical.choose_spec (hsurj m)
  let g : M → N := fun m => (pre m : N)
  -- `g` is injective
  have hginj : Function.Injective g := by
    intro m₁ m₂ hmm
    have h1 : pre m₁ = pre m₂ := Subtype.val_injective hmm
    calc m₁ = τ (pre m₁) := (hpre m₁).symm
      _ = τ (pre m₂) := by rw [h1]
      _ = m₂ := hpre m₂
  -- `g` commutes with the function symbols
  have hfun : ∀ {n : ℕ} (F : L.Functions n) (x : Fin n → M),
      g (Structure.funMap F x) = Structure.funMap F (g ∘ x) := by
    intro n F x
    change (pre (Structure.funMap F x) : N) = Structure.funMap F (fun i : Fin n => (pre (x i) : N))
    -- the formula `F (x̄) = F x` with parameters `pre (x i)`, `pre (F x)` from `B`
    let φ : L.Formula B := Term.equal (Term.func F (fun i => Term.var (pre (x i))))
      (Term.var (pre (Structure.funMap F x)))
    have hM : φ.Realize τ := by simp [φ, hpre]
    have hN : φ.Realize (Subtype.val : B → N) := (h φ).mpr hM
    simpa [φ] using hN.symm
  -- `g` preserves and reflects the relation symbols
  have hrel : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → M),
      Structure.RelMap R (g ∘ x) ↔ Structure.RelMap R x := by
    intro n R x
    change Structure.RelMap R (fun i : Fin n => (pre (x i) : N)) ↔ Structure.RelMap R x
    -- the formula `R (x̄)` with parameters `pre (x i)` from `B`
    let φ : L.Formula B := R.formula (fun i => Term.var (pre (x i)))
    have key : φ.Realize (Subtype.val : B → N) ↔ φ.Realize τ := h φ
    have e1 : φ.Realize (Subtype.val : B → N) ↔
        Structure.RelMap R (fun i => (pre (x i) : N)) := by simp [φ]
    have e2 : φ.Realize τ ↔ Structure.RelMap R (fun i => τ (pre (x i))) := by simp [φ]
    have hiff : Structure.RelMap R (fun i => (pre (x i) : N)) ↔
        Structure.RelMap R (fun i => τ (pre (x i))) := (e1.symm.trans key).trans e2
    have hxx : Structure.RelMap R x ↔ Structure.RelMap R (fun i => τ (pre (x i))) := by
      simp [hpre]
    exact hiff.trans hxx.symm
  refine ⟨⟨⟨g, hginj⟩, hfun, hrel⟩, ?_⟩
  -- `g` extends `σ`: both `pre a` and `σ a` are the unique preimage of `a` under `τ`
  intro a
  show (pre (a : M) : N) = σ a
  have hb : pre (a : M) = ⟨σ a, hrange ⟨a, rfl⟩⟩ := by
    apply hτinj
    rw [hpre (a : M), hagree a (hrange ⟨a, rfl⟩)]
  exact congrArg Subtype.val hb

end Work.WilC5
