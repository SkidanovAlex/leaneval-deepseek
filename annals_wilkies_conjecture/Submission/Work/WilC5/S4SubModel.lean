/-
  WilC5 — the **submodel extension property** and its assembly into model completeness.

  van den Dries–Macintyre–Marker prove (Ann. of Math. 140 (1994), Theorem 4.1) that a
  log-preserving embedding of a *submodel* `F₀ ⊨ T_an` of a model `K ⊨ T_an(exp)` into a
  `|K|⁺`-saturated model `L ⊨ T_an(exp)` extends to an embedding of `K` into `L`, and derive from
  it (their Corollary 4.5) quantifier elimination for `T_an(exp,log)` and model completeness of
  `T_an(exp)`.

  This module formalizes the *second* half of that derivation in the sharpest form the source
  supports, and in a form that needs no quantifier elimination at all:

  * `Work.WilC5.HasExtPropSub L T` — the extension property above, restricted to substructures
    `A ⊆ M` which are themselves models of `T` (van den Dries–Macintyre–Marker apply it to the
    ranges of embeddings of models, so this is exactly what their proof of Corollary 4.5 uses);
  * `Work.WilC5.realize_of_hasExtPropSub` — **the Sacks-test ingredient**: if `HasExtPropSub L T`
    holds then every embedding of models of `T` into a `κ`-saturated model of `T` (`κ > |M|`) is
    elementary.  This is the induction of `Work.WilC5.realize_goodEmb`, with the crucial
    observation that at the `∀`-step the extension property is applied to the *image* `f(M)`, a
    substructure of the target which is isomorphic to `M`, hence a model of `T`;
  * `Work.WilC5.modelComplete_of_hasExtPropSub` — hence `HasExtPropSub L T` implies model
    completeness of `T` (`WilkiesDesign.CG.ModelComplete`), by passing to a saturated elementary
    extension.

  Together with `Work.WilC5.hasExtProp_of_modelComplete`, which proves the converse, this shows
  that for any theory `T`
  `HasExtPropSub L T ↔ WilkiesDesign.CG.ModelComplete T`, so that the residual content of area C5
  may be stated either way; `Submission/Work/WilC5/S4SubTE.lean` states it for `T = TE`.
-/
import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ExistsSaturated
import Submission.Work.WilC5.QE
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- **The extension property for submodels.**  Every embedding `σ : A → N` of an `L`-substructure
`A` of a model `M ⊨ T` which is *itself* a model of `T` into a model `N ⊨ T` which is `κ`-saturated
for some `κ > |M|` extends to an embedding `M → N`. -/
def HasExtPropSub (L : FirstOrder.Language.{0, 0}) (T : L.Theory) : Prop :=
  ∀ (M N : Type) [L.Structure M] [L.Structure N],
    FirstOrder.Language.Theory.Model M T → FirstOrder.Language.Theory.Model N T →
    ∀ (κ : Cardinal.{0}), Cardinal.mk M < κ →
    @Work.WilC5.IsSaturated L N _ κ →
    ∀ (A : L.Substructure M), FirstOrder.Language.Theory.Model A T →
      ∀ (σ : FirstOrder.Language.Embedding L A N),
        ∃ g : FirstOrder.Language.Embedding L M N, ∀ a : A, g a = σ a

/-- **Every embedding of models of `T` into a `κ`-saturated model of `T` is elementary**, assuming
the submodel extension property `HasExtPropSub L T`.

This is the induction on formulas of Sacks' quantifier-elimination test (vdDMM's proof of Corollary
4.5, quoting [15]).  At the `∀`-step one extends the embedding `σ⁻¹` of the *range* `f(M)`
(which, being isomorphic to `M ⊨ T`, is a model of `T`) to an embedding `N → P` into a saturated
elementary extension `P` of `M`; the induction hypothesis applied to that embedding transfers the
witness. -/
theorem realize_of_hasExtPropSub (hext : HasExtPropSub L T) :
    ∀ {α : Type} {n : ℕ} (ψ : L.BoundedFormula α n)
      {M N : Type} [L.Structure M] [L.Structure N]
      (hM : M ⊨ T) (hN : N ⊨ T) {κ : Cardinal.{0}} (hκ : Cardinal.mk M < κ)
      (hsat : @IsSaturated L N _ κ) (f : L.Embedding M N) (v : α → M) (xs : Fin n → M),
      ψ.Realize (f ∘ v) (f ∘ xs) ↔ ψ.Realize v xs := by
  intro α n ψ
  induction ψ with
  | falsum =>
    intro M N _ _ hM hN κ hκ hsat f v xs
    exact Iff.rfl
  | equal t₁ t₂ =>
    intro M N _ _ hM hN κ hκ hsat f v xs
    exact BoundedFormula.IsQF.realize_embedding
      (BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal t₁ t₂)) f
  | rel R ts =>
    intro M N _ _ hM hN κ hκ hsat f v xs
    exact BoundedFormula.IsQF.realize_embedding
      (BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel R ts)) f
  | imp φ ψ ihφ ihψ =>
    intro M N _ _ hM hN κ hκ hsat f v xs
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
    exact Iff.imp (ihφ hM hN hκ hsat f v xs) (ihψ hM hN hκ hsat f v xs)
  | all φ ih =>
    intro M N _ _ hM hN κ hκ hsat f v xs
    constructor
    · -- from the truth in `N` to the truth in `M`
      intro hv
      rw [BoundedFormula.realize_all] at hv ⊢
      intro m
      refine (ih hM hN hκ hsat f v (Fin.snoc xs m)).mp ?_
      rw [Fin.comp_snoc]
      exact hv (f m)
    · -- from the truth in `M` to the truth in `N`: this is where saturation enters
      intro hv
      rw [BoundedFormula.realize_all] at hv ⊢
      intro a
      -- a `κ'`-saturated elementary extension `P` of `M`, with `κ' > |N|`
      obtain ⟨P, instP, e, hsatP⟩ := ExistsSaturated (L := L) M (2 ^ Cardinal.mk N)
      letI : L.Structure P := instP
      have hP : P ⊨ T := (e.theory_model_iff T).mp hM
      -- the restriction of `e` to the range of `f` (i.e. `e ∘ f⁻¹`)
      let σ : L.Embedding ↥(f.toHom.range) P :=
        (e.toEmbedding).comp (f.equivRange.symm).toEmbedding
      have hσ : ∀ m : M, σ ⟨f m, (Hom.mem_range).mpr ⟨m, rfl⟩⟩ = e m := by
        intro m
        have h1 : f.equivRange m = ⟨f m, (Hom.mem_range).mpr ⟨m, rfl⟩⟩ :=
          Subtype.ext (Embedding.equivRange_apply f m)
        change e (f.equivRange.symm ⟨f m, (Hom.mem_range).mpr ⟨m, rfl⟩⟩) = e m
        rw [← h1]
        exact congrArg e (Language.Equiv.symm_apply_apply (f.equivRange) m)
      -- the range of `f` is a model of `T`: it is `M` transported along an isomorphism
      have hrange : (↥(f.toHom.range)) ⊨ T :=
        (f.equivRange.toElementaryEmbedding.theory_model_iff T).mp hM
      -- the extension property extends it to all of `N`
      obtain ⟨h, hh⟩ := hext N P hN hP (2 ^ Cardinal.mk N) (Cardinal.cantor (Cardinal.mk N))
        hsatP (f.toHom.range) hrange σ
      have hhf : ∀ m : M, h (f m) = e m := by
        intro m
        have hmem := hh ⟨f m, (Hom.mem_range).mpr ⟨m, rfl⟩⟩
        rw [hσ m] at hmem
        exact hmem
      -- the induction hypothesis for the body, applied to `h` and the witness `a`
      have hIH := ih (M := N) (N := P) hN hP (κ := 2 ^ Cardinal.mk N)
        (Cardinal.cantor (Cardinal.mk N)) hsatP h (f ∘ v) (Fin.snoc (f ∘ xs) a)
      refine hIH.mp ?_
      have hcomp1 : (h ∘ (f ∘ v)) = (e ∘ v) := funext fun i => hhf (v i)
      have hcomp2 : (h ∘ (Fin.snoc (f ∘ xs) a)) = Fin.snoc (e ∘ xs) (h a) := by
        rw [Fin.comp_snoc]
        congr 1
        funext i
        exact hhf (xs i)
      rw [hcomp1, hcomp2]
      -- evaluate the `∀`-formula of `M` in `P` at `h a`
      have hforall : (BoundedFormula.all φ).Realize (e ∘ v) (e ∘ xs) :=
        (e.map_boundedFormula (BoundedFormula.all φ) v xs).mpr
          ((BoundedFormula.realize_all (M := M) (θ := φ) (v := v) (xs := xs)).mpr hv)
      exact (BoundedFormula.realize_all (M := P) (θ := φ) (v := e ∘ v)
        (xs := e ∘ xs)).mp hforall (h a)

/-- **The submodel extension property implies model completeness.**

If every embedding of a submodel `A ⊨ T` of a model `M ⊨ T` into a `κ`-saturated model of `T`
(`κ > |M|`) extends to `M`, then `T` is model complete: given an embedding `f : M ↪ N` of models,
pass to a saturated elementary extension `P` of `N`, where `f` is elementary by
`Work.WilC5.realize_of_hasExtPropSub`, and descend along the elementary embedding `N → P`. -/
theorem modelComplete_of_hasExtPropSub (hext : HasExtPropSub L T) :
    WilkiesDesign.CG.ModelComplete T := by
  intro M N _instM _instN hM hN f n φ x
  obtain ⟨P, instP, e, hsatP⟩ := ExistsSaturated (L := L) N (2 ^ Cardinal.mk M)
  letI : L.Structure P := instP
  have hP : P ⊨ T := (e.theory_model_iff T).mp hN
  have hc : Cardinal.mk M < 2 ^ Cardinal.mk M := Cardinal.cantor (Cardinal.mk M)
  have h1 : BoundedFormula.Realize (L := L) (M := P) φ ((e.toEmbedding.comp f) ∘ x)
        ((e.toEmbedding.comp f) ∘ (default : Fin 0 → M)) ↔
      BoundedFormula.Realize (L := L) (M := M) φ x (default : Fin 0 → M) :=
    realize_of_hasExtPropSub (L := L) (T := T) hext φ hM hP hc hsatP
      (e.toEmbedding.comp f) x (default : Fin 0 → M)
  have hbP := Formula.boundedFormula_realize_eq_realize (L := L) (M := P) φ
    ((e.toEmbedding.comp f) ∘ x) ((e.toEmbedding.comp f) ∘ (default : Fin 0 → M))
  have hbM := Formula.boundedFormula_realize_eq_realize (L := L) (M := M) φ x
    (default : Fin 0 → M)
  have he := e.map_formula φ ((f : M → N) ∘ x)
  exact he.symm.trans (hbP.symm.trans (h1.trans hbM))

end Work.WilC5
