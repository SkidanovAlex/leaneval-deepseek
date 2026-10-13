import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ExtSatAux
import Submission.Work.WilC5.ExtSatChain
import Submission.Work.WilC5.ElemOnExtendAux
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-!
# The extension property from model completeness

This file proves `Work.WilC5.hasExtProp_of_modelComplete`: if the theory `T` is model complete
(`WilkiesDesign.CG.ModelComplete`, i.e. every embedding between models of `T` is elementary), then
an embedding `σ : A → N` of a *substructure* `A ⊆ M` which is itself a model of `T` extends to an
embedding `M → N`, as soon as `N` is `κ`-saturated with `κ > |M|`.

The proof has two parts.

* Model completeness makes `σ` elementary (in the strong sense of the comparison between
  `M`-realization with the parameters interpreted by the inclusion `A ↪ M` and `N`-realization
  with the parameters interpreted by `σ`), by applying it to the inclusion `A ↪ M` and to `σ`.
  This is `realize_iff_of_modelComplete`, and `elemOn_range_of_modelComplete` turns it into the
  initial partial elementary map `τ₀ = σ⁻¹` of the Zorn argument.
* The Zorn argument of `extends_of_elementary_sat`: partial elementary maps `B → M` with
  `B ⊆ N`, `range σ ⊆ B`, extending `σ⁻¹`; chains have upper bounds (`PEM.iUnion_valid`), and a
  maximal element must be surjective, since otherwise the type of a missing value over `B` can be
  realized by saturation (`elemOn_extend_of_sat`).  A surjective partial elementary map is the
  inverse of the desired embedding (`embedding_of_surjective`).
-/

/-- **Model completeness gives the comparison between `M` and `N`.**  If `A ⊆ M` is a
substructure which is a model of the model complete theory `T`, if `M, N ⊨ T` and if
`σ : A → N` is an embedding, then for every formula `φ` with free variables in an arbitrary type
`α` and every `v : α → A`, `φ` holds of the tuple `v` in `M` (parameters interpreted by the
inclusion `A ↪ M`) if and only if it holds of the tuple `σ ∘ v` in `N`. -/
theorem realize_iff_of_modelComplete {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    (hMC : WilkiesDesign.CG.ModelComplete T) {M N : Type} [L.Structure M] [L.Structure N]
    (hM : M ⊨ T) (hN : N ⊨ T) (A : L.Substructure M) (hA : A ⊨ T) (σ : L.Embedding A N) :
    ∀ {α : Type} (φ : L.Formula α) (v : α → A),
      @Formula.Realize L M _ α φ ((Subtype.val : A → M) ∘ v) ↔
      @Formula.Realize L N _ α φ ((σ : A → N) ∘ v) := by
  haveI hA' : A ⊨ T := hA
  haveI hM' : M ⊨ T := hM
  haveI hN' : N ⊨ T := hN
  let e₁ : A ↪ₑ[L] M :=
    ⟨Substructure.subtype A, fun n ψ x => hMC A M (Substructure.subtype A) ψ x⟩
  let e₂ : A ↪ₑ[L] N := ⟨(σ : A → N), fun n ψ x => hMC A N σ ψ x⟩
  intro α φ v
  have h1 : @Formula.Realize L M _ α φ ((Subtype.val : A → M) ∘ v) ↔
      @Formula.Realize L A _ α φ v := e₁.map_formula φ v
  have h2 : @Formula.Realize L N _ α φ ((σ : A → N) ∘ v) ↔
      @Formula.Realize L A _ α φ v := e₂.map_formula φ v
  exact h1.trans h2.symm

/-- The chosen preimage of `y ∈ range σ` under the embedding `σ`. -/
def invFun {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]
    {A : L.Substructure M} (σ : L.Embedding A N) : ↥(Set.range (σ : A → N)) → A :=
  fun y => Classical.choose y.2

/-- The chosen preimage of `y`, as an element of `M`. -/
abbrev invEmb {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]
    {A : L.Substructure M} (σ : L.Embedding A N) : ↥(Set.range (σ : A → N)) → M :=
  fun y => ((invFun σ y : A) : M)

theorem invFun_spec {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]
    {A : L.Substructure M} (σ : L.Embedding A N) (y : ↥(Set.range (σ : A → N))) :
    (σ (invFun σ y) : N) = (y : N) :=
  Classical.choose_spec y.2

/-- **The inverse of `σ` is a partial elementary map on `range σ`.** -/
theorem elemOn_range_of_modelComplete {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    (hMC : WilkiesDesign.CG.ModelComplete T) {M N : Type} [L.Structure M] [L.Structure N]
    (hM : M ⊨ T) (hN : N ⊨ T) (A : L.Substructure M) (hA : A ⊨ T) (σ : L.Embedding A N) :
    @ElemOn L M N _ _ (Set.range (σ : A → N)) (fun y => ((invFun σ y : A) : M)) := by
  intro φ
  have hrel1 : (φ.relabel (invFun σ)).Realize (fun a : A => (σ a : N)) ↔
      φ.Realize (Subtype.val : ↥(Set.range (σ : A → N)) → N) := by
    rw [Formula.realize_relabel]
    refine iff_of_eq (congrArg (fun w : ↥(Set.range (σ : A → N)) → N => φ.Realize w) ?_)
    funext y
    exact invFun_spec σ y
  have hrel2 : (φ.relabel (invFun σ)).Realize (Subtype.val : A → M) ↔
      φ.Realize (fun y => ((invFun σ y : A) : M)) := by
    rw [Formula.realize_relabel]
    rfl
  have hmain : (φ.relabel (invFun σ)).Realize (Subtype.val : A → M) ↔
      (φ.relabel (invFun σ)).Realize (fun a : A => (σ a : N)) := by
    have h := realize_iff_of_modelComplete hMC hM hN A hA σ (φ.relabel (invFun σ)) (id : A → A)
    simpa using h
  exact hrel1.symm.trans (hmain.symm.trans hrel2)

/-- **A surjective partial elementary map is the inverse of an embedding.**  If `τ : B → M` is
elementary (for the comparison `N` versus `M`), surjective, contains `range σ` and inverts `σ`
there, then `τ⁻¹ : M → N` is an `L`-embedding extending `σ`. -/
theorem embedding_of_surjective {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {A : L.Substructure M} {σ : L.Embedding A N} {B : Set N} {τ : B → M}
    (h : @ElemOn L M N _ _ B τ) (hsurj : ∀ m : M, ∃ b : B, τ b = m)
    (hrange : Set.range (σ : A → N) ⊆ B) (hagree : ∀ a : A, ∀ hh : (σ a : N) ∈ B, τ ⟨σ a, hh⟩ = a) :
    ∃ g : L.Embedding M N, ∀ a : A, g a = σ a := by
  classical
  let bof : M → B := fun m => Classical.choose (hsurj m)
  have bof_spec : ∀ m : M, τ (bof m) = m := fun m => Classical.choose_spec (hsurj m)
  let g : M → N := fun m => ((bof m : B) : N)
  have hinjτ : Function.Injective τ := elemOn_injective h
  have hinj : Function.Injective g := by
    intro m₁ m₂ h12
    have hb : bof m₁ = bof m₂ := Subtype.ext h12
    calc m₁ = τ (bof m₁) := (bof_spec m₁).symm
      _ = τ (bof m₂) := by rw [hb]
      _ = m₂ := bof_spec m₂
  have hmap_fun : ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M),
      g (@Structure.funMap L M _ n f x) = @Structure.funMap L N _ n f (g ∘ x) := by
    intro n f x
    have hbτ : ∀ i, τ (bof (x i)) = x i := fun i => bof_spec (x i)
    have hkey : @Structure.funMap L N _ n f (fun i => ((bof (x i) : B) : N)) =
        ((bof (@Structure.funMap L M _ n f x) : B) : N) := by
      have hφ := h (Term.equal
        (Term.func f (fun i => Term.var (bof (x i))))
        (Term.var (bof (@Structure.funMap L M _ n f x))))
      rw [Formula.realize_equal, Formula.realize_equal] at hφ
      simp only [Term.realize_func, Term.realize_var] at hφ
      refine hφ.mpr ?_
      simp only [bof_spec]
    show g (@Structure.funMap L M _ n f x) = @Structure.funMap L N _ n f (g ∘ x)
    rw [show g (@Structure.funMap L M _ n f x) =
      ((bof (@Structure.funMap L M _ n f x) : B) : N) from rfl, ← hkey]
    rfl
  have hmap_rel : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → M),
      @Structure.RelMap L N _ n r (g ∘ x) ↔ @Structure.RelMap L M _ n r x := by
    intro n r x
    have hφ := h (Relations.formula r (fun i => Term.var (bof (x i))))
    rw [Formula.realize_rel, Formula.realize_rel] at hφ
    simp only [Term.realize_var] at hφ
    rw [show (fun i => τ (bof (x i))) = x from funext fun i => bof_spec (x i)] at hφ
    have hg : (g ∘ x) = (fun i => ((bof (x i) : B) : N)) := rfl
    rw [hg]
    exact hφ
  refine ⟨⟨⟨g, hinj⟩, hmap_fun, hmap_rel⟩, ?_⟩
  intro a
  have hmem : (σ a : N) ∈ B := hrange (Set.mem_range_self a)
  have h3 : bof a = ⟨σ a, hmem⟩ := hinjτ (by rw [bof_spec a, hagree a hmem])
  show ((bof a : B) : N) = σ a
  rw [h3]

/-- **The Zorn argument.**  If `σ : A → N` has an elementary inverse on its range, then it extends
to an embedding of `M` into `N`, provided `N` is `κ`-saturated with `κ > |M|`. -/
theorem extends_of_elemOn {L : FirstOrder.Language.{0, 0}} {T : L.Theory} {M N : Type}
    [L.Structure M] [L.Structure N] (hM : M ⊨ T) (hN : N ⊨ T)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk M < κ) (hsat : @Work.WilC5.IsSaturated L N _ κ)
    (A : L.Substructure M) (σ : L.Embedding A N)
    (helem : @ElemOn L M N _ _ (Set.range (σ : A → N))
      (fun y => ((invFun σ y : A) : M))) :
    ∃ g : L.Embedding M N, ∀ a : A, g a = σ a := by
  classical
  -- the partial elementary maps extending `σ⁻¹`
  let s : Set (PEM L M N) :=
    {p | p.Valid ∧ Set.range (σ : A → N) ⊆ p.1 ∧
      ∀ a : A, ∀ hh : (σ a : N) ∈ p.1, p.2 ⟨σ a, hh⟩ = a}
  have hbase : (⟨Set.range (σ : A → N), fun y => ((invFun σ y : A) : M)⟩ : PEM L M N) ∈ s := by
    refine ⟨helem, subset_rfl, ?_⟩
    intro a hh
    have hspec : invFun σ ⟨σ a, hh⟩ = a := by
      apply σ.injective
      rw [invFun_spec]
    exact congrArg (fun x : A => (x : M)) hspec
  -- chains have upper bounds
  have hub : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hchain y hy
    obtain ⟨ub, hubvalid, hubdom, huble⟩ :=
      PEM.iUnion_valid hchain ⟨y, hy⟩ (fun p hp => (hcs hp).1)
    refine ⟨ub, ⟨hubvalid, ?_, ?_⟩, huble⟩
    · intro a ha
      rw [hubdom]
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, (hcs hy).2.1 ha⟩⟩
    · intro a hh
      have hy1 : (σ a : N) ∈ y.1 := (hcs hy).2.1 (Set.mem_range_self a)
      have key := (huble y hy).2 ⟨σ a, hy1⟩
      rw [show (⟨σ a, hh⟩ : ub.1) = ⟨σ a, (huble y hy).1 hy1⟩ from Subtype.ext rfl] at key
      rw [key]
      exact (hcs hy).2.2 a hy1
  obtain ⟨pstar, -, hpstar_max⟩ :=
    zorn_le_nonempty₀ s hub (⟨Set.range (σ : A → N), fun y => ((invFun σ y : A) : M)⟩ : PEM L M N)
      hbase
  have hpstar_valid : @ElemOn L M N _ _ pstar.1 pstar.2 := hpstar_max.1.1
  -- a maximal element is surjective
  have hsurj : ∀ m : M, ∃ b : pstar.1, pstar.2 b = m := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm⟩ := hcon
    have hm' : m ∉ Set.range pstar.2 := by
      rintro ⟨b, hb⟩
      exact hm b hb
    have hκstar : Cardinal.mk pstar.1 < κ :=
      lt_of_le_of_lt (mk_le_of_elemOn hpstar_valid) hκ
    obtain ⟨n, hnB, hext⟩ := elemOn_extend_of_sat hpstar_valid κ hκstar hsat m hm'
    have hy'_s : (⟨insert n pstar.1, PEM.extendFun pstar.2 n m⟩ : PEM L M N) ∈ s := by
      refine ⟨hext, ?_, ?_⟩
      · exact Set.Subset.trans hpstar_max.1.2.1 (Set.subset_insert _ _)
      · intro a hh
        have ha_mem : (σ a : N) ∈ pstar.1 :=
          hpstar_max.1.2.1 (Set.mem_range_self (f := (σ : ↥A → N)) a)
        show PEM.extendFun pstar.2 n m ⟨σ a, hh⟩ = (a : M)
        rw [PEM.extendFun_apply_of_mem pstar.2 ⟨σ a, hh⟩ ha_mem]
        exact hpstar_max.1.2.2 a ha_mem
    have hle' : pstar ≤ (⟨insert n pstar.1, PEM.extendFun pstar.2 n m⟩ : PEM L M N) := by
      change ∃ h : pstar.1 ⊆ insert n pstar.1,
        ∀ x : pstar.1, PEM.extendFun pstar.2 n m ⟨x.1, h x.2⟩ = pstar.2 x
      exact ⟨fun x hx => Set.mem_insert_of_mem n hx, fun x =>
        PEM.extendFun_apply_of_mem pstar.2 ⟨x.1, _⟩ x.2⟩
    have hnle : ¬ (⟨insert n pstar.1, PEM.extendFun pstar.2 n m⟩ : PEM L M N) ≤ pstar := by
      intro hle
      exact hnB (hle.1 (Set.mem_insert_iff.mpr (Or.inl rfl)))
    exact hnle (hpstar_max.2 hy'_s hle')
  exact embedding_of_surjective hpstar_valid hsurj hpstar_max.1.2.1 hpstar_max.1.2.2

theorem hasExtProp_of_modelComplete {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    (hMC : WilkiesDesign.CG.ModelComplete T) :
    ∀ (M N : Type) [L.Structure M] [L.Structure N],
      FirstOrder.Language.Theory.Model M T → FirstOrder.Language.Theory.Model N T →
      ∀ (κ : Cardinal.{0}), Cardinal.mk M < κ → @Work.WilC5.IsSaturated L N _ κ →
      ∀ (A : L.Substructure M), FirstOrder.Language.Theory.Model A T →
        ∀ (σ : L.Embedding A N), ∃ g : L.Embedding M N, ∀ a : A, g a = σ a := by
  intro M N _ _ hM hN κ hκ hsat A hA σ
  exact extends_of_elemOn hM hN κ hκ hsat A σ (elemOn_range_of_modelComplete hMC hM hN A hA σ)

end Work.WilC5
