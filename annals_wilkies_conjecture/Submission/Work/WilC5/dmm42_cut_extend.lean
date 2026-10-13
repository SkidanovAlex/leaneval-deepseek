import Mathlib
import Submission.Work.WilC5.cut_determines_type_gen
import Submission.Work.WilC5.exists_embedding_closure_of_same_type
import Submission.Work.WilC5.dcl_image_of_elementary
import Submission.Work.WilC5.ExistsEmbeddingClosurePoint
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-- **The cut determined by `σ` determines the `LRc`-type over `F`.**

`x : K` and `y : L` define the same order cut over `F` (transported by `σ`), so — over the
`dcl`-closed parameter set `F` — they satisfy the same `LRc`-formulas with parameters from `F`,
with the parameters interpreted by `σ`.  This is the hypothesis `htype` of
`Work.WilC5.ExistsEmbeddingClosurePoint`.

The proof reduces to the two-model cut theorem `Work.WilC5.cut_determines_type_gen` (which uses
`hOM`, o-minimality of the models of `TR`): by model completeness of `TR` the inclusion `F ↪ K`
and the embedding `σ : F ↪ L` are elementary, so `σ` is a partial elementary map on the parameter
set `F ⊆ K` with values in `L`, and the cut hypothesis is exactly the input of the cut theorem. -/
theorem cut_determines_type_F (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∀ {n : ℕ} (φ : WilkiesDesign.CG.LRc.Formula (F ⊕ Fin (n + 1))) (v : Fin n → F),
      φ.Realize (Sum.elim Subtype.val (Fin.cons x (fun i => (v i : K)))) ↔
        φ.Realize (Sum.elim (fun f : F => (σ f : L))
          (Fin.cons y (fun i => (σ (v i) : L)))) := by
  intro n φ v
  have hFmodel : (F : Type) ⊨ WilkiesDesign.CG.TR := hF
  -- elementarity of the inclusion `F → K` and of `σ : F → L`, by model completeness of `TR`
  have helemF : ∀ {m : ℕ} (ψ : WilkiesDesign.CG.LRc.Formula (Fin m)) (a : Fin m → F),
      ψ.Realize (((↑) : F → K) ∘ a) ↔ ψ.Realize a :=
    fun ψ a => hMCr F K (FirstOrder.Language.Substructure.subtype F) ψ a
  have helemσ : ∀ {m : ℕ} (ψ : WilkiesDesign.CG.LRc.Formula (Fin m)) (a : Fin m → F),
      ψ.Realize (σ ∘ a) ↔ ψ.Realize a :=
    fun ψ a => hMCr F L σ ψ a
  -- the partial elementary map on the parameter set `F`
  set A : Set K := (F : Set K) with hAdef
  let σA : A → Set.univ := fun a => ⟨σ ⟨a.1, a.2⟩, Set.mem_univ _⟩
  have hσ : ∀ {m : ℕ} (ψ : WilkiesDesign.CG.LRc.Formula (Fin m)) (a : Fin m → A),
      (ψ.Realize (fun i => (a i : K)) ↔
        ψ.Realize (fun i => ((σA (a i) : Set.univ) : L))) := by
    intro m ψ a
    have h1 : ψ.Realize (fun i => (a i : K)) ↔
        ψ.Realize (fun i => ((⟨(a i : K), (a i).2⟩ : F))) := by
      have h := helemF ψ (fun i => (⟨(a i : K), (a i).2⟩ : F))
      rw [show ((↑) : F → K) ∘ (fun i => (⟨(a i : K), (a i).2⟩ : F)) =
          (fun i => (a i : K)) from by funext i; rfl] at h
      exact h
    have h2 : ψ.Realize (fun i => ((⟨(a i : K), (a i).2⟩ : F))) ↔
        ψ.Realize (fun i => ((σ ⟨(a i : K), (a i).2⟩ : L))) :=
      (helemσ ψ (fun i => (⟨(a i : K), (a i).2⟩ : F))).symm
    refine h1.trans (h2.trans (iff_of_eq (congrArg (fun w => ψ.Realize w) ?_)))
    funext i
    rfl
  have hcutA : (∀ a : A, ((a : K) < x ↔ (σA a : Set.univ) < y)) ∧
      (∀ a : A, (x < (a : K) ↔ y < (σA a : Set.univ))) := by
    constructor
    · intro a; exact hcut.1 ⟨a.1, a.2⟩
    · intro a; exact hcut.2 ⟨a.1, a.2⟩
  -- the two-model cut theorem
  have key := Work.WilC5.cut_determines_type_gen (K := K) (L := L) hOM
    (A := (F : Set K)) hFdcl (B := Set.univ) (fun _ _ => Set.mem_univ _)
    σA hσ (x := x) (y := y) hcutA (n := n) φ v
  -- the two index types `F` and `↥(F : Set K)` are definitionally equal
  refine key.trans (iff_of_eq (congrArg (fun w => φ.Realize w) ?_))
  funext z
  rcases z with a | j <;> rfl

theorem dmm42_cut_extend (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∃ σ' : WilkiesDesign.CG.LRc.Embedding
        (FirstOrder.Language.Substructure.closure WilkiesDesign.CG.LRc ((F : Set K) ∪ {x})) L,
      (σ' ⟨x, FirstOrder.Language.Substructure.subset_closure (Or.inr (Set.mem_singleton x))⟩ = y) ∧
      (∀ f : F, σ' ⟨(f : K), FirstOrder.Language.Substructure.subset_closure (Or.inl f.2)⟩ = σ f) :=
  Work.WilC5.ExistsEmbeddingClosurePoint (L := WilkiesDesign.CG.LRc) (M := K) (N := L)
    F σ x y (cut_determines_type_F hMCr hOM F hF hFdcl σ hcut)

end Work.WilC5
