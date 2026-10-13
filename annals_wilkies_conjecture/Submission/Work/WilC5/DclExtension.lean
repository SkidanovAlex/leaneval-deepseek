import Mathlib
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC5.DclMapAux
import Submission.Work.WilC5.ElemOnOfSurjRelabel

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

instance lrcRelationsIsEmpty (n : ℕ) : IsEmpty (WilkiesDesign.CG.LRc.Relations n) :=
  ⟨fun r => by rcases r with (r | r) | r <;> exact r.elim⟩

theorem DclExtension {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∃ (S : WilkiesDesign.CG.LRc.Substructure K)
      (hS : (S : Set K) = Work.WilC2.Dcl ((F : Set K) ∪ {x}))
      (hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K))
      (hle : F ≤ S) (hxS : x ∈ (S : Set K)),
      ∃ σ' : WilkiesDesign.CG.LRc.Embedding S L,
        (∀ f : F, σ' ⟨(f : K), hle f.2⟩ = σ f) ∧ σ' ⟨x, hxS⟩ = y := by
  classical
  let γ : Type := ↥((F : Set K) ∪ {x})
  let iP : γ → K := Subtype.val
  let jP : γ → L := fun a => if h : (a : K) ∈ (F : Set K) then σ ⟨a.1, h⟩ else y
  let iA : (↥F ⊕ Fin 1) → K := Sum.elim (fun f : ↥F => (f : K)) (fun _ => x)
  let jA : (↥F ⊕ Fin 1) → L := Sum.elim (fun f : ↥F => (σ f : L)) (fun _ => y)
  have hy_eq : ∀ (hxF : x ∈ (F : Set K)), y = σ ⟨x, hxF⟩ := by
    intro hxF
    have h1 : ¬ ((σ ⟨x, hxF⟩ : L) < y) := fun hlt =>
      absurd ((hcut.1 ⟨x, hxF⟩).mpr hlt) (lt_irrefl x)
    have h2 : ¬ (y < (σ ⟨x, hxF⟩ : L)) := fun hlt =>
      absurd ((hcut.2 ⟨x, hxF⟩).mpr hlt) (lt_irrefl x)
    exact (le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)).symm
  have H0 : ∀ φ : WilkiesDesign.CG.LRc.Formula (↥F ⊕ Fin 1),
      φ.Realize iA ↔ φ.Realize jA := by
    intro φ
    have h := cut_determines_type_F hMCr hOM F hF hFdcl σ hcut (n := 0) φ
      (fun i : Fin 0 => i.elim0)
    have e1 : (Sum.elim (Subtype.val : ↥F → K)
        (Fin.cons x (fun i : Fin 0 => (((i.elim0 : ↥F)) : K)))) = iA := by
      funext z; rcases z with f | j
      · rfl
      · fin_cases j; simp [iA]
    have e2 : (Sum.elim (fun f : ↥F => (σ f : L))
        (Fin.cons y (fun i : Fin 0 => ((σ (i.elim0 : ↥F)) : L)))) = jA := by
      funext z; rcases z with f | j
      · rfl
      · fin_cases j; simp [jA]
    rw [e1, e2] at h
    exact h
  let sfun : (↥F ⊕ Fin 1) → γ :=
    Sum.elim (fun f : ↥F => (⟨(f : K), Or.inl f.2⟩ : γ))
      (fun _ => (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ))
  have hsurj : Function.Surjective sfun := by
    rintro ⟨a, ha⟩
    rcases ha with ha | ha
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [sfun]⟩
    · rw [Set.mem_singleton_iff] at ha
      exact ⟨Sum.inr 0, by simp [sfun, ha]⟩
  have hj_inl : ∀ f : ↥F, jP (⟨(f : K), Or.inl f.2⟩ : γ) = σ f := by
    intro f
    show (if h : (f : K) ∈ (F : Set K) then σ ⟨(f : K), h⟩ else y) = σ f
    have hf : (f : K) ∈ (F : Set K) := f.2
    rw [dif_pos hf]
  have hj_inr : jP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ) = y := by
    by_cases hxF : x ∈ (F : Set K)
    · show (if h : x ∈ (F : Set K) then σ ⟨x, h⟩ else y) = y
      rw [dif_pos hxF]
      exact (hy_eq hxF).symm
    · show (if h : x ∈ (F : Set K) then σ ⟨x, h⟩ else y) = y
      rw [dif_neg hxF]
  have hi : iP ∘ sfun = iA := by
    funext z; rcases z with f | j
    · rfl
    · fin_cases j; rfl
  have hj : jP ∘ sfun = jA := by
    funext z; rcases z with f | j
    · exact hj_inl f
    · fin_cases j; exact hj_inr
  have H : ∀ φ : WilkiesDesign.CG.LRc.Formula γ, φ.Realize iP ↔ φ.Realize jP :=
    ElemOnOfSurjRelabel (L := WilkiesDesign.CG.LRc) iA jA iP jP sfun hsurj hi hj H0
  obtain ⟨hclosed, w, hwinj, hwext, hwfun⟩ :=
    DclMapAux (L := WilkiesDesign.CG.LRc) (M := K) (N := L) iP jP H
  have hmem_iP : ∀ a : γ, iP a ∈ DefDom (L := WilkiesDesign.CG.LRc) iP := by
    intro a
    refine ⟨(Term.var (Sum.inr 0)).equal (Term.var (Sum.inl a)), ?_⟩
    intro v
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    simp [Sum.elim_inr, Sum.elim_inl]
  let S : WilkiesDesign.CG.LRc.Substructure K := ⟨DefDom (L := WilkiesDesign.CG.LRc) iP, hclosed⟩
  let w' : ↥S → L := fun z => w ⟨z.1, z.2⟩
  have hSdef : (S : Set K) = DefDom (L := WilkiesDesign.CG.LRc) iP := rfl
  have hS : (S : Set K) = Work.WilC2.Dcl ((F : Set K) ∪ {x}) := by
    rw [hSdef]
    ext ss
    rw [Work.WilC2.mem_dcl, Set.Definable₁, Set.definable_iff_exists_formula_sum]
    have key : ∀ φ : WilkiesDesign.CG.LRc.Formula (γ ⊕ Fin 1),
        ((∀ v : Fin 1 → K, v 0 = ss ↔ φ.Realize (Sum.elim iP v)) ↔
          ({v : Fin 1 → K | v 0 = ss} =
            {v : Fin 1 → K | φ.Realize (Sum.elim (Subtype.val : γ → K) v)})) := by
      intro φ
      rw [Set.ext_iff]
      exact Iff.rfl
    simp only [DefDom, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ, (key φ).mp hφ⟩
    · rintro ⟨φ, hφ⟩
      exact ⟨φ, (key φ).mpr hφ⟩
  have hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K) := by
    rw [hS, Work.WilC2.dcl_idem]
  have hle : F ≤ S := by
    intro f hf
    have h := hmem_iP (⟨f, Or.inl hf⟩ : γ)
    have hif : iP (⟨f, Or.inl hf⟩ : γ) = f := rfl
    rw [hif] at h
    exact h
  have hxS : x ∈ (S : Set K) := by
    have h := hmem_iP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ)
    have hif : iP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ) = x := rfl
    rw [hif] at h
    exact h
  have hmap : ∀ {n : ℕ} (f : WilkiesDesign.CG.LRc.Functions n) (xd : Fin n → S),
      w' (Structure.funMap f xd) = Structure.funMap f (w' ∘ xd) := by
    intro n f xd
    exact hwfun f (fun k => (xd k : K)) (fun k => (xd k).2)
  have hwinj' : Function.Injective w' := by
    intro a b hab
    have h : (⟨a.1, a.2⟩ : ↥(DefDom (L := WilkiesDesign.CG.LRc) iP)) = ⟨b.1, b.2⟩ :=
      hwinj hab
    exact Subtype.ext (Subtype.ext_iff.mp h)
  let σ' : WilkiesDesign.CG.LRc.Embedding S L :=
    FirstOrder.Language.Embedding.mk ⟨w', hwinj'⟩
      (fun {n} f xd => hmap f xd) (fun {n} r xd => isEmptyElim r)
  refine ⟨S, hS, hSdcl, hle, hxS, σ', ?_, ?_⟩
  · intro f
    have hb := hmem_iP (⟨(f : K), Or.inl f.2⟩ : γ)
    have key : w (⟨iP (⟨(f : K), Or.inl f.2⟩ : γ), hb⟩ :
        ↥(DefDom (L := WilkiesDesign.CG.LRc) iP)) = σ f := by
      have h := hwext (⟨(f : K), Or.inl f.2⟩ : γ) hb
      rwa [hj_inl f] at h
    have harg : (⟨iP (⟨(f : K), Or.inl f.2⟩ : γ), hb⟩ :
          ↥(DefDom (L := WilkiesDesign.CG.LRc) iP)) =
        (⟨(f : K), hle f.2⟩ : ↥S) := Subtype.ext rfl
    change w' (⟨(f : K), hle f.2⟩ : ↥S) = σ f
    rw [← harg]
    exact key
  · have hb := hmem_iP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ)
    have key : w (⟨iP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ), hb⟩ :
        ↥(DefDom (L := WilkiesDesign.CG.LRc) iP)) = y := by
      have h := hwext (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ) hb
      rwa [hj_inr] at h
    have harg : (⟨iP (⟨x, Or.inr (Set.mem_singleton x)⟩ : γ), hb⟩ :
          ↥(DefDom (L := WilkiesDesign.CG.LRc) iP)) = (⟨x, hxS⟩ : ↥S) := Subtype.ext rfl
    change w' (⟨x, hxS⟩ : ↥S) = y
    rw [← harg]
    exact key

end Work.WilC5
