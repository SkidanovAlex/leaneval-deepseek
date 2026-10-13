import Mathlib
import Submission.Work.WilC4.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

section Helpers

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- The definable closure of a single parameter set `T`, i.e. `Dcl T ∅`. -/
private def Cl (T : Set M) : Set M := {x | T.Definable LRc {fun _ : Fin 1 => x}}

private lemma mem_Cl {T : Set M} {x : M} :
    x ∈ Cl T ↔ T.Definable LRc {fun _ : Fin 1 => x} :=
  Iff.rfl

private lemma dcl_eq_Cl (S A : Set M) : Dcl S A = Cl (S ∪ A) := rfl

private lemma cl_mono {T T' : Set M} (h : T ⊆ T') : Cl T ⊆ Cl T' :=
  fun _ hx => Set.Definable.mono hx h

/-- The singleton consisting of the constant function with value `x` is the set of tuples whose
zeroth coordinate is `x`. -/
private lemma unit_const_set (x : M) :
    ({fun _ : Fin 1 => x} : Set (Fin 1 → M)) = {v : Fin 1 → M | v 0 = x} := by
  ext v
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    rfl
  · intro h
    funext i
    show v i = x
    rw [show i = 0 from Subsingleton.elim i 0]
    exact h

private lemma subset_cl (T : Set M) : T ⊆ Cl T := by
  intro x hx
  rw [mem_Cl, unit_const_set x]
  simpa only [Set.Definable₁, Set.mem_singleton_iff] using
    (Set.Definable.singleton_of_mem (L := LRc) (A := T) hx)

/-- **Elimination of one definable parameter.**  If `a` is definable over `A` and a set `s` is
definable over `A ∪ {a}`, then `s` is definable over `A`. -/
private theorem dcl_elim_one_aux
    (A : Set M) (a : M) (ha : A.Definable LRc {w : Fin 1 → M | w 0 = a})
    {ι : Type*} (s : Set (ι → M)) (hs : (A ∪ {a}).Definable LRc s) :
    A.Definable LRc s := by
  classical
  rw [Set.definable_iff_exists_formula_sum] at ha hs ⊢
  obtain ⟨φ, hφ⟩ := hs
  obtain ⟨ψ, hψ⟩ := ha
  rw [hφ]
  have hψ' : ∀ w : Fin 1 → M, ψ.Realize (Sum.elim ((↑) : ↥A → M) w) ↔ w 0 = a := by
    intro w
    simpa using (Set.ext_iff.mp hψ w).symm
  let tz : LRc.Term ((A ⊕ ι) ⊕ Fin 1) := Term.var (Sum.inr 0)
  let σ : (↥(A ∪ ({a} : Set M)) ⊕ ι) → LRc.Term ((A ⊕ ι) ⊕ Fin 1) :=
    Sum.elim
      (fun p : ↥(A ∪ ({a} : Set M)) =>
        if h : (p : M) = a then tz
        else Term.var (Sum.inl (Sum.inl ⟨(p : M), by
          have hp := p.2
          simp only [Set.mem_union, Set.mem_singleton_iff] at hp
          exact hp.resolve_right h⟩)))
      (fun i => Term.var (Sum.inl (Sum.inr i)))
  let g : (↥A ⊕ Fin 1) → ((A ⊕ ι) ⊕ Fin 1) := Sum.map (Sum.inl : ↥A → ↥A ⊕ ι) id
  refine ⟨Formula.iExs (Fin 1) ((φ.subst σ) ⊓ (ψ.relabel g)), ?_⟩
  ext v
  simp only [Set.mem_setOf_eq]
  have hsubst : ∀ W : ((A ⊕ ι) ⊕ Fin 1) → M,
      Formula.Realize (φ.subst σ) W ↔ Formula.Realize φ (fun c => (σ c).realize W) := by
    intro W
    simp only [Formula.Realize, BoundedFormula.realize_subst]
  have hrel : ∀ W : ((A ⊕ ι) ⊕ Fin 1) → M,
      Formula.Realize (ψ.relabel g) W ↔ Formula.Realize ψ (W ∘ g) := by
    intro W
    rw [Formula.realize_relabel]
  have hcomp : ∀ (v : ι → M) (z : Fin 1 → M),
      (Sum.elim (Sum.elim ((↑) : ↥A → M) v) z) ∘ g = Sum.elim ((↑) : ↥A → M) z := by
    intro v z
    funext c
    rcases c with y | j <;> rfl
  have hassign : ∀ (v : ι → M) (z : Fin 1 → M), z 0 = a →
      (fun c : ↥(A ∪ ({a} : Set M)) ⊕ ι =>
        (σ c).realize (Sum.elim (Sum.elim ((↑) : ↥A → M) v) z))
        = Sum.elim ((↑) : ↥(A ∪ ({a} : Set M)) → M) v := by
    intro v z hz
    funext c
    rcases c with p | i
    · show (σ (Sum.inl p)).realize (Sum.elim (Sum.elim ((↑) : ↥A → M) v) z) = ↑p
      dsimp only [σ]
      rw [Sum.elim_inl]
      split_ifs with h
      · dsimp only [tz]
        rw [Term.realize_var, Sum.elim_inr, hz]
        exact h.symm
      · rw [Term.realize_var, Sum.elim_inl]
        rfl
    · show (σ (Sum.inr i)).realize (Sum.elim (Sum.elim ((↑) : ↥A → M) v) z) = v i
      dsimp only [σ]
      rw [Sum.elim_inr, Term.realize_var, Sum.elim_inl]
      rfl
  simp only [Formula.realize_iExs, Formula.realize_inf]
  constructor
  · intro hv
    refine ⟨fun _ => a, ?_, ?_⟩
    · rw [hsubst, hassign v (fun _ => a) rfl]
      exact hv
    · rw [hrel, hcomp v (fun _ => a), hψ']
  · rintro ⟨z, hz1, hz2⟩
    rw [hsubst] at hz1
    rw [hrel, hcomp v z, hψ'] at hz2
    rw [hassign v z hz2] at hz1
    exact hz1

private lemma cl_elim_one (A : Set M) (a : M) (ha : a ∈ Cl A) : Cl (A ∪ {a}) ⊆ Cl A := by
  intro x hx
  rw [mem_Cl] at hx ⊢
  have ha' : A.Definable LRc {w : Fin 1 → M | w 0 = a} := by
    rw [mem_Cl, unit_const_set a] at ha
    exact ha
  exact dcl_elim_one_aux A a ha' _ hx

private lemma cl_absorb_finset (T : Set M) (F : Finset M) (hF : ∀ y ∈ F, y ∈ Cl T) :
    Cl (T ∪ (F : Set M)) ⊆ Cl T := by
  induction F using Finset.induction with
  | empty =>
      simp only [Finset.coe_empty, Set.union_empty]
      intro x hx
      exact hx
  | insert y F' hy ih =>
      rw [Finset.coe_insert]
      have hy' : y ∈ Cl T := hF y (Finset.mem_insert_self y F')
      have hF' : ∀ z ∈ F', z ∈ Cl T := fun z hz => hF z (Finset.mem_insert_of_mem hz)
      have ih' : Cl (T ∪ (F' : Set M)) ⊆ Cl T := ih hF'
      have hset : T ∪ insert y ((F' : Finset M) : Set M) = (T ∪ (F' : Set M)) ∪ {y} := by
        ext z
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      intro x hx
      exact ih' (cl_elim_one (T ∪ (F' : Set M)) y
        (cl_mono Set.subset_union_left hy') hx)

private lemma cl_absorb (T P : Set M) (hP : ∀ y ∈ P, y ∈ Cl T) : Cl (T ∪ P) ⊆ Cl T := by
  intro x hx
  rw [mem_Cl, Set.definable_iff_finitely_definable] at hx
  obtain ⟨F, hF, hFd⟩ := hx
  have hFT : ∀ y ∈ F, y ∈ Cl T := by
    intro y hy
    have hy' : y ∈ T ∪ P := hF (by simpa using hy)
    rcases hy' with h | h
    · exact subset_cl T h
    · exact hP y h
  have hx' : x ∈ Cl (T ∪ (F : Set M)) := by
    rw [mem_Cl]
    exact Set.Definable.mono hFd Set.subset_union_right
  exact cl_absorb_finset T F hFT hx'

private lemma cl_idem (T : Set M) : Cl (Cl T) = Cl T := by
  refine Set.Subset.antisymm ?_ (cl_mono (subset_cl T))
  have hsub : T ∪ Cl T = Cl T := by
    ext z
    exact ⟨fun h => h.elim (fun hz => subset_cl T hz) id, fun h => Or.inr h⟩
  have h1 : Cl (Cl T) = Cl (T ∪ Cl T) := by rw [hsub]
  rw [h1]
  exact cl_absorb T (Cl T) (fun y hy => hy)

private lemma cl_absorb_union (T B : Set M) : Cl (Cl T ∪ B) = Cl (T ∪ B) := by
  refine Set.Subset.antisymm ?_ ?_
  · have hsub : Cl T ∪ B ⊆ Cl (T ∪ B) := by
      intro z hz
      rcases hz with hz | hz
      · exact cl_mono Set.subset_union_left hz
      · exact subset_cl (T ∪ B) (Set.subset_union_right hz)
    calc Cl (Cl T ∪ B) ⊆ Cl (Cl (T ∪ B)) := cl_mono hsub
      _ = Cl (T ∪ B) := cl_idem (T ∪ B)
  · apply cl_mono
    intro z hz
    rcases hz with h | h
    · exact Or.inl (subset_cl T h)
    · exact Or.inr h

end Helpers

theorem dcl_idem {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (S A B : Set M) : Dcl (Dcl S A) B = Dcl S (A ∪ B) := by
  have hL : Dcl (Dcl S A) B = Cl (Cl (S ∪ A) ∪ B) := by
    rw [dcl_eq_Cl (Dcl S A) B, dcl_eq_Cl S A]
  have hR : Dcl S (A ∪ B) = Cl ((S ∪ A) ∪ B) := by
    rw [dcl_eq_Cl S (A ∪ B), Set.union_assoc]
  rw [hL, hR]
  exact cl_absorb_union (S ∪ A) B

end Work.WilC4
