import Mathlib
import Submission.Work.ANALYTIC.CechPt.codegeneracy_homology_isZero

/-!
# Acyclicity of the type-level Čech complex in positive degrees

For **any** map of types `f : A ⟶ B`, the Čech nerve `X_•` of `f` carries a "quasi-section":
a choice, for every point `b` of `B` lying in the range of `f`, of a point of `A` mapping to `b`.
Prepending the quasi-section of the base point gives maps

`u_q : X_q ⟶ X_{q+1}`, `(a_0, …, a_q) ↦ (λ b, a_0, …, a_q)`

where `b` is the common image in `B` of the `a_i`, and these satisfy the extra-degeneracy
identities `d_0 ∘ u_q = id` and `d_{i+1} ∘ u_q = u_{q-1} ∘ d_i`.  Hence the free simplicial
`ℤ`-module `ℤ[X_•]` carries a contracting homotopy away from degree `0` (see
`Work.ANALYTIC.CechPt.codegeneracy_homology_isZero`), and its alternating face map complex is
acyclic in positive degrees: `Work.ANALYTIC.CechPt.cech_acyclic_type`.

The point is that `λ` is only a *partial* section of `f` — there is no global section of an
arbitrary map of types — but it need only be defined on the range of `f`, and it only enters
through the base point of the nerve, so the identities are exactly the extra-degeneracy ones.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits AlgebraicTopology
open scoped CategoryTheory Simplicial

noncomputable section

variable {A B : Type}

/-- The Čech nerve of `f`, written so that it unfolds during unification. -/
@[implicit_reducible]
noncomputable def typeNerve (f : A ⟶ B) : SimplicialObject (Type) :=
  Arrow.cechNerve (Arrow.mk f)

/-- A choice, for every point of `B` lying in the range of `f`, of a preimage in `A`. -/
noncomputable def secR (f : A ⟶ B) (z : Set.range (f : A → B)) : A :=
  Classical.choose z.2

theorem secR_spec (f : A ⟶ B) (z : Set.range (f : A → B)) :
    (f : A → B) (secR f z) = z.1 :=
  Classical.choose_spec z.2

/-- Every base point of the Čech nerve of `f` lies in the range of `f`. -/
theorem nbase_mem_range (f : A ⟶ B) (q : ℕ)
    (y : (typeNerve f).obj (Opposite.op ⦋q⦌)) :
    ∃ a : A, (f : A → B) a
      = (WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)) y :=
  ⟨(WidePullback.π (fun _ : Fin (q + 1) => (Arrow.mk f).hom) 0) y, by
    have h := congrArg
      (fun m : (typeNerve f).obj (Opposite.op ⦋q⦌) ⟶ B => (m : _ → B))
      (WidePullback.π_arrow (fun _ : Fin (q + 1) => (Arrow.mk f).hom) (0 : Fin (q + 1)))
    exact congrFun h y⟩

/-- The "prepending" morphism: the chosen point of the fibre of the base point. -/
noncomputable def pre (f : A ⟶ B) (q : ℕ) :
    (typeNerve f).obj (Opposite.op ⦋q⦌) ⟶ A :=
  ↾(fun y : (typeNerve f).obj (Opposite.op ⦋q⦌) =>
    secR f ⟨(WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)) y,
      nbase_mem_range f q y⟩)

theorem pre_apply (f : A ⟶ B) (q : ℕ)
    (y : (typeNerve f).obj (Opposite.op ⦋q⦌)) :
    (pre f q) y = secR f ⟨(WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)) y,
      nbase_mem_range f q y⟩ := rfl

/-- `pre` only depends on the base point. -/
theorem pre_eq_of_base_eq (f : A ⟶ B) {q q' : ℕ}
    {x : (typeNerve f).obj (Opposite.op ⦋q⦌)}
    {y : (typeNerve f).obj (Opposite.op ⦋q'⦌)}
    (h : (WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)) x
      = (WidePullback.base (fun _ : Fin (q' + 1) => (Arrow.mk f).hom)) y) :
    (pre f q) x = (pre f q') y :=
  congrArg (secR f) (Subtype.ext h)

/-- The chosen point of the fibre really maps to the base point. -/
theorem pre_comp (f : A ⟶ B) (q : ℕ) :
    pre f q ≫ (Arrow.mk f).hom
      = WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom) := by
  apply ConcreteCategory.hom_ext
  intro y
  simp only [CategoryTheory.types_comp]
  exact secR_spec f ⟨_, nbase_mem_range f q y⟩

/-- The face maps of the Čech nerve, on projections. -/
theorem nerve_δ_π (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2)) (j : Fin (q + 1)) :
    (typeNerve f).δ i ≫ WidePullback.π (fun _ : Fin (q + 1) => (Arrow.mk f).hom) j
      = WidePullback.π (fun _ : Fin (q + 2) => (Arrow.mk f).hom) (Fin.succAbove i j) := by
  dsimp only [typeNerve, SimplicialObject.δ_def, Arrow.cechNerve]
  erw [WidePullback.lift_π]
  rfl

/-- The face maps of the Čech nerve do not change the base point. -/
theorem nerve_δ_base (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2)) :
    (typeNerve f).δ i ≫ WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)
      = WidePullback.base (fun _ : Fin (q + 2) => (Arrow.mk f).hom) := by
  dsimp only [typeNerve, SimplicialObject.δ_def, Arrow.cechNerve]
  erw [WidePullback.lift_base]

/-- The previous lemma, evaluated at a point. -/
theorem nbase_δ_apply (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2))
    (x : (typeNerve f).obj (Opposite.op ⦋q + 1⦌)) :
    (WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom)) ((typeNerve f).δ i x)
      = (WidePullback.base (fun _ : Fin (q + 2) => (Arrow.mk f).hom)) x := by
  have h := congrArg
    (fun m : (typeNerve f).obj (Opposite.op ⦋q + 1⦌) ⟶ B => (m : _ → B))
    (nerve_δ_base f q i)
  simpa using congrFun h x

/-- Inserting the gap at `i.succ` leaves the index `0` fixed. -/
theorem succAbove_succ_zero {q : ℕ} (i : Fin (q + 2)) :
    Fin.succAbove i.succ (0 : Fin (q + 2)) = 0 := by
  simp [Fin.succAbove]

/-- Inserting the gap at `i.succ` commutes with shifting by one. -/
theorem succAbove_succ_succ {q : ℕ} (i : Fin (q + 2)) (j : Fin (q + 1)) :
    Fin.succAbove i.succ j.succ = (Fin.succAbove i j).succ := by
  simp [Fin.succAbove]
  split_ifs <;> simp

/-- `pre` is compatible with the face maps. -/
theorem pre_comp_δ (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2)) :
    pre f (q + 1) = (typeNerve f).δ i ≫ pre f q := by
  apply ConcreteCategory.hom_ext
  intro x
  show (pre f (q + 1)) x = (pre f q) ((typeNerve f).δ i x)
  exact pre_eq_of_base_eq f (nbase_δ_apply f q i x).symm

/-- The contracting homotopy of the Čech nerve: `(a_0, …, a_q) ↦ (λ b, a_0, …, a_q)`. -/
noncomputable def u (f : A ⟶ B) (q : ℕ) :
    (typeNerve f).obj (Opposite.op ⦋q⦌) ⟶ (typeNerve f).obj (Opposite.op ⦋q + 1⦌) :=
  WidePullback.lift (WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom))
    (Fin.cases (pre f q)
      (fun j => WidePullback.π (fun _ : Fin (q + 1) => (Arrow.mk f).hom) j))
    (by
      intro i
      cases i using Fin.cases with
      | zero => rw [Fin.cases_zero, pre_comp]
      | succ j => rw [Fin.cases_succ, WidePullback.π_arrow])

/-- The `0`-th coordinate of `u f q`. -/
theorem u_π_zero (f : A ⟶ B) (q : ℕ) :
    u f q ≫ WidePullback.π (fun _ : Fin (q + 2) => (Arrow.mk f).hom) 0 = pre f q := by
  dsimp only [u]
  erw [WidePullback.lift_π]
  simp only [Fin.cases_zero]

/-- The other coordinates of `u f q`: they are shifted. -/
theorem u_π_succ (f : A ⟶ B) (q : ℕ) (j : Fin (q + 1)) :
    u f q ≫ WidePullback.π (fun _ : Fin (q + 2) => (Arrow.mk f).hom) j.succ
      = WidePullback.π (fun _ : Fin (q + 1) => (Arrow.mk f).hom) j := by
  dsimp only [u]
  erw [WidePullback.lift_π]
  simp only [Fin.cases_succ]

/-- The map to the base of `u f q`. -/
theorem u_base (f : A ⟶ B) (q : ℕ) :
    u f q ≫ WidePullback.base (fun _ : Fin (q + 2) => (Arrow.mk f).hom)
      = WidePullback.base (fun _ : Fin (q + 1) => (Arrow.mk f).hom) := by
  dsimp only [u]
  exact WidePullback.lift_base ..

/-- **First contraction identity**: the `0`-th face of `u f q` is the identity. -/
theorem u_comp_δ_zero (f : A ⟶ B) (q : ℕ) :
    u f q ≫ (typeNerve f).δ (0 : Fin (q + 2)) = 𝟙 _ := by
  apply WidePullback.hom_ext (fun _ : Fin (q + 1) => (Arrow.mk f).hom)
  · intro j
    rw [Category.assoc, nerve_δ_π, Fin.succAbove_zero, u_π_succ, Category.id_comp]
  · rw [Category.assoc, nerve_δ_base, u_base, Category.id_comp]

/-- **Second contraction identity**: `d_{i+1} ∘ u_q = u_{q-1} ∘ d_i`. -/
theorem u_comp_δ_succ (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2)) :
    u f (q + 1) ≫ (typeNerve f).δ i.succ = (typeNerve f).δ i ≫ u f q := by
  apply WidePullback.hom_ext (fun _ : Fin (q + 2) => (Arrow.mk f).hom)
  · intro j
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h
      simp only [Category.assoc]
      rw [nerve_δ_π, succAbove_succ_zero, u_π_zero, u_π_zero, pre_comp_δ]
    · simp only [Category.assoc]
      rw [nerve_δ_π, succAbove_succ_succ, u_π_succ, u_π_succ, nerve_δ_π]
  · simp only [Category.assoc]
    rw [nerve_δ_base, u_base, u_base, nerve_δ_base]

/-- The face maps of the free Čech complex are the free maps of the face maps of the nerve. -/
theorem cechNerveFree_δ (f : A ⟶ B) (q : ℕ) (i : Fin (q + 2)) :
    SimplicialObject.δ (Arrow.cechNerve (Arrow.mk f) ⋙ ModuleCat.free ℤ) i
      = (ModuleCat.free ℤ).map ((typeNerve f).δ i) := rfl

theorem cech_acyclic_type {A B : Type} (f : A ⟶ B) (n : ℕ) :
    CategoryTheory.Limits.IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (CategoryTheory.Functor.comp (CategoryTheory.Arrow.cechNerve (CategoryTheory.Arrow.mk f))
        (ModuleCat.free ℤ))).homology (n + 1)) := by
  refine codegeneracy_homology_isZero
    (Arrow.cechNerve (Arrow.mk f) ⋙ ModuleCat.free ℤ)
    (fun q => (ModuleCat.free ℤ).map (u f q)) ?_ ?_ n
  · intro q
    show (ModuleCat.free ℤ).map (u f q)
        ≫ (ModuleCat.free ℤ).map ((typeNerve f).δ (0 : Fin (q + 2)))
      = 𝟙 ((ModuleCat.free ℤ).obj ((typeNerve f).obj (Opposite.op ⦋q⦌)))
    rw [← Functor.map_comp, u_comp_δ_zero]
    exact (ModuleCat.free ℤ).map_id _
  · intro q i
    show (ModuleCat.free ℤ).map (u f (q + 1))
        ≫ (ModuleCat.free ℤ).map ((typeNerve f).δ i.succ)
      = (ModuleCat.free ℤ).map ((typeNerve f).δ i) ≫ (ModuleCat.free ℤ).map (u f q)
    rw [← Functor.map_comp, ← Functor.map_comp, u_comp_δ_succ]

end

end Work.ANALYTIC.CechPt
