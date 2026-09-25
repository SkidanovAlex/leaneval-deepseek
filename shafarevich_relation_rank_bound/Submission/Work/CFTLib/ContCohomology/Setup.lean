import Mathlib

/-!
# Continuous cohomology via functions on the powers of the group

Mathlib's `continuousCohomology n X` (for `X : TopRep k G`) is the homology of the complex of
invariants of the `coind₁`-resolution `X → C(G, X) → C(G, C(G, X)) → ⋯`.

This file develops the elementary bridge between that complex and the *classical* description of
continuous cohomology as the cohomology of the complex of *invariant continuous functions*
`G^{n+1} → X`.

## Main definitions

* `Work.CFTLib.ContCohomology.evalIter` — the iterated evaluation
  `Φ ↦ (x₀, …, xₙ) ↦ Φ x₀ x₁ ⋯ xₙ` of an element of the `n`-th term `coind₁ⁿ X` of the
  resolution.
* `Work.CFTLib.ContCohomology.homCochain X n` — the module of continuous functions
  `(Fin (n+1) → G) → X` invariant under the diagonal action.
* `Work.CFTLib.ContCohomology.homDiff X n` — the (homogeneous) differential
  `f ↦ Σᵢ (-1)ⁱ f ∘ deleteᵢ`.
-/

noncomputable section

open TopRep

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ]

/-- Iterated evaluation of an element of the `n`-th term of the `coind₁`-resolution of a
topological representation `X` of `Γ`: the function `(x₀, …, xₙ₋₁) ↦ Φ x₀ ⋯ xₙ₋₁`. -/
def evalIter (X : TopRep k Γ) : (n : ℕ) → ↥(TopRep.resolutionX X n) → (Fin n → Γ) → ↥X
  | 0, m, _ => m
  | n+1, F, x => evalIter X n (F (x 0)) (Fin.tail x)

@[simp] lemma evalIter_zero (X : TopRep k Γ) (m : ↥X) (x : Fin 0 → Γ) :
    evalIter X 0 m x = m := rfl

@[simp] lemma evalIter_succ (X : TopRep k Γ) (n : ℕ) (F : ↥(TopRep.resolutionX X (n+1)))
    (x : Fin (n+1) → Γ) :
    evalIter X (n+1) F x = evalIter X n (F (x 0)) (Fin.tail x) := rfl

lemma evalIter_add (X : TopRep k Γ) (n : ℕ) (a b : ↥(TopRep.resolutionX X n))
    (x : Fin n → Γ) :
    evalIter X n (a + b) x = evalIter X n a x + evalIter X n b x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [evalIter_succ, ContinuousMap.add_apply, ih]

lemma evalIter_neg (X : TopRep k Γ) (n : ℕ) (a : ↥(TopRep.resolutionX X n)) (x : Fin n → Γ) :
    evalIter X n (-a) x = -evalIter X n a x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [evalIter_succ, ContinuousMap.neg_apply, ih]

lemma evalIter_sub (X : TopRep k Γ) (n : ℕ) (a b : ↥(TopRep.resolutionX X n))
    (x : Fin n → Γ) :
    evalIter X n (a - b) x = evalIter X n a x - evalIter X n b x := by
  rw [sub_eq_add_neg, evalIter_add, evalIter_neg, sub_eq_add_neg]

lemma evalIter_smul (X : TopRep k Γ) (n : ℕ) (r : k) (a : ↥(TopRep.resolutionX X n))
    (x : Fin n → Γ) :
    evalIter X n (r • a) x = r • evalIter X n a x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [evalIter_succ, ContinuousMap.smul_apply, ih]

lemma evalIter_cons (X : TopRep k Γ) (n : ℕ) (v : ↥(TopRep.resolutionX X (n+1))) (g : Γ)
    (y : Fin n → Γ) :
    evalIter X (n+1) v (Fin.cons g y) = evalIter X n (v g) y := by
  simp only [evalIter_succ, Fin.cons_zero, Fin.tail_cons]

lemma succAbove_succ {n : ℕ} (j : Fin (n+1)) (i : Fin n) :
    Fin.succAbove (Fin.succ j) (Fin.succ i) = Fin.succ (Fin.succAbove j i) := by
  ext; simp only [Fin.succAbove, Fin.val_succ]; split_ifs <;> simp_all

omit [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
lemma fin_cons_tail_succAbove {n : ℕ} {α : Type*} (x : Fin (n+2) → α) (j : Fin (n+1)) :
    Fin.cons (x 0) (Fin.tail x ∘ Fin.succAbove j) = x ∘ Fin.succAbove (Fin.succ j) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Fin.cons_zero, Fin.succAbove]
  | succ i =>
    show x (Fin.succAbove j i).succ = x (Fin.succAbove (Fin.succ j) i.succ)
    rw [succAbove_succ]

/-- **The differential of the `coind₁`-resolution is the simplicial differential.** For an element
`v` of the `n`-th term of the resolution, the evaluation of its image under the `n`-th differential
is the alternating sum of the evaluations `x ↦ Φ (x ∘ deleteᵢ)`. -/
theorem evalIter_d (X : TopRep k Γ) (n : ℕ) (v : ↥(TopRep.resolutionX X n))
    (x : Fin (n+1) → Γ) :
    evalIter X (n+1) ((TopRep.d X n).hom v) x
      = ∑ i : Fin (n+1), (-1 : k) ^ (i : ℕ) • evalIter X n v (x ∘ Fin.succAbove i) := by
  induction n with
  | zero =>
    rw [TopRep.d_zero, TopRep.hom_ofHom, ContRepresentation.coind₁ι_toFun]
    simp only [evalIter_zero, evalIter_succ, ContinuousMap.const_apply]
    rw [Fin.sum_univ_one]
    simp
  | succ n ih =>
    rw [TopRep.hom_d_succ, ContIntertwiningMap.sub_apply, ContRepresentation.coind₁Map_toFun,
      ContRepresentation.coind₁ι_toFun]
    rw [evalIter_succ]
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply]
    rw [evalIter_sub]
    change evalIter X (n+1) v (Fin.tail x)
        - evalIter X (n+1) ((Hom.hom (X.d n)) (v (x 0))) (Fin.tail x)
      = ∑ i : Fin (n+2), (-1 : k) ^ (i : ℕ) • evalIter X (n+1) v (x ∘ Fin.succAbove i)
    rw [show evalIter X (n+1) ((Hom.hom (X.d n)) (v (x 0))) (Fin.tail x)
        = ∑ i : Fin (n+1),
            (-1:k)^(i:ℕ) • evalIter X n (v (x 0)) ((Fin.tail x) ∘ Fin.succAbove i)
        from ih (v (x 0)) (Fin.tail x)]
    have hterm : ∀ i : Fin (n+1), evalIter X n (v (x 0)) ((Fin.tail x) ∘ Fin.succAbove i)
        = evalIter X (n+1) v (x ∘ Fin.succAbove (Fin.succ i)) := by
      intro i
      rw [← evalIter_cons X n v (x 0) ((Fin.tail x) ∘ Fin.succAbove i),
        fin_cons_tail_succAbove]
    have hfirst : evalIter X (n+1) v (Fin.tail x)
        = evalIter X (n+1) v (x ∘ Fin.succAbove (0 : Fin (n+2))) := by
      rw [Fin.succAbove_zero]; rfl
    rw [hfirst]
    conv_rhs => rw [Fin.sum_univ_succ]
    have hsum : (∑ i : Fin (n+1),
          (-1:k)^(i:ℕ) • evalIter X n (v (x 0)) ((Fin.tail x) ∘ Fin.succAbove i))
        = - ∑ i : Fin (n+1),
            (-1:k)^((Fin.succ i : Fin (n+2)):ℕ) •
              evalIter X (n+1) v (x ∘ Fin.succAbove (Fin.succ i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hterm i, Fin.val_succ, pow_succ]
      simp [neg_smul, mul_neg]
    rw [hsum]
    simp only [Fin.val_zero, pow_zero, one_smul]
    abel

/-- **The action of `Γ` commutes with `evalIter`.** -/
lemma evalIter_act (X : TopRep k Γ) (n : ℕ) (W : ↥(TopRep.resolutionX X n)) (g : Γ)
    (x : Fin n → Γ) :
    evalIter X n ((TopRep.resolutionX X n).ρ g W) x = X.ρ g (evalIter X n W (g⁻¹ • x)) := by
  induction n with
  | zero => rw [evalIter_zero, evalIter_zero]
  | succ n ih =>
    rw [evalIter_succ, evalIter_succ]
    have h1 : ((TopRep.resolutionX X (n+1)).ρ g W) (x 0)
        = (TopRep.resolutionX X n).ρ g (W (g⁻¹ * x 0)) := by
      rw [ContRepresentation.coind₁_apply_apply]
    rw [h1, ih]
    congr 2

/-- The module of **homogeneous `n`-cochains**: continuous functions on `Γ^{n+1}` invariant under
the diagonal action `(x₀, …, xₙ) ↦ (g x₀, …, g xₙ)`. -/
def homCochain (X : TopRep k Γ) (n : ℕ) : Submodule k ((Fin (n+1) → Γ) → ↥X) where
  carrier := {f | Continuous f ∧ ∀ (g : Γ) (x : Fin (n+1) → Γ),
    f (fun i => g * x i) = X.ρ g (f x)}
  zero_mem' := ⟨continuous_zero, by intro g x; simp⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨hf.1.add hh.1, fun g x => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, hf.2 g x, hh.2 g x, map_add]
  smul_mem' := by
    intro r f hf
    refine ⟨hf.1.const_smul r, fun g x => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, hf.2 g x, map_smul]

/-- The map `Fin (n+2) → Γ → Fin (n+1) → Γ`, `x ↦ x ∘ deleteᵢ`. -/
def deleteMap (n : ℕ) (i : Fin (n+2)) : C(Fin (n+2) → Γ, Fin (n+1) → Γ) :=
  ⟨fun x => x ∘ Fin.succAbove i, continuous_pi fun j => continuous_apply (Fin.succAbove i j)⟩

omit [Group Γ] [IsTopologicalGroup Γ] in
@[simp] lemma deleteMap_apply (n : ℕ) (i : Fin (n+2)) (x : Fin (n+2) → Γ) (j : Fin (n+1)) :
    deleteMap n i x j = x (Fin.succAbove i j) := rfl

variable (X : TopRep k Γ) in
/-- Precomposition with the `i`-th deletion `x ↦ x ∘ deleteᵢ`, as a linear map on homogeneous
cochains. -/
def compDelete (n : ℕ) (i : Fin (n+2)) :
    ↥(homCochain X n) →ₗ[k] ↥(homCochain X (n+1)) where
  toFun f := ⟨fun x => f.1 (deleteMap n i x), by
    refine ⟨f.2.1.comp (deleteMap n i).continuous, fun g x => ?_⟩
    change f.1 (deleteMap n i (fun i' => g * x i')) = X.ρ g (f.1 (deleteMap n i x))
    have hc : deleteMap n i (fun i' => g * x i') = g • (deleteMap n i x) := by
      funext j; rfl
    rw [hc]
    exact f.2.2 g (deleteMap n i x)⟩
  map_add' f h := by ext x; rfl
  map_smul' r f := by ext x; rfl

variable (X : TopRep k Γ) in
/-- The **homogeneous differential** `δ : C^n → C^{n+1}`, `(δf)(x) = Σᵢ (-1)ⁱ f (x ∘ deleteᵢ)`. -/
noncomputable def homDiff (n : ℕ) : ↥(homCochain X n) →ₗ[k] ↥(homCochain X (n+1)) :=
  Finset.sum Finset.univ fun i : Fin (n+2) => ((-1 : k) ^ (i : ℕ)) • (compDelete X n i)

variable (X : TopRep k Γ) in
@[simp] lemma homDiff_apply (n : ℕ) (f : ↥(homCochain X n)) (x : Fin (n+2) → Γ) :
    (homDiff X n f).1 x
      = ∑ i : Fin (n+2), (-1 : k) ^ (i : ℕ) • f.1 (deleteMap n i x) := by
  simp [homDiff, compDelete]

end Work.CFTLib.ContCohomology
