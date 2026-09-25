import Mathlib
import Submission.Work.CFTLib.ContCohomology.Setup

/-!
# Surjectivity of the iterated evaluation of the `coind₁`-resolution

The `n`-th continuous cohomology of a topological representation `X` of `Γ` is the homology of
the complex of invariants of the `coind₁`-resolution
`X → C(Γ, X) → C(Γ, C(Γ, X)) → ⋯`.  An element `Φ` of the `(n+1)`-st term of that resolution can
be *evaluated* on a tuple `(x₀, …, xₙ)` of group elements, giving the function

`evalIter X (n+1) Φ (x₀, …, xₙ) = Φ x₀ x₁ ⋯ xₙ`.

Unfolding the definition of `coind₁` shows that this identification is an isomorphism between the
`(n+1)`-st term of the resolution and the continuous functions on `Γⁿ⁺¹` (currying/uncurrying),
and that it identifies the *invariant* elements of the resolution term with the *invariant*
continuous functions — i.e. with `homCochain X n`.  This file proves the surjectivity of
`evalIter` on invariants, by constructing an explicit inverse `curryRes`, which is the iterated
currying of a continuous function on `Γⁿ⁺¹`.

## Main results

* `Work.CFTLib.ContCohomology.curryRes` — iterated currying
  `C(Γⁿ⁺¹, X) → ↥(coind₁ⁿ⁺¹ X)`, continuous in the function argument.
* `Work.CFTLib.ContCohomology.evalIter_curryRes` — `evalIter` is a left inverse of `curryRes`.
* `Work.CFTLib.ContCohomology.evalIter_ext` — `evalIter` is injective.
* `Work.CFTLib.ContCohomology.exists_evalIter_eq` — every invariant continuous function on
  `Γⁿ⁺¹` is the iterated evaluation of an invariant element of the `(n+1)`-st term.
-/

noncomputable section

set_option linter.unusedSectionVars false

open TopRep

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ]

/-- The continuous map `Γ × (Fin m → Γ) → (Fin (m+1) → Γ)`, `(t, y) ↦ (t, y₀, y₁, …)`: it inserts
a group element in front of a tuple.  This is the structural map along which the `coind₁`-resolution
unfolds a function of `n + 1` variables into a function of one variable with values in functions of
`n` variables. -/
def consCont (m : ℕ) : C(Γ × (Fin m → Γ), Fin (m+1) → Γ) where
  toFun p := Fin.cons (α := fun _ : Fin (m+1) => Γ) p.1 p.2
  continuous_toFun := continuous_pi fun i => by
    refine Fin.cases (motive := fun i => Continuous fun p : Γ × (Fin m → Γ) =>
      Fin.cons (α := fun _ : Fin (m+1) => Γ) p.1 p.2 i) ?_ ?_ i
    · exact continuous_fst
    · intro j; exact (continuous_apply j).comp continuous_snd

variable [LocallyCompactSpace Γ]

/-- **Iterated currying** into the `coind₁`-resolution.  A continuous function
`F : Γⁿ⁺¹ → X` is sent to the element of the `(n+1)`-st term `coind₁ⁿ⁺¹ X` obtained by currying it
`n + 1` times.  We construct it together with the proof that it is continuous in `F`. -/
noncomputable def curryResCM (X : TopRep k Γ) :
    (m : ℕ) → C(C(Fin m → Γ, ↥X), ↥(TopRep.resolutionX X m))
  | 0 => ⟨fun F => F Fin.elim0, continuous_eval_const (Fin.elim0 : Fin 0 → Γ)⟩
  | m+1 =>
    ⟨fun F => (curryResCM X m).comp ((F.comp (consCont (Γ := Γ) m)).curry),
     (ContinuousMap.continuous_postcomp (curryResCM X m)).comp
       (ContinuousMap.continuous_curry.comp
        (ContinuousMap.continuous_precomp (consCont (Γ := Γ) m)))⟩

/-- The iterated currying `C(Γⁿ⁺¹, X) → ↥(coind₁ⁿ⁺¹ X)` as a plain function. -/
noncomputable def curryRes (X : TopRep k Γ) (m : ℕ) :
    C(Fin m → Γ, ↥X) → ↥(TopRep.resolutionX X m) :=
  fun F => curryResCM X m F

@[simp] lemma curryRes_apply (X : TopRep k Γ) (m : ℕ) (F : C(Fin m → Γ, ↥X)) :
    curryRes X m F = curryResCM X m F := rfl

lemma continuous_curryRes (X : TopRep k Γ) (m : ℕ) : Continuous (curryRes X m) :=
  (curryResCM X m).continuous

/-- The defining equation of the iterated currying: on the first coordinate it is the currying of
the function given by inserting that coordinate. -/
@[simp] lemma curryRes_succ_apply (X : TopRep k Γ) (m : ℕ) (F : C(Fin (m+1) → Γ, ↥X))
    (t : Γ) :
    curryRes X (m+1) F t = curryRes X m (((F.comp (consCont (Γ := Γ) m)).curry) t) := rfl

/-- **`evalIter` is a left inverse of the iterated currying.** -/
theorem evalIter_curryRes (X : TopRep k Γ) :
    ∀ (m : ℕ) (F : C(Fin m → Γ, ↥X)) (x : Fin m → Γ),
      evalIter X m (curryRes X m F) x = F x := by
  intro m
  induction m with
  | zero => intro F x; exact congrArg F (Subsingleton.elim (Fin.elim0 : Fin 0 → Γ) x)
  | succ m ih =>
    intro F x
    show evalIter X m (curryRes X (m+1) F (x 0)) (Fin.tail x) = F x
    rw [curryRes_succ_apply]
    rw [ih]
    rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply]
    rw [show (consCont (Γ := Γ) m) (x 0, Fin.tail x) = Fin.cons (x 0) (Fin.tail x) from rfl]
    rw [Fin.cons_self_tail]

/-- **`evalIter` is injective**: an element of the `coind₁`-resolution is determined by its
iterated evaluations. -/
theorem evalIter_ext (X : TopRep k Γ) :
    ∀ m : ℕ, Function.Injective
      (fun Φ : ↥(TopRep.resolutionX X m) => fun x : Fin m → Γ => evalIter X m Φ x) := by
  intro m
  induction m with
  | zero =>
    intro Φ Ψ h
    exact congrFun h (Fin.elim0 : Fin 0 → Γ)
  | succ m ih =>
    intro Φ Ψ h
    apply ContinuousMap.ext
    intro t
    apply ih
    funext y
    exact congrFun h (Fin.cons t y)

/-- Every invariant continuous function on `Γ^{n+1}` is the iterated evaluation of an invariant
element of the `(n+1)`-st term of the `coind₁`-resolution. -/
theorem exists_evalIter_eq
    {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    (X : TopRep k Γ) (n : ℕ) (f : ↥(Work.CFTLib.ContCohomology.homCochain X n)) :
    ∃ Φ : ↥(TopRep.resolutionX X (n+1)),
      Φ ∈ (TopRep.resolutionX X (n+1)).ρ.invariants ∧
      ∀ x : Fin (n+1) → Γ, Work.CFTLib.ContCohomology.evalIter X (n+1) Φ x = f.1 x := by
  have hf : Continuous f.1 := f.2.1
  refine ⟨curryRes X (n+1) ⟨f.1, hf⟩, ?_, ?_⟩
  · rw [ContRepresentation.mem_invariants]
    intro g
    -- it suffices that both sides have the same iterated evaluations
    apply evalIter_ext X (n+1)
    funext x
    change evalIter X (n+1) ((TopRep.resolutionX X (n+1)).ρ g (curryRes X (n+1) ⟨f.1, hf⟩)) x
      = evalIter X (n+1) (curryRes X (n+1) ⟨f.1, hf⟩) x
    rw [evalIter_act]
    rw [evalIter_curryRes, evalIter_curryRes]
    change (X.ρ g) (f.1 (fun i => g⁻¹ * x i)) = f.1 x
    -- invariance of `f` in the direction `g⁻¹`
    rw [f.2.2 g⁻¹ x]
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  · intro x
    exact evalIter_curryRes X (n+1) ⟨f.1, hf⟩ x

end Work.CFTLib.ContCohomology
