import Mathlib
import Submission.Work.TangentClasses.Cohomology
import Submission.Work.CharacteristicClasses.Invariants

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The first Pontryagin class of a rank-4 real bundle over `S⁴`, pulled back to any base

`Submission/Work/CharacteristicClasses/` computes the first Pontryagin class of a rank-4 oriented
real bundle over `S⁴` as a *number*: for a bundle presented by its spin decomposition
`b : SpinBundle` (a pair of clutching functions `S³ → S³`), the invariants are functions of the
degrees of the clutching functions, in particular `b.pontryagin1 : ℤ`
(`p₁(ξ) = 6` for Milnor's bundle).

This module turns that into a *class* in `H⁴` of any space that maps to `S⁴`, and then into a
class of any finite sum of such pullbacks:

* `p1Pulled G φ b ∈ H⁴(B;ℤ)` is `φ^*(p₁(b) · G)`, where `G ∈ H⁴(S⁴;ℤ)` is a chosen generator of
  `H⁴(S⁴;ℤ) ≅ ℤ` and `φ : C(B, S⁴)`; this is the first Pontryagin class of the rank-4 bundle with
  clutching presentation `b` pulled back along `φ`.
* `ClutchPresentation B = List (C(B,S⁴) × SpinBundle)` is the chapter's notion of a bundle
  presented as a finite Whitney sum of rank-4 bundles pulled back from `S⁴`; `ClutchPresentation.p1`
  is the sum of the contributions.

The API is complete for the chapter's purposes:

* **naturality**: `p1Pulled_natural`, `ClutchPresentation.p1_comp` (pullback along `ψ`), and
  `p1Pulled_id` (on `S⁴` itself, `p1Pulled G id b = p₁(b) · G` — the **normalisation** and the
  agreement with the chapter's `pontryagin1`);
* **Whitney additivity**: `p1Pulled_sum`, `ClutchPresentation.p1_append` (concatenation of
  presentations is the sum of the classes, i.e. `p₁(E ⊕ F) = p₁(E) + p₁(F)`);
* **stability**: `p1Pulled_sum_trivial`, `ClutchPresentation.p1_stabilize` — the trivial summand
  contributes nothing (`p₁(TS⁴) = 0` is `p1Pulled_tangentSphere`);
* **the two numerical values used by the endgame**: `p1Pulled_xi` (pullback of `p₁(ξ) = 6 · G`) and
  `p1Pulled_tangent_sum_xi` (pullback of `p₁(TS⁴ ⊕ ξ) = 6 · G`, i.e. the value of `p₁(TX)` on the
  disc bundle of `X = D(ξ) ∪_F D⁸`, used in `Submission/Work/TangentClasses/Capped.lean`);
* **the product formula**: `ClutchPresentation.p1_prod` —
  `p₁(T(M × N)) = π₁^*(p₁(TM)) + π₂^*(p₁(TN))` for the induced presentations.
-/

namespace Work.TangentClasses

open CategoryTheory
open Work.CharacteristicClasses

noncomputable section

/-- The base `S⁴ = ℝ⁴ ∪ {∞}` of Milnor's bundles (definitionally the workspace's
`Submission.Milnor.S4`). -/
abbrev S4 : Type := OnePoint (EuclideanSpace ℝ (Fin 4))

variable {B : Type} [TopologicalSpace B]

/-- **The first Pontryagin class of a rank-4 real bundle over `S⁴` with clutching presentation
`b`, pulled back along `φ : C(B, S⁴)`**: the class `φ^*(p₁(b) · G) ∈ H⁴(B;ℤ)`, where
`G ∈ H⁴(S⁴;ℤ)` is a chosen generator of `H⁴(S⁴;ℤ) ≅ ℤ` and `p₁(b) ∈ ℤ` is the chapter's
`Work.CharacteristicClasses.SpinBundle.pontryagin1`. -/
def p1Pulled (G : H 4 S4) (φ : C(B, S4)) (b : SpinBundle) : H 4 B :=
  (HMap φ 4).hom ((b.pontryagin1 : ℤ) • G)

/-- **Normalisation / agreement with the chapter's `pontryagin1` on `S⁴`**: for a bundle over
`S⁴` itself (`φ = id`), the class is `p₁(b) · G`. -/
@[simp] theorem p1Pulled_id (G : H 4 S4) (b : SpinBundle) :
    p1Pulled G (ContinuousMap.id S4) b = (b.pontryagin1 : ℤ) • G := by
  rw [p1Pulled, HMap_id]
  rfl

/-- **Naturality**: the class of the bundle pulled back along `ψ` is the pullback of the class. -/
theorem p1Pulled_natural (G : H 4 S4) (φ : C(B, S4)) {B' : Type} [TopologicalSpace B']
    (ψ : C(B', B)) (b : SpinBundle) :
    p1Pulled G (φ.comp ψ) b = (HMap ψ 4).hom (p1Pulled G φ b) := by
  rw [p1Pulled, p1Pulled, HMap_comp]
  rfl

/-- **Whitney additivity**: the class of a Whitney sum of two presented bundles is the sum. -/
theorem p1Pulled_sum (G : H 4 S4) (φ : C(B, S4)) (b₁ b₂ : SpinBundle) :
    p1Pulled G φ (b₁.sum b₂) = p1Pulled G φ b₁ + p1Pulled G φ b₂ := by
  rw [p1Pulled, p1Pulled, p1Pulled, SpinBundle.pontryagin1_sum, add_zsmul]
  exact map_add _ _ _

/-- The trivial bundle has vanishing first Pontryagin class. -/
@[simp] theorem p1Pulled_trivial (G : H 4 S4) (φ : C(B, S4)) :
    p1Pulled G φ SpinBundle.trivial = 0 := by
  rw [p1Pulled, SpinBundle.pontryagin1_trivial, zero_zsmul]
  exact map_zero _

/-- **Stability**: a trivial summand contributes nothing. -/
@[simp] theorem p1Pulled_sum_trivial (G : H 4 S4) (φ : C(B, S4)) (b : SpinBundle) :
    p1Pulled G φ (b.sum SpinBundle.trivial) = p1Pulled G φ b := by
  rw [p1Pulled_sum, p1Pulled_trivial, add_zero]

/-- **`p₁(TS⁴) = 0`**: the tangent bundle of `S⁴` is stably trivial, so its first Pontryagin
class (pulled back to any base) vanishes. -/
@[simp] theorem p1Pulled_tangentSphere (G : H 4 S4) (φ : C(B, S4)) :
    p1Pulled G φ SpinBundle.tangentSphere = 0 := by
  rw [p1Pulled, SpinBundle.pontryagin1_tangentSphere, zero_zsmul]
  exact map_zero _

/-- **`p₁(ξ) = 6` in class form**: the pullback of Milnor's bundle `ξ = ξ_{-2} = L²R⁻¹` has first
Pontryagin class `6 · φ^*G`. -/
theorem p1Pulled_xi (G : H 4 S4) (φ : C(B, S4)) :
    p1Pulled G φ SpinBundle.xi = (6 : ℤ) • (HMap φ 4).hom G := by
  rw [p1Pulled, SpinBundle.pontryagin1_xi]
  rw [HMap_zsmul]

/-- **The value on the disc bundle of `X = D(ξ) ∪_F D⁸`**: `p₁(TS⁴ ⊕ ξ) = p₁(ξ) = 6`, so the
pullback of the presented bundle `TS⁴ ⊕ ξ` has class `6 · φ^*G`. -/
theorem p1Pulled_tangent_sum_xi (G : H 4 S4) (φ : C(B, S4)) :
    p1Pulled G φ (SpinBundle.tangentSphere.sum SpinBundle.xi) =
      (6 : ℤ) • (HMap φ 4).hom G := by
  rw [p1Pulled_sum, p1Pulled_tangentSphere, p1Pulled_xi, zero_add]

/-! ## Presentations as finite sums of pullbacks from `S⁴` -/

/-- A **clutching presentation** of a real bundle over `B`: a finite list of rank-4 bundles over
`S⁴` (each with its clutching presentation) pulled back along maps `B → S⁴`, to be read as their
Whitney sum.  This is the shape in which the tangent bundles of the chapter's manifolds are
presented (e.g. `TX` restricted to the disc bundle of `X = D(ξ) ∪_F D⁸` is the single summand
`(π, TS⁴ ⊕ ξ)`). -/
abbrev ClutchPresentation (B : Type) [TopologicalSpace B] : Type := List (C(B, S4) × SpinBundle)

namespace ClutchPresentation

variable {G : H 4 S4}

/-- **The first Pontryagin class of a clutching presentation**: the sum of the contributions
`φ_i^*(p₁(b_i)·G)`. -/
def p1 (G : H 4 S4) (P : ClutchPresentation B) : H 4 B :=
  (P.map (fun p => p1Pulled G p.1 p.2)).sum

@[simp] theorem p1_nil (G : H 4 S4) : p1 G ([] : ClutchPresentation B) = 0 := rfl

@[simp] theorem p1_singleton (G : H 4 S4) (φ : C(B, S4)) (b : SpinBundle) :
    p1 G [(φ, b)] = p1Pulled G φ b := by
  simp [p1]

/-- **Whitney additivity**, in presentation form: concatenating presentations adds the classes. -/
theorem p1_append (G : H 4 S4) (P Q : ClutchPresentation B) :
    p1 G (P ++ Q) = p1 G P + p1 G Q := by
  simp [p1]

/-- A presentation whose summands are all trivial has vanishing first Pontryagin class. -/
theorem p1_of_trivial (G : H 4 S4) (P : ClutchPresentation B)
    (hP : ∀ p ∈ P, p.2 = SpinBundle.trivial) : p1 G P = 0 := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp : p.2 = SpinBundle.trivial := hP p (by simp)
    have hP' : ∀ q ∈ P, q.2 = SpinBundle.trivial := fun q hq => hP q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, p1] at *
    rw [hp, p1Pulled_trivial, ih hP', zero_add]

/-- **Naturality** for presentations: pulling every summand back along `ψ : C(B', B)`. -/
theorem p1_comp (G : H 4 S4) (P : ClutchPresentation B) {B' : Type} [TopologicalSpace B']
    (ψ : C(B', B)) :
    p1 G (P.map (fun p => (p.1.comp ψ, p.2))) = (HMap ψ 4).hom (p1 G P) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons, p1] at *
    rw [ih, p1Pulled_natural]
    exact (map_add _ _ _).symm

/-- **Stability** for presentations: replacing every summand by its sum with the trivial bundle
does not change the class. -/
theorem p1_stabilize (G : H 4 S4) (P : ClutchPresentation B) :
    p1 G (P.map (fun p => (p.1, p.2.sum SpinBundle.trivial))) = p1 G P := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons, p1] at *
    rw [ih, p1Pulled_sum_trivial]

/-- **Stability**, in presentation form: appending a presentation all of whose summands are
trivial does not change the class. -/
theorem p1_append_trivial (G : H 4 S4) (P Q : ClutchPresentation B)
    (hQ : ∀ q ∈ Q, q.2 = SpinBundle.trivial) : p1 G (P ++ Q) = p1 G P := by
  rw [p1_append, p1_of_trivial G Q hQ, add_zero]

/-- **Stability `p₁(T(M × ℝ^k)) = p₁(TM)`**: if `P` presents `TM`, then the presentation of
`T(M × ℝ^k)` — the summands of `P` pulled back along the first projection, together with `k`
trivial summands for the second factor — has first Pontryagin class `π₁^*(p₁(TM))`. -/
theorem p1_prod_model (G : H 4 S4) {M : Type} [TopologicalSpace M]
    (P : ClutchPresentation M) (k : ℕ) (x₀ : S4) :
    p1 G ((P.map (fun p =>
          (p.1.comp (ContinuousMap.fst : C(M × (Fin k → ℝ), M)), p.2))) ++
        (List.replicate k ((ContinuousMap.const (M × (Fin k → ℝ)) x₀),
          SpinBundle.trivial))) =
      (HMap (ContinuousMap.fst : C(M × (Fin k → ℝ), M)) 4).hom (p1 G P) := by
  rw [p1_append, p1_comp]
  suffices h : p1 G (List.replicate k
      ((ContinuousMap.const (M × (Fin k → ℝ)) x₀), SpinBundle.trivial)) = 0 by rw [h, add_zero]
  exact p1_of_trivial G _ fun q hq => by
    rw [List.mem_replicate] at hq
    rw [hq.2]

/-- **The product formula**: for presentations `P` of `TM` (over `M`) and `Q` of `TN` (over `N`),
the presentation of `T(M × N)` — every summand pulled back along the corresponding projection —
has first Pontryagin class `π₁^* p₁(TM) + π₂^* p₁(TN)`. -/
theorem p1_prod (G : H 4 S4) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (P : ClutchPresentation M) (Q : ClutchPresentation N) :
    p1 G ((P.map (fun p => (p.1.comp (ContinuousMap.fst : C(M × N, M)), p.2))) ++
        (Q.map (fun q => (q.1.comp (ContinuousMap.snd : C(M × N, N)), q.2)))) =
      (HMap (ContinuousMap.fst : C(M × N, M)) 4).hom (p1 G P) +
        (HMap (ContinuousMap.snd : C(M × N, N)) 4).hom (p1 G Q) := by
  rw [p1_append, p1_comp, p1_comp]

end ClutchPresentation

end

end Work.TangentClasses
