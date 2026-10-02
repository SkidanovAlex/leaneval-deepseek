import Mathlib
import Submission.Work.Bordism.Basic
import Submission.Work.Bordism.interForm_pullback
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.SignatureBordism.BilinearQuadratic
import Submission.Work.SignatureBordism.tensor_bilin_ext

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The middle form of the boundary of a bordism, and its isotropy

Let `W` be a bordism from `M` to `N` (see `Submission/Work/Bordism/Basic.lean`), so that
`∂W = M ⊔ N̄` and the two boundary parametrisations `iM : M ⟶ W`, `iN : N ⟶ W` satisfy
`(iM)_*[M] = (iN)_*[N]` in `Hₙ(W;ℤ)`.

The **middle form of the boundary** is the orthogonal sum

`Q_∂ = Q_M ⊥ (-Q_N)`

on `H^k(M;ℚ) × H^k(N;ℚ)` (`Work.Bordism.boundaryForm`), where `Q_M = Work.Bordism.midForm M` is
the rationalised middle intersection form `y ↦ ⟨y ⌣ y, [M]⟩` of `M` and the sign in front of `Q_N`
is the orientation reversal `N̄`.

The **middle comparison map** is the pullback of the two boundary parametrisations,

`Φ = (iM*, iN*) : H^k(W;ℚ) → H^k(M;ℚ) × H^k(N;ℚ)`

(`Work.Bordism.middleMap`), whose image `K` is the subspace of `Q_∂` whose *Lagrangian* status — a
consequence of Lefschetz duality — is the geometric content of bordism invariance of the signature.

## Main results

* `Work.Bordism.boundaryForm_middleMap_eq_zero` — **total isotropy of the image**: the image of `Φ`
  is totally isotropic for `Q_∂`.  This needs *no* duality: with `y = iM* x` and `z = iN* x'` for
  the same class `x ∈ H^k(W;ℚ)`,
  `⟨y ⌣ y, [M]⟩ = ⟨x ⌣ x, (iM)_*[M]⟩ = ⟨x ⌣ x, (iN)_*[N]⟩ = ⟨z ⌣ z, [N]⟩`
  by naturality of the cup product and of the Kronecker pairing (`interForm_pullback`) and by the
  boundary relation `hbd`.  This is the half of the Lagrangian statement that *is* elementary.
* `Work.Bordism.boundaryBilin_middleMap_eq_zero` — the same for the bilinear form, in the form used
  to deduce the quadratic statement on the whole image.
* `Work.Bordism.HalfDimension` — **the other half, named**: Lefschetz duality in the middle degree
  ("half lives on each side"), i.e. the image of `Φ` has half the dimension of the middle
  cohomology of the boundary.
* `Work.Bordism.sigma_eq_of_bordant` (`Submission/Work/Bordism/Invariance.lean`) — bordism
  invariance of the signature, from the isotropy proved here plus `HalfDimension` and Poincaré
  duality on the two closed pieces.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open CategoryTheory AlgebraicTopology
open TensorProduct

namespace Work.Bordism

open Work.Cohomology Work.SignatureBordism

noncomputable section

/-- **Nondegeneracy of a quadratic form**: its radical (the kernel of the associated bilinear form)
is trivial.  For the middle intersection form of a closed oriented `2k`-manifold this is Poincaré
duality; it is not available in this library in general and is therefore an explicit hypothesis
where it is used (`Submission/Work/Bordism/Invariance.lean`). -/
def Nondegenerate {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [Invertible (2 : 𝕜)]
    (Q : QuadraticForm 𝕜 V) : Prop :=
  ∀ x : V, (∀ y : V, QuadraticMap.associated Q x y = 0) → x = 0

/-- **The middle intersection form** of a closed oriented `2k`-manifold `M`, rationalised: the
quadratic form `y ↦ ⟨y ⌣ y, [M]⟩` on `H^k(M;ℤ) ⊗[ℤ] ℚ`.  Its signature is
`Work.SignatureBordism.sigma k M.X M.c`. -/
def midForm {k : ℕ} (M : ClosedOriented (k + k)) :
    QuadraticForm ℚ (ratCohomology k (TopCat.toSSet.obj M.X)) :=
  quadOfBilin (ratInterForm k (TopCat.toSSet.obj M.X) M.c)

@[simp] theorem midForm_apply {k : ℕ} (M : ClosedOriented (k + k))
    (y : ratCohomology k (TopCat.toSSet.obj M.X)) :
    midForm M y = ratInterForm k (TopCat.toSSet.obj M.X) M.c y y := rfl

/-- The signature of a closed oriented `2k`-manifold is the signature of its middle form. -/
theorem sigma_eq_signature_midForm {k : ℕ} (M : ClosedOriented (k + k)) :
    sigma k (TopCat.toSSet.obj M.X) M.c = signature (midForm M) := rfl

/-- **The middle form of the boundary** `M ⊔ N̄` of a bordism: the orthogonal sum
`Q_M ⊥ (-Q_N)`. -/
def boundaryForm {k : ℕ} (M N : ClosedOriented (k + k)) :
    QuadraticForm ℚ
      (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) :=
  (midForm M).prod (-(midForm N))

/-- The **bilinear form of the boundary**, whose diagonal is `boundaryForm`: on
`((y, z), (y', z'))` it is `⟨y ⌣ y', [M]⟩ - ⟨z ⌣ z', [N]⟩`. -/
def boundaryBilin {k : ℕ} (M N : ClosedOriented (k + k)) :
    (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) →ₗ[ℚ]
      ((ratCohomology k (TopCat.toSSet.obj M.X) ×
        ratCohomology k (TopCat.toSSet.obj N.X)) →ₗ[ℚ] ℚ) :=
  LinearMap.compl₁₂ (ratInterForm k (TopCat.toSSet.obj M.X) M.c)
      (LinearMap.fst ℚ _ _) (LinearMap.fst ℚ _ _)
    - LinearMap.compl₁₂ (ratInterForm k (TopCat.toSSet.obj N.X) N.c)
      (LinearMap.snd ℚ _ _) (LinearMap.snd ℚ _ _)

/-- The diagonal of the boundary bilinear form is the boundary quadratic form. -/
theorem boundaryBilin_self {k : ℕ} (M N : ClosedOriented (k + k))
    (v : ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) :
    boundaryBilin M N v v = boundaryForm M N v := by
  simp only [boundaryBilin, boundaryForm, midForm, quadOfBilin_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, QuadraticMap.prod_apply, neg_apply, sub_eq_add_neg]

/-- **The pullback on rationalised cohomology**, `Hᵏ(Y;ℚ) → Hᵏ(X;ℚ)`: the base change to `ℚ` of the
integral pullback `Work.Cohomology.singularCohomologyMap`. -/
def pullbackRat (k : ℕ) {X Y : TopCat} (f : X ⟶ Y) :
    ratCohomology k (TopCat.toSSet.obj Y) →ₗ[ℚ] ratCohomology k (TopCat.toSSet.obj X) :=
  (singularCohomologyMap ℤ X Y f k).hom.baseChange ℚ

theorem pullbackRat_tmul (k : ℕ) {X Y : TopCat} (f : X ⟶ Y) (a : ℚ)
    (x : (cochainC ℤ (TopCat.toSSet.obj Y)).homology k) :
    pullbackRat k f (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] ((singularCohomologyMap ℤ X Y f k).hom x) :=
  LinearMap.baseChange_tmul _ a x

theorem pullbackRat_id (k : ℕ) (X : TopCat) :
    pullbackRat k (𝟙 X) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [pullbackRat_tmul]; simp
  | add x y hx hy => rw [map_add, hx, hy]; simp

/-- **The middle comparison map** of a bordism: the pullbacks of the two boundary
parametrisations, `Hᵏ(W;ℚ) → Hᵏ(M;ℚ) × Hᵏ(N;ℚ)`.  Its image is the subspace of the middle form of
the boundary on which the Lagrangian of bordism invariance of the signature lives. -/
def middleMap (k : ℕ) {M N : ClosedOriented (k + k)} (h : Bordism M N) :
    ratCohomology k (TopCat.toSSet.obj h.W) →ₗ[ℚ]
      (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) :=
  (pullbackRat k h.iM).prod (pullbackRat k h.iN)

@[simp] theorem middleMap_apply {k : ℕ} {M N : ClosedOriented (k + k)} (h : Bordism M N)
    (z : ratCohomology k (TopCat.toSSet.obj h.W)) :
    middleMap k h z = (pullbackRat k h.iM z, pullbackRat k h.iN z) := rfl

theorem middleMap_tmul (k : ℕ) {M N : ClosedOriented (k + k)} (h : Bordism M N) (a : ℚ)
    (x : (cochainC ℤ (TopCat.toSSet.obj h.W)).homology k) :
    middleMap k h (a ⊗ₜ[ℤ] x)
      = (a ⊗ₜ[ℤ] ((singularCohomologyMap ℤ M.X h.W h.iM k).hom x),
         a ⊗ₜ[ℤ] ((singularCohomologyMap ℤ N.X h.W h.iN k).hom x)) := by
  rw [middleMap_apply, pullbackRat_tmul, pullbackRat_tmul]

/-! ## Isotropy of the image of the middle map -/

/-- **The image of the middle comparison map is totally isotropic** (bilinear form version): for
`z, z' ∈ Hᵏ(W;ℚ)`,

`⟨iM* z ⌣ iM* z', [M]⟩ - ⟨iN* z ⌣ iN* z', [N]⟩ = 0`.

This is the elementary half of the Lagrangian statement: it needs *no* duality, only the boundary
relation `(iM)_*[M] = (iN)_*[N]` (which `∂W = M ⊔ N̄` gives through the long exact sequence of the
pair) together with the naturality of the cup product and of the Kronecker pairing. -/
theorem boundaryBilin_middleMap_eq_zero (k : ℕ) {M N : ClosedOriented (k + k)} (h : Bordism M N)
    (z z' : ratCohomology k (TopCat.toSSet.obj h.W)) :
    boundaryBilin M N (middleMap k h z) (middleMap k h z') = 0 := by
  have hΨ : LinearMap.compl₁₂ (boundaryBilin M N) (middleMap k h) (middleMap k h) = 0 := by
    apply tensor_bilin_ext
    intro a b x x'
    show boundaryBilin M N (middleMap k h (a ⊗ₜ[ℤ] x)) (middleMap k h (b ⊗ₜ[ℤ] x')) = 0
    rw [middleMap_tmul k h a x, middleMap_tmul k h b x']
    simp only [boundaryBilin, LinearMap.sub_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rw [ratInterForm_tmul k (TopCat.toSSet.obj M.X) M.c a b _ _, 
      ratInterForm_tmul k (TopCat.toSSet.obj N.X) N.c a b _ _]
    rw [interForm_pullback h.iM k M.c x x', interForm_pullback h.iN k N.c x x',
      h.hbd]
    ring
  have h2 : ∀ z z' : ratCohomology k (TopCat.toSSet.obj h.W),
      boundaryBilin M N (middleMap k h z) (middleMap k h z') = 0 := by
    intro z z'
    have h3 := LinearMap.congr_fun (LinearMap.congr_fun hΨ z) z'
    simpa using h3
  exact h2 z z'

/-- **The image of the middle comparison map is totally isotropic** (quadratic form version): the
middle form of the boundary vanishes on the image of `Hᵏ(W;ℚ) → Hᵏ(∂W;ℚ)`.

This is the first half of the statement that the image is a *Lagrangian*: the second half —
maximality, i.e. `HalfDimension` below — is Lefschetz duality. -/
theorem boundaryForm_middleMap_eq_zero (k : ℕ) {M N : ClosedOriented (k + k)} (h : Bordism M N)
    (z : ratCohomology k (TopCat.toSSet.obj h.W)) :
    boundaryForm M N (middleMap k h z) = 0 := by
  rw [← boundaryBilin_self M N (middleMap k h z)]
  exact boundaryBilin_middleMap_eq_zero k h z z

/-- Every element of the image of the middle map is isotropic for the middle form of the
boundary. -/
theorem boundaryForm_eq_zero_of_mem_range (k : ℕ) {M N : ClosedOriented (k + k)}
    (h : Bordism M N)
    (v : ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X))
    (hv : v ∈ LinearMap.range (middleMap k h)) : boundaryForm M N v = 0 := by
  obtain ⟨z, rfl⟩ := hv
  exact boundaryForm_middleMap_eq_zero k h z

/-! ## The duality input -/

/-- **The Lefschetz-duality (middle degree) input of bordism invariance of the signature.**

For a bordism `W` with `∂W = M ⊔ N̄` the middle comparison map
`Φ = (iM*, iN*) : Hᵏ(W;ℚ) → Hᵏ(M;ℚ) × Hᵏ(N;ℚ)` has image of exactly half the dimension of the
middle cohomology `Hᵏ(∂W;ℚ) = Hᵏ(M;ℚ) × Hᵏ(N;ℚ)` of the boundary — "half lives on each side".

This is the middle-dimensional consequence of Poincaré–Lefschetz duality,
`Hᵏ(∂W;ℚ)/K ≅ H^{k+1}(W,∂W;ℚ) ≅ H_k(W;ℚ)`, together with the long exact sequence of the pair
`(W, ∂W)`.  It is a theorem of topology for compact oriented manifolds with boundary; no proof of
Lefschetz duality exists in this library, so it is carried as an explicit hypothesis.  Together with
the elementary isotropy `boundaryForm_middleMap_eq_zero` and Poincaré duality on the closed pieces
(`Nondegenerate (midForm M)`, `Nondegenerate (midForm N)`), it *is* the statement that the image of
`Φ` is a Lagrangian of the middle form of the boundary. -/
def HalfDimension (k : ℕ) {M N : ClosedOriented (k + k)} (h : Bordism M N) : Prop :=
  2 * Module.finrank ℚ (LinearMap.range (middleMap k h)) =
    Module.finrank ℚ (ratCohomology k (TopCat.toSSet.obj M.X) ×
      ratCohomology k (TopCat.toSSet.obj N.X))

end

end Work.Bordism
