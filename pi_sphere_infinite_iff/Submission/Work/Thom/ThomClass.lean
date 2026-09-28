import Mathlib
import Submission.Work.Thom.Euler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The Thom class, the Thom isomorphism, and the Gysin sequence

Let `E → B` be a real bundle (`Z : Work.TangentClasses.RealBundle B F ι`, gluing data) of rank `n`,
`E∖0 ⊆ E` the complement of the zero section and `π : E → B` the projection.

* `Work.Thom.thomMap Z n τ k : H^k(B;ℤ) → H^{k+n}(E,E∖0;ℤ)` is the **Thom map**
  `x ↦ π^*(x) ⌣ τ` (the exterior cup product of the absolute class `π^*x` with the relative class
  `τ`, `Work.Thom.mixedCupC`).
* `Work.Thom.ThomClass Z n` is a **Thom class** of `Z`: a class `τ ∈ H^n(E,E∖0;ℤ)` for which the
  Thom map is bijective in every degree — the **Thom isomorphism**
  `H^k(B;ℤ) ≅ H^{k+n}(E,E∖0;ℤ)`.  An integral Thom class is exactly an *orientation* of the bundle
  (plus the Thom isomorphism it implies), so this structure is the chapter's model of "oriented
  real bundle of rank `n`".
* `Work.Thom.ThomClass.thomIso` — the Thom isomorphism as an isomorphism of `ℤ`-modules.
* `Work.Thom.ThomClass.eulerClass` — the **Euler class** `e(E) = z^*(τ) ∈ H^n(B;ℤ)` of the
  oriented bundle, the pullback of the Thom class along the zero section
  (`Work.Thom.eulerClass`), together with the vanishing theorems of
  `Submission/Work/Thom/Euler.lean`.

## The projection is a homotopy equivalence (proved here)

Two facts about the pair `(E,E∖0)` that *are* available in the workspace model:

* `Work.Thom.CohMap_zeroSection_comp_bundleProj` — `π^* ∘ z^* = id`: the zero section followed by
  the projection is the identity, and the other composite `z ∘ π` is homotopic to the identity of
  `E` through the fibrewise rescaling `(p,t) ↦ ⟨p.1, t • p.2⟩`
  (`Work.Thom.homotopic_zeroSection_comp_bundleProj`);
* consequently `π^* : H^k(B;ℤ) → H^k(E;ℤ)` is an isomorphism with inverse `z^*`
  (`Work.Thom.bijective_CohMap_bundleProj`).

This is the geometric input that turns the long exact sequence of the pair into the **Gysin
sequence** of the sphere bundle: with `π^*` invertible and the Thom isomorphism
`H^k(B) ≅ H^{k+n}(E,E∖0)`, the pair sequence
`H^{k-1+n}(E∖0) → H^{k+n}(E,E∖0) → H^{k+n}(E) → H^{k+n}(E∖0) → …` becomes
`… → H^k(B) --∪e--> H^{k+n}(B) --π^*--> H^{k+n}(E∖0) --δ--> H^{k+1}(B) → …`,
which is `Work.Thom.GysinSequence` (the exactness statements are
`Submission/Work/Thom/gysin_exact_*.lean`).

## What is *not* here

The **existence** of a Thom class for a general bundle — i.e. the Thom isomorphism theorem — is
*not* proved in this chapter.  It is the missing input, and its exact shape is recorded as
`Work.Thom.ThomClassExists` below.  What is proved is everything *conditional* on a Thom class:
the Euler class and its vanishing, the homotopy equivalence `π ≃ id`, and (delegated) the Gysin
sequence.  See `Submission/Work/Thom/README.md` for the precise statement of the gap.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter CategoryTheory

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The projection of a bundle, and the Thom map -/

/-- The **projection** `π : E → B` of a real bundle, as a continuous map. -/
def bundleProj (Z : RealBundle B F ι) : C(Z.TotalSpace, B) :=
  ⟨Z.proj, Z.continuous_proj⟩

@[simp] theorem bundleProj_apply (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    bundleProj Z p = p.1 := rfl

/-- The composite `π ∘ z` of the projection with the zero section is the identity. -/
theorem bundleProj_comp_zeroSection (Z : RealBundle B F ι) :
    (bundleProj Z).comp (zeroSection Z) = ContinuousMap.id B := by
  ext x
  rfl

/-- **The composite `z ∘ π` is homotopic to the identity of the total space**, through the
fibrewise rescaling `(p,t) ↦ ⟨p.1, t • p.2⟩` (`Work.Thom.continuous_smul_section`). -/
theorem homotopic_zeroSection_comp_bundleProj (Z : RealBundle B F ι) :
    ContinuousMap.Homotopic ((zeroSection Z).comp (bundleProj Z)) (ContinuousMap.id Z.TotalSpace) := by
  have hcont : Continuous (fun p : unitInterval × Z.TotalSpace =>
      (⟨(p.2).1, ((p.1 : unitInterval) : ℝ) • (p.2).2⟩ : Z.TotalSpace)) :=
    continuous_smul_section Z
      ((ContinuousMap.id Z.TotalSpace).comp ⟨Prod.snd, continuous_snd⟩)
      ⟨fun p : unitInterval × Z.TotalSpace => ((p.1 : unitInterval) : ℝ),
        continuous_subtype_val.comp continuous_fst⟩
  refine ⟨ContinuousMap.Homotopy.mk ⟨_, hcont⟩ ?_ ?_⟩
  · intro p
    show (⟨(p).1, ((0 : unitInterval) : ℝ) • (p).2⟩ : Z.TotalSpace)
      = (zeroSection Z).comp (bundleProj Z) p
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_smul]
    rfl
  · intro p
    show (⟨(p).1, ((1 : unitInterval) : ℝ) • (p).2⟩ : Z.TotalSpace) = p
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul]

/-- `π^* ∘ z^*` composed with the pullbacks: `z^*` is a left inverse of `π^*` on cohomology, from
`π ∘ z = id`. -/
theorem CohMap_zeroSection_comp_bundleProj (Z : RealBundle B F ι) (k : ℕ) :
    ((CohMap (zeroSection Z) ℤ k).hom).comp ((CohMap (bundleProj Z) ℤ k).hom) = LinearMap.id := by
  have h := CohMap_comp (zeroSection Z) (bundleProj Z) ℤ k
  rw [bundleProj_comp_zeroSection, CohMap_id] at h
  have h2 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k B => f.hom) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_assoc] using h2.symm

/-- `π^* ∘ z^* = id` on cohomology, from the homotopy `z ∘ π ≃ id`. -/
theorem CohMap_bundleProj_comp_zeroSection (Z : RealBundle B F ι) (k : ℕ) :
    ((CohMap (bundleProj Z) ℤ k).hom).comp ((CohMap (zeroSection Z) ℤ k).hom) = LinearMap.id := by
  have h := CohMap_comp (bundleProj Z) (zeroSection Z) ℤ k
  have h2 : (CohMap (zeroSection Z) ℤ k) ≫ (CohMap (bundleProj Z) ℤ k)
      = 𝟙 (Coh ℤ k Z.TotalSpace) := by
    rw [← h, CohMap_homotopic (homotopic_zeroSection_comp_bundleProj Z) ℤ k, CohMap_id]
  have h3 := congrArg (fun f : Coh ℤ k Z.TotalSpace ⟶ Coh ℤ k Z.TotalSpace => f.hom) h2
  simpa [ModuleCat.hom_comp] using h3

/-- **The projection induces an isomorphism on cohomology** (the bundle is a homotopy equivalence):
`π^* : H^k(B;ℤ) → H^k(E;ℤ)` is bijective, with inverse `z^*`. -/
theorem bijective_CohMap_bundleProj (Z : RealBundle B F ι) (k : ℕ) :
    Function.Bijective (CohMap (bundleProj Z) ℤ k).hom := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨(CohMap (zeroSection Z) ℤ k).hom y, ?_⟩⟩
  · have h := LinearMap.congr_fun (CohMap_zeroSection_comp_bundleProj Z k) x
    have h' := LinearMap.congr_fun (CohMap_zeroSection_comp_bundleProj Z k) y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h h'
    rw [hxy] at h
    exact h.symm.trans h'
  · exact LinearMap.congr_fun (CohMap_bundleProj_comp_zeroSection Z k) y

/-! ## The Thom map and the Thom class -/

/-- **The Thom map** `H^k(B;ℤ) → H^{k+n}(E,E∖0;ℤ)`, `x ↦ π^*(x) ⌣ τ`: the exterior cup product of
the pullback of `x` with the relative class `τ`.  For the Thom class `τ = 𝔱(E)` of a rank-`n`
bundle this is the **Thom isomorphism**. -/
def thomMap (Z : RealBundle B F ι) (n : ℕ) (τ : OpenThom Z n) (k : ℕ) :
    Coh ℤ k B →ₗ[ℤ] OpenThom Z (k + n) :=
  ((LinearMap.applyₗ τ).comp (mixedCupC ℤ (zeroComplement Z) k n)).comp
    (CohMap (bundleProj Z) ℤ k).hom

/-- The defining formula of the Thom map on a class: it is `π^*(x) ⌣ τ`. -/
theorem thomMap_apply (Z : RealBundle B F ι) (n : ℕ) (τ : OpenThom Z n) (k : ℕ)
    (x : Coh ℤ k B) :
    thomMap Z n τ k x = mixedCupC ℤ (zeroComplement Z) k n ((CohMap (bundleProj Z) ℤ k).hom x) τ :=
  rfl

/-- **A Thom class** of a rank-`n` real bundle `E → B`: a class `τ ∈ H^n(E,E∖0;ℤ)` for which the
Thom map `x ↦ π^*(x) ⌣ τ` is an isomorphism `H^k(B;ℤ) ≅ H^{k+n}(E,E∖0;ℤ)` in every degree.  An
integral Thom class is the same thing as an *orientation* of the bundle together with the Thom
isomorphism it induces, so a `ThomClass` is this chapter's model of "oriented real bundle of rank
`n`". -/
structure ThomClass (Z : RealBundle B F ι) (n : ℕ) where
  /-- the Thom class itself -/
  τ : OpenThom Z n
  /-- the Thom isomorphism: cupping with `τ` after pulling back along `π` is bijective -/
  isThom : ∀ k, Function.Bijective (thomMap Z n τ k)

namespace ThomClass

variable {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n)

/-- **The Euler class** of the oriented bundle: `e(E) = z^*(𝔱(E))`, the pullback of the Thom class
along the zero section. -/
def eulerClass : Coh ℤ n B :=
  Work.Thom.eulerClass Z n T.τ

/-- The definition of the Euler class of a Thom class, as a pullback of the Thom class. -/
theorem eulerClass_def :
    T.eulerClass = (CohMap (zeroSection Z) ℤ n).hom ((openToAbs Z n).hom T.τ) :=
  rfl

/-- **The Euler class vanishes** for an oriented bundle admitting a nowhere-zero continuous section
(`Work.Thom.eulerClass_eq_zero_of_nowhereZeroSection`). -/
theorem eulerClass_eq_zero_of_nowhereZeroSection (σ : C(B, Z.TotalSpace))
    (hσ : ∀ x, (σ x).1 = x) (hσ0 : ∀ x, (σ x).2 ≠ 0) : T.eulerClass = 0 :=
  Work.Thom.eulerClass_eq_zero_of_nowhereZeroSection Z σ hσ hσ0 n T.τ

/-- **The Thom isomorphism** `H^k(B;ℤ) ≅ H^{k+n}(E,E∖0;ℤ)` as a linear equivalence. -/
def thomEquiv (k : ℕ) : Coh ℤ k B ≃ₗ[ℤ] OpenThom Z (k + n) :=
  LinearEquiv.ofBijective (thomMap Z n T.τ k) (T.isThom k)

/-- The Thom isomorphism is the Thom map. -/
@[simp] theorem thomEquiv_apply (k : ℕ) (x : Coh ℤ k B) :
    T.thomEquiv k x = thomMap Z n T.τ k x := rfl

end ThomClass

variable {Z : RealBundle B F ι} {n : ℕ}

/-! ## The Gysin sequence of a sphere bundle

With the Thom isomorphism `H^k(B) ≅ H^{k+n}(E,E∖0)` and the homotopy equivalence
`π : E → B` (so that `π^*` is invertible with inverse `z^*`,
`Work.Thom.bijective_CohMap_bundleProj`), the long exact sequence of the pair `(E,E∖0)`

  `H^{k+n}(E∖0) → H^{k+1+n}(E,E∖0) → H^{k+1+n}(E) → H^{k+n}(E∖0) → …`

becomes the **Gysin sequence** of the sphere bundle `S(E) = E∖0`:

  `H^k(B) --∪e--> H^{k+n}(B) --π_S^*--> H^{k+n}(S E) --δ--> H^{k+1}(B) --∪e--> H^{k+n+1}(B) → …`

The three maps are defined below as `Work.Thom.gysinEuler` (`∪e`), `Work.Thom.gysinπ` (the
restriction of `π^*` to the sphere bundle) and `Work.Thom.gysinδ` (the transgression).  The
exactness statements are `Submission/Work/Thom/gysin_exact_*.lean`. -/

/-- The map `∪e : H^k(B;ℤ) → H^{k+n}(B;ℤ)` of the Gysin sequence: the Thom isomorphism followed by
the restriction to the absolute cohomology and the pullback along the zero section.  That this *is*
multiplication by the Euler class is `Work.Thom.gysinEuler_eq_cupEuler`
(`Submission/Work/Thom/gysin_cupEuler.lean`). -/
def gysinEuler (T : ThomClass Z n) (k : ℕ) : Coh ℤ k B →ₗ[ℤ] Coh ℤ (k + n) B :=
  ((CohMap (zeroSection Z) ℤ (k + n)).hom).comp
    (((relToAbs ℤ (zeroComplement Z) (k + n)).hom).comp (thomMap Z n T.τ k))

/-- The middle map `π_S^* : H^k(B;ℤ) → H^k(S E;ℤ)` of the Gysin sequence: the pullback along the
projection, restricted to the sphere bundle `S(E) = E∖0`. -/
def gysinπ (Z : RealBundle B F ι) (k : ℕ) : Coh ℤ k B →ₗ[ℤ] Coh ℤ k (zeroComplement Z) :=
  ((CohMap (subtypeMap (zeroComplement Z)) ℤ k).hom).comp ((CohMap (bundleProj Z) ℤ k).hom)

/-- The **transgression** `δ : H^{k+n}(S E;ℤ) → H^{k+1}(B;ℤ)` of the Gysin sequence: the connecting
map of the pair `(E,E∖0)` followed by the inverse of the Thom isomorphism.  (The equation
`(k+n)+1 = (k+1)+n` is `Nat.add_right_comm`.) -/
def gysinδ (T : ThomClass Z n) (k : ℕ) :
    Coh ℤ (k + n) (zeroComplement Z) →ₗ[ℤ] Coh ℤ (k + 1) B :=
  ((T.thomEquiv (k + 1)).symm).comp
    (Eq.mp (congrArg (fun m : ℕ => (Coh ℤ (k + n) (zeroComplement Z) →ₗ[ℤ] OpenThom Z m))
      (Nat.add_right_comm k n 1)) (pairδC (zeroComplement Z) (k + n)).hom)

/-! ## The missing existence statement -/

/-- **The Thom isomorphism theorem** (the missing input of this chapter), in the form the chapter
targets: the *trivial* rank-`n` real bundle `B × F → B` — model fibre `F` — carries a Thom class
`τ ∈ H^n(E,E∖0;ℤ)` for which cupping with `τ` is the Thom isomorphism.

This is the statement that the chapter does *not* prove in general: its proof needs the cohomology
of `(E,E∖0)` in terms of the cohomology of `B` — the standard argument is an induction over a
cell/CW decomposition of `B` (or a Mayer–Vietoris induction over a cover), with the trivial bundle
as the induction step.  The rank-`0` case is trivial and the trivial-bundle case is the first
target; everything *conditional* on a `ThomClass` (the Euler class, its vanishing, the Gysin
sequence) is proved in this chapter.

**The statement below is deliberately *not* `∀ Z, Nonempty (ThomClass Z n)`.**  That unqualified
form is **FALSE**: for `n = 1`, `B = S¹` the Möbius bundle is a `RealBundle` with no integral Thom
class — an integral Thom class restricts to a generator of `H¹(D(E_x), S(E_x);ℤ) ≅ ℤ` on every fibre,
and a class restricting to generators on all fibres *is* an orientation, which the Möbius bundle does
not have (`H¹(D(E),S(E);ℤ) = 0` for the Möbius bundle while `H⁰(B;ℤ) ≅ ℤ` would have to hit it).
The true general statement must be restricted to **orientable** bundles; the concrete target the
chapter works towards is the **trivial** bundle, whose Thom class is the induction step of the
Mayer–Vietoris proof, and that is what this `def` states.  It is *proved* for rank `0` and rank `1`
over an arbitrary base (`Work.Thom.nonempty_thomClass_rank_zero`,
`Work.Thom.thomClassExistsTrivial_rank_one`). -/
def ThomClassExists (B : Type) [TopologicalSpace B] (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type) [Inhabited ι] (n : ℕ) : Prop :=
  Nonempty (ThomClass (RealBundle.trivial B F ι) n)

end

end Work.Thom
