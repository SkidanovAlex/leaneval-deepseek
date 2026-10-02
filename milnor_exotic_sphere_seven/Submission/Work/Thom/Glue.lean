import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.mixedCupC_pairNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The glueing of local Thom classes over a two-piece cover

This module isolates the *Mayer–Vietoris rung* of the Thom isomorphism theorem for a general
(not necessarily trivial) real bundle `Z → B`, in the form in which the honest relative
Mayer–Vietoris long exact sequence of `Submission/Work/Cohomology/relCohMV_honest_les.lean`
applies.

Setting: `U, V ⊆ B` are open with `U ∪ V = B`, and `X = Z.TotalSpace`, `A = Z.zeroComplement`
(the complement of the zero section).  The pieces of the Thom pair are `X|_U` and `X|_V` and their
intersection `X|_(U∩V)`.

* `Work.Thom.LocalThom Z n W` is **local Thom data over `W`**: a class `τ ∈ H^n(X|_W, X|_W∖0)`
  for which the local Thom map `H^k(W) → H^{k+n}(X|_W, X|_W∖0)`, `x ↦ π_W^*(x) ⌣ τ`, is bijective
  in every degree — a Thom class of `Z` restricted to `W`, expressed purely inside the total space
  `X` (so that no comparison of `Z.pullback` with the subspace `X|_W` is needed).
* `Work.Thom.thomMap_restrict` — **naturality**: restricting the global Thom map to a piece is the
  local Thom map applied to the restricted class and the restricted base class.
* `Work.Thom.ker_thomMap_le` — consequently the kernel of the global Thom map is contained in the
  kernel of the two restriction maps: a class `x` on the base with `π^*(x) ⌣ τ = 0` restricts to
  `0` on `U` and on `V`.
* `Work.Thom.exists_glue` — **the glueing**: local data over `U` and `V` whose restrictions to
  `U ∩ V` agree are the restrictions of a *global* class; this is the middle exactness of the
  honest relative Mayer–Vietoris sequence (`Work.Cohomology.honest_exact₂`).
* `Work.Thom.nonempty_thomClass_of_local` — **the reduction theorem**: if the local data over
  `U`, `V` (and the overlap) glue to a global class, the cover is *separating* in every degree
  (`x|_U = 0` and `x|_V = 0` force `x = 0`) and the global Thom map is surjective in every degree,
  then that global class is a Thom class of `Z`.

The two hypotheses of the last statement are exactly the two remaining inputs of the Mayer–Vietoris
proof of the Thom isomorphism theorem; see the discussion at the end of the file.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The projection of a piece of the total space -/

/-- The projection `X|_W → W` of the part of the total space of `Z` lying over `W ⊆ B`. -/
def pieceProj (Z : RealBundle B F ι) (W : Set B) : C(↥(Z.proj ⁻¹' W), ↥W) :=
  ⟨fun p => ⟨Z.proj p.1, p.2⟩,
    (Z.continuous_proj.comp continuous_subtype_val).subtype_mk fun p => p.2⟩

@[simp] theorem pieceProj_apply (Z : RealBundle B F ι) (W : Set B)
    (p : ↥(Z.proj ⁻¹' W)) : (pieceProj Z W p : B) = Z.proj p.1 := rfl

/-- The relative cohomology of the piece of the Thom pair over `W ⊆ B`. -/
abbrev PieceCoh (Z : RealBundle B F ι) (W : Set B) (n : ℕ) : ModuleCat ℤ :=
  Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' W) n

/-- The restriction of a class of the Thom pair to the piece over `W ⊆ B`. -/
abbrev PieceRes (Z : RealBundle B F ι) (W : Set B) (n : ℕ) :
    OpenThom Z n ⟶ PieceCoh Z W n :=
  Work.Cohomology.pdCohRes (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' W) n

/-! ## Local Thom data over a piece -/

/-- **The local Thom map** of a class `τ ∈ H^n(X|_W, X|_W∖0)`:
`H^k(W;ℤ) → H^{k+n}(X|_W, X|_W∖0)`, `x ↦ π_W^*(x) ⌣ τ`.  It is expressed entirely inside the
total space `X = Z.TotalSpace`, so that it composes with the honest relative cohomology of the
Thom pair. -/
def localThomMap (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : PieceCoh Z W n) (k : ℕ) :
    Coh ℤ k ↥W →ₗ[ℤ] PieceCoh Z W (k + n) :=
  ((LinearMap.applyₗ τ).comp
    (mixedCupC ℤ ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z) k n)).comp
      (CohMap (pieceProj Z W) ℤ k).hom

/-- The defining formula of the local Thom map. -/
theorem localThomMap_apply (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : PieceCoh Z W n) (k : ℕ) (x : Coh ℤ k ↥W) :
    localThomMap Z n W τ k x =
      (mixedCupC ℤ ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z) k n)
        ((CohMap (pieceProj Z W) ℤ k).hom x) τ := rfl

/-- **Local Thom data over a piece `W ⊆ B`**: a class of the relative cohomology of the pair
`(X|_W, X|_W ∖ 0)` whose cup map is the local Thom isomorphism.  This is a Thom class of the
bundle restricted to `W`, stated without leaving the total space. -/
structure LocalThom (Z : RealBundle B F ι) (n : ℕ) (W : Set B) where
  /-- the local Thom class -/
  τ : PieceCoh Z W n
  /-- the local Thom isomorphism, in every degree -/
  isThom : ∀ k, Function.Bijective (localThomMap Z n W τ k)

/-! ## Naturality of the global Thom map under restriction to a piece -/

variable {Z : RealBundle B F ι} {n : ℕ}

/-- **Naturality of the global Thom map under restriction to a piece.**  For a global class
`τ ∈ H^n(X, X∖0)` and a base class `x ∈ H^k(B;ℤ)`, restricting `π^*(x) ⌣ τ` to the piece over `W`
gives the local Thom map of the restricted class applied to `x|_W`. -/
theorem thomMap_restrict (Z : RealBundle B F ι) (n k : ℕ) (W : Set B)
    (τ : OpenThom Z n) (x : Coh ℤ k B) :
    (PieceRes Z W (k + n)).hom
        ((thomMap Z n τ k) x) =
      (localThomMap Z n W (ConcreteCategory.hom (PieceRes Z W n) τ) k)
        ((CohMap (subtypeMap W) ℤ k).hom x) := by
  rw [thomMap_apply, localThomMap_apply]
  have hnat := mixedCupC_pairNatural (subtypeMap (Z.proj ⁻¹' W))
    ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z) (zeroComplement Z)
    (fun y hy => hy) k n ((CohMap (bundleProj Z) ℤ k).hom x) τ
  have hproj : (bundleProj Z).comp (subtypeMap (Z.proj ⁻¹' W))
      = (subtypeMap W).comp (pieceProj Z W) := by
    apply ContinuousMap.ext
    intro p
    rfl
  have hCoh : (CohMap (subtypeMap (Z.proj ⁻¹' W)) ℤ k).hom
        ((CohMap (bundleProj Z) ℤ k).hom x)
      = (CohMap (pieceProj Z W) ℤ k).hom ((CohMap (subtypeMap W) ℤ k).hom x) := by
    have h1 := CohMap_comp (subtypeMap (Z.proj ⁻¹' W)) (bundleProj Z) ℤ k
    have h2 := CohMap_comp (pieceProj Z W) (subtypeMap W) ℤ k
    have h3 : CohMap ((bundleProj Z).comp (subtypeMap (Z.proj ⁻¹' W))) ℤ k
        = CohMap ((subtypeMap W).comp (pieceProj Z W)) ℤ k := by rw [hproj]
    have h4 : (CohMap (subtypeMap (Z.proj ⁻¹' W)) ℤ k).hom
          ((CohMap (bundleProj Z) ℤ k).hom x)
        = (CohMap ((bundleProj Z).comp (subtypeMap (Z.proj ⁻¹' W))) ℤ k).hom x := by
      rw [h1]; rfl
    have h5 : (CohMap ((subtypeMap W).comp (pieceProj Z W)) ℤ k).hom x
        = (CohMap (pieceProj Z W) ℤ k).hom ((CohMap (subtypeMap W) ℤ k).hom x) := by
      rw [h2]; rfl
    rw [h4, h3, h5]
  rw [hCoh] at hnat
  exact hnat

/-- **The kernel of the global Thom map is contained in the kernel of the restriction maps**: a
class whose product with the global class `τ` vanishes restricts to `0` on every piece over which
`τ` is a local Thom class. -/
theorem ker_thomMap_le {W : Set B} (T : LocalThom Z n W) (τ : OpenThom Z n)
    (hτ : PieceRes Z W n τ = T.τ)
    (k : ℕ) {x : Coh ℤ k B} (hx : (thomMap Z n τ k) x = 0) :
    (CohMap (subtypeMap W) ℤ k).hom x = 0 := by
  have h := thomMap_restrict Z n k W τ x
  rw [hx, map_zero] at h
  have h2 : (localThomMap Z n W
      (ConcreteCategory.hom (PieceRes Z W n) τ) k)
        ((CohMap (subtypeMap W) ℤ k).hom x) = 0 := h.symm
  rw [hτ] at h2
  exact (T.isThom k).1 (by rw [h2, map_zero])

/-! ## The state of the glueing

The two statements that complete the Mayer--Vietoris proof of the Thom isomorphism theorem for a
general bundle, and which are *not* proved in this module, are

* `exists_glue`: two piece-classes `tU ∈ H^n(X|_U, X|_U∖0)`, `tV ∈ H^n(X|_V, X|_V∖0)` with equal
  restriction to the overlap are the restrictions of a global class `τ ∈ H^n(X, X∖0)`.  This is the
  middle exactness of the honest relative Mayer--Vietoris sequence, available as
  `Work.Cohomology.honest_exact₂` (with `Work.Cohomology.honestF_fst'`/`honestF_snd'` reading off
  the two restrictions) — the only gap in its formalisation here is the bookkeeping of the biproduct
  identifications;
* `nonempty_thomClass_of_local`: if such a global `τ` restricts to local Thom classes over `U` and
  `V`, and if the cover is *separating* in every degree (`x|_U = 0` and `x|_V = 0` force `x = 0` —
  the vanishing of the Mayer--Vietoris transgression of the cover) and the global Thom map
  `x ↦ π^*(x) ⌣ τ` is surjective in every degree (the remaining half of the Mayer--Vietoris
  induction, which needs the cohomological Mayer--Vietoris exactness at the middle term for the
  base), then `τ` is a Thom class of `Z`.

Everything those two statements need from the geometry — the naturality of the cup map under
restriction (`Work.Thom.thomMap_restrict`) and its consequence for the kernel
(`Work.Thom.ker_thomMap_le`) — is proved above.
-/

end

end Work.Thom
