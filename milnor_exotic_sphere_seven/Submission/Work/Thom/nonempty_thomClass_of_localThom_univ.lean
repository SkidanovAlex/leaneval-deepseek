import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Glue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

namespace Work.Thom

/-- **Local Thom data over the whole base is a Thom class.**

If the piece over `Set.univ` of a real bundle `Z` carries local Thom data — a class
`τ ∈ PieceCoh Z Set.univ n` whose local Thom map over `↥(Set.univ : Set B)` is bijective in every
degree — then `Z` carries a Thom class of rank `n`.

The pair `(↥(Z.proj ⁻¹' Set.univ), ↥(Z.proj ⁻¹' Set.univ) ∩ zeroComplement Z)` is the pair
`(Z.TotalSpace, zeroComplement Z)` under a homeomorphism of pairs, and `↥(Set.univ : Set B)` is `B`
under the canonical homeomorphism; both are compatible with the two projections.  So the class
transports along `Work.Thom.cupMap_transfer_bwdA`, and the two copies of the base cohomology
(`H^k(↥(Set.univ : Set B))` and `H^k(B)`) are identified by the bijectivity of the `CohMap` of the
canonical homeomorphism.

NOTE (import islands).  This workspace contains mutually incompatible copies of the same constants
(`Work.Cohomology.Yt` in four modules, `Work.Cohomology.dualZ` in two).  Permitted imports for this
file are exactly the transitive closure of

  `Submission.Work.Thom.Glue` (for `LocalThom`, `PieceCoh`, `pieceProj`, `zeroComplement`) and
  `Submission.Work.Thom.ATools` (for `cupMap_transfer_iffA`, `cupMap_transfer_bwdA`,
  `bijective_relCohMap_of_homeomorphA`, `relCohMap_compA`, `relCohMap_congrA`, `relCohMap_idA`).

In particular do NOT import `Submission.Work.Thom.ModelThomDefs` (its `cupMap_transfer_bwd` is the
twin of `Work.Thom.cupMap_transfer_bwdA` but lives in the other island) and not
`Submission.Work.Cohomology.subsingleton_pdCohSub_union`.  Check with `lake build` of your module.

PROOF ROUTE (all pieces are already in the workspace; this is bookkeeping, not new mathematics).
Set `X := Z.TotalSpace`, `A := zeroComplement Z`, `Y := ↥(Z.proj ⁻¹' (Set.univ : Set B))`,
`Bs := (Subtype.val : ↥(Z.proj ⁻¹' Set.univ) → Z.TotalSpace) ⁻¹' zeroComplement Z`
(so `Bs = {y : Y | (y : Z.TotalSpace) ∈ A}`), `f : C(Y, X) := Work.Thom.subtypeMap (Z.proj ⁻¹' Set.univ)`
(= the coercion), and let `e : Y ≃ₜ X` be the canonical homeomorphism (`Subtype.val` with inverse
`fun p => ⟨p, Set.mem_univ p⟩`), so that `bijective_relCohMap_of_homeomorphA A Bs e he ℤ m` gives
the bijectivity hypothesis of `cupMap_transfer_bwdA`.  Take the common codomain of the two
projections to be `↥(Set.univ : Set B)`: `πX : C(X, ↥Set.univ) := ⟨fun p => ⟨Z.proj p, trivial⟩, _⟩`
and `πY := Work.Thom.pieceProj Z Set.univ` (then `πX.comp f = πY` is `rfl`), and apply
`Work.Thom.cupMap_transfer_bwdA f A Bs hf hfbij πX πY hπ n T.τ hτ` where `hτ : ∀ k,
Function.Bijective (fun x : Coh ℤ k ↥univ => (mixedCupC ℤ Bs k n) ((CohMap πY ℤ k).hom x) T.τ)`
is literally `T.isThom` (`Work.Thom.localThomMap_apply`).  This returns `τ' : OpenThom Z n` and the
bijectivity of `fun x : Coh ℤ k ↥univ => (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) τ'`.

It remains to replace the base `↥(Set.univ : Set B)` by `B`.  Let
`φ : C(B, ↥(Set.univ : Set B)) := ⟨fun x => ⟨x, trivial⟩, _⟩`.  Then `πX = φ.comp (bundleProj Z)`,
so by `Work.Thom.CohMap_comp` (and `ModuleCat.hom_comp`) the map
`fun x => (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) τ'` is
`(Work.Thom.thomMap Z n τ' k)` composed with `(CohMap φ ℤ k).hom : Coh ℤ k ↥univ → Coh ℤ k B`.
That map is bijective: with `g := Work.Thom.subtypeMap (Set.univ : Set B) : C(↥Set.univ, B)` one has
`CohMap φ ℤ k ≫ CohMap g ℤ k = CohMap (g.comp φ) ℤ k = 𝟙` (as `g.comp φ = ContinuousMap.id B`) and
`CohMap g ℤ k ≫ CohMap φ ℤ k = 𝟙` (as `φ.comp g = ContinuousMap.id ↥Set.univ`), both by
`Work.Thom.CohMap_comp` + `Work.Thom.CohMap_id`; conclude with
`LinearMap.hom (CohMap φ ℤ k)` bijective.  Then `thomMap Z n τ' k` is bijective because it is
`(bijective composite) ∘ (bijective)⁻¹`, e.g.
`Function.Bijective.of_comp_left`/`Function.Bijective.comp` bookkeeping: a map `F` with `F ∘ ψ`
bijective and `ψ` bijective is bijective.

Package as `⟨τ', fun k => ...⟩ : Nonempty (ThomClass Z n)`. -/
theorem nonempty_thomClass_of_localThom_univ
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type} {n : ℕ} (Z : Work.TangentClasses.RealBundle B F ι)
    (T : Work.Thom.LocalThom Z n Set.univ) :
    Nonempty (Work.Thom.ThomClass Z n) := by
  let e : ↥(Z.proj ⁻¹' (Set.univ : Set B)) ≃ₜ Z.TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  let Bs : Set ↥(Z.proj ⁻¹' (Set.univ : Set B)) :=
    (Subtype.val : ↥(Z.proj ⁻¹' (Set.univ : Set B)) → Z.TotalSpace) ⁻¹' zeroComplement Z
  let f : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace) := (e : C(_, _))
  have he : ∀ y : ↥(Z.proj ⁻¹' (Set.univ : Set B)), y ∈ Bs ↔ e y ∈ zeroComplement Z :=
    fun y => Iff.rfl
  have hf : ∀ y ∈ Bs, f y ∈ zeroComplement Z := fun y hy => (he y).mp hy
  -- the pullback along the (identity) homeomorphism `Y ≃ₜ Z.TotalSpace` is bijective
  have hfbij : ∀ m, Function.Bijective (relCohMap f Bs (zeroComplement Z) hf ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA Bs (zeroComplement Z) e (fun y => Iff.rfl) ℤ m
  let πX : C(Z.TotalSpace, ↥(Set.univ : Set B)) :=
    ⟨fun p => ⟨Z.proj p, trivial⟩, Z.continuous_proj.subtype_mk (fun _ => trivial)⟩
  let πY : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), ↥(Set.univ : Set B)) := pieceProj Z Set.univ
  have hπ : πX.comp f = πY := rfl
  -- the local Thom map of `T` is the cup map of `T.τ`
  have hτ : ∀ k, Function.Bijective (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
      (mixedCupC ℤ Bs k n) ((CohMap πY ℤ k).hom x) T.τ) := by
    intro k
    have hfun : (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
        (mixedCupC ℤ Bs k n) ((CohMap πY ℤ k).hom x) T.τ)
        = ⇑(localThomMap Z n Set.univ T.τ k) := by
      funext x
      rw [localThomMap_apply]
    rw [hfun]
    exact T.isThom k
  -- transport of the class to the total space
  obtain ⟨τ', -, hτ'⟩ :=
    cupMap_transfer_bwdA f (zeroComplement Z) Bs hf hfbij πX πY hπ n T.τ hτ
  -- replace the base `↥(Set.univ : Set B)` by `B`
  let φ : C(B, ↥(Set.univ : Set B)) :=
    ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk (fun _ => trivial)⟩
  let g : C(↥(Set.univ : Set B), B) := subtypeMap Set.univ
  have hgφ : g.comp φ = ContinuousMap.id B := by ext x; rfl
  have hφg : φ.comp g = ContinuousMap.id ↥(Set.univ : Set B) := by ext y; rfl
  have hφbij : ∀ k, Function.Bijective (CohMap φ ℤ k).hom := by
    intro k
    have h1 : ((CohMap g ℤ k).hom).comp ((CohMap φ ℤ k).hom) = LinearMap.id := by
      have h := CohMap_comp g φ ℤ k
      rw [hφg, CohMap_id] at h
      have h2 := congrArg (fun f : Coh ℤ k ↥(Set.univ : Set B) ⟶
        Coh ℤ k ↥(Set.univ : Set B) => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h2
    have h2 : ((CohMap φ ℤ k).hom).comp ((CohMap g ℤ k).hom) = LinearMap.id := by
      have h := CohMap_comp φ g ℤ k
      rw [hgφ, CohMap_id] at h
      have h3 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k B => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h3
    constructor
    · intro a b hab
      have ha := LinearMap.congr_fun h1 a
      have hb := LinearMap.congr_fun h1 b
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
      rw [hab] at ha
      exact ha.symm.trans hb
    · intro b
      exact ⟨(CohMap g ℤ k).hom b, LinearMap.congr_fun h2 b⟩
  refine ⟨⟨τ', fun k => ?_⟩⟩
  have hCoh : (CohMap πX ℤ k).hom
      = ((CohMap (bundleProj Z) ℤ k).hom).comp ((CohMap φ ℤ k).hom) := by
    have h := CohMap_linear_comp (bundleProj Z) φ ℤ k
    have hπX : πX = φ.comp (bundleProj Z) := by ext p; rfl
    rw [hπX]
    exact h.symm
  -- the cup map through `πX` is the Thom map preceded by `φ^*`
  have hcomp : Function.Bijective
      ((fun y : Coh ℤ k B => (mixedCupC ℤ (zeroComplement Z) k n)
        ((CohMap (bundleProj Z) ℤ k).hom y) τ') ∘ (CohMap φ ℤ k).hom) := by
    rw [show ((fun y : Coh ℤ k B => (mixedCupC ℤ (zeroComplement Z) k n)
          ((CohMap (bundleProj Z) ℤ k).hom y) τ') ∘ (CohMap φ ℤ k).hom)
        = (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
            (mixedCupC ℤ (zeroComplement Z) k n) ((CohMap πX ℤ k).hom x) τ') from by
      funext x
      simp only [Function.comp_apply]
      rw [LinearMap.congr_fun hCoh x]
      rfl]
    exact hτ' k
  -- hence the Thom map is bijective
  have hF : Function.Bijective (fun y : Coh ℤ k B =>
      (mixedCupC ℤ (zeroComplement Z) k n) ((CohMap (bundleProj Z) ℤ k).hom y) τ') := by
    have hψ := hφbij k
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hψ.2 a
      obtain ⟨b', rfl⟩ := hψ.2 b
      exact congrArg (CohMap φ ℤ k).hom (hcomp.1 hab)
    · intro c
      obtain ⟨x, hx⟩ := hcomp.2 c
      exact ⟨(CohMap φ ℤ k).hom x, hx⟩
  exact hF

end Work.Thom
