import Mathlib
import Submission.Work.Pi6.EFACTS.tuctDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The universal coefficient theorem for injective coefficients

For a chain complex `C` of `ℤ`-modules (indexed by `ℕ`) and an injective `ℤ`-module `G`, the `k`-th
cohomology of the cochain complex `Hom_ℤ(C, G)` is the `G`-dual of the `k`-th homology of `C`:

`Hᵏ(Hom_ℤ(C, G)) ≅ Hom_ℤ(Hₖ(C), G)`.

Because `G` is injective, `Hom_ℤ(-, G)` is exact; consequently the comparison map

`Ψₖ : ker δᵏ ⟶ Hom_ℤ(Zₖ ⧸ Bₖ, G),  f ↦ (z ↦ f(z))`

(where `Zₖ` are the `k`-cycles and `Bₖ` the `k`-boundaries of `C`) is onto — every functional on the
cycles that vanishes on the boundaries extends, by injectivity of `G` — and its kernel is the image
of the transposed differential `δᵏ⁻¹`. This gives the middle isomorphism
`ker δᵏ ⧸ im δᵏ⁻¹ ≅ Hom_ℤ(Hₖ(C), G)`, and both `Hᵏ(Hom(C,G))` and `Hₖ(C)` are identified with the
corresponding `ker ⧸ im` quotients.

`Module.Injective ℤ G` is only the extension property for modules in the same universe as `G`, so
the extension statements used below are derived from it through `Module.Baer` (Baer's criterion for
`ℤ`, whose ideals live in the same universe as `ℤ`), which is universe-polymorphic.

Everything is stated with an explicit universe `v` for the carriers of `C`: this keeps the universe
parameters of the intermediate results "single", instead of the `max u₁ u₂` shapes that the
`ModuleCat.of` in the statements would otherwise produce, which the elaborator cannot invert.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

universe v

namespace Work.Pi6.EFACTS

noncomputable section

variable (G : Type) [AddCommGroup G] [Module ℤ G]

/-- Universe-polymorphic form of the extension property of an injective `ℤ`-module: `Module.Injective
ℤ G` only gives it for modules in the universe of `G`, whereas here the source and target may live
in any universes.  Derived from Baer's criterion, which for `ℤ` is universe-polymorphic. -/
lemma injective_out_ulift {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module ℤ X]
    [Module ℤ Y] [Module.Injective ℤ G] (g : X →ₗ[ℤ] G) (ι : X →ₗ[ℤ] Y)
    (hι : Function.Injective ι) :
    ∃ h : Y →ₗ[ℤ] G, ∀ x, h (ι x) = g x := by
  obtain ⟨h, H⟩ := Module.Baer.extension_property
    (Module.Baer.of_injective (R := ℤ) (Q := G) ‹Module.Injective ℤ G›) ι hι g
  exact ⟨h, fun x => DFunLike.congr_fun H x⟩

/-- Precomposition with a linear equivalence, as a linear equivalence of `Hom`-modules
(contravariant in the source).  Built from an additive equivalence so that the `ℤ`-module structure
on the `Hom`-modules is the canonical one (`AddEquiv.toIntLinearEquiv`). -/
noncomputable def precompEquiv {M : Type*} {N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) : (N →ₗ[ℤ] G) ≃ₗ[ℤ] (M →ₗ[ℤ] G) :=
  ({ toFun := fun f => f.comp e.toLinearMap
     invFun := fun f => f.comp e.symm.toLinearMap
     left_inv := by intro f; ext x; simp
     right_inv := by intro f; ext x; simp
     map_add' := by intro f g; ext x; simp } : (N →ₗ[ℤ] G) ≃+ (M →ₗ[ℤ] G)).toIntLinearEquiv

/-- The underlying `ℤ`-linear map of an element of `Hom_ℤ(Cₙ, G)`. -/
def hval (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ) (φ : ↥((homComplex G C).X n)) :
    (↥(C.X n) →ₗ[ℤ] G) := φ

lemma homComplex_d_apply (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    (φ : ↥((homComplex G C).X n)) :
    ((homComplex G C).d n (n+1)).hom φ = (hval G C n φ).comp ((C.d (n+1) n).hom) := by
  rw [homComplex_d]
  rfl

lemma homComplex_d_sub_apply (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    (g : ↥(C.X (n-1)) →ₗ[ℤ] G) :
    ((homComplex G C).d (n-1) n).hom (g : ↥((homComplex G C).X (n-1))) =
      g.comp ((C.d n (n-1)).hom) := by
  rcases n with _ | n
  · have h0 : (homComplex G C).d (0-1) 0 = 0 :=
      HomologicalComplex.shape _ _ _ (by simp [ComplexShape.up])
    have h1 : C.d 0 (0-1) = 0 :=
      HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down])
    rw [h0, h1]
    simp [ModuleCat.hom_zero]
  · show ((homComplex G C).d n (n+1)).hom (g : ↥((homComplex G C).X n)) =
      g.comp ((C.d (n+1) n).hom)
    rw [homComplex_d]
    rfl

/-- The comparison map `Ψ` is well defined: a cocycle kills the boundaries. -/
lemma homKill (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    (f : ↥(LinearMap.ker ((homComplex G C).d n (n+1)).hom)) :
    Work.Cohomology.uctH C n ≤
      LinearMap.ker ((hval G C n f.1).comp (Work.Cohomology.uctZ C n).subtype) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change (hval G C n f.1) ↑x = 0
  have hx' : (↑x : ↥(C.X n)) ∈ Work.Cohomology.uctB C n :=
    (Work.Cohomology.mem_uctH C n x).1 hx
  obtain ⟨y, hy⟩ := hx'
  have h2 : (hval G C n f.1) ((C.d (n+1) n).hom y) = 0 := by
    have hf : ((homComplex G C).d n (n+1)).hom f.1 = 0 := LinearMap.mem_ker.mp f.2
    rw [homComplex_d_apply] at hf
    simpa using LinearMap.congr_fun hf y
  rw [show (↑x : ↥(C.X n)) = (C.d (n+1) n).hom y from hy.symm]
  exact h2

/-- The comparison map from the `n`-cocycles of `Hom_ℤ(C, G)` to the `G`-dual of the
`n`-th homology of `C`. -/
def uctPsi (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ) :
    (↥(LinearMap.ker ((homComplex G C).d n (n+1)).hom)) →ₗ[ℤ]
      ((↥(Work.Cohomology.uctZ C n) ⧸ Work.Cohomology.uctH C n) →ₗ[ℤ] G) where
  toFun f := (Work.Cohomology.uctH C n).liftQ
    ((hval G C n f.1).comp (Work.Cohomology.uctZ C n).subtype) (homKill G C n f)
  map_add' f g := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (Work.Cohomology.uctH C n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, hval,
      Submodule.coe_add, Submodule.subtype_apply]
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (Work.Cohomology.uctH C n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, hval,
      Submodule.coe_smul, Submodule.subtype_apply, RingHom.id_apply]
    rfl

lemma uctPsi_apply (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    (f : ↥(LinearMap.ker ((homComplex G C).d n (n+1)).hom))
    (x : ↥(Work.Cohomology.uctZ C n)) :
    uctPsi G C n f ((Work.Cohomology.uctH C n).mkQ x) = (hval G C n f.1) x := by
  show (Work.Cohomology.uctH C n).liftQ
      ((hval G C n f.1).comp (Work.Cohomology.uctZ C n).subtype) _
      ((Work.Cohomology.uctH C n).mkQ x) = (hval G C n f.1) x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
  rfl

/-- `Ψ` is surjective: every `G`-valued functional on the homology extends to the cocycles,
because `G` is injective. -/
theorem uctPsi_surj (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    [Module.Injective ℤ G] :
    Function.Surjective (uctPsi G C n) := by
  intro g
  let h' : ↥(Work.Cohomology.uctZ C n) →ₗ[ℤ] G :=
    g.comp (Submodule.mkQ (Work.Cohomology.uctH C n))
  obtain ⟨F, hF⟩ := injective_out_ulift G h' (Work.Cohomology.uctZ C n).subtype
    Subtype.val_injective
  have hFmem : ((homComplex G C).d n (n+1)).hom (F : ↥((homComplex G C).X n)) = 0 := by
    rw [homComplex_d_apply]
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hy : ((C.d (n+1) n).hom y : ↥(C.X n)) ∈ Work.Cohomology.uctB C n := ⟨y, rfl⟩
    have hmem : (⟨(C.d (n+1) n).hom y, Work.Cohomology.uctB_le_uctZ C n hy⟩ :
        ↥(Work.Cohomology.uctZ C n)) ∈ Work.Cohomology.uctH C n :=
      (Work.Cohomology.mem_uctH C n _).mpr hy
    have h1 : F ((C.d (n+1) n).hom y) =
        h' ⟨(C.d (n+1) n).hom y, Work.Cohomology.uctB_le_uctZ C n hy⟩ :=
      hF ⟨(C.d (n+1) n).hom y, Work.Cohomology.uctB_le_uctZ C n hy⟩
    have h2 : (Submodule.mkQ (Work.Cohomology.uctH C n))
        ⟨(C.d (n+1) n).hom y, Work.Cohomology.uctB_le_uctZ C n hy⟩ = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hmem
    show F ((C.d (n+1) n).hom y) = 0
    rw [h1]
    show g ((Submodule.mkQ (Work.Cohomology.uctH C n))
      ⟨(C.d (n+1) n).hom y, Work.Cohomology.uctB_le_uctZ C n hy⟩) = 0
    rw [h2, map_zero]
  refine ⟨⟨F, hFmem⟩, ?_⟩
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := (Work.Cohomology.uctH C n).mkQ_surjective w
  rw [uctPsi_apply]
  show F ((Work.Cohomology.uctZ C n).subtype z) =
    g ((Submodule.mkQ (Work.Cohomology.uctH C n)) z)
  rw [hF z]
  rfl

/-- The kernel of the comparison map `Ψ` is the image of the transposed differential. -/
theorem uctPsi_ker (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    [Module.Injective ℤ G] :
    LinearMap.ker (uctPsi G C n) = homPre G C n := by
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have hkill : (hval G C n f.1).comp (Work.Cohomology.uctZ C n).subtype = 0 :=
      Work.Cohomology.liftQ_eq_zero_imp (Work.Cohomology.uctH C n) _
        (homKill G C n f) hf
    have hkill' : ∀ x : ↥(C.X n), x ∈ Work.Cohomology.uctZ C n →
        (hval G C n f.1) x = 0 := by
      intro x hx
      have h := LinearMap.congr_fun hkill ⟨x, hx⟩
      have h2 : (hval G C n f.1) ((Work.Cohomology.uctZ C n).subtype ⟨x, hx⟩) = 0 := h
      simpa using h2
    let fbar : (↥(C.X n) ⧸ Work.Cohomology.uctZ C n) →ₗ[ℤ] G :=
      (Work.Cohomology.uctZ C n).liftQ (hval G C n f.1) (fun x hx => hkill' x hx)
    let e := ((C.d n (n-1)).hom).quotKerEquivRange
    let g₀ : ↥(LinearMap.range ((C.d n (n-1)).hom)) →ₗ[ℤ] G := fbar.comp e.symm.toLinearMap
    obtain ⟨y, hy⟩ := injective_out_ulift G g₀ (LinearMap.range ((C.d n (n-1)).hom)).subtype
      Subtype.val_injective
    refine ⟨y, ?_⟩
    apply Subtype.ext
    show ((homComplex G C).d (n-1) n).hom (y : ↥((homComplex G C).X (n-1))) = f.1
    rw [homComplex_d_sub_apply]
    apply LinearMap.ext
    intro x
    show y ((C.d n (n-1)).hom x) = (hval G C n f.1) x
    have h1 : y ((C.d n (n-1)).hom x) = g₀ ⟨(C.d n (n-1)).hom x, ⟨x, rfl⟩⟩ :=
      hy ⟨(C.d n (n-1)).hom x, ⟨x, rfl⟩⟩
    rw [h1]
    show fbar (e.symm ⟨(C.d n (n-1)).hom x, ⟨x, rfl⟩⟩) = (hval G C n f.1) x
    have h2 : e.symm ⟨(C.d n (n-1)).hom x, ⟨x, rfl⟩⟩ = (Work.Cohomology.uctZ C n).mkQ x :=
      LinearMap.quotKerEquivRange_symm_apply_image _ x ⟨x, rfl⟩
    rw [h2]
    show fbar ((Work.Cohomology.uctZ C n).mkQ x) = (hval G C n f.1) x
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  · intro f hf
    rw [LinearMap.mem_ker]
    obtain ⟨y, hy⟩ := hf
    have hval' : ((homComplex G C).d (n-1) n).hom (y : ↥((homComplex G C).X (n-1))) = f.1 := by
      have h := congrArg Subtype.val hy
      simpa [LinearMap.codRestrict_apply] using h
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (Work.Cohomology.uctH C n).mkQ_surjective w
    rw [uctPsi_apply, LinearMap.zero_apply, ← hval']
    show (hval G C n (((homComplex G C).d (n-1) n).hom
      (y : ↥((homComplex G C).X (n-1))))) ↑x = 0
    rw [homComplex_d_sub_apply]
    show (hval G C (n-1) y) ((C.d n (n-1)).hom (x : ↥(C.X n))) = 0
    rw [show (C.d n (n-1)).hom (x : ↥(C.X n)) = 0 from LinearMap.mem_ker.mp x.2, map_zero]

/-- **The middle isomorphism**: `ker δⁿ ⧸ im δⁿ⁻¹ ≅ Hom_ℤ(Zₙ ⧸ Bₙ, G)`. -/
noncomputable def uctMiddle (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ)
    [Module.Injective ℤ G] :
    (↥(LinearMap.ker ((homComplex G C).d n (n+1)).hom) ⧸ homPre G C n) ≃ₗ[ℤ]
      ((↥(Work.Cohomology.uctZ C n) ⧸ Work.Cohomology.uctH C n) →ₗ[ℤ] G) :=
  (Submodule.quotEquivOfEq (homPre G C n) (LinearMap.ker (uctPsi G C n))
      (uctPsi_ker G C n).symm).trans
    (LinearMap.quotKerEquivOfSurjective (uctPsi G C n) (uctPsi_surj G C n))

end

/-- The `n`-th cohomology of `Hom_ℤ(C, G)` computed as `ker δⁿ ⧸ im δⁿ⁻¹`, with the carriers of `C`
pinned to an explicit universe (so that the statement has no `max` in its universes). -/
lemma homology_homComplex_iso'' (G : Type) [AddCommGroup G] [Module ℤ G]
    (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (n : ℕ) :
    Nonempty ((Work.Pi6.EFACTS.homComplex G C).homology n ≅
      ModuleCat.of ℤ (↥(LinearMap.ker ((homComplex G C).d n (n+1)).hom) ⧸ homPre G C n)) :=
  ⟨((homComplex G C).homologyIsoSc' (n - 1) n (n + 1)
        (Work.Cohomology.up_prev n) (Work.Cohomology.up_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso ((homComplex G C).sc' (n - 1) n (n + 1))⟩

/-- The `k`-th cohomology of `Hom_ℤ(C, G)` is the `G`-dual of the `k`-th homology of `C`, for `G`
an injective `ℤ`-module; stated with an explicit universe for the carriers of `C`. -/
lemma homComplexInjectiveCore (G : Type) [AddCommGroup G] [Module ℤ G] [Module.Injective ℤ G]
    (C : ChainComplex (ModuleCat.{v, 0} ℤ) ℕ) (k : ℕ) :
    Nonempty ((Work.Pi6.EFACTS.homComplex G C).homology k ≅
      ModuleCat.of ℤ (↥(C.homology k) →ₗ[ℤ] G)) := by
  obtain ⟨eD⟩ := homology_homComplex_iso'' G C k
  obtain ⟨eE⟩ := Work.Cohomology.homology_iso_H C k
  refine ⟨eD ≪≫ LinearEquiv.toModuleIso (uctMiddle G C k) ≪≫ ?_⟩
  exact LinearEquiv.toModuleIso
    (precompEquiv G (Work.Cohomology.uctIsoToLinearEquiv eE))

theorem homComplexInjective (G : Type) [AddCommGroup G] [Module ℤ G] [Module.Injective ℤ G]
    (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Nonempty ((Work.Pi6.EFACTS.homComplex G C).homology k ≅
      ModuleCat.of ℤ (↥(C.homology k) →ₗ[ℤ] G)) :=
  homComplexInjectiveCore G C k

end Work.Pi6.EFACTS
