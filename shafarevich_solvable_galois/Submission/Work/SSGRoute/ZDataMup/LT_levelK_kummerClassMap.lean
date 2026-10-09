import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.toClass_apply_congr
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.finite_H1loc_inertia_free
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
import Submission.Work.SSGRoute.ZConstruction.local_class_has_global_representative
import Submission.Work.SSGRoute.ZConstruction.localKummerHom
import Submission.Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class map of the level-`K` local Kummer character

The level-`K` local Kummer map sends a global unit `β ∈ Kˣ` to the class in
`H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)` of the locally constant `1`-cocycle

  `σ ↦ χ_β(σ)`  (`σ ∈ D_A ⊓ G_K`),

where `χ_β` is the Kummer character of `β` at the finite place `A` (`kummerCharHom`, i.e. the
element of `↥(lcHoms p ↥(decomp ↥K A))` classified by the local Kummer dictionary).  Because the
coefficient module is trivial on `G_K`, the coboundaries at `H = decomp k A ⊓ K.fixingSubgroup` are
exactly the functions vanishing on `H` (`isCoboundaryOn_iff_forall_eq_zero`), so the class of a
cocycle is determined by its restriction to `H` (`toClass_eq_iff_forall_eq`).

The resulting map `Ψ : Kˣ → H1loc …` is

* additive (`Ψ (β β') = Ψ β + Ψ β'`),
* with kernel exactly the local `p`-th powers (`NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1`),
* and hits the class of every locally constant cocycle on `G_K` (via the surjectivity of the
  Kummer character map `β ↦ χ_β` on `↥(lcHoms p ↥(decomp ↥K A))`).
-/

namespace Work.SSGRoute.ZDataMup

open Classical
open scoped Pointwise

section Helpers

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- On a subgroup of `G_K = K.fixingSubgroup` the restriction `res k K` is trivial. -/
lemma res_eq_one_of_le_fixingSubgroup (hH : H ≤ K.fixingSubgroup)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ H) : SSGRoute.res k K g = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (E := K)]
  exact hH hg

/-- On a subgroup of `G_K`, the `1`-coboundaries are exactly the functions vanishing on `H`. -/
lemma isCoboundaryOn_iff_forall_eq_zero (hH : H ≤ K.fixingSubgroup)
    (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f ↔ ∀ g ∈ H, f g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    rw [hm g hg, res_eq_one_of_le_fixingSubgroup hH hg, one_smul, sub_self]
  · intro h
    exact ⟨0, fun g hg => by rw [h g hg, smul_zero, sub_zero]⟩

/-- The class of a locally constant cocycle on `H ≤ G_K` is zero iff the cocycle vanishes on
`H`. -/
lemma toClass_eq_zero_iff_forall_eq_zero (hH : H ≤ K.fixingSubgroup)
    {f : (Ω ≃ₐ[k] Ω) → ZMod p} (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H) :
    Work.SSGRoute.toClass p k Ω K (ZMod p) H f = 0 ↔ ∀ g ∈ H, f g = 0 := by
  rw [Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p) H hf,
    Work.SSGRoute.mem_coboundaries, isCoboundaryOn_iff_forall_eq_zero hH]

/-- Two locally constant cocycles on `H ≤ G_K` have the same class iff they agree on `H`. -/
lemma toClass_eq_iff_forall_eq (hH : H ≤ K.fixingSubgroup)
    {f f' : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)
    (hf' : f' ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H) :
    Work.SSGRoute.toClass p k Ω K (ZMod p) H f =
        Work.SSGRoute.toClass p k Ω K (ZMod p) H f' ↔
      ∀ g ∈ H, f g = f' g := by
  constructor
  · intro h g hg
    exact Work.SSGRoute.LTDDefs.toClass_apply_congr p k Ω K H hH hf hf' h g hg
  · intro h
    have hcob : f - f' ∈ Work.SSGRoute.coboundaries p k Ω K (ZMod p) H := by
      rw [Work.SSGRoute.mem_coboundaries]
      refine (isCoboundaryOn_iff_forall_eq_zero hH _).mpr fun g hg => ?_
      show f g - f' g = 0
      rw [h g hg, sub_self]
    have hsub : f - f' ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H :=
      Submodule.sub_mem _ hf hf'
    rw [Work.SSGRoute.toClass, dif_pos hf, Work.SSGRoute.toClass, dif_pos hf',
      Submodule.mkQ_apply, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.mem_comap]
    have hsub' : (⟨f, hf⟩ - ⟨f', hf'⟩ : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)) =
        ⟨f - f', hsub⟩ := Subtype.ext rfl
    rw [hsub']
    exact hcob

/-- Local constancy transfers from `IsLocConstOn` on a subgroup to the subgroup itself. -/
lemma isLocallyConstant_restrict_of_isLocConstOn {H : Subgroup (Ω ≃ₐ[k] Ω)}
    {f : (Ω ≃ₐ[k] Ω) → ZMod p} (hf : SSGRoute.IsLocConstOn H f) :
    _root_.IsLocallyConstant (fun h : ↥H => f (h : Ω ≃ₐ[k] Ω)) := by
  obtain ⟨U, hUo, hU⟩ := hf
  rw [_root_.IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y : ↥H => (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)),
    hUo.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
  · show (x : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  · intro y hy
    show f (y : Ω ≃ₐ[k] Ω) = f (x : Ω ≃ₐ[k] Ω)
    have hyH : (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.2) y.2
    have hthis := hU (x : Ω ≃ₐ[k] Ω) x.2 ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) hy hyH
    have hxy : (x : Ω ≃ₐ[k] Ω) * ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) =
        (y : Ω ≃ₐ[k] Ω) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [← hxy, hthis]

end Helpers

section ProperSubring

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A prime-adic valuation subring is a proper subring: `A.comap` along the structure map of a
completion is never all of the field. -/
lemma valuationSubringAtPrime_ne_top (𝔭 : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ≠ ⊤ := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

end ProperSubring

section Extend

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- The additive character of `H = decomp k A ⊓ K.fixingSubgroup` attached to a locally constant
character of the level-`K` local group `↥(decomp ↥K A)`. -/
noncomputable def lcHomsToH (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ZMod p :=
  fun g => (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd

lemma lcHomsToH_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    lcHomsToH A χ g = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd := rfl

/-- The additive character attached to a locally constant character is a locally constant additive
`1`-cocycle on `H` (for the action through `res k K`, trivial on `H`). -/
lemma lcHomsToH_mem_Z1 (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsToH A χ ∈
      Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p) := by
  rw [Work.AbsoluteKummer.mem_Z1_iff]
  constructor
  · intro g h
    show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A (g * h))).toAdd =
      g • (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd +
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd
    rw [map_mul (Work.SSGRoute.decompEquiv_fok k Ω K A), map_mul, toAdd_mul]
    have h2 : g • (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd =
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd := by
      rw [hcompat g, res_eq_one_of_le_fixingSubgroup (H := _) inf_le_right g.2, one_smul]
    rw [h2]
    abel
  · intro x
    have hχloc : _root_.IsLocallyConstant
        (χ.1 : ↥(SSGRoute.decomp (k := ↥K) A) → Multiplicative (ZMod p)) := χ.2
    obtain ⟨V, hVo, hxV, hV⟩ := hχloc.exists_open (Work.SSGRoute.decompEquiv_fok k Ω K A x)
    exact ⟨(Work.SSGRoute.decompEquiv_fok k Ω K A) ⁻¹' V,
      hVo.preimage (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).continuous,
      hxV, fun y hy => by
        show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A y)).toAdd =
          (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A x)).toAdd
        rw [hV (Work.SSGRoute.decompEquiv_fok k Ω K A y) hy]⟩

/-- Extension by `0` off `H` of the additive character `lcHomsToH A χ`. -/
noncomputable def lcHomsExtend (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    (Ω ≃ₐ[k] Ω) → ZMod p :=
  (extendCocycle p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hcompat
    ⟨lcHomsToH A χ, lcHomsToH_mem_Z1 A hcompat χ⟩).1

lemma lcHomsExtend_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : Ω ≃ₐ[k] Ω) :
    lcHomsExtend A hcompat χ g =
      if hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup then
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)).toAdd else 0 := rfl

/-- The value of the extension on `H`. -/
lemma lcHomsExtend_apply_of_mem (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup) :
    lcHomsExtend A hcompat χ g =
      (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)).toAdd := by
  rw [lcHomsExtend_apply, dif_pos hg]

/-- The extension is a locally constant `1`-cocycle on `H`. -/
lemma lcHomsExtend_mem (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsExtend A hcompat χ ∈
      Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
  (extendCocycle p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hcompat
    ⟨lcHomsToH A χ, lcHomsToH_mem_Z1 A hcompat χ⟩).2

/-- The extension is additive in the character. -/
lemma lcHomsExtend_add_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ χ' : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : Ω ≃ₐ[k] Ω) :
    lcHomsExtend A hcompat (χ * χ') g =
      lcHomsExtend A hcompat χ g + lcHomsExtend A hcompat χ' g := by
  rw [lcHomsExtend_apply, lcHomsExtend_apply, lcHomsExtend_apply]
  by_cases hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup
  · rw [dif_pos hg, dif_pos hg, dif_pos hg]
    have h1 : (χ * χ').1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) =
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) *
          χ'.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) := by
      rw [Subgroup.coe_mul, MonoidHom.mul_apply]
    rw [h1, toAdd_mul]
  · rw [dif_neg hg, dif_neg hg, dif_neg hg, add_zero]

/-- The extension vanishes on `H` iff the character is trivial. -/
lemma lcHomsExtend_eq_zero_iff (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    (∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, lcHomsExtend A hcompat χ g = 0) ↔ χ = 1 := by
  constructor
  · intro h
    refine Subtype.ext (MonoidHom.ext fun y => ?_)
    have h1 : lcHomsExtend A hcompat χ
        ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y) = 0 := h _ ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2
    rw [lcHomsExtend_apply, dif_pos ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2] at h1
    have h2 : (Work.SSGRoute.decompEquiv_fok k Ω K A)
        ⟨(Work.SSGRoute.decompEquiv_fok k Ω K A).symm y,
          ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2⟩ = y :=
      MulEquiv.apply_symm_apply _ y
    rw [h2] at h1
    show χ.1 y = (1 : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))).1 y
    have h3 : χ.1 y = Multiplicative.ofAdd (0 : ZMod p) := by
      calc χ.1 y = Multiplicative.ofAdd (χ.1 y).toAdd := (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd 0 := by rw [h1]
    simpa using h3
  · intro h g hg
    rw [lcHomsExtend_apply, dif_pos hg]
    have h1 : χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) = 1 := by rw [h]; rfl
    rw [h1]
    rfl

/-- The level-`K` local group at a place `A` of `Ω`. -/
abbrev kLevelLocalGroup (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

end Extend

section ExtendAdditivity

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- The extension is additive in the character (function form). -/
lemma lcHomsExtend_add (A : ValuationSubring Ω)
    [DistribMulAction ↥(kLevelLocalGroup k Ω K A) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(kLevelLocalGroup k Ω K A)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ χ' : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsExtend A hcompat (χ * χ') =
      lcHomsExtend A hcompat χ + lcHomsExtend A hcompat χ' :=
  funext fun g => lcHomsExtend_add_apply A hcompat χ χ' g

end ExtendAdditivity

section Target

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **Surjectivity of the Kummer character map** (the level-`K` local Kummer isomorphism in
character form): every locally constant character of the level-`K` local group is the Kummer
character of a global unit. -/
theorem kummerCharMonoidHom_surjective_aux [IsAlgClosed Ω] [NumberField ↥K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    Function.Surjective
      (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA) := by
  classical
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- `A` is a finite place of `Ω` over `↥K` as well
  have hAK : SSGRoute.IsFinPlace ↥K A := by
    show A.comap (algebraMap ↥K Ω) ≠ ⊤
    rw [h𝔭]
    intro h
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (K := ↥K)] at h
    exact (Valuation.valuationSubring_eq_top_iff _).mp h inferInstance
  -- the prime of `K` below `A` is `𝔭`
  have hprime : 𝔭 = Submission.NeukirchUchida.primeOf A hAK := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K) ?_
    rw [← h𝔭]
    exact Submission.NeukirchUchida.primeOf_spec A hAK
  -- the descent `Kˣ ⧸ ker ρ →* lcHoms` is injective ...
  have hinj := Work.SSGRoute.ZConstruction.kummerCharLift_injective (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭
  -- ... between finite groups of the same cardinality
  haveI hfinκ : Finite (((𝔭.adicCompletion ↥K)ˣ ⧸
      (powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range)) :=
    Work.SSGRoute.finite_powClass_localField _ p Fact.out
  haveI hfinD : Finite (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) :=
    Finite.of_equiv (((𝔭.adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range))
      (Work.SSGRoute.ZConstruction.quotientKerLocalPowClassEquiv (p := p) (K := K) 𝔭).symm.toEquiv
  haveI hfinL : Finite ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω)
      (K := K) (A := A) hA hAK hAK
  haveI hFintypeD : Fintype (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) :=
    Fintype.ofFinite _
  haveI hFintypeL : Fintype ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Fintype.ofFinite _
  have hcard : Nat.card (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) =
      Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := by
    rw [Nat.card_congr (Work.SSGRoute.ZConstruction.quotientKerLocalPowClassEquiv
      (p := p) (K := K) 𝔭).toEquiv,
      Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup (p := p) (k := k)
        (Ω := Ω) (K := K) A hA hAK hAK, hprime]
  have hsurj : Function.Bijective (Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k)
      (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭) :=
    (Fintype.bijective_iff_injective_and_card
      (Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭)).mpr
      ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩
  -- consequently the Kummer character map `β ↦ χ_β` is surjective
  intro χ
  obtain ⟨q, hq⟩ := hsurj.2 χ
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective
    (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) q
  refine ⟨β, ?_⟩
  rw [← Work.SSGRoute.ZConstruction.kummerCharLift_mk (p := p) (k := k) (Ω := Ω) (K := K)
    (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭 β]
  exact hq

/-- **The character of a cocycle on `G_K`**: restricting a locally constant `1`-cocycle on
`K.fixingSubgroup` to `H = decomp k A ⊓ K.fixingSubgroup` and transporting along
`decompEquiv_fok` gives a locally constant character of the level-`K` local group. -/
theorem exists_lcHoms_of_cocycle_aux
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup) :
    ∃ χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)),
      ∀ g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) = Multiplicative.ofAdd (a g) := by
  classical
  have hHle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
  -- on `H` the action is trivial, so the cocycle condition is additivity
  have hcyc : SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a :=
    fun g hg h hh => ha.1 g (hHle hg) h (hHle hh)
  have hlocOn : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a :=
    let ⟨U, hUo, hU⟩ := ha.2
    ⟨U, hUo, fun g hg u hu huH => hU g (hHle hg) u hu (hHle huH)⟩
  have hadd : ∀ g h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      a ((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) =
        a (g : Ω ≃ₐ[k] Ω) + a (h : Ω ≃ₐ[k] Ω) := by
    intro g h
    have h1 := hcyc (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
    rw [res_eq_one_of_le_fixingSubgroup hHle g.2, one_smul] at h1
    exact h1
  have hone : a (1 : Ω ≃ₐ[k] Ω) = 0 := by
    have h1 : a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) := by
      have h := hadd 1 1
      simpa using h
    have h2 : a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  have hloc0 : _root_.IsLocallyConstant
      (fun g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) => a (g : Ω ≃ₐ[k] Ω)) :=
    isLocallyConstant_restrict_of_isLocConstOn hlocOn
  -- the character of `↥H` defined by `a`
  let ψ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative (ZMod p) :=
    { toFun := fun g => Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω))
      map_one' := by
        show Multiplicative.ofAdd (a (1 : Ω ≃ₐ[k] Ω)) = 1
        rw [hone]
        rfl
      map_mul' := by
        intro g h
        show Multiplicative.ofAdd (a ((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
            Ω ≃ₐ[k] Ω)) =
          Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) *
            Multiplicative.ofAdd (a (h : Ω ≃ₐ[k] Ω))
        rw [hadd, ofAdd_add] }
  have hψloc : _root_.IsLocallyConstant ψ := hloc0.comp Multiplicative.ofAdd
  -- transport along `decompEquiv_fok : H ≃* decomp ↥K A`
  have hsymm : Continuous ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm :
      ↥(SSGRoute.decomp (k := ↥K) A) → ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    (Work.SSGRoute.decompEquiv_fok k Ω K A).toEquiv.continuous_symm_iff.2
      (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).isOpenMap
  refine ⟨⟨ψ.comp (Work.SSGRoute.decompEquiv_fok k Ω K A).symm.toMonoidHom, ?_⟩, ?_⟩
  · exact hψloc.comp_continuous hsymm
  · intro g
    show ψ ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm
      (Work.SSGRoute.decompEquiv_fok k Ω K A g)) = Multiplicative.ofAdd (a g)
    rw [MulEquiv.symm_apply_apply]
    rfl

end Target

theorem LT_levelK_kummerClassMap
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    ∃ Ψ : Kˣ → Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      (∀ β β' : Kˣ, Ψ (β * β') = Ψ β + Ψ β') ∧
      (∀ β : Kˣ, Ψ β = 0 ↔ NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1) ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → ZMod p),
        a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup →
        ∃ β : Kˣ, Ψ β = Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) := by
  classical
  haveI hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- the action of the level-`K` local group on the coefficients, through `res`
  letI : DistribMulAction ↥(kLevelLocalGroup k Ω K A) (ZMod p) :=
    Work.SSGRoute.subgroupDistribMulAction k Ω K (ZMod p) (kLevelLocalGroup k Ω K A)
  have hcompat : ∀ (h : ↥(kLevelLocalGroup k Ω K A)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := fun _ _ => rfl
  have hle : kLevelLocalGroup k Ω K A ≤ K.fixingSubgroup := inf_le_right
  -- a primitive `p`-th root of unity in `↥K`
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (ζ := ⟨ζ, hζK⟩)
      (by simpa using hζ) (algebraMap ↥K Ω).injective
  refine ⟨fun β => Work.SSGRoute.toClass p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A)
      (lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
        (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β)), ?_, ?_, ?_⟩
  · intro β β'
    have hfun : lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom
          (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA
          (β * β')) =
        lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
          (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β) +
        lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
          (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β') := by
      rw [map_mul, lcHomsExtend_add]
    simp only [hfun]
    refine Work.SSGRoute.toClass_add p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) ?_ ?_
    · exact lcHomsExtend_mem A hcompat _
    · exact lcHomsExtend_mem A hcompat _
  · intro β
    have hmem : lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom
        (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β) ∈
        Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) :=
      lcHomsExtend_mem A hcompat _
    rw [toClass_eq_zero_iff_forall_eq_zero hle hmem]
    rw [lcHomsExtend_eq_zero_iff A hcompat]
    exact Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (k := k)
      (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA 𝔭 h𝔭 β
  · intro a ha
    have haH : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) :=
      ⟨fun g hg h hh => ha.1 g (hle hg) h (hle hh),
        (let ⟨U, hUo, hU⟩ := ha.2
         ⟨U, hUo, fun g hg u hu huH => hU g (hle hg) u hu (hle huH)⟩)⟩
    obtain ⟨χ, hχ⟩ := exists_lcHoms_of_cocycle_aux (p := p) (k := k) (Ω := Ω) (K := K) A hA a ha
    obtain ⟨β, hβ⟩ := kummerCharMonoidHom_surjective_aux (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ⟨ζ, hζK⟩) (hζ := hζK') A hA 𝔭 h𝔭 χ
    refine ⟨β, ?_⟩
    refine (toClass_eq_iff_forall_eq hle (lcHomsExtend_mem A hcompat _) haH).mpr ?_
    intro g hg
    rw [lcHomsExtend_apply_of_mem A hcompat _ hg, hβ]
    rw [hχ ⟨g, hg⟩]
    rfl

end Work.SSGRoute.ZDataMup
