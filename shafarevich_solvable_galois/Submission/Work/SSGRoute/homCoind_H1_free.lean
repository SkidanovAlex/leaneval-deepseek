import Mathlib
import Submission.Work.SSGRoute.homCoindDefs
import Submission.Work.SSGRoute.coindU_aux
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(Ω/k), Hom_ℤ(Coeff[Gal(K/k)]^ι, Ωˣ))` is trivial

Let `k` be a field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois subextension and `ι` a
finite type.  The coefficient module
`homCoind k Ω K (Rep.free Coeff Gal(K/k) ι) = Hom_ℤ(ι →₀ Coeff[Gal(K/k)], Ωˣ)` is, as an abelian
group, the product `∏_{i ∈ ι} ∏_{g ∈ Gal(K/k)} Ωˣ`; the `Gal(Ω/k)`-action relevant for the target
statement is the pointwise one (the `AddMonoidHom` action), so `H¹` of it is the product of copies
of `H¹(Gal(Ω/k), Ωˣ)`.  The latter vanishes by Hilbert 90 (`hilbert90_isAlgClosure`), and `H¹`
commutes with finite products of coefficients (`nonempty_h1_pi_equiv`).

The additive equivalence underlying the product decomposition is `freeHomEquiv` below; it sends
`φ` to `(i, g) ↦ φ (single i (single g 1))`.
-/

open scoped Classical

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ι : Type} [Finite ι]

/-- The coordinate equivalence `(Coeff →+ A) ≃+ A` (`Coeff = ULift ℤ`, so an additive hom is
determined by its value at `1`). -/
def coeffHomEquiv : (SSGRoute.PTExt.Coeff →+ Additive Ωˣ) ≃+ Additive Ωˣ :=
  (AddEquiv.addMonoidHomCongrLeft (AddEquiv.ulift : ULift ℤ ≃+ ℤ)).trans
    ((zmultiplesAddHom (Additive Ωˣ)).symm)

theorem coeffHomEquiv_apply (h : SSGRoute.PTExt.Coeff →+ Additive Ωˣ) :
    coeffHomEquiv h = h 1 := by
  simp only [coeffHomEquiv, AddEquiv.trans_apply, AddEquiv.addMonoidHomCongrLeft_apply,
    AddMonoidHom.comp_apply, zmultiplesAddHom_symm_apply]
  rfl

/-- **The product decomposition.** The additive group
`Hom_ℤ(ι →₀ Coeff[Gal(K/k)], Ωˣ)` is the product `∏_{i ∈ ι} ∏_{g ∈ Gal(K/k)} Ωˣ`, the value of
`φ` at the pair `(i, g)` being `φ (single i (single g 1))`. -/
def freeHomEquiv :
    homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι) ≃+
      (ι → (K ≃ₐ[k] K) → Additive Ωˣ) :=
  ((Finsupp.liftAddHom (α := ι) (M := MonoidAlgebra SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
      (N := Additive Ωˣ)).symm).trans
    (AddEquiv.piCongrRight (fun _ =>
      ((AddEquiv.addMonoidHomCongrLeft
          (MonoidAlgebra.coeffAddEquiv (R := SSGRoute.PTExt.Coeff) (M := K ≃ₐ[k] K))).trans
        (((Finsupp.liftAddHom (α := K ≃ₐ[k] K) (M := SSGRoute.PTExt.Coeff)
            (N := Additive Ωˣ)).symm).trans
          (AddEquiv.piCongrRight (fun _ => coeffHomEquiv))))))

theorem freeHomEquiv_apply
    (φ : homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
    (i : ι) (g : K ≃ₐ[k] K) :
    freeHomEquiv φ i g = φ (Finsupp.single i (MonoidAlgebra.single g 1)) := by
  simp only [freeHomEquiv, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply,
    AddEquiv.addMonoidHomCongrLeft_apply, AddMonoidHom.comp_apply,
    Finsupp.liftAddHom_symm_apply, MonoidAlgebra.coeffAddEquiv_symm_apply,
    MonoidAlgebra.ofCoeff_single, Finsupp.singleAddHom_apply, coeffHomEquiv_apply]
  rfl

/-- `freeHomEquiv` is `Gal(Ω/k)`-equivariant for the pointwise action on both sides. -/
theorem freeHomEquiv_smul (σ : Ω ≃ₐ[k] Ω)
    (φ : homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) :
    freeHomEquiv (σ • φ) = σ • freeHomEquiv φ := by
  funext i g
  rw [freeHomEquiv_apply]
  rw [show (σ • freeHomEquiv φ) i g = σ • (freeHomEquiv φ i g) from rfl]
  rw [freeHomEquiv_apply]
  rfl

/-! ## Hilbert 90 in cohomological form -/

/-- **Hilbert 90.** `H¹(Gal(Ω/k), Ωˣ) = 0` for `Ω` an algebraic closure of `k`. -/
theorem subsingleton_H1_addUnitsΩ :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Additive Ωˣ) F from hF.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
  obtain ⟨hcross, hloc⟩ := (Work.AbsoluteKummer.mem_Z1_iff _).mp F.2
  have humap : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      Work.SSGRoute.umap k Ω σ u = algEquivUnitsMapΩ k Ω σ u :=
    fun σ u => Units.ext (by rw [Work.SSGRoute.umap_coe, algEquivUnitsMapΩ_coe])
  have hcross' : ∀ σ τ : Ω ≃ₐ[k] Ω,
      Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) (σ * τ))
        = Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)
          * Work.SSGRoute.umap k Ω σ (Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) τ)) := by
    intro σ τ
    have h := congrArg Additive.toMul (hcross σ τ)
    simp only [toMul_add, addUnits_smul_toMulΩ] at h
    rw [h, ← humap σ (Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) τ)), mul_comm]
  have hloc' : Work.AbsoluteKummer.IsLocallyConstant
      (fun σ : Ω ≃ₐ[k] Ω => Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)) :=
    Work.AbsoluteKummer.IsLocallyConstant.map Additive.toMul hloc
  obtain ⟨b, hb⟩ := hilbert90_isAlgClosure (k := k) (Ω := Ω)
    (fun σ : Ω ≃ₐ[k] Ω => Additive.toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)) hcross' hloc'
  refine ⟨Additive.ofMul b, ?_⟩
  funext σ
  rw [Work.GroupCohomology.d0_apply]
  have hb' : (F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ
      = Additive.ofMul (Work.SSGRoute.umap k Ω σ b / b) := by
    rw [← ofMul_toMul ((F : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ), hb σ]
  have hsmul : σ • Additive.ofMul b = Additive.ofMul (Work.SSGRoute.umap k Ω σ b) := by
    show Additive.ofMul (algEquivUnitsMapΩ k Ω σ b)
        = Additive.ofMul (Work.SSGRoute.umap k Ω σ b)
    rw [humap σ b]
  rw [hb', hsmul, ofMul_div]

/-! ## Transfers -/

/-- `H¹` of a finite product of coefficient modules is the product of the `H¹`'s, so it is a
subsingleton as soon as each factor is. -/
theorem subsingleton_H1_pi {Γ : Type*} [TopologicalSpace Γ] [Group Γ]
    {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, AddCommGroup (X i)]
    [∀ i, DistribMulAction Γ (X i)]
    (h : ∀ i, Subsingleton (Work.AbsoluteKummer.H1 Γ (X i))) :
    Subsingleton (Work.AbsoluteKummer.H1 Γ (∀ i, X i)) := by
  obtain ⟨e⟩ := Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv (G := Γ) X
  exact ⟨fun x y => e.injective (funext fun i => (h i).elim (e x i) (e y i))⟩

/-- If `e : M ≃+ N` is `G`-equivariant and `H¹(G,N)` is a subsingleton, then so is `H¹(G,M)`. -/
theorem subsingleton_H1_of_addEquiv {G : Type*} [TopologicalSpace G] [Group G]
    {M N : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup N] [DistribMulAction G N]
    (e : M ≃+ N) (he : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (hN : Subsingleton (Work.AbsoluteKummer.H1 G N)) :
    Subsingleton (Work.AbsoluteKummer.H1 G M) := by
  haveI : Subsingleton (Work.AbsoluteKummer.H1 G N) := hN
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 G M).comap (Work.AbsoluteKummer.Z1 G M).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π G M F from hF.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
  obtain ⟨hc, hl⟩ := (Work.AbsoluteKummer.mem_Z1_iff _).mp F.2
  have hF' : (fun g => e ((F : G → M) g)) ∈ Work.AbsoluteKummer.Z1 G N := by
    rw [Work.AbsoluteKummer.mem_Z1_iff]
    refine ⟨?_, Work.AbsoluteKummer.IsLocallyConstant.map e hl⟩
    intro g h
    show e ((F : G → M) (g * h)) = g • e ((F : G → M) h) + e ((F : G → M) g)
    rw [hc g h, map_add, he]
  have hz : Work.AbsoluteKummer.H1π G N
      ⟨(fun g => e ((F : G → M) g)), hF'⟩ = 0 := Subsingleton.elim _ _
  rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨e.symm a, ?_⟩
  have hev : ∀ (g : G) (n : N), e.symm (g • n) = g • e.symm n := by
    intro g n
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  funext g
  rw [Work.GroupCohomology.d0_apply]
  have h2 : g • a - a = e ((F : G → M) g) := by
    have h := congrFun ha g
    simpa only [Work.GroupCohomology.d0_apply] using h
  have h4 : e.symm (g • a - a) = (F : G → M) g := by
    rw [congrArg e.symm h2, e.symm_apply_apply]
  rw [map_sub, hev] at h4
  exact h4

end

theorem homCoind_H1_free {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {ι : Type} [Finite ι] :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  have hA : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)) :=
    subsingleton_H1_addUnitsΩ
  have hGA : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      ((K ≃ₐ[k] K) → Additive Ωˣ)) :=
    subsingleton_H1_pi (fun _ : K ≃ₐ[k] K => hA)
  have hιGA : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (ι → (K ≃ₐ[k] K) → Additive Ωˣ)) :=
    subsingleton_H1_pi (fun _ : ι => hGA)
  exact subsingleton_H1_of_addEquiv freeHomEquiv (fun σ φ => freeHomEquiv_smul σ φ) hιGA

end Work.SSGRoute
