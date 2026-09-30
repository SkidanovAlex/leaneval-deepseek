import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.covolume_isometry_map_volume
import Submission.Work.BW.covolume_prod
import Submission.Work.BW.covolume_comap_linearEquiv
import Submission.Work.BW.covolume_prodEquivOfIsCompl_measurePreserving

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Work.BW

open MeasureTheory

/-- For a linear isomorphism `T` between finite-dimensional real inner product spaces,
the two composites of the adjoint with `T` have the same determinant. -/
theorem det_adjoint_comp_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E ≃L[ℝ] F) :
    LinearMap.det (((T : E →L[ℝ] F).comp (T : E →L[ℝ] F).adjoint : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      LinearMap.det (((T : E →L[ℝ] F).adjoint.comp (T : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [← LinearMap.det_conj
    (f := (((T : E →L[ℝ] F).adjoint.comp (T : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (e := (T : E ≃ₗ[ℝ] F))]
  congr 1
  ext x
  simp [LinearMap.comp_apply]

theorem covolume_kernel_mul_image_aux {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
    (f : V →L[ℝ] W) (hf : Function.Surjective f)
    (K : Submodule ℝ V) (hK : K = LinearMap.ker (f : V →ₗ[ℝ] W))
    (L : Submodule ℤ V) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    (Λ : Submodule ℤ ↥K) (hΛ : ∀ x : ↥K, x ∈ Λ ↔ (x : V) ∈ L)
    [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ]
    (M : Submodule ℤ W) (hM : ∀ y : W, y ∈ M ↔ ∃ x ∈ L, f x = y)
    [DiscreteTopology ↥M] [IsZLattice ℝ M] :
    ZLattice.covolume Λ MeasureTheory.volume * ZLattice.covolume M MeasureTheory.volume
      = ZLattice.covolume L MeasureTheory.volume *
        Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  have hmemK : ∀ x : V, x ∈ K ↔ f x = 0 := by
    intro x
    rw [hK, LinearMap.mem_ker]
    rfl
  -- A : the restriction of `f` to `Kᗮ`
  have hkerA : (f.comp Kᗮ.subtypeL).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx1 : (x : V) ∈ K := (hmemK _).mpr (by simpa using LinearMap.mem_ker.mp hx)
    have hx2 : (x : V) ∈ K ⊓ Kᗮ := ⟨hx1, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hx2
    simpa using hx2
  have hrangeA : (f.comp Kᗮ.subtypeL).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨v, hv⟩ := hf w
    obtain ⟨κ, hκ, p, hp, hvp⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) v
    refine ⟨⟨p, hp⟩, ?_⟩
    have hκ0 : f κ = 0 := (hmemK κ).mp hκ
    show (f.comp Kᗮ.subtypeL) ⟨p, hp⟩ = w
    rw [← hv, hvp, map_add, hκ0, zero_add]
    rfl
  let Ae : ↥(Kᗮ) ≃L[ℝ] W := ContinuousLinearEquiv.ofBijective (f.comp Kᗮ.subtypeL) hkerA hrangeA
  have hAefn : ∀ y : ↥(Kᗮ), Ae y = f (y : V) := by
    intro y
    rw [show Ae = ContinuousLinearEquiv.ofBijective (f.comp Kᗮ.subtypeL) hkerA hrangeA from rfl,
      ContinuousLinearEquiv.coeFn_ofBijective]
    rfl
  have hAAc : ((Ae : ↥(Kᗮ) →L[ℝ] W).comp (Ae : ↥(Kᗮ) →L[ℝ] W).adjoint : W →L[ℝ] W)
      = (f.comp f.adjoint : W →L[ℝ] W) := by
    have h1 : (Ae : ↥(Kᗮ) →L[ℝ] W) = f.comp Kᗮ.subtypeL :=
      ContinuousLinearEquiv.coe_ofBijective ..
    rw [h1, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    ext w
    have hmem : (f.adjoint w : V) ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [ContinuousLinearMap.adjoint_inner_right, (hmemK u).mp hu, inner_zero_left]
    have hproj : ((Kᗮ).subtypeL ((Kᗮ).orthogonalProjectionOnto (f.adjoint w)) : V)
        = (f.adjoint w : V) :=
      congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := Kᗮ)
        (v := (⟨(f.adjoint w : V), hmem⟩ : ↥(Kᗮ))))
    show f ((Kᗮ).subtypeL ((Kᗮ).orthogonalProjectionOnto (f.adjoint w))) = f (f.adjoint w)
    rw [hproj]
  have hAA : (((Ae : ↥(Kᗮ) →L[ℝ] W).comp (Ae : ↥(Kᗮ) →L[ℝ] W).adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)
      = ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W) := by
    rw [hAAc]
  -- the product lattice
  let Θ : (↥K × ↥(Kᗮ)) ≃L[ℝ] V :=
    (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).toContinuousLinearEquiv
  let L' : Submodule ℤ (↥K × ↥(Kᗮ)) := ZLattice.comap ℝ L Θ.toLinearMap
  let M' : Submodule ℤ ↥(Kᗮ) := ZLattice.comap ℝ M Ae.toLinearMap
  have hΘapply : ∀ x : ↥K × ↥(Kᗮ), Θ x = (x.1 : V) + (x.2 : V) := by
    intro x
    simp [Θ, Submodule.coe_prodEquivOfIsCompl']
  have hΛ' : ∀ x : ↥K, x ∈ Λ ↔ (x, 0) ∈ L' := by
    intro x
    rw [hΛ x]
    show (x : V) ∈ L ↔ Θ (x, 0) ∈ L
    rw [hΘapply]
    simp
  have hM' : ∀ y : ↥(Kᗮ), y ∈ M' ↔ ∃ x : ↥K, (x, y) ∈ L' := by
    intro y
    have hM'eq : y ∈ M' ↔ Ae y ∈ M := by
      have h := (Submodule.mem_comap (p := M)
        (f := (Ae.toLinearMap.restrictScalars ℤ)) (x := y))
      exact h
    rw [hM'eq, hM]
    constructor
    · rintro ⟨v, hvL, hfv⟩
      obtain ⟨κ, hκ, p, hp, hvp⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) v
      have hpy : (⟨p, hp⟩ : ↥(Kᗮ)) = y := by
        apply Ae.injective
        rw [hAefn, ← hfv, hvp, map_add, (hmemK κ).mp hκ, zero_add]
      refine ⟨⟨κ, hκ⟩, ?_⟩
      show Θ ((⟨κ, hκ⟩ : ↥K), y) ∈ L
      rw [hΘapply]
      rw [show ((⟨κ, hκ⟩ : ↥K) : V) + (y : V) = v from by rw [hvp, ← congrArg Subtype.val hpy]]
      exact hvL
    · rintro ⟨x, hx⟩
      have hxL : Θ (x, y) ∈ L := hx
      refine ⟨Θ (x, y), hxL, ?_⟩
      rw [hΘapply, map_add, (hmemK (x : V)).mp x.2, zero_add]
      exact (hAefn y).symm
  haveI : Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure (↥K × ↥(Kᗮ))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  have hprod : ZLattice.covolume L' MeasureTheory.volume
      = ZLattice.covolume Λ MeasureTheory.volume * ZLattice.covolume M' MeasureTheory.volume :=
    covolume_prod L' Λ hΛ' M' hM'
  have hMP : MeasureTheory.MeasurePreserving Θ MeasureTheory.volume MeasureTheory.volume := by
    have h := covolume_prodEquivOfIsCompl_measurePreserving K K.isCompl_orthogonal
    simpa [Θ, LinearEquiv.coe_toContinuousLinearEquiv] using h
  have htrans : ZLattice.covolume L' MeasureTheory.volume
      = ZLattice.covolume L MeasureTheory.volume :=
    ZLattice.covolume_comap (L := L) (μ := (MeasureTheory.volume : MeasureTheory.Measure V))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (↥K × ↥(Kᗮ)))) (e := Θ) hMP
  have hscale := covolume_comap_linearEquiv Ae M
  have hdet : LinearMap.det (((Ae : ↥(Kᗮ) →L[ℝ] W).adjoint.comp (Ae : ↥(Kᗮ) →L[ℝ] W)
        : ↥(Kᗮ) →L[ℝ] ↥(Kᗮ)) : ↥(Kᗮ) →ₗ[ℝ] ↥(Kᗮ))
      = LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W) := by
    rw [← det_adjoint_comp_eq Ae]
    exact congrArg (fun g => LinearMap.det (g : W →ₗ[ℝ] W)) hAA
  have hscale' : ZLattice.covolume M' MeasureTheory.volume *
      Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W))
      = ZLattice.covolume M MeasureTheory.volume := by
    rw [← hdet]
    exact hscale
  calc ZLattice.covolume Λ MeasureTheory.volume * ZLattice.covolume M MeasureTheory.volume
      = ZLattice.covolume Λ MeasureTheory.volume *
          (ZLattice.covolume M' MeasureTheory.volume *
            Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W))) := by
        rw [hscale']
    _ = (ZLattice.covolume Λ MeasureTheory.volume * ZLattice.covolume M' MeasureTheory.volume) *
          Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by ring
    _ = ZLattice.covolume L' MeasureTheory.volume *
          Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by
        rw [hprod]
    _ = ZLattice.covolume L MeasureTheory.volume *
          Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by
        rw [htrans]

/-- **Kernel-lattice covolume (duality).**

Let `V`, `W` be finite-dimensional real inner product spaces, `f : V →L[ℝ] W` surjective with kernel
`K`, `L ⊆ V` a ℤ-lattice, `Λ = L ∩ K` (assumed to *span* `K` over `ℝ`, i.e. "rational with respect
to `K`" — this is exactly the `IsZLattice ℝ Λ` instance below) and `M = f '' L`.  Then

  `covol(Λ) · covol(M) = covol(L) · √det(f ∘ f†)`,

where `f†` is the adjoint of `f`; `√det(f ∘ f†)` is the Jacobian of `f` on `(ker f)ᵖᵉʳᵖ`, i.e. the
ℓ² coarea constant.  All three covolumes are those of the *Lebesgue* (Haar) measures of the inner
product structures: this is what makes the identity true, and it is precisely where the earlier
attempt at this statement (`BW/covolumeKernel`, declared FALSE) went wrong — the kernel must be
measured with the ℓ² structure inherited from `V`, which is why `e` below is an isometry from
`EuclideanSpace ℝ (Fin k)` onto `↥K`, so that `Measure.map e volume` is the Lebesgue measure of `K`
inherited from `V` (not the sup-norm normalisation).  The two default measures are the canonical
inner-product Haar measures (`MeasureTheory.volume`).

Proof: take a ℤ-basis `λ₁,…,λ_k` of `Λ` and lifts `v₁,…,v_m ∈ L` whose `f`-images form a ℤ-basis of
`M`; the exact sequence `0 → Λ → L → M → 0` splits (`M` is free), so `(λ, v)` is a ℤ-basis of `L`;
in orthonormal coordinates adapted to `V = K ⊕ Kᵖᵉʳᵖ` its coordinate matrix is block upper
triangular, and `det = det(K-part) · det(Kᵖᵉʳᵖ-part)` is the identity.  Usable interfaces:
`Real.sqrt (B.det)` (the Gram determinant) for an explicit matrix, `ZLattice.covolume_eq_measure_fundamentalDomain`
to compute `covol(L)` and `covol(M)`. -/
theorem covolume_kernel_mul_image {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
    (f : V →L[ℝ] W) (hf : Function.Surjective f) {k : ℕ}
    (e : EuclideanSpace ℝ (Fin k) ≃ᵢ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)))
    (L : Submodule ℤ V) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    (Λ : Submodule ℤ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)))
    (hΛ : ∀ x : ↥(LinearMap.ker (f : V →ₗ[ℝ] W)), x ∈ Λ ↔ (x : V) ∈ L)
    [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ]
    (M : Submodule ℤ W) (hM : ∀ y : W, y ∈ M ↔ ∃ x ∈ L, f x = y)
    [DiscreteTopology ↥M] [IsZLattice ℝ M] :
    ZLattice.covolume Λ (MeasureTheory.Measure.map e MeasureTheory.volume) * ZLattice.covolume M
      = ZLattice.covolume L *
        Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by
  rw [covolume_isometry_map_volume e]
  exact covolume_kernel_mul_image_aux f hf (LinearMap.ker (f : V →ₗ[ℝ] W)) rfl L Λ hΛ M hM

end Work.BW
