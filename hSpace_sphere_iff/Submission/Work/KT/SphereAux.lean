import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.SphereSetup

/-!
# Auxiliary lemmas for `sphere_K`

Basic facts about the algebraic `K₀` of `Defs.lean`, the algebra isomorphism `C(Y) ≅ C(X)` induced
by a homeomorphism `X ≃ₜ Y`, and the "radial normalisation" homeomorphism
`Sph V ≃ₜ Sph W` induced by a linear equivalence `V ≃ₗ[ℝ] W`.
-/

namespace Work.KT

noncomputable section

open Matrix

/-! ## Elementary `K₀` facts -/

section K0basic

variable {R S : Type}

/-- The block-sum relation in `K₀`. -/
lemma sphKT_cls_sum [Ring R] {p q : Mat R} (hp : Mat.IsIdem p) (hq : Mat.IsIdem q) :
    cls (Mat.sum p q) = cls p + cls q := by
  have hmem : FreeAbelianGroup.of (Mat.sum p q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q
      ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inl ⟨p, q, hp, hq, rfl⟩))
  have h1 : cls (Mat.sum p q) - cls p - cls q = (0 : K0 R) := by
    have h2 : QuotientAddGroup.mk (FreeAbelianGroup.of (Mat.sum p q) - FreeAbelianGroup.of p
        - FreeAbelianGroup.of q) = cls (Mat.sum p q) - cls p - cls q := by
      simp only [cls, QuotientAddGroup.mk_sub]
    rw [← h2, QuotientAddGroup.eq_zero_iff]
    exact hmem
  have h3 : cls (Mat.sum p q) - cls p = cls q := sub_eq_zero.mp h1
  have h4 : cls (Mat.sum p q) = cls q + cls p := sub_eq_iff_eq_add.mp h3
  rw [h4, add_comm]

/-- A matrix class whose underlying matrix vanishes is trivial in `K₀`. -/
lemma sphKT_cls_of_zero [Ring R] {p : Mat R} (hp : p.2 = 0) : cls p = 0 := by
  have hzero : Mat.IsIdem (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) :=
    Subsingleton.elim _ _
  have hp' : Mat.IsIdem p := by simp only [Mat.IsIdem, hp, mul_zero]
  have hmem : FreeAbelianGroup.of p
      - FreeAbelianGroup.of (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨p, ⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩,
      hp', hzero, ⟨0, 0, by simp [hp], by simp⟩, rfl⟩))
  have h1 : cls p = cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
    have h2 : QuotientAddGroup.mk (FreeAbelianGroup.of p
        - FreeAbelianGroup.of (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R))
        = cls p - cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
      simp only [cls, QuotientAddGroup.mk_sub]
    have h3 : cls p - cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) = 0 := by
      rw [← h2, QuotientAddGroup.eq_zero_iff]
      exact hmem
    exact sub_eq_zero.mp h3
  have hsum0 : Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
      ⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ = ⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      ext i j
      exact Fin.elim0 i
  have hzero0 : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) = 0 := by
    have h : cls (Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
        ⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩)
        = cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
          + cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := sphKT_cls_sum hzero hzero
    rw [hsum0] at h
    have hc : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) + (0 : K0 R)
        = cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
          + cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
      rw [add_zero]; exact h
    exact (add_left_cancel hc).symm
  rw [h1, hzero0]

/-- `K₀` of a ring homomorphism on the class of an idempotent. -/
lemma sphKT_K0.map_cls [Ring R] [Ring S] (φ : R →+* S) {p : Mat R} (hp : Mat.IsIdem p) :
    K0.map φ (cls p) = cls (Mat.map φ p) := by
  classical
  unfold K0.map cls
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  unfold mapCls
  rw [if_pos hp]
  rfl

end K0basic

/-! ## Pullback of functions along a homeomorphism -/

section Pull

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism, regarded as a continuous map. -/
def sphKT_homeomorphToCM (e : X ≃ₜ Y) : C(X, Y) := ⟨e, e.continuous_toFun⟩

@[simp] lemma homeomorphToCM_apply (e : X ≃ₜ Y) (x : X) : sphKT_homeomorphToCM e x = e x := rfl

/-- Pullback of continuous functions along a homeomorphism, as an algebra equivalence. -/
def sphKT_pullAlgEquiv (e : X ≃ₜ Y) : C(Y, ℂ) ≃ₐ[ℂ] C(X, ℂ) where
  toFun := pullAlg (sphKT_homeomorphToCM e)
  invFun := pullAlg (sphKT_homeomorphToCM e.symm)
  left_inv := by
    intro f
    ext x
    simp [pullAlg, sphKT_homeomorphToCM]
  right_inv := by
    intro g
    ext y
    simp [pullAlg, sphKT_homeomorphToCM]
  map_mul' := by intro f g; ext x; simp [pullAlg, sphKT_homeomorphToCM]
  map_add' := by intro f g; ext x; simp [pullAlg, sphKT_homeomorphToCM]
  commutes' := by intro c; ext x; simp [pullAlg, sphKT_homeomorphToCM]

@[simp] lemma pullAlgEquiv_apply (e : X ≃ₜ Y) (f : C(Y, ℂ)) :
    sphKT_pullAlgEquiv e f = f.comp (sphKT_homeomorphToCM e) := rfl

@[simp] lemma pullAlgEquiv_symm_apply (e : X ≃ₜ Y) (g : C(X, ℂ)) :
    (sphKT_pullAlgEquiv e).symm g = g.comp (sphKT_homeomorphToCM e.symm) := rfl

@[simp] lemma pullAlgEquiv_apply_apply (e : X ≃ₜ Y) (f : C(Y, ℂ)) (x : X) :
    sphKT_pullAlgEquiv e f x = f (e x) := rfl

end Pull

/-! ## The algebra isomorphism `C(S^d) ≅ C(D^d/S^{d-1})` -/

section DiskQuot

open Classical in
/-- The algebra isomorphism `C(S^d, ℂ) ≅ Kpair ℝ^d` induced by a quotient map `q : D^d → S^d`
collapsing the boundary of the disc to the north pole.  Evaluation at the north pole corresponds
to evaluation at any boundary point. -/
def sphKT_diskQuotAlgEquiv (d : ℕ) (q : C(Ball (Euc d), Sph (ModelSphere d)))
    (hq : Topology.IsQuotientMap q)
    (hfib : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)))
    (hnp : ∀ x ∈ bdry (Euc d), q x = sphKT_northPole d) :
    C(Sph (ModelSphere d), ℂ) ≃ₐ[ℂ] Kpair (Euc d) := by
  have hfac : ∀ g : Kpair (Euc d), Function.FactorsThrough (g : C(Ball (Euc d), ℂ)) q := by
    intro g a a' h
    rcases hfib a a' h with rfl | ⟨ha, ha'⟩
    · rfl
    · exact g.2 a ha a' ha'
  have hmem : ∀ h : C(Sph (ModelSphere d), ℂ), pullAlg q h ∈ Kpair (Euc d) := by
    intro h a ha a' ha'
    rw [show (pullAlg q h) a = h (q a) from rfl, show (pullAlg q h) a' = h (q a') from rfl,
      hnp a ha, hnp a' ha']
  have hinj : Function.Injective (pullAlg q) := by
    intro f g h
    ext y
    obtain ⟨x, rfl⟩ := hq.surjective y
    simpa using ContinuousMap.ext_iff.mp h x
  refine AlgEquiv.ofBijective ((pullAlg q).codRestrict (Kpair (Euc d)) hmem) ⟨?_, ?_⟩
  · exact (AlgHom.injective_codRestrict _ _ _).mpr hinj
  · intro g
    refine ⟨hq.lift (g : C(Ball (Euc d), ℂ)) (hfac g), ?_⟩
    apply Subtype.ext
    rw [AlgHom.coe_codRestrict]
    show pullAlg q (hq.lift (g : C(Ball (Euc d), ℂ)) (hfac g)) = (g : C(Ball (Euc d), ℂ))
    exact hq.lift_comp _ _

/-- The augmentation compatibility of `sphKT_diskQuotAlgEquiv`. -/
lemma diskQuotAlgEquiv_aug (d : ℕ) (q : C(Ball (Euc d), Sph (ModelSphere d)))
    (hq : Topology.IsQuotientMap q)
    (hfib : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)))
    (hnp : ∀ x ∈ bdry (Euc d), q x = sphKT_northPole d)
    (y0 : Ball (Euc d)) (hy0 : y0 ∈ bdry (Euc d)) (h : C(Sph (ModelSphere d), ℂ)) :
    augPair (Euc d) y0 (sphKT_diskQuotAlgEquiv d q hq hfib hnp h) = evalC (sphKT_northPole d) h := by
  have h1 : ((sphKT_diskQuotAlgEquiv d q hq hfib hnp h : Kpair (Euc d)) : C(Ball (Euc d), ℂ)) y0
      = h (q y0) := rfl
  rw [show augPair (Euc d) y0 (sphKT_diskQuotAlgEquiv d q hq hfib hnp h)
      = ((sphKT_diskQuotAlgEquiv d q hq hfib hnp h : Kpair (Euc d)) : C(Ball (Euc d), ℂ)) y0
        from rfl, h1, hnp y0 hy0]
  rfl

end DiskQuot

/-! ## The radial-normalisation homeomorphism `Sph V ≃ₜ Sph W` -/

section SphereHomeo

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A point of the unit sphere has norm one. -/
lemma sphKT_norm_coe_sph (x : Sph V) : ‖(x : V)‖ = 1 := by
  have h := Metric.mem_sphere.mp x.2
  rwa [dist_eq_norm, sub_zero] at h

/-- A point of the unit sphere is nonzero. -/
lemma sphKT_ne_zero_of_sph (x : Sph V) : (x : V) ≠ 0 := by
  intro h
  have h1 := sphKT_norm_coe_sph x
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- `L x / ‖L x‖` is a unit vector when `x ≠ 0`. -/
lemma sphKT_normalize_mem_sphere (L : V ≃ₗ[ℝ] W) {x : V} (hx : x ≠ 0) :
    ‖L x‖⁻¹ • L x ∈ Metric.sphere (0 : W) 1 := by
  have hLx : L x ≠ 0 := fun h => hx (L.injective (by simpa using h))
  have hnorm : ‖L x‖ ≠ 0 := norm_ne_zero_iff.mpr hLx
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (L x)),
    inv_mul_cancel₀ hnorm]

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [CompleteSpace V] [CompleteSpace W]

/-- The homeomorphism `Sph V ≃ₜ Sph W` induced by a linear equivalence, by radial normalisation
of `L x` (and of `L.symm y` for the inverse). -/
def sphKT_sphereHomeoOfLinearEquiv (L : V ≃ₗ[ℝ] W) : Sph V ≃ₜ Sph W where
  toFun x := ⟨‖L (x:V)‖⁻¹ • L (x:V), sphKT_normalize_mem_sphere L (sphKT_ne_zero_of_sph x)⟩
  invFun y := ⟨‖L.symm (y:W)‖⁻¹ • L.symm (y:W), sphKT_normalize_mem_sphere L.symm (sphKT_ne_zero_of_sph y)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have hx : (x:V) ≠ 0 := sphKT_ne_zero_of_sph x
    have hLx : L (x:V) ≠ 0 := fun h => hx (L.injective (by simpa using h))
    have hnorm : ‖L (x:V)‖ ≠ 0 := norm_ne_zero_iff.mpr hLx
    have h1 : ‖(‖L (x:V)‖⁻¹) • (x:V)‖ = ‖L (x:V)‖⁻¹ := by
      rw [norm_smul, sphKT_norm_coe_sph x, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have h2 : (‖(‖L (x:V)‖⁻¹) • (x:V)‖)⁻¹ = ‖L (x:V)‖ := by rw [h1, inv_inv]
    calc ‖L.symm (‖L (x:V)‖⁻¹ • L (x:V))‖⁻¹ • L.symm (‖L (x:V)‖⁻¹ • L (x:V))
        = ‖(‖L (x:V)‖⁻¹) • (x:V)‖⁻¹ • ((‖L (x:V)‖⁻¹) • (x:V)) := by
          rw [map_smul, LinearEquiv.symm_apply_apply]
      _ = (x:V) := by rw [h2, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  right_inv := by
    intro y
    apply Subtype.ext
    have hy : (y:W) ≠ 0 := sphKT_ne_zero_of_sph y
    have hLy : L.symm (y:W) ≠ 0 := fun h => hy (L.symm.injective (by simpa using h))
    have hnorm : ‖L.symm (y:W)‖ ≠ 0 := norm_ne_zero_iff.mpr hLy
    have h1 : ‖(‖L.symm (y:W)‖⁻¹) • (y:W)‖ = ‖L.symm (y:W)‖⁻¹ := by
      rw [norm_smul, sphKT_norm_coe_sph y, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have h2 : (‖(‖L.symm (y:W)‖⁻¹) • (y:W)‖)⁻¹ = ‖L.symm (y:W)‖ := by rw [h1, inv_inv]
    calc ‖L (‖L.symm (y:W)‖⁻¹ • L.symm (y:W))‖⁻¹ • L (‖L.symm (y:W)‖⁻¹ • L.symm (y:W))
        = ‖(‖L.symm (y:W)‖⁻¹) • (y:W)‖⁻¹ • ((‖L.symm (y:W)‖⁻¹) • (y:W)) := by
          rw [map_smul, LinearEquiv.apply_symm_apply]
      _ = (y:W) := by rw [h2, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  continuous_toFun := by
    have hgc : ContinuousOn (fun x : V => ‖L x‖⁻¹ • L x) (Metric.sphere (0 : V) 1) := by
      apply ContinuousOn.smul
      · refine ContinuousOn.inv₀ ?_ ?_
        · exact (continuous_norm.comp L.continuous_of_finiteDimensional).continuousOn
        · intro x hx
          exact norm_ne_zero_iff.mpr
            (fun h => sphKT_ne_zero_of_sph (⟨x, hx⟩ : Sph V) (L.injective (by simpa using h)))
      · exact L.continuous_of_finiteDimensional.continuousOn
    exact hgc.restrict.subtype_mk (fun x => sphKT_normalize_mem_sphere L (sphKT_ne_zero_of_sph x))
  continuous_invFun := by
    have hgc : ContinuousOn (fun y : W => ‖L.symm y‖⁻¹ • L.symm y) (Metric.sphere (0 : W) 1) := by
      apply ContinuousOn.smul
      · refine ContinuousOn.inv₀ ?_ ?_
        · exact (continuous_norm.comp L.symm.continuous_of_finiteDimensional).continuousOn
        · intro y hy
          exact norm_ne_zero_iff.mpr
            (fun h => sphKT_ne_zero_of_sph (⟨y, hy⟩ : Sph W) (L.symm.injective (by simpa using h)))
      · exact L.symm.continuous_of_finiteDimensional.continuousOn
    exact hgc.restrict.subtype_mk (fun y => sphKT_normalize_mem_sphere L.symm (sphKT_ne_zero_of_sph y))

@[simp] lemma sphereHomeoOfLinearEquiv_apply_coe (L : V ≃ₗ[ℝ] W) (x : Sph V) :
    ((sphKT_sphereHomeoOfLinearEquiv L x : Sph W) : W) = ‖L (x:V)‖⁻¹ • L (x:V) := rfl

end SphereHomeo

/-! ## A linear equivalence sending a prescribed unit vector to the north pole -/

section LinearModel

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The north pole of the model sphere, as a vector. -/
def sphKT_northPoleVec (d : ℕ) : ModelSphere d := WithLp.toLp 2 ((0 : Euc d), (1 : ℝ))

lemma norm_northPoleVec (d : ℕ) : ‖sphKT_northPoleVec d‖ = 1 := by
  rw [sphKT_northPoleVec, WithLp.prod_norm_eq_of_L2]
  simp

lemma sphKT_finrank_modelSphere (d : ℕ) : Module.finrank ℝ (ModelSphere d) = d + 1 := by
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Euc d × ℝ)), Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_self]

/-- A homeomorphism `Sph V ≃ₜ Sph (ℝ^d × ℝ)` sending a prescribed unit vector to the north pole. -/
lemma sphKT_exists_sphereHomeo_modelSphere (t0 : Sph V) (d : ℕ)
    (hd : Module.finrank ℝ V = d + 1) :
    ∃ e : Sph V ≃ₜ Sph (ModelSphere d), e t0 = sphKT_northPole d := by
  have hfd : Module.finrank ℝ V = Module.finrank ℝ (ModelSphere d) := by
    rw [hd, sphKT_finrank_modelSphere]
  obtain ⟨L₀⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hfd
  have hu : L₀ (t0 : V) ≠ 0 := fun h => sphKT_ne_zero_of_sph t0 (L₀.injective (by rw [h, map_zero]))
  have hnu : ‖L₀ (t0 : V)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnorm : ‖L₀ (t0 : V)‖ = ‖‖L₀ (t0 : V)‖ • sphKT_northPoleVec d‖ := by
    rw [norm_smul, norm_northPoleVec, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine ⟨sphKT_sphereHomeoOfLinearEquiv (L₀.trans
      ((ℝ ∙ (L₀ (t0 : V) - ‖L₀ (t0 : V)‖ • sphKT_northPoleVec d))ᗮ.reflection).toLinearEquiv), ?_⟩
  apply Subtype.ext
  rw [sphereHomeoOfLinearEquiv_apply_coe, LinearEquiv.trans_apply]
  rw [show ((ℝ ∙ (L₀ (t0 : V) - ‖L₀ (t0 : V)‖ • sphKT_northPoleVec d))ᗮ.reflection).toLinearEquiv
        (L₀ (t0 : V)) = ‖L₀ (t0 : V)‖ • sphKT_northPoleVec d from Submodule.reflection_sub hnorm]
  have hnorm2 : ‖‖L₀ (t0 : V)‖ • sphKT_northPoleVec d‖ = ‖L₀ (t0 : V)‖ := by
    rw [norm_smul, norm_northPoleVec, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hnorm2, smul_smul, inv_mul_cancel₀ hnu, one_smul]
  rfl

end LinearModel

end

end Work.KT
