import Mathlib
import Submission.Work.KT.ExtGen.Triple
import Submission.Work.KT.ExtGen.TripleBdry
import Submission.Work.KT.ExtAux.MilnorExact
import Submission.Work.KT.ext_product
import Submission.Work.KT.ExtGen.bdryProj_surjective
import Submission.Work.KT.ExtGen.bdryEps_spec
import Submission.Work.KT.ExtGen.bdry_lift
import Submission.Work.KT.ExtGen.exists_bdryKernel_iso
import Submission.Work.KT.ExtGen.tripleInclQ_bijective_of_subsingleton
import Submission.Work.KT.ExtGen.tripleInclP_bijective_of_subsingleton
import Submission.Work.KT.ExtGen.smashIncl_bijective_of_subsingleton

/-!
# `Work.KT.ExtGen.tripleIncl_injective`

Injectivity of the smash-to-triple-product comparison map `tripleIncl V W Z`, proved by Milnor
exactness (`k0_exact` (1)+(2)) applied to the three-chart restriction `bdryProj` of `tripleAlg`;
see `Submission/Work/KT/ExtGen/TripleBdry.lean`.  The degenerate cases in which one of `V`, `W`, `Z`
is trivial (so that it has no unit vector) are reduced to `Work.KT.ext_product` via the two other
factorisations of `tripleIncl` (`tripleInclP`, `tripleInclQ`).
-/

namespace Work.KT.ExtGen

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-! ## `K₀`-bookkeeping -/

lemma tIncl_mapA_comp {A B Cc : Type} [Ring A] [Ring B] [Ring Cc] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra ℂ Cc] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] Cc) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  ExtAux.k0map_comp A B Cc φ.toRingHom ψ.toRingHom

lemma tIncl_mapA_id {A : Type} [Ring A] [Algebra ℂ A] :
    K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) := ExtAux.k0map_id A

lemma tIncl_mapA_apply_comp {A B Cc : Type} [Ring A] [Ring B] [Ring Cc] [Algebra ℂ A]
    [Algebra ℂ B] [Algebra ℂ Cc] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] Cc) (x : K0 A) :
    K0.mapA (ψ.comp φ) x = K0.mapA ψ (K0.mapA φ x) := by
  rw [tIncl_mapA_comp φ ψ, AddMonoidHom.comp_apply]

lemma tIncl_mapA_injective_of_bijective {A B : Type} [Ring A] [Ring B] [Algebra ℂ A]
    [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (hφ : Function.Bijective φ) :
    Function.Injective (K0.mapA φ) := by
  intro x y hxy
  let e : A ≃ₐ[ℂ] B := AlgEquiv.ofBijective φ hφ
  have key : ∀ z : K0 A, K0.mapA e.symm.toAlgHom (K0.mapA φ z) = z := by
    intro z
    rw [← tIncl_mapA_apply_comp φ e.symm.toAlgHom z,
      show e.symm.toAlgHom.comp φ = AlgHom.id ℂ A from
        AlgHom.ext (fun a => e.symm_apply_apply a), tIncl_mapA_id]
    rfl
  rw [← key x, hxy, key y]

/-! ## Trivial factors -/

/-- A real normed space with no unit vector is trivial. -/
lemma subsingleton_of_no_bdry (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : ¬ ∃ y : Ball X, y ∈ bdry X) : Subsingleton X :=
  ⟨fun x y => by
    by_contra hxy
    have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hnu : ‖((‖x - y‖)⁻¹) • (x - y)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hnorm]
    exact h ⟨⟨(‖x - y‖)⁻¹ • (x - y), by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hnu.le⟩, by
      show ‖((‖x - y‖)⁻¹ • (x - y) : X)‖ = 1
      exact hnu⟩⟩

/-! ## Injectivity of the smash inclusion on reduced classes -/

lemma smashIncl_inj_reduced (U X : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (y0 : Ball (U × X)) (hy0 : y0 ∈ bdry (U × X)) :
    ∀ z : K0 (Kpair (U × X)), K0.mapA (augPair (U × X) y0) z = 0 →
      K0.mapA (smashIncl U X) z = 0 → z = 0 := by
  by_cases hU : ∃ u0 : Ball U, u0 ∈ bdry U
  · by_cases hX : ∃ x0 : Ball X, x0 ∈ bdry X
    · obtain ⟨u0, hu0⟩ := hU
      obtain ⟨x0, hx0⟩ := hX
      exact (ext_product U X u0 hu0 x0 hx0 y0 hy0).2
    · have hsub := subsingleton_of_no_bdry X hX
      intro z hz1 hz2
      exact tIncl_mapA_injective_of_bijective (smashIncl U X)
        (smashIncl_bijective_of_subsingleton U X (Or.inr hsub))
        (hz2.trans (map_zero (K0.mapA (smashIncl U X))).symm)
  · have hsub := subsingleton_of_no_bdry U hU
    intro z hz1 hz2
    exact tIncl_mapA_injective_of_bijective (smashIncl U X)
      (smashIncl_bijective_of_subsingleton U X (Or.inl hsub))
      (hz2.trans (map_zero (K0.mapA (smashIncl U X))).symm)

/-! ## The generic case: three genuine charts -/

theorem tripleIncl_injective_of_bdry (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)
    (y0 : Ball (V × (W × Z))) (hy0 : y0 ∈ bdry (V × (W × Z))) :
    ∀ x : K0 (Kpair (V × (W × Z))),
      K0.mapA (augPair (V × (W × Z)) y0) x = 0 →
      K0.mapA (tripleIncl V W Z) x = 0 → x = 0 := by
  intro x hx1 hx2
  obtain ⟨ψ, hψ⟩ := exists_bdryKernel_iso V W Z v0 hv0 w0 hw0 z0 hz0
  letI : Ring ↥(Kpair (V × (W × Z))) :=
    @Subalgebra.toRing ℂ C(Ball (V × (W × Z)), ℂ) _ _ _ (Kpair (V × (W × Z)))
  letI : Algebra ℂ ↥(Kpair (V × (W × Z))) := (Kpair (V × (W × Z))).algebra
  letI : Ring ↥(bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) :=
    @Subalgebra.toRing ℂ ↥(tripleAlg V W Z) _ _ _ (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0)
  letI : Algebra ℂ ↥(bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) :=
    (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).algebra
  let φψ : Kpair (V × (W × Z)) →ₐ[ℂ] ↥(bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) := ψ.toAlgHom
  let φψinv : ↥(bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) →ₐ[ℂ] Kpair (V × (W × Z)) := ψ.symm.toAlgHom
  have hψ' : (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val.comp φψ = tripleIncl V W Z := hψ
  have hkey := ExtAux.k0_exact_injective (tripleAlg V W Z)
    (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0)
    (bdryProj_surjective V W Z v0 hv0 w0 hw0 z0 hz0)
    (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) (fun r => Iff.rfl)
    (bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0)
    (bdryEps_spec V W Z v0 hv0 w0 hw0 z0 hz0 y0 hy0)
    (bdry_lift V W Z v0 hv0 w0 hw0 z0 hz0)
  have heps : (bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0).comp φψ = augPair (V × (W × Z)) y0 := by
    apply AlgHom.ext
    intro F
    rw [AlgHom.comp_apply, bdryEps_apply]
    show ((bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val (φψ F) : C(Ball (V × (W × Z)), ℂ)) y0
      = (F : C(Ball (V × (W × Z)), ℂ)) y0
    have h1 : (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val (φψ F) = tripleIncl V W Z F := by
      rw [← AlgHom.comp_apply, hψ']
    rw [h1]
    rfl
  have hw1 : K0.mapA (bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0) (K0.mapA φψ x) = 0 := by
    rw [← AddMonoidHom.comp_apply,
      ← tIncl_mapA_comp φψ (bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0), heps]
    exact hx1
  have hw2 : K0.mapA (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val (K0.mapA φψ x) = 0 := by
    rw [← AddMonoidHom.comp_apply,
      ← tIncl_mapA_comp φψ (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val, hψ']
    exact hx2
  have hw := hkey (K0.mapA φψ x) hw1 hw2
  have hx : x = K0.mapA φψinv (K0.mapA φψ x) := by
    rw [← tIncl_mapA_apply_comp φψ φψinv x,
      show φψinv.comp φψ = AlgHom.id ℂ (Kpair (V × (W × Z))) from
        AlgHom.ext (fun a => ψ.symm_apply_apply a), tIncl_mapA_id]
    rfl
  rw [hx, hw, map_zero]

/-! ## The degenerate case `V` trivial -/

theorem tripleIncl_injective_of_subsingletonV (V W Z : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (hsub : Subsingleton V) (y0 : Ball (V × (W × Z))) (hy0 : y0 ∈ bdry (V × (W × Z))) :
    ∀ x : K0 (Kpair (V × (W × Z))),
      K0.mapA (augPair (V × (W × Z)) y0) x = 0 →
      K0.mapA (tripleIncl V W Z) x = 0 → x = 0 := by
  intro x hx1 hx2
  have hinjQ := tIncl_mapA_injective_of_bijective (tripleInclQ V W Z)
    (tripleInclQ_bijective_of_subsingleton V W Z hsub)
  set x' := K0.mapA (pairAssocEquiv V W Z).symm.toAlgHom x with hx'def
  have hxeq : K0.mapA (pairAssocEquiv V W Z).toAlgHom x' = x := by
    rw [hx'def, ← tIncl_mapA_apply_comp (pairAssocEquiv V W Z).symm.toAlgHom
      (pairAssocEquiv V W Z).toAlgHom x,
      show (pairAssocEquiv V W Z).toAlgHom.comp (pairAssocEquiv V W Z).symm.toAlgHom
        = AlgHom.id ℂ (Kpair (V × (W × Z))) from
        AlgHom.ext (fun a => (pairAssocEquiv V W Z).apply_symm_apply a), tIncl_mapA_id]
    rfl
  have haug : (augPair ((V × W) × Z) (ballAssoc V W Z y0)).comp
      (pairAssocEquiv V W Z).symm.toAlgHom = augPair (V × (W × Z)) y0 := by
    apply AlgHom.ext
    intro F
    show ((F : C(Ball (V × (W × Z)), ℂ)).comp (ballAssocInv V W Z)) (ballAssoc V W Z y0)
      = (F : C(Ball (V × (W × Z)), ℂ)) y0
    rw [ContinuousMap.comp_apply, ballAssocInv_ballAssoc]
  have hfac : K0.mapA (tripleIncl V W Z) (K0.mapA (pairAssocEquiv V W Z).toAlgHom x')
      = K0.mapA (tripleInclQ V W Z) (K0.mapA (smashIncl (V × W) Z) x') := by
    rw [← tIncl_mapA_apply_comp (pairAssocEquiv V W Z).toAlgHom (tripleIncl V W Z) x',
      ← tIncl_mapA_apply_comp (smashIncl (V × W) Z) (tripleInclQ V W Z) x',
      tripleInclQ_comp_smashIncl V W Z, ← tripleIncl'_eq_comp_pairAssoc V W Z]
  have hsm : K0.mapA (smashIncl (V × W) Z) x' = 0 := by
    refine hinjQ ?_
    rw [map_zero, ← hfac, hxeq, hx2]
  have haug' : K0.mapA (augPair ((V × W) × Z) (ballAssoc V W Z y0)) x' = 0 := by
    rw [hx'def, ← tIncl_mapA_apply_comp (pairAssocEquiv V W Z).symm.toAlgHom
      (augPair ((V × W) × Z) (ballAssoc V W Z y0)) x, haug, hx1]
  have hfin := smashIncl_inj_reduced (V × W) Z (ballAssoc V W Z y0)
    ((bdry_ballAssoc_iff V W Z y0).mpr hy0) x' haug' hsm
  rw [← hxeq, hfin, map_zero]

/-! ## The degenerate case `W` or `Z` trivial -/

theorem tripleIncl_injective_of_subsingletonWZ (V W Z : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (h : Subsingleton W ∨ Subsingleton Z) (y0 : Ball (V × (W × Z)))
    (hy0 : y0 ∈ bdry (V × (W × Z))) :
    ∀ x : K0 (Kpair (V × (W × Z))),
      K0.mapA (augPair (V × (W × Z)) y0) x = 0 →
      K0.mapA (tripleIncl V W Z) x = 0 → x = 0 := by
  intro x hx1 hx2
  have hinjP := tIncl_mapA_injective_of_bijective (tripleInclP V W Z)
    (tripleInclP_bijective_of_subsingleton V W Z h)
  have hsm : K0.mapA (smashIncl V (W × Z)) x = 0 := by
    refine hinjP ?_
    rw [map_zero, ← tIncl_mapA_apply_comp (smashIncl V (W × Z)) (tripleInclP V W Z) x,
      tripleInclP_comp_smashIncl V W Z]
    exact hx2
  exact smashIncl_inj_reduced V (W × Z) y0 hy0 x hx1 hsm

/-! ## The main statement -/

/-- ROUTE (node `ext_nesting`): injectivity of the smash-to-triple-product comparison map.

`tripleAlg V W Z` is the algebra `C(S^a × S^b × S^c)` realised inside `C(Ball (V × (W × Z)), ℂ)`
(functions constant in each coordinate on its sphere, see
`Submission/Work/KT/ExtGen/Triple.lean`), and `tripleIncl : Kpair (V × (W × Z)) →ₐ[ℂ] tripleAlg V W Z`
is the inclusion, with `Kpair (V × (W × Z)) = C(D_{V×(W×Z)}/∂) = C(S^{a+b+c})`.  The statement is
that this comparison is injective on reduced classes, i.e. that the product of the three
pulled-back Bott classes is non-zero. -/
theorem tripleIncl_injective (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (y0 : Ball (V × (W × Z))) (hy0 : y0 ∈ bdry (V × (W × Z))) :
    ∀ x : K0 (Kpair (V × (W × Z))),
      K0.mapA (augPair (V × (W × Z)) y0) x = 0 →
      K0.mapA (tripleIncl V W Z) x = 0 → x = 0 := by
  intro x hx1 hx2
  by_cases hV : ∃ v0 : Ball V, v0 ∈ bdry V
  · by_cases hW : ∃ w0 : Ball W, w0 ∈ bdry W
    · by_cases hZ : ∃ z0 : Ball Z, z0 ∈ bdry Z
      · obtain ⟨v0, hv0⟩ := hV
        obtain ⟨w0, hw0⟩ := hW
        obtain ⟨z0, hz0⟩ := hZ
        exact tripleIncl_injective_of_bdry V W Z v0 hv0 w0 hw0 z0 hz0 y0 hy0 x hx1 hx2
      · exact tripleIncl_injective_of_subsingletonWZ V W Z
          (Or.inr (subsingleton_of_no_bdry Z hZ)) y0 hy0 x hx1 hx2
    · exact tripleIncl_injective_of_subsingletonWZ V W Z
        (Or.inl (subsingleton_of_no_bdry W hW)) y0 hy0 x hx1 hx2
  · exact tripleIncl_injective_of_subsingletonV V W Z
      (subsingleton_of_no_bdry V hV) y0 hy0 x hx1 hx2

end

end Work.KT.ExtGen
