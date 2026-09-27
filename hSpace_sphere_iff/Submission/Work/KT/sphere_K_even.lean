import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.SphereSetup
import Submission.Work.KT.SphereAux
import Submission.Work.KT.diskQuot
import Submission.Work.KT.SG.odd
import Submission.Work.KT.k0_basic

/-!
# The even clause of `Work.KT.sphere_K`, isolated

`K̃(Sph V) = 0` when `finrank ℝ V` is odd, i.e. the reduced `K`-theory of an odd-dimensional
sphere vanishes.  This is the transport of `Work.KT.SG.oddKpair_vanishing` (proved from
`Work.KT.fund_product` alone, without the Adams operations) across the algebra
isomorphism `C(Sph V) ≅ Kpair (ℝ^d)`.

The lemma `Work.KT.sphere_K_even_aux` in `sphere_K.lean` says the same thing; it is repeated here
in a form whose import closure consists of `SG/odd` and the Tietze/quotient infrastructure,
so that the clutching construction of `Work.KT.sphere_GL` does not depend on the (much larger)
development of the Adams operations.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

/-! ## `K₀` along algebra isomorphisms -/

section Transport

variable {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

lemma sphereEven_mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
  have hto : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := by ext x; rfl
  change K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
  rw [hto]
  exact k0_basic.2.2.1 (A := A) (B := B) (C := C) φ.toRingHom ψ.toRingHom

lemma sphereEven_mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  k0_basic.2.2.2.1 (A := A)

lemma sphereEven_mapA_symm_apply (Φ : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA (Φ.symm).toAlgHom (K0.mapA Φ.toAlgHom x) = x := by
  have h2 : (K0.mapA (Φ.symm).toAlgHom).comp (K0.mapA Φ.toAlgHom) =
      AddMonoidHom.id (K0 A) := by
    rw [← sphereEven_mapA_comp Φ.toAlgHom (Φ.symm).toAlgHom, AlgEquiv.symm_comp (e := Φ)]
    exact sphereEven_mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma sphereEven_mapA_injective (Φ : A ≃ₐ[ℂ] B) : Function.Injective (K0.mapA Φ.toAlgHom) := by
  intro x y h
  rw [← sphereEven_mapA_symm_apply Φ x, ← sphereEven_mapA_symm_apply Φ y, h]

end Transport

/-! ## The algebra isomorphism `C(Sph V) ≅ Kpair ℝ^d` -/

section RingIso

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The algebra isomorphism `C(Sph V) ≅ Kpair (ℝ^d)` when `finrank ℝ V = d + 1`, compatible with
the augmentations: evaluation at `t0` corresponds to evaluation at any boundary point. -/
lemma sphereEven_exists_algEquiv_Kpair (t0 : Sph V) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : Module.finrank ℝ V = d + 1) :
    ∃ Φ : C(Sph V, ℂ) ≃ₐ[ℂ] Kpair (Euc d),
      ∀ (y0 : Ball (Euc d)) (hy0 : y0 ∈ bdry (Euc d)), ∀ h : C(Sph V, ℂ),
        augPair (Euc d) y0 (Φ h) = evalC t0 h := by
  obtain ⟨e, he⟩ := sphKT_exists_sphereHomeo_modelSphere V t0 d hd
  obtain ⟨q, hq, hnp, hfib⟩ := diskQuot d hd1
  let hf : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)) := fun x x' h => (hfib x x').mp h
  let Ψ : C(Sph (ModelSphere d), ℂ) ≃ₐ[ℂ] Kpair (Euc d) := sphKT_diskQuotAlgEquiv d q hq hf hnp
  refine ⟨(sphKT_pullAlgEquiv e.symm).trans Ψ, ?_⟩
  intro y0 hy0 h
  rw [AlgEquiv.trans_apply]
  have hΨ : augPair (Euc d) y0 (Ψ ((sphKT_pullAlgEquiv e.symm) h))
      = evalC (sphKT_northPole d) ((sphKT_pullAlgEquiv e.symm) h) :=
    diskQuotAlgEquiv_aug d q hq hf hnp y0 hy0 _
  rw [hΨ]
  have hsymm : e.symm (sphKT_northPole d) = t0 := by rw [← he, Homeomorph.symm_apply_apply]
  change ((sphKT_pullAlgEquiv e.symm) h) (sphKT_northPole d) = h t0
  rw [pullAlgEquiv_apply_apply, hsymm]

end RingIso

lemma sphereEven_exists_unit_Euc (d : ℕ) (hd : 1 ≤ d) :
    ∃ y0 : Ball (Euc d), y0 ∈ bdry (Euc d) := by
  refine ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, PiLp.norm_single, norm_one]
  · show ‖(EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Euc d)‖ = 1
    rw [PiLp.norm_single, norm_one]

/-! ## The vanishing -/

/-- **The reduced `K`-theory of an odd-dimensional sphere vanishes.**  If `finrank ℝ V = 2j+2`
then `Sph V = S^{2j+1}` and every reduced element of `K₀(C(Sph V, ℂ))` is zero. -/
theorem sphere_K_even (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (j : ℕ) (hV : Module.finrank ℝ V = 2 * j + 2) (t0 : Sph V) :
    ∀ z : K0 C(Sph V, ℂ), K0.mapA (evalC t0) z = 0 → z = 0 := by
  have hd1 : 1 ≤ 2 * j + 1 := by omega
  obtain ⟨Φ, hΦ⟩ := sphereEven_exists_algEquiv_Kpair V t0 (2 * j + 1) hd1 (by omega)
  obtain ⟨y0, hy0⟩ := sphereEven_exists_unit_Euc (2 * j + 1) hd1
  have hχ : K0.mapA (evalC t0) =
      (K0.mapA (augPair (Euc (2 * j + 1)) y0)).comp (K0.mapA Φ.toAlgHom) := by
    rw [show evalC t0 = (augPair (Euc (2 * j + 1)) y0).comp Φ.toAlgHom
      from AlgHom.ext fun h => (hΦ y0 hy0 h).symm]
    exact sphereEven_mapA_comp Φ.toAlgHom (augPair (Euc (2 * j + 1)) y0)
  intro z hz
  have hz' : K0.mapA (augPair (Euc (2 * j + 1)) y0) (K0.mapA Φ.toAlgHom z) = 0 := by
    change ((K0.mapA (augPair (Euc (2 * j + 1)) y0)).comp (K0.mapA Φ.toAlgHom)) z = 0
    rw [← hχ]
    exact hz
  have h0 : K0.mapA Φ.toAlgHom z = 0 :=
    SG.oddKpair_vanishing (Euc (2 * j + 1)) j
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * j + 1)) y0 hy0 _ (by
        simpa using hz')
  exact sphereEven_mapA_injective Φ (by rw [h0, map_zero])

end

end Work.KT
