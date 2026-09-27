import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.Nat
import Submission.Work.KT.Psi.sq2Part_idem
import Submission.Work.KT.K0map.map_comp
import Submission.Work.KT.K0map.map_id
import Submission.Work.KT.radRescaleSpec
import Submission.Work.KT.cubePartIsIdem

/-!
# `Work.KT.ballK_transfer`: change of norm and dimension for `BallKStmt`

`BallKStmt` is invariant under a linear isomorphism `φ : V ≃ₗ[ℝ] W` of finite-dimensional real
normed spaces.  The radial map `x ↦ ‖x‖ • (‖φ x‖)⁻¹ • φ x` is a homeomorphism `D_V → D_W` of ball
pairs (`Work.KT.radRescaleSpec`), so it induces an algebra isomorphism
`Kpair W ≃ₐ[ℂ] Kpair V` carrying the augmentation to the augmentation (any boundary points) and
natural for `ψ²`, `ψ³`.  The `ψ`-operations are transported by conjugating with the induced
isomorphism along `K0.mapA`, using the naturality of `psi2Cls`/`psi3Cls` on idempotent generators.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

/-! ## Helpers -/

/-! ## 1. `K₀` along algebra isomorphisms -/

section Transport

variable {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

lemma bkT_mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
  have hto : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := by ext x; rfl
  change K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
  rw [hto]
  exact K0map.map_comp A B C φ.toRingHom ψ.toRingHom

lemma bkT_mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  K0map.map_id A

lemma bkT_mapA_symm_apply (Φ : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA (Φ.symm).toAlgHom (K0.mapA Φ.toAlgHom x) = x := by
  have h2 : (K0.mapA (Φ.symm).toAlgHom).comp (K0.mapA Φ.toAlgHom) =
      AddMonoidHom.id (K0 A) := by
    rw [← bkT_mapA_comp Φ.toAlgHom (Φ.symm).toAlgHom, AlgEquiv.symm_comp (e := Φ)]
    exact bkT_mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma bkT_mapA_apply_symm (Φ : A ≃ₐ[ℂ] B) (x : K0 B) :
    K0.mapA Φ.toAlgHom (K0.mapA (Φ.symm).toAlgHom x) = x := by
  have h2 : (K0.mapA Φ.toAlgHom).comp (K0.mapA (Φ.symm).toAlgHom) =
      AddMonoidHom.id (K0 B) := by
    rw [← bkT_mapA_comp (Φ.symm).toAlgHom Φ.toAlgHom, AlgEquiv.comp_symm (e := Φ)]
    exact bkT_mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma bkT_mapA_injective (Φ : A ≃ₐ[ℂ] B) : Function.Injective (K0.mapA Φ.toAlgHom) := by
  intro x y h
  rw [← bkT_mapA_symm_apply Φ x, ← bkT_mapA_symm_apply Φ y, h]

end Transport

/-! ## 2. Matrix naturality helpers -/

lemma bkT_Mat_map_id {A : Type} [Ring A] (p : Mat A) : p.map (RingHom.id A) = p := by
  obtain ⟨n, M⟩ := p
  simp only [Mat.map]
  congr 1

lemma bkT_Mat_map_comp {A B C : Type} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (g : B →+* C) (p : Mat A) :
    (p.map f).map g = p.map (g.comp f) := by
  obtain ⟨n, M⟩ := p
  simp only [Mat.map, Matrix.map_map]
  congr 1

/-! ## 3. Naturality of `psi2Cls`, `psi3Cls` on idempotents -/

lemma bkT_psi2Cls_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (hA : ∀ x y : A, x * y = y * x) {p : Mat A} (hp : Mat.IsIdem p) :
    K0.mapA φ (psi2Cls p) = psi2Cls (p.map φ.toRingHom) := by
  have hp' : (p.map φ.toRingHom).IsIdem := Mat.isIdem_map hp φ.toRingHom
  rw [show psi2Cls p = cls (sq2Part 1 p) - cls (sq2Part (-1) p) from by
        unfold psi2Cls; rw [if_pos hp],
      show psi2Cls (p.map φ.toRingHom) = cls (sq2Part 1 (p.map φ.toRingHom)) -
          cls (sq2Part (-1) (p.map φ.toRingHom)) from by
        unfold psi2Cls; rw [if_pos hp'],
      map_sub]
  congr 1
  · rw [show K0.mapA φ (cls (sq2Part 1 p)) = mapCls φ.toRingHom (sq2Part 1 p) from
          map_cls_uncond φ.toRingHom (sq2Part 1 p),
        mapCls, if_pos (Psi.sq2Part_idem hA 1 (by norm_num) hp), sq2Part_map]
  · rw [show K0.mapA φ (cls (sq2Part (-1) p)) = mapCls φ.toRingHom (sq2Part (-1) p) from
          map_cls_uncond φ.toRingHom (sq2Part (-1) p),
        mapCls, if_pos (Psi.sq2Part_idem hA (-1) (by norm_num) hp), sq2Part_map]

lemma bkT_psi3Cls_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (hA : ∀ x y : A, x * y = y * x) {p : Mat A} (hp : Mat.IsIdem p) :
    K0.mapA φ (psi3Cls p) = psi3Cls (p.map φ.toRingHom) := by
  have hp' : (p.map φ.toRingHom).IsIdem := Mat.isIdem_map hp φ.toRingHom
  rw [show psi3Cls p = cls (cubePart 1 p) - cls (cubePart omega p) from by
        unfold psi3Cls; rw [if_pos hp],
      show psi3Cls (p.map φ.toRingHom) = cls (cubePart 1 (p.map φ.toRingHom)) -
          cls (cubePart omega (p.map φ.toRingHom)) from by
        unfold psi3Cls; rw [if_pos hp'],
      map_sub]
  congr 1
  · rw [show K0.mapA φ (cls (cubePart 1 p)) = mapCls φ.toRingHom (cubePart 1 p) from
          map_cls_uncond φ.toRingHom (cubePart 1 p),
        mapCls, if_pos (cubePartIsIdem hA 1 (by norm_num) hp), cubePart_map]
  · rw [show K0.mapA φ (cls (cubePart omega p)) = mapCls φ.toRingHom (cubePart omega p) from
          map_cls_uncond φ.toRingHom (cubePart omega p),
        mapCls, if_pos (cubePartIsIdem hA omega omega_pow_three hp), cubePart_map]

/-! ## 4. The radial ball map -/

section Radial

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

lemma bkT_ball_norm_le {x : V} (hx : x ∈ Metric.closedBall (0 : V) 1) : ‖x‖ ≤ 1 := by
  simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx

/-- The radial homeomorphism of the unit balls induced by a linear isomorphism `φ`. -/
def bkT_ballMap (φ : V ≃ₗ[ℝ] W) : C(Ball V, Ball W) where
  toFun x := ⟨radRescale φ (x : V), by
    have hx2 : ‖(x : V)‖ ≤ 1 := bkT_ball_norm_le x.2
    have h : ‖radRescale φ (x : V)‖ = ‖(x : V)‖ := (radRescaleSpec φ).1 (x : V)
    rw [Metric.mem_closedBall, dist_zero_right, h]
    exact hx2⟩
  continuous_toFun := Continuous.subtype_mk (f := fun x : Ball V => radRescale φ (x : V))
    ((radRescaleSpec φ).2.1.comp continuous_subtype_val)
    (fun x => by
      have hx2 : ‖(x : V)‖ ≤ 1 := bkT_ball_norm_le x.2
      have h : ‖radRescale φ (x : V)‖ = ‖(x : V)‖ := (radRescaleSpec φ).1 (x : V)
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖radRescale φ (x : V)‖ ≤ 1
      rw [h]
      exact hx2)

lemma bkT_ballMap_apply (φ : V ≃ₗ[ℝ] W) (x : Ball V) :
    ((bkT_ballMap φ x : Ball W) : W) = radRescale φ (x : V) := rfl

lemma bkT_ballMap_bdry (φ : V ≃ₗ[ℝ] W) {x : Ball V} (hx : x ∈ bdry V) :
    bkT_ballMap φ x ∈ bdry W := by
  have hx' : ‖(x : V)‖ = 1 := hx
  show ‖((bkT_ballMap φ x : Ball W) : W)‖ = 1
  rw [bkT_ballMap_apply, (radRescaleSpec φ).1, hx']

lemma bkT_mul_comm {E : Type} [NormedAddCommGroup E] (x y : Kpair E) : x * y = y * x := by
  apply Subtype.ext
  ext z
  exact mul_comm _ _

/-! ## 5. The algebra map on `Kpair` -/

/-- Pull-back of functions along the radial map, as an algebra homomorphism `Kpair W → Kpair V`. -/
def bkT_kpairMap (φ : V ≃ₗ[ℝ] W) : Kpair W →ₐ[ℂ] Kpair V :=
  AlgHom.codRestrict ((pullAlg (bkT_ballMap φ)).comp (Kpair W).val) (Kpair V) (by
    intro g x hx x' hx'
    show (g : C(Ball W, ℂ)) (bkT_ballMap φ x) = (g : C(Ball W, ℂ)) (bkT_ballMap φ x')
    exact g.2 _ (bkT_ballMap_bdry φ hx) _ (bkT_ballMap_bdry φ hx'))

lemma bkT_kpairMap_apply (φ : V ≃ₗ[ℝ] W) (f : Kpair W) (x : Ball V) :
    ((bkT_kpairMap φ f : Kpair V) : C(Ball V, ℂ)) x = (f : C(Ball W, ℂ)) (bkT_ballMap φ x) :=
  rfl

lemma bkT_kpairMap_comp_symm (φ : V ≃ₗ[ℝ] W) :
    (bkT_kpairMap φ).comp (bkT_kpairMap φ.symm) = AlgHom.id ℂ (Kpair V) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change ((bkT_kpairMap φ (bkT_kpairMap φ.symm f) : Kpair V) : C(Ball V, ℂ)) x =
    (f : C(Ball V, ℂ)) x
  rw [bkT_kpairMap_apply, bkT_kpairMap_apply]
  congr 1
  exact Subtype.ext ((radRescaleSpec φ).2.2.1 (x : V))

lemma bkT_kpairMap_symm_comp (φ : V ≃ₗ[ℝ] W) :
    (bkT_kpairMap φ.symm).comp (bkT_kpairMap φ) = AlgHom.id ℂ (Kpair W) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change ((bkT_kpairMap φ.symm (bkT_kpairMap φ f) : Kpair W) : C(Ball W, ℂ)) y =
    (f : C(Ball W, ℂ)) y
  rw [bkT_kpairMap_apply, bkT_kpairMap_apply]
  congr 1
  exact Subtype.ext ((radRescaleSpec φ).2.2.2 (y : W))

/-- The algebra isomorphism `Kpair W ≃ₐ[ℂ] Kpair V` induced by `φ`. -/
def bkT_kpairEquiv (φ : V ≃ₗ[ℝ] W) : Kpair W ≃ₐ[ℂ] Kpair V :=
  AlgEquiv.ofAlgHom (bkT_kpairMap φ) (bkT_kpairMap φ.symm) (bkT_kpairMap_comp_symm φ)
    (bkT_kpairMap_symm_comp φ)

/-- The augmentation is carried to the augmentation (any boundary points). -/
lemma bkT_aug (φ : V ≃ₗ[ℝ] W) (y0 : Ball V) (hy0 : y0 ∈ bdry V) (y0' : Ball W)
    (hy0' : y0' ∈ bdry W) :
    (augPair V y0).comp (bkT_kpairMap φ) = augPair W y0' := by
  apply AlgHom.ext
  intro f
  show ((bkT_kpairMap φ f : Kpair V) : C(Ball V, ℂ)) y0 = (f : C(Ball W, ℂ)) y0'
  rw [bkT_kpairMap_apply]
  exact f.2 _ (bkT_ballMap_bdry φ hy0) _ hy0'

end Radial

/-! ## 6. Conjugating `IsPsi2`, `IsPsi3` along an algebra isomorphism -/

section Conj

variable {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

lemma bkT_conj_psi2 (Φ : B ≃ₐ[ℂ] A) (hA : ∀ x y : A, x * y = y * x)
    (ψ : K0 A →+ K0 A) (hψ : IsPsi2 ψ) :
    IsPsi2 ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) := by
  intro p
  by_cases hp : p.IsIdem
  · have hp' : (p.map Φ.toAlgHom.toRingHom).IsIdem := Mat.isIdem_map hp Φ.toAlgHom.toRingHom
    have hFp : K0.mapA Φ.toAlgHom (cls p) = cls (p.map Φ.toAlgHom.toRingHom) := by
      rw [show K0.mapA Φ.toAlgHom (cls p) = mapCls Φ.toAlgHom.toRingHom p from
            map_cls_uncond Φ.toAlgHom.toRingHom p]
      unfold mapCls
      rw [if_pos hp]
    have h1 : ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) (cls p) =
        K0.mapA Φ.symm.toAlgHom (psi2Cls (p.map Φ.toAlgHom.toRingHom)) := by
      simp only [AddMonoidHom.comp_apply]
      rw [hFp, hψ (p.map Φ.toAlgHom.toRingHom)]
    rw [h1, bkT_psi2Cls_map Φ.symm.toAlgHom hA hp']
    congr 1
    have hcomp : Φ.symm.toAlgHom.toRingHom.comp Φ.toAlgHom.toRingHom = RingHom.id B :=
      RingHom.ext (fun x => AlgEquiv.symm_apply_apply Φ x)
    rw [bkT_Mat_map_comp Φ.toAlgHom.toRingHom Φ.symm.toAlgHom.toRingHom p, hcomp,
      bkT_Mat_map_id]
  · have hFp : K0.mapA Φ.toAlgHom (cls p) = 0 := by
      rw [show K0.mapA Φ.toAlgHom (cls p) = mapCls Φ.toAlgHom.toRingHom p from
            map_cls_uncond Φ.toAlgHom.toRingHom p]
      unfold mapCls
      rw [if_neg hp]
    have h1 : ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) (cls p) = 0 := by
      simp only [AddMonoidHom.comp_apply]
      rw [hFp, map_zero, map_zero]
    rw [h1, show psi2Cls p = 0 from by unfold psi2Cls; rw [if_neg hp]]

lemma bkT_conj_psi3 (Φ : B ≃ₐ[ℂ] A) (hA : ∀ x y : A, x * y = y * x)
    (ψ : K0 A →+ K0 A) (hψ : IsPsi3 ψ) :
    IsPsi3 ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) := by
  intro p
  by_cases hp : p.IsIdem
  · have hp' : (p.map Φ.toAlgHom.toRingHom).IsIdem := Mat.isIdem_map hp Φ.toAlgHom.toRingHom
    have hFp : K0.mapA Φ.toAlgHom (cls p) = cls (p.map Φ.toAlgHom.toRingHom) := by
      rw [show K0.mapA Φ.toAlgHom (cls p) = mapCls Φ.toAlgHom.toRingHom p from
            map_cls_uncond Φ.toAlgHom.toRingHom p]
      unfold mapCls
      rw [if_pos hp]
    have h1 : ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) (cls p) =
        K0.mapA Φ.symm.toAlgHom (psi3Cls (p.map Φ.toAlgHom.toRingHom)) := by
      simp only [AddMonoidHom.comp_apply]
      rw [hFp, hψ (p.map Φ.toAlgHom.toRingHom)]
    rw [h1, bkT_psi3Cls_map Φ.symm.toAlgHom hA hp']
    congr 1
    have hcomp : Φ.symm.toAlgHom.toRingHom.comp Φ.toAlgHom.toRingHom = RingHom.id B :=
      RingHom.ext (fun x => AlgEquiv.symm_apply_apply Φ x)
    rw [bkT_Mat_map_comp Φ.toAlgHom.toRingHom Φ.symm.toAlgHom.toRingHom p, hcomp,
      bkT_Mat_map_id]
  · have hFp : K0.mapA Φ.toAlgHom (cls p) = 0 := by
      rw [show K0.mapA Φ.toAlgHom (cls p) = mapCls Φ.toAlgHom.toRingHom p from
            map_cls_uncond Φ.toAlgHom.toRingHom p]
      unfold mapCls
      rw [if_neg hp]
    have h1 : ((K0.mapA Φ.symm.toAlgHom).comp (ψ.comp (K0.mapA Φ.toAlgHom))) (cls p) = 0 := by
      simp only [AddMonoidHom.comp_apply]
      rw [hFp, map_zero, map_zero]
    rw [h1, show psi3Cls p = 0 from by unfold psi3Cls; rw [if_neg hp]]

end Conj

/-! ## 7. Transport of `BallKStmt` along an augmentation-compatible algebra isomorphism -/

section Transf

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

lemma bkT_transfer_of_algEquiv (hfin : Module.finrank ℝ W = Module.finrank ℝ V)
    (Φ : Kpair W ≃ₐ[ℂ] Kpair V) (y0 : Ball V) (hy0 : y0 ∈ bdry V)
    (y0' : Ball W) (hy0' : y0' ∈ bdry W) (j : ℕ)
    (haug : (augPair V y0).comp Φ.toAlgHom = augPair W y0')
    (h : BallKStmt W y0' hy0' j) : BallKStmt V y0 hy0 j := by
  set F : K0 (Kpair W) →+ K0 (Kpair V) := K0.mapA Φ.toAlgHom with hF
  set G : K0 (Kpair V) →+ K0 (Kpair W) := K0.mapA Φ.symm.toAlgHom with hG
  set aV : K0 (Kpair V) →+ K0 ℂ := K0.mapA (augPair V y0) with haV
  set aW : K0 (Kpair W) →+ K0 ℂ := K0.mapA (augPair W y0') with haW
  have hGF : ∀ x : K0 (Kpair W), G (F x) = x := fun x => by
    rw [hF, hG]; exact bkT_mapA_symm_apply Φ x
  have hFG : ∀ x : K0 (Kpair V), F (G x) = x := fun x => by
    rw [hF, hG]; exact bkT_mapA_apply_symm Φ x
  have hχ : aV.comp F = aW := by
    rw [haV, hF, haW, ← bkT_mapA_comp Φ.toAlgHom (augPair V y0), haug]
  have key : ∀ z : K0 (Kpair V), aV z = 0 → aW (G z) = 0 := by
    intro z hz
    have h1 : aW (G z) = aV z := by rw [← hχ, AddMonoidHom.comp_apply, hFG z]
    rw [h1]; exact hz
  have hcommV : ∀ x y : Kpair V, x * y = y * x := fun x y => bkT_mul_comm x y
  refine ⟨?_, ?_⟩
  · intro hV
    have hW : Module.finrank ℝ W = 2 * j := by rw [hfin]; exact hV
    obtain ⟨⟨g', hg'mem, hg'inf, hg'gen⟩, hpsi2, hpsi3⟩ := h.1 hW
    refine ⟨⟨F g', ?_, ?_, ?_⟩, ?_, ?_⟩
    · have h2 : aV (F g') = aW g' := by rw [← hχ, AddMonoidHom.comp_apply]
      rw [h2]; exact hg'mem
    · intro k hk
      have hz : k • g' = 0 := by
        have h1 := congrArg G hk
        rw [map_zsmul, hGF g', map_zero] at h1
        exact h1
      exact hg'inf k hz
    · intro z hz
      obtain ⟨k, hk⟩ := hg'gen (G z) (key z hz)
      exact ⟨k, by rw [← hFG z, hk, map_zsmul]⟩
    · intro ψ hψ z hz
      have hψW : IsPsi2 (G.comp (ψ.comp F)) := by
        have h' := bkT_conj_psi2 Φ hcommV ψ hψ
        rw [← hF, ← hG] at h'
        exact h'
      have h2 := hpsi2 (G.comp (ψ.comp F)) hψW (G z) (key z hz)
      have h2' : G (ψ z) = (2 ^ j : ℤ) • G z := by
        simpa only [AddMonoidHom.comp_apply, hFG z] using h2
      have h3 := congrArg F h2'
      simpa only [map_zsmul, hFG (ψ z), hFG z] using h3
    · intro ψ hψ z hz
      have hψW : IsPsi3 (G.comp (ψ.comp F)) := by
        have h' := bkT_conj_psi3 Φ hcommV ψ hψ
        rw [← hF, ← hG] at h'
        exact h'
      have h2 := hpsi3 (G.comp (ψ.comp F)) hψW (G z) (key z hz)
      have h2' : G (ψ z) = (3 ^ j : ℤ) • G z := by
        simpa only [AddMonoidHom.comp_apply, hFG z] using h2
      have h3 := congrArg F h2'
      simpa only [map_zsmul, hFG (ψ z), hFG z] using h3
  · intro hV z hz
    have hW : Module.finrank ℝ W = 2 * j + 1 := by rw [hfin]; exact hV
    rw [← hFG z, h.2 hW (G z) (key z hz), map_zero]

end Transf

/-! ## 8. The transfer theorem -/

theorem ballK_transfer (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (φ : V ≃ₗ[ℝ] W) (y0 : Ball V) (hy0 : y0 ∈ bdry V)
    (y0' : Ball W) (hy0' : y0' ∈ bdry W) (j : ℕ)
    (h : BallKStmt W y0' hy0' j) : BallKStmt V y0 hy0 j :=
  bkT_transfer_of_algEquiv (φ.finrank_eq.symm) (bkT_kpairEquiv φ) y0 hy0 y0' hy0' j
    (bkT_aug φ y0 hy0 y0' hy0') h

end

end Work.KT
