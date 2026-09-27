import Mathlib
import Submission.Work.KT.HopfK.hk_sliceFst_pre
import Submission.Work.KT.HopfK.hopfPsiFst_cls
import Submission.Work.KT.HopfK.hk_slice_gen
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.HopfK.hk_sliceFst

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 4000000

/-- The main body of `hk_slice_gen_fst`, given the first-slice class identity
`hcls : cls (v.map hopfPsiFst) = cls (Q.map coneToT)`. -/
theorem hk_slice_gen_fst_aux (m : ℕ) (hm : 1 ≤ m) (hS : HSpace (Sph (Eu m)))
    (n r : ℕ) (t0 : Tgt m)
    (α : K0 C(Tgt m, ℂ)) (hαred : K0.mapA (evalC t0) α = 0)
    (hαnz : ∀ k : ℤ, k • α = 0 → k = 0)
    (hαgen : ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • α)
    (Q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hQ : Q * Q = Q)
    (hcap : ∀ t : Tgt m, t ∈ capTminus m →
      Q.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    (hclsQ : K0.mapA (coneToT (hopfKMap m hS.hmul))
      (cls (⟨n, Q⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
        - cls (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)) = α)
    (v : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hv : Mat.IsIdem (⟨n, v⟩ : Mat (Kpair (Eu m))))
    (hvQ : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = evalD m (hopfKMap m hS.hmul) (ptFst m hS.e y) (Q i j))
    (hcls : cls (⟨n, v.map (hopfPsiFst m hS)⟩ : Mat C(Tgt m, ℂ))
      = cls (⟨n, Q.map (coneToT (hopfKMap m hS.hmul))⟩ : Mat C(Tgt m, ℂ))) :
    K0.mapA (augPair (Eu m) (sphToBall hS.e)) (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
        - cls (diagMat (Kpair (Eu m)) r n)) = 0 ∧
      (∀ k : ℤ, k • (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n)) = 0 → k = 0) ∧
      (∀ z : K0 (Kpair (Eu m)), K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 →
        ∃ k : ℤ, z = k • (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n))) := by
  classical
  set γ : K0 (Kpair (Eu m)) :=
    cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n) with hγdef
  set yt : Ball (Eu m) :=
    (if 0 ≤ tgtHeight m t0 then lowerPt m t0 else sphToBall hS.e) with hyt
  have hcomp : (evalC t0).comp (hopfPsiFst m hS) = augPair (Eu m) yt := by
    apply AlgHom.ext
    intro u'
    show hopfPsiFst m hS u' t0 = (u' : C(Ball (Eu m), ℂ)) yt
    rw [hopfPsiFst_apply]
    simp only [hopfPsiFstFun]
    rw [hyt]
  have key_eval : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (evalC t0) (K0.mapA (hopfPsiFst m hS) z) = K0.mapA (augPair (Eu m) yt) z := by
    intro z
    have h1 : ((K0.mapA (evalC t0)).comp (K0.mapA (hopfPsiFst m hS))) z
        = K0.mapA ((evalC t0).comp (hopfPsiFst m hS)) z :=
      congrFun (congrArg DFunLike.coe (hkK0.mapA_comp (hopfPsiFst m hS) (evalC t0))).symm z
    rw [hcomp] at h1
    exact h1
  have key_indep : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) yt) z = K0.mapA (augPair (Eu m) (sphToBall hS.e)) z := by
    intro z
    exact congrFun (congrArg DFunLike.coe
      (Work.KT.HopfK.augPair_K0_independent m yt (sphToBall hS.e))) z
  have hαeq : α = cls (⟨n, Q.map (coneToT (hopfKMap m hS.hmul))⟩ : Mat C(Tgt m, ℂ))
      - cls (diagMat C(Tgt m, ℂ) r n) :=
    hclsQ.symm.trans (cls_coneToT_sub m hS.hmul n r Q hQ)
  have hpsi_v : K0.mapA (hopfPsiFst m hS) (cls (⟨n, v⟩ : Mat (Kpair (Eu m))))
      = cls (⟨n, v.map (hopfPsiFst m hS)⟩ : Mat C(Tgt m, ℂ)) := by
    rw [sphKT_K0.map_cls (hopfPsiFst m hS).toRingHom hv]
    rfl
  have hpsi_diag : K0.mapA (hopfPsiFst m hS) (cls (diagMat (Kpair (Eu m)) r n))
      = cls (diagMat C(Tgt m, ℂ) r n) := by
    rw [sphKT_K0.map_cls (hopfPsiFst m hS).toRingHom (diagMat_isIdem (Kpair (Eu m)) r n),
      diagMat_map (hopfPsiFst m hS).toRingHom r n]
  have hψγ : K0.mapA (hopfPsiFst m hS) γ = α := by
    have hsub : K0.mapA (hopfPsiFst m hS)
        (cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n))
        = cls (⟨n, v.map (hopfPsiFst m hS)⟩ : Mat C(Tgt m, ℂ))
          - cls (diagMat C(Tgt m, ℂ) r n) := by
      rw [map_sub, hpsi_v, hpsi_diag]
    rw [hγdef, hsub, hcls, ← hαeq]
  have hkerγ : K0.mapA (augPair (Eu m) (sphToBall hS.e)) γ = 0 := by
    rw [← key_indep γ, ← key_eval γ, hψγ]
    exact hαred
  obtain ⟨Φ, hΦ⟩ := hk_exists_algEquiv_Kpair (EuclideanSpace ℝ (Fin (2 * m + 1))) t0 (2 * m)
    (by omega) (by simp)
  have hΦev : (augPair (Eu m) (sphToBall hS.e)).comp Φ.toAlgHom
      = (evalC t0 : C(Tgt m, ℂ) →ₐ[ℂ] ℂ) :=
    AlgHom.ext fun h => hΦ (sphToBall hS.e) (sphToBall_mem_bdry hS.e) h
  let g0 : K0 (Kpair (Eu m)) := K0.mapA Φ.toAlgHom α
  have keyΦ : ∀ w : K0 C(Tgt m, ℂ),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) (K0.mapA Φ.toAlgHom w)
        = K0.mapA (evalC t0) w := by
    intro w
    have h1 : ((K0.mapA (augPair (Eu m) (sphToBall hS.e))).comp (K0.mapA Φ.toAlgHom)) w
        = K0.mapA ((augPair (Eu m) (sphToBall hS.e)).comp Φ.toAlgHom) w :=
      congrFun (congrArg DFunLike.coe
        (hkK0.mapA_comp Φ.toAlgHom (augPair (Eu m) (sphToBall hS.e)))).symm w
    rw [hΦev] at h1
    exact h1
  have hg0_mem : K0.mapA (augPair (Eu m) (sphToBall hS.e)) g0 = 0 := by
    have h := keyΦ α
    rw [hαred] at h
    exact h
  have hunit : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 → ∃ k : ℤ, z = k • g0 := by
    intro z hz
    have hz' : K0.mapA (evalC t0) (K0.mapA (Φ.symm).toAlgHom z) = 0 := by
      have h := keyΦ (K0.mapA (Φ.symm).toAlgHom z)
      rw [hkK0.mapA_apply_symm Φ z] at h
      exact h.symm.trans hz
    obtain ⟨k, hk⟩ := hαgen _ hz'
    refine ⟨k, ?_⟩
    rw [← hkK0.mapA_apply_symm Φ z, hk, map_zsmul]
  have hgenγ : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 → ∃ k : ℤ, z = k • γ := by
    intro z hz
    obtain ⟨ℓ, hℓ⟩ := hunit z hz
    obtain ⟨ℓ', hℓ'⟩ := hunit γ hkerγ
    have hmem : K0.mapA (evalC t0) (K0.mapA (hopfPsiFst m hS) g0) = 0 := by
      have h1 : K0.mapA (evalC t0) (K0.mapA (hopfPsiFst m hS) g0)
          = K0.mapA (augPair (Eu m) yt) g0 := key_eval g0
      rw [h1, key_indep g0]
      exact hg0_mem
    obtain ⟨mm, hmm⟩ := hαgen _ hmem
    have hαeq2 : (ℓ' * mm) • α = α := by
      rw [← smul_smul, ← hmm, ← map_zsmul, ← hℓ', ← hψγ]
    have hprod : (ℓ' * mm - 1) • α = 0 := by
      rw [sub_smul, hαeq2, one_smul, sub_self]
    have h1 : ℓ' * mm - 1 = 0 := hαnz _ hprod
    have h2 : ℓ' * mm = 1 := sub_eq_zero.mp h1
    have h3 : ℓ' = 1 ∨ ℓ' = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have hg0eq : g0 = ℓ' • γ := by
      rcases h3 with h | h
      · rw [hℓ', h]; simp
      · rw [hℓ', h]; simp
    refine ⟨ℓ * ℓ', ?_⟩
    rw [hℓ, hg0eq, smul_smul]
  refine ⟨hkerγ, ?_, hgenγ⟩
  · intro k hk
    have h := congrArg (K0.mapA (hopfPsiFst m hS)) hk
    rw [map_zsmul, map_zero, hψγ] at h
    exact hαnz k h


/-- The first-slice generator statement: the `(·, e)`-slice of a collared idempotent over the
mapping cone generates the reduced `K`-theory of `Kpair (Eu m)`. -/
theorem hk_slice_gen_fst (m : ℕ) (hm : 1 ≤ m) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (t0 : Tgt m)
    (α : K0 C(Tgt m, ℂ)) (hαred : K0.mapA (evalC t0) α = 0)
    (hαnz : ∀ k : ℤ, k • α = 0 → k = 0)
    (hαgen : ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • α)
    (Q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hQ : Q * Q = Q)
    (hcap : ∀ t : Tgt m, t ∈ capTminus m →
      Q.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    (hcol : ∀ z : Ball (Eu m × Eu m), Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalD m (hopfKMap m hS.hmul) z) = diagIdemMat r n)
    (hclsQ : K0.mapA (coneToT (hopfKMap m hS.hmul))
      (cls (⟨n, Q⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
        - cls (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)) = α)
    (v : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hv : Mat.IsIdem (⟨n, v⟩ : Mat (Kpair (Eu m))))
    (hvQ : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = evalD m (hopfKMap m hS.hmul) (ptFst m hS.e y) (Q i j)) :
    K0.mapA (augPair (Eu m) (sphToBall hS.e)) (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
        - cls (diagMat (Kpair (Eu m)) r n)) = 0 ∧
      (∀ k : ℤ, k • (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n)) = 0 → k = 0) ∧
      (∀ z : K0 (Kpair (Eu m)), K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 →
        ∃ k : ℤ, z = k • (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n))) :=
  hk_slice_gen_fst_aux m hm hS n r t0 α hαred hαnz hαgen Q hQ hcap hclsQ v hv hvQ
    (hopfPsiFst_cls m hS n r Q hQ hcap v hv hvQ)

end

end Work.KT.HopfK
