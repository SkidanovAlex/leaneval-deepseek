import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.Cofibre.HopfSetup
import Submission.Work.Cofibre.continuous_hopfRaw
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.HopfK.Cone
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.hk_relprod
import Submission.Work.KT.HopfK.hk_collared
import Submission.Work.KT.HopfK.hk_cellcollar_snd
import Submission.Work.KT.HopfK.hk_cellcollar_fst
import Submission.Work.KT.HopfK.hk_diskAng_bdry
import Submission.Work.KT.HopfK.hk_diskW_class_move
import Submission.Work.KT.HopfK.hk_diskW_prod
import Submission.Work.KT.HopfK.hk_relprod_chi
import Submission.Work.KT.HopfK.hk_sliceSnd
import Submission.Work.KT.HopfK.hk_sliceFst
import Submission.Work.KT.HopfK.hk_gamma_eq
import Submission.Work.KT.HopfK.hk_bdry_reduced
import Submission.Work.KT.HopfK.hk_slice_gen
import Submission.Work.KT.HopfK.hk_slice_gen_fst
import Submission.Work.KT.ext_generator
import Submission.Work.KT.cone_exact
import Submission.Work.KT.ext_product
import Submission.Work.KT.sphere_K
import Submission.Work.KT.k0_basic

/-! Guidance from the project lead (the requester): ... -/

namespace Work.KT

open Matrix

open HopfK

noncomputable section

set_option maxHeartbeats 40000000
set_option profiler true
set_option profiler.threshold 500

/-- Applied functoriality of `K₀` along algebra maps (local copy, to avoid importing
`Submission.Work.KT.hk_Tgen`). -/
lemma hk_mapA_comp_apply {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Ring C] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA ψ (K0.mapA φ x) = K0.mapA (ψ.comp φ) x := by
  have h : K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
    show K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
    exact k0_basic.2.2.1 A B C φ.toRingHom ψ.toRingHom
  rw [h]
  rfl

theorem hopf_K (m : ℕ) (hm : 1 ≤ m) (hS : HSpace (Sph (Eu m))) :
    ∃ f : C(Sph (Eu m × Eu m), Tgt m), HopfOddK m f := by
  classical
  refine ⟨hopfKMap m hS.hmul, ?_⟩
  -- ## The base points
  have h2m : 0 < 2 * m := by omega
  let i0 : Fin (2 * m) := ⟨0, h2m⟩
  let x0 : Eu m := EuclideanSpace.single i0 (Real.sqrt 3 / 2)
  let yv : Eu m := EuclideanSpace.single i0 1
  have hx0 : ‖x0‖ = Real.sqrt 3 / 2 := by
    show ‖EuclideanSpace.single i0 (Real.sqrt 3 / 2)‖ = Real.sqrt 3 / 2
    rw [EuclideanSpace.norm_single, Real.norm_of_nonneg (by positivity)]
  have hyv : ‖yv‖ = 1 := by
    show ‖EuclideanSpace.single i0 (1 : ℝ)‖ = 1
    rw [EuclideanSpace.norm_single, norm_one]
  have hs3le : Real.sqrt 3 / 2 ≤ 1 := by
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hpair : ‖((x0, yv) : Eu m × Eu m)‖ = 1 := by
    rw [Prod.norm_def, hx0, hyv, max_eq_right hs3le]
  let y0 : Ball (Eu m × Eu m) :=
    ⟨(x0, yv), mem_closedBall_zero_iff.mpr (le_of_eq hpair)⟩
  have hy0 : y0 ∈ bdry (Eu m × Eu m) := by
    show ‖((x0, yv) : Eu m × Eu m)‖ = 1
    exact hpair
  let y0E : Ball (Eu m) := ⟨yv, mem_closedBall_zero_iff.mpr (le_of_eq hyv)⟩
  have hy0E : y0E ∈ bdry (Eu m) := by
    show ‖yv‖ = 1
    exact hyv
  let y0s : Sph (Eu m × Eu m) := sphBdry (Eu m × Eu m) ⟨y0, hy0⟩
  have hy0sval : ((y0s : Sph (Eu m × Eu m)) : Eu m × Eu m) = (x0, yv) := rfl
  let t0 : Tgt m := hopfKMap m hS.hmul y0s
  have ht0 : tgtHeight m t0 = 1 / 2 := by
    show tgtHeight m (hopfKMap m hS.hmul y0s) = 1 / 2
    rw [tgtHeight_hopfKMap]
    show hopfSnd m ((y0s : Sph (Eu m × Eu m)) : Eu m × Eu m) = 1 / 2
    rw [hy0sval, hopfSnd_of_le m (by rw [hx0, hyv]; exact hs3le), hx0, hyv, one_pow]
    rw [show (1 : ℝ) - (Real.sqrt 3 / 2) ^ 2 = (1 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  have ht0p : t0 ∈ capTplus m := by
    show tgtHeight m t0 ≥ -(1 / 2)
    rw [ht0]; norm_num
  have ht0m : t0 ∈ capTminus m := by
    show tgtHeight m t0 ≤ 1 / 2
    rw [ht0]
  -- ## The generator `α` of `K̃(S^{2m})` and the vanishing of its pull-back
  obtain ⟨⟨α, hαred, hαinf, hαgen⟩, _, _⟩ :=
    (sphere_K (EuclideanSpace ℝ (Fin (2 * m + 1))) t0 m).1 (by
      rw [finrank_euclideanSpace_fin])
  have hfin : Module.finrank ℝ (Eu m × Eu m) = 2 * (2 * m - 1) + 2 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hpullα : K0.mapA (pullAlg (hopfKMap m hS.hmul)) α = 0 := by
    have hcomp : (evalC y0s).comp (pullAlg (hopfKMap m hS.hmul)) = evalC t0 := by
      apply AlgHom.ext
      intro g
      show (pullAlg (hopfKMap m hS.hmul) g) y0s = g (hopfKMap m hS.hmul y0s)
      rfl
    have h1 : K0.mapA (evalC y0s) (K0.mapA (pullAlg (hopfKMap m hS.hmul)) α) = 0 := by
      have h2 : K0.mapA (evalC y0s) (K0.mapA (pullAlg (hopfKMap m hS.hmul)) α)
          = K0.mapA ((evalC y0s).comp (pullAlg (hopfKMap m hS.hmul))) α :=
        hk_mapA_comp_apply (pullAlg (hopfKMap m hS.hmul)) (evalC y0s) α
      rw [h2, hcomp, hαred]
    exact (sphere_K (Eu m × Eu m) y0s (2 * m - 1)).2 hfin _ h1
  -- ## The class `a` in the mapping cone
  haveI : Nonempty (Tgt m) := ⟨southPt m⟩
  obtain ⟨a, ha⟩ := (cone_exact (Eu m × Eu m) (Tgt m) (hopfKMap m hS.hmul) y0 hy0).2.1 α 0 (by
    simpa using hpullα)
  have haug : K0.mapA (augCone (hopfKMap m hS.hmul) t0) a = 0 := by
    have h2 : K0.mapA ((evalC t0).comp (coneToT (hopfKMap m hS.hmul))) a
        = K0.mapA (evalC t0) (K0.mapA (coneToT (hopfKMap m hS.hmul)) a) :=
      (hk_mapA_comp_apply (coneToT (hopfKMap m hS.hmul)) (evalC t0) a).symm
    show K0.mapA ((evalC t0).comp (coneToT (hopfKMap m hS.hmul))) a = 0
    rw [h2, ha, hαred]
  -- ## The collared representatives
  obtain ⟨n, r, p, q, hp, hq, hpa, hqa, hpc, hqc, hpcoll, hqcoll⟩ :=
    hk_collared m hm hS.hmul t0 ht0p ht0m a haug
  -- ## The cell collars
  have hδpos : (0 : ℝ) < 1 - Real.sqrt 3 / 2 := by
    have h3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have hδle : Real.sqrt 3 / 2 ≤ 1 - (1 - Real.sqrt 3 / 2) := le_of_eq (by ring)
  have hpc' := hk_cellcollar_snd m hS.hmul n r (1 - Real.sqrt 3 / 2) hδle p hpc hpcoll
  have hqc' := hk_cellcollar_fst m hS.hmul n r (1 - Real.sqrt 3 / 2) hδle q hqc hqcoll
  -- ## The disk side of the relative product
  obtain ⟨χ, hχ, H, hZidem, hZsize, hZrel⟩ :=
    hk_relprod_chi m hS.hmul n r (1 - Real.sqrt 3 / 2) hδpos p q hp hq hpc' hqc' hpc hqc y0 hy0
  let P : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)) := coneCell (hopfKMap m hS.hmul) p
  let Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)) := coneCell (hopfKMap m hS.hmul) q
  have hPidem : P * P = P := by
    show coneCell (hopfKMap m hS.hmul) p * coneCell (hopfKMap m hS.hmul) p = coneCell (hopfKMap m hS.hmul) p
    rw [← Matrix.map_mul, hp]
  have hQidem : Q * Q = Q := by
    show coneCell (hopfKMap m hS.hmul) q * coneCell (hopfKMap m hS.hmul) q = coneCell (hopfKMap m hS.hmul) q
    rw [← Matrix.map_mul, hq]
  have hPc : ∀ z : Ball (Eu m × Eu m), 1 - (1 - Real.sqrt 3 / 2) ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n := by
    intro z hz
    show (coneCell (hopfKMap m hS.hmul) p).map (evalC z) = diagIdemMat r n
    rw [coneCell_mul_apply]
    exact hpc' z hz
  have hQc : ∀ z : Ball (Eu m × Eu m), 1 - (1 - Real.sqrt 3 / 2) ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n := by
    intro z hz
    show (coneCell (hopfKMap m hS.hmul) q).map (evalC z) = diagIdemMat r n
    rw [coneCell_mul_apply]
    exact hqc' z hz
  let ν : K0 (Kpair (Eu m × Eu m)) :=
    cls (hopfDiskZ m n r χ P Q H)
      - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))
  have hνred : K0.mapA (augPair (Eu m × Eu m) y0) ν = 0 :=
    hk_bdry_reduced m hS.hmul n r (1 - Real.sqrt 3 / 2) χ hχ P Q hPidem hQidem hPc hQc
      (le_of_eq (by ring)) H y0 hy0
  have hνrel : K0.mapA (relToCone (hopfKMap m hS.hmul) y0 hy0) ν =
      cls (Mat.sum (Mat.kron (⟨n, p⟩ : Mat (coneAlg (hopfKMap m hS.hmul))) ⟨n, q⟩)
        (Mat.kron (coneDiag m (hopfKMap m hS.hmul) r n) (coneDiag m (hopfKMap m hS.hmul) r n))) -
      cls (Mat.sum (Mat.kron (⟨n, p⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
          (coneDiag m (hopfKMap m hS.hmul) r n))
        (Mat.kron (coneDiag m (hopfKMap m hS.hmul) r n) ⟨n, q⟩)) := hZrel
  -- the relative square is the class of `ν`
  have hisk0 : ∀ μ'' : K0 (coneAlg (hopfKMap m hS.hmul)) →+ K0 (coneAlg (hopfKMap m hS.hmul)) →+
      K0 (coneAlg (hopfKMap m hS.hmul)), IsK0Mul μ'' →
      μ'' a a = K0.mapA (relToCone (hopfKMap m hS.hmul) y0 hy0) ν := by
    intro μ'' hμ''
    rw [hνrel]
    exact isk0Mul_sq_eq (coneAlg_comm m (hopfKMap m hS.hmul)) a μ'' hμ''
      (⟨n, p⟩ : Mat (coneAlg (hopfKMap m hS.hmul))) ⟨n, q⟩ (coneDiag m (hopfKMap m hS.hmul) r n)
      hp hq (coneDiag_isIdem m (hopfKMap m hS.hmul) r n) hpa hqa
  -- ## The slices
  obtain ⟨u, hu, huval, huP, huRed⟩ :=
    hk_sliceSnd m hS.hmul n r hS.e y0E hy0E p hp hpc
  obtain ⟨v, hv, hvval, hvQ, hvRed⟩ :=
    hk_sliceFst m hS.hmul n r hS.e y0E hy0E q hq hqc
  let s : K0 (Kpair (Eu m)) :=
    cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)
  let t : K0 (Kpair (Eu m)) :=
    cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)
  have hs : K0.mapA (augPair (Eu m) y0E) s = 0 := huRed
  have ht : K0.mapA (augPair (Eu m) y0E) t = 0 := hvRed
  have hsg : ∀ z, K0.mapA (augPair (Eu m) y0E) z = 0 → ∃ k : ℤ, z = k • s := by
    have hy0E' : augPair (Eu m) (HopfK.sphToBall hS.e) = augPair (Eu m) y0E := by
      ext g
      exact g.2 (HopfK.sphToBall hS.e) (sphToBall_mem_bdry hS.e) y0E hy0E
    have hαcls : K0.mapA (coneToT (hopfKMap m hS.hmul))
        (cls (⟨n, p⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
          - cls (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)) = α := by
      rw [show (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)
          = coneDiag m (hopfKMap m hS.hmul) r n from rfl]
      rw [hpa]; exact ha
    have huP' : ∀ (i j : Fin n) (y : Ball (Eu m)),
        ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
          = evalD m (hopfKMap m hS.hmul) (ptSnd m hS.e y) (p i j) := by
      intro i j y
      rw [huval]
      rfl
    have hcol' : ∀ z : Ball (Eu m × Eu m), Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).2‖ →
        p.map (evalD m (hopfKMap m hS.hmul) z) = diagIdemMat r n := by
      intro z hz
      exact hpc' z (by linarith [hz])
    have hgen' := (hk_slice_gen m hm hS n r t0 α hαred hαinf hαgen p hp hpc hcol'
      hαcls u hu huP').2.2
    intro z hz
    have hz' : K0.mapA (augPair (Eu m) (HopfK.sphToBall hS.e)) z = 0 := by
      rw [hy0E']; exact hz
    exact hgen' z hz'
  have htg : ∀ z, K0.mapA (augPair (Eu m) y0E) z = 0 → ∃ k : ℤ, z = k • t := by
    have hy0E' : augPair (Eu m) (HopfK.sphToBall hS.e) = augPair (Eu m) y0E := by
      ext g
      exact g.2 (HopfK.sphToBall hS.e) (sphToBall_mem_bdry hS.e) y0E hy0E
    have hαcls : K0.mapA (coneToT (hopfKMap m hS.hmul))
        (cls (⟨n, q⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
          - cls (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)) = α := by
      rw [show (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)
          = coneDiag m (hopfKMap m hS.hmul) r n from rfl]
      rw [hqa]; exact ha
    have hvQ' : ∀ (i j : Fin n) (y : Ball (Eu m)),
        ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
          = evalD m (hopfKMap m hS.hmul) (ptFst m hS.e y) (q i j) := by
      intro i j y
      rw [hvval]
      rfl
    have hcol' : ∀ z : Ball (Eu m × Eu m), Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).1‖ →
        q.map (evalD m (hopfKMap m hS.hmul) z) = diagIdemMat r n := by
      intro z hz
      exact hqc' z (by linarith [hz])
    have hgen' := (hk_slice_gen_fst m hm hS n r t0 α hαred hαinf hαgen q hq hqc hcol'
      hαcls v hv hvQ').2.2
    intro z hz
    have hz' : K0.mapA (augPair (Eu m) (HopfK.sphToBall hS.e)) z = 0 := by
      rw [hy0E']; exact hz
    exact hgen' z hz'
  -- ## The product form of the class of `ν`
  have hPsh : P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom
      = (fun i j => ((pullSnd (Eu m) (Eu m) (u i j) : prodAlg (Eu m) (Eu m)) :
          C(Ball (Eu m × Eu m), ℂ))) := by
    show (coneCell (hopfKMap m hS.hmul) p).map (pullAlg (shiftSnd m hS.e 1)).toRingHom
      = (fun i j => ((pullSnd (Eu m) (Eu m) (u i j) : prodAlg (Eu m) (Eu m)) :
          C(Ball (Eu m × Eu m), ℂ)))
    exact huP
  have hQsh : Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom
      = (fun i j => ((pullFst (Eu m) (Eu m) (v i j) : prodAlg (Eu m) (Eu m)) :
          C(Ball (Eu m × Eu m), ℂ))) := by
    show (coneCell (hopfKMap m hS.hmul) q).map (pullAlg (shiftFst m hS.e 1)).toRingHom
      = (fun i j => ((pullFst (Eu m) (Eu m) (v i j) : prodAlg (Eu m) (Eu m)) :
          C(Ball (Eu m × Eu m), ℂ)))
    exact hvQ
  have hPshidem : (P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom)
      * (P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom)
      = P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom := by
    rw [← Matrix.map_mul, hPidem]
  have hQshidem : (Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom)
      * (Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom)
      = Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom := by
    rw [← Matrix.map_mul, hQidem]
  have hPshc := hkDM_collar_snd m hS.e (1 - Real.sqrt 3 / 2) 1 P hPc
  have hQshc := hkDM_collar_fst m hS.e (1 - Real.sqrt 3 / 2) 1 Q hQc
  let Hd : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r (diskAng m) (P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom)
        (Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom) i j ∈ Kpair (Eu m × Eu m) :=
    hk_diskW_mem_Kpair m hS.hmul n r (1 - Real.sqrt 3 / 2) (diskAng m) (hk_diskAng_bdry m hS.hmul)
      _ _ hPshidem hQshidem hPshc hQshc (le_of_eq (by ring))
  have hmove : cls (hopfDiskZ m n r χ P Q H) = cls (hopfDiskZ m n r (diskAng m)
      (P.map (pullAlg (shiftSnd m hS.e 1)).toRingHom)
      (Q.map (pullAlg (shiftFst m hS.e 1)).toRingHom) Hd) :=
    hk_diskW_class_move m hS.hmul n r (1 - Real.sqrt 3 / 2) (le_of_eq (by ring)) hS.e P Q
      hPidem hQidem hPc hQc χ (diskAng m) hχ (hk_diskAng_bdry m hS.hmul) H Hd
  obtain ⟨μ', hS.hmul', hprod⟩ :=
    hk_diskW_prod m hS.e n r _ _ u v hu hv hPsh hQsh Hd
  have hsmash : K0.mapA (smashIncl (Eu m) (Eu m)) ν =
      μ' (K0.mapA (pullSnd (Eu m) (Eu m)) s) (K0.mapA (pullFst (Eu m) (Eu m)) t) := by
    show K0.mapA (smashIncl (Eu m) (Eu m))
      (cls (hopfDiskZ m n r χ P Q H)
        - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))) =
      μ' (K0.mapA (pullSnd (Eu m) (Eu m))
            (cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)))
        (K0.mapA (pullFst (Eu m) (Eu m))
            (cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)))
    rw [hmove]
    exact hprod
  have hsmashAll : ∀ μ'' : K0 (prodAlg (Eu m) (Eu m)) →+ K0 (prodAlg (Eu m) (Eu m)) →+
      K0 (prodAlg (Eu m) (Eu m)), IsK0Mul μ'' →
      K0.mapA (smashIncl (Eu m) (Eu m)) ν =
        μ'' (K0.mapA (pullSnd (Eu m) (Eu m)) s) (K0.mapA (pullFst (Eu m) (Eu m)) t) := by
    intro μ'' hμ''
    rw [ep_isK0Mul_unique μ'' μ' hμ'' hS.hmul']
    exact hsmash
  -- ## The external product and the generator `ν`
  obtain ⟨μx, hμx⟩ := (ext_product (Eu m) (Eu m) y0E hy0E y0E hy0E y0 hy0).1
  have hinjSm : ∀ w, K0.mapA (augPair (Eu m × Eu m) y0) w = 0 →
      K0.mapA (smashIncl (Eu m) (Eu m)) w = 0 → w = 0 :=
    (ext_product (Eu m) (Eu m) y0E hy0E y0E hy0E y0 hy0).2
  have hνgen : ν = μx t s :=
    hk_gamma_eq m y0E y0 μx hμx hinjSm s t ν hs ht hνred hsmashAll
  have hgen : ∀ z, K0.mapA (augPair (Eu m × Eu m) y0) z = 0 → ∃ k : ℤ, z = k • ν := by
    intro z hz
    obtain ⟨k, hk⟩ := ext_generator (Eu m) (Eu m) y0E hy0E y0E hy0E y0 hy0 m m
      (by rw [finrank_euclideanSpace_fin]) (by rw [finrank_euclideanSpace_fin])
      μx hμx t s ht htg hs hsg z hz
    exact ⟨k, by rw [hk, hνgen]⟩
  -- ## Conclusion
  exact ⟨t0, y0, hy0, a, ν, 1, odd_one, haug, hνred, hgen, fun μ'' hμ'' => by
    rw [hisk0 μ'' hμ'', one_zsmul]⟩

end

end Work.KT
