import Mathlib
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.hk_relprod
import Submission.Work.KT.bott_aux
import Submission.Work.KT.HopfK.hk_diskW_map
import Submission.Work.KT.HopfK.hk_diskW_class_prod

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 4000000

lemma hk_diskAng_eq_of (m : ℕ) {z z' : Ball (Eu m × Eu m)}
    (h1 : ‖(z : Eu m × Eu m).1‖ = ‖(z' : Eu m × Eu m).1‖)
    (h2 : ‖(z : Eu m × Eu m).2‖ = ‖(z' : Eu m × Eu m).2‖) : diskAng m z = diskAng m z' := by
  rw [diskAng_apply, diskAng_apply, h1, h2]

lemma hk_diskCos_mem_prodAlg (m : ℕ) : diskCos (diskAng m) ∈ prodAlg (Eu m) (Eu m) := by
  constructor
  · intro z z' h1 h2 h3
    show (Real.cos (Real.pi / 2 * diskAng m z) : ℂ) = (Real.cos (Real.pi / 2 * diskAng m z') : ℂ)
    rw [hk_diskAng_eq_of m (h1.trans h2.symm) (by rw [h3])]
  · intro z z' h1 h2 h3
    show (Real.cos (Real.pi / 2 * diskAng m z) : ℂ) = (Real.cos (Real.pi / 2 * diskAng m z') : ℂ)
    rw [hk_diskAng_eq_of m (by rw [h3]) (h1.trans h2.symm)]

lemma hk_diskSin_mem_prodAlg (m : ℕ) : diskSin (diskAng m) ∈ prodAlg (Eu m) (Eu m) := by
  constructor
  · intro z z' h1 h2 h3
    show (Real.sin (Real.pi / 2 * diskAng m z) : ℂ) = (Real.sin (Real.pi / 2 * diskAng m z') : ℂ)
    rw [hk_diskAng_eq_of m (h1.trans h2.symm) (by rw [h3])]
  · intro z z' h1 h2 h3
    show (Real.sin (Real.pi / 2 * diskAng m z) : ℂ) = (Real.sin (Real.pi / 2 * diskAng m z') : ℂ)
    rw [hk_diskAng_eq_of m (by rw [h3]) (h1.trans h2.symm)]

theorem hk_diskW_prod (m : ℕ) (e₀ : Sph (Eu m)) (n r : ℕ)
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (u v : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hu : Mat.IsIdem (⟨n, u⟩ : Mat (Kpair (Eu m))))
    (hv : Mat.IsIdem (⟨n, v⟩ : Mat (Kpair (Eu m))))
    (hPu : P = fun i j => ((pullSnd (Eu m) (Eu m) (u i j) : prodAlg (Eu m) (Eu m)) :
      C(Ball (Eu m × Eu m), ℂ)))
    (hQv : Q = fun i j => ((pullFst (Eu m) (Eu m) (v i j) : prodAlg (Eu m) (Eu m)) :
      C(Ball (Eu m × Eu m), ℂ)))
    (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r (diskAng m) P Q i j ∈ Kpair (Eu m × Eu m)) :
    ∃ μ' : K0 (prodAlg (Eu m) (Eu m)) →+ K0 (prodAlg (Eu m) (Eu m)) →+
        K0 (prodAlg (Eu m) (Eu m)),
      IsK0Mul (A := prodAlg (Eu m) (Eu m)) μ' ∧
      K0.mapA (smashIncl (Eu m) (Eu m))
          (cls (hopfDiskZ m n r (diskAng m) P Q H)
            - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))) =
        μ' (K0.mapA (pullSnd (Eu m) (Eu m)) (cls (⟨n, u⟩ : Mat (Kpair (Eu m)))
              - cls (diagMat (Kpair (Eu m)) r n)))
           (K0.mapA (pullFst (Eu m) (Eu m)) (cls (⟨n, v⟩ : Mat (Kpair (Eu m)))
              - cls (diagMat (Kpair (Eu m)) r n))) := by
  classical
  let Pc : Matrix (Fin n) (Fin n) (prodAlg (Eu m) (Eu m)) := fun i j => pullSnd (Eu m) (Eu m) (u i j)
  let Qc : Matrix (Fin n) (Fin n) (prodAlg (Eu m) (Eu m)) := fun i j => pullFst (Eu m) (Eu m) (v i j)
  let Ec : Matrix (Fin n) (Fin n) (prodAlg (Eu m) (Eu m)) :=
    matConst (prodAlg (Eu m) (Eu m)) (diagIdemMat r n)
  let cR : prodAlg (Eu m) (Eu m) := ⟨diskCos (diskAng m), hk_diskCos_mem_prodAlg m⟩
  let sR : prodAlg (Eu m) (Eu m) := ⟨diskSin (diskAng m), hk_diskSin_mem_prodAlg m⟩
  let φA : prodAlg (Eu m) (Eu m) →+* C(Ball (Eu m × Eu m), ℂ) :=
    (prodAlg (Eu m) (Eu m)).val.toRingHom
  have hcR : φA cR = diskCos (diskAng m) := rfl
  have hsR : φA sR = diskSin (diskAng m) := rfl
  have hPc_map : Pc.map φA = P := by
    rw [hPu]; ext i j; rfl
  have hQc_map : Qc.map φA = Q := by
    rw [hQv]; ext i j; rfl
  have hEc_map : Ec.map φA = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n) := by
    show ((diagIdemMat r n).map (algebraMap ℂ (prodAlg (Eu m) (Eu m)))).map ⇑φA
      = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)
    rw [Matrix.map_map]
    congr 1
  have hPc_idem : Pc * Pc = Pc := by
    have h := Mat.map_idem (pullSnd (Eu m) (Eu m)).toRingHom hu
    have hmat : (⟨n, Pc⟩ : Mat (prodAlg (Eu m) (Eu m))) =
        Mat.map (pullSnd (Eu m) (Eu m)).toRingHom (⟨n, u⟩ : Mat (Kpair (Eu m))) := rfl
    rwa [← hmat] at h
  have hQc_idem : Qc * Qc = Qc := by
    have h := Mat.map_idem (pullFst (Eu m) (Eu m)).toRingHom hv
    have hmat : (⟨n, Qc⟩ : Mat (prodAlg (Eu m) (Eu m))) =
        Mat.map (pullFst (Eu m) (Eu m)).toRingHom (⟨n, v⟩ : Mat (Kpair (Eu m))) := rfl
    rwa [← hmat] at h
  have hEc_idem : Ec * Ec = Ec := by
    show matConst (prodAlg (Eu m) (Eu m)) (diagIdemMat r n)
      * matConst (prodAlg (Eu m) (Eu m)) (diagIdemMat r n)
      = matConst (prodAlg (Eu m) (Eu m)) (diagIdemMat r n)
    rw [← matConst_mul]
    congr 1
    exact diagMat_isIdem ℂ r n
  have hcs : cR * cR + sR * sR = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one]
    rw [show ((cR : prodAlg (Eu m) (Eu m)) : C(Ball (Eu m × Eu m), ℂ)) = diskCos (diskAng m) from rfl,
      show ((sR : prodAlg (Eu m) (Eu m)) : C(Ball (Eu m × Eu m), ℂ)) = diskSin (diskAng m) from rfl]
    exact diskCos_sq_add_diskSin_sq (diskAng m)
  have hWmap : (diskW Pc Qc Ec cR sR).map φA = hopfDiskW m n r (diskAng m) P Q := by
    rw [hk_diskW_map φA Pc Qc Ec cR sR]
    rw [hPc_map, hQc_map, hEc_map, hcR, hsR]
    rfl
  have hP_idem : P * P = P := by
    rw [← hPc_map, ← Matrix.map_mul, hPc_idem]
  have hQ_idem : Q * Q = Q := by
    rw [← hQc_map, ← Matrix.map_mul, hQc_idem]
  have hW_idem : hopfDiskW m n r (diskAng m) P Q * hopfDiskW m n r (diskAng m) P Q
      = hopfDiskW m n r (diskAng m) P Q := by
    apply diskW_idem
    · exact hP_idem
    · exact hQ_idem
    · rw [← matConst_mul]; congr 1; exact diagMat_isIdem ℂ r n
    · exact diskCos_sq_add_diskSin_sq (diskAng m)
  let Zw : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (Kpair (Eu m × Eu m)) :=
    fun i j => ⟨hopfDiskW m n r (diskAng m) P Q i j, H i j⟩
  let Z : Mat (Kpair (Eu m × Eu m)) := ⟨(n * n + n * n) + (n * n + n * n), Zw⟩
  have hZeq : hopfDiskZ m n r (diskAng m) P Q H = Z := rfl
  have hZmat : Zw.map ((Kpair (Eu m × Eu m)).val.toRingHom)
      = hopfDiskW m n r (diskAng m) P Q := by
    apply Matrix.ext
    intro i j
    rfl
  have hZidem : Z.IsIdem := by
    show Zw * Zw = Zw
    refine Matrix.map_injective (f := ⇑((Kpair (Eu m × Eu m)).val.toRingHom)) ?_ ?_
    · intro x y h; exact Subtype.ext h
    · change (Zw * Zw).map ⇑((Kpair (Eu m × Eu m)).val.toRingHom)
        = Zw.map ⇑((Kpair (Eu m × Eu m)).val.toRingHom)
      rw [Matrix.map_mul, hZmat, hW_idem]
  have hentry : ∀ (i j : Fin ((n * n + n * n) + (n * n + n * n))),
      (smashIncl (Eu m) (Eu m)) (Zw i j) = diskW Pc Qc Ec cR sR i j := by
    intro i j
    apply Subtype.ext
    have hij : ((diskW Pc Qc Ec cR sR) i j : C(Ball (Eu m × Eu m), ℂ))
        = hopfDiskW m n r (diskAng m) P Q i j := by
      have h := congrFun (congrFun hWmap i) j
      rwa [Matrix.map_apply] at h
    rw [hij]
    rfl
  have hmatZ : Zw.map (smashIncl (Eu m) (Eu m)).toRingHom = diskW Pc Qc Ec cR sR := by
    apply Matrix.ext
    intro i j
    exact hentry i j
  have hmapZ : Mat.map (smashIncl (Eu m) (Eu m)).toRingHom Z
      = (⟨(n * n + n * n) + (n * n + n * n), diskW Pc Qc Ec cR sR⟩ :
          Mat (prodAlg (Eu m) (Eu m))) := by
    show (⟨(n * n + n * n) + (n * n + n * n),
        Zw.map (smashIncl (Eu m) (Eu m)).toRingHom⟩ : Mat (prodAlg (Eu m) (Eu m))) = _
    rw [hmatZ]
  have hsmashZ : K0.mapA (smashIncl (Eu m) (Eu m)) (cls Z)
      = cls (⟨(n * n + n * n) + (n * n + n * n), diskW Pc Qc Ec cR sR⟩ :
          Mat (prodAlg (Eu m) (Eu m))) := by
    change K0.map (smashIncl (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (smashIncl (Eu m) (Eu m)).toRingHom hZidem, hmapZ]
  have hsmashD : K0.mapA (smashIncl (Eu m) (Eu m))
        (cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n))))
      = cls (diagMat (prodAlg (Eu m) (Eu m)) (2 * (n * n)) (4 * (n * n))) := by
    change K0.map (smashIncl (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (smashIncl (Eu m) (Eu m)).toRingHom
      (diagMat_isIdem (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))]
    congr 1
    exact Mat.diagMat_map (smashIncl (Eu m) (Eu m)).toRingHom (2 * (n * n)) (4 * (n * n))
  have hpullSnd_u : K0.mapA (pullSnd (Eu m) (Eu m)) (cls (⟨n, u⟩ : Mat (Kpair (Eu m))))
      = cls (⟨n, Pc⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    change K0.map (pullSnd (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (pullSnd (Eu m) (Eu m)).toRingHom hu]
    congr 1
  have hpullSnd_d : K0.mapA (pullSnd (Eu m) (Eu m)) (cls (diagMat (Kpair (Eu m)) r n))
      = cls (⟨n, Ec⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    change K0.map (pullSnd (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (pullSnd (Eu m) (Eu m)).toRingHom (diagMat_isIdem (Kpair (Eu m)) r n)]
    congr 1
    rw [Mat.diagMat_map (pullSnd (Eu m) (Eu m)).toRingHom r n]
    exact (Mat.diagMat_map (algebraMap ℂ (prodAlg (Eu m) (Eu m))) r n).symm
  have hpullFst_v : K0.mapA (pullFst (Eu m) (Eu m)) (cls (⟨n, v⟩ : Mat (Kpair (Eu m))))
      = cls (⟨n, Qc⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    change K0.map (pullFst (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (pullFst (Eu m) (Eu m)).toRingHom hv]
    congr 1
  have hpullFst_d : K0.mapA (pullFst (Eu m) (Eu m)) (cls (diagMat (Kpair (Eu m)) r n))
      = cls (⟨n, Ec⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    change K0.map (pullFst (Eu m) (Eu m)).toRingHom _ = _
    rw [K0.map_cls (pullFst (Eu m) (Eu m)).toRingHom (diagMat_isIdem (Kpair (Eu m)) r n)]
    congr 1
    rw [Mat.diagMat_map (pullFst (Eu m) (Eu m)).toRingHom r n]
    exact (Mat.diagMat_map (algebraMap ℂ (prodAlg (Eu m) (Eu m))) r n).symm
  have hA : K0.mapA (pullSnd (Eu m) (Eu m))
        (cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n))
      = cls (⟨n, Pc⟩ : Mat (prodAlg (Eu m) (Eu m)))
        - cls (⟨n, Ec⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    rw [map_sub, hpullSnd_u, hpullSnd_d]
  have hB : K0.mapA (pullFst (Eu m) (Eu m))
        (cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n))
      = cls (⟨n, Qc⟩ : Mat (prodAlg (Eu m) (Eu m)))
        - cls (⟨n, Ec⟩ : Mat (prodAlg (Eu m) (Eu m))) := by
    rw [map_sub, hpullFst_v, hpullFst_d]
  have hcommR : ∀ x y : prodAlg (Eu m) (Eu m), x * y = y * x := by
    intro x y
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    exact mul_comm _ _
  obtain ⟨μ, hμ⟩ := ba_exists_isK0Mul (prodAlg (Eu m) (Eu m)) hcommR
  refine ⟨μ, hμ, ?_⟩
  rw [show hopfDiskZ m n r (diskAng m) P Q H = Z from rfl]
  rw [map_sub, hsmashZ, hsmashD,
    hk_diskW_class_prod (A := prodAlg (Eu m) (Eu m)) n Pc Qc Ec
      hPc_idem hQc_idem hEc_idem hcs μ hμ,
    ← hA, ← hB]

end

end Work.KT.HopfK
