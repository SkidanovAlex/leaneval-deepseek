import Mathlib
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.HopfK.hk_diskW_map
import Submission.Work.KT.HopfK.hk_diskW_base_oneBlk
import Submission.Work.KT.hk_relprod

set_option maxHeartbeats 4000000

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-!
# The disk side of the relative product, with a prescribed angle `χ`

This is `Work.KT.hk_relprod` with the rotation angle `χ` made explicit as an *existential* whose
boundary values are fixed: `χ` restricts to `chiB m ∘ hopfKMap m μ` on `∂D`.  The point is that
for any such `χ` the cell part of the cone-level `W`-matrix *is* the disk-level `hopfDiskW`, and
the base part is the constant `oneBlk` (because `p`, `q` are the trivial idempotent on the two
caps); the mapping-cone relation `cell = base ∘ f` then forces the cell part to be constant on the
boundary sphere, so `hopfDiskZ` is a well-defined element of `Mat (Kpair (Eu m × Eu m))`.
-/

/-- `cos(πχ/2)` as an element of the mapping cone `C_f`: base part `hkCos m`, cell part
`diskCos χ`; these agree on the sphere because `χ` extends `chiB m ∘ f` there. -/
def chiHatCos (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    coneAlg (hopfKMap m μ) :=
  ⟨(hkCos m, diskCos χ), by
    intro y hy
    show (Real.cos (Real.pi / 2 * χ y) : ℂ)
      = hkCos m (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [hχ y hy]
    rfl⟩

/-- `sin(πχ/2)` as an element of the mapping cone `C_f`. -/
def chiHatSin (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    coneAlg (hopfKMap m μ) :=
  ⟨(hkSin m, diskSin χ), by
    intro y hy
    show (Real.sin (Real.pi / 2 * χ y) : ℂ)
      = hkSin m (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [hχ y hy]
    rfl⟩

@[simp] lemma chiHatCos_val (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    ((chiHatCos m μ χ hχ : coneAlg (hopfKMap m μ)) :
      C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) = (hkCos m, diskCos χ) := rfl

@[simp] lemma chiHatSin_val (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    ((chiHatSin m μ χ hχ : coneAlg (hopfKMap m μ)) :
      C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) = (hkSin m, diskSin χ) := rfl

lemma coneToT_chiHatCos (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    coneToT (hopfKMap m μ) (chiHatCos m μ χ hχ) = hkCos m := rfl

lemma coneToT_chiHatSin (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    coneToT (hopfKMap m μ) (chiHatSin m μ χ hχ) = hkSin m := rfl

/-- `cos² + sin² = 1` in the mapping cone. -/
lemma chiHatCos_sq_add_chiHatSin_sq (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) :
    chiHatCos m μ χ hχ * chiHatCos m μ χ hχ
      + chiHatSin m μ χ hχ * chiHatSin m μ χ hχ = 1 := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show hkCos m * hkCos m + hkSin m * hkSin m = 1
    exact hkCos_sq_add_hkSin_sq m
  · show diskCos χ * diskCos χ + diskSin χ * diskSin χ = 1
    exact diskCos_sq_add_diskSin_sq χ

theorem hk_relprod_chi (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (p q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))) (hp : p * p = p) (hq : q * q = q)
    (hpc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      p.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n)
    (hqc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      q.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n)
    (hpb : ∀ t : Tgt m, t ∈ capTplus m →
      p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (hqb : ∀ t : Tgt m, t ∈ capTminus m →
      q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (y0 : Ball (Eu m × Eu m)) (hy0 : y0 ∈ bdry (Eu m × Eu m)) :
    ∃ (χ : C(Ball (Eu m × Eu m), ℝ))
      (_ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
        χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
      (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
        hopfDiskW m n r χ (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q) i j
          ∈ Kpair (Eu m × Eu m)),
      Mat.IsIdem (hopfDiskZ m n r χ (coneCell (hopfKMap m μ) p)
        (coneCell (hopfKMap m μ) q) H) ∧
      (hopfDiskZ m n r χ (coneCell (hopfKMap m μ) p)
        (coneCell (hopfKMap m μ) q) H).1 = 4 * (n * n) ∧
      K0.mapA (relToCone (hopfKMap m μ) y0 hy0)
          (cls (hopfDiskZ m n r χ (coneCell (hopfKMap m μ) p)
              (coneCell (hopfKMap m μ) q) H)
            - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))) =
        cls (Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩)
          (Mat.kron (coneDiag m (hopfKMap m μ) r n) (coneDiag m (hopfKMap m μ) r n))) -
        cls (Mat.sum (Mat.kron ⟨n, p⟩ (coneDiag m (hopfKMap m μ) r n))
          (Mat.kron (coneDiag m (hopfKMap m μ) r n) ⟨n, q⟩)) := by
  classical
  letI : CommRing (coneAlg (hopfKMap m μ)) :=
    { (inferInstance : Ring (coneAlg (hopfKMap m μ))) with
      mul_comm := coneAlg_comm m (hopfKMap m μ) }
  -- ## 1. The angle `χ`: any continuous extension of `chiB m ∘ f` to the closed ball
  have hclosed : IsClosed (bdry (Eu m × Eu m)) :=
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const
  let phiR : C(bdry (Eu m × Eu m), ℝ) :=
    ⟨fun y => chiB m (hopfKMap m μ (sphBdry (Eu m × Eu m) y)),
      (chiB m).continuous.comp ((hopfKMap m μ).continuous.comp (sphBdry _).continuous)⟩
  obtain ⟨χ, hχres⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ) hclosed phiR
  have hχbdry : ∀ y : bdry (Eu m × Eu m), χ y = phiR y := by
    intro y
    have h := congrArg (fun g : C(bdry (Eu m × Eu m), ℝ) => g y) hχres
    rwa [ContinuousMap.restrict_apply] at h
  have hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
    intro z hz
    have h := hχbdry ⟨z, hz⟩
    simpa [phiR, sphBdry] using h
  -- ## 2. The two elements of the mapping cone
  let cA : coneAlg (hopfKMap m μ) := chiHatCos m μ χ hχ
  let sA : coneAlg (hopfKMap m μ) := chiHatSin m μ χ hχ
  have hcsA : cA * cA + sA * sA = 1 := chiHatCos_sq_add_chiHatSin_sq m μ χ hχ
  -- ## 3. The cone-level `W`-matrix
  let E : Mat (coneAlg (hopfKMap m μ)) := coneDiag m (hopfKMap m μ) r n
  have hEidem : Mat.IsIdem E := coneDiag_isIdem m (hopfKMap m μ) r n
  let ZAm : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (coneAlg (hopfKMap m μ)) :=
    diskW p q E.2 cA sA
  let ZA : Mat (coneAlg (hopfKMap m μ)) := ⟨(n * n + n * n) + (n * n + n * n), ZAm⟩
  have hZAidem : Mat.IsIdem ZA := diskW_idem p q E.2 hp hq hEidem hcsA
  let Q1 : Mat (coneAlg (hopfKMap m μ)) :=
    Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩) (Mat.kron E E)
  let Q2 : Mat (coneAlg (hopfKMap m μ)) :=
    Mat.sum (Mat.kron ⟨n, p⟩ E) (Mat.kron E ⟨n, q⟩)
  have hQ1def : (⟨n * n + n * n, diskQ1 p q E.2⟩ : Mat (coneAlg (hopfKMap m μ))) = Q1 := rfl
  have hQ2def : (⟨n * n + n * n, diskQ2 p q E.2⟩ : Mat (coneAlg (hopfKMap m μ))) = Q2 := rfl
  have hclass : cls ZA - cls (diagMat (coneAlg (hopfKMap m μ)) (n * n + n * n)
      ((n * n + n * n) + (n * n + n * n))) = cls Q1 - cls Q2 := by
    have h := diskW_class p q E.2 hp hq hEidem hcsA
    rw [show ZA = (⟨(n * n + n * n) + (n * n + n * n), diskW p q E.2 cA sA⟩ :
        Mat (coneAlg (hopfKMap m μ))) from rfl, h, hQ1def, hQ2def]
    abel
  -- ## 4. The cell part is the disk-level `W`-matrix
  let φc : coneAlg (hopfKMap m μ) →+* C(Ball (Eu m × Eu m), ℂ) :=
    ((AlgHom.snd ℂ C(Tgt m, ℂ) C(Ball (Eu m × Eu m), ℂ)).comp
      (coneAlg (hopfKMap m μ)).val).toRingHom
  have hcellW : ZAm.map φc
      = hopfDiskW m n r χ (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q) := by
    have h := hk_diskW_map φc p q E.2 cA sA
    rw [show ZAm = diskW p q E.2 cA sA from rfl, h]
    show diskW (p.map φc) (q.map φc) (E.2.map φc) (φc cA) (φc sA)
      = diskW (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q)
          (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)) (diskCos χ) (diskSin χ)
    rw [show p.map φc = coneCell (hopfKMap m μ) p from rfl,
      show q.map φc = coneCell (hopfKMap m μ) q from rfl,
      show E.2.map φc = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n) from
        (by rw [show E.2.map φc = coneCell (hopfKMap m μ) E.2 from rfl]
            exact coneCell_coneDiag m r n (hopfKMap m μ)),
      show φc cA = diskCos χ from rfl,
      show φc sA = diskSin χ from rfl]
  have hcellW_entry : ∀ i j, hopfDiskW m n r χ (coneCell (hopfKMap m μ) p)
      (coneCell (hopfKMap m μ) q) i j = (ZAm i j).1.2 := by
    intro i j
    have h := congrFun (congrFun hcellW i) j
    rw [Matrix.map_apply] at h
    rw [← h]
    rfl
  -- ## 5. The base part is the constant `diag(1_{n²+n²}, 0)`
  have hbaseW : ZAm.map (coneToT (hopfKMap m μ)).toRingHom
      = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) := by
    rw [show ZAm = diskW p q E.2 cA sA from rfl,
      hk_diskW_map (coneToT (hopfKMap m μ)).toRingHom p q E.2 cA sA]
    show diskW (p.map (coneToT (hopfKMap m μ)).toRingHom)
        (q.map (coneToT (hopfKMap m μ)).toRingHom)
        (E.2.map (coneToT (hopfKMap m μ)).toRingHom)
        ((coneToT (hopfKMap m μ)).toRingHom cA) ((coneToT (hopfKMap m μ)).toRingHom sA)
      = oneBlk (C(Tgt m, ℂ)) (n * n + n * n)
    rw [show (coneToT (hopfKMap m μ)).toRingHom cA = hkCos m from rfl,
      show (coneToT (hopfKMap m μ)).toRingHom sA = hkSin m from rfl]
    exact hk_diskW_base_oneBlk m μ n r p q hp hq hpb hqb
  have hZAbase_const : ∀ (i j : Fin ((n * n + n * n) + (n * n + n * n))) (s s' : Tgt m),
      (ZAm i j).1.1 s = (ZAm i j).1.1 s' := by
    intro i j s s'
    have hentry : (coneToT (hopfKMap m μ)).toRingHom (ZAm i j)
        = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) i j := by
      have h := congrFun (congrFun hbaseW i) j
      rwa [Matrix.map_apply] at h
    rw [show (coneToT (hopfKMap m μ)).toRingHom (ZAm i j) = (ZAm i j).1.1 from rfl] at hentry
    rw [hentry]
    exact reindex_fromBlocks_one_apply_const (Tgt m) (n * n + n * n) i j s s'
  have hcell_const : ∀ (i j : Fin ((n * n + n * n) + (n * n + n * n)))
      (y y' : Ball (Eu m × Eu m)), y ∈ bdry (Eu m × Eu m) → y' ∈ bdry (Eu m × Eu m) →
      (ZAm i j).1.2 y = (ZAm i j).1.2 y' := by
    intro i j y y' hy hy'
    calc (ZAm i j).1.2 y
        = (ZAm i j).1.1 (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) :=
          (ZAm i j).2 y hy
      _ = (ZAm i j).1.1 (hopfKMap m μ ⟨(y' : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy'⟩) :=
          hZAbase_const i j _ _
      _ = (ZAm i j).1.2 y' := ((ZAm i j).2 y' hy').symm
  -- ## 6. The `Kpair`-valued matrix `Z`
  have H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q) i j
        ∈ Kpair (Eu m × Eu m) := by
    intro i j
    show ∀ a ∈ bdry (Eu m × Eu m), ∀ a' ∈ bdry (Eu m × Eu m),
      hopfDiskW m n r χ (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q) i j a
        = hopfDiskW m n r χ (coneCell (hopfKMap m μ) p) (coneCell (hopfKMap m μ) q) i j a'
    intro a ha a' ha'
    rw [hcellW_entry i j]
    exact hcell_const i j a a' ha ha'
  let Zmat : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (Kpair (Eu m × Eu m)) :=
    fun i j => ⟨hopfDiskW m n r χ (coneCell (hopfKMap m μ) p)
      (coneCell (hopfKMap m μ) q) i j, H i j⟩
  let Z : Mat (Kpair (Eu m × Eu m)) := hopfDiskZ m n r χ (coneCell (hopfKMap m μ) p)
    (coneCell (hopfKMap m μ) q) H
  have hZ2 : Z.2 = Zmat := rfl
  -- ## 7. `Z` is idempotent
  have hinj : Function.Injective (relToCone (hopfKMap m μ) y0 hy0) := by
    intro a b hab
    refine Subtype.ext ?_
    have h := congrArg (fun x : coneAlg (hopfKMap m μ) =>
      (x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2) hab
    exact h
  have hmapZ : Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom = ZAm := by
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply]
    show relToCone (hopfKMap m μ) y0 hy0 (Zmat i j) = ZAm i j
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · ext s
      show (Zmat i j).val y0 = (ZAm i j).1.1 s
      rw [show (Zmat i j).val = (ZAm i j).1.2 from hcellW_entry i j]
      rw [hZAbase_const i j _
        (hopfKMap m μ ⟨(y0 : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy0⟩)]
      exact (ZAm i j).2 y0 hy0
    · show (Zmat i j).val = (ZAm i j).1.2
      exact hcellW_entry i j
  have hZidem : Mat.IsIdem Z := by
    show Z.2 * Z.2 = Z.2
    show Zmat * Zmat = Zmat
    apply Matrix.ext
    intro i j
    apply hinj
    have h : (relToCone (hopfKMap m μ) y0 hy0) ((Zmat * Zmat) i j)
        = (relToCone (hopfKMap m μ) y0 hy0) (Zmat i j) := by
      show ((Zmat * Zmat).map (relToCone (hopfKMap m μ) y0 hy0).toRingHom) i j
        = (Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom) i j
      rw [Matrix.map_mul, hmapZ, show ZAm * ZAm = ZAm from hZAidem]
    exact h
  refine ⟨χ, hχ, H, hZidem, ?_, ?_⟩
  · show ((n * n + n * n) + (n * n + n * n)) = 4 * (n * n)
    ring
  · have hmapcls : K0.mapA (relToCone (hopfKMap m μ) y0 hy0) (cls Z) = cls ZA := by
      rw [K0map.map_cls]
      unfold mapCls
      rw [if_pos hZidem]
      have hZZ : Z.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom = ZA := by
        show (⟨(n * n + n * n) + (n * n + n * n),
            Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom⟩ :
              Mat (coneAlg (hopfKMap m μ)))
          = ⟨(n * n + n * n) + (n * n + n * n), ZAm⟩
        rw [hmapZ]
      exact congrArg cls hZZ
    have hmapclsD : K0.mapA (relToCone (hopfKMap m μ) y0 hy0)
        (cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n))))
        = cls (diagMat (coneAlg (hopfKMap m μ)) (2 * (n * n)) (4 * (n * n))) := by
      rw [K0map.map_cls]
      unfold mapCls
      rw [if_pos (diagMat_isIdem (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))]
      exact congrArg cls (Mat.diagMat_map (relToCone (hopfKMap m μ) y0 hy0).toRingHom
        (2 * (n * n)) (4 * (n * n)))
    have hcast : cls (diagMat (coneAlg (hopfKMap m μ)) (n * n + n * n)
        ((n * n + n * n) + (n * n + n * n)))
        = cls (diagMat (coneAlg (hopfKMap m μ)) (2 * (n * n)) (4 * (n * n))) :=
      cls_diagMat_cast (by ring) (by ring)
    rw [map_sub, hmapcls, hmapclsD, ← hcast]
    exact hclass

end

end Work.KT.HopfK
