import Mathlib
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-! ## Helpers -/

lemma norm_sphere_coe {V : Type} [NormedAddCommGroup V] (x : Sph V) : ‖(x : V)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

lemma norm_ball_coe {V : Type} [NormedAddCommGroup V] (x : Ball V) : ‖(x : V)‖ ≤ 1 :=
  mem_closedBall_zero_iff.mp x.2

lemma ptFst_coe (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) :
    ((ptFst m e₀ x : Ball (Eu m × Eu m)) : Eu m × Eu m) = ((x : Eu m), (e₀ : Eu m)) := rfl

lemma ptFst_mem_bdry (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) :
    ptFst m e₀ x ∈ bdry (Eu m × Eu m) := by
  show ‖((ptFst m e₀ x : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1
  rw [ptFst_coe, Prod.norm_def, norm_sphere_coe e₀, max_eq_right (norm_ball_coe x)]

/-- The sphere point `(x, e₀)` of `Sph (Eu m × Eu m)`. -/
def ptFstSph (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) : Sph (Eu m × Eu m) :=
  ⟨((x : Eu m), (e₀ : Eu m)), by
    rw [mem_sphere_zero_iff_norm, Prod.norm_def, norm_sphere_coe e₀, max_eq_right (norm_ball_coe x)]⟩

@[simp] lemma ptFstSph_coe (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) :
    ((ptFstSph m e₀ x : Sph (Eu m × Eu m)) : Eu m × Eu m) = ((x : Eu m), (e₀ : Eu m)) := rfl

lemma ptFst_sphere_eq (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) :
    ptFstSph m e₀ x = (⟨((ptFst m e₀ x : Ball (Eu m × Eu m)) : Eu m × Eu m),
        mem_sphere_zero_iff_norm.mpr (ptFst_mem_bdry m e₀ x)⟩ : Sph (Eu m × Eu m)) := by
  apply Subtype.ext
  rw [ptFstSph_coe, ptFst_coe]

lemma tgtHeight_ptFstSph (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (e₀ : Sph (Eu m)) (x : Ball (Eu m)) :
    tgtHeight m (hopfKMap m μ (ptFstSph m e₀ x)) = Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2) := by
  have key := tgtHeight_eq_of_norm_snd_eq_one m μ (ptFstSph m e₀ x)
    (by show ‖(e₀ : Eu m)‖ = 1; exact norm_sphere_coe e₀)
  simpa [ptFstSph] using key

lemma capTminus_ptFstSph (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (e₀ : Sph (Eu m)) (x : Ball (Eu m)) (hx : ‖(x : Eu m)‖ = 1) :
    hopfKMap m μ (ptFstSph m e₀ x) ∈ capTminus m := by
  show tgtHeight m (hopfKMap m μ (ptFstSph m e₀ x)) ≤ 1 / 2
  rw [tgtHeight_ptFstSph, hx]
  norm_num

lemma pullAlg_val {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (h : C(Y, ℂ)) (x : X) : pullAlg g h x = h (g x) := rfl

lemma pullFst_val (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    (h : Kpair V) (z : Ball (V × W)) :
    ((pullFst V W h : prodAlg V W) : C(Ball (V × W), ℂ)) z = (h : C(Ball V, ℂ)) (prFst V W z) :=
  rfl

lemma shiftFst_one_apply (m : ℕ) (e₀ : Sph (Eu m)) (z : Ball (Eu m × Eu m)) :
    shiftFst m e₀ 1 z = ptFst m e₀ (prFst (Eu m) (Eu m) z) := by
  apply Subtype.ext
  simp only [shiftFst, ptFst, prFst, ContinuousMap.coe_mk]
  norm_num

end

/-! ## The slice lemma -/

theorem hk_sliceFst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ)
    (e₀ : Sph (Eu m)) (y0E : Ball (Eu m)) (hy0E : y0E ∈ bdry (Eu m))
    (q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))) (hq : q * q = q)
    (hqb : ∀ t : Tgt m, t ∈ capTminus m → q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n) :
    ∃ v : Matrix (Fin n) (Fin n) (Kpair (Eu m)),
      Mat.IsIdem (⟨n, v⟩ : Mat (Kpair (Eu m))) ∧
      (∀ i j, (v i j : C(Ball (Eu m), ℂ))
        = ⟨fun x : Ball (Eu m) => coneCell (hopfKMap m μ) q i j (ptFst m e₀ x),
           (coneCell (hopfKMap m μ) q i j).continuous.comp (continuous_ptFst m e₀)⟩) ∧
      (coneCell (hopfKMap m μ) q).map (pullAlg (shiftFst m e₀ 1)).toRingHom
        = (fun i j => ((pullFst (Eu m) (Eu m) (v i j) : prodAlg (Eu m) (Eu m)) :
            C(Ball (Eu m × Eu m), ℂ))) ∧
      K0.mapA (augPair (Eu m) y0E)
        (cls (⟨n, v⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)) = 0 := by
  classical
  let ptF : C(Ball (Eu m), Ball (Eu m × Eu m)) := ⟨ptFst m e₀, continuous_ptFst m e₀⟩
  let φ : C(Ball (Eu m × Eu m), ℂ) →ₐ[ℂ] C(Ball (Eu m), ℂ) := pullAlg ptF
  let w : Matrix (Fin n) (Fin n) (C(Ball (Eu m), ℂ)) :=
    (coneCell (hopfKMap m μ) q).map φ.toRingHom
  have hw_apply : ∀ (i j : Fin n) (x : Ball (Eu m)),
      w i j x = coneCell (hopfKMap m μ) q i j (ptFst m e₀ x) := by
    intro i j x
    show (coneCell (hopfKMap m μ) q i j) (ptF x) =
      coneCell (hopfKMap m μ) q i j (ptFst m e₀ x)
    rfl
  -- the key pointwise statement: on the boundary the cell part is the constant `diag(1_r,0)`
  have hbdry_val : ∀ (i j : Fin n) (x : Ball (Eu m)), ‖(x : Eu m)‖ = 1 →
      coneCell (hopfKMap m μ) q i j (ptFst m e₀ x) = diagIdemMat r n i j := by
    intro i j x hx
    have hz : ptFst m e₀ x ∈ bdry (Eu m × Eu m) := ptFst_mem_bdry m e₀ x
    have hcond := (q i j).2 (ptFst m e₀ x) hz
    rw [coneCell_apply_apply, hcond]
    set xs : Sph (Eu m × Eu m) :=
      ⟨↑(ptFst m e₀ x), mem_sphere_zero_iff_norm.mpr hz⟩ with hxs
    have hcap : hopfKMap m μ xs ∈ capTminus m := by
      show tgtHeight m (hopfKMap m μ xs) ≤ 1 / 2
      have hxsval : (xs : Eu m × Eu m) = ((x : Eu m), (e₀ : Eu m)) := by rw [hxs]; rfl
      have hgt : tgtHeight m (hopfKMap m μ xs) = Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2) := by
        have h' := tgtHeight_eq_of_norm_snd_eq_one m μ xs
          (by rw [hxsval]; exact mem_sphere_zero_iff_norm.mp e₀.2)
        simpa [hxsval] using h'
      rw [hgt, hx]
      norm_num
    have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j)
      (hqb (hopfKMap m μ xs) hcap)
    rw [← hb, Matrix.map_apply]
    rw [show evalT m (hopfKMap m μ) (hopfKMap m μ xs) (q i j)
        = ((↑(q i j) : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))).1
            (hopfKMap m μ xs) from rfl]
  have hmem : ∀ i j : Fin n, w i j ∈ Kpair (Eu m) := by
    intro i j a ha a' ha'
    rw [hw_apply i j a, hw_apply i j a',
      hbdry_val i j a ha, hbdry_val i j a' ha']
  let v : Matrix (Fin n) (Fin n) (Kpair (Eu m)) := fun i j => ⟨w i j, hmem i j⟩
  have hww : w * w = w := by
    show (coneCell (hopfKMap m μ) q).map φ.toRingHom
        * (coneCell (hopfKMap m μ) q).map φ.toRingHom
      = (coneCell (hopfKMap m μ) q).map φ.toRingHom
    rw [← Matrix.map_mul]
    rw [← coneCell_mul, hq]
  have hval : v.map (Kpair (Eu m)).val = w := by
    ext i j
    rfl
  have hvv : (v * v).map (Kpair (Eu m)).val = w := by
    rw [Matrix.map_mul (f := (Kpair (Eu m)).val), hval, hww]
  have hidemv : v * v = v := by
    refine Matrix.map_injective (f := (Kpair (Eu m)).val) ?_ ?_
    · intro x y h
      exact Subtype.ext h
    · simp only [hvv, hval]
  refine ⟨v, hidemv, ?_, ?_, ?_⟩
  · intro i j
    apply ContinuousMap.ext
    intro x
    exact hw_apply i j x
  · ext i j z
    rw [Matrix.map_apply]
    change (pullAlg (shiftFst m e₀ 1) (coneCell (hopfKMap m μ) q i j)) z
      = ((pullFst (Eu m) (Eu m) (v i j) : prodAlg (Eu m) (Eu m)) :
          C(Ball (Eu m × Eu m), ℂ)) z
    rw [pullAlg_val, shiftFst_one_apply m e₀ z, pullFst_val]
    exact (hw_apply i j (prFst (Eu m) (Eu m) z)).symm
  · have hval_diag : v.map (augPair (Eu m) y0E).toRingHom = diagIdemMat r n := by
      ext i j
      rw [Matrix.map_apply]
      show (augPair (Eu m) y0E) (v i j) = diagIdemMat r n i j
      rw [show (augPair (Eu m) y0E) (v i j) = w i j y0E from rfl,
        hw_apply i j y0E, hbdry_val i j y0E hy0E]
    have hmat1 : Mat.map (augPair (Eu m) y0E).toRingHom (⟨n, v⟩ : Mat (Kpair (Eu m)))
        = (⟨n, diagIdemMat r n⟩ : Mat ℂ) := by
      show (⟨n, v.map (augPair (Eu m) y0E).toRingHom⟩ : Mat ℂ) = ⟨n, diagIdemMat r n⟩
      rw [hval_diag]
    have hmat2 : Mat.map (augPair (Eu m) y0E).toRingHom (diagMat (Kpair (Eu m)) r n)
        = (⟨n, diagIdemMat r n⟩ : Mat ℂ) := by
      show (⟨n, (Matrix.diagonal (fun i : Fin n =>
          if (i : ℕ) < r then (1 : Kpair (Eu m)) else 0)).map
            (augPair (Eu m) y0E).toRingHom⟩ : Mat ℂ) = ⟨n, diagIdemMat r n⟩
      congr 1
      ext i j
      show (augPair (Eu m) y0E)
          ((Matrix.diagonal (fun i : Fin n =>
            if (i : ℕ) < r then (1 : Kpair (Eu m)) else 0)) i j)
        = (Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0)) i j
      rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        by_cases hir : (i : ℕ) < r <;> simp [hir]
      · rw [if_neg hij, if_neg hij]
        simp
    have hmv : K0.mapA (augPair (Eu m) y0E) (cls (⟨n, v⟩ : Mat (Kpair (Eu m))))
        = cls (⟨n, diagIdemMat r n⟩ : Mat ℂ) := by
      rw [K0.map_cls (augPair (Eu m) y0E).toRingHom
        (p := (⟨n, v⟩ : Mat (Kpair (Eu m)))) hidemv]
      rw [hmat1]
    have hmd : K0.mapA (augPair (Eu m) y0E) (cls (diagMat (Kpair (Eu m)) r n))
        = cls (⟨n, diagIdemMat r n⟩ : Mat ℂ) := by
      rw [K0.map_cls (augPair (Eu m) y0E).toRingHom
        (p := diagMat (Kpair (Eu m)) r n) (diagMat_isIdem (Kpair (Eu m)) r n)]
      rw [hmat2]
    rw [map_sub, hmv, hmd, sub_self]

end Work.KT.HopfK
