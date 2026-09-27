import Mathlib
import Submission.Work.KT.HopfK.hk_sliceFst_pre

namespace Work.KT.HopfK

theorem hopfPsiFst_cls (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (Q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul))) (hQ : Q * Q = Q)
    (hcap : ∀ t : Tgt m, t ∈ capTminus m →
      Q.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    (v : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hv : Mat.IsIdem (⟨n, v⟩ : Mat (Kpair (Eu m))))
    (hvQ : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = evalD m (hopfKMap m hS.hmul) (ptFst m hS.e y) (Q i j)) :
    cls (⟨n, v.map (hopfPsiFst m hS)⟩ : Mat C(Tgt m, ℂ))
      = cls (⟨n, Q.map (coneToT (hopfKMap m hS.hmul))⟩ : Mat C(Tgt m, ℂ)) := by
  classical
  set g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := Q.map (coneToT (hopfKMap m hS.hmul)) with hg
  have hgg : g * g = g := by
    rw [hg, ← Matrix.map_mul, hQ]
  -- (a) pointwise value of `v`
  have hv_eq : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = g i j (hopfKMap m hS.hmul (ptFstSph m hS.e y)) := by
    intro i j y
    rw [hvQ i j y]
    show (Q i j).1.2 (ptFst m hS.e y)
      = (coneToT (hopfKMap m hS.hmul) (Q i j)) (hopfKMap m hS.hmul (ptFstSph m hS.e y))
    exact (Q i j).2 (ptFst m hS.e y) (ptFst_mem_bdry m hS.e y)
  -- (b) values on the boundary
  have hv_bdry : ∀ (i j : Fin n) (y : Ball (Eu m)), y ∈ bdry (Eu m) →
      ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y = diagIdemMat r n i j := by
    intro i j y hy
    rw [hv_eq i j y]
    have ht : hopfKMap m hS.hmul (ptFstSph m hS.e y) ∈ capTminus m :=
      capTminus_ptFstSph m hS.hmul hS.e y hy
    have hmat := map_evalC_g_eq_diagFst m hS n r Q hcap ht
    rw [← hg] at hmat
    have := congrFun (congrFun hmat i) j
    rw [Matrix.map_apply] at this
    exact this
  -- (c) the pointwise homotopy endpoints
  have hG0 : ∀ (i j : Fin n) (t : Tgt m),
      hopfGHomFst m hS g (0, t) i j = hopfPsiFst m hS (v i j) t := by
    intro i j t
    by_cases ht : 0 ≤ tgtHeight m t
    · rw [show hopfGHomFst m hS g (0, t) = g.map (evalC (homPtFst m hS 0 t)) from by
        unfold hopfGHomFst; rw [if_pos ht]]
      rw [Matrix.map_apply, hopfPsiFst_apply, hopfPsiFstFun, if_pos ht]
      rw [show homPtFst m hS 0 t = hopfKMap m hS.hmul (ptFstSph m hS.e (lowerPt m t))
          from ?_]
      · show (g i j) (hopfKMap m hS.hmul (ptFstSph m hS.e (lowerPt m t)))
          = ((v i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) (lowerPt m t)
        rw [← hv_eq i j (lowerPt m t)]
      · have h1 := homPtFst_zero_hemiUp m hS (lowerPt m t)
        rwa [hemiUp_lowerPt m t ht] at h1
    · push Not at ht
      rw [show hopfGHomFst m hS g (0, t) = g.map (evalC t) from by
        unfold hopfGHomFst; rw [if_neg (not_le.mpr ht)]]
      rw [Matrix.map_apply, hopfPsiFst_apply, hopfPsiFstFun, if_neg (not_le.mpr ht)]
      rw [hv_bdry i j (sphToBall hS.e) (sphToBall_mem_bdry hS.e)]
      rw [hg]
      have hmat := map_evalC_g_eq_diagFst m hS n r Q hcap
        (show t ∈ capTminus m by rw [capTminus, Set.mem_setOf_eq]; linarith)
      have := congrFun (congrFun hmat i) j
      rw [Matrix.map_apply] at this
      exact this
  have hG1 : ∀ (i j : Fin n) (t : Tgt m), hopfGHomFst m hS g (1, t) i j = g i j t := by
    intro i j t
    by_cases ht : 0 ≤ tgtHeight m t
    · rw [show hopfGHomFst m hS g (1, t) = g.map (evalC (homPtFst m hS 1 t)) from by
        unfold hopfGHomFst; rw [if_pos ht]]
      rw [Matrix.map_apply, homPtFst_one]
      rfl
    · push Not at ht
      rw [show hopfGHomFst m hS g (1, t) = g.map (evalC t) from by
        unfold hopfGHomFst; rw [if_neg (not_le.mpr ht)]]
      rw [Matrix.map_apply]
      rfl
  -- (d) the homotopy of matrices over `C(Tgt m, ℂ)`
  let Gc : unitInterval → Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := fun s i j =>
    ⟨fun t => hopfGHomFst m hS g (s, t) i j,
      ((continuous_hopfGHomFst m hS n r Q hcap).matrix_elem i j).comp
        (continuous_const.prodMk continuous_id)⟩
  have hGc_cont : Continuous Gc := by
    apply continuous_matrix
    intro i j
    exact (ContinuousMap.curry ⟨fun st : unitInterval × Tgt m => hopfGHomFst m hS g st i j,
      (continuous_hopfGHomFst m hS n r Q hcap).matrix_elem i j⟩).continuous
  have hGcmap : ∀ (s : unitInterval) (t : Tgt m),
      (Gc s).map (evalC t) = hopfGHomFst m hS g (s, t) := by
    intro s t
    ext i j
    rfl
  have hGc_idem : ∀ s : unitInterval, Gc s * Gc s = Gc s := by
    intro s
    apply Matrix.ext
    intro i j
    apply ContinuousMap.ext
    intro t
    have h2 : (Gc s * Gc s).map (evalC t) = (Gc s).map (evalC t) := by
      rw [Matrix.map_mul, hGcmap s t, hopfGHomFst_idem m hS g hgg (s, t)]
    exact congrFun (congrFun h2 i) j
  have hcls := Work.KT.Fund.cls_eq_of_path (C(Tgt m, ℂ)) Gc hGc_cont hGc_idem
  have hGc0 : Gc 0 = v.map (hopfPsiFst m hS) := by
    ext i j t
    exact hG0 i j t
  have hGc1 : Gc 1 = g := by
    ext i j t
    exact hG1 i j t
  rw [hGc0, hGc1, hg] at hcls
  exact hcls

end Work.KT.HopfK
