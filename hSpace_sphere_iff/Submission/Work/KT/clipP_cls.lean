import Mathlib
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.clipP_isIdem
import Submission.Work.KT.clipP_cls_aux
import Submission.Work.KT.twoDisk_ringEquiv

/-!
# The `K₀`-class of the clutching projection (`Work.KT.cls_clipP_of_vanishing`)

The class in `K₀(TwoDisk V) = K₀(C(S^{dim V}))` of the clutching projection `clipP` of
`Work.KT.PatchProjDefs` is the class of the trivial bundle of rank `n`: the projection has rank
`n` at the centre of the first disk, so its class is reduced, so it is trivial as soon as the
reduced `K`-theory of the odd sphere `S^{2j+1} = Sph (WithLp 2 (V × ℝ))` vanishes.  That
vanishing is the hypothesis `hvan` here; `Work.KT.cls_clipP` discharges it.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- If the reduced `K`-theory of the odd sphere `Sph (WithLp 2 (V × ℝ))` vanishes, then the
clutching projection of the unit `gamma` has the class of the trivial bundle of rank `n`. -/
theorem cls_clipP_of_vanishing (j : ℕ) (hV : Module.finrank ℝ V = 2 * j + 1) (n : ℕ)
    (gamma : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n gamma)
    (hvan : ∀ (t0 : Sph (WithLp 2 (V × ℝ)))
      (z : K0 C(Sph (WithLp 2 (V × ℝ)), ℂ)), K0.mapA (evalC t0) z = 0 → z = 0) :
    cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)) = cls (Mat.one (TwoDisk V) n) := by
  obtain ⟨Θ, hΘ⟩ := twoDisk_ringEquiv V
  -- the base point of `Sph (WithLp 2 (V × ℝ))`
  let t0 : Sph (WithLp 2 (V × ℝ)) := ⟨WithLp.toLp 2 ((0 : V), 1), by simp⟩
  -- evaluation of a function on the ball at the centre
  let χ₁ : C(Ball V, ℂ) →+* ℂ :=
    ((evalC (⟨0, by simp⟩ : Ball V)) : C(Ball V, ℂ) →ₐ[ℂ] ℂ).toRingHom
  let χ : TwoDisk V →+* ℂ := χ₁.comp (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ))
  have hchar : χ = ((evalC t0).toRingHom).comp Θ.symm.toRingHom := by
    refine RingHom.ext fun z => ?_
    have h := hΘ (Θ.symm z)
    rw [Θ.apply_symm_apply] at h
    exact h
  have hPidem : Mat.IsIdem (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)) :=
    clipP_isIdem V n gamma G hG
  -- the value of the projection at the centre of the first disk
  have hmapZ : (RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ))
      (clipZ V n)).map (⇑χ₁) = stdProj ℂ n := by
    rw [mapMatrix_fstHom_clipZ, ← RingHom.mapMatrix_apply, mapMatrix_stdProj]
  have hmap : (clipP V n gamma G hG).map (⇑χ) =
      ((↑(G⁻¹) : BallMat V n).map (⇑χ₁)) * stdProj ℂ n *
        ((↑G : BallMat V n).map (⇑χ₁)) := by
    rw [show (clipP V n gamma G hG).map (⇑χ) =
        (((↑(G⁻¹) : BallMat V n) *
          RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ)) (clipZ V n) *
            (↑G : BallMat V n))).map (⇑χ₁) from rfl]
    rw [Matrix.map_mul, Matrix.map_mul, hmapZ]
  have h1 : ((↑G : BallMat V n).map (⇑χ₁)) * ((↑(G⁻¹) : BallMat V n).map (⇑χ₁)) = 1 := by
    rw [← Matrix.map_mul, ← RingHom.mapMatrix_apply, Units.mul_inv, map_one]
  have h2 : ((↑(G⁻¹) : BallMat V n).map (⇑χ₁)) * ((↑G : BallMat V n).map (⇑χ₁)) = 1 := by
    rw [← Matrix.map_mul, ← RingHom.mapMatrix_apply, Units.inv_mul, map_one]
  have hcls : cls (⟨n + n, (clipP V n gamma G hG).map (⇑χ)⟩ : Mat ℂ) = cls (Mat.one ℂ n) := by
    rw [hmap]
    exact (cls_conj_pc h1 h2 (stdProj_isIdem (R := ℂ) n)).trans (cls_stdProj_pc n)
  -- the transported class is reduced
  have hz : K0.mapA (evalC t0)
      (K0.map Θ.symm.toRingHom (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V))) -
        cls (Mat.one C(Sph (WithLp 2 (V × ℝ)), ℂ) n)) = 0 := by
    have hterm1 : K0.mapA (evalC t0)
        (K0.map Θ.symm.toRingHom (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)))) =
        cls (Mat.one ℂ n) := by
      change ((K0.map (evalC t0).toRingHom).comp (K0.map Θ.symm.toRingHom))
        (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V))) = cls (Mat.one ℂ n)
      rw [← K0.map_comp Θ.symm.toRingHom (evalC t0).toRingHom, ← hchar, K0.map_cls χ hPidem]
      exact hcls
    have hterm2 : K0.mapA (evalC t0) (cls (Mat.one C(Sph (WithLp 2 (V × ℝ)), ℂ) n)) =
        cls (Mat.one ℂ n) := by
      rw [K0.mapA, K0.map_cls (evalC t0).toRingHom
        (Mat.one_isIdem (R := C(Sph (WithLp 2 (V × ℝ)), ℂ)) n), Mat.map_one_pc]
    rw [map_sub, hterm1, hterm2, sub_self]
  -- vanishing of the reduced `K`-theory of the odd sphere
  have hkey : K0.map Θ.symm.toRingHom (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V))) =
      cls (Mat.one C(Sph (WithLp 2 (V × ℝ)), ℂ) n) := sub_eq_zero.mp (hvan t0 _ hz)
  -- transport back
  have hid : Θ.toRingHom.comp Θ.symm.toRingHom = RingHom.id (TwoDisk V) :=
    RingHom.ext fun z => Θ.apply_symm_apply z
  have hX : K0.map Θ.toRingHom
      (K0.map Θ.symm.toRingHom (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)))) =
      cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)) := by
    change ((K0.map Θ.toRingHom).comp (K0.map Θ.symm.toRingHom))
      (cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V))) =
        cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V))
    rw [← K0.map_comp Θ.symm.toRingHom Θ.toRingHom, hid, K0.map_id_apply]
  have hfinal := congrArg (K0.map Θ.toRingHom) hkey
  rw [hX, K0.map_cls Θ.toRingHom
    (Mat.one_isIdem (R := C(Sph (WithLp 2 (V × ℝ)), ℂ)) n), Mat.map_one_pc] at hfinal
  exact hfinal

end

end Work.KT
