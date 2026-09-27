import Mathlib
import Submission.Work.KT.clipP_range_defs
import Submission.Work.KT.clipP_isIdem

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

/-- The first block of `M *ᵥ v`, after applying a ring homomorphism, is the first block of the
image vector.  (Dual bookkeeping to `Work.KT.map_padVec_ringHom`.) -/
lemma fstBlk_map_mulVec {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m : ℕ}
    (M : Matrix (Fin (m + m)) (Fin (m + m)) A) (v : Fin (m + m) → A) :
    (fun i => φ (fstBlk (M *ᵥ v) i)) =
      fstBlk ((RingHom.mapMatrix φ M) *ᵥ (fun k => φ (v k))) := by
  funext i
  simp only [fstBlk]
  rw [RingHom.map_mulVec]
  rfl

/-- **Surjectivity of the clutching isomorphism.**  Every element of the range of the clutching
projection `clipP` is the image under `clipRangeFun` of a patched pair, i.e. `clipRangeFun` maps
the patched module of `γ` onto `range (mvLin (comm_twoDisk V) (clipP V n γ G hG))`.

Given `W = clipP *ᵥ v` (so `W` is fixed by `clipP`), the preimage is
`(fstBlk (G *ᵥ W₁), fstBlk W₂)` where `W₁`, `W₂` are the two components of `W`: fixing by `clipP`
forces the second block of `G *ᵥ W₁` and of `W₂` to vanish, so `W₁ = G⁻¹ *ᵥ padVec (fstBlk (G *ᵥ W₁)) 0`
and `W₂ = padVec (fstBlk W₂) 0`; the compatibility `ρ (fstBlk (G *ᵥ W₁)) = γ *ᵥ ρ (fstBlk W₂)` is the
statement that the two components of an element of the fibre product have equal `ρ`-images. -/
theorem clipRangeFun_surjective (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ)
    (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    ∀ w : (mvLin (comm_twoDisk V) (clipP V n γ G hG)).range,
      ∃ z : clipPatched V n γ, clipRangeFun V n γ G hG z = (w : Fin (n + n) → TwoDisk V) := by
  intro w
  obtain ⟨v, hv⟩ := (mem_range_mvLin (clipP V n γ G hG) (w : Fin (n+n) → TwoDisk V)).mp w.2
  -- `w` is a fixed point of `clipP`
  have hW : clipP V n γ G hG *ᵥ (w : Fin (n + n) → TwoDisk V) = (w : Fin (n + n) → TwoDisk V) := by
    rw [← hv, Matrix.mulVec_mulVec, clipP_isIdem]
  -- the second component of `w`, read in `C(Ball V, ℂ)`, is fixed by the standard projection
  have hZ2 : stdProj (C(Ball V, ℂ)) n *ᵥ (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2) =
      (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2) := by
    have h := congrArg (fun f : Fin (n+n) → TwoDisk V => (fun j => (f j).1.2)) hW
    rw [map_sndHom_mulVec, mapMatrix_clipP_snd, mapMatrix_sndHom_clipZ] at h
    exact h
  -- the first component of `w`, read in `C(Ball V, ℂ)`, is fixed by `G⁻¹ Z G`
  have hE : ((↑(G⁻¹) : BallMat V n) * stdProj (C(Ball V, ℂ)) n * (↑G : BallMat V n)) *ᵥ
      (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1) =
      (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1) := by
    have h := congrArg (fun f : Fin (n+n) → TwoDisk V => (fun j => (f j).1.1)) hW
    rw [map_fstHom_mulVec, mapMatrix_clipP_fst, mapMatrix_fstHom_clipZ] at h
    exact h
  -- hence the standard projection fixes `G *ᵥ W₁`
  have hZ1 : stdProj (C(Ball V, ℂ)) n *ᵥ ((↑G : BallMat V n) *ᵥ
      (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1)) =
      (↑G : BallMat V n) *ᵥ (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1) := by
    have hGG : (↑G : BallMat V n) * (↑(G⁻¹) : BallMat V n) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hZG : stdProj (C(Ball V, ℂ)) n * (↑G : BallMat V n) =
        (↑G : BallMat V n) *
          ((↑(G⁻¹) : BallMat V n) * stdProj (C(Ball V, ℂ)) n * (↑G : BallMat V n)) := by
      rw [← mul_assoc (↑G : BallMat V n)
            ((↑(G⁻¹) : BallMat V n) * stdProj (C(Ball V, ℂ)) n) (↑G : BallMat V n),
        ← mul_assoc (↑G : BallMat V n) (↑(G⁻¹) : BallMat V n) (stdProj (C(Ball V, ℂ)) n),
        hGG, one_mul]
    rw [Matrix.mulVec_mulVec, hZG, ← Matrix.mulVec_mulVec, hE]
  have hpad1 : (↑G : BallMat V n) *ᵥ (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1) =
      padVec (fstBlk ((↑G : BallMat V n) *ᵥ
        (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1))) 0 := by
    apply eq_padVec_fstBlk_zero
    funext i
    rw [sndBlk]
    exact (stdProj_mulVec_eq_self_iff _).mp hZ1 i
  have hpad2 : (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2) =
      padVec (fstBlk (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2)) 0 := by
    apply eq_padVec_fstBlk_zero
    funext i
    rw [sndBlk]
    exact (stdProj_mulVec_eq_self_iff _).mp hZ2 i
  -- the two components of `w`, viewed in `C(Sph V, ℂ)`, agree
  have hρ : (fun k => restRho V ((w : Fin (n+n) → TwoDisk V) k).1.1) =
      (fun k => restRho V ((w : Fin (n+n) → TwoDisk V) k).1.2) := by
    funext k
    exact ((w : Fin (n+n) → TwoDisk V) k).2
  -- compatibility of the patched pair
  have hmem : (fun i => restRho V (fstBlk ((↑G : BallMat V n) *ᵥ
        (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1)) i)) =
      (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) *ᵥ
        (fun i => restRho V (fstBlk (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2) i)) := by
    rw [fstBlk_map_mulVec (restRho V) (↑G : BallMat V n)
        (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1), hG, fstBlk_diagGlue_mulVec]
    rw [show (fun i => restRho V
          (fstBlk (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2) i)) =
        fstBlk (fun k => restRho V ((w : Fin (n+n) → TwoDisk V) k).1.2) from by
          funext i; rfl,
      ← hρ]
  refine ⟨⟨(fstBlk ((↑G : BallMat V n) *ᵥ (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1)),
    fstBlk (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2)), hmem⟩, ?_⟩
  funext j
  apply Subtype.ext
  apply Prod.ext
  · show ((↑(G⁻¹) : BallMat V n) *ᵥ padVec (fstBlk ((↑G : BallMat V n) *ᵥ
        (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.1))) 0) j =
        ((w : Fin (n+n) → TwoDisk V) j).1.1
    rw [← hpad1, Matrix.mulVec_mulVec]
    have hGG' : (↑(G⁻¹) : BallMat V n) * (↑G : BallMat V n) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hGG', Matrix.one_mulVec]
  · show (padVec (fstBlk (fun j => ((w : Fin (n+n) → TwoDisk V) j).1.2)) 0) j =
        ((w : Fin (n+n) → TwoDisk V) j).1.2
    rw [← hpad2]

end

end Work.KT
