import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FPatch
import Submission.Work.KT.ClutchGeom
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.mvLin
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.lift_diag_unit
import Submission.Work.KT.clipP_isIdem
import Submission.Work.KT.clipP_range
import Submission.Work.KT.clipP_cls_K
import Submission.Work.KT.mvN_range_iso
import Submission.Work.KT.sum_range_iso
import Submission.Work.KT.patched_sum_iso
import Submission.Work.KT.isUnit_sum_one
import Submission.Work.KT.K0_detect
import Submission.Work.KT.patched_free_units
import Submission.Work.KT.homotopy_of_units
import Submission.Work.KT.Cone.Setup

/-!
# `Work.KT.sphere_GL`: invertible matrices over an even-dimensional sphere

For `finrank ℝ V = 2j+1` the unit sphere `Sph V` is `S^{2j}`.  Every invertible matrix over
`C(Sph V, ℂ)`, after adding an identity block, is homotopic through invertible matrices to a
constant matrix.

The proof is the clutching construction.  A unit `u` over the sphere gives a projection over the
double disk (`Work.KT.clipP`) whose image is the patched module of `u`
(`Work.KT.clipP_range`) and whose `K₀`-class is that of the trivial bundle
(`Work.KT.cls_clipP`, from the vanishing `Work.KT.sphere_K_even_aux` of the reduced `K`-theory of
the odd sphere `S^{2j+1}`).  Stable Murray–von Neumann equivalence with the trivial projection
(`Work.KT.K0_detect` + `Work.KT.mvN_range_iso` + `Work.KT.sum_range_iso`) exhibits the patched
module of `u ⊕ 1_k` as free; `Work.KT.patched_free_units` then produces units over the two disks
whose boundary restrictions differ by `u ⊕ 1_k`, and `Work.KT.homotopy_of_units` unwinds the
patching into the required homotopy.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The first block of `Fin (n+k)` does not meet the second. -/
lemma fin_castAdd_ne_natAdd {n k : ℕ} (a : Fin n) (b : Fin k) :
    (Fin.castAdd k a : Fin (n + k)) ≠ Fin.natAdd n b := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 : (Fin.castAdd k a : ℕ) = a := rfl
  have h3 : (Fin.natAdd n b : ℕ) = n + b := rfl
  have h4 := a.isLt
  omega

/-- The second block of `Fin (n+k)` does not meet the first. -/
lemma fin_natAdd_ne_castAdd {n k : ℕ} (a : Fin k) (b : Fin n) :
    (Fin.natAdd n a : Fin (n + k)) ≠ Fin.castAdd k b :=
  fun h => fin_castAdd_ne_natAdd b a h.symm

/-- The second component of a block sum of two identity matrices is the identity. -/
theorem Mat.sum_one_snd {R : Type} [Ring R] (n k : ℕ) :
    ((Mat.one R n).sum (Mat.one R k)).2 =
      (1 : Matrix (Fin (n + k)) (Fin (n + k)) R) := by
  show Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin k) (Fin k) R)) = 1
  rw [Matrix.fromBlocks_one]
  ext i j
  rcases finSumFinEquiv_cases' n k i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases finSumFinEquiv_cases' n k j with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
        Fin.castAdd_inj, Fin.natAdd_inj, fin_castAdd_ne_natAdd, fin_natAdd_ne_castAdd,
        Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff,
        finSumFinEquiv.injective.eq_iff]

/-- Restriction of functions on the ball to the boundary sphere is surjective (Tietze). -/
theorem restRho_surjective : Function.Surjective (restRho V) := fun a => by
  obtain ⟨G, hG⟩ := Cone.restrictSph_surjective (V := V) a
  exact ⟨G, hG⟩

/-- `K¹(S^{2j}) = K¹(pt)`: invertible matrices over an even-dimensional sphere are stably
homotopic to constants. -/
theorem sphere_GL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (j : ℕ) (hV : Module.finrank ℝ V = 2 * j + 1) : GLStablyTrivial (Sph V) := by
  intro n u hu
  rw [← hu.unit_spec]
  -- the lift of `diag(u, u⁻¹)` over the ball
  obtain ⟨G, hG⟩ := lift_diag_unit V hu.unit
  have hGu : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n hu.unit := hG
  -- the clutching projection and its `K₀`-class
  have hPidem : Mat.IsIdem (⟨n + n, clipP V n hu.unit G hGu⟩ : Mat (TwoDisk V)) :=
    clipP_isIdem V n hu.unit G hGu
  have hcls := cls_clipP V j hV n hu.unit G hGu
  -- stable Murray–von Neumann equivalence with the trivial projection
  obtain ⟨k, hk⟩ := K0_detect (⟨n + n, clipP V n hu.unit G hGu⟩ : Mat (TwoDisk V))
    (Mat.one (TwoDisk V) n) hPidem (Mat.one_isIdem (R := TwoDisk V) n) hcls
  obtain ⟨A, B, hBA, hAB⟩ := hk
  have hAB' : A * B = 1 := by
    have h := hAB
    rw [Mat.sum_one_snd] at h
    exact h
  -- the four isomorphisms
  obtain ⟨e1⟩ := mvN_range_iso (comm_twoDisk V) hBA hAB'
  obtain ⟨e2⟩ := sum_range_iso (comm_twoDisk V) (clipP V n hu.unit G hGu)
  obtain ⟨e3⟩ := clipP_range V n hu.unit G hGu
  obtain ⟨e4⟩ := patched_sum_iso (ρ₁ := restRho V) (ρ₂ := restRho V) (comm_sphereC V)
    (k := k) (hu.unit : Matrix (Fin n) (Fin n) C(Sph V, ℂ))
  -- the patched module of `u ⊕ 1_k` is free
  have e : FiberProd.patched (ρ₁ := restRho V) (ρ₂ := restRho V) (comm_sphereC V) (n + k)
      ((Mat.sum ⟨n, (hu.unit : Matrix (Fin n) (Fin n) C(Sph V, ℂ))⟩
        (Mat.one C(Sph V, ℂ) k)).2) ≃ₗ[TwoDisk V]
        (Fin (n + k) → TwoDisk V) :=
    e4.trans ((e3.prodCongr (LinearEquiv.refl (TwoDisk V) (Fin k → TwoDisk V))).trans
      (e2.symm.trans e1.symm))
  -- unwinding the patching
  obtain ⟨G₁, G₂, hunits⟩ := patched_free_units (ρ₁ := restRho V) (ρ₂ := restRho V)
    (comm_sphereC V) (comm_ballC V) (comm_ballC V) (restRho_surjective V)
    ((Mat.sum ⟨n, (hu.unit : Matrix (Fin n) (Fin n) C(Sph V, ℂ))⟩
      (Mat.one C(Sph V, ℂ) k)).2)
    (isUnit_sum_one (m := n) (k := k) hu.unit.isUnit) e
  obtain ⟨H, hHunit, hH0, c, hH1⟩ := homotopy_of_units
    (w := ((Mat.sum ⟨n, (hu.unit : Matrix (Fin n) (Fin n) C(Sph V, ℂ))⟩
      (Mat.one C(Sph V, ℂ) k)).2)) G₁ G₂ hunits
  exact ⟨k, H, hHunit, hH0, ⟨c, hH1⟩⟩

end

end Work.KT
