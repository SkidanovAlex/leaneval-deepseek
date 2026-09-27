import Mathlib
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.mvLin
import Submission.Work.KT.clipP_range_defs
import Submission.Work.KT.clipRangeFun_injective
import Submission.Work.KT.clipRangeFun_surjective

namespace Work.KT

open Matrix

/-- The image of the clutching projection `clipP` is the patched module of `γ`
(`Work.KT.PatchProjDefs`).

Route sketch.  Write `A₁ = C(Ball V, ℂ)`, `ρ = restRho V`, `R = TwoDisk V`, `J = Fin (n+n)` and
`e = finSumFinEquiv : Fin n ⊕ Fin n ≃ J`, and let `z : patched n γ` have components
`f : Fin n → A₁` and `g : Fin n → A₂` with `ρ f = γ *ᵥ ρ g`.  The isomorphism is

  `z ↦ (fun j : J => ⟨((↑G⁻¹ : BallMat V n) *ᵥ padVec f 0) j, (padVec g 0) j⟩) : J → R`,

mapping onto the range of the idempotent matrix `clipP`.  Membership in `R` uses
`RingHom.map_mulVec`, `map_padVec_ringHom`, `blockMulVec_padVec` and
`mapMatrix_Ginv_mul_diagGlue`; the range condition uses `mapMatrix_clipP_fst`,
`mapMatrix_clipP_snd`, `fiberMatrix_ext`, `mapMatrix_fstHom_clipZ`,
`mapMatrix_sndHom_clipZ` and `stdProj_mulVec_eq_self_iff` (here `Z = diag(1,0)` fixes
`padVec f 0` and `padVec g 0` since their second blocks vanish).  Injectivity uses `padVec_inj`
and invertibility of `G`; surjectivity sends `v` with `clipP *ᵥ v = v` to
`(fstBlk (G *ᵥ fstBlk v), fstBlk (sndBlk v))`, the equation `clipP *ᵥ v = v` saying exactly that
the second blocks of `sndBlk v` and of `G *ᵥ fstBlk v` vanish (`eq_padVec_of_sndBlk_eq`), with
the patched condition following from `blockMulVec_inl` for `diagGlue` and the fact that the two
components of an element of `R` have equal `ρ`-images. -/
theorem clipP_range (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ)
    (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    Nonempty (FiberProd.patched (ρ₁ := restRho V) (ρ₂ := restRho V) (comm_sphereC V) n (↑γ)
      ≃ₗ[TwoDisk V] (mvLin (comm_twoDisk V) (clipP V n γ G hG)).range) := by
  refine ⟨?_⟩
  let Φ : clipPatched V n γ →ₗ[TwoDisk V] (mvLin (comm_twoDisk V) (clipP V n γ G hG)).range :=
    (clipRangeLin V n γ G hG).codRestrict _ (fun z => clipRangeFun_mem_range V n γ G hG z)
  have hΦval : ∀ z, (Φ z : Fin (n + n) → TwoDisk V) = clipRangeFun V n γ G hG z := fun z => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    refine clipRangeFun_injective V n γ G hG ?_
    have h := congrArg (fun w : (mvLin (comm_twoDisk V) (clipP V n γ G hG)).range =>
      (w : Fin (n + n) → TwoDisk V)) hxy
    simpa only [hΦval] using h
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨z, hz⟩ := clipRangeFun_surjective V n γ G hG w
    exact ⟨z, Subtype.ext hz⟩
  exact LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩

end Work.KT
