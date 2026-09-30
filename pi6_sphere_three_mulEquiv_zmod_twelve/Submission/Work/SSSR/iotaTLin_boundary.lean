import Mathlib
import Submission.Work.SSSR.serreE1Snd
import Submission.Work.SSSR.ezLinSnd_boundary
import Submission.Work.SSSR.serreE1D1
import Submission.Work.SSSR.ezSimplex_liftFam_coface
import Submission.Work.SSSR.ezSimplexZero_aux
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.KunnethEZ.ezGen_map_fst
import Submission.Work.SSSR.hornCok_d_faceLift_chain
import Submission.Work.SSSR.ezLinSnd_map_fst
import Submission.Work.SSSR.iotaTLift_last_eq
import Submission.Work.SSSR.ezLinSnd_bdry_elem
import Submission.Work.SSSR.iotaTLinFace_eq
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000

/-- **The degree transport of a differential.**  If `h : j' = j` then the differential `K.d i j'`,
regarded in degree `j` along the transport `K.X j' ≅ K.X j`, is the differential `K.d i j`. -/
lemma iotaTLinD_cast {K : ChainComplex (ModuleCat R) ℕ} {i j j' : ℕ} (h : j' = j)
    (x : K.X i) :
    (ModuleCat.Hom.hom (eqToHom (congrArg (fun k : ℕ => K.X k) h)))
        ((ModuleCat.Hom.hom (K.d i j')) x) = (ModuleCat.Hom.hom (K.d i j)) x := by
  subst h
  simp

/-- **The boundary of the lifted Eilenberg–Zilber chain, linearised in the fibre chain.**

For `σ : Δ[s+1] ⟶ Sing B`, `b = σ(v₀)` and an arbitrary CYCLE chain `z` of the fibre over `b`, the
boundary of `Work.SSSR.iotaTLin p hfib s t b σ h z` (the shuffle chain of the fundamental
`(s+1)`-simplex and `z`, pushed into `T_σ` along `ezSimplex_σ`) decomposes into the `s+2` face terms
`Work.SSSR.iotaTLinFace p hfib s t b σ h i z`, with the alternating signs, the `∂z`-term having
dropped out by `hz`. -/
theorem iotaTLin_boundary {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (eqToHom (congrArg (fun k : ℕ =>
        ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X k))
        (by rw [Work.SSSR.down_next_eq]; omega :
          (ComplexShape.down ℕ).next ((s+1)+t) = s + t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
          ((s+1)+t) ((ComplexShape.down ℕ).next ((s+1)+t))))
        (Work.SSSR.iotaTLin p hfib s t b σ h z))
    = ∑ i : Fin (s+2), (-1 : ℤ)^((i : ℕ)) • Work.SSSR.iotaTLinFace p hfib s t b σ h i z := by
  -- Lemma 1: a differential followed by a degree transport is the differential at the
  -- transported index.
  rw [iotaTLinD_cast]
  · -- Lemma 2 (`Work.SSSR.iotaTLin` unfolded): the lifted chain is the shuffle chain
    -- `ezLinSnd (s+1) t` of the fundamental `(s+1)`-simplex, pushed into `T_σ` along
    -- `ezSimplex_σ`; since that push-forward is a chain map, the differential moves inside.
    have hunfold : Work.SSSR.iotaTLin p hfib s t b σ h z
        = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h)).f ((s+1)+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.ezLinSnd (s+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.stdIdSimplex (s+1))))) z) := rfl
    conv_lhs => rw [hunfold, Work.SSSR.chainMap_comm_apply_elem]
    -- Lemma 3 (the elementwise Eilenberg–Zilber boundary formula): the boundary of the shuffle
    -- chain is the alternating sum of its face terms; the `∂z`-term dies by `hz`.
    rw [Work.SSSR.ezLinSnd_bdry_elem s t
          (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (s+1)) z hz]
    simp only [map_sum, map_zsmul]
    -- Lemma 4: each face term of the Eilenberg–Zilber boundary is `iotaTLinFace`.
    exact Finset.sum_congr rfl (fun i _ => by
      rw [← Work.SSSR.iotaTLinFace_eq p hfib s t b σ h i z])
  · -- the degree transport
    rw [Work.SSSR.down_next_eq]
    omega

end Work.SSSR
