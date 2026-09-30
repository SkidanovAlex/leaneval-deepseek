import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.ezLinSnd_d_zero
import Submission.Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR
import Submission.Work.SSSR.chainCondAux
import Submission.Work.SSSR.sndToSerre_range
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Eilenberg–Zilber chain `cruxChain` of the mixed evaluation lies in the Serre filtration `A_{s+1}`

`Work.Pi6.MSS.cruxChain 𝕜 p hfib s q σ z` is the image in `C_*(E)` of the Eilenberg–Zilber chain
`iotaT` of a simplex `σ : Δ[s] ⟶ Sing B` and a fibre chain `z` of degree `q` over the first vertex of
`σ`.  Since the second projection `T_σ ⟶ Sing E` factors through the `(s+1)`-st Serre subcomplex
`A_{s+1} = (sSingP p) ⁻¹' (sk (s+1))`, every such chain has a canonical lift to `C_*(A_{s+1})`; the
statement below also records that the image of this lift in the graded piece `Kg s` is a *cycle* —
the chain level form of the fact that the fibre class `ι_σ z` of a cycle `z` is a cycle of the
`σ`-piece.

The proof splits into three cases.

* `σ` nondegenerate (`s = k+1`): the lift is `sCCMap (sndToR (sSingP p) y) (cruxIota …)` where
  `y : nIndex (Sing B) (k+1)` is the nondegenerate simplex underlying `σ`; its boundary is
  `incF (Fc p) k` of an explicit chain of `A_{k+1}` (`Work.SSSR.d_sndToR_iotaTLin`), which
  `Kgπ 𝕜 p (k+1) = coker (incF (Fc p) k)` kills.
* `σ` degenerate (`s = k+1`): here the image of the second projection already lies in the smaller
  subcomplex `A_{k+1}`, so the lift factors through `incF (Fc p) k` and its `Kg`-class is `0`.
* `s = 0`: `Kgπ 𝕜 p 0` is the identity and `Kg 𝕜 p 0 = C_*(A_1)`, so the class of the lift *is* the
  lift; here `σ` is a vertex and the Eilenberg–Zilber chain is a cycle whenever `z` is
  (`ezLinSnd_d_zero`, the `P = 0` case of the Eilenberg–Zilber derivation).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The simplex map `nIndexSigma Y d` of the `nIndexEquiv`-image of a nondegenerate `d`-simplex `x`
of `Y` is `yonedaEquiv.symm x`. -/
lemma nIndexSigma_nIndexEquiv_eq {Y : SSet.{0}} {d : ℕ} (x : Y.nonDegenerate d) :
    Work.SSSR.nIndexSigma Y d (Work.SSSR.nIndexEquiv Y d x) = SSet.yonedaEquiv.symm x.1 := by
  rw [Work.SSSR.nIndexSigma]
  congr 1

/-- `sCCMap` of a composite of simplicial maps, evaluated on an element. -/
lemma sCCMap_apply_comp (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜] {X Y Z : SSet.{0}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (x : (Work.SSSR.sCC 𝕜 X).X n) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 h).f n))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 g).f n)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (g ≫ h)).f n)) x := by
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
    ← Work.SSSR.sCCMap_comp']

variable (𝕜 : Type) [Field 𝕜] (p : C(E, B))

/-- `Kgπ 𝕜 p (k+1)`, the projection onto the `(k+1)`-st graded piece, kills the image of the
inclusion `incF (Fc 𝕜 p) k` of the chains of `A_{k+1}` into those of `A_{k+2}`. -/
lemma Kgπ_incF_apply (k n : ℕ) (y : ((Work.SSSR.Fc (R := 𝕜) p).obj k).X n) :
    (ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k + 1)).f n))
        ((ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.Fc (R := 𝕜) p) k).f n)) y) = 0 := by
  rw [Work.SSSR.grFι_succ (R := 𝕜) (Work.SSSR.sSingP p) k, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, cokernel.condition]
  simp

variable (hfib : Work.StemsB.IsSerreFibration p)

/-- The `k`-th Serre subcomplex of `Sing E` over `Sing B`, as a simplicial set. -/
abbrev sserA (k : ℕ) : SSet.{0} :=
  ((Work.SSSR.StemsB.serreSubcomplex (Work.SSSR.sSingP p) k :
    (Work.SSSR.sSing E).Subcomplex) : SSet)

/-- Its inclusion into `Sing E`. -/
abbrev sserInc (k : ℕ) : sserA (p := p) k ⟶ Work.SSSR.sSing E :=
  (Work.SSSR.StemsB.serreSubcomplex (Work.SSSR.sSingP p) k).ι

/-- The chain complex of `sserA p k`. -/
abbrev sserCC (k : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.sCC 𝕜 (sserA (p := p) k)

/-- The simplex map attached to a nondegenerate `d`-simplex `y` of `Sing B`. -/
abbrev nSig (d : ℕ) (y : Work.SSSR.nIndex (Work.SSSR.sSing B) d) :
    (SSet.stdSimplex.obj (SimplexCategory.mk d) : SSet.{0}) ⟶ Work.SSSR.sSing B :=
  Work.SSSR.nIndexSigma (Work.SSSR.sSing B) d y

/-- The value of the `n`-th component of a chain map on an element. -/
abbrev ev {C D : ChainComplex (ModuleCat 𝕜) ℕ} (n : ℕ) (f : C ⟶ D) (x : C.X n) : D.X n :=
  (ModuleCat.Hom.hom (f.f n)) x

/-- The Eilenberg–Zilber chain `cruxIota` of a *vertex* `σ : Δ[0] ⟶ Sing B` and a cycle `z` of the
fibre over that vertex is a cycle of `C(T_σ)`: for a vertex there are no `X`-face terms in the
Eilenberg–Zilber derivation. -/
lemma d_cruxIota_zero (q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
        ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (0 + q)
        ((ComplexShape.down ℕ).next (0 + q))))
      (cruxIota 𝕜 p hfib 0 q σ z) = 0 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show (ComplexShape.down ℕ).next (0 + 0) = 0 from by rw [Work.SSSR.down_next_eq]]
    rw [HomologicalComplex.shape _ 0 0 (by rw [ComplexShape.down_Rel]; omega)]
    simp
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hnext : (ComplexShape.down ℕ).next (0 + (q' + 1)) = 0 + q' := by
      rw [Work.SSSR.down_next_eq]; omega
    rw [show cruxIota 𝕜 p hfib 0 (q' + 1) σ z
        = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + (q' + 1))))
          (Work.SSSR.ezLinSnd 0 (q' + 1) (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSS.sigmaVert σ)))
            (Work.SSSR.stdIdSimplex 0) z) from
      Work.SSSR.iotaT_eq_ezLinSnd_gen (R := 𝕜) p hfib 0 (q' + 1) (Work.SSS.sigmaVert σ) σ rfl z]
    rw [Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.sCCMap 𝕜 (Work.SSSR.ezSimplex p
      (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl))]
    rw [hnext]
    have h2 : (ModuleCat.Hom.hom
          ((Work.SSSR.sCC 𝕜 ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
            Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSS.sigmaVert σ)))).d (0 + (q' + 1)) (0 + q')))
        ((ModuleCat.Hom.hom (Work.SSSR.ezLinSnd 0 (q' + 1)
            (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSS.sigmaVert σ)))
            (Work.SSSR.stdIdSimplex 0))) z)
      = (ModuleCat.Hom.hom (Work.SSSR.ezLinSnd 0 q'
            (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSS.sigmaVert σ)))
            (Work.SSSR.stdIdSimplex 0)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
            (Work.SSS.sigmaVert σ)))).d (q' + 1) q')) z) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        ezLinSnd_d_zero 𝕜 q' (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSS.sigmaVert σ)))
          (Work.SSSR.stdIdSimplex 0),
        ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h2]
    rw [show (ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
          (Work.SSS.sigmaVert σ)))).d (q' + 1) q')) z = 0 from by
      rw [show (ComplexShape.down ℕ).next (q' + 1) = q' from ChainComplex.next_nat_succ q'] at hz
      exact hz]
    simp

end

/-- The Eilenberg–Zilber chain `cruxChain` of the mixed evaluation has a lift to the chains of the
`(s+1)`-st Serre subcomplex whose class in the graded piece `Kg s` is a cycle. -/
theorem cruxChain_mem_A (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
        ((ComplexShape.down ℕ).next q) z = 0) :
    ∃ C : ↥((Work.Pi6.MSS.Cc 𝕜 p (s+1)).X (s+q)),
      (Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q) C
          = Work.Pi6.MSS.cruxChain 𝕜 p hfib s q σ z ∧
      (Work.Pi6.MSS.Kg 𝕜 p s).d (s+q) ((ComplexShape.down ℕ).next (s+q))
          ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (s+q) C) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos s with hs | hs
  · -- ## `s = 0`
    subst hs
    have hnd : SSet.yonedaEquiv σ ∈ (Work.SSSR.sSing B).nonDegenerate 0 := by
      rw [SSet.nondegenerate_zero]; exact Set.mem_univ _
    obtain ⟨y, hy⟩ : ∃ y : Work.SSSR.nIndex (Work.SSSR.sSing B) 0,
        Work.SSSR.nIndexSigma (Work.SSSR.sSing B) 0 y = σ :=
      ⟨Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) 0 ⟨SSet.yonedaEquiv σ, hnd⟩, by
        rw [nIndexSigma_nIndexEquiv_eq]; exact Equiv.symm_apply_apply _ _⟩
    cases hy
    refine ⟨(ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
      (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f (0 + q)))
      (cruxIota 𝕜 p hfib 0 q (nSig 0 y) z), ?_, ?_⟩
    · change (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (sserInc (p := p) (0+1))).f (0 + q)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
            (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f (0 + q)))
            (cruxIota 𝕜 p hfib 0 q (nSig 0 y) z))
        = Work.Pi6.MSS.cruxChain 𝕜 p hfib 0 q (nSig 0 y) z
      rw [sCCMap_apply_comp, Work.SSSR.sndToR_ι]
      rfl
    · change (ModuleCat.Hom.hom ((sserCC 𝕜 p (0+1)).d (0 + q) ((ComplexShape.down ℕ).next (0 + q))))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
            (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f (0 + q)))
            (cruxIota 𝕜 p hfib 0 q (nSig 0 y) z)) = 0
      rw [Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToR (Work.SSSR.sSingP p) y))
        (cruxIota 𝕜 p hfib 0 q (nSig 0 y) z)]
      have hz0 : (ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜
            (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (nSig 0 y))).d (0 + q)
            ((ComplexShape.down ℕ).next (0 + q))))
          (cruxIota 𝕜 p hfib 0 q (nSig 0 y) z) = 0 :=
        d_cruxIota_zero 𝕜 p hfib q (nSig 0 y) z hz
      rw [hz0]
      simp
  · -- ## `s = k + 1`
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    by_cases hnd : SSet.yonedaEquiv σ ∈ (Work.SSSR.sSing B).nonDegenerate (k+1)
    · -- ## `σ` nondegenerate
      obtain ⟨y, hy⟩ : ∃ y : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1),
          Work.SSSR.nIndexSigma (Work.SSSR.sSing B) (k+1) y = σ :=
        ⟨Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) (k+1) ⟨SSet.yonedaEquiv σ, hnd⟩, by
          rw [nIndexSigma_nIndexEquiv_eq]; exact Equiv.symm_apply_apply _ _⟩
      cases hy
      refine ⟨(ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f ((k+1) + q)))
        (cruxIota 𝕜 p hfib (k+1) q (nSig (k+1) y) z), ?_, ?_⟩
      · change (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (sserInc (p := p) (k+1+1))).f ((k+1) + q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f ((k+1) + q)))
              (cruxIota 𝕜 p hfib (k+1) q (nSig (k+1) y) z))
          = Work.Pi6.MSS.cruxChain 𝕜 p hfib (k+1) q (nSig (k+1) y) z
        rw [sCCMap_apply_comp, Work.SSSR.sndToR_ι]
        rfl
      · exact Kgpi_d_cruxIota_sndToR 𝕜 E B p hfib k q y z hz
    · -- ## `σ` degenerate
      have h1 : SSet.Subcomplex.range (pullback.snd σ (Work.SSSR.sSingP p)) ≤
          Work.SSSR.StemsB.serreSubcomplex (Work.SSSR.sSingP p) (k+1+1) :=
        (Work.SSSR.sndToSerre_range (Work.SSSR.sSingP p)).1 σ
      have h2 : SSet.Subcomplex.range (pullback.snd σ (Work.SSSR.sSingP p)) ≤
          Work.SSSR.StemsB.serreSubcomplex (Work.SSSR.sSingP p) (k+1) :=
        (Work.SSSR.sndToSerre_range (Work.SSSR.sSingP p)).2 σ hnd
      refine ⟨(ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1+1) h1)).f ((k+1) + q)))
        (cruxIota 𝕜 p hfib (k+1) q σ z), ?_, ?_⟩
      · change (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (sserInc (p := p) (k+1+1))).f ((k+1) + q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1+1) h1)).f ((k+1) + q)))
              (cruxIota 𝕜 p hfib (k+1) q σ z))
          = Work.Pi6.MSS.cruxChain 𝕜 p hfib (k+1) q σ z
        rw [sCCMap_apply_comp, Work.SSSR.sndToSerre_ι]
        rfl
      · change (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p))
              (k+1)).d ((k+1) + q) ((ComplexShape.down ℕ).next ((k+1) + q))))
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f ((k+1) + q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
                (Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1+1) h1)).f ((k+1) + q)))
                (cruxIota 𝕜 p hfib (k+1) q σ z))) = 0
        have hfac : Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1) h2 ≫
              Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono (Work.SSSR.sSingP p)
                (Nat.le_succ (k+1)))
            = Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1+1) h1 := by
          apply (cancel_mono (Work.SSSR.StemsB.serreSubcomplex
            (Work.SSSR.sSingP p) (k+1+1)).ι).1
          rw [Category.assoc, Subfunctor.homOfLe_ι, Work.SSSR.sndToSerre_ι,
            Work.SSSR.sndToSerre_ι]
        have hC0 : (ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f
              ((k+1) + q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (Work.SSSR.sndToSerre (Work.SSSR.sSingP p) σ (k+1+1) h1)).f ((k+1) + q)))
              (cruxIota 𝕜 p hfib (k+1) q σ z)) = 0 := by
          rw [← hfac, Work.SSSR.sCCMap_comp', HomologicalComplex.comp_f, ModuleCat.hom_comp,
            LinearMap.comp_apply, Work.SSSR.sCCMap_homOfLe_serre_aux]
          exact Kgπ_incF_apply 𝕜 p k ((k+1) + q) _
        rw [hC0, map_zero]
end Work.Pi6.MSS
