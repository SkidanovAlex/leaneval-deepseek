import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.Pi6.MSS.E2cfkHorn
import Submission.Work.Pi6.MSS.fibre_to_pullback
import Submission.Work.Pi6.MSS.horn_to_fibre
import Submission.Work.Pi6.MSS.pieceHorn_lift
import Submission.Work.SSS.sndToSerre_range
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The transport of a fibre cycle along a 1-simplex of the base

`Work.Pi6.MSS.transport_chain`: for a Serre fibration `p : E → B`, a 1-simplex
`σ : Δ[1] ⟶ Sing B` with endpoints `b₀ = sigmaVert σ` and `b₁ = lastVert σ`, and a cycle `z` of the
singular chains of the fibre over `b₀`, there are a cycle `w` of the chains of the fibre over `b₁`
and a `(q+1)`-chain `c` of `E` lying in the second Serre stage such that

`(fibreIncl p b₀)_* z - (fibreIncl p b₁)_* w = ∂ c`.

The proof pushes `z` into the pullback `T_σ = Δ[1] ×_{Sing B} Sing E` along `σ`, uses that the
pair `(T_σ, horn)` is acyclic (`pieceHorn_lift_cycle`) to replace `z` by a cycle `z'` of the horn up
to a boundary, transports `z'` back to the fibre over `b₁` through the isomorphism
`horn ≅ Sing (p⁻¹ b₁)` (`horn_to_fibre`), and checks that the boundary term lies in the second
Serre stage: every simplex of `T_σ` lies over `σ ∘ fst`, and `σ` is a 1-simplex, so its image in
`Sing B` lies in the `2`-skeleton (`Work.SSS.sndToSerre_range`).
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-! ## Auxiliary lemmas on the coproduct description of the singular chains -/

/-- The `n`-th component of a composite of chain maps, applied to a chain. -/
theorem chainMap_comp_apply {𝕜 : Type} [CommRing 𝕜] {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (x : (Work.SSSR.sChains 𝕜 X).X n) :
    ((Work.SSSR.sChainMap 𝕜 g).f n).hom (((Work.SSSR.sChainMap 𝕜 f).f n).hom x)
      = ((Work.SSSR.sChainMap 𝕜 (f ≫ g)).f n).hom x := by
  rw [← Work.SSSR.sChainMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  rfl

/-- Naturality of the differential of a chain map: `d (φ x) = φ (d x)`. -/
theorem chainMap_d_apply {𝕜 : Type} [CommRing 𝕜] {C D : ChainComplex (ModuleCat 𝕜) ℕ}
    (φ : C ⟶ D) (i j : ℕ) (x : C.X i) :
    (D.d i j).hom ((φ.f i).hom x) = (φ.f j).hom ((C.d i j).hom x) := by
  have h := HomologicalComplex.Hom.comm φ i j
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  exact DFunLike.congr_fun h2 x

/-- The fibre inclusion `fIncl` is the chain map induced by `Sing` of the fibre inclusion. -/
theorem fIncl_eq {𝕜 : Type} [CommRing 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) :
    E2cfk.fIncl 𝕜 p b = Work.SSSR.sChainMap 𝕜 (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)) :=
  rfl

/-- The Serre inclusion `sserInc` is the chain map induced by the inclusion of the Serre stage. -/
theorem sserInc_eq {𝕜 : Type} [CommRing 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s : ℕ) :
    E2cfk.sserInc 𝕜 p s = Work.SSSR.sChainMap 𝕜 (E2cfk.sser p s).ι :=
  rfl

/-- **The second projection `T_σ ⟶ Sing E` of the pullback along `σ` lands in the second Serre
stage**, so the `(q+1)`-chains of `T_σ` push forward into the image of `sserInc 𝕜 p 2`. -/
theorem sndToSerre_lift {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    SSet.Subcomplex.range (pullback.snd σ (Work.SSS.sSingP p))
      ≤ Work.StemsB.serreSubcomplex (Work.SSS.sSingP p) 2 :=
  (Work.SSS.sndToSerre_range (Work.SSS.sSingP p)).1 (P := 1) σ

end

end Work.Pi6.MSS

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

theorem transport_chain (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.SSS.sigmaVert σ)).X q)
    (hz : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.SSS.sigmaVert σ)).d q (q - 1) z = 0) :
    ∃ (w : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).X q)
      (c : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X (q + 1)),
      (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).d q (q - 1) w = 0 ∧
      (∃ c' : (((Work.Pi6.MSS.E2cfk.sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
        ((Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 2).f (q + 1)).hom c' = c) ∧
      ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSS.sigmaVert σ)).f q).hom z
        - ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).f q).hom w
        = ((Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d (q + 1) q).hom c := by
  classical
  obtain ⟨κ, hκ⟩ := fibre_to_pullback p σ
  obtain ⟨ψ, hψiso, hψ⟩ := horn_to_fibre p σ
  haveI : IsIso ψ := hψiso
  -- ### The cycle `z`, pushed into the pullback `T_σ` along `σ`
  set z1 : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).X q :=
    ((Work.SSSR.sChainMap 𝕜 κ).f q).hom z with hz1def
  have hz1cyc : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d q (q - 1) z1
      = 0 := by
    rw [hz1def, chainMap_d_apply (Work.SSSR.sChainMap 𝕜 κ) q (q - 1) z, hz]
    exact map_zero _
  -- ### The horn replacement of `z1`
  have hPL : ∃ (z' : (Work.SSSR.sChains 𝕜
        (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).toSSet).X q)
      (c1 : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).X (q + 1)),
      (Work.SSSR.sChains 𝕜 (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).toSSet).d q (q - 1) z'
        = 0 ∧
      z1 = ((Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι).f q).hom z'
        + ((Work.SSSR.sChains 𝕜
            (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d (q + 1) q).hom c1 :=
    Work.Pi6.MSS.pieceHorn_lift_cycle 𝕜 E B p hfib q σ z1 hz1cyc
  obtain ⟨z', c1, hz'cyc, hsplit⟩ := hPL
  -- ### The transported cycle and the correction chain
  set w : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).X q :=
    ((Work.SSSR.sChainMap 𝕜 ψ).f q).hom z' with hwdef
  have hwcyc : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).d q (q - 1) w
      = 0 := by
    rw [hwdef, chainMap_d_apply (Work.SSSR.sChainMap 𝕜 ψ) q (q - 1) z', hz'cyc]
    exact map_zero _
  set c : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X (q + 1) :=
    ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f (q + 1)).hom c1 with hcdef
  refine ⟨w, c, hwcyc, ?_, ?_⟩
  · -- ### The correction chain lies in the second Serre stage
    refine ⟨((Work.SSSR.sChainMap 𝕜
      (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2 (sndToSerre_lift p σ))).f (q + 1)).hom c1, ?_⟩
    have hΦ : CategoryTheory.CategoryStruct.comp
        (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2 (sndToSerre_lift p σ))
        (E2cfk.sser p 2).ι = pullback.snd σ (Work.SSS.sSingP p) :=
      Work.SSS.sndToSerre_ι _ _ _ _
    have hcp : ((Work.SSSR.sChainMap 𝕜 (E2cfk.sser p 2).ι).f (q + 1)).hom
          (((Work.SSSR.sChainMap 𝕜
            (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2 (sndToSerre_lift p σ))).f (q + 1)).hom c1)
        = ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f (q + 1)).hom c1 :=
      chainMap_comp_apply (𝕜 := 𝕜)
        (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2 (sndToSerre_lift p σ)) (E2cfk.sser p 2).ι
        (q + 1) c1
    have hsin : (E2cfk.sserInc 𝕜 p 2)
        = Work.SSSR.sChainMap 𝕜 (E2cfk.sser p 2).ι := sserInc_eq p 2
    rw [hsin]
    exact hcp.trans hcdef.symm
  · -- ### The transport identity
    have hcomp1 : Work.SSSR.sChainMap 𝕜
          (Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.SSS.sigmaVert σ)))
        = Work.SSSR.sChainMap 𝕜 κ ≫
          Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p)) := by
      rw [Work.SSSR.sChainMap_comp]
      exact (congrArg (fun f => Work.SSSR.sChainMap 𝕜 f) hκ).symm
    have hA : ((E2cfk.fIncl 𝕜 p (Work.SSS.sigmaVert σ)).f q).hom z
        = ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f q).hom z1 := by
      rw [fIncl_eq p (Work.SSS.sigmaVert σ), hz1def, hcomp1]
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
      rfl
    have hcomp2 : Work.SSSR.sChainMap 𝕜 ψ ≫
          Work.SSSR.sChainMap 𝕜 (Work.SSS.sSingP
            (Work.StemsB.fibreIncl p (E2cfk.lastVert σ)))
        = Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι ≫
          Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p)) := by
      rw [Work.SSSR.sChainMap_comp, Work.SSSR.sChainMap_comp]
      exact congrArg (fun f => Work.SSSR.sChainMap 𝕜 f) hψ
    have hB : ((E2cfk.fIncl 𝕜 p (E2cfk.lastVert σ)).f q).hom w
        = ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f q).hom
            (((Work.SSSR.sChainMap 𝕜
              (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι).f q).hom z') := by
      have h2 := congrArg (fun φ => (φ.f q).hom z') hcomp2
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      rw [fIncl_eq p (E2cfk.lastVert σ), hwdef]
      exact h2
    have hsub : z1 - ((Work.SSSR.sChainMap 𝕜
          (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι).f q).hom z'
        = ((Work.SSSR.sChains 𝕜
            (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d (q + 1) q).hom c1 := by
      rw [hsplit, add_sub_cancel_left]
    rw [hA, hB, ← map_sub, hsub]
    have hstep : ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f q).hom
          (((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d (q + 1) q).hom c1)
        = ((E2cfk.ECC 𝕜 E).d (q + 1) q).hom
          (((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f (q + 1)).hom c1) :=
      (chainMap_d_apply (Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p)))
        (q + 1) q c1).symm
    rw [hstep, hcdef]

end

end Work.Pi6.MSS
