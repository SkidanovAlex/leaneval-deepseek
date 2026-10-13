import Mathlib
import Submission.Work.DSM5c.Eta.exists_chartMap
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.Eta.U.EtaMap
import Submission.Work.DSM5c.Eta.U.EtaCrux

namespace Work.DSM5c.Eta

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

/-- **Universe-polymorphic restatement of `Work.DSM5c.Eta.exists_chartMap`** (gap G1: the chart map
`η : chartPresheaf t ⟶ chartD …` with `η_S (algebraMap w) = w • 1`).

The original lives in the `Eta/` subtree, which is stated at `Type 0` and therefore unusable at
`Type a`; the frozen node `DSMap.Mix2.area_M5c` and the assembly in
`Submission/Work/DSM5c/Main.lean` live at `Type a` (`W : Type a`, `ι : Type a`).

The proof transfers verbatim: copy the `Eta/` files on the live path
(`EtaMap.lean`, `EtaCrux.lean`, `chartRing_gLoc_range.lean`, `gLoc_fracU.lean`, `locRes_fracT.lean`,
`tiltChartRes_fracU.lean`, `exists_algHom_of_le_range.lean`, `vS_eq_teich_prod.lean`,
`teich_algebraMap.lean`, `sharp_chartTiltGen.lean`, `chartDMap_teich.lean`,
`isSMulRegular_algebraMap_t.lean`, `isSMulRegular_uProd.lean`, `DS_p_adic_separated.lean`,
`exists_chartMap.lean`, and any others they import) into a *distinct* namespace/module
(e.g. `Work.DSM5c.Eta.U`), replacing the `Type 0` binders by a universe variable; the argument
(`vS = ♯(u_S)` is a non-zero-divisor of `D_S`, so `locD` is injective and the chart generators
`t_k/t_i ↦ ♯(u_k/u_i)` descend) is universe-independent.  Keep the original files. -/
theorem exists_chartMapU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) :
    ∃ η : DSMap.Mix2.chartPresheaf t ⟶
        Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e,
      ∀ (S : (Finset ι)ᵒᵖᵒᵖ) (w : W),
        letI := Work.DSM5c.chartDAlg (p := p) (W := W) Q hθ t tr htr0 htr j₀ e S.unop.unop
        η.app S (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w) =
          w • (1 : Work.DSM5c.untiltOf (p := p) (W := W)
            (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
            (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S.unop.unop)) := by
  -- the crux at an arbitrary universe: `vS S = ♯(u_S)` is a non-zero-divisor of `D_S`,
  -- hence the localisation map `locD S : D_S →+* D_S[1/v_S]` is injective
  have hInj : ∀ S : Finset ι, Function.Injective
      (Work.DSM5c.Eta.U.locD Q hθ t tr htr0 htr j₀ e S) :=
    Work.DSM5c.Eta.U.injective_locD_of_isSMulRegular_vS Q hθ t tr htr0 htr j₀ e
      (fun S => Work.DSM5c.Eta.U.isSMulRegular_vS Q hθ t tr htr0 htr j₀ e hj₀ S)
  -- and the chart map `η` is the descent `Work.DSM5c.Eta.U.etaNat`
  exact ⟨Work.DSM5c.Eta.U.etaNat Q hθ t tr htr0 htr j₀ e hj₀ hInj,
    fun S w => Work.DSM5c.Eta.U.etaNat_app_algebraMap Q hθ t tr htr0 htr j₀ e hj₀ hInj S w⟩

end Work.DSM5c.Eta
