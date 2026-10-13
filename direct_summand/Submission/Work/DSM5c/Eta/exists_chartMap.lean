import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.ChartLp
import Submission.Work.DSPB2.Main
import Submission.Work.DSM5c.Eta.EtaMap
import Submission.Work.DSM5c.Eta.EtaCrux

namespace Work.DSM5c.Eta

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-- The chart map `η : chartPresheaf t ⟶ Dp` of the M5c node (gap G1 of
`Submission/Work/DSM5c/NOTES.md` §20.3): a natural family of `W`-linear maps from the honest chart
rings `W[J/t_S] ⊆ W_{t_S}` to the chart untilts `D_S = untiltOf R_S φ_S`, sending the unit
`1 = algebraMap W (chartRing t S) 1` of the chart ring to `1 ∈ D_S` (equivalently, by `W`-linearity:
`η_S 1 = 1`; equivalently the coaugmentation `chartCoaugW t ≫ (Č η).f 0` is the diagonal
`w ↦ (w • 1)_i`).  This is exactly what the M5c transport consumes
(`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2`, `Work.DSM5c.almostAcyc_span_pow`).

Note the hypothesis `hj₀ : t j₀ = Q.ϖ 0 ^ e` (it is the `hj₀` of the frozen `DSMap.Mix2.area_M5c`):
it is what makes `♯(u i) = t i` for *every* index `i`, `u = Work.DSM5c.chartTiltGen …` being the
tilted chart datum (`u j₀ = (ϖ♭)^e` by construction, and `♯((ϖ♭)^e) = ϖ₀^e` is
`DSMap.Mix.perfectoid_varpiFlat_proved`).

Intended route: `η_S` sends the chart generators `t_k/t_i` to `♯(u_k/u_i) ∈ D_S`; as a `W`-linear map
it is the restriction of the localisation map `W_{t_S} →+* D_S[1/♯(u_S)]`
(`IsLocalization.Away.lift`, available since `t_k ↦ ♯(u_k)` and `♯(u_S)` is inverted in the target),
whose image on the chart ring lies in `D_S` because the chart ring is generated as a ring by `W` and
the elements `♯(u_k/u_i) ∈ D_S`; naturality in `S` is the naturality of `♯` along
`Work.DSM5c.untiltOf.map`.  (Route (ii) of NOTES §20.3 — the chart-tilting identification
`chartRing t S ≅ untiltOf (chartRing u S)` composed with `untiltOf.map` along
`chartRing u S ⊆ R_S` — is equally acceptable.) -/
theorem exists_chartMap {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
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
  -- the crux: `vS S = ♯(u_S)` is a non-zero-divisor of `D_S`
  have hreg : ∀ S : Finset ι,
      IsSMulRegular (DS Q t tr htr0 htr j₀ e S) (vS Q hθ t tr htr0 htr j₀ e S) :=
    fun S => isSMulRegular_vS Q hθ t tr htr0 htr j₀ e hj₀ S
  -- hence the localisation map `D_S → D_S[1/v_S]` is injective, and the chart map exists
  have hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S) :=
    injective_locD_of_isSMulRegular_vS Q hθ t tr htr0 htr j₀ e hreg
  exact ⟨etaNat Q hθ t tr htr0 htr j₀ e hj₀ hInj,
    fun S w => etaNat_app_algebraMap Q hθ t tr htr0 htr j₀ e hj₀ hInj S w⟩

end Work.DSM5c.Eta
