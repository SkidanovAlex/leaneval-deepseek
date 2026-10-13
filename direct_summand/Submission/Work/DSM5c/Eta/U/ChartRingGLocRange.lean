import Mathlib
import Submission.Work.DSM5c.Eta.U.Setup
import Submission.Work.DSM5c.Eta.U.GLocFracU
import Submission.Work.DSM5c.Eta.U.SharpChartTiltGen
import Submission.Work.DSM5c.Eta.U.TeichAlgebraMap

universe a

namespace Work.DSM5c.Eta.U

/-- **The image of the honest chart ring under `gLoc` lands in the chart untilt.**

`Work.DSM5c.Eta.U.gLoc … S : W_{t_S} →+* D_S[1/v_S]` carries the honest chart ring
`chartRing t S = Algebra.adjoin W (chartGens t S)` into the image of
`Work.DSM5c.Eta.U.locD … S : D_S →+* D_S[1/v_S]`.

Proof: the image of `locD` is a subring of `D_S[1/v_S]` containing `gLoc (algebraMap W _ w)`
(`Work.DSM5c.Eta.U.gLoc_algebraMap`) and containing `gLoc x` for the generators
`x ∈ chartGens t S` (witnessed by `i ∈ S`, `j` with `x * algebraMap W _ (t i) = algebraMap W _ (t j)`):
such an `x` is `fracT t S i j hi` (as `algebraMap W _ (t i)` is a unit of `W_{t_S}`, by
`Work.DSM5c.Eta.U.fracT_spec`), so `gLoc x = locD (teich (fracU S i j hi))` by
`Work.DSM5c.Eta.U.gLoc_fracU`.  Hence `Algebra.adjoin W (chartGens t S) ≤ gLoc ⁻¹' (range locD)`
by `Algebra.adjoin_le_iff`.

One of the two remaining inputs for the descent `Work.DSM5c.Eta.U.exists_algHom_of_le_range` producing
the chart map `η` of the M5c node (the other being the injectivity of `locD`, the crux
`Work.DSM5c.Eta.U.isSMulRegular_teich`). -/
theorem chartRing_gLoc_range {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) :
    ∀ x ∈ DSMap.Mix2.chartRing t S,
      ∃ d : Work.DSM5c.Eta.U.DS Q t tr htr0 htr j₀ e S,
        Work.DSM5c.Eta.U.locD Q hθ t tr htr0 htr j₀ e S d
          = Work.DSM5c.Eta.U.gLoc Q hθ t tr htr0 htr j₀ e S x := by
  intro x hx
  -- The set of `x : W_{t_S}` whose `gLoc`-image lies in the image of `locD` is a `W`-subalgebra
  -- of `W_{t_S}` (the image of a ring hom is a subring).
  let T : Subalgebra W (Localization.Away (DSMap.Mix2.tS t S)) :=
    { carrier := {x | ∃ d : Work.DSM5c.Eta.U.DS Q t tr htr0 htr j₀ e S,
        Work.DSM5c.Eta.U.locD Q hθ t tr htr0 htr j₀ e S d
          = Work.DSM5c.Eta.U.gLoc Q hθ t tr htr0 htr j₀ e S x}
      add_mem' := by
        rintro a b ⟨da, hda⟩ ⟨db, hdb⟩
        exact ⟨da + db, by rw [map_add, map_add, hda, hdb]⟩
      mul_mem' := by
        rintro a b ⟨da, hda⟩ ⟨db, hdb⟩
        exact ⟨da * db, by rw [map_mul, map_mul, hda, hdb]⟩
      algebraMap_mem' := fun w =>
        ⟨untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) w,
          (gLoc_algebraMap Q hθ t tr htr0 htr j₀ e S w).symm⟩ }
  -- The chart generators lie in `T`: a generator `x` satisfies `x * t i = t k` with `i ∈ S`, so
  -- `x = t_k/t_i = fracT t S i k hi`, and `gLoc` of that is `locD (teich (fracU …))`.
  have hgen : DSMap.Mix2.chartGens t S ≤ T := by
    rintro x ⟨i, hi, k, hx⟩
    refine ⟨Work.DSM5c.Eta.U.teich Q t tr htr0 htr j₀ e S
      (Work.DSM5c.Eta.U.fracU Q t tr htr0 htr j₀ e S i k hi), ?_⟩
    have hx' : x = fracT t S i k hi := by
      have hu : IsUnit (algebraMap W (Localization.Away (DSMap.Mix2.tS t S)) (t i)) :=
        ⟨unitT t S i hi, unitT_spec t S i hi⟩
      exact IsUnit.mul_right_cancel hu (hx.trans (fracT_spec t S i k hi).symm)
    rw [hx']
    exact (gLoc_fracU Q hθ t tr htr0 htr j₀ e hj₀ S hi k).symm
  -- `chartRing t S = Algebra.adjoin W (chartGens t S)`, so it suffices to adjoin the generators.
  have hle : DSMap.Mix2.chartRing t S ≤ T := by
    rw [DSMap.Mix2.chartRing, Algebra.adjoin_le_iff]
    exact hgen
  exact hle hx

end Work.DSM5c.Eta.U
