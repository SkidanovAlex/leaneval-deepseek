import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.isPreconnected_petal
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le
import Submission.Work.FatouCoord.Flower.widePetal_growth
import Submission.Work.FatouCoord.Flower.exists_iterate_mem_Petal
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_injOn
import Submission.Work.FatouCoord.Exist.fatouCoordW_image_bdd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set

namespace Work.FatouParabolic2

/-- **The petal data of a simple parabolic germ.**  For a germ `f z = z + z ^ 2 * h z` satisfying
the quantitative hypotheses `Work.FatouCoord.ParabolicBounds f h a r A A'` there is a level `M > 0`
such that the *explicit* Leau--Fatou petal `Work.FatouCoord.Petal r M` carries the structure
`PetalData f 0` (at the fixed point `0`): open, preconnected, `f`-invariant, all its orbits
converging to `0`, every orbit converging to `0` without attaining it entering it, and with
`Work.FatouCoord.fatouCoord f (1 - a)` as the Fatou coordinate — holomorphic and injective on the
petal, satisfying the Abel equation, with image containing the tail of every horizontal strip.

All ingredients are delivered; the intended proof strategy is:

* `Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le hb` gives `M₀` such that for every `M ≥ M₀` the
  petal `Petal r M` is `f`-invariant with all orbits converging to `0`;
* `Work.FatouCoord.Flower.widePetal_growth hb` gives a level `Ms` (`1 ≤ Ms`, `1 / r < Ms`) with
  `hgr : ∀ W, Ms < sgauge W → Ms < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1/2`;
* `Work.FatouCoord.Flower.exists_iterate_mem_Petal hb hMs hMsr hgr hM hMr` is exactly the `enters`
  clause for the level `M` (needs `1 ≤ M`, `1/r < M`);
* the proof of `Work.FatouCoord.exists_petal_fatouCoord hb` supplies the Fatou-coordinate facts,
  the injectivity and the strip-tail image at the level it chooses; making the thresholds of
  `Work.FatouCoord.Exist.fatouCoordW_differentiable / _abel / _injOn` explicit and taking `M` to be
  the maximum of `M₀`, `Ms`, `1`, `1/r` and those thresholds replays that proof (the statements are
  monotone in the threshold, and the image statement holds at every level `M ≥ 1/r` because its
  witness `chart w` satisfies `M < w.re` and `1/r < ‖w‖`);
* preconnectedness for `M ≥ 1/r` is `Work.FatouParabolic2.isPreconnected_petal`. -/
theorem exists_petalData_germ {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ (M : ℝ) (pd : PetalData f 0), 0 < M ∧ pd.Pa = Work.FatouCoord.Petal r M ∧
      pd.φa = Work.FatouCoord.fatouCoord f (1 - a) := by
  classical
  obtain ⟨M₁, hpetal₁⟩ := Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le hb
  obtain ⟨Ms, hMs1, hMsr, hgr⟩ := Work.FatouCoord.Flower.widePetal_growth hb
  obtain ⟨N₃, hN₃pos, hN₃r, hdiff⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨N₄, hN₄pos, hN₄r, habel⟩ := Work.FatouCoord.Exist.fatouCoordW_abel hb
  obtain ⟨N₅, hN₅pos, hN₅r, hinj⟩ := Work.FatouCoord.Exist.fatouCoordW_injOn hb
  have hr : 0 < r := hb.hr
  -- the level is the maximum of all the thresholds, and at least `1`, `1 / r` and `Ms`
  let s : Finset ℝ := {M₁, Ms, 1, N₃, N₄, N₅, 1 / r}
  have hs : s.Nonempty := ⟨M₁, by simp [s]⟩
  set M : ℝ := s.max' hs with hMdef
  have hle : ∀ x ∈ s, x ≤ M := fun x hx => by rw [hMdef]; exact Finset.le_max' s x hx
  have hM₁ : M₁ ≤ M := hle M₁ (by simp [s])
  have hMs : Ms ≤ M := hle Ms (by simp [s])
  have h1M : (1 : ℝ) ≤ M := hle 1 (by simp [s])
  have hN₃ : N₃ ≤ M := hle N₃ (by simp [s])
  have hN₄ : N₄ ≤ M := hle N₄ (by simp [s])
  have hN₅ : N₅ ≤ M := hle N₅ (by simp [s])
  have h1r : 1 / r ≤ M := hle (1 / r) (by simp [s])
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one h1M
  have hMr : 1 / r < M := lt_of_lt_of_le hMsr hMs
  obtain ⟨hmap, hconv⟩ := hpetal₁ M hM₁
  -- differentiability of the Fatou coordinate on the petal
  have hdiffM : DifferentiableOn ℂ (Work.FatouCoord.fatouCoord f (1 - a))
      (Work.FatouCoord.Petal r M) := by
    have hmaps : MapsTo Work.FatouCoord.chart (Work.FatouCoord.Petal r M) {w : ℂ | N₃ < w.re} :=
      fun z hz => lt_of_le_of_lt hN₃ (Work.FatouCoord.chart_mem_of_mem_petal hz)
    exact hdiff.comp Work.FatouCoord.differentiableOn_chart_petal hmaps
  -- the Abel equation on the petal
  have habelM : ∀ z ∈ Work.FatouCoord.Petal r M,
      Work.FatouCoord.fatouCoord f (1 - a) (f z) = Work.FatouCoord.fatouCoord f (1 - a) z + 1 := by
    intro z hz
    have hcw : N₄ < (Work.FatouCoord.chart z).re :=
      lt_of_le_of_lt hN₄ (Work.FatouCoord.chart_mem_of_mem_petal hz)
    have h1 : Work.FatouCoord.chart (f z) = Work.FatouCoord.wMap f (Work.FatouCoord.chart z) :=
      Work.FatouCoord.chart_comp f (Work.FatouCoord.ne_zero_of_mem_Petal hz)
    simp only [Work.FatouCoord.fatouCoord_eq]
    rw [h1, habel (Work.FatouCoord.chart z) hcw]
  -- injectivity of the Fatou coordinate on the petal
  have hinjM : Set.InjOn (Work.FatouCoord.fatouCoord f (1 - a)) (Work.FatouCoord.Petal r M) := by
    intro z hz z' hz' heq
    have hcz : N₅ < (Work.FatouCoord.chart z).re :=
      lt_of_le_of_lt hN₅ (Work.FatouCoord.chart_mem_of_mem_petal hz)
    have hcz' : N₅ < (Work.FatouCoord.chart z').re :=
      lt_of_le_of_lt hN₅ (Work.FatouCoord.chart_mem_of_mem_petal hz')
    have hch : Work.FatouCoord.chart z = Work.FatouCoord.chart z' := hinj hcz hcz' heq
    calc z = Work.FatouCoord.chart (Work.FatouCoord.chart z) :=
          (Work.FatouCoord.chart_chart (Work.FatouCoord.ne_zero_of_mem_Petal hz)).symm
      _ = Work.FatouCoord.chart (Work.FatouCoord.chart z') := by rw [hch]
      _ = z' := Work.FatouCoord.chart_chart (Work.FatouCoord.ne_zero_of_mem_Petal hz')
  -- the image of the petal exhausts the tail of every horizontal strip
  have himg : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Work.FatouCoord.Petal r M, Work.FatouCoord.fatouCoord f (1 - a) z = τ := by
    intro B _
    obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.fatouCoordW_image_bdd hb M B
    refine ⟨C, ?_⟩
    intro τ hτ hτB
    obtain ⟨w, hw, hψ⟩ := hC τ hτ hτB
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hw
      simp at hw
      exact absurd hw (not_lt_of_ge hMpos.le)
    have hwr : 1 / r < ‖w‖ :=
      lt_of_lt_of_le (lt_of_le_of_lt h1r hw) (Complex.re_le_norm w)
    refine ⟨Work.FatouCoord.chart w, ?_, ?_⟩
    · have hcz : Work.FatouCoord.chart (Work.FatouCoord.chart w) = w :=
        Work.FatouCoord.chart_chart hw0
      rw [Work.FatouCoord.chart_mem_Petal_iff hr (Work.FatouCoord.chart_ne_zero hw0), hcz]
      exact ⟨hw, hwr⟩
    · simp only [Work.FatouCoord.fatouCoord_eq, Work.FatouCoord.chart_chart hw0, hψ]
  have hpd : ∃ pd : PetalData f 0, pd.Pa = Work.FatouCoord.Petal r M ∧
      pd.φa = Work.FatouCoord.fatouCoord f (1 - a) :=
    ⟨{ Pa := Work.FatouCoord.Petal r M
       φa := Work.FatouCoord.fatouCoord f (1 - a)
       isOpen_Pa := Work.FatouCoord.isOpen_Petal
       isPreconnected_Pa := isPreconnected_petal hr h1r
       z₀_not_mem := Work.FatouCoord.not_mem_Petal_zero
       mapsTo_Pa := hmap
       tendsto_Pa := hconv
       enters_Pa := Work.FatouCoord.Flower.exists_iterate_mem_Petal hb hMs1 hMsr hgr h1M hMr
       φa_diff := hdiffM
       φa_shift := habelM
       φa_inj := hinjM
       image_strip := himg }, rfl, rfl⟩
  obtain ⟨pd, hPd, hφ⟩ := hpd
  exact ⟨M, pd, hMpos, hPd, hφ⟩

end Work.FatouParabolic2
