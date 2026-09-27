import Mathlib
import Submission.Work.Drive.chPhiProduct
import Submission.Work.Drive.atlas_transition_deriv
import Submission.Work.Drive.pair_gadget_tendsto
import Submission.Work.Drive.tendsto_gPhi_mul_star_phase
import Submission.Work.Drive.tendsto_chPhi_at_pivot

/-!
# The local form at the pole: `chPhi · star (phase ζ)` has a non-zero limit at `z₀`

This is the chart-family version of `Work.Drive.tendsto_gPhi_mul_star_phase`.  It is the step that
turns the product `chPhi c a ρ` of transfer gadgets into a function with a *simple zero in the chart
`chartAt ℂ z₀`*: dividing by the chart coordinate `ζ x = (chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀`,
i.e. multiplying by `star (phase ζ)`, removes the singularity at the pole and leaves a non-zero
value.

## The computation

Write `d := ζ x` (the preferred chart difference) and `D := (c 0) x - (c 0) z₀`,
`Q := (c 0) (a 1) - (c 0) z₀ ≠ 0` (the chart difference in the *chosen* chart `c 0`, whose second
pivot is `a 1`; `Q ≠ 0` because `a` is injective).  For `x` in the inner region of gadget `0`,

`chGadget c a ρ 0 x = phase (D / (D - Q))`  (`Work.Drive.chGadget_eq_phase`),

and the two elementary identities

* `phase (z / (z - w)) * star (phase z) = star (phase (z - w))` (`z, w ≠ 0`, this is
  `Work.Drive.phase_div_mul_star_phase` with `z := z`, `w := z - w`), and
* `star (phase d) = star (phase D) * phase (D / d)` (`d, D ≠ 0`,
  `Work.Drive.star_phase_eq_star_phase_mul_phase_div`)

give

`chGadget c a ρ 0 x * star (phase d) = star (phase (D - Q)) * phase (D / d)`.

Now `D - Q → -Q ≠ 0` and — this is where the two charts meet — the slope of the chart transition
`(c 0).symm.trans (chartAt ℂ z₀)` at `(c 0) z₀` is non-zero:

* `star (phase (D - Q)) → star (phase (-Q))` (continuity in the chart `c 0`),
* `phase (D / d) → phase (deriv ((c 0).symm.trans (chartAt ℂ z₀)) ((c 0) z₀))`,
  by `Work.Drive.tendsto_transition_slope_of_mem_maximalAtlas` (`D/d` is exactly the slope of the
  reversed transition) and `Work.Drive.deriv_transition_ne_zero_of_mem_maximalAtlas`,

while the product of the *other* gadgets has a non-zero limit at `z₀` (they are continuous there —
`z₀ = a 0` is not one of their pivots, by injectivity of `a` — and each has modulus one off the
pivots, `Work.Drive.norm_chGadget_eq_one`).  Multiplying gives the non-zero limit `u₀`.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## An elementary identity for `star ∘ phase` -/

/-- `star (phase d) = star (phase D) * phase (D / d)` for `d, D ≠ 0`. -/
theorem star_phase_eq_star_phase_mul_phase_div {d D : ℂ} (hd : d ≠ 0) (hD : D ≠ 0) :
    star (phase d) = star (phase D) * phase (D / d) := by
  have hdD : d / D ≠ 0 := div_ne_zero hd hD
  have hDd : D / d ≠ 0 := div_ne_zero hD hd
  have h1 : phase (d / D) * star (phase d) = star (phase D) :=
    phase_div_mul_star_phase hd hD
  have h2 : phase (d / D) * phase (D / d) = 1 := by
    rw [phase_mul hdD hDd]
    have h3 : (d / D) * (D / d) = 1 := by field_simp
    rw [h3]
    simp [phase]
  calc star (phase d) = star (phase d) * (phase (d / D) * phase (D / d)) := by rw [h2, mul_one]
    _ = (phase (d / D) * star (phase d)) * phase (D / d) := by ring
    _ = star (phase D) * phase (D / d) := by rw [h1]

/-! ## The main theorem -/

theorem tendsto_chPhi_mul_star_phase {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} {z₀ : X}
    (ha0 : a 0 = z₀)
    (hca : ∀ i : ℕ, c i ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hρ : ∀ i : ℕ, 0 < ρ i)
    (hinj : Function.Injective a)
    (hchain : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source ∧
      ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i)
    (hwell : ∀ i : ℕ, closure {x : X | x ∈ (c i).source ∧
      (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {x : X | x ∈ (c i).source ∧
      (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite) :
    ∃ u₀ : ℂ, u₀ ≠ 0 ∧ Filter.Tendsto (fun x : X =>
        Work.Drive.chPhi c a ρ x * star (Work.Drive.phase ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀)))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds u₀) := by
  classical
  rw [← ha0]
  -- ### 0. The chain data in usable form
  have hsrc : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source :=
    fun i => ⟨(hchain i).1, (hchain i).2.1⟩
  have hclose : ∀ i : ℕ, ‖chQ c a i - chP c a i‖ < 2 * ρ i := by
    intro i
    have h := (hchain i).2.2
    have hq : ‖chQ c a i - chP c a i‖ = ‖(c i) (a (i + 1)) - (c i) (a i)‖ := by
      simp [chQ, chP]
    rw [hq]
    linarith [hρ i]
  have hlf' : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite :=
    fun A hA => by simpa [chBall] using hlf A hA
  have hsrc0 : a 0 ∈ (c 0).source := (hchain 0).1
  have hsrc1 : a 1 ∈ (c 0).source := (hchain 0).2.1
  have h01 : a 0 ≠ a 1 := fun h => Nat.zero_ne_one (hinj h)
  have hQne : (c 0) (a 1) - (c 0) (a 0) ≠ 0 :=
    sub_ne_zero.mpr fun h => h01 ((c 0).injOn hsrc1 hsrc0 h).symm
  have hPne : (c 0) (a 0) - (c 0) (a 1) ≠ 0 :=
    sub_ne_zero.mpr fun h => h01 ((c 0).injOn hsrc0 hsrc1 h)
  -- ### 1. Only finitely many gadgets are non-trivial near the base point
  obtain ⟨F₀, hF₀⟩ := exists_finset_eventually_chGadget_ne_one (c := c) (a := a) (ρ := ρ) hρ hlf' (a 0)
  set F : Finset ℕ := insert 0 F₀ with hF
  have h0F : (0 : ℕ) ∈ F := by rw [hF]; exact Finset.mem_insert_self 0 F₀
  have hFev : ∀ᶠ y in 𝓝 (a 0), ∀ i : ℕ, chGadget c a ρ i y ≠ 1 → i ∈ F :=
    hF₀.mono fun y hy i hi => by
      rw [hF]
      exact Finset.mem_insert_of_mem (hy i hi)
  -- the product splits off the singular gadget `0`
  have hsplit : ∀ᶠ y in 𝓝 (a 0),
      chPhi c a ρ y = chGadget c a ρ 0 y * ∏ i ∈ F.erase 0, chGadget c a ρ i y := by
    filter_upwards [hFev] with y hy
    conv_lhs => rw [chPhi_eq_prod_of hy, ← Finset.insert_erase h0F]
    rw [Finset.prod_insert (f := fun i => chGadget c a ρ i y) (Finset.notMem_erase 0 F)]
  -- ### 2. The complement product is continuous and non-zero at the base point
  have hrest_tend : Filter.Tendsto (fun y : X => ∏ i ∈ F.erase 0, chGadget c a ρ i y) (𝓝 (a 0))
      (𝓝 (∏ i ∈ F.erase 0, chGadget c a ρ i (a 0))) := by
    refine tendsto_finsetProd _ (fun i hi => ?_)
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hne1 : a 0 ≠ a i := fun h => hi0 (hinj h).symm
    have hne2 : a 0 ≠ a (i + 1) := fun h => Nat.succ_ne_zero i (hinj h).symm
    exact (continuousAt_chGadget (hρ i) (hclose i) (hsrc i).1 (hsrc i).2 (hwell i)
      hne1 hne2).tendsto
  have hrest_ne : (∏ i ∈ F.erase 0, chGadget c a ρ i (a 0)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact chGadget_ne_zero_of_ne_pivots (hsrc i).1 (hsrc i).2
      (fun h => hi0 (hinj h).symm) (fun h => Nat.succ_ne_zero i (hinj h).symm)
  -- ### 3. The normalized singular gadget
  have hsrc0_ev : ∀ᶠ y in 𝓝 (a 0), y ∈ (c 0).source := (c 0).open_source.mem_nhds hsrc0
  have hne1_ev : ∀ᶠ y in 𝓝 (a 0), y ≠ a 1 :=
    eventually_ne_nhds (fun h : a 0 = a 1 => Nat.zero_ne_one (hinj h))
  have hball_ev : ∀ᶠ y in 𝓝 (a 0), ‖(c 0) y - (c 0) (a 0)‖ < 2 * ρ 0 := by
    have hlt : ‖(c 0) (a 0) - (c 0) (a 0)‖ < 2 * ρ 0 := by
      rw [sub_self, norm_zero]
      linarith [hρ 0]
    have hcont : ContinuousAt (fun y : X => ‖(c 0) y - (c 0) (a 0)‖) (a 0) :=
      (((c 0).continuousAt hsrc0).sub continuousAt_const).norm
    exact hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
  have hsrcch_ev : ∀ᶠ y in 𝓝 (a 0), y ∈ (chartAt ℂ (a 0)).source :=
    (chartAt ℂ (a 0)).open_source.mem_nhds (mem_chart_source ℂ (a 0))
  -- on the punctured neighbourhood the normalized gadget is a nice product of phases
  have hev_pair : (fun y : X => chGadget c a ρ 0 y *
        star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0))))
      =ᶠ[𝓝[≠] (a 0)]
      (fun y : X => star (phase ((c 0) y - (c 0) (a 1))) *
        phase (((c 0) y - (c 0) (a 0)) / ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0)))) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hsrc0_ev,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hne1_ev,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hball_ev,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hsrcch_ev] with y hy hy0 hy1 hyb hych
    have hya0 : y ≠ a 0 := by simpa using hy
    have hD : (c 0) y - (c 0) (a 0) ≠ 0 :=
      sub_ne_zero.mpr fun h => hya0 ((c 0).injOn hy0 hsrc0 h)
    have hkey : (c 0) y - (c 0) (a 1)
        = (c 0) y - (c 0) (a 0) - ((c 0) (a 1) - (c 0) (a 0)) := by ring
    have hDQ : (c 0) y - (c 0) (a 0) - ((c 0) (a 1) - (c 0) (a 0)) ≠ 0 := by
      rw [← hkey]
      exact sub_ne_zero.mpr fun h => hy1 ((c 0).injOn hy0 hsrc1 h)
    have hd : (chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0) ≠ 0 :=
      sub_ne_zero.mpr fun h => hya0 ((chartAt ℂ (a 0)).injOn hych (mem_chart_source ℂ (a 0)) h)
    have hgd : chGadget c a ρ 0 y
        = phase (((c 0) y - chP c a 0) / ((c 0) y - chQ c a 0)) :=
      chGadget_eq_phase ⟨hy0, le_of_lt hyb⟩
    rw [hgd, chP, chQ, hkey, star_phase_eq_star_phase_mul_phase_div hd hD, ← mul_assoc,
      phase_div_mul_star_phase hD hDQ]
  -- ### 4. The two factors of the limit
  have hlim_star : Filter.Tendsto (fun y : X => star (phase ((c 0) y - (c 0) (a 1))))
      (𝓝[≠] (a 0)) (𝓝 (star (phase ((c 0) (a 0) - (c 0) (a 1))))) := by
    have hcont : ContinuousAt (fun y : X => (c 0) y - (c 0) (a 1)) (a 0) :=
      ((c 0).continuousAt hsrc0).sub continuousAt_const
    exact (tendsto_phase_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hPne).star
  have hphase_ratio : Filter.Tendsto (fun y : X =>
        phase (((c 0) y - (c 0) (a 0)) /
          ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0))))
      (𝓝[≠] (a 0))
      (𝓝 (phase (deriv (((chartAt ℂ (a 0)).symm.trans (c 0)) : ℂ → ℂ)
        ((chartAt ℂ (a 0)) (a 0))))) :=
    tendsto_phase_of_tendsto
      (tendsto_transition_slope_of_mem_maximalAtlas (c₀ := chartAt ℂ (a 0)) (c₁ := c 0)
        (IsManifold.chart_mem_maximalAtlas (a 0)) (hca 0)
        (mem_chart_source ℂ (a 0)) hsrc0)
      (deriv_transition_ne_zero_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (a 0)) (hca 0)
        (mem_chart_source ℂ (a 0)) hsrc0)
  have hpair : Filter.Tendsto (fun y : X => chGadget c a ρ 0 y *
        star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0))))
      (𝓝[≠] (a 0))
      (𝓝 (star (phase ((c 0) (a 0) - (c 0) (a 1))) *
        phase (deriv (((chartAt ℂ (a 0)).symm.trans (c 0)) : ℂ → ℂ)
          ((chartAt ℂ (a 0)) (a 0))))) :=
    (hlim_star.mul hphase_ratio).congr' hev_pair.symm
  -- ### 5. Assembly
  refine ⟨(∏ i ∈ F.erase 0, chGadget c a ρ i (a 0)) *
      (star (phase ((c 0) (a 0) - (c 0) (a 1))) *
        phase (deriv (((chartAt ℂ (a 0)).symm.trans (c 0)) : ℂ → ℂ)
          ((chartAt ℂ (a 0)) (a 0)))), ?_, ?_⟩
  · exact mul_ne_zero hrest_ne (mul_ne_zero (star_ne_zero.mpr (phase_ne_zero hPne))
      (phase_ne_zero (deriv_transition_ne_zero_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (a 0)) (hca 0)
        (mem_chart_source ℂ (a 0)) hsrc0)))
  · have hmain : Filter.Tendsto (fun y : X => (∏ i ∈ F.erase 0, chGadget c a ρ i y) *
        (chGadget c a ρ 0 y * star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0)))))
        (𝓝[≠] (a 0))
        (𝓝 ((∏ i ∈ F.erase 0, chGadget c a ρ i (a 0)) *
          (star (phase ((c 0) (a 0) - (c 0) (a 1))) *
            phase (deriv (((chartAt ℂ (a 0)).symm.trans (c 0)) : ℂ → ℂ)
              ((chartAt ℂ (a 0)) (a 0)))))) :=
      (hrest_tend.mono_left nhdsWithin_le_nhds).mul hpair
    refine hmain.congr' ?_
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hsplit] with y hy
    rw [hy]
    ring

end Work.Drive
