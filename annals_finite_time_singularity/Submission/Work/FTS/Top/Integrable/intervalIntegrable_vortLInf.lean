import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Top.Defs
import Submission.Work.ConstructionInstance.vorticity_bound_of_strip
import Submission.Work.FTS.Top.Integrable.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal Matrix ENNReal

namespace Work.FTS.Top.Integrable

/-
The Beale--Kato--Majda integrand `s ↦ Work.LWP.vortLInf B.u s = ⨆ x, ‖vorticity (B.u · s) x‖` is
interval-integrable on `[0,t]` for every `t < T`, for a blow-up datum
`B : Work.FTS.Top.BlowupAt α T`.

Route:
* `B.strip` gives `IsContDiffHolderOn ℝ α B.u.uncurry (univ ×ˢ Icc 0 S)` for every `S ∈ Ioo 0 T`;
  pick `S` with `t < S < T` and apply the *proved* workspace result
  `Work.ConstructionInstance.vorticity_bound_of_strip` (a joint `C^{1,α}` strip bound transfers to
  a uniform bound `‖vorticity (u · s) x‖ ≤ K` on the strictly shorter strip `s ∈ Ico 0 t`); then
  `vortLInf B.u s ≤ K` on `Ico 0 t` by `ciSup_le`.  Prove this as a helper
  `exists_bound_vortLInf_on_Ico` first: for `t ∈ Ico 0 T` there is `K ≥ 0` with
  `vortLInf B.u s ≤ K` for all `s ∈ Ico 0 t`.  (This is the honest "compaction" statement for
  `BlowupAt`: the bound is only on closed sub-strips `[0,t]`, `t < T`, which is exactly why the
  interface is not vacuous, unlike `Work.StabilityFar.AssemblyInputs`.)
* the slices `s ↦ ‖vorticity (B.u · s) x‖` are continuous at every `s ∈ Ioo 0 S` for each fixed
  `x`: at such a point `(x,s)` is an interior point of the strip `univ ×ˢ Ico 0 T`, so
  `ContDiffWithinAt` upgrades to `ContDiffAt` (`ContDiffWithinAt.contDiffAt`) and
  `fderiv ℝ B.u.uncurry` is continuous there (`ContDiffAt.continuousAt_fderiv`); combine with the
  description of `vorticity` through `fderiv` at a differentiable point (see
  `Submission/Work/SolutionDelivery/Measurable/continuousOn_vorticity_of_contDiffOn.lean` for the
  technique, or prove it directly using `fderiv_slice_eq`-style lemmas and
  `hasFDerivAt_prodMk_left`).  You may READ files under `Submission/Work/SolutionDelivery/` for
  technique, but do NOT import them.
* hence `s ↦ vortLInf B.u s` is lower semicontinuous on the open set `Ioo 0 t`: given
  `a < ⨆ x, θ x s` there is `x` with `a < θ x s` (use `lt_ciSup_iff` when the range is bounded
  above and `Real.iSup_of_not_bddAbove` otherwise), and `θ x` is continuous at `s`; so
  `{s | a < vortLInf B.u s}` is open there (equivalently use
  `lowerSemicontinuous_iSup`/`lowerSemicontinuous_ciSup`, or a countable dense subset of `R3`);
* a function which is lower semicontinuous on the open set `Ioo 0 t` is Borel measurable there
  (`LowerSemicontinuousOn`/`LowerSemicontinuous.measurable`); `Ioc 0 t` differs from `Ioo 0 t` by
  the null set `{t}`, so `vortLInf B.u` is a.e. strongly measurable on `Ioc 0 t`;
* with a.e. strong measurability on the finite measure space `volume.restrict (Ioc 0 t)` and the
  bound `K` on `Ico 0 t`, `IntegrableOn (vortLInf B.u) (Ioc 0 t) volume` follows from
  `MeasureTheory.Integrable.of_bound` (or `Integrable.mono'` against a constant majorant); finally
  `intervalIntegrable_iff` identifies `IntervalIntegrable f volume 0 t` with
  `IntegrableOn f (uIoc 0 t) volume`, and for `t = 0` the interval is empty (`uIoc 0 0 = ∅`), so
  that case is trivial.  Namespace `Work.FTS.Top`.
-/

/-- **The uniform vorticity bound on a closed sub-strip.**  By
`Work.ConstructionInstance.vorticity_bound_of_strip` applied to the joint `C^{1,α}` strip bound
`B.strip S₂` with `t < S₁ < S₂ < T`, the vorticity of every slice `B.u · s`, `s ∈ (0,t]`, is
bounded by a single constant `K ≥ 0`. -/
theorem exists_bound_vorticity_Ioc {α : NNReal} {T : ℝ} (B : BlowupAt α T) {t : ℝ}
    (ht : t ∈ Set.Ico 0 T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Ioc 0 t, ∀ x : R3, ‖vorticity (B.u · s) x‖ ≤ K := by
  obtain ⟨S₁, htS₁, hS₁T⟩ := exists_between ht.2
  obtain ⟨S₂, hS₁S₂, hS₂T⟩ := exists_between hS₁T
  have hS₁pos : 0 < S₁ := lt_of_le_of_lt ht.1 htS₁
  have hS₂pos : 0 < S₂ := lt_trans hS₁pos hS₁S₂
  obtain ⟨K, hKnn, hK⟩ := Work.ConstructionInstance.vorticity_bound_of_strip (u := B.u)
    (S := S₂) (T := S₁) hS₁S₂ (B.strip S₂ ⟨hS₂pos, hS₂T⟩)
  exact ⟨K, hKnn, fun s hs x => hK s ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 htS₁⟩ x⟩

/-- **Joint continuity of the vorticity on an open strip.**  For `t ∈ Ico 0 T` there is `S` with
`t < S < T`; on the open strip `ℝ³ × (0,S)` — which contains `ℝ³ × (0,t]` — the map
`(x,s) ↦ ‖vorticity (B.u · s) x‖` is continuous (`continuousOn_vorticity_joint`). -/
theorem exists_continuousOn_vorticity {α : NNReal} {T : ℝ} (B : BlowupAt α T) {t : ℝ}
    (ht : t ∈ Set.Ico 0 T) :
    ∃ S : ℝ, t < S ∧
      ContinuousOn (fun p : R3 × ℝ => ‖vorticity (B.u · p.2) p.1‖) (Set.univ ×ˢ Set.Ioo 0 S) := by
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hSpos : 0 < S := lt_of_le_of_lt ht.1 htS
  exact ⟨S, htS, continuousOn_vorticity_joint (B.strip S ⟨hSpos, hST⟩).1⟩

/-- **A supremum over a separable family is a.e. strongly measurable on a right interval.**

Let `θ : ℝ³ → ℝ → ℝ` be such that `(y,s) ↦ θ y s` is continuous on the open strip `ℝ³ × (0,S)` and
such that for every `s ∈ (0,t]` the family `y ↦ θ y s` is bounded above.  Then `s ↦ ⨆ y, θ y s` is
a.e. strongly measurable on `(0,t]`.

Indeed, on `(0,t]` the function `s ↦ ⨆ y, θ y s` coincides with the supremum over a countable dense
subset `J ⊆ ℝ³` of the functions `s ↦ θ j s`, which are continuous on `(0,S) ⊇ (0,t]` and hence
a.e. strongly measurable; a countable supremum of such functions is a.e. strongly measurable
(`AEMeasurable.iSup`).  The two suprema agree at `s ∈ (0,t]` because the slice `y ↦ θ y s` is
continuous and bounded above: `≤` is `le_ciSup`, while for `≥` one uses that `{y | c < θ y s}` is a
neighbourhood of any `x` with `c < θ x s`, and the dense `J` meets it. -/
theorem aemeasurable_ciSup_of_continuousOn {θ : R3 → ℝ → ℝ} {S t : ℝ}
    (ht : 0 ≤ t) (htS : t < S)
    (hcont : ContinuousOn (fun p : R3 × ℝ => θ p.1 p.2) (Set.univ ×ˢ Set.Ioo 0 S))
    (hbdd : ∀ s ∈ Set.Ioc 0 t, BddAbove (Set.range fun y : R3 => θ y s)) :
    AEMeasurable (fun s => ⨆ y, θ y s) (volume.restrict (Set.Ioc 0 t)) := by
  obtain ⟨J, hJc, hJd⟩ := TopologicalSpace.exists_countable_dense R3
  haveI : Countable J := hJc.to_subtype
  haveI : Nonempty J := ⟨hJd.nonempty.some, hJd.nonempty.some_mem⟩
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo 0 S : Set (R3 × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hsub : Set.Ioc 0 t ⊆ Set.Ioo 0 S := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htS⟩
  -- each `s ↦ θ j s` is continuous on the open strip
  have hslice : ∀ j : J, ContinuousOn (fun s => θ (j : R3) s) (Set.Ioo 0 S) := by
    intro j
    have hmap : Set.MapsTo (fun s : ℝ => ((j : R3), s)) (Set.Ioo 0 S)
        (Set.univ ×ˢ Set.Ioo 0 S) := fun s hs => ⟨trivial, hs⟩
    exact hcont.comp' ((continuous_const.prodMk continuous_id).continuousOn) hmap
  have hmeas : ∀ j : J, AEMeasurable (fun s => θ (j : R3) s)
      (volume.restrict (Set.Ioc 0 t)) := fun j =>
    ((hslice j).aemeasurable measurableSet_Ioo).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hsup : AEMeasurable (fun s => ⨆ j : J, θ (j : R3) s)
      (volume.restrict (Set.Ioc 0 t)) := AEMeasurable.iSup hmeas
  refine AEMeasurable.congr hsup ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
  have hsS : s ∈ Set.Ioo 0 S := hsub hs
  have hbddJ : BddAbove (Set.range fun j : J => θ (j : R3) s) := by
    obtain ⟨c, hc⟩ := hbdd s hs
    exact ⟨c, by rintro y ⟨j, rfl⟩; exact hc ⟨(j : R3), rfl⟩⟩
  refine le_antisymm (ciSup_le fun j => le_ciSup (hbdd s hs) (j : R3)) (ciSup_le fun x => ?_)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hxcont : ContinuousAt (fun y : R3 => θ y s) x := by
    have hF : Tendsto (fun p : R3 × ℝ => θ p.1 p.2) (𝓝 (x, s)) (𝓝 (θ x s)) :=
      (hcont.continuousWithinAt ⟨trivial, hsS⟩).continuousAt (hopen.mem_nhds ⟨trivial, hsS⟩)
    have h2 : Tendsto (fun y : R3 => (y, s)) (𝓝 x) (𝓝 (x, s)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have h3 : Tendsto ((fun p : R3 × ℝ => θ p.1 p.2) ∘ fun y : R3 => (y, s)) (𝓝 x) (𝓝 (θ x s)) :=
      hF.comp h2
    change Tendsto ((fun p : R3 × ℝ => θ p.1 p.2) ∘ fun y : R3 => (y, s)) (𝓝 x) (𝓝 (θ x s))
    exact h3
  have hmem : {y : R3 | θ x s - ε < θ y s} ∈ 𝓝 x := by
    have hlt : θ x s - ε < θ x s := by linarith
    have h1 : (fun y : R3 => θ y s) ⁻¹' Set.Ioi (θ x s - ε) ∈ 𝓝 x :=
      hxcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (s := Set.Ioi (θ x s - ε)) hlt)
    have h2 : (fun y : R3 => θ y s) ⁻¹' Set.Ioi (θ x s - ε) = {y : R3 | θ x s - ε < θ y s} := by
      ext y
      simp
    rw [h2] at h1
    exact h1
  have hj := hJd.inter_nhds_nonempty hmem
  have hjJ : hj.some ∈ J := mem_of_mem_inter_left hj.some_mem
  have hjmem : hj.some ∈ {y : R3 | θ x s - ε < θ y s} := mem_of_mem_inter_right hj.some_mem
  have hjval : θ x s - ε < θ hj.some s := hjmem
  have hle : θ hj.some s ≤ ⨆ j : J, θ (j : R3) s := le_ciSup hbddJ ⟨hj.some, hjJ⟩
  linarith

theorem intervalIntegrable_vortLInf {α : NNReal} {T : ℝ} (B : Work.FTS.Top.BlowupAt α T) :
    ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf B.u) volume 0 t := by
  intro t ht
  obtain ⟨K, hKnn, hK⟩ := exists_bound_vorticity_Ioc B ht
  obtain ⟨S, htS, hcont⟩ := exists_continuousOn_vorticity B ht
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
  change IntegrableOn (fun s => ⨆ x, ‖vorticity (B.u · s) x‖) (Set.Ioc 0 t) volume
  have hbdd : ∀ s ∈ Set.Ioc 0 t, BddAbove (Set.range fun x : R3 => ‖vorticity (B.u · s) x‖) :=
    fun s hs => ⟨K, by rintro y ⟨x, rfl⟩; exact hK s hs x⟩
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ K ?_
  · exact (aemeasurable_ciSup_of_continuousOn ht.1 htS hcont hbdd).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have hle : (⨆ x, ‖vorticity (B.u · s) x‖) ≤ K := ciSup_le fun x => hK s hs x
    have hnn : 0 ≤ ⨆ x, ‖vorticity (B.u · s) x‖ :=
      le_trans (norm_nonneg _) (le_ciSup (hbdd s hs) (0 : R3))
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, hle⟩

end Work.FTS.Top.Integrable
