import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.V_hasBasis_nhds_one

/-!
# `Work.EKLComp.ball_nhds` — the action of `SL₃(ℝ)` on `X₃` is continuous in the `V`-metric

The frozen contract `Work.EKLContract.V δ` replaces a metric on `G = SL₃(ℝ)` by the entrywise
boxes around the identity, and `V_hasBasis_nhds_one` records that these boxes are a neighbourhood
basis of `1`.  The lemma proved here says that, in this language, the orbit map
`(g, h) ↦ (g * h) • x` is continuous at `(c, 1)`:

given an open `U ∋ c • x`, the elements `g` with `g * c⁻¹ ∈ V ε` (i.e. `g` in the `ε`-box around
`c`) and the elements `h ∈ V δ` satisfy `(g * h) • x ∈ U`.

The mathematical content is small but the decomposition matters: writing `v = g * c⁻¹` (the
`ε`-displacement of `g` from `c`) and `w = c * h * c⁻¹` (the conjugation of `h` by `c`), one has

`g * h = v * (c * h * c⁻¹) * c = v * w * c`,  hence  `(g * h) • x = (v * w) • (c • x)`.

So it suffices to know that the *joint* map `(v, w) ↦ (v * w) • (c • x)` is continuous at
`(1, 1)` — this needs neither large `ε` nor a small ball around `c`: only that:

* the product `SL₃(ℝ) × SL₃(ℝ) → SL₃(ℝ)` and the action `SL₃(ℝ) × X₃ → X₃` are continuous
  (`ContinuousSMul` for the left action on the quotient `SL₃(ℝ)/SL₃(ℤ)`),
* `V` is a neighbourhood basis of `1` (to turn the two `nhds 1` factors of `nhds (1,1)` into
  `V ε` and `V ε₂`),
* conjugation by the fixed element `c` is continuous at `1` (to turn `h ∈ V δ` into
  `c * h * c⁻¹ ∈ V ε₂`).

-/

set_option maxHeartbeats 1000000

open Filter Topology

namespace Work.EKLComp

open Work.EKLContract

/-- **Continuity of the joint product map at `1`.**  For every open `U ∋ c • x` there are
neighbourhoods `A ∋ 1`, `B ∋ 1` of the identity in `SL₃(ℝ)` with `(v * w) • (c • x) ∈ U` for all
`v ∈ A`, `w ∈ B`. -/
theorem exists_nhds_one_mul_smul_subset {U : Set X3} (hU : IsOpen U) (x : X3) (c : SL3)
    (hc : c • x ∈ U) :
    ∃ A ∈ nhds (1 : SL3), ∃ B ∈ nhds (1 : SL3),
      ∀ v ∈ A, ∀ w ∈ B, (v * w) • (c • x) ∈ U := by
  have hF : Continuous fun p : SL3 × SL3 => (p.1 * p.2) • (c • x) :=
    (continuous_fst.mul continuous_snd).smul continuous_const
  have hmem : (fun p : SL3 × SL3 => (p.1 * p.2) • (c • x)) ⁻¹' U ∈
      nhds ((1 : SL3), (1 : SL3)) :=
    (hF.continuousAt (x := ((1 : SL3), (1 : SL3)))).preimage_mem_nhds
      (by simpa using hU.mem_nhds hc)
  rw [nhds_prod_eq] at hmem
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hmem
  exact ⟨A, hA, B, hB, fun v hv w hw => hAB (Set.mk_mem_prod hv hw)⟩

/-- Conjugation by a fixed `c : SL₃(ℝ)` is continuous at `1`, so every `V ε`-neighbourhood of the
identity pulls back to a `V δ`-neighbourhood of the identity. -/
theorem exists_V_conj {c : SL3} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : SL3, h ∈ V δ → c * h * c⁻¹ ∈ V ε := by
  have hconj : Continuous fun h : SL3 => c * h * c⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hVε : V ε ∈ nhds ((fun h : SL3 => c * h * c⁻¹) 1) := by
    simpa using (Work.EKLContract.Lemmas.V_open_one ε hε).1.mem_nhds
      (Work.EKLContract.Lemmas.V_open_one ε hε).2
  have hpre : (fun h : SL3 => c * h * c⁻¹) ⁻¹' V ε ∈ nhds (1 : SL3) :=
    (hconj.continuousAt (x := (1 : SL3))).preimage_mem_nhds hVε
  obtain ⟨δ, hδ, hδsub⟩ := V_hasBasis_nhds_one.mem_iff.mp hpre
  exact ⟨δ, hδ, hδsub⟩

theorem ball_nhds {U : Set Work.EKLContract.X3} (hU : IsOpen U) (x : Work.EKLContract.X3) (c : Work.EKLContract.SL3) (hc : c • x ∈ U) : ∃ ε > 0, ∃ δ > 0, ∀ g h : Work.EKLContract.SL3, g * c⁻¹ ∈ Work.EKLContract.V ε → h ∈ Work.EKLContract.V δ → (g * h) • x ∈ U := by
  obtain ⟨A, hA, B, hB, hAB⟩ := exists_nhds_one_mul_smul_subset hU x c hc
  -- `V ε ⊆ A`, `V ε₂ ⊆ B`
  obtain ⟨ε, hε, hεA⟩ := V_hasBasis_nhds_one.mem_iff.mp hA
  obtain ⟨ε₂, hε₂, hε₂B⟩ := V_hasBasis_nhds_one.mem_iff.mp hB
  -- `h ∈ V δ → c * h * c⁻¹ ∈ V ε₂`
  obtain ⟨δ, hδ, hδsub⟩ := exists_V_conj (c := c) hε₂
  refine ⟨ε, hε, δ, hδ, fun g h hg hh => ?_⟩
  -- `v = g * c⁻¹ ∈ V ε ⊆ A`, `w = c * h * c⁻¹ ∈ V ε₂ ⊆ B`, and `g * h = v * w * c`.
  have hvA : g * c⁻¹ ∈ A := hεA hg
  have hwB : c * h * c⁻¹ ∈ B := hε₂B (hδsub h hh)
  have hgh : g * h = (g * c⁻¹) * (c * h * c⁻¹) * c := by group
  rw [hgh, mul_smul]
  exact hAB (g * c⁻¹) hvA (c * h * c⁻¹) hwB

end Work.EKLComp
