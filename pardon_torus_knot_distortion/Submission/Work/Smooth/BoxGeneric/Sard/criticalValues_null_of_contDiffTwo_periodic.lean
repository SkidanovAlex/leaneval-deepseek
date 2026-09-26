import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_critical_null
import Submission.Work.Smooth.BoxGeneric.Sard.volume_image_null_of_partials_fderiv_eq_zero

/-!
# Two-dimensional Sard for periodic `C²` functions

The critical values of a `C²` function `G : ℝ × ℝ → ℝ`

* the set `{u | ∃ p, G p = u ∧ fderiv ℝ G p = 0}`

has Lebesgue measure zero.  Neither the periodicity hypotheses nor the full strength of `C²`
(with respect to a mere Lipschitz hypothesis on the gradient) are used beyond the fact that `G`
is twice continuously differentiable; the extra hypotheses only record the intended setting.

## Proof

Write `S = {p | fderiv ℝ G p = 0}` for the critical set and split

`S = B₀ ∪ B₁ₓ ∪ B₁_y`

where, with `Gₓ = fderiv ℝ G · (1, 0)` and `G_y = fderiv ℝ G · (0, 1)` the two partial
derivatives,

* `B₀ = {p ∈ S | fderiv ℝ Gₓ p = 0 ∧ fderiv ℝ G_y p = 0}` is the set of points at which the
  gradient *and* the Hessian vanish.  On such a set `G` is flat to second order, so `G '' B₀` is
  null (the sibling lemma `volume_image_null_of_partials_fderiv_eq_zero`, a covering argument);
* on `B₁ₓ = {p ∈ S | fderiv ℝ Gₓ p ≠ 0}` the level set `{Gₓ = 0}` is a `C¹` curve through every
  point (implicit function theorem), and `S ∩ {Gₓ = 0}` is contained in the critical set of the
  restriction of `G` to the curve, so Sard in dimension one (the sibling lemma
  `exists_isOpen_volume_image_critical_null`) makes `G '' B₁ₓ` locally null; a Lindelöf cover
  globalises this.  The set `B₁_y` is treated symmetrically.
-/

open MeasureTheory Set

open scoped Topology

namespace Work.Smooth.BoxGeneric.Sard

set_option linter.unusedVariables false in
theorem criticalValues_null_of_contDiffTwo_periodic {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hper₁ : ∀ p : ℝ × ℝ, G (p.1 + 2 * Real.pi, p.2) = G p) (hper₂ : ∀ p : ℝ × ℝ, G (p.1, p.2 + 2 * Real.pi) = G p) : MeasureTheory.volume {u : ℝ | ∃ p : ℝ × ℝ, G p = u ∧ fderiv ℝ G p = 0} = 0 := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  set Gx : ℝ × ℝ → ℝ := fun p => fderiv ℝ G p ((1 : ℝ), 0) with hGx
  set Gy : ℝ × ℝ → ℝ := fun p => fderiv ℝ G p ((0 : ℝ), 1) with hGy
  have hGxcd : ContDiff ℝ 1 Gx := by
    rw [hGx]
    exact (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hGycd : ContDiff ℝ 1 Gy := by
    rw [hGy]
    exact (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  set B0 : Set (ℝ × ℝ) :=
    {p | fderiv ℝ G p = 0 ∧ fderiv ℝ Gx p = 0 ∧ fderiv ℝ Gy p = 0} with hB0
  set B1x : Set (ℝ × ℝ) := {p | fderiv ℝ G p = 0 ∧ fderiv ℝ Gx p ≠ 0} with hB1x
  set B1y : Set (ℝ × ℝ) := {p | fderiv ℝ G p = 0 ∧ fderiv ℝ Gy p ≠ 0} with hB1y
  have hmemB0 : ∀ p : ℝ × ℝ,
      p ∈ B0 ↔ fderiv ℝ G p = 0 ∧ fderiv ℝ Gx p = 0 ∧ fderiv ℝ Gy p = 0 :=
    fun p => by simp [hB0]
  have hmemB1x : ∀ p : ℝ × ℝ, p ∈ B1x ↔ fderiv ℝ G p = 0 ∧ fderiv ℝ Gx p ≠ 0 :=
    fun p => by simp [hB1x]
  have hmemB1y : ∀ p : ℝ × ℝ, p ∈ B1y ↔ fderiv ℝ G p = 0 ∧ fderiv ℝ Gy p ≠ 0 :=
    fun p => by simp [hB1y]
  have hset : {u : ℝ | ∃ p : ℝ × ℝ, G p = u ∧ fderiv ℝ G p = 0}
      = G '' ({p : ℝ × ℝ | fderiv ℝ G p = 0}) := by
    ext u; constructor
    · rintro ⟨p, hp, hd⟩; exact ⟨p, hd, hp⟩
    · rintro ⟨p, hd, hp⟩; exact ⟨p, hp, hd⟩
  rw [hset]
  have hSB : ({p : ℝ × ℝ | fderiv ℝ G p = 0}) = B0 ∪ B1x ∪ B1y := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, hmemB0 p, hmemB1x p, hmemB1y p]
    constructor
    · intro hp
      by_cases h1 : fderiv ℝ Gx p = 0
      · by_cases h2 : fderiv ℝ Gy p = 0
        · exact Or.inl (Or.inl ⟨hp, h1, h2⟩)
        · exact Or.inr ⟨hp, h2⟩
      · exact Or.inl (Or.inr ⟨hp, h1⟩)
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  -- ## The flat part `B₀`
  have hB0n : MeasureTheory.volume (G '' B0) = 0 := by
    have hterm : ∀ n : ℕ,
        MeasureTheory.volume (G '' (B0 ∩ Metric.closedBall (0 : ℝ × ℝ) n)) = 0 := by
      intro n
      apply volume_image_null_of_partials_fderiv_eq_zero hG
      · exact Metric.isBounded_closedBall.subset Set.inter_subset_right
      · intro p hp
        exact ((hmemB0 p).mp hp.1).1
      · intro p hp
        exact ((hmemB0 p).mp hp.1).2.1
      · intro p hp
        exact ((hmemB0 p).mp hp.1).2.2
    have hcov : G '' B0 = ⋃ n : ℕ, G '' (B0 ∩ Metric.closedBall (0 : ℝ × ℝ) n) := by
      rw [← Set.image_iUnion, Metric.iUnion_inter_closedBall_nat]
    rw [hcov]
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume (⋃ n : ℕ, G '' (B0 ∩ Metric.closedBall (0 : ℝ × ℝ) n))
        ≤ ∑' n : ℕ, MeasureTheory.volume (G '' (B0 ∩ Metric.closedBall (0 : ℝ × ℝ) n)) :=
          MeasureTheory.measure_iUnion_le _
      _ = 0 := by simp [hterm]
  -- ## The curved part along `Gx = 0`
  have hB1xn : MeasureTheory.volume (G '' B1x) = 0 := by
    classical
    have hcurve : ∀ p : ℝ × ℝ, p ∈ B1x → ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
        MeasureTheory.volume (G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
          {q : ℝ × ℝ | Gx q = 0} ∩ U)) = 0 := by
      intro p hp
      have hp0 : fderiv ℝ G p = 0 := ((hmemB1x p).mp hp).1
      have hgx : fderiv ℝ Gx p ≠ 0 := ((hmemB1x p).mp hp).2
      have hpGx : Gx p = 0 := by rw [hGx]; simp [hp0]
      exact exists_isOpen_volume_image_critical_null hG1 hGxcd hpGx hgx
    let U : ℝ × ℝ → Set (ℝ × ℝ) := fun p => if h : p ∈ B1x then (hcurve p h).choose else ∅
    have hU : ∀ p : ℝ × ℝ, ∀ hp : p ∈ B1x, IsOpen (U p) ∧ p ∈ U p ∧
        MeasureTheory.volume (G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
          {q : ℝ × ℝ | Gx q = 0} ∩ U p)) = 0 := by
      intro p hp
      simp only [U, dif_pos hp]
      exact (hcurve p hp).choose_spec
    have hnhd : ∀ p ∈ B1x, U p ∈ 𝓝 p := fun p hp => (hU p hp).1.mem_nhds (hU p hp).2.1
    obtain ⟨t, htc, htsub, hcover⟩ :=
      (HereditarilyLindelofSpace.isLindelof B1x).elim_nhds_subcover U hnhd
    have hsub : G '' B1x ⊆ ⋃ p ∈ t, G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
        {q : ℝ × ℝ | Gx q = 0} ∩ U p) := by
      rintro u ⟨q, hq, rfl⟩
      have hq' : q ∈ ⋃ p ∈ t, U p := hcover hq
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hq'
      obtain ⟨hxt, hxq⟩ := Set.mem_iUnion.mp hx
      have hq0 : fderiv ℝ G q = 0 := ((hmemB1x q).mp hq).1
      have hqGx : Gx q = 0 := by rw [hGx]; simp [hq0]
      exact Set.mem_biUnion hxt ⟨q, ⟨⟨hq0, hqGx⟩, hxq⟩, rfl⟩
    refine le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq ?_)) bot_le
    rw [MeasureTheory.measure_biUnion_null_iff htc]
    intro x hx
    exact (hU x (htsub x hx)).2.2
  -- ## The curved part along `Gy = 0`
  have hB1yn : MeasureTheory.volume (G '' B1y) = 0 := by
    classical
    have hcurve : ∀ p : ℝ × ℝ, p ∈ B1y → ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
        MeasureTheory.volume (G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
          {q : ℝ × ℝ | Gy q = 0} ∩ U)) = 0 := by
      intro p hp
      have hp0 : fderiv ℝ G p = 0 := ((hmemB1y p).mp hp).1
      have hgy : fderiv ℝ Gy p ≠ 0 := ((hmemB1y p).mp hp).2
      have hpGy : Gy p = 0 := by rw [hGy]; simp [hp0]
      exact exists_isOpen_volume_image_critical_null hG1 hGycd hpGy hgy
    let U : ℝ × ℝ → Set (ℝ × ℝ) := fun p => if h : p ∈ B1y then (hcurve p h).choose else ∅
    have hU : ∀ p : ℝ × ℝ, ∀ hp : p ∈ B1y, IsOpen (U p) ∧ p ∈ U p ∧
        MeasureTheory.volume (G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
          {q : ℝ × ℝ | Gy q = 0} ∩ U p)) = 0 := by
      intro p hp
      simp only [U, dif_pos hp]
      exact (hcurve p hp).choose_spec
    have hnhd : ∀ p ∈ B1y, U p ∈ 𝓝 p := fun p hp => (hU p hp).1.mem_nhds (hU p hp).2.1
    obtain ⟨t, htc, htsub, hcover⟩ :=
      (HereditarilyLindelofSpace.isLindelof B1y).elim_nhds_subcover U hnhd
    have hsub : G '' B1y ⊆ ⋃ p ∈ t, G '' ({q : ℝ × ℝ | fderiv ℝ G q = 0} ∩
        {q : ℝ × ℝ | Gy q = 0} ∩ U p) := by
      rintro u ⟨q, hq, rfl⟩
      have hq' : q ∈ ⋃ p ∈ t, U p := hcover hq
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hq'
      obtain ⟨hxt, hxq⟩ := Set.mem_iUnion.mp hx
      have hq0 : fderiv ℝ G q = 0 := ((hmemB1y q).mp hq).1
      have hqGy : Gy q = 0 := by rw [hGy]; simp [hq0]
      exact Set.mem_biUnion hxt ⟨q, ⟨⟨hq0, hqGy⟩, hxq⟩, rfl⟩
    refine le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq ?_)) bot_le
    rw [MeasureTheory.measure_biUnion_null_iff htc]
    intro x hx
    exact (hU x (htsub x hx)).2.2
  rw [hSB, Set.image_union, Set.image_union]
  apply le_antisymm _ bot_le
  calc MeasureTheory.volume (G '' B0 ∪ G '' B1x ∪ G '' B1y)
      ≤ MeasureTheory.volume (G '' B0) + MeasureTheory.volume (G '' B1x)
          + MeasureTheory.volume (G '' B1y) := by
        refine le_trans (MeasureTheory.measure_union_le (G '' B0 ∪ G '' B1x) (G '' B1y)) ?_
        gcongr
        exact MeasureTheory.measure_union_le (G '' B0) (G '' B1x)
    _ = 0 := by simp [hB0n, hB1xn, hB1yn]

end Work.Smooth.BoxGeneric.Sard
