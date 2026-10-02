import Mathlib
import Submission.Work.ThomBordism.localChartBallDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The chart neighbourhood of `0` is homeomorphic to the open `ε`-disc bundle

This file proves `Work.ThomBordism.chartNbhd_pairHomeo`: the capped chart map
`p ↦ chartAffine E x (cap E ε p)` restricts to a homeomorphism of pairs

`(chartOpenBall E ε, chartOpenBall E ε ∖ {0_x}) ≅ (chartNbhd E C x, chartNbhd E C x ∖ {0})`,

where

* `chartOpenBall E ε = {p | normalNorm E p < ε}` is the open `ε`-disc bundle of the normal bundle,
* `chartNbhd E C x = {y | y + E.e x ∈ C.openTube}` is the translate by `-E.e x` of the open tube.

Since the capping is the identity on the open disc bundle, the forward map is really the tubular map
`p ↦ tubeMap E p - E.e x`, with inverse `y ↦ C.inv (y + E.e x)`; the capping is inserted only so
that the forward map is *definitionally* `chartAffine E x ∘ cap E ε`, as the consumer requires.
-/

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The capped chart map vanishes only at the zero-section point.**  For a point `p` of the closed
`ε`-disc bundle, `chartAffine E x (cap E ε p) = 0` iff `p` is the zero vector over `x`.  This is the
pair condition behind the last conjunct of `chartNbhd_pairHomeo`. -/
theorem chartAffine_cap_eq_zero_iff (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) {p : Work.Tubular.NormalTotal E}
    (hp : Work.Tubular.normalNorm E p ≤ ε) :
    Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) = 0
      ↔ p = Work.Tubular.zeroSectionNormal E x := by
  have hcap : Work.ThomBordism.cap E ε p = p :=
    Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le hp
  constructor
  · intro h0
    rw [hcap] at h0
    have htube : Work.Tubular.tubeMap E p = E.e x := by
      rw [Work.ThomBordism.chartAffine_apply] at h0
      exact sub_eq_zero.mp (by simpa [Work.Tubular.tubeMap] using h0)
    rw [← Work.ThomBordism.inv_embed E C x, ← htube]
    exact (C.inv_tubeMap p hp).symm
  · intro h
    rw [h]
    have hz : Work.ThomBordism.cap E ε (Work.Tubular.zeroSectionNormal E x)
        = Work.Tubular.zeroSectionNormal E x := by
      refine Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le ?_
      rw [Work.Tubular.zeroSectionNormal_apply, Work.Tubular.normalNorm_mk, norm_zero]
      exact C.eps_pos.le
    rw [hz, Work.ThomBordism.chartAffine_zeroSection]

/-- **The translate by `-E.e x` of the capped chart map** `p ↦ chartAffine E x (cap E ε p) + E.e x`
is the tubular map, on the closed disc bundle where the capping is invisible. -/
theorem chartAffine_cap_add_eq_tubeMap
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    {p : Work.Tubular.NormalTotal E} (hp : Work.Tubular.normalNorm E p ≤ ε) :
    Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) + E.e x
      = Work.Tubular.tubeMap E p := by
  rw [Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le hp, Work.ThomBordism.chartAffine_apply]
  simp only [Work.Tubular.tubeMap]
  exact sub_add_cancel _ _

theorem chartNbhd_pairHomeo {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    ∃ (Φ : ↥(Work.ThomBordism.chartOpenBall E ε) ≃ₜ ↥(Work.ThomBordism.chartNbhd E C x)),
      IsOpen (Work.ThomBordism.chartNbhd E C x) ∧
      (0 : Work.Tubular.Euc (8 + k)) ∈ Work.ThomBordism.chartNbhd E C x ∧
      (∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
        (Φ p : Work.Tubular.Euc (8 + k))
          = Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
              (p : Work.Tubular.NormalTotal E))) ∧
      (∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
        ((p : Work.Tubular.NormalTotal E) ≠ Work.Tubular.zeroSectionNormal E x)
          ↔ ((Φ p : Work.Tubular.Euc (8 + k)) ≠ 0)) := by
  -- the capping is the identity on the open disc bundle
  have hball_le : ∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
      Work.Tubular.normalNorm E (p : Work.Tubular.NormalTotal E) ≤ ε :=
    fun p => le_of_lt ((Work.ThomBordism.mem_chartOpenBall E ε _).1 p.2)
  -- the forward map lands in the chart neighbourhood
  have hmem : ∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
        (p : Work.Tubular.NormalTotal E)) ∈ Work.ThomBordism.chartNbhd E C x := by
    intro p
    rw [Work.ThomBordism.mem_chartNbhd,
      chartAffine_cap_add_eq_tubeMap E C x (hball_le p)]
    exact ⟨(p : Work.Tubular.NormalTotal E), p.2, rfl⟩
  -- the inverse map lands in the open disc bundle
  have hmem' : ∀ y : ↥(Work.ThomBordism.chartNbhd E C x),
      C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x)
        ∈ Work.ThomBordism.chartOpenBall E ε := by
    intro y
    rw [Work.ThomBordism.mem_chartOpenBall]
    have h : (y : Work.Tubular.Euc (8 + k)) + E.e x ∈ C.openTube := y.2
    rw [Work.Tubular.TubeChart.openTube_eq] at h
    exact h.2
  let toFun : ↥(Work.ThomBordism.chartOpenBall E ε) → ↥(Work.ThomBordism.chartNbhd E C x) :=
    fun p => ⟨Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
      (p : Work.Tubular.NormalTotal E)), hmem p⟩
  let invFun : ↥(Work.ThomBordism.chartNbhd E C x) → ↥(Work.ThomBordism.chartOpenBall E ε) :=
    fun y => ⟨C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x), hmem' y⟩
  have left_inv : Function.LeftInverse invFun toFun := by
    intro p
    apply Subtype.ext
    show C.inv (Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
        (p : Work.Tubular.NormalTotal E)) + E.e x) = (p : Work.Tubular.NormalTotal E)
    rw [chartAffine_cap_add_eq_tubeMap E C x (hball_le p), C.inv_tubeMap _ (hball_le p)]
  have right_inv : Function.RightInverse invFun toFun := by
    intro y
    apply Subtype.ext
    show Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
        (C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x))) = (y : Work.Tubular.Euc (8 + k))
    have hU : (y : Work.Tubular.Euc (8 + k)) + E.e x ∈ C.U := C.openTube_subset_U y.2
    rw [Work.ThomBordism.cap_inv E C hU, Work.ThomBordism.chartAffine_inv E C x hU]
    exact add_sub_cancel_right _ _
  have cont_toFun : Continuous toFun := by
    have h1 : Continuous fun p : ↥(Work.ThomBordism.chartOpenBall E ε) =>
        Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
          (p : Work.Tubular.NormalTotal E)) :=
      hcont.comp continuous_subtype_val
    exact h1.subtype_mk hmem
  have cont_invFun : Continuous invFun := by
    have h1 : Continuous fun y : ↥(Work.ThomBordism.chartNbhd E C x) =>
        C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x) :=
      C.continuousOn_inv.comp_continuous
        (continuous_subtype_val.add continuous_const)
        (fun y => C.openTube_subset_U y.2)
    exact h1.subtype_mk hmem'
  let Φ : ↥(Work.ThomBordism.chartOpenBall E ε) ≃ₜ ↥(Work.ThomBordism.chartNbhd E C x) :=
    Homeomorph.mk (Equiv.mk toFun invFun left_inv right_inv) cont_toFun cont_invFun
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · -- the chart neighbourhood is open
    have hset : Work.ThomBordism.chartNbhd E C x
        = (fun y : Work.Tubular.Euc (8 + k) => y + E.e x) ⁻¹' C.openTube := rfl
    rw [hset]
    exact IsOpen.preimage (f := fun y : Work.Tubular.Euc (8 + k) => y + E.e x)
      (continuous_id.add continuous_const) C.openTube_isOpen
  · -- it contains `0`
    rw [Work.ThomBordism.mem_chartNbhd]
    simpa using C.mem_openTube x
  · -- the formula for the forward map
    intro p
    rfl
  · -- the pair condition
    intro p
    have hiff := chartAffine_cap_eq_zero_iff E C x (hball_le p)
    have hcoe : (Φ p : Work.Tubular.Euc (8 + k))
        = Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
            (p : Work.Tubular.NormalTotal E)) := rfl
    rw [hcoe]
    exact (not_congr hiff).symm

end

end Work.ThomBordism
