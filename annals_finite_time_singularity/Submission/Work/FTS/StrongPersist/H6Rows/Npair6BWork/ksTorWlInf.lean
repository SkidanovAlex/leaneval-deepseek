import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Slot bounds for `KsTor α`

`KsTor α = fun z θ => sin²θ · Ks(z)` is a product of a function of `θ` alone and a
function of `z` alone, so every mixed derivative factors (`pzIter_KsTor`,
`pzIter_DthIter_KsTor` in `KsAux`):

* `∂_z^k KsTor α = sin²θ · ∂_z^k Ks`,
* `∂_z^k D_θ^j KsTor α = D_θ^j(sin²)(θ) · ∂_z^k Ks`.

Hence each `𝒲^{6,∞}`-slot is the product of a `θ`-factor and a `z`-factor.  The `z`-factor
is bounded by `2α·k!·(k+1) ≤ 2α·5040` (`ks_pz_bound` + `fact_mul_le_5040`), the `θ`-factor of
a radial slot by `1`, and the weighted `θ`-factor of an angular slot by the constant of
`dthU_sinSq_weight`. -/

/-- `sin θ ^ 2 ≤ 1`. -/
private theorem sin_sq_le_one (θ : ℝ) : Real.sin θ ^ 2 ≤ 1 := by
  nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/-- The `z`-factor of a slot: `|(z+1)^k ∂_z^k Ks| ≤ 2α·k!·(k+1) ≤ 2α·5040` for `k ≤ 6`. -/
private theorem ks_zfactor_le {α : ℝ} (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| ≤ 2 * α * 5040 := by
  have h1 := ks_pz_bound α hα k z hz θ
  have h2 := fact_mul_le_5040 k hk
  calc |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) := h1
    _ ≤ 2 * α * 5040 := mul_le_mul_of_nonneg_left h2 (by linarith)

/-- **The radial slots.**  For `k ≤ 6` and `(z,θ)` in the closed quadrant,
`|(z+1)^k ∂_z^k KsTor α| ≤ 2α·5040`. -/
private theorem radial_slot_le {α : ℝ} (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ| ≤ 2 * α * 5040 := by
  rw [pzIter_KsTor]
  have hsin : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hsin1 : Real.sin θ ^ 2 ≤ 1 := sin_sq_le_one θ
  have hres := ks_zfactor_le hα k hk hz θ
  calc |(z + 1) ^ k * (Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ)|
      = Real.sin θ ^ 2 * |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| := by
        rw [show (z + 1) ^ k * (Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ)
              = Real.sin θ ^ 2 * ((z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ)
            from by ring,
          abs_mul, abs_of_nonneg hsin]
    _ ≤ 1 * (2 * α * 5040) := mul_le_mul hsin1 hres (abs_nonneg _) (by norm_num)
    _ = 2 * α * 5040 := by ring

/-- **The angular slots.**  The `θ`-factor carries the weighted endpoint bound (`hCw`,
the content of `dthU_sinSq_weight`), the `z`-factor the radial bound. -/
private theorem ang_slot_le {α Cw : ℝ} (hα : 0 < α) (_hα1 : α ≤ 1) (hCwpos : 0 < Cw)
    (hCw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ Cw)
    (j k : ℕ) (hj1 : 1 ≤ j) (hjk : k + j ≤ 6) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ Cw * (2 * α * 5040) := by
  rw [pzIter_DthIter_KsTor]
  have hj6 : j ≤ 6 := by omega
  have hk6 : k ≤ 6 := by omega
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) hden.le
  have hD := hCw j hj1 hj6 θ hθ
  have hD' : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ Cw := by
    simpa only [div_eq_mul_inv, mul_assoc] using hD
  have hZ := ks_zfactor_le hα.le k hk6 hz θ
  calc |(z + 1) ^ k * (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
          * Work.Spaces.pzIter k (KsFun α) z θ)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      = (|Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        * |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| := by
        rw [show (z + 1) ^ k * (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
              * Work.Spaces.pzIter k (KsFun α) z θ)
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
            = (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
              * ((z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ) from by ring,
          abs_mul, abs_mul, abs_of_nonneg hw0]
    _ ≤ Cw * (2 * α * 5040) := mul_le_mul hD' hZ (abs_nonneg _) hCwpos.le

/-! ## The main statement -/

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsTor α = fun z θ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))` — definitionally the
-- function below — and proves the helpers `KsTor_eq_FK`, `pzIter_KsTor`,
-- `pzIter_DthIter_KsTor`, `ks_pz_bound`, `pzIter_KsFun`), plus
-- `Submission.Work.Spaces.Defs` and the weighted endpoint bound
-- `Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight`:
-- `|D_θ^j (sin²) θ| · sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1095801216` for `1 ≤ j ≤ 6`, `0 < α ≤ 1`,
-- `θ ∈ Iθ`.  Route: `pzIter_KsTor` + `ks_pz_bound` bound the radial slots by `2α·k!(k+1)`;
-- for the angular slots `pzIter_DthIter_KsTor` factors the slot as
-- `D_θ^j(sin²)(θ) · ∂_z^k Ks(z) · sin(2θ)^{-α/5}/(α+sin 2θ)`, and `dthU_sinSq_weight` bounds
-- the θ-part by `1095801216` while `ks_pz_bound` bounds the z-part by `2α·k!(k+1) ≤ 10080α`.
theorem ksTorWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.WlInfMem α 6 (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))) ∧
    Work.Spaces.WlInf α 6 (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
      ≤ C * α := by
  obtain ⟨Cw, hCwpos, hCw⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight
  refine ⟨max 1 (70560 + 49 * Cw * 10080), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro α hαI
  obtain ⟨hα, hα1⟩ := hαI
  have hα0 : 0 ≤ α := le_of_lt hα
  change Work.Spaces.WlInfMem α 6 (KsTor α) ∧
      Work.Spaces.WlInf α 6 (KsTor α) ≤ max 1 (70560 + 49 * Cw * 10080) * α
  have hCwα : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ Cw := hCw α hα hα1
  have hmem : Work.Spaces.WlInfMem α 6 (KsTor α) := by
    refine ⟨fun k hk => ?_, fun j _ k _ hj1 hjk => ?_⟩
    · exact Work.Spaces.supFinite_of_pointwise
        (fun z hz θ hθ => radial_slot_le hα0 k hk hz hθ)
    · exact Work.Spaces.supFinite_of_pointwise
        (fun z hz θ hθ => ang_slot_le hα hα1 hCwpos hCwα j k hj1 hjk hz hθ)
  have hbound : Work.Spaces.WlInf α 6 (KsTor α)
      ≤ max 1 (70560 + 49 * Cw * 10080) * α := by
    rw [Work.Spaces.WlInf]
    have hZterm : ∀ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ)
          ≤ 2 * α * 5040 := by
      intro k hk
      have hk6 : k ≤ 6 := by have := Finset.mem_range.mp hk; omega
      exact Work.Spaces.supAbs_le (fun z hz θ hθ => radial_slot_le hα0 k hk6 hz hθ)
    have hZ : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ))
        ≤ 7 * (2 * α * 5040) := by
      calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ))
          ≤ ∑ _k ∈ Finset.range (6 + 1), (2 * α * 5040) := Finset.sum_le_sum hZterm
        _ = 7 * (2 * α * 5040) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have hTterm : ∀ j k : ℕ,
        (if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ Cw * (2 * α * 5040) := by
      intro j k
      by_cases hc : 1 ≤ j ∧ k + j ≤ 6
      · rw [ite_eq_left hc]
        exact Work.Spaces.supAbs_le
          (fun z hz θ hθ => ang_slot_le hα hα1 hCwpos hCwα j k hc.1 hc.2 hz hθ)
      · rw [ite_eq_right hc]
        have hnn : 0 ≤ Cw * (2 * α * 5040) := by positivity
        exact hnn
    have hT : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 49 * (Cw * (2 * α * 5040)) := by
      calc (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
            if 1 ≤ j ∧ k + j ≤ 6 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0)
          ≤ ∑ _j ∈ Finset.range (6 + 1), ∑ _k ∈ Finset.range (6 + 1),
              (Cw * (2 * α * 5040)) :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hTterm j k))
        _ = 49 * (Cw * (2 * α * 5040)) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
    have hfin : 7 * (2 * α * 5040) + 49 * (Cw * (2 * α * 5040))
        ≤ max 1 (70560 + 49 * Cw * 10080) * α := by
      have hEq : 7 * (2 * α * 5040) + 49 * (Cw * (2 * α * 5040))
          = (70560 + 49 * Cw * 10080) * α := by ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hα0
    linarith
  exact ⟨hmem, hbound⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
