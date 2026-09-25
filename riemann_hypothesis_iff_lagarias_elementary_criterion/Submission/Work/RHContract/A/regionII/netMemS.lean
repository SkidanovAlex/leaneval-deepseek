import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs
import Submission.Work.RHContract.A.regionII.caNet2_eps_le

namespace Work.RHContract.A.regionII

/-- **The gain-region index set is contained in `netS`.**

Every prime `p` in the "replacement window" `netPf ξ < p ≤ netNf ξ` belongs to the index
set `netS ε = {q prime : q ≤ ξ₂(ε), ⌊√ξ⌋₊ < q}` of the net-gain sum `Net₂`, where
`ξ = caXi ε`.

The two facts needed are:

* `netM ξ = ⌊√ξ⌋₊ ≤ ⌊(115/100)√ξ⌋₊ = netPf ξ < p`, so `p` clears the lower cut;
* `p ≤ netNf ξ ≤ netQlo ξ = √(2ξ)(1 − log2/(2 log ξ))`, and `√(2ξ) ≤ ξ` because `ξ ≥ 2`,
  so `p ≤ ξ`; moreover `ε ≤ g(ξ)` (`caNet2_eps_le`) and
  `ca_level_two_lower` then give `2 ≤ μ(p,ε)`, i.e. `p` has colossally abundant exponent
  `≥ 2` and hence lies below `ξ₂(ε) = caXi2 ε`. -/
theorem netMemS (ε : ℝ) (hε : 0 < ε) (hlo : (100000 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ))
    (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8) :
    ∀ p : ℕ, Nat.Prime p → netPf (Work.RHPlan.caXi ε : ℝ) < p →
      p ≤ netNf (Work.RHPlan.caXi ε : ℝ) → p ∈ netS ε := by
  intro p hp hpf hpn
  have hξ1530 : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hξpos : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hξgt1 : (1 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hξ2 : (2 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hlogξpos : (0 : ℝ) < Real.log (Work.RHPlan.caXi ε : ℝ) := Real.log_pos hξgt1
  -- `ε ≤ g(ξ)`
  have hεg : ε ≤ Real.log (1 + 1 / (Work.RHPlan.caXi ε : ℝ)) / Real.log (Work.RHPlan.caXi ε : ℝ) :=
    caNet2_eps_le ε hε hξ1530
  -- `netQlo ξ ≥ 0`
  have hfac_nonneg : 0 ≤ 1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    have h2 : Real.log 2 ≤ Real.log (Work.RHPlan.caXi ε : ℝ) :=
      Real.log_le_log (by norm_num) hξ2
    linarith
  have hnetQlo_nonneg : 0 ≤ netQlo (Work.RHPlan.caXi ε : ℝ) := by
    unfold netQlo
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg _)) hfac_nonneg
  -- `p ≤ netQlo ξ`
  have hpN : (p : ℝ) ≤ (netNf (Work.RHPlan.caXi ε : ℝ) : ℝ) := by exact_mod_cast hpn
  have hNq : ((netNf (Work.RHPlan.caXi ε : ℝ) : ℕ) : ℝ) ≤ netQlo (Work.RHPlan.caXi ε : ℝ) := by
    simpa [netNf] using Nat.floor_le hnetQlo_nonneg
  have hq_eq : netQlo (Work.RHPlan.caXi ε : ℝ)
      = Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
          * (1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ))) := by
    unfold netQlo
    rw [show Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
          = Real.sqrt 2 * Real.sqrt (Work.RHPlan.caXi ε : ℝ) from
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _]
  have hple : (p : ℝ) ≤ Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
      * (1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ))) := by
    calc (p : ℝ) ≤ (netNf (Work.RHPlan.caXi ε : ℝ) : ℝ) := hpN
      _ ≤ netQlo (Work.RHPlan.caXi ε : ℝ) := hNq
      _ = Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
            * (1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ))) := hq_eq
  -- `2 ≤ μ(p,ε)`
  have htwo : (2 : ℝ) ≤ Work.RHPlan.caMu p ε := by
    have h := Commons.NumberTheory.Robin.ca_level_two_lower hε hξ1530 hεg hp hple
    simpa [Work.RHPlan.caMu] using h
  have hfloor : 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := Nat.le_floor htwo
  -- `p ≤ ξ`
  have hfac_le : (1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ))) ≤ 1 := by
    have : 0 ≤ Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ)) := by positivity
    linarith
  have hsqrt_le : Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ)) ≤ (Work.RHPlan.caXi ε : ℝ) := by
    have hs : 2 * (Work.RHPlan.caXi ε : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
          ≤ Real.sqrt ((Work.RHPlan.caXi ε : ℝ) ^ 2) := Real.sqrt_le_sqrt hs
      _ = (Work.RHPlan.caXi ε : ℝ) := Real.sqrt_sq (le_of_lt hξpos)
  have hpξ : p ≤ Work.RHPlan.caXi ε := by
    have h1 : Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ))
        * (1 - Real.log 2 / (2 * Real.log (Work.RHPlan.caXi ε : ℝ)))
        ≤ Real.sqrt (2 * (Work.RHPlan.caXi ε : ℝ)) :=
      mul_le_of_le_one_right (Real.sqrt_nonneg _) hfac_le
    have hreal : (p : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
    exact_mod_cast hreal
  -- `p ≤ ξ₂(ε)`
  have hmem : p ∈ Work.RHPlan.caSupport ε :=
    (Work.RHContract.A.mem_caSupport_iff ε hε hξ1530).mpr ⟨hpξ, hp⟩
  have hpT : p ∈ (Work.RHPlan.caSupport ε).filter (fun q => 2 ≤ ⌊Work.RHPlan.caMu q ε⌋₊) :=
    Finset.mem_filter.mpr ⟨hmem, hfloor⟩
  have hpxi2 : p ≤ Work.RHContract.Margin.caXi2 ε := by
    rw [Work.RHContract.Margin.caXi2]
    exact Finset.le_sup (f := id) hpT
  -- `netM ξ < p`
  have hMle : netM (Work.RHPlan.caXi ε : ℝ) ≤ netPf (Work.RHPlan.caXi ε : ℝ) := by
    unfold netM netPf
    apply Nat.floor_mono
    nlinarith [Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
  have hMlt : netM (Work.RHPlan.caXi ε : ℝ) < p := lt_of_le_of_lt hMle hpf
  rw [netS]
  exact Finset.mem_filter.mpr ⟨by rw [Nat.mem_primesLE]; exact ⟨hpxi2, hp⟩, hMlt⟩

end Work.RHContract.A.regionII
