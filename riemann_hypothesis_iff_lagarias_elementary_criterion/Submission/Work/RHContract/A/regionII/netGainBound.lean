import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs
import Submission.Work.NumberTheory.Chebyshev.theta_deficit_upper
import Submission.Work.RHContract.A.regionII.netGain.floorBounds
import Submission.Work.RHContract.A.regionII.netGain.cBound
import Submission.Work.RHContract.A.regionII.netGain.hbBound
import Submission.Work.RHContract.A.regionII.netGain.massCore

namespace Work.RHContract.A.regionII

open scoped BigOperators

noncomputable section

/-- **The `θ`-difference over the primes of an interval.**
`θ b − θ a = Σ_{a < p ≤ b, p prime} log p` for `a ≤ b`. -/
lemma theta_sub_primesLE (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)
      = ∑ p ∈ (Nat.primesLE b).filter (fun q => a < q), Real.log (p : ℝ) := by
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := Nat.primesLE_mono hab
  have hdiff : Nat.primesLE b \ Nat.primesLE a = (Nat.primesLE b).filter (fun q => a < q) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpb, hpp⟩, hna⟩
      exact ⟨⟨hpb, hpp⟩, Nat.lt_of_not_le (fun hpa => hna ⟨hpa, hpp⟩)⟩
    · rintro ⟨⟨hpb, hpp⟩, hap⟩
      exact ⟨⟨hpb, hpp⟩, fun h => absurd h.1 (not_le.mpr hap)⟩
  have h1 : Chebyshev.theta (b : ℝ) = ∑ p ∈ Nat.primesLE b, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have h2 : Chebyshev.theta (a : ℝ) = ∑ p ∈ Nat.primesLE a, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  rw [h1, h2, ← hdiff]
  have hs := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
  linarith [hs]

/-- **Per-prime gain bound.**  If `c ≥ netHb ξ + m` and the weight `netHb ξ` dominates
`1/(2p(p−1))` on the gain region, then the gain-region summand dominates `m log p`. -/
lemma netF_ge_of (ξ c m : ℝ)
    (hcb : netHb ξ + m ≤ c)
    (hhb : ∀ p : ℕ, netPf ξ < p →
      1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) ≤ netHb ξ * Real.log (p : ℝ))
    {p : ℕ} (hp : netPf ξ < p) (hp2 : 2 ≤ p) :
    m * Real.log (p : ℝ) ≤ netF c p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (le_of_lt hp1)
  have h1 : (netHb ξ + m) * Real.log (p : ℝ) ≤ c * Real.log (p : ℝ) :=
    mul_le_mul_of_nonneg_right hcb hlog
  rw [add_mul] at h1
  have h2 := hhb p hp
  unfold netF
  linarith

/-- `log ξ ≥ 11.5` for `ξ ≥ 10^5`. -/
lemma log_ge_115 (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) : (11.5 : ℝ) ≤ Real.log ξ := by
  have hlog10 : (2.3025850926 : ℝ) ≤ Real.log 10 := by
    rw [Real.log_ten_eq]; linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have h1 : Real.log (100000 : ℝ) ≤ Real.log ξ := Real.log_le_log (by norm_num) hlo
  have h2 : Real.log (100000 : ℝ) = 5 * Real.log 10 := by
    rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]; norm_num
  linarith

/-- On Region II the gain-window endpoint satisfies `netNf ξ ≤ 14000`, so that the
certified deficit bound `theta_deficit_upper` applies.  The key point is that the factor
`1 − log 2/(2 log ξ)` of `netQlo ξ` is at most `1 − 0.0188143`, because `log ξ < 8 log 10`. -/
lemma netNf_le_14000 (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    netNf ξ ≤ 14000 := by
  have hξ0 : 0 < ξ := by linarith
  have hlog10hi : Real.log 10 ≤ 2.3025850940 := by
    rw [Real.log_ten_eq]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hLhi : Real.log ξ ≤ 8 * Real.log 10 := by
    have h1 : Real.log ξ < Real.log ((10 : ℝ) ^ 8) := Real.log_lt_log hξ0 hhi
    have h2 : Real.log ((10 : ℝ) ^ 8) = 8 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    linarith
  have hLpos : 0 < Real.log ξ := by linarith [log_ge_115 ξ hlo]
  have hδ : (0.0188143 : ℝ) ≤ Real.log 2 / (2 * Real.log ξ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * Real.log ξ)]
    nlinarith [Real.log_two_gt_d9, hLhi, hlog10hi]
  have hq : netQlo ξ ≤ 14000 := by
    unfold netQlo
    rw [show Real.sqrt 2 * Real.sqrt ξ = Real.sqrt (2 * ξ) from
      (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ξ).symm]
    have hA : Real.sqrt (2 * ξ) ≤ 14142.136 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [hhi]⟩
    have hfac : 1 - Real.log 2 / (2 * Real.log ξ) ≤ 1 - 0.0188143 := by linarith
    have hfac0 : 0 ≤ 1 - Real.log 2 / (2 * Real.log ξ) := by
      rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 2 * Real.log ξ)]
      nlinarith [Real.log_two_lt_d9, log_ge_115 ξ hlo]
    have h5 := mul_le_mul hA hfac hfac0 (by norm_num : (0 : ℝ) ≤ 14142.136)
    nlinarith [h5]
  calc netNf ξ = ⌊netQlo ξ⌋₊ := rfl
    _ ≤ 14000 := le_trans (Nat.floor_mono hq) (le_of_eq (Nat.floor_natCast 14000))

theorem netGainBound (ε : ℝ) (hε : 0 < ε) (hlo : (100000 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ))
    (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8)
    (hmem : ∀ p : ℕ, Nat.Prime p → netPf (Work.RHPlan.caXi ε : ℝ) < p →
      p ≤ netNf (Work.RHPlan.caXi ε : ℝ) → p ∈ netS ε) :
    netK (Real.log (Work.RHPlan.caXi ε : ℝ)) / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)) ^ 2
        * netMasslb (Real.sqrt (Work.RHPlan.caXi ε : ℝ)) (Real.log (Work.RHPlan.caXi ε : ℝ))
      ≤ ∑ p ∈ (netS ε).filter (fun q => netPf (Work.RHPlan.caXi ε : ℝ) < q),
          netF (Work.RHContract.Margin.caC ε) p := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ0 : 0 < ξ := by linarith
  set s : ℝ := Real.sqrt ξ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξ0
  have hs2 : s ^ 2 = ξ := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hξ0)
  set L : ℝ := Real.log ξ with hLdef
  have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hL115 : (11.5 : ℝ) ≤ L := hLdef ▸ log_ge_115 ξ hlo
  -- ================= delegated arithmetic =================
  have hfloor : 430 ≤ netNf ξ ∧ netNf ξ ≤ 14142 ∧ 360 ≤ netPf ξ ∧ netPf ξ ≤ 12000
      ∧ netPf ξ < netNf ξ := by
    exact netGain.floorBounds ξ hlo hhi
  obtain ⟨hNf430, hNf14142, hPf360, hPf12000, hPfNf⟩ := hfloor
  have hmass : netMasslb s L
      ≤ ((netNf ξ : ℝ) - 21 / 10 * Real.sqrt (netNf ξ))
        - ((netPf ξ : ℝ) - (1 / 2) * Real.sqrt (netPf ξ)) := by
    exact netGain.massCore ξ hlo hhi
  have hcB : netHb ξ + netK L / ξ ≤ Work.RHContract.Margin.caC ε := by
    exact netGain.cBound ε hε hlo hhi
  have hhb : ∀ p : ℕ, netPf ξ < p →
      1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) ≤ netHb ξ * Real.log (p : ℝ) := by
    exact netGain.hbBound ξ hlo hhi
  -- ================= end delegated =================
  set T : Finset ℕ := (Nat.primesLE (netNf ξ)).filter (fun q => netPf ξ < q) with hTdef
  set B : Finset ℕ := (netS ε).filter (fun q => netPf ξ < q) with hBdef
  -- θ bounds
  have hθNf : (netNf ξ : ℝ) - 21 / 10 * Real.sqrt (netNf ξ) ≤ Chebyshev.theta (netNf ξ : ℝ) :=
    Work.NumberTheory.Chebyshev.theta_deficit_upper (netNf ξ) hNf430
      (netNf_le_14000 ξ hlo hhi)
  have hθPf : Chebyshev.theta (netPf ξ : ℝ) ≤ (netPf ξ : ℝ) - 1 / 2 * Real.sqrt (netPf ξ) :=
    theta_deficit_half (netPf ξ : ℝ) (by exact_mod_cast hPf360) (by exact_mod_cast hPf12000)
  have hmass' : netMasslb s L ≤ Chebyshev.theta (netNf ξ : ℝ) - Chebyshev.theta (netPf ξ : ℝ) := by
    linarith [hmass, hθNf, hθPf]
  have hsumid : Chebyshev.theta (netNf ξ : ℝ) - Chebyshev.theta (netPf ξ : ℝ)
      = ∑ p ∈ T, Real.log (p : ℝ) :=
    theta_sub_primesLE (netPf ξ) (netNf ξ) (le_of_lt hPfNf)
  -- the gain-region summand dominates `(netK L / s²) log p`
  have hper : ∀ p : ℕ, netPf ξ < p → 2 ≤ p →
      netK L / s ^ 2 * Real.log (p : ℝ) ≤ netF (Work.RHContract.Margin.caC ε) p := by
    intro p hp hp2
    have h1 := netF_ge_of ξ (Work.RHContract.Margin.caC ε) (netK L / ξ) hcB hhb hp hp2
    simpa [hs2] using h1
  -- the prime sum over `T` is dominated by the sum of the summands
  have hsumT : netK L / s ^ 2 * (∑ p ∈ T, Real.log (p : ℝ))
      ≤ ∑ p ∈ T, netF (Work.RHContract.Margin.caC ε) p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [hTdef, Finset.mem_filter] at hp
    exact hper p hp.2 (by omega)
  -- `T ⊆ B`
  have hsub : T ⊆ B := by
    intro p hp
    rw [hTdef, Finset.mem_filter] at hp
    obtain ⟨hp1, hpf⟩ := hp
    obtain ⟨hpNf, hpprime⟩ := Nat.mem_primesLE.mp hp1
    rw [hBdef, Finset.mem_filter]
    exact ⟨hmem p hpprime hpf hpNf, hpf⟩
  -- the summands outside `T` are nonnegative
  have hKpos : 0 < netK L := by
    unfold netK
    apply div_pos
    · nlinarith [hL115]
    · have h1 : (0 : ℝ) < L + 941 / 10000 := by linarith
      have h2 : (0 : ℝ) < L / 2 + 1397 / 10000 := by linarith
      positivity
  have hK0 : 0 ≤ netK L / s ^ 2 := le_of_lt (div_pos hKpos (by positivity))
  have hnonneg : ∀ p ∈ B, p ∉ T → 0 ≤ netF (Work.RHContract.Margin.caC ε) p := by
    intro p hpB _
    rw [hBdef, Finset.mem_filter] at hpB
    have hpf : netPf ξ < p := hpB.2
    have hle := hper p hpf (by omega)
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
      have : (1 : ℕ) ≤ p := by omega
      exact_mod_cast this)
    exact le_trans (mul_nonneg hK0 hlogp) hle
  have hsumB : ∑ p ∈ T, netF (Work.RHContract.Margin.caC ε) p
      ≤ ∑ p ∈ B, netF (Work.RHContract.Margin.caC ε) p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  -- assembly
  calc netK L / s ^ 2 * netMasslb s L
      ≤ netK L / s ^ 2 * (∑ p ∈ T, Real.log (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        rw [← hsumid]
        exact hmass'
    _ ≤ ∑ p ∈ T, netF (Work.RHContract.Margin.caC ε) p := hsumT
    _ ≤ ∑ p ∈ B, netF (Work.RHContract.Margin.caC ε) p := hsumB

end

end Work.RHContract.A.regionII
