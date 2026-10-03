/-
# Non-aliasing of the exact-height IW frequencies at the repaired window `uRep`

`Work.KMTAreas.A7.uRep_nonAliasing`: for `0 < ρ ≤ 1`, every `l ≤ max l₁ l₂` and all
`k₁,k₂`, the exact-height Ionescu–Wainger frequency set `diffFreqs ρ l` is non-aliased at the
arc scale `k = 1 - 2·uRep ρ l₁ l₂ k₁ k₂`.  This is the hypothesis `hnaᵢ` of
`Work.KMTAreas.A7.hiKconcN_sub_hiKmodNRep`.

The content is the *separation* of two distinct exact-height frequencies: the arcs
`α + ℝ_{≤k}` and `β + ℝ_{≤k}` are disjoint iff `‖α - β‖ > 2^{k+1} = 2^{2-2u}`.  The proof splits
on the two regimes of `iwP ρ l`:

* `l ≤ iwC0 ρ`: then `iwP ρ l = [1, 2^l]`, so two distinct frequencies `a/q`, `a'/q'` have
  `q,q' ≤ 2^l` and `‖α - β‖ ≥ 1/(q q') ≥ 2^{-2l} > 2^{2-2u}`, because `u ≥ max l₁ l₂ + 3 ≥ l + 3`
  (`lp_sep_le_of_den`, `lp_iwP_le_two_pow`).
* `l > iwC0 ρ`: then `iwP ρ l = iwPconcrete ρ l`, every one of whose elements is at most
  `T = Q_0^{(l)}·(2^l)^{D_ρ²}`, so `‖α - β‖ ≥ 1/T²`; and `u ≥ uScale ρ L ≥ 2^{2ρl} - 1`
  (`uRep_gt_sq`), so `2^{2-2u} < 2^{2·2^{ρl}-4}` while `T ≤ 2^{2^{2ρl}-2}`
  (`lp_T_le_sharp`), giving `T² < 2^{2u-2}`, i.e. `2^{2-2u} < 1/T²`.

The second regime is the only place where the repair `max l₁ l₂ + 3` of `uRep` is used: the
elements of `iwPconcrete ρ l` have denominators as large as `2^{C 2^{ρl}} ≫ 2^l`, so the sharp
separation `2^{-2l}` of the first regime is *false* there, and only the quadratic growth
`u ≳ 2^{2ρl}` of `uScale` rescues the estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpNonAliasAtWindow
import Submission.Work.KMTAreas.A7.lp_T_le_sharp

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- **The repaired window dominates `2^{2ρl} - 1`.**  For `l ≤ max l₁ l₂` one has
`(uRep ρ l₁ l₂ k₁ k₂ : ℝ) > 2^{2ρl} - 1`; this is the quantitative content of the repair
`uRep ≥ uScale ρ L` together with `L ≥ l`. -/
lemma uRep_gt_sq (ρ : ℝ) (hρ : 0 < ρ) (l₁ l₂ k₁ k₂ l : ℕ) (hl : l ≤ max l₁ l₂) :
    (2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 1 < (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by
  set X : ℕ := max (max l₁ l₂) (max k₁ k₂) with hX
  have hL : l ≤ X := le_trans hl (le_max_left _ _)
  have hfloor : (2 : ℝ) ^ (2 * ρ * (X : ℝ)) - 1 < (uScale ρ X : ℝ) := by
    have hXc : (uScale ρ X : ℝ) = ((⌊(2 : ℝ) ^ (2 * ρ * (X : ℝ))⌋₊ : ℕ) : ℝ) := by
      rw [uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
      norm_num
    rw [hXc]
    exact Nat.sub_one_lt_floor ((2 : ℝ) ^ (2 * ρ * (X : ℝ)))
  have hmono : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (X : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h : (l : ℝ) ≤ (X : ℝ) := by exact_mod_cast hL
    exact mul_le_mul_of_nonneg_left h (by linarith [hρ.le] : (0 : ℝ) ≤ 2 * ρ)
  have hle : (uScale ρ X : ℝ) ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by
    have h : uScale ρ X ≤ uRep ρ l₁ l₂ k₁ k₂ := by
      rw [uRep, ← hX]
      exact le_max_left _ _
    exact_mod_cast h
  linarith

/-- **Separation in the first regime `l ≤ iwC0 ρ`.** -/
lemma sep_regime1 (ρ : ℝ) (l₁ l₂ k₁ k₂ l : ℕ) (hl : l ≤ max l₁ l₂)
    (hlc : l ≤ iwC0 ρ) {α β : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ diffFreqs ρ l) (hβ : β ∈ diffFreqs ρ l) (hne : α ≠ β) :
    (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) < ‖α - β‖ := by
  have hB : 0 < 2 ^ l := by positivity
  have hsep : (1 : ℝ) / ((2 ^ l : ℕ) : ℝ) ^ 2 ≤ ‖α - β‖ :=
    lp_sep_le_of_den (ρ := ρ) (l := l) (B := 2 ^ l) hB hα hβ
      (fun q hq _ => lp_iwP_le_two_pow hq hlc)
      (fun q hq _ => lp_iwP_le_two_pow hq hlc) hne
  have huR : (l : ℝ) + 3 ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by
    have h1 : (l : ℝ) ≤ (max l₁ l₂ : ℝ) := by exact_mod_cast hl
    have h2 : (max l₁ l₂ + 3 : ℕ) ≤ uRep ρ l₁ l₂ k₁ k₂ := by
      rw [uRep]
      exact le_max_right _ _
    have h3 : ((max l₁ l₂ + 3 : ℕ) : ℝ) ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hcast2 : ((2 ^ l : ℕ) : ℝ) ^ 2 = (2 : ℝ) ^ (2 * (l : ℝ)) := by
    have h1 : ((2 ^ l : ℕ) : ℝ) = (2 : ℝ) ^ l := by rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [h1, ← Real.rpow_natCast (2 : ℝ) l,
      lp_rpow_pow (2 : ℝ) (l : ℝ) (by norm_num) 2]
    congr 1
    ring
  have hcast3 : (1 : ℝ) / (2 : ℝ) ^ (2 * (l : ℝ)) = (2 : ℝ) ^ (-(2 * (l : ℝ))) := by
    rw [one_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  refine lt_of_lt_of_le ?_ hsep
  rw [hcast2, hcast3]
  exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)

/-- **Separation in the second regime `iwC0 ρ < l`.** -/
lemma sep_regime2 (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ l₂ k₁ k₂ l : ℕ)
    (hl : l ≤ max l₁ l₂) (hlc : iwC0 ρ < l) {α β : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ diffFreqs ρ l) (hβ : β ∈ diffFreqs ρ l) (hne : α ≠ β) :
    (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) < ‖α - β‖ := by
  set T : ℕ := iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l)) (by positivity)
  have hbound : ∀ q ∈ iwP ρ l, q • α = 0 → q ≤ T := by
    intro q hq _
    rw [mem_iwP] at hq
    rcases hq with ⟨h1, -⟩ | ⟨-, hq'⟩
    · exact absurd h1 (not_le.mpr hlc)
    · rw [hTdef]
      exact lp_iwPconcrete_le hq'
  have hbound' : ∀ q ∈ iwP ρ l, q • β = 0 → q ≤ T := by
    intro q hq _
    rw [mem_iwP] at hq
    rcases hq with ⟨h1, -⟩ | ⟨-, hq'⟩
    · exact absurd h1 (not_le.mpr hlc)
    · rw [hTdef]
      exact lp_iwPconcrete_le hq'
  have hsep : (1 : ℝ) / (T : ℝ) ^ 2 ≤ ‖α - β‖ :=
    lp_sep_le_of_den (ρ := ρ) (l := l) (B := T) hTpos hα hβ hbound hbound' hne
  -- the numeric comparison `T² < 2^{2u-2}`
  have hs2 : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 1 < (uRep ρ l₁ l₂ k₁ k₂ : ℝ) :=
    uRep_gt_sq ρ hρ l₁ l₂ k₁ k₂ l hl
  have hexp : 2 * ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2) < 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2 := by
    linarith
  have hT : (T : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2) := by
    rw [hTdef]
    exact lp_T_le_sharp ρ hρ hρ1 hlc
  have hTsq : (T : ℝ) ^ 2 < (2 : ℝ) ^ (2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2) := by
    have h1 : (T : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2)) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self (by positivity) hT
    have h2 : ((2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2)) ^ 2
        = (2 : ℝ) ^ (2 * ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2)) := by
      rw [lp_rpow_pow (2 : ℝ) ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2) (by norm_num) 2]
      congr 1
      ring
    have h3 : (2 : ℝ) ^ (2 * ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2))
        < (2 : ℝ) ^ (2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hexp
    calc (T : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2)) ^ 2 := h1
      _ = (2 : ℝ) ^ (2 * ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2)) := h2
      _ < (2 : ℝ) ^ (2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2) := h3
  -- conclude `2^{2-2u} < 1/T²`
  have hlt : (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) < (1 : ℝ) / (T : ℝ) ^ 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) ^ 2)]
    have hmul := mul_lt_mul_of_pos_left hTsq
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)))
    have hzero : (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ))
        * (2 : ℝ) ^ (2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have : (2 : ℝ) - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)
          + (2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) - 2) = 0 := by ring
      rw [this, Real.rpow_zero]
    rwa [hzero] at hmul
  linarith [hlt, hsep]

/-- **The exact-height IW frequencies at the repaired window are non-aliased.** -/
theorem uRep_nonAliasing (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ l₂ k₁ k₂ l : ℕ)
    (hl : l ≤ max l₁ l₂) :
    Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l) := by
  intro α hα β hβ θ hθ θ' hθ' heq
  have hsub : α - β = ((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    rw [AddCircle.coe_sub (1 : ℝ) θ' θ, sub_eq_sub_iff_add_eq_add, heq, add_comm]
  have hEr : (((1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) : ℤ) : ℝ))
      = 1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by push_cast; ring
  have hθr : |θ| ≤ (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) := by
    have h := hθ
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ| ≤ (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) := abs_le.mpr h
    rw [lp_zpow_two_eq_rpow] at hb
    rw [hEr] at hb
    exact hb
  have hθ'r : |θ'| ≤ (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) := by
    have h := hθ'
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ'| ≤ (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) := abs_le.mpr h
    rw [lp_zpow_two_eq_rpow] at hb
    rw [hEr] at hb
    exact hb
  have hdd : |θ' - θ| ≤ (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) := by
    have h1 : |θ' - θ| ≤ |θ'| + |θ| := abs_sub θ' θ
    have h2 : |θ'| + |θ| ≤ (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ))
        + (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) := add_le_add hθ'r hθr
    have h3 : (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ))
        + (2 : ℝ) ^ (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ))
        = (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) := by
      have hx : (2 : ℝ) - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)
          = (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) + 1 := by ring
      rw [hx, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    linarith [h1, h2, h3]
  have hnorm : ‖α - β‖ ≤ |θ' - θ| := by
    rw [hsub]
    exact lp_norm_coe_circle_le_abs (θ' - θ)
  rcases eq_or_ne α β with hAB | hAB
  · refine ⟨hAB, ?_⟩
    have hsub0 : ((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [← hsub, hAB, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hsub0
    have hnR : θ' - θ = (n : ℝ) := by rw [← hn, zsmul_one]
    have hu3 : (3 : ℕ) ≤ uRep ρ l₁ l₂ k₁ k₂ := by
      have h : (max l₁ l₂ + 3 : ℕ) ≤ uRep ρ l₁ l₂ k₁ k₂ := le_max_right _ _
      omega
    have hnabs : |(n : ℝ)| < 1 := by
      rw [← hnR]
      have hsmall : (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) ≤ 1 / 16 := by
        have h4 : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by
          have h4' : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
          rw [h4', Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          norm_num
        rw [← h4]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (3 : ℝ) ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℝ) := by exact_mod_cast hu3
        linarith
      linarith [hdd, hsmall, (by norm_num : (1 : ℝ) / 16 < 1)]
    have hn0 : n = 0 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp hnabs
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < (1 : ℤ) := by exact_mod_cast h2
      omega
    have hθθ' : θ = θ' := by
      have hz : θ' - θ = 0 := by rw [hnR, hn0]; norm_num
      linarith
    exact hθθ'
  · exfalso
    have hsep : (2 : ℝ) ^ (2 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℝ)) < ‖α - β‖ := by
      by_cases hlc : l ≤ iwC0 ρ
      · exact sep_regime1 ρ l₁ l₂ k₁ k₂ l hl hlc hα hβ hAB
      · exact sep_regime2 ρ hρ hρ1 l₁ l₂ k₁ k₂ l hl (not_le.mp hlc) hα hβ hAB
    linarith [hsep, hnorm, hdd]

end

end Work.KMTAreas.A7
