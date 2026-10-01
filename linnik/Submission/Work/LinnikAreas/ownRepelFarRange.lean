import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.sameCharRepelHalf
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# The far range of the same-character Deuring–Heilbronn repulsion (`λ₀ → 0` slice)

The same-character Deuring–Heilbronn repulsion is trivial in its *far range*: once
`λ(u) ≥ λ(ρ₀)·(1/qᵋ)` — equivalently, once `λ(u) ≥ δ log q` for a fixed `δ > 0` — Siegel's theorem
(`1 - β ≥ C(ε)q^{-ε}`, i.e. `log(1/λ(ρ₀)) ≤ ε log q + C(ε)`, proved in the workspace) gives
`λ(u) ≥ δ log q ≥ (δ/ε)(log(1/λ(ρ₀)) - C(ε)) ≳ log(1/λ(ρ₀))`.

This is precisely the part of the repulsion that the §5/§6/§8 window machinery *cannot* reach:
that machinery needs the repelled zero to lie in the window `λ(u) ≤ δ log q` with
`δ ≤ √(loglog q)/log q` (`DhRepel.lemma8_5`'s `hδle`, `DhRepel.dhTrianglePt`'s `hrect'`), i.e.
`λ(u) ≤ √(loglog q)`, which for large `q` is far below `log q/100`.  Splitting the repulsion into
this far range (below) and the complementary window range (`λ(u) ≤ log q/100`, where the §8.5
assembly is available) therefore covers the whole `λ₀ → 0` regime that the capped lemmas miss.
-/

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **Far range of the same-character Deuring–Heilbronn repulsion.**

For a real character `χ₀` modulo `q` with a real zero `ρ₀` of minimal `λ = (1 - Re)·log q`
(`IsMin1`) and `λ(ρ₀) ≤ 1/100`, every other zero `u` of `χ₀` with `|Im u| ≤ 1` and
`λ(u) ≥ log q / 100` satisfies `λ(u) ≥ (1/100)·log (1/λ(ρ₀))` — an absolute constant times the
logarithm, uniformly in `q`, with *no* restriction on `λ(ρ₀)` beyond `≤ 1/100`.

Proof: Siegel's theorem in logarithmic form (`siegelLogBoundLoc`, from
`Commons…LFunction_realZero_siegel_uniform`) applied with `ε = 1/2` gives
`log (1/λ(ρ₀)) ≤ (1/2) log q + C`; combined with `λ(u) ≥ log q/100` this yields the claim (the
remaining range `log (1/λ(ρ₀)) < 2C` is handled by `log q ≥ 2C`, i.e. `q ≥ q₀`). -/
theorem ownRepelFarRange : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
      (1 / 100) * Real.log (q : ℝ) ≤ Work.LinnikContract.lamOf q u →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨C, hCpos, hC⟩ := siegelLogBoundLoc (1 / 2) (by norm_num)
  refine ⟨1 / 100, by norm_num, max (Nat.ceil (Real.exp (2 * C))) 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 h100 u hzm him hne hfar
  have hχ0 : χ₀ ≠ 1 := hmin.1.1
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  -- `log q ≥ 2C` for `q ≥ ⌈e^{2C}⌉`
  have hqexp : Real.exp (2 * C) ≤ (q : ℝ) := by
    have h1 : Real.exp (2 * C) ≤ ((Nat.ceil (Real.exp (2 * C)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (2 * C)) : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans (le_max_left _ _) hq)
    linarith
  have hL2C : 2 * C ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hqexp
    rwa [Real.log_exp] at h
  have hsiegel : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ (1 / 2) * Real.log (q : ℝ) + C :=
    hC q χ₀ ρ₀ hχ0 hsq him0 (hmin.1.2.1)
  rcases lt_or_ge (2 * C) (Real.log (1 / Work.LinnikContract.lamOf q ρ₀)) with hcase | hcase
  · -- `log (1/λ₀) ≥ 2C`: Siegel gives `log q ≥ log (1/λ₀)`
    have hkey : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Real.log (q : ℝ) := by
      linarith only [hsiegel, hcase]
    calc (1 / 100) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ (1 / 100) * Real.log (q : ℝ) := by linarith only [hkey]
      _ ≤ Work.LinnikContract.lamOf q u := hfar
  · -- `log (1/λ₀) < 2C`: then `log q ≥ 2C` dominates
    have hkey : (1 / 100) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ (1 / 100) * (2 * C) := by
      linarith only [hcase]
    have hkey2 : (1 / 100) * (2 * C) ≤ (1 / 100) * Real.log (q : ℝ) := by
      linarith only [hL2C]
    linarith only [hkey, hkey2, hfar]

/-- **The full (uncapped) same-character Deuring–Heilbronn repulsion from its window half.**

Given the *window* half — the repulsion for zeros with `λ(u) ≤ log q/100` — the *far* half is
`ownRepelFarRange` above, and the two together give the repulsion
`c_r log (1/λ(ρ₀)) ≤ λ(u)` for every other zero with `|Im u| ≤ 1`, with **no** restriction on
`λ(u)` and **no** restriction on `λ(ρ₀)` beyond `≤ 1/100`.

WARNING on the route to the window half (both reviewers of `Work.LinnikAreas.ownRepelNearWindow`
flagged this): it does **not** follow from the §5/§6/§8 window machinery on record.  Every
formalised §8.5 lemma carries `hδle : δ ≤ √(loglog q)/log q` (`DhRepel.lemma8_5`,
`DhRepel.Spec8_5`, `DhNear`), so that machinery reaches only `λ(u) ≤ √(loglog q)`, far below the
`log q/100` needed here; and `sameCharRepelCapped` needs `lamS ≤ λ(ρ₀)`, giving a constant that
degenerates as `λ(ρ₀) → 0`.  The window half is therefore the residual deep input in window form —
the Turán power-sum route (Kadiri–Ng–Wong arXiv:1902.08640 §2, i.e. the `DhK` development) or
Graham's sieve.  Only the split (far half proved here + window half) is new. -/
theorem ownRepelUncapped_of_nearWindow
    (hnear : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        Work.LinnikContract.lamOf q u ≤ (1 / 100) * Real.log (q : ℝ) →
        c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u) :
    ∃ c_r : ℝ, 0 < c_r ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        c_r * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₁, hc₁, q₁, hn⟩ := hnear
  obtain ⟨c₂, hc₂, q₂, hf⟩ := ownRepelFarRange
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max q₁ q₂) 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him h100 u hzm himu hne
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  -- `λ(ρ₀) > 0`, hence `log (1/λ(ρ₀)) ≥ 0`
  have hlam0 : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    have hre := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₀ (hmin.1.2.1)
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlogq
  have hlog0 : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hlam0).mpr (by linarith [h100])
  rcases lt_or_ge (Work.LinnikContract.lamOf q u) ((1 / 100) * Real.log (q : ℝ)) with hcase | hcase
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog0)
      (hn q hq1 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne hcase.le)
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0)
      (hf q hq2 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne hcase)

/-- **The full (uncapped) same-character Deuring–Heilbronn repulsion from its two window ranges.**

Splitting the repelled zero's `λ` into three ranges, the requested repulsion follows from

* **(near)** `ownRepelNearCase` as stated by the fleet (`Work.LinnikAreas.sameCharNearCase`,
  HB §6 triangle inequality: `λ(u) ≤ (1/3)logloglog q`),
* **(middle)** `Work.LinnikAreas.ownRepelMidRange` — the residual slice
  `(1/3)logloglog q ≤ λ(u) ≤ log q/100`, which is exactly the `λ₀ → 0` regime that the §5/§6/§8
  window machinery cannot reach (its lemmas cap at `λ(u) ≤ √(loglog q)`), and
* **(far)** `ownRepelFarRange` above — **proved**, via Siegel.

No ordering of the two thresholds is needed: the case split only brackets `λ(u)`. -/
theorem ownRepelUncapped_of_near_mid_far
    (hnear : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        Work.LinnikContract.lamOf q u ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u)
    (hmid : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        Real.log (Real.log (Real.log (q : ℝ))) / 3 ≤ Work.LinnikContract.lamOf q u →
        Work.LinnikContract.lamOf q u ≤ (1 / 100) * Real.log (q : ℝ) →
        c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u) :
    ∃ c_r : ℝ, 0 < c_r ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        c_r * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₁, hc₁, q₁, hn⟩ := hnear
  obtain ⟨c₂, hc₂, q₂, hm⟩ := hmid
  obtain ⟨c₃, hc₃, q₃, hf⟩ := ownRepelFarRange
  refine ⟨min (min c₁ c₂) c₃, lt_min (lt_min hc₁ hc₂) hc₃, max (max (max q₁ q₂) q₃) 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him h100 u hzm himu hne
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hq3 : q₃ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq4 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlam0 : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    have hre := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₀ (hmin.1.2.1)
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlogq
  have hlog0 : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hlam0).mpr (by linarith [h100])
  rcases lt_or_ge ((1 / 100) * Real.log (q : ℝ)) (Work.LinnikContract.lamOf q u) with hgt | hle
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0)
      (hf q hq3 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne hgt.le)
  · by_cases h2 : Work.LinnikContract.lamOf q u ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3
    · exact le_trans (mul_le_mul_of_nonneg_right
        (le_trans (min_le_left _ _) (min_le_left _ _)) hlog0)
        (hn q hq1 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne h2)
    · push_neg at h2
      exact le_trans (mul_le_mul_of_nonneg_right
        (le_trans (min_le_left _ _) (min_le_right _ _)) hlog0)
        (hm q hq2 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne h2.le hle)

/-- **The fleet's `sameCharRepelFar` target needs only its middle slice.**

`Work.LinnikAreas.sameCharRepelFar` (the same-character repulsion for `λ(u) ≥ logloglog q/3` and
`Re u > 1/2`, still open) has its top range `λ(u) ≥ log q/100` supplied **for free** by
`ownRepelFarRange` above (Siegel).  Hence, given the middle slice
`Work.LinnikAreas.ownRepelMidRange` (`logloglog q/3 ≤ λ(u) ≤ log q/100`), the whole of
`sameCharRepelFar` follows.  This shrinks the fleet's open target to its middle range. -/
theorem ownRepelAboveThirdLogloglog_of_mid
    (hmid : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        Real.log (Real.log (Real.log (q : ℝ))) / 3 ≤ Work.LinnikContract.lamOf q u →
        Work.LinnikContract.lamOf q u ≤ (1 / 100) * Real.log (q : ℝ) →
        c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₀ →
        Real.log (Real.log (Real.log (q : ℝ))) / 3 ≤ Work.LinnikContract.lamOf q u →
        c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₂, hc₂, q₂, hm⟩ := hmid
  obtain ⟨c₃, hc₃, q₃, hf⟩ := ownRepelFarRange
  refine ⟨min c₂ c₃, lt_min hc₂ hc₃, max (max q₂ q₃) 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him h100 u hzm himu hne h3
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq3 : q₃ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq4 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlam0 : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    have hre := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₀ (hmin.1.2.1)
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlogq
  have hlog0 : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hlam0).mpr (by linarith [h100])
  rcases lt_or_ge ((1 / 100) * Real.log (q : ℝ)) (Work.LinnikContract.lamOf q u) with hgt | hle
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0)
      (hf q hq3 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne hgt.le)
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog0)
      (hm q hq2 χ₀ ρ₀ hmin hsq him h100 u hzm himu hne h3 hle)

end Work.LinnikAreas
