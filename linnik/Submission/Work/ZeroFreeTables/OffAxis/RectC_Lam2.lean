/-
# ZeroFreeTables/OffAxis — `RectC_Lam2`

The `λ₂ ≥ 0.701` clause of `Z3` at rectangle height `L`, in the form the off-axis assembly
consumes it (`OFFAXIS_ROUTE_LEAD.md` §3.1): for a pair carrying the height-`L` numbering
`IsRectMin L χ₁ ρ₁` (HB §6 numbering with room: `|Im ρ₁| ≤ L` and `λ₁` minimal over *all*
non-principal zeros of height `≤ 10L`), every zero of height `≤ 1` of a character
`χ ∉ {χ₁, χ₁⁻¹}` has `λ ≥ 0.701`.

The mathematical content is HB's Lemma 9.4 (= Table 10 via Lemma 9.3, with HB Lemma 6.2 for
small orders), run at rectangle height `L`; the on-axis proof is
`Submission/Work/ZeroFreeTables/HBLemma9_4_proof.lean` and its `HB94/rowcontra*` components,
transcribed at height `L` in `Submission/Work/ZeroFreeTables/OffAxis/RectLam2.lean`.

The difference from `RectLam2` is exactly the hypothesis: `RectLam2` assumes the *strip*
numbering `IsRectStrip L` (minimality at height `L` plus a zero-free strip `(L, 10L]`), which
has to be converted into the height-`10L` numbering `IsMinWideAt L (10L)`; here the height-`L`
hypothesis `IsRectMin L` *is* that numbering (its minimality clause is already stated over
`|Im| ≤ 10L`), so `isMinWideAt_of_isRectMin` below replaces the strip conversion and the rest
of the argument is verbatim.  The four routes are:

* `λ₁ < 0.348`: HB Lemma 6.2 with the unconditional `ψ = 1/2` (`HB94.L52supply16`) and the
  region certificate `certA_348_701` (`OffAxis/Rect2Cert.lean`);
* `λ₁ ≥ 0.348`, `χ₁² ∉ {1, χ, χ⁻¹}`: HB Lemma 9.2 (Table 9), `P9F.rowcontra_0704_0704`;
* `λ₁ ≥ 0.348`, `χ₁² ∈ {1, χ, χ⁻¹}`, `χ² ∉ {1, χ₁, χ₁⁻¹}`: HB Lemma 9.3 (`table10_93_cert`);
* both relations (`(C3)`, forcing `χ₁⁶⁰ = χ⁶⁰ = 1`): HB Lemma 6.2 with `ψ = 3/8`
  (`HB94.L52supply_pow`, `table10_62_cert`).

Since `q₀` may depend on `L`, the large-`q` threshold absorbs the hypotheses `L ≤ Real.log q`
and `2 ≤ √(log log q)` that the `Ksum` bounds need.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.RectLam2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- **`IsRectMin L` gives the height-`10L` numbering.**  The minimality clause of `IsRectMin` is
stated over the whole window `|Im| ≤ 10L`, which is exactly the fourth component of
`IsMinWideAt L (10L)`; the first three components are the `IsZAt L` clause. -/
theorem isMinWideAt_of_isRectMin {q : ℕ} [NeZero q] {L : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hR : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁) :
    Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
  ⟨hR.1.1, hR.1.2.1, hR.1.2.2, fun χ u hχ hzm him => hR.2 χ u ⟨hχ, hzm, him⟩⟩

/-- **HB Lemma 9.4 (Table 10) at rectangle height `L`, from the `IsRectMin` numbering.**
`Work.ZeroFreeTables.Lam2BoundH L χ₁ (701/1000)`: every zero of height `≤ L` of a character
`χ ∉ {χ₁, χ₁⁻¹}` has `λ ≥ 0.701`. -/
theorem rectC_lam2H : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ →
      Work.ZeroFreeTables.Lam2BoundH L χ₁ (701/1000) := by
  intro L hL
  -- the two log-derivative supplies
  obtain ⟨δ₁, hδ₁0, hδ₁1, q₁₆, h16⟩ := Work.ZeroFreeTables.HB94.L52supply16
  obtain ⟨δ₂, hδ₂0, hδ₂1, q₆₀, h60⟩ := Work.ZeroFreeTables.HB94.L52supply_pow
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδ0 : 0 < δ := lt_min hδ₁0 hδ₂0
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) hδ₁1
  -- the certificates for the single Table 10 row `(0.702, 0.702)`
  obtain ⟨lam62, hl62, hcert62⟩ := Work.ZeroFreeTables.table10_62_cert
    ((702/1000 : ℝ), (702/1000 : ℝ)) (by simp [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable10])
  obtain ⟨lam93, k93, hl93, hk93, hcert93⟩ := Work.ZeroFreeTables.table10_93_cert
    ((702/1000 : ℝ), (702/1000 : ℝ))
    (by simp [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable10]) (by norm_num)
  -- the height-`L` engines, all with `H = L`, `W = 10 L`
  have hH0 : (0:ℝ) ≤ L := by linarith
  have h3L : 3 * L + δ ≤ 10 * L := by linarith
  obtain ⟨q62a, h62a⟩ := hbLemma6_2_engine_H
    (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)) ((1:ℝ)/6) (1/1000000) δ L (10 * L)
    (by norm_num) hδ0 hδ1 hH0 h3L
  obtain ⟨q62b, h62b⟩ := hbLemma6_2_engine_H
    (Work.ZeroFreeTables.tf72T lam62 hl62) ((1:ℝ)/8) (1/1000000) δ L (10 * L)
    (by norm_num) hδ0 hδ1 hH0 h3L
  obtain ⟨q93, h93⟩ := hbLemma9_3_engine_H
    (Work.ZeroFreeTables.tf72T lam93 hl93) k93 ((1:ℝ)/6) (1/1000000) δ L (10 * L)
    hk93 (by norm_num) hδ0 hδ1 hH0 h3L
  have hθ0 : 0 < Real.arctan 25 := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan 25 < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htan25 : Real.tan (Real.arctan 25) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  obtain ⟨q92, h92⟩ := hbLemma9_2_engine_H
    (Work.ZeroFreeTables.tf71T (Real.arctan 25) (13/250) hθ0 hθπ (by norm_num))
    (107/125) ((1:ℝ)/6) (1/1000000) δ L (10 * L)
    (by norm_num) (by norm_num) hδ0 hδ1 hH0 h3L
  -- the threshold
  refine ⟨max (max (max q₁₆ q₆₀) (max (max q62a q62b) (max q93 q92)))
      (max (Nat.ceil (Real.exp L) + 1) (Nat.ceil (Real.exp (Real.exp 4)) + 1)), ?_⟩
  intro q hq _inst χ₁ ρ₁ hR
  have hq₁₆ : q₁₆ ≤ q := by omega
  have hq₆₀ : q₆₀ ≤ q := by omega
  have hq62a : q62a ≤ q := by omega
  have hq62b : q62b ≤ q := by omega
  have hq93 : q93 ≤ q := by omega
  have hq92 : q92 ≤ q := by omega
  have hqexp : Nat.ceil (Real.exp L) + 1 ≤ q := by omega
  have hqexp4 : Nat.ceil (Real.exp (Real.exp 4)) + 1 ≤ q := by omega
  have hlogL : L ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp L ≤ (q : ℝ) := by
      have h2 : Real.exp L ≤ ((Nat.ceil (Real.exp L) : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((Nat.ceil (Real.exp L) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqexp
      have h3' : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
        push_cast at h3; linarith
      linarith
    have h := Real.log_le_log (Real.exp_pos L) h1
    rwa [Real.log_exp] at h
  have hlog1 : 1 ≤ Real.log (q : ℝ) := le_trans hL hlogL
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := by linarith
  have hsqrt4 : (4:ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
    have h1 : Real.exp (Real.exp 4) ≤ (q : ℝ) := by
      have h2 : Real.exp (Real.exp 4) ≤ ((Nat.ceil (Real.exp (Real.exp 4)) : ℕ) : ℝ) :=
        Nat.le_ceil _
      have h3 : ((Nat.ceil (Real.exp (Real.exp 4)) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hqexp4
      have h3' : ((Nat.ceil (Real.exp (Real.exp 4)) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
        push_cast at h3; linarith
      linarith
    have h4 : Real.exp 4 ≤ Real.log (q : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 4)) h1
      rwa [Real.log_exp] at h
    have h5 : Real.log (Real.exp 4) ≤ Real.log (Real.log (q : ℝ)) :=
      Real.log_le_log (Real.exp_pos 4) h4
    rwa [Real.log_exp] at h5
  have hsqrt2 : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h := Real.sqrt_le_sqrt hsqrt4
    rw [show Real.sqrt 4 = 2 by norm_num] at h
    exact h
  -- the two supplies at the common `δ`
  have hL16 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ := fun χ _ hχ =>
    Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_left _ _) (h16 q hq₁₆ χ hχ)
  have hL8 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ ^ 60 = 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ := fun χ _ hχ hχ60 =>
    Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_right _ _) (h60 q hq₆₀ χ hχ hχ60)
  -- the Engines at `q`
  have hE62a : Engine62 (q := q) ((1:ℝ)/6) δ L (10 * L)
      (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)) := by
    intro a b c d i1 i2 i3 i4 h1 h2 h3 h4 hmin hzm hχ hγ hne1 hne2 hl1 hl2
    exact h62a q hq62a a b c d hlogL h1 h2 h3 h4 hmin hzm hχ hγ hne1 hne2 hl1 hl2
  have hE62b : Engine62 (q := q) ((1:ℝ)/8) δ L (10 * L)
      (Work.ZeroFreeTables.tf72T lam62 hl62) := by
    intro a b c d i1 i2 i3 i4 h1 h2 h3 h4 hmin hzm hχ hγ hne1 hne2 hl1 hl2
    exact h62b q hq62b a b c d hlogL h1 h2 h3 h4 hmin hzm hχ hγ hne1 hne2 hl1 hl2
  have hE93 : Engine93 (q := q) δ L (10 * L)
      (Work.ZeroFreeTables.tf72T lam93 hl93) k93 := by
    intro a b c d hL hmin hzm hχ hγ hne1 hne2 hcsq hcsq1 hcsq2 hl1 hl2
    exact h93 q hq93 a b c d hL hlogL hmin hzm hχ hγ hne1 hne2 hcsq hcsq1 hcsq2 hl1 hl2
  have hE92 : Engine92 (q := q) δ L (10 * L) (Real.arctan 25) (13/250) (107/125) := by
    intro a b c d hL hmin hzm hχ hγ hne1 hne2 hsq hsq1 hsq2 hl1 hl2 hsqrt
    have hcore := h92 q hq92 a b c d hL hlogL hmin hzm hχ hγ hne1 hne2 hsq hsq1 hsq2 hl1 hl2 hsqrt
    rw [Work.ZeroFreeTables.P9F.tf71T_F_eq_La (Real.arctan 25) (13/250) hθ0 hθπ (by norm_num)
          (-(lamOf q c)),
        Work.ZeroFreeTables.P9F.tf71T_F_eq_La (Real.arctan 25) (13/250) hθ0 hθπ (by norm_num)
          (lamOf q d - lamOf q c),
        Work.ZeroFreeTables.P9F.tf71T_F_eq_La (Real.arctan 25) (13/250) hθ0 hθπ (by norm_num) 0]
      at hcore
    simpa only [neg_neg, neg_sub, neg_zero, Work.ZeroFreeTables.tf71T] using hcore
  -- the contradiction
  intro χ ρ hZAt hne1 hne2
  -- the `IsRectMin` hypothesis *is* the height-`10L` numbering
  have hmin : IsMinWideAt L (10 * L) χ₁ ρ₁ := isMinWideAt_of_isRectMin hR
  have hl12 : lamOf q ρ₁ ≤ lamOf q ρ :=
    hmin.2.2.2 χ ρ hZAt.1 hZAt.2.1 (hZAt.2.2.trans (by linarith))
  by_contra hcon
  push_neg at hcon
  by_cases hlam : lamOf q ρ₁ < 701/1000
  · have hγ : |ρ.im| ≤ 10 * L := hZAt.2.2.trans (by linarith)
    have hzm : zeroMult χ ρ ≠ 0 := hZAt.2.1
    have hχ : χ ≠ 1 := hZAt.1
    by_cases hsmall : lamOf q ρ₁ < 348/1000
    · exact rowSmall hE62a hmin hzm hχ hZAt.2.2 hne1 hne2 (le_of_lt hsmall) (le_of_lt hcon)
        hl12 hL16
    · push_neg at hsmall
      by_cases hA : χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ ∨ χ₁ ^ 2 = χ⁻¹
      · by_cases hB2 : χ ^ 2 = 1 ∨ χ ^ 2 = χ₁ ∨ χ ^ 2 = χ₁⁻¹
        · obtain ⟨ha60, hb60⟩ := pow60_of_relations hA hB2
          have hA60 : (χ₁ * χ) ^ 60 = 1 := by rw [mul_pow, ha60, hb60, one_mul]
          have hB60 : (χ₁ * χ⁻¹) ^ 60 = 1 := by
            rw [mul_pow, ha60, inv_pow, hb60, one_mul, inv_one]
          haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
          haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
          haveI : NeZero (χ₁ * χ).conductor := ⟨(χ₁ * χ).conductor_ne_zero⟩
          haveI : NeZero (χ₁ * χ⁻¹).conductor := ⟨(χ₁ * χ⁻¹).conductor_ne_zero⟩
          exact row62C3 hl62 hE62b hcert62 hmin hzm hχ hZAt.2.2 hne1 hne2
            (by linarith) (by linarith) hl12
            (hL8 χ₁ hmin.1 ha60) (hL8 χ hχ hb60)
            (hL8 (χ₁ * χ) (fun h => hne2 (eq_inv_of_mul_eq_one_right h)) hA60)
            (hL8 (χ₁ * χ⁻¹) (fun h => hne1 ((mul_inv_eq_one.mp h).symm)) hB60)
        · push_neg at hB2
          exact row93 hl93 hk93 hE93 hcert93 hmin hzm hχ hZAt.2.2 hne1 hne2 hsmall
            (by linarith) (by linarith) hl12 hB2.1 hB2.2.1 hB2.2.2 hL16
      · push_neg at hA
        exact row92 hθ0 hθπ (by norm_num) hE92
          (fun {la1 laj} hn hle1 hle2 hcore =>
            Work.ZeroFreeTables.P9F.rowcontra_0704_0704
              Work.ZeroFreeTables.P9F.arctan25_bounds.1
              Work.ZeroFreeTables.P9F.arctan25_bounds.2 htan25 hn hle1 hle2 hcore)
          hmin hzm hχ hZAt.2.2 hne1 hne2 hA.1 hA.2.1 hA.2.2
          (lamOf_nonneg_of_minWide hmin hlogq0) (by linarith) (by linarith) hL16 hsqrt2
  · push_neg at hlam
    exact absurd hcon (not_lt.mpr (hlam.trans hl12))

/-- **The `λ₂ ≥ 0.701` clause of `Z3` at rectangle height `L`.**  For the `IsRectMin L`
numbering, every zero of height `≤ 1` of a character `χ ∉ {χ₁, χ₁⁻¹}` has `λ ≥ 0.701`. -/
theorem RectC_Lam2 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      Work.LinnikContract.Lam2Bound χ₁ 0.701 := by
  intro L hL
  obtain ⟨q₀, hq₀⟩ := rectC_lam2H L hL
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hR _hoff => ?_⟩
  have hone : (0.701 : ℝ) = 701/1000 := by norm_num
  rw [hone]
  exact Work.ZeroFreeTables.Lam2BoundH.toIsZ hL (hq₀ q hq χ₁ ρ₁ hR)

end Work.ZeroFreeTables.OffAxis
