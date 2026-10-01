/-
# ZeroFreeTables — `HBLemma8_1_witness`

`Work.ZeroFreeTables.HBLemma8_1` (HB's Lemma 8.1, in the corrected *floored* form of
`HB8Defs.lean`), assembled here from pieces already proved in the workspace.

## The argument (the route of `NOTE_HBLemma8_1_route.md`)

Data: `ε > 0`, `lamS > 0`, and for real `χ₁` (`χ₁ ^ 2 = 1`) with a real exceptional zero `ρ₁`
(`IsMin1WideAt 10`, `lamS ≤ λ₁ ≤ 1/5`) an *other* zero `ρ₀` of the working region with
`4e ≤ λ(ρ₀)`.  Goal: `(2-ε)·log(1/λ₁) ≤ λ(ρ₀)`.

* If `(2-ε)·log(1/λ₁) ≤ 4e` this is immediate.  Otherwise `2 - ε > 0` and the hypothesis
  `λ(ρ₀) < (2-ε)·log(1/λ₁) ≤ C' := (2-ε)·log(1/lamS)` gives, for `q ≥ q₀(C', δ)`, the two
  "constant" side conditions `λ(ρ₀) ≤ lamMax q` and `λ(ρ₀) ≤ δ·log q` (the latter for `δ` the
  common window radius below).
* **The box witness.**  `GlueWitness` (`t23GlueWitness_of_logFreeCount` with the unconditional
  log-free near-line count `t23NearLineCountLogFree_holds`) then produces a further zero `ρ' ≠ ρ₁`
  of `χ₁` and a box height `Hb` with `λ(ρ') ≤ λ(ρ₀)`, `|ρ'.im| + δ ≤ Hb`, `|ρ'.im| ≤ 10 log q`
  and `ρ'` `λ`-minimal among the zeros of `χ₁` other than `ρ₁` in the box `|u.im| ≤ Hb`.
* **A row of Tables 2 and 3 forces `4e ≤ λ(ρ')`.**  `t23cover.1` meets `λ₁ ≤ 1/5` by a row
  `(λ,b,v)` of `t23rows` with `min (4e) (2 log(1/λ₁)) ≤ v`; since `4e < (2-ε) log(1/λ₁) ≤
  2 log(1/λ₁)`, the minimum is `4e`.  The §6 inequality `GlueH63` (`t23glue`) at `ρ'`, the row
  certificate `RowCert_all` and the row mechanism `row_bound₀` give `v ≤ λ(ρ')`.
* **The §6 triangle at `ρ'`.**  `HB81_capped_app` (the "capped wide" engine with the box height
  `|ρ₀.im| + δ` built in, i.e. the box that the §6 window of radius `δ` actually needs) applied at
  `ρ'` -- the maximality over `|u.im| ≤ Hb` restricts to `|u.im| ≤ |ρ'.im| + δ ≤ Hb` -- yields
  `(2-ε)·log(1/λ₁) ≤ λ(ρ') ≤ λ(ρ₀)`, contradicting the assumption.  ∎

The two `Heath-Brown Lemma 3.1` inputs (`L52Hyp`) needed are supplied at a single common radius
`δw := min δ₁ δ₂ (1/2) ≤ 1/2`: `δ₁` with the sharp constant `1/8 + 10⁻⁶` for *all*
`ε' ∈ (0,1]` (from `t23l52`, needed by `GlueH63`), and `δ₂` with the constant
`1/8 + εs - εL/4` (from `HB81_l52_shift`, needed by the triangle).  `L52Hyp_mono` shrinks both to
`δw`.  The box height is *not* needed as a free parameter: since `dhTrianglePtH` produces its
threshold before binding the height, the "box" of the triangle can be taken to be exactly
`|ρ₀.im| + δ`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.HBTable2and3_all
import Submission.Work.ZeroFreeTables.RowCert_all
import Submission.Work.ZeroFreeTables.t23cover
import Submission.Work.ZeroFreeTables.t23glue
import Submission.Work.ZeroFreeTables.t23l52
import Submission.Work.ZeroFreeTables.t23simple
import Submission.Work.ZeroFreeTables.HB81_capped
import Submission.Work.ZeroFreeTables.HB81_capped_app
import Submission.Work.ZeroFreeTables.HBTable4range_engine
import Submission.Work.ZeroFreeTables.HB84Assembly
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.log_unbounded_nat

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## `(1/3) log log log q` is eventually above every constant -/

/-- `K ≤ lamMax q` for all large `q` (the triple logarithm dominates every constant). -/
private theorem hb81w_lamMax_ge (K : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → K ≤ Work.LinnikContract.lamMax q := by
  obtain ⟨q₀, hq₀⟩ := Work.LinnikAreas.log_unbounded_nat (Real.exp (Real.exp (3 * K)))
  refine ⟨max q₀ 2, ?_⟩
  intro q hq
  have h1 : Real.exp (Real.exp (3 * K)) ≤ Real.log (q : ℝ) :=
    hq₀ q (le_trans (le_max_left _ _) hq)
  have h2 : Real.exp (3 * K) ≤ Real.log (Real.log (q : ℝ)) := by
    have h3 := Real.log_le_log (Real.exp_pos (Real.exp (3 * K))) h1
    rwa [Real.log_exp] at h3
  have h4 : 3 * K ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h5 := Real.log_le_log (Real.exp_pos (3 * K)) h2
    rwa [Real.log_exp] at h5
  rw [Work.LinnikContract.lamMax]
  linarith

/-! ## The assembly -/

theorem HBLemma8_1_witness : Work.ZeroFreeTables.HBLemma8_1 := by
  classical
  intro ε hε lamS hlamS
  -- the small parameters of the §8.1 arithmetic
  set εs : ℝ := ε / 256 with hεsdef
  set εL : ℝ := ε / 256 with hεLdef
  set ec : ℝ := 2 * εs + 3.5 * εL with hecdef
  have hεs : 0 < εs := by rw [hεsdef]; positivity
  have hεL : 0 < εL := by rw [hεLdef]; positivity
  have hsmall : 8 * (2 - ε) * ec ≤ ε := by
    rw [hecdef, hεsdef, hεLdef]; nlinarith [hε]
  -- the two `L52Hyp` providers, shrunk to a common window radius `δw ≤ 1/2`
  obtain ⟨δ₁, hδ₁0, hδ₁half, q52, h52⟩ := t23l52
  obtain ⟨δ₂, hδ₂0, hδ₂lt1, qL52, hL52raw⟩ := HB81_l52_shift εs hεs εL hεL
  set δw : ℝ := min (min δ₁ δ₂) (1 / 2) with hδwdef
  have hδw0 : 0 < δw := by rw [hδwdef]; exact lt_min (lt_min hδ₁0 hδ₂0) (by norm_num)
  have hδwhalf : δw ≤ 1 / 2 := by rw [hδwdef]; exact min_le_right _ _
  have hδwlt1 : δw < 1 := by linarith
  have hδw₁ : δw ≤ δ₁ := by
    rw [hδwdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδw₂ : δw ≤ δ₂ := by
    rw [hδwdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  -- the thresholds of the pieces
  obtain ⟨qW, hW⟩ :=
    t23GlueWitness_of_logFreeCount t23NearLineCountLogFree_holds δw hδw0 hδwhalf
  obtain ⟨qG, hG⟩ := t23glue δw hδw0 hδwhalf
  obtain ⟨qS, hS⟩ := t23simple
  obtain ⟨qD, hD⟩ := HB81_capped_app δw ec εs εL hδw0 hδwlt1 hεs hεL hecdef ε hε hsmall
  set C' : ℝ := (2 - ε) * Real.log (1 / lamS) with hC'def
  obtain ⟨qA, hA⟩ := Work.LinnikAreas.log_unbounded_nat (C' / δw)
  obtain ⟨qB, hB⟩ := hb81w_lamMax_ge C'
  refine ⟨({q52, qL52, qW, qG, qS, qD, qA, qB, 3} : Finset ℕ).max' (by simp), ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ₀ hwide hsq him0 hZ hne hmax hfloor h15 h4e
  have hq52 : q52 ≤ q := le_trans (Finset.le_max' _ q52 (by simp)) hq
  have hqL52 : qL52 ≤ q := le_trans (Finset.le_max' _ qL52 (by simp)) hq
  have hqW : qW ≤ q := le_trans (Finset.le_max' _ qW (by simp)) hq
  have hqG : qG ≤ q := le_trans (Finset.le_max' _ qG (by simp)) hq
  have hqS : qS ≤ q := le_trans (Finset.le_max' _ qS (by simp)) hq
  have hqD : qD ≤ q := le_trans (Finset.le_max' _ qD (by simp)) hq
  have hqA : qA ≤ q := le_trans (Finset.le_max' _ qA (by simp)) hq
  have hqB : qB ≤ q := le_trans (Finset.le_max' _ qB (by simp)) hq
  have hq3 : 3 ≤ q := le_trans (Finset.le_max' _ 3 (by simp)) hq
  by_cases hbig : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 4 * Real.exp 1
  · linarith
  · push_neg at hbig
    by_contra hcon
    push_neg at hcon
    -- `hbig : 4e < (2-ε)·log(1/λ₁)` and `hcon : λ(ρ₀) < (2-ε)·log(1/λ₁)`
    have hχ1 : χ₁ ≠ 1 := hwide.1.1.1
    have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := hwide.1.1.2.1
    have hq2 : 2 ≤ q := by omega
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    obtain ⟨hre1pos, hre1lt, hlam1pos⟩ :=
      Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
    have hρ₁eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him0]
    -- the exceptional zero is simple
    have hsimple : zeroMult χ₁ ρ₁ = 1 := by
      have h : zeroMult χ₁ ((ρ₁.re : ℝ) : ℂ) = 1 :=
        hS q hqS χ₁ ρ₁.re hχ1 hsq hre1lt (by rw [← hρ₁eq]; exact hzm1)
          (fun u hzu himu => by
            rw [← hρ₁eq]
            exact hwide.2 χ₁ u hχ1 hzu (by linarith [abs_le.mp himu]))
          (by rw [← hρ₁eq]; linarith)
      rw [congrArg (fun z => zeroMult χ₁ z) hρ₁eq]
      exact h
    have hlog1nn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hlam1pos]
      linarith
    have h2εpos : 0 < 2 - ε := by
      by_contra hcon2
      push_neg at hcon2
      have h0 : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcon2 hlog1nn
      linarith [hbig, Real.exp_pos 1]
    have hlog_le : Real.log (1 / lamOf q ρ₁) ≤ Real.log (1 / lamS) := by
      refine Real.log_le_log (by positivity) ?_
      rw [one_div, one_div, inv_le_inv₀ hlam1pos hlamS]
      exact hfloor
    -- the two "constant" side conditions of the witness
    have hlam0lt : lamOf q ρ₀ < C' := by
      refine lt_of_lt_of_le hcon ?_
      rw [hC'def]
      exact mul_le_mul_of_nonneg_left hlog_le h2εpos.le
    have hcapρ : lamOf q ρ₀ ≤ lamMax q := le_trans hlam0lt.le (hB q hqB)
    have hδρ : lamOf q ρ₀ ≤ δw * Real.log (q : ℝ) := by
      have h1 : C' ≤ Real.log (q : ℝ) * δw := (div_le_iff₀ hδw0).mp (hA q hqA)
      linarith [hlam0lt.le, h1]
    -- the box witness
    obtain ⟨ρ', Hb, hzm', hne', him', hHb', hleu, hmaxbox⟩ :=
      hW q hqW χ₁ ρ₁ ρ₀ hwide hsq him0 hZ hne hcapρ hδρ
    have hcap' : lamOf q ρ' ≤ lamMax q := le_trans hleu hcapρ
    have hδρ' : lamOf q ρ' ≤ δw * Real.log (q : ℝ) := le_trans hleu hδρ
    have hmaxbox' : ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ |ρ'.im| + δw → u ≠ ρ₁ →
        lamOf q ρ' ≤ lamOf q u := by
      intro u hzu himu hune
      rcases hmaxbox u hzu (le_trans himu hHb') with h | h
      · exact absurd h hune
      · exact h
    -- a row of Tables 2 and 3 forces `4e ≤ λ(ρ')`
    obtain ⟨p, hp, hbp, hvp⟩ := t23cover.1 (lamOf q ρ₁) hlam1pos h15
    have hpmem : p ∈ t23rows ++ rowG := List.mem_append.mpr (Or.inl hp)
    have hlammem : p.1 ∈ t23lams := t23lamsmem p hpmem
    have hp1pos : 0 < p.1 := t23pos p hpmem
    have hL52row : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε' δw :=
      fun ε' hε' hε'1 =>
        Work.LinnikAreas.DhCapped.L52Hyp_mono χ₁ hχ1 hδw₁ (h52 q hq52 χ₁ hχ1 hsq ε' hε' hε'1)
    have hineq := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him'
      hHb' hmaxbox hcap' hδρ' (by linarith : lamOf q ρ₁ ≤ 2 / 5) hsimple hL52row p.1 hlammem
      hp1pos
    have hcert := RowCert_all p hp
    have hvle : p.2.2 ≤ lamOf q ρ' :=
      row_bound₀ hp1pos hineq hcert hbp hlam1pos.le
    have h4e2log : 4 * Real.exp 1 ≤ 2 * Real.log (1 / lamOf q ρ₁) := by
      have h2 : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 2 * Real.log (1 / lamOf q ρ₁) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog1nn
      linarith [hbig, h2]
    have hvp' : 4 * Real.exp 1 ≤ p.2.2 := by
      rw [min_eq_left h4e2log] at hvp
      exact hvp
    have h4eρ' : 4 * Real.exp 1 ≤ lamOf q ρ' := le_trans hvp' hvle
    -- the §6 triangle at `ρ'`
    have htri := hD q hqD χ₁ ρ₁ ρ' hwide hsq him0 hzm' hne' hmaxbox' him' h15 h4eρ' hcap'
      (Work.LinnikAreas.DhCapped.L52Hyp_mono χ₁ hχ1 hδw₂ (hL52raw q hqL52 χ₁ hχ1 hsq))
    linarith [htri, hleu, hcon]

end Work.ZeroFreeTables
