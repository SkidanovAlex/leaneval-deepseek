import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.Reduce
import Submission.Work.BoseBox.Windows
import Submission.Work.BoseBox.exists_gcTwoTerm_pos_of_neg
import Submission.Work.BoseBox.lhyBox_of_av_neg
import Submission.Work.BoseBox.perStateBox_forces_gcTwoTerm_nonpos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.perStateBox_of_LHYBox_compareBox` — the `C`+`B` ⟹ `G` step

## The intended mathematics (all of it machine-checked below)

`PerStateBox` (the canonical per-`(L,N,state)` box bound, the input of the `G`-node
`HBoxG_of_perStateBox`) is derived from FS `thm:LHY-Box` (`LHYBox`) and
FS `thm:CompareBoxEnergy` (`CompareBox`) at the **matching parameters `μ := ρ`**
(exactly as `BOSE_AUDIT_LEAD.md` §4 G prescribes: "Then S, then C, then B with
`μ := ρ`"):

* `LHYBox` at `μ = ρ` gives `ℓ³·Λ(a v, C, η₀, ρ) ≤ EBoxAt ρ (a v) v h`
  (the infimum over all `(n, Φ)` of the box word; `le_ciInf` twice);
* `CompareBox ρ` gives
  `(L/ℓ)³·min 0 (EBoxAt ρ (a v) v h) ≤ Rayl N L v Ψ − 8π(a v)ρN`;
* `min 0` is monotone and `ℓ³ ≥ 0`, so
  `L³·min 0 (Λ(a v, C, η₀, ρ)) ≤ Rayl N L v Ψ − 8π(a v)ρN`;
* the `N = 0` sector of `LHYBox` (where `boxWordU 0 = 0`, so that
  `ℓ³Λ·∫Φ₀² ≤ 0` with `∫Φ₀² > 0`) gives `Λ(a v, C, η₀, ρ) ≤ 0`; combined with
  `Λ = gcTwoTerm` (`Lambda_eq_gcTwoTerm`) this is the claimed bound.

## The defect of the *unconditional* statement

The unconditional statement — `perStateBox_of_LHYBox_compareBox`, as requested — is
**not derivable** from its hypotheses: it is missing a hypothesis on the sign of the
scattering length.  Concretely:

* if `0 < a v` the chain above is complete (it is
  `perStateBox_of_LHYBox_compareBox_of_av_nonneg` below, with `ha : 0 ≤ a v`);
* if `a v = 0` the claim is trivial (`gcTwoTerm (a v) = 0` and `CompareBox` at any
  admissible density gives `0 ≤ Rayl`), and only `CompareBox` is used — also covered
  by `perStateBox_of_LHYBox_compareBox_of_av_nonneg`;
* if `a v < 0`, however, the hypothesis `ρ·(a v)³ ≤ ε₀` of `PerStateBox` is satisfied by
  **every** `ρ > 0` (division by the negative number `(a v)³` flips the inequality), so
  `PerStateBox v η₀ C` would impose, at `N = 0` and any `L ≥ L₀` with `Rayl 0 L v Ψ = 0`
  (`𝓗 0 v = 0`), the requirement
  `gcTwoTerm (a v) C (1/2+η₀) ρ ≤ 0` for **every** `ρ > 0` — which is false: for a negative
  base `ρ(a v)³ < 0` one has `√(ρ(a v)³) = 0` and `(ρ(a v)³)^s = |ρ(a v)³|^s cos(πs)`
  (Mathlib's `Real.rpow`), so `gcTwoTerm (a v) C s ρ = 4π(a v)ρ²(-1 − C|ρ(a v)³|^s cos(πs))`
  has the sign of the bracket and is positive for suitable `ρ` (for *all* `ρ` when `C = 0`).
  Nothing in the hypotheses excludes `a v < 0`: `ScatSol v` carries no sign information
  (`a v = (8π)⁻¹∫v(1−w)`), and `LHYBox` is *automatic* at a negative scattering length
  (the box side degenerates, `sideAt μ (a v) = 0`, so its left side vanishes and, for
  `n ≥ 1`, the degenerate box `abox n 0` is null and `CSBox n 0` is empty — see
  `Submission.Work.BoseBox.lhyBox_of_av_neg`; alternatively `ParamsOK` already fails at
  negative diluteness), while `CompareBox` with `a v < 0` degenerates
  (`sideAt μ (a v) = 0`) to the statement that the box energy is bounded below by a
  *linear* function of `N` — a constraint that is not implied by anything in the
  hypotheses here (and that fails for the physically relevant attractive potentials,
  whose box energy is unbounded below in `N`).

The paper's standing assumption is `v ≥ 0` (FS `assump:v`), which gives `a v ≥ 0`; the
corrected statement below carries exactly that missing sign hypothesis, and the file
closes with the machine-checked diagnosis of the defect:

* `not_perStateBox_of_av_neg` : `a v < 0 → 0 ≤ C → ¬ PerStateBox v η₀ C`;
* `lhyBox_of_av_neg` (module `Submission.Work.BoseBox.lhyBox_of_av_neg`) :
  `a v < 0 → LHYBox v h η₀ C` — `LHYBox` is *automatic* there;
* `compareBox_iff_rayl_ge_of_av_neg` : at `a v < 0`, `CompareBox ρ` degenerates to the
  linear lower bound `8π(a v)ρN ≤ Rayl N L v Ψ` on every box energy;
* `rayl_nonneg_of_eventually_compareBox_of_av_neg` : hence `CompareBox` (eventually in
  `ρ`) forces `0 ≤ Rayl N L v Ψ` for every box state.

So the unconditional statement is *equivalent* to "every potential of negative scattering
length has a box state of negative energy" — a variational statement about `𝓗 N v` that
no hypothesis here carries (and whose proof would need a variational *upper* bound for
attractive gases, outside both this chapter and the paper, which assumes `v ≥ 0`).
Nothing in the chain `HBoxG_of_perStateBox` / `hpres_of_HBoxG` (see `Reduce.lean`,
`Target.lean`) needs the `a v < 0` case: those consumers already carry `0 < a v`. -/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

open Filter Metric MeasureTheory
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false

/-! ### The originally requested statement (recorded, NOT asserted)

The statement first requested at this path omitted the sign hypothesis on the
scattering length:

    ... (hC : 0 ≤ C) (hpar : ...) (hL : LHYBox v h η₀ C) (hcmp : ...) : PerStateBox v η₀ C

It is **false**: for `a v < 0` the conclusion fails
(`Work.BoseBox.not_perStateBox_of_av_neg`, proved below), and nothing in the
hypotheses excludes that branch.  The correct statement carries `0 ≤ a v`
(equivalently the paper's standing `0 ≤ v`): it is
`Work.BoseBox.perStateBox_of_LHYBox_compareBox_of_av_nonneg` below.  In the
theorem's application this hypothesis is *automatic*
(`Submission.BoseGases.av_nonneg` gives `0 ≤ a v` from the hypotheses of
`theorem_1_2`), and the `a v = 0` branch is handled separately by
`Submission.UBBtoGc.hpres_of_av_zero`.

-/

/-- Extraction from an eventual statement near `0⁺`: some `δ > 0` works for all
`0 < t ≤ δ`. -/
private lemma ext_pos_le {P : ℝ → Prop}
    (h : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), P t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ → P t := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  exact ⟨ε / 2, by positivity, fun t ht hle =>
    hball (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.le]; linarith) ht⟩

/-- The box word of the empty box (`n = 0`) vanishes: all sums are empty. -/
private lemma boxWordU_zero (ℓ μ d s eT b : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ IsScatteringSolution w v)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X 0 → ℝ) :
    boxWordU 0 ℓ μ d s eT b v h u Φ = 0 := by
  have h1 : tKinWord 0 ℓ d s eT b u Φ = 0 := by
    simp [tKinWord, Work.BoseKinLoc.kinForm]
  have h2 : Submission.BoseGases.qLHSword (N := 0) ℓ μ
      (Submission.BoseGases.wLoc ℓ v u) (Submission.BoseGases.wLoc ℓ (g0 v h) u) Φ = 0 := by
    simp [Submission.BoseGases.qLHSword, pairSet]
  rw [boxWordU, h1, h2, zero_add]

/-- `0^(-1/2) = 0` in the exact syntactic form produced by `boxSide` at a vanishing
scattering length. -/
private lemma zero_rpow_neg_half : (0 : ℝ) ^ (-(1 / 2 : ℝ)) = 0 :=
  Real.zero_rpow (by norm_num)

/-- **`PerStateBox` from `LHYBox` and `CompareBox`, with the sign hypothesis `0 ≤ a v`.**

For `0 < a v` this is the `μ := ρ` chain described in the file header; for `a v = 0`
it is `CompareBox` alone (`gcTwoTerm (a v) = 0` and `CompareBox` forces `Rayl ≥ 0`
because `sideAt μ (a v) = 0`, hence the factor `((L + 0)/0)³` vanishes).

The error coefficient moves `C ↦ C + 1`: `CompareBox` carries FS's *boundary*
factor `((L+ℓ)/ℓ)³` (the volume of the localisation region), and the loss
`((L+ℓ)/L)³ → 1` is absorbed by one extra unit of the coefficient
(`Lambda_factor_absorb`).  The constant is free throughout (the consumer only
needs *some* `Cw`), so this costs nothing. -/
theorem perStateBox_of_LHYBox_compareBox_of_av_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {η₀ C : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ _root_.BoseGases.a v)
    (hpar : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.BoseBox.ParamsOK (Work.BoseBox.fsParams t) t)
    (hL : Work.BoseBox.LHYBox v h η₀ C)
    (hcmp : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.BoseBox.CompareBox v h ρ) :
    Work.BoseBox.PerStateBox v η₀ (C + 1) := by
  rcases lt_or_eq_of_le ha with hapos | ha0
  · -- the case `0 < a v`
    obtain ⟨εL, hεL, hLb⟩ := hL
    obtain ⟨δ₁, hδ₁, hδ₁p⟩ := ext_pos_le hpar
    obtain ⟨δ₂, hδ₂, hδ₂p⟩ := ext_pos_le hcmp
    have hA3 : 0 < (_root_.BoseGases.a v) ^ 3 := pow_pos hapos 3
    have hlhyC : 0 < lhyC := by
      dsimp [lhyC]
      positivity
    refine ⟨min εL (min δ₁ (min (δ₂ * (_root_.BoseGases.a v) ^ 3) (1 / (4 * lhyC ^ 2)))), ?_, ?_⟩
    · exact lt_min hεL (lt_min hδ₁ (lt_min (mul_pos hδ₂ hA3)
        (by positivity)))
    · intro ρ hρ hsmall
      have hεL' : ρ * (_root_.BoseGases.a v) ^ 3 ≤ εL := le_trans hsmall (min_le_left _ _)
      have hδ₁' : ρ * (_root_.BoseGases.a v) ^ 3 ≤ δ₁ :=
        le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
      have hρδ₂ : ρ ≤ δ₂ := by
        have h2 : ρ * (_root_.BoseGases.a v) ^ 3 ≤ δ₂ * (_root_.BoseGases.a v) ^ 3 :=
          le_trans hsmall (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
        exact le_of_mul_le_mul_right h2 hA3
      have hLHYbracket : lhyC * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) < 1 := by
        have h2 : ρ * (_root_.BoseGases.a v) ^ 3 ≤ 1 / (4 * lhyC ^ 2) :=
          le_trans hsmall (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _)))
        have h3 : Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) ≤ 1 / (2 * lhyC) := by
          have h4 : Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) ≤ Real.sqrt (1 / (4 * lhyC ^ 2)) :=
            Real.sqrt_le_sqrt h2
          have h5 : Real.sqrt (1 / (4 * lhyC ^ 2)) = 1 / (2 * lhyC) := by
            have h6 : (1 : ℝ) / (4 * lhyC ^ 2) = (1 / (2 * lhyC)) ^ 2 := by ring
            rw [h6, Real.sqrt_sq (by positivity)]
          linarith [h4, h5]
        have h7 : lhyC * (1 / (2 * lhyC)) = 1 / 2 := by field_simp
        have h8 := mul_le_mul_of_nonneg_left h3 hlhyC.le
        rw [h7] at h8
        linarith
      have hPAR : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt ρ (_root_.BoseGases.a v))
          (ρ * (_root_.BoseGases.a v) ^ 3) :=
        hδ₁p (ρ * (_root_.BoseGases.a v) ^ 3) (mul_pos hρ hA3) hδ₁'
      have hCMP : Work.BoseBox.CompareBox v h ρ := hδ₂p ρ hρ hρδ₂
      have hside : 0 < Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) := by
        simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
          Work.BoseBox.fsParams]
        exact mul_pos (Work.BoseBox.fsXp_pos (mul_pos hρ hA3))
          (Real.rpow_pos_of_pos (mul_pos hρ hapos) _)
      have hbound := hLb ρ hρ hεL' hPAR
      -- (A) `LHYBox` at `μ = ρ`: the infimum over all sectors dominates `ℓ³Λ`
      have hEB : Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
            Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ
          ≤ Work.BoseBox.EBoxAt ρ (_root_.BoseGases.a v) v h := by
        rw [Work.BoseBox.EBoxAt, Work.BoseBox.EBox]
        refine le_ciInf (fun n => ?_)
        haveI : Nonempty (Submission.BoseGases.CSBox n (Work.BoseBox.boxSide
            (Work.BoseBox.paramsAt ρ (_root_.BoseGases.a v)) ρ (_root_.BoseGases.a v))) :=
          Submission.BoseGases.nonempty_CSBox n
            (by show 0 < Work.BoseBox.sideAt ρ (_root_.BoseGases.a v); exact hside)
        refine le_ciInf (fun Φ => ?_)
        rw [le_div_iff₀ Φ.sq_pos]
        exact hbound n Φ
      -- (B) the `n = 0` sector of `LHYBox` forces `Λ ≤ 0`
      have hΛ0 : Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ ≤ 0 := by
        obtain ⟨Φ₀⟩ := (Submission.BoseGases.nonempty_CSBox 0 hside :
          Nonempty (Submission.BoseGases.CSBox 0
            (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v))))
        have hb := hbound 0 Φ₀
        rw [boxWordU_zero] at hb
        have hI : 0 < (∫ x in Submission.BoseGases.abox 0
              (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)),
            ((Φ₀ : Submission.BoseGases.X 0 → ℝ) x) ^ 2) := Φ₀.sq_pos
        have hℓ3 : 0 < Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 := pow_pos hside 3
        have hpos : 0 < Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
            (∫ x in Submission.BoseGases.abox 0 (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)),
              ((Φ₀ : Submission.BoseGases.X 0 → ℝ) x) ^ 2) := mul_pos hℓ3 hI
        have hb' : Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ *
            (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
              (∫ x in Submission.BoseGases.abox 0
                  (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)),
                ((Φ₀ : Submission.BoseGases.X 0 → ℝ) x) ^ 2)) ≤ 0 := by
          nlinarith [hb]
        exact nonpos_of_mul_nonpos_left hb' hpos
      -- (C) `CompareBox` at `μ = ρ`: FS's factor `((L+ℓ)/ℓ)³` with the boundary
      --     loss `((L+ℓ)/L)³ → 1` absorbed by one unit of the error coefficient
      obtain ⟨LΛ, hLΛpos, hLΛ⟩ := Lambda_factor_absorb (a := _root_.BoseGases.a v) (ρ := ρ)
        (ℓ := Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) (C := C) (η₀ := η₀)
        hρ hapos hside.le hC hLHYbracket
      refine ⟨max 1 LΛ, le_max_left _ _, fun L hL N hN Ψ => ?_⟩
      have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
      have hLΛ' : LΛ ≤ L := le_trans (le_max_right _ _) hL
      have hc := hCMP L hL1 N Ψ
      have hmin : Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
            Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ
          ≤ min 0 (Work.BoseBox.EBoxAt ρ (_root_.BoseGases.a v) v h) := by
        have h1 : min (0 : ℝ) (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
              Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ)
            ≤ min 0 (Work.BoseBox.EBoxAt ρ (_root_.BoseGases.a v) v h) :=
          min_le_min_left 0 hEB
        have h2 : min (0 : ℝ) (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
              Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ)
            = Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
              Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ :=
          min_eq_right (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hside.le 3) hΛ0)
        rwa [h2] at h1
      have hnonneg : 0 ≤ ((L + Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) /
          Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) ^ 3 :=
        pow_nonneg (div_nonneg (by linarith) hside.le) 3
      have hmul := mul_le_mul_of_nonneg_left hmin hnonneg
      have hpow : ((L + Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) /
            Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) ^ 3 *
          Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3
          = (L + Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) ^ 3 := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hside))]
      have hstep : (L + Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) ^ 3 *
            Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ
          ≤ Work.UBB.Rayl N L v Ψ - 8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ) := by
        have h1 : ((L + Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) /
              Work.BoseBox.sideAt ρ (_root_.BoseGases.a v)) ^ 3 *
              (Work.BoseBox.sideAt ρ (_root_.BoseGases.a v) ^ 3 *
                Work.UBB.Lambda (_root_.BoseGases.a v) C η₀ ρ)
            ≤ Work.UBB.Rayl N L v Ψ - 8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ) :=
          le_trans hmul hc
        rwa [← mul_assoc, hpow] at h1
      have hgoal : L ^ 3 * Work.UBB.Lambda (_root_.BoseGases.a v) (C + 1) η₀ ρ
          ≤ Work.UBB.Rayl N L v Ψ - 8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ) :=
        le_trans (hLΛ L hLΛ') hstep
      rw [← Lambda_eq_gcTwoTerm]
      exact hgoal
  · -- the case `a v = 0`: `CompareBox` alone
    obtain ⟨δ₂, hδ₂, hδ₂p⟩ := ext_pos_le hcmp
    have hCMP : Work.BoseBox.CompareBox v h (δ₂ / 2) :=
      hδ₂p (δ₂ / 2) (by positivity) (by linarith)
    have ha0' : _root_.BoseGases.a v = 0 := ha0.symm
    have hside0 : Work.BoseBox.sideAt (δ₂ / 2) (_root_.BoseGases.a v) = 0 := by
      simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
        Work.BoseBox.fsParams, ha0', mul_zero, zero_rpow_neg_half]
    have hray : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, ∀ Ψ : BoseGases.CInfty0Box N L,
        0 ≤ Work.UBB.Rayl N L v Ψ := by
      intro L hL1 N Ψ
      have hc := hCMP L hL1 N Ψ
      rw [hside0, ha0'] at hc
      simp [Submission.BoseGases.gcTwoTerm] at hc
      linarith
    refine ⟨1, one_pos, fun ρ hρ hsmall => ⟨1, le_rfl, fun L hL1 N hN Ψ => ?_⟩⟩
    have := hray L hL1 N Ψ
    rw [ha0']
    simp [Submission.BoseGases.gcTwoTerm]
    linarith

/-! ## The diagnosis: what happens when `a v < 0`

The two lemmas below are the machine-checked core of the file-header discussion: at a
negative scattering length the box side collapses and `CompareBox` degenerates, so
`PerStateBox` is *false* (see `not_perStateBox_of_av_neg`), while `LHYBox` is *vacuous*
(`lhyBox_of_av_neg`); the unconditional statement is therefore equivalent to the claim
that every potential of negative scattering length has a box state of negative energy
— a variational statement about `𝓗 N v` that is not carried by any hypothesis here. -/

/-- At a negative scattering length `CompareBox ρ` degenerates
(`sideAt μ (a v) = 0`, `lhyBox_of_av_neg.sideAt_eq_zero_of_av_neg`, so the factor
`(L / sideAt μ (a v))³` vanishes) to the statement that **every** box energy dominates
the *linear* function `8π(a v)ρN` of the particle number — a lower bound on the box
Hamiltonian, carrying no sign information on `a v`. -/
lemma compareBox_iff_rayl_ge_of_av_neg {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {ρ : ℝ} (hav : _root_.BoseGases.a v < 0) (hρ : 0 < ρ) :
    (Work.BoseBox.CompareBox v h ρ ↔ ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      ∀ Ψ : BoseGases.CInfty0Box N L,
        8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ) ≤ Work.UBB.Rayl N L v Ψ) := by
  have hz := sideAt_eq_zero_of_av_neg hρ hav
  constructor
  · intro hc L hL N Ψ
    have h1 := hc L hL N Ψ
    rw [hz] at h1
    simp only [div_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] at h1
    linarith
  · intro hg L hL N Ψ
    rw [hz]
    simp only [div_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul]
    linarith [hg L hL N Ψ]

/-- **`CompareBox` at a negative scattering length forces every box energy to be
nonnegative** (letting `ρ → 0⁺` in `8π(a v)ρN ≤ Rayl N L v Ψ`).  This is the exact
remaining gap of the unconditional statement: together with `not_perStateBox_of_av_neg`
the requested lemma is *equivalent* to the variational claim that some potential of
negative scattering length has a box state of negative energy — a claim about `𝓗 N v`
that none of the hypotheses (`ScatSol`, `LHYBox`, `CompareBox`, `ParamsOK`) carries. -/
lemma rayl_nonneg_of_eventually_compareBox_of_av_neg {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} (hav : _root_.BoseGases.a v < 0)
    (hcmp : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.BoseBox.CompareBox v h ρ) :
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, ∀ Ψ : BoseGases.CInfty0Box N L,
      0 ≤ Work.UBB.Rayl N L v Ψ := by
  intro L hL1 N Ψ
  have htendN : Tendsto (fun ρ : ℝ => 8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 : Tendsto (fun ρ : ℝ => (8 * π * (_root_.BoseGases.a v) * (N : ℝ)) * ρ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 ((8 * π * (_root_.BoseGases.a v) * (N : ℝ)) * 0)) := h1.const_mul _
    rw [mul_zero] at h2
    exact h2.congr (fun ρ => by ring)
  have hev : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      8 * π * (_root_.BoseGases.a v) * ρ * (N : ℝ) ≤ Work.UBB.Rayl N L v Ψ := by
    filter_upwards [hcmp, self_mem_nhdsWithin] with ρ hc hρ
    rw [compareBox_iff_rayl_ge_of_av_neg hav hρ] at hc
    exact hc L hL1 N Ψ
  exact le_of_tendsto htendN hev

/-- **`PerStateBox v η₀ C` is FALSE at a negative scattering length.**  The `N = 0`
sector forces `gcTwoTerm (a v) C (1/2+η₀) ρ ≤ 0` for every admissible `ρ`
(`perStateBox_forces_gcTwoTerm_nonpos`), while for `a v < 0` the admissibility condition
`ρ(a v)³ ≤ ε₀` holds for *every* `ρ > 0` and `gcTwoTerm (a v) C (1/2+η₀) ρ > 0` for some
such `ρ` (`exists_gcTwoTerm_pos_of_neg`). -/
theorem not_perStateBox_of_av_neg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {η₀ C : ℝ}
    (hav : _root_.BoseGases.a v < 0) (hC : 0 ≤ C) : ¬ Work.BoseBox.PerStateBox v η₀ C := by
  intro hps
  obtain ⟨ε₀, hε₀, hfor⟩ := perStateBox_forces_gcTwoTerm_nonpos hps
  obtain ⟨ρ, hρ, hpos⟩ :=
    exists_gcTwoTerm_pos_of_neg (a := _root_.BoseGases.a v) (C := C) (s := 1 / 2 + η₀) hav hC
  have h3 : (_root_.BoseGases.a v) ^ 3 < 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_lt hav)]
  have hadm : ρ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ :=
    le_of_lt (lt_of_lt_of_le (mul_neg_of_pos_of_neg hρ h3) hε₀.le)
  exact not_lt_of_ge (hfor ρ hρ hadm) hpos

end Work.BoseBox
