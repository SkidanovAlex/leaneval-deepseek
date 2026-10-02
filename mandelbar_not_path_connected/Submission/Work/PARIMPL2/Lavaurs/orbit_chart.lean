import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

open Complex

/-! ## The non-degeneracy of one model step, from the transit strip and smallness

The exact identity `Work.Implosion.Disp.ecalPt_add_modelDisp` relates one iterate of the
local model `normalForm a h` to the translation `u ↦ u + modelDisp a h u` in the Écalle
coordinate, but it needs the three non-degeneracies `ecalE a u ≠ 1`,
`1 + dispNum1 a h u ≠ 0`, `1 + dispNum2 a h u ≠ 0`.  In the transit regime these are
*automatic*: the strip `R ≤ Re u ≤ π/λ − R` with `R ≥ 4` keeps `u` away from the punctures
`(πi/a)ℤ` of the Écalle cylinder, and `4(‖ζ‖ + λ) ≤ 1` together with `‖h‖ ≤ 2` keeps the
perturbations `A₁`, `A₂` of absolute value `≤ 1/2`, hence `1 + A₁`, `1 + A₂` in the unit
disc centred at `1`.  This is exactly the derivation performed inline in
`Work.Implosion.Approx.approxEcal_step`; here it is packaged as a standalone lemma. -/

/-- If `‖z‖ ≤ 1/2` then `1 + z ≠ 0`. -/
private lemma one_add_ne_zero_of_norm_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : 1 + z ≠ 0 := by
  intro h
  have h1 : z = -1 := by linear_combination h
  rw [h1, norm_neg, norm_one] at hz
  norm_num at hz

/-- For `a = λ·I` with `λ > 0`, the transit strip `R ≤ Re u ≤ π/λ − R` with `R ≥ 4`
contains no puncture of the Écalle cylinder: `ecalE a u ≠ 1`.  Indeed `ecalE a u = 1`
forces `u = n·(π/λ)` with `n ∈ ℤ`, and `Re u ≥ R > 0` gives `n ≥ 1`, whence
`Re u ≥ π/λ > π/λ − R ≥ Re u`. -/
private lemma ecalE_ne_one_of_mem_transitStrip {lam R : ℝ} (hlam : 0 < lam) (hR : 4 ≤ R)
    {u : ℂ} (hstrip : u ∈ Work.Implosion.transitStrip lam R) :
    Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1 := by
  intro hE
  have hane : ((lam : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hmem : u ∈ Work.Implosion.periodLattice ((lam : ℂ) * Complex.I) := hE
  rw [Work.Implosion.mem_periodLattice_iff _ _ hane] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hratio : Real.pi * Complex.I / ((lam : ℂ) * Complex.I) = ((Real.pi / lam : ℝ) : ℂ) := by
    rw [mul_div_mul_right _ _ Complex.I_ne_zero]
    exact (Complex.ofReal_div _ _).symm
  rw [hratio] at hn
  have hure : u.re = (n : ℝ) * (Real.pi / lam) := by
    rw [hn]; simp [Complex.mul_re]
  rw [Work.Implosion.mem_transitStrip_iff] at hstrip
  obtain ⟨hstr1, hstr2⟩ := hstrip
  have hπ : 0 < Real.pi / lam := div_pos Real.pi_pos hlam
  have h1' : (n : ℝ) * (Real.pi / lam) ≥ R := by rw [← hure]; exact hstr1
  have hpos : 0 < (n : ℝ) := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [h1', hπ, hR]
  have hposZ : (0 : ℤ) < n := by exact_mod_cast hpos
  have hn1 : (1 : ℤ) ≤ n := Int.lt_iff_add_one_le.mp hposZ
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h2' : u.re ≥ Real.pi / lam := by rw [hure]; nlinarith [hn1R, hπ]
  linarith [hstr2, h2', hR]

/-- The two numerator perturbations `A₁ = (ζ−a)h(ζ)`, `A₂ = (ζ+a)h(ζ)` at `ζ = ecalPt a u`
are bounded by `(‖ζ‖ + ‖a‖)·C` as soon as `‖h ζ‖ ≤ C`. -/
private lemma norm_dispNum_le_of_norm_h {a : ℂ} {h : ℂ → ℂ} (u : ℂ) {C : ℝ} (_hC : 0 ≤ C)
    (hh : ‖h (Work.Implosion.ecalPt a u)‖ ≤ C) :
    ‖Work.Implosion.dispNum1 a h u‖ ≤ (‖Work.Implosion.ecalPt a u‖ + ‖a‖) * C ∧
      ‖Work.Implosion.dispNum2 a h u‖ ≤ (‖Work.Implosion.ecalPt a u‖ + ‖a‖) * C := by
  have h1 : 0 ≤ ‖Work.Implosion.ecalPt a u‖ + ‖a‖ := by positivity
  constructor
  · rw [Work.Implosion.dispNum1, norm_mul]
    exact mul_le_mul (norm_sub_le _ _) hh (norm_nonneg _) h1
  · rw [Work.Implosion.dispNum2, norm_mul]
    exact mul_le_mul (norm_add_le _ _) hh (norm_nonneg _) h1

private lemma ane {lam : ℝ} (hlam : 0 < lam) : (lam : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero

/-- **Non-degeneracy of one model step in the transit regime.**  With `a = λ·I`, `λ > 0`,
`R ≥ 4`, `u` in the transit strip, `4(‖ecalPt a u‖ + λ) ≤ 1` and `‖h (ecalPt a u)‖ ≤ 2`,
all three hypotheses of `Work.Implosion.Disp.ecalPt_add_modelDisp` hold. -/
private lemma nondegenerate_of_strip_small {a : ℂ} {h : ℂ → ℂ} {lam R : ℝ} {u : ℂ}
    (hlam : 0 < lam) (ha : a = (lam : ℂ) * Complex.I) (hR : 4 ≤ R)
    (hstrip : u ∈ Work.Implosion.transitStrip lam R)
    (hsmall : 4 * (‖Work.Implosion.ecalPt a u‖ + lam) ≤ 1)
    (hh : ‖h (Work.Implosion.ecalPt a u)‖ ≤ 2) :
    Work.Implosion.ecalE a u ≠ 1 ∧ (1 + Work.Implosion.dispNum1 a h u) ≠ 0 ∧
      (1 + Work.Implosion.dispNum2 a h u) ≠ 0 := by
  have hna : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hE : Work.Implosion.ecalE a u ≠ 1 := by
    rw [ha]; exact ecalE_ne_one_of_mem_transitStrip hlam hR hstrip
  have hle : ‖Work.Implosion.ecalPt a u‖ + lam ≤ 1 / 4 := by linarith
  obtain ⟨hb1, hb2⟩ := norm_dispNum_le_of_norm_h (a := a) (h := h) u (C := 2) (by norm_num) hh
  have hb1' : ‖Work.Implosion.dispNum1 a h u‖ ≤ 1 / 2 := by
    have h2 : (‖Work.Implosion.ecalPt a u‖ + ‖a‖) * 2 ≤ 1 / 2 := by rw [hna]; linarith
    linarith
  have hb2' : ‖Work.Implosion.dispNum2 a h u‖ ≤ 1 / 2 := by
    have h2 : (‖Work.Implosion.ecalPt a u‖ + ‖a‖) * 2 ≤ 1 / 2 := by rw [hna]; linarith
    linarith
  exact ⟨hE, one_add_ne_zero_of_norm_le_half hb1', one_add_ne_zero_of_norm_le_half hb2'⟩

/-- **The model orbit is the chart orbit.**  In the normal-form chart `z = P.m c + P.s c·ζ`, one
iterate of `Ft c` corresponds to one iterate of the local model `ζ ↦ normalForm (a c) (h c) ζ`,
which in the Écalle coordinate is `u ↦ u + modelDisp (a c) (h c) u`.  Hence the `k`-th iterate of
a chart point is the chart point of the `k`-th *model* orbit, as long as the whole model orbit
stays in the transit strip (`u_j ∈ transitStrip lam R`, `4(‖ζ_j‖ + lam) ≤ 1`) and in the chart ball
`‖ζ_j‖ < P.r`, where `P.a c = i·lam` and `ζ_j = ecalPt (P.a c) u_j`.

Uses `P.conj` (`Ft c (m + s ζ) = m + s·normalForm (a c) (h c) ζ` on `‖ζ‖ < P.r`) and the exact
identity `Work.Implosion.ecalPt_add_modelDisp`
(`ecalPt a (u + modelDisp a h u) = normalForm a h (ecalPt a u)`), whose non-degeneracy
hypotheses `ecalE a u_j ≠ 1`, `1 + dispNum1 a h u_j ≠ 0`, `1 + dispNum2 a h u_j ≠ 0` are derived
from the strip and smallness hypotheses exactly as in the delivered
`Work.Implosion.Approx.approxEcal_step` (a degenerate `ecalE a u = 1` forces
`u.re = n·π/lam`, which the strip `R ≤ u.re ≤ π/lam - R` with `R ≥ 4` excludes, and
`‖dispNum‖ ≤ (‖ζ‖ + lam)·(3/2) ≤ 3/8 < 1` gives the other two). -/
theorem orbit_chart {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ P.ρ₀) (u0 : ℂ) (k : ℕ) {lam R : ℝ} (hlam : 0 < lam)
    (ha : P.a c = (lam : ℂ) * Complex.I) (hR : 4 ≤ R)
    (hstrip : ∀ j : ℕ, j ≤ k → Work.Implosion.modelOrbit (P.a c) (P.h c) j u0 ∈
      Work.Implosion.transitStrip lam R)
    (hsmall : ∀ j : ℕ, j ≤ k → 4 * (‖Work.Implosion.ecalPt (P.a c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ + lam) ≤ 1)
    (hk : ∀ j : ℕ, j ≤ k → ‖Work.Implosion.ecalPt (P.a c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ < P.r) :
    (Work.PARIMPL.Ft c)^[k] (P.m c + P.s c * Work.Implosion.ecalPt (P.a c) u0)
      = P.m c + P.s c * Work.Implosion.ecalPt (P.a c)
          (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) := by
  -- The `k`-th iterate of the chart point is the chart point of the `k`-th model orbit;
  -- proved by induction on `k`, one step being `P.conj` plus `ecalPt_add_modelDisp`.
  have main : ∀ k : ℕ,
      (∀ j : ℕ, j ≤ k → Work.Implosion.modelOrbit (P.a c) (P.h c) j u0 ∈
        Work.Implosion.transitStrip lam R) →
      (∀ j : ℕ, j ≤ k → 4 * (‖Work.Implosion.ecalPt (P.a c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ + lam) ≤ 1) →
      (∀ j : ℕ, j ≤ k → ‖Work.Implosion.ecalPt (P.a c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ < P.r) →
      (Work.PARIMPL.Ft c)^[k] (P.m c + P.s c * Work.Implosion.ecalPt (P.a c) u0)
        = P.m c + P.s c * Work.Implosion.ecalPt (P.a c)
            (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) := by
    intro k
    induction k with
    | zero => intro _ _ _; simp
    | succ n ih =>
      intro hstrip' hsmall' hk'
      -- the same hypotheses, restricted to the indices `≤ n`
      have hs : ∀ j : ℕ, j ≤ n → Work.Implosion.modelOrbit (P.a c) (P.h c) j u0 ∈
          Work.Implosion.transitStrip lam R :=
        fun j hj => hstrip' j (Nat.le_trans hj (Nat.le_succ n))
      have hm : ∀ j : ℕ, j ≤ n → 4 * (‖Work.Implosion.ecalPt (P.a c)
          (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ + lam) ≤ 1 :=
        fun j hj => hsmall' j (Nat.le_trans hj (Nat.le_succ n))
      have hb : ∀ j : ℕ, j ≤ n → ‖Work.Implosion.ecalPt (P.a c)
          (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ < P.r :=
        fun j hj => hk' j (Nat.le_trans hj (Nat.le_succ n))
      -- peel off one iterate and replace it by the chart expression of the model step
      rw [Function.iterate_succ_apply', ih hs hm hb]
      rw [P.conj c hc _ (by simpa using hb n le_rfl)]
      -- `h (ζ_n)` is bounded by `2` by the uniform bounds of the parameter normal form
      have hh2 : ‖P.h c (Work.Implosion.ecalPt (P.a c)
          (Work.Implosion.modelOrbit (P.a c) (P.h c) n u0))‖ ≤ 2 :=
        (P.bounds c hc).2.2.2.1 _ (by simpa using hb n le_rfl)
      have hnd := nondegenerate_of_strip_small hlam ha hR (hs n le_rfl) (hm n le_rfl) hh2
      -- the exact model step, in the Écalle coordinate
      rw [← Work.Implosion.Disp.ecalPt_add_modelDisp (P.a c) (P.h c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) n u0)
        (by rw [ha]; exact ane hlam) hnd.1 hnd.2.1 hnd.2.2]
      rw [Work.Implosion.modelOrbit_succ]
  exact main k hstrip hsmall hk

end Work.PARIMPL2.Lavaurs
