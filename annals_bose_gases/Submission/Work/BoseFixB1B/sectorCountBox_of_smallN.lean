import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.paramsOK_fsParams_le_one
import Submission.Work.BoseFixB1.CornerMismatch
import Submission.Work.BoseFixB1.CrossWordsDefs
import Submission.Work.BoseFixB1.corner_regime
import Submission.Work.BoseFixB1B.sectorCountBox_assembly
import Submission.Work.BoseFixB1S.PerBoxGapAbsorbB1
import Submission.Work.BoseFixB1S.mfGatesV2B1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountBox_of_smallN` — the target reduced to the small-`n` bounds

This module packages FS's descent into the **final reduction** of
`Work.BoseFixB1B.SectorCountSmallboxBox v h`: the target follows from the *small-`n`* group bounds
of FS `thm:smallbox` (`final_v2.tex` 3960–4050), i.e. from `SmallNBounds v h Cn C` below:

* at every admissible `μ`, every `u ∈ goodSet`, every group size `n'` with
  `C_n μ|B(u)| ≤ n' < (C_n+1) μ|B(u)|`, FS's **positive group bound**
  `(1/18)·μ·(n'/|B|)·∬w_{1,B}·∫Ψ² ≤ sbWord_{n'}(Ψ)` — the reduced form of their intermediate
  estimate `e_B(n′) ≥ ⅛(μ−n′/|B|)²∬w₁ − Cμa(n′/|B|)∫χ_B²` for large `C_n`;
* at every remainder size `n''` with `n'' ≤ 2C_nμ|B|`, the **intermediate count form**
  `[¼(n″/|B| − μ)²∬w₁ − ½μ²∬w₁ − C(μ²aΓ_B∬w₁ + μa)]·∫Ψ² ≤ sbWord_{n''}(Ψ)`;
* at every count `n` with `n/|B| < C_n μ`, the target's own inequality
  `boxLHS h (1/20) C μ n u·∫Ψ² ≤ sbWord_n(Ψ)` (the `m = 0` branch of the descent).

All three are the *same rung* (FS `lm:appinteractionestimate` + `lm:appbogolubov` at the sliding
box, plus the `C_n`-large reduction of the intermediate estimate); the descent itself —
the grouping (`sbWord_slice_superadd_regime_holds`), its iterated form
(`sbWord_descent_atSizes`), the `m ≥ 1` arithmetic (`sectorCountBox_descent_step` +
`fsStepEFinalArith`) and the `m = 0` case — is **proved** here and in
`Submission/Work/BoseFixB1B/sectorCountBox_assembly.lean`.

See `FINDING_sectorCountBox_grouping_session.md` for the full status, the numerical verification of
the descent arithmetic, and the exact residual (the sliding-box Bogoliubov port for `boxA2`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The small-`n` group bounds of FS's descent** (the residual analytic input of the target).
`C` is the error constant of the target's `boxLHS`; `C_n` is FS's grouping constant (any
`C_n ≥ 2` works for the descent; the `C_n`-large reduction of the intermediate estimate is part of
the *analytic* input `hB1`). -/
def SmallNBounds (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        (∀ {n' : ℕ}, Cn * μ * PBBV v μ u ≤ (n' : ℝ) →
            (n' : ℝ) < (Cn + 1) * μ * PBBV v μ u →
            ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → InBox v μ u Ψ →
              (1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u
                  * (∫ x in Submission.BoseGases.abox n' (PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1.sbWord h μ u Ψ)
        ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * Cn * μ * PBBV v μ u →
            ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → InBox v μ u Ψ →
              ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u
                  - (1 / 2) * μ ^ 2 * PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                      + μ * (_root_.BoseGases.a v)))
                  * (∫ x in Submission.BoseGases.abox n'' (PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1.sbWord h μ u Ψ)
        ∧ (∀ {n : ℕ}, (n : ℝ) < Cn * μ * PBBV v μ u →
            ∀ (Ψ : Submission.BoseGases.X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → InBox v μ u Ψ →
              boxLHS h (1 / 20) C μ n u
                  * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1.sbWord h μ u Ψ)

/-- **The target from the small-`n` bounds.**  With `c = 1/20` and FS's grouping choice
`n' = ⌈C_n μ|B(u)|⌉`, `m = n/n'`, `n'' = n % n'`, the `m = 0` branch is the third conjunct of
`SmallNBounds` and the `m ≥ 1` branch is `Work.BoseFixB1B.sectorCountBox_descent_step`. -/
theorem sectorCountSmallboxBox_of_smallN {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {Cn C : ℝ} (hCn : 2 ≤ Cn) (hC : 0 ≤ C) (hB : SmallNBounds v h Cn C) :
    SectorCountSmallboxBox v h := by
  obtain ⟨ε₁, hε₁, hBnd⟩ := hB
  obtain ⟨εr, hεr, hBreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  have hε₁le : min (min ε₁ εr) 1 ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεrle : min (min ε₁ εr) 1 ≤ εr := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε1le : min (min ε₁ εr) 1 ≤ 1 := min_le_right _ _
  refine ⟨min (min ε₁ εr) 1, 1 / 20, C, lt_min (lt_min hε₁ hεr) one_pos,
    (by norm_num), (by norm_num), hC, ?_⟩
  intro μ hAdm n Φ u hu hsupp hnorm
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm hε₁le
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm hε1le
  obtain ⟨hR16, hRχ⟩ := hBreg μ hAdm.1 (hAdm.2.1.trans hεrle)
  -- the standing data
  have hμ : 0 < μ := hAdm.1
  have hav0 : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
  have hd1 : PBd v μ ≤ 1 := by
    rw [PBd, Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hav0 3)) ht1 (by norm_num)
  have hμcube : 1 ≤ μ * (PBℓ v μ * PBd v μ) ^ 3 := by
    have hh := Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube (A := _root_.BoseGases.a v)
      (μ := μ) hav0 hμ ht1
    simpa only [PBℓ, PBd, mul_comm] using hh
  have hV : 0 < PBBV v μ u := by
    rw [PBBV]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hμV : 1 ≤ μ * PBBV v μ u := by
    rw [PBBV]
    have hld : 0 < PBℓ v μ * PBd v μ := mul_pos hℓ hd
    have h13 : μ ^ (-(1 / 3 : ℝ)) ≤ PBℓ v μ * PBd v μ := by
      rw [Work.BoseFixB1S.rpow_neg_third_eq]
      exact Work.BoseFixB1S.inv_third_le_of_one_le_mul_cube hμ hld.le hμcube
    have hvol := Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ h13 hu
    have hcube : μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
      rw [Work.BoseFixB1S.rpow_neg_third_eq μ]
      rw [← Real.rpow_natCast (μ ^ (-1 / 3 : ℝ)) 3,
        ← Real.rpow_mul (x := μ) hμ.le (-1 / 3) ((3 : ℕ) : ℝ),
        show ((-1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
        mul_inv_cancel₀ (ne_of_gt hμ)]
    calc (1 : ℝ) = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := hcube.symm
      _ ≤ μ * Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u :=
          mul_le_mul_of_nonneg_left hvol hμ.le
  obtain ⟨h1, h2, h3⟩ := hBnd μ hAdm₁ u hu
  -- FS's grouping parameters: `n' = ⌈C_n μ|B(u)|⌉`, `m = n/n'`, `n'' = n % n'`
  set X : ℝ := Cn * μ * PBBV v μ u with hX
  have hX0 : 0 < X := by
    have hCn0 : 0 < Cn := by linarith
    rw [hX]; exact mul_pos (mul_pos hCn0 hμ) hV
  set n' : ℕ := ⌈X⌉₊ with hn'def
  have hn'pos : 0 < n' := by
    rw [hn'def]; exact Nat.ceil_pos.mpr hX0
  have hn'ge : X ≤ (n' : ℝ) := by
    rw [hn'def]; exact Nat.le_ceil X
  have hn'lt : (n' : ℝ) < X + 1 := by
    rw [hn'def]; exact Nat.ceil_lt_add_one hX0.le
  have hn'le : (n' : ℝ) < (Cn + 1) * μ * PBBV v μ u := by
    have hle : X + 1 ≤ (Cn + 1) * μ * PBBV v μ u := by
      have heq : (Cn + 1) * μ * PBBV v μ u = X + μ * PBBV v μ u := by rw [hX]; ring
      rw [heq]; linarith [hμV]
    linarith
  by_cases hcase : n < n'
  · -- ## the `m = 0` branch: `n` is below the group size
    have hnX : (n : ℝ) < X := by
      have hnle : n + 1 ≤ n' := hcase
      have h2' : (n : ℝ) + 1 ≤ (n' : ℝ) := by exact_mod_cast hnle
      linarith [hn'lt]
    have hthis := h3 (n := n) (by rw [hX] at hnX; exact hnX) (Φ : Submission.BoseGases.X n → ℝ)
      Φ.contDiff hsupp
    rw [hnorm, mul_one] at hthis
    show boxLHS h (1 / 20) C μ n u ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
    exact hthis
  · -- ## the `m ≥ 1` branch
    have hn'n : n' ≤ n := le_of_not_gt hcase
    have hm : 1 ≤ n / n' := Nat.one_le_div_iff hn'pos |>.mpr hn'n
    have hn''lt : n % n' < n' := Nat.mod_lt n hn'pos
    have hn''V : ((n % n' : ℕ) : ℝ) ≤ 2 * Cn * μ * PBBV v μ u := by
      have h1' : ((n % n' : ℕ) : ℝ) < (n' : ℝ) := by exact_mod_cast hn''lt
      have h3' : X + 1 ≤ 2 * Cn * μ * PBBV v μ u := by
        have heq : 2 * Cn * μ * PBBV v μ u = 2 * X := by rw [hX]; ring
        rw [heq]
        have hXge : 1 ≤ X := by
          have hle1 : 1 ≤ Cn * μ * PBBV v μ u := by nlinarith [hCn, hμV]
          rw [hX]; exact hle1
        linarith
      linarith
    have h2μ : 2 * μ ≤ (n' : ℝ) / PBBV v μ u := by
      have hCn2 : 2 * μ * PBBV v μ u ≤ Cn * μ * PBBV v μ u := by nlinarith [hCn, hμ, hV]
      have hfin : 2 * μ * PBBV v μ u ≤ (n' : ℝ) := le_trans hCn2 (hX.ge.trans hn'ge)
      rw [le_div_iff₀ hV]
      linarith
    have hmain := sectorCountBox_descent_step (v := v) (h := h) hv hv1 hvrad hR hv_supp hav
      hAdm hR16 hRχ u hu C (n := n) (n' := n') (n'' := n % n')
      (by rw [mul_comm]; exact (Nat.div_add_mod n n').symm) hm hn''lt h2μ
      (h1 (n' := n') (hX.ge.trans hn'ge) hn'le)
      (h2 (n'' := n % n') hn''V) Φ.contDiff hsupp hnorm
    show boxLHS h (1 / 20) C μ n u ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
    exact hmain

end Work.BoseFixB1B
