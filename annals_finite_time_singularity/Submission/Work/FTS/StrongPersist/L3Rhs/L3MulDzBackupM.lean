/-
# `L3MulDzBackupM` — the mixed-slot fallback for `L3MulDz`

Self-contained (namespace-disjoint) fallback for the mixed slots of the product `h · D_z f`:
`(D_z^J D_θ^I (h·D_z f) · Wt)² ≤ C |h|²_{𝒲^{4,∞}} GmajW α f`, `1 ≤ I`, `I+J ≤ 3`.

The proof follows `Work.FTS.OpenPkg.WProdWin.mslot_le_winf` (whose private auxiliary
`mslot_gside_le` is re-derived here as `gside_le_b`), with the `f`-side slots shifted by one
radial derivative whenever a `θ`-derivative falls on the factor `D_z f`
(`Work.FTS.StrongPersist.L3Rhs.mixed_Dz_eq`, `…dzIter_Dz_eq`).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM

open Work.Spaces (Dz DzIter DthIter mixed Wt w wTheta HkIntegrand eta gam)

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.OpenPkg.WProdWin

/-! ## Elementary angular algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

private theorem phi_sq_b {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

private theorem psi2_le_four_b {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·Wt)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq_b {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Wt α z θ) ^ 2 = (x * w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Wt, wTheta, mul_pow, hstep]
  ring

/-! ## The `f`-side step: the mean-term estimate produces the `TW`-block of `GmajW` -/

private theorem gside_le_b {α CB : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hfm : Work.Spaces.HkMem α 4 f)
    (hCB : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (DzIter d f z θ * w z) ^ 2
          ≤ CB * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
              + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z))
    {d : ℕ} (hd : d ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (DzIter d f z θ * Wt α z θ) ^ 2
      ≤ max CB 1 * GmajW α f z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  have hX0 : 0 ≤ (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
      + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α f d z))
  have hg1 : (DzIter d f z θ * w z) ^ 2
      ≤ max CB 1 * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  have hmem : d ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α f d z
      ≤ ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α f d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α f d' z) hmem
  have hw : (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2) ≤ HgInt α f z :=
    w_sq_mul_slice_le_HgInt hfm (by omega) hz
  have hXle : (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z
      ≤ HgInt α f z + (gam α - 1)⁻¹ * ∑ d' ∈ Finset.range 4,
          Work.FTS.H2.WPQ.Aang α f d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  rw [mul_Wt_sq_b hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) = TW α θ := by
    rw [TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((DzIter d f z θ * w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
      = (DzIter d f z θ * w z) ^ 2 * TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) * TW α θ
      ≤ GmajW α f z θ := by
    simp only [GmajW]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
  calc (max CB 1 * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
          + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z)) * TW α θ
      = max CB 1 * (((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
          + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) * TW α θ) := by ring
    _ ≤ max CB 1 * GmajW α f z θ := mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_dz_le_b : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
  obtain ⟨CB, hCB0, hCBmean⟩ := dzIter_w_mean_le
  have hCpos : (0 : ℝ) < 2 * 10 ^ 12 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 12 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 12 * (1 + max CB 1), hCpos, ?_⟩
  intro α h f hα hα1 hsmh hWm hsmf hfm I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hGnn : 0 ≤ GmajW α f z θ := GmajW_nonneg hα f hθI
  have hHkG : HkIntegrand α 4 f z θ ≤ GmajW α f z θ := HkIntegrand_le_GmajW hα f hθI
  have hHknn : 0 ≤ HkIntegrand α 4 f z θ := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hM0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hJ3 : J ≤ 3 := by omega
  have hJ4 : J ≤ 4 := by omega
  have hI4 : I ≤ 4 := by omega
  have h1M : (1 : ℝ) ≤ 1 + max CB 1 := by linarith
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Dz f) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hsmf
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I h (Dz f) hsmh hDzsm z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((mixed b a h z θ) * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) with hYdef
  have hYsplit : (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (mixed J I (fun z θ => h z θ * Dz f z θ) z θ) * Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
        * GmajW α f z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul (Work.Spaces.choose_sq_le_256 I a (by omega) (by omega))
              (Work.Spaces.choose_sq_le_256 J b (by omega) (by omega))
              (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((mixed b a h z θ) * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    -- the `h`-factor, in both regimes
    have hma : (mixed b a h z θ) ^ 2
        ≤ 40000 * (Work.Spaces.WlInf α 4 h) ^ 2 := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0
        rw [Work.Spaces.mixed_zero_right]
        have hh : |DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
          Work.FTS.OpenPkg.DzIter_le_WlInf_open hsmh hWm (by omega) hz hθ
        have h1 : (DzIter b h z θ) ^ 2 ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 :=
          Work.Spaces.sq_le_sq_of_abs_le hh
        nlinarith [h1, sq_nonneg (Work.Spaces.WlInf α 4 h)]
      · have ha1 : 1 ≤ a := by omega
        have hh := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := h) (a := a) (b := b)
          hα hsmh hWm ha1 (by omega) hz hθ
        calc (mixed b a h z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 h
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le hh
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq_b hθ]; ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 * 4 :=
              mul_le_mul_of_nonneg_left (psi2_le_four_b hα hα1 hθ) (sq_nonneg _)
          _ = 40000 * (Work.Spaces.WlInf α 4 h) ^ 2 := by ring
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on the `D_z f` factor
      have hIa : 1 ≤ I - a := by omega
      have hmg : (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ) ^ 2
          ≤ HkIntegrand α 4 f z θ := by
        have hshift : mixed (J - b) (I - a) (Dz f) z θ = mixed (J - b + 1) (I - a) f z θ :=
          mixed_Dz_eq hsmf (J - b) (I - a) hz hθ0 hθ1
        rw [hshift]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (I - a) (J - b + 1) hIa
          (by omega)
      have hbase2 : ((mixed b a h z θ)
            * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ (40000 * (Work.Spaces.WlInf α 4 h) ^ 2) * HkIntegrand α 4 f z θ := by
        rw [mul_pow]
        exact mul_le_mul hma hmg (sq_nonneg _) (by positivity)
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ 65536 * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((40000 * (Work.Spaces.WlInf α 4 h) ^ 2)
              * HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ := by
            rw [show 65536 * ((40000 * (Work.Spaces.WlInf α 4 h) ^ 2)
                  * HkIntegrand α 4 f z θ)
                = (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * HkIntegrand α 4 f z θ) from by ring]
            calc (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * HkIntegrand α 4 f z θ)
                ≤ (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hM0]) (mul_nonneg hWsq hGnn)
              _ = (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ := by ring
    · -- all `θ`-derivatives fall on `h`: the mean-term estimate is consumed
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b + 1 ≤ 3 := by omega
      have hmb : (mixed b a h z θ) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have hh := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := h) (a := a) (b := b)
          hα hsmh hWm ha1 (by omega) hz hθ
        calc (mixed b a h z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 h
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le hh
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq_b hθ]; ring
      have hT : (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ) ^ 2
          = (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2 := by
        rw [hsub, Work.Spaces.mixed_zero_right, dzIter_Dz_eq]
      have hgside := gside_le_b (α := α) (CB := CB) (f := f) hα hfm
        (fun d hd z' θ' hz' hθ0' hθ1' =>
          hCBmean α f d hα hα1 hsmf hfm hd z' θ' hz' hθ0' hθ1') hdJ hz hθ
      have hbase2 : ((mixed b a h z θ)
            * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1) * GmajW α f z θ := by
        rw [mul_pow, hT]
        calc (mixed b a h z θ) ^ 2 * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2
            ≤ ((100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2) := by ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * (max CB 1 * GmajW α f z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1) * GmajW α f z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ 65536 * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1)
              * GmajW α f z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ := by
            rw [show 65536 * ((100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1)
                  * GmajW α f z θ)
                = (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ) from by ring]
            have hAB : (65536 * 10000 * (max CB 1) : ℝ)
                ≤ 65536 * 40000 * (1 + max CB 1) := by nlinarith [hM0]
            calc (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ)
                ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) ≤ 4 := by exact_mod_cast hI4
    have h2 : (J : ℝ) ≤ 4 := by exact_mod_cast hJ4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hKper_nn : (0 : ℝ) ≤ 65536 * 40000 * (1 + max CB 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) (by linarith)
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                * GmajW α f z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ) := by rw [hsumconst]; ring
    _ ≤ 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ ≤ (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
        rw [show 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ)
            = (625 * (65536 * 40000 * (1 + max CB 1))) * ((Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ) from by ring]
        have hle : 625 * (65536 * 40000 * (1 + max CB 1)) ≤ 2 * 10 ^ 12 * (1 + max CB 1) := by
          nlinarith [hM0]
        calc (625 * (65536 * 40000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ)
            ≤ (2 * 10 ^ 12 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                * GmajW α f z θ := by ring

end Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
