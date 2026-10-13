import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow11
import Submission.Work.FTS.Nonlinear.Open.Row11

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option linter.unusedVariables false

/-- **Priced row 11**: the `ℋ⁴`-honesty and the `α²`-bound of the star piece `N₁^{**} = 2 · ℛ(Φ̃_*) · F_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow11_of_wlInf` (row 11 in the open
vocabulary): that result states `∃ K, 0 < K ∧ ∀ …, Ctx … → HkMem α 4 (N1ss α Φs) ∧
Xn α (N1ss α Φs) ≤ K * α ^ 2`, but its `K` is opaque in `Cs`, which a consumer needing
`≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow)` cannot use.  The proof of `NRow11_of_wlInf` already
*constructs* the explicit constant `1 + Cw * (10 ^ 6 * Ca) * max Cs 0` (`Cw` = constant of
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `Ca` = `Work.FTS.Nonlinear.Pieces.RNPV2.Ca`), and
its body uses nothing but `0 < α`, `α ≤ 1`, `StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about
`Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs = ((z+1)/z) · ℛ(Φ̃_*)`, which `StarPkgo2.RW` supplies.  So
the proof is a copy of that proof with the interfaces (`N4Norm'`, `N4Extra'`, `Ctx`, `GalClass`,
`EllPkgGo`) removed and `C = 1 + Cw * (10 ^ 6 * Ca)`, using `max Cs 0 ≤ 1 + |Cs|`. -/
theorem N1ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ C * (1 + |Cs|) * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  have hCa0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca :=
    le_of_lt Work.FTS.Nonlinear.Pieces.RNPV2.Ca_pos
  refine ⟨1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca), ?_, ?_⟩
  · have h1 : 0 ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) :=
      mul_nonneg hCw.le (mul_nonneg (by norm_num) hCa0)
    linarith
  · intro α hαIoc Cs Φs hsp
    obtain ⟨hα, hα1⟩ := hαIoc
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hsp.toStarPkgo
    have hW : Work.Spaces.WlInfMem α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) :=
      show Work.Spaces.WlInfMem α 4
        (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) from hsp.RW.1
    have hWb : Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) ≤ Cs * α :=
      show Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ Cs * α from hsp.RW.2
    set WA : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) with hWA
    have hWA0 : 0 ≤ WA := by
      rw [hWA]
      exact Work.FTS.H2.sqm_WlInf_nonneg α 4 _ hW
    have hWAle : WA ≤ max Cs 0 * α := by
      rw [hWA]
      exact hWb.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    -- the smoothness of the radial factor and the weighted identity
    have hid := (Work.FTS.NonlinRows.smoothOpen_radA hα hα1 hs).2
    have hSOrad : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) :=
      (Work.FTS.NonlinRows.smoothOpen_radA hα hα1 hs).1
    have hmemG : Work.Spaces.WlInfMem α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.weighted_eq_Rv]
      exact hW
    have hWAeq : Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)
        = WA := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.weighted_eq_Rv, hWA]
    -- the two pointwise estimates for the radial factor
    have hrad : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m
            * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
          ≤ 200000 * WA := by
      intro m hm z hz θ hθ
      have h := Work.FTS.NonlinRows.WtoH_Radial_O hα hα1 hSOrad hmemG m hm z hz θ hθ
      rwa [hWAeq] at h
    have hmix : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
          ≤ 200000 * (WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have h := Work.FTS.NonlinRows.WtoH_Mixed_O hα hα1 hSOrad hmemG i l hi hli z hz θ hθ
      rwa [hWAeq] at h
    -- smoothness of the angular factor and of the piece
    have hSOang : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad
        (Work.FTS.Nonlinear.Pieces.RNPV2.smoothQuad_angF α)
    have hSOmul : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
          * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
          * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) Work.FTS.EllipticEst.Q0
      refine ContDiffOn.congr (hSOang.mul hSOrad) ?_
      intro p hp
      obtain ⟨z, θ⟩ := p
      rfl
    have hSmoothN1ss : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Nonlin.N1ss α Φs) := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
      simpa only [Work.FTS.Nonlinear.Pieces.RNPV2.angB] using hSOmul
    -- the weight
    set W : ℝ := 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA) with hWdef
    have hW0 : 0 ≤ W := by
      rw [hWdef]
      exact mul_nonneg (mul_nonneg (by norm_num) hCa0) (mul_nonneg hα.le hWA0)
    -- the pointwise hypotheses of `wtoHQ_of_pointwise_open`
    have hboundA : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m
            * Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ|
          ≤ 200000 * W := by
      intro m hm z hz θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hfac : Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ
          = Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
            * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ := by
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
        simp only [Work.FTS.Nonlinear.Pieces.RNPV2.angB]
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.pzIter_theta_mul m
          (Work.FTS.Nonlinear.Pieces.RNPV2.angF α)
          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)]
      rw [hfac]
      have habs : |(1 + z) * Work.Spaces.w z * z ^ m
            * (Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)|
          = |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ| := by
        rw [show (1 + z) * Work.Spaces.w z * z ^ m
              * (Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)
            = Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ * ((1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)
            by ring, abs_mul]
      rw [habs]
      have h1 := Work.FTS.Nonlinear.Pieces.RNPV2.angF_abs_le hα hα1 hθI
      have h2 := hrad m hm z hz θ hθ
      have h40 : (40 : ℝ) ≤ 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca := by
        have h := Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40
        nlinarith [hCa0]
      have harith : 40 * α * (200000 * WA) ≤ 200000 * W := by
        rw [hWdef]
        calc 40 * α * (200000 * WA)
            ≤ (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * α * (200000 * WA) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h40 hα.le
          _ = 200000 * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA)) := by ring
      calc |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
          ≤ (40 * α) * (200000 * WA) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ 200000 * W := harith
    have hboundB : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)) z θ|
          ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hl4 : l ≤ 4 := by omega
      have hi4 : i ≤ 4 := by omega
      have hΦ0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
        Work.FTS.Nonlinear.Pieces.RNPV2.Phi_nonneg α hα hθI
      have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l := by
        have hw0 : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]; positivity
        exact mul_nonneg (mul_nonneg (by linarith) hw0) (pow_nonneg (le_of_lt hz) l)
      have hfun : Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)
          = Work.Spaces.DthIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
        simp only [Work.FTS.Nonlinear.Pieces.RNPV2.angB]
      rw [hfun]
      -- the Leibniz bound, with the sum collapsed
      have hleib := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ)
        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) hSOang hSOrad z hz θ hθ
      have hsum : |Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|) :=
        hleib.trans (le_of_eq (by rw [Work.FTS.Nonlinear.Pieces.RNPV2.mixed_sum_collapse l i
          (Work.FTS.Nonlinear.Pieces.RNPV2.angF α)
          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ]))
      -- the per-`a` estimate
      have hterm : ∀ a ∈ Finset.range (i + 1),
          |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
            * |Work.Spaces.pzIter l
                (Work.Spaces.DthIter (i - a)
                  (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
            * ((1 + z) * Work.Spaces.w z * z ^ l)
          ≤ 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
        intro a ha
        have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        have heq : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              * |Work.Spaces.pzIter l
                  (Work.Spaces.DthIter (i - a)
                    (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
              * ((1 + z) * Work.Spaces.w z * z ^ l)
            = |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              * |(1 + z) * Work.Spaces.w z * z ^ l
                  * Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ| := by
          rw [abs_mul, abs_of_nonneg hρ]
          ring
        rw [heq]
        rcases lt_or_eq_of_le hai with hlt | heq2
        · -- `a < i`: the mixed estimate for the radial factor
          have h1 : 1 ≤ i - a := by omega
          have h2 : l + (i - a) ≤ 4 := by omega
          have hR := hmix (i - a) l h1 h2 z hz θ hθ
          have hD : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := by
            rcases eq_or_lt_of_le (Nat.zero_le a) with h0 | hpos
            · subst h0
              show |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ|
                ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
              have hf := Work.FTS.Nonlinear.Pieces.RNPV2.angF_abs_le hα hα1 hθI
              have h40 : 40 * α ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α :=
                mul_le_mul_of_nonneg_right
                  Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40 hα.le
              linarith
            · have ha4 : a ≤ 4 := by omega
              have hf := Work.FTS.Nonlinear.Pieces.RNPV2.dthU_angF_le hα hα1 a hpos ha4 hθ
              have h80 : 80 * Work.FTS.Nonlinear.Pieces.RNPV2.TBound * α
                  ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α :=
                mul_le_mul_of_nonneg_right
                  Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_80 hα.le
              linarith
          have hR0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := mul_nonneg hCa0 hα.le
          calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l
                    * Work.Spaces.pzIter l
                        (Work.Spaces.DthIter (i - a)
                          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
              ≤ (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α)
                  * (200000 * (WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) :=
                mul_le_mul hD hR (abs_nonneg _) hR0
            _ = 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                  * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
        · -- `a = i`: the radial estimate for the radial factor
          have hia : i - a = 0 := by omega
          rw [hia, Work.Spaces.DthIter_zero]
          have ha1 : 1 ≤ a := by omega
          have ha4 : a ≤ 4 := by omega
          have hR := hrad l hl4 z hz θ hθ
          have hD := Work.FTS.Nonlinear.Pieces.RNPV2.dthU_angF_weight_le hα hα1 a ha1 ha4 hθ
          have hD' : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ := by
            have h40 : 40 * α * Work.FTS.Nonlinear.Pieces.RNPV2.TBound
                ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := by
              have h := mul_le_mul_of_nonneg_right
                Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40TB hα.le
              linarith
            calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                ≤ 40 * α * Work.FTS.Nonlinear.Pieces.RNPV2.TBound
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ := hD
              _ ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
                  mul_le_mul_of_nonneg_right h40 hΦ0
          have hR0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
            mul_nonneg (mul_nonneg hCa0 hα.le) hΦ0
          calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l
                    * Work.Spaces.pzIter l
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
              ≤ (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) * (200000 * WA) :=
                mul_le_mul hD' hR (abs_nonneg _) hR0
            _ = 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                  * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
      -- assemble
      have hρ2 : |(1 + z) * Work.Spaces.w z * z ^ l
            * Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          = ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ| := by
        rw [abs_mul, abs_of_nonneg hρ]
      rw [hρ2]
      have hnn : 0 ≤ 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
          * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (mul_nonneg hCa0 hα.le) hWA0) hΦ0)
      have hi5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
        have : i + 1 ≤ 5 := by omega
        exact_mod_cast this
      have hstep1 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) :=
        mul_le_mul_of_nonneg_left hsum hρ
      have hstep2 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|))
          = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := by
        have h1 : ((1 + z) * Work.Spaces.w z * z ^ l)
              * (257 * (∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                  * |Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|))
            = 257 * (((1 + z) * Work.Spaces.w z * z ^ l) * (∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                  * |Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) := by
          ring
        rw [h1, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun a ha => by ring)
      have hstep3 : 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l))
          ≤ 257 * (∑ _a ∈ Finset.range (i + 1),
              200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      have hstep4 : 257 * (∑ _a ∈ Finset.range (i + 1),
            200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))
          = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hstep5 : 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)))
          ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
        rw [hWdef]
        calc 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
                * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)))
            = (257 * ((i + 1 : ℕ) : ℝ)) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
                * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by ring
          _ ≤ (257 * 5) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_left hi5 (by norm_num)
          _ ≤ 10 ^ 6 * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              norm_num
          _ = 200000 * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA)
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
      calc ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) := hstep1
        _ = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := hstep2
        _ ≤ 257 * (∑ _a ∈ Finset.range (i + 1),
              200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := hstep3
        _ = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))) := hstep4
        _ ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := hstep5
    -- the transfer: `ℋ⁴`-honesty and the norm bound
    have hmain := hwto α (Work.FTS.Nonlin.N1ss α Φs) W hα hα1 hW0 hSmoothN1ss hboundA hboundB
    -- the final arithmetic
    have hWle : W ≤ 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * (max Cs 0 * α)) := by
      rw [hWdef]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWAle hα.le)
        (mul_nonneg (by norm_num) hCa0)
    have hstepC : Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0
        ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) := by
      have hCwCa : 0 ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) :=
        mul_nonneg hCw.le (mul_nonneg (by norm_num) hCa0)
      have hmax : max Cs 0 ≤ 1 + |Cs| := by
        have h1 : max Cs 0 ≤ |Cs| := max_le (le_abs_self Cs) (abs_nonneg Cs)
        linarith
      have habs1 : 0 ≤ 1 + |Cs| := by positivity
      calc Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0
          ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * (1 + |Cs|) :=
            mul_le_mul_of_nonneg_left hmax hCwCa
        _ ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) :=
            mul_le_mul_of_nonneg_right (by linarith) habs1
    refine ⟨hmain.1, ?_⟩
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ Cw * W := hmain.2
      _ ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * (max Cs 0 * α))) :=
          mul_le_mul_of_nonneg_left hWle hCw.le
      _ = (Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0) * α ^ 2 := by ring
      _ ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) * α ^ 2 :=
          mul_le_mul_of_nonneg_right hstepC (sq_nonneg α)

end Work.FTS.StrongPersist.L3Rhs
