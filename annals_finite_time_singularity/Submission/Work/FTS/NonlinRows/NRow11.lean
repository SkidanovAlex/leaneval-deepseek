import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise
import Submission.Work.FTS.Nonlinear.Pieces.RNPV2.row11
import Submission.Work.FTS.NonlinRows.WtoH_Radial_O
import Submission.Work.FTS.NonlinRows.WtoH_Mixed_O
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## Row 11 with the `𝒲`-decay of the star coefficient restored

The statement `NRow11` of this file is **not derivable from its hypotheses as frozen**: its
`HkMem α 4 (N1ss α Φs)` conjunct is a weighted-decay statement, and the primed package
`Work.FTS.VocabO.StarPkgo` supplies only *flat* open-quadrant suprema
(`WDMem 4 (((z+1)/z)·ℛ(Φ̃_*))`, `WDp 4 (…) ≤ Cs·α`), which by the proved
`Work.FTS.OpenPkg.WDMem_of_WDp_le` give only `|∂_z^b D_θ^j Rv| ≤ Cs·α` — no control of
`z^b ∂_z^b D_θ^j Rv`, which is exactly what the `ℋ⁴`-integrand of `N1ss` needs.  The frozen
*unprimed* `StarPkg.R` carries that information as a `WlInfMem`/`WlInf` field, and the unprimed
row 11 (`Work.FTS.Nonlinear.Pieces.RNPV2.row11`, verified `sorry`-free) is proved from it.

See `NOTES_NRow11.md` for the full diagnosis.  The lemma below is the same row *with that field
restored as an explicit hypothesis*; it is the statement the lead obtains by adding the
`WlInf`-form of `StarPkg.R` (resp. of `dU`, `V` for rows 14/15/18/19) to `StarPkgo`, and it is
proved by running the unprimed proof in the primed (open-quadrant) class, using the
open-quadrant ports `WtoH_Radial_O`, `WtoH_Mixed_O`, `sqm_pz_DthIter_mul_le_4_open`,
`smoothOpen_radA` and `wtoHQ_of_pointwise_open`. -/
theorem NRow11_of_wlInf (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.WlInfMem α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) →
      Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) ≤ Cs * α →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := wtoHQ_of_pointwise_open
  refine ⟨1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0, ?_, ?_⟩
  · have h1 : 0 ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0 :=
      mul_nonneg (mul_nonneg hCw.le
          (mul_nonneg (by norm_num) (le_of_lt Work.FTS.Nonlinear.Pieces.RNPV2.Ca_pos)))
        (le_max_right _ _)
    linarith
  · intro α g Φs Φg hctx hW hWb
    obtain ⟨hα, hα1, hαα₂, hgal, hs, hell⟩ := hctx
    have hCa0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca :=
      le_of_lt Work.FTS.Nonlinear.Pieces.RNPV2.Ca_pos
    set WA : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) with hWA
    have hWA0 : 0 ≤ WA := by
      rw [hWA]
      exact Work.FTS.H2.sqm_WlInf_nonneg α 4 _ hW
    have hWAle : WA ≤ max Cs 0 * α := by
      rw [hWA]
      exact hWb.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    -- the smoothness of the radial factor and the weighted identity
    have hid := (smoothOpen_radA hα hα1 hs).2
    have hSOrad : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) := (smoothOpen_radA hα hα1 hs).1
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
      have h := WtoH_Radial_O hα hα1 hSOrad hmemG m hm z hz θ hθ
      rwa [hWAeq] at h
    have hmix : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
          ≤ 200000 * (WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have h := WtoH_Mixed_O hα hα1 hSOrad hmemG i l hi hli z hz θ hθ
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
      have hleib := sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
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
    refine ⟨hmain.1, ?_⟩
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ Cw * W := hmain.2
      _ ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * (max Cs 0 * α))) :=
          mul_le_mul_of_nonneg_left hWle hCw.le
      _ = (Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0) * α ^ 2 := by ring
      _ ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0) * α ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg α)
          linarith

/- **RETIRED.**  The row-11 statement under the *frozen* `Work.FTS.NonlinRows.Ctx`
(`VocabO.StarPkgo`) is not derivable: its `HkMem α 4 (N1ss α Φs)` conjunct needs
`(1+z)^b ∂_z^b D_θ^j ((z+1)/z·ℛ(Φ̃_*)) = O(1)` for `b + j ≤ 4`, which the flat `WDMem`/`WDp`
pricing of the star coefficient cannot supply (see `NOTES_NRow11.md`; the machine-checked argument
is in the docstring of `NRow11_of_wlInf` above).  The **true** form is
`Work.FTS.NonlinRows.NRow11T2` in `Submission/Work/FTS/NonlinRows/NRow11T2.lean`, proved against
the upgraded `Work.FTS.VocabO2.Ctx2` whose `StarPkgo2.RW` is exactly the missing `𝒲^{4,∞}` field. -/

end Work.FTS.NonlinRows
