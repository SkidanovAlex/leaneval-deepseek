/-
# Row 25 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlinear.Open.Row25`: the `ℋ⁴`-honesty together with the `√α`-bound of the two pieces

  `N₅^{gs} = -sin²θ·FK(g)·F_*`,        `N₅^{sg} = -sin²θ·FK(F_*)·g`,

in the primed context `N4Norm'`/`N4Extra'` with the open-quadrant packages `StarPkgo`/`EllPkgGo`.

## Route

Write `FM.Fstar z = 2z/(1+z)² = 2·hKer z`, `F_* z θ = α(Γ(θ)/c)·FM.Fstar z` and
`FK(F_*) z = α·FM.Fstar z` (`FstarPkg.FK_Fstar`), so that

* `N₅^{sg} = -2α·(sin²θ · (hKer·g))`, a *radial* `𝒲^{4,∞}`-coefficient `2α·hKer` times `g`
  composed with the angular factor `sin²θ`;
* `N₅^{gs} = -(α/c)·(aG·(FM.Fstar·FK g))` with the angular profile `aG = sin²θ·Γ(α)`.

**`N₅^{sg}`.**  `hKer·g ∈ ℋ⁴` with `|hKer·g| ≤ Ci·α^{-1/2}·200·|g|` by the primed `wprod` clause
(`WlInfMem α 4 hKer` from `hKerConstWlInf`, `WlInf α 4 hKer ≤ 200`), and the angular factor is
handled by the primed `angmul` clause applied to the rescaled profile
`asq θ = ε·(-sin²θ)`, `ε = Ci/(2·192)`, which satisfies the two hypotheses `|asq| ≤ Ci` and
`|D_θ^i asq| ≤ Ci·sin(2θ)` (from `angProfile_sinSq`).  The constant of the clause is `Ci²`, and
the rescaling `1/ε = 2·192/Ci` together with `α·α^{-1/2} = √α` produces exactly the stated `√α`.

**`N₅^{gs}`.**  This is the row proved in the un-primed vocabulary
(`Pieces/RNP/row25.lean`), whose proof uses only the primed-independent lemmas
`fkH`, `Rr_le_HkSq`, `Rint_mul_le`, `HkIntegrand_ang_rad_sin_le`, `HkSq_ang_rad_of_le` and the
`𝒲^{4,∞}`-bound of `FM.Fstar`; the only adaptation needed is that the primed `fkH` clause takes
`HQo α 4 g` (`= SmoothOpen g ∧ HkMem α 4 g`, both from `GalClass α g`) instead of `RegQ α 4 g`.
The `ℋ⁴`-honesty conjunct is the same pointwise computation fed into `HkMem_ang_rad`
(angular × radial products), with the angular majorant `G θ = sin(2θ)^{α/5}` of
`dthSinSqGam_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.smoothOpen_FK_radial
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.Nonlinear.Open.Row25Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## Small `SmoothOpen` helpers on the open quadrant -/

/-- **Row 25** of the honest chapter: `HkMem` of `N5gs`, `N5sg` and the `√α X` bound on their sum. -/
theorem Row25 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gs α g) ∧ Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5sg α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g) + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCipos, hα₂pos⟩ := hN.pos
  obtain ⟨Bdth, hBdthpos, hdth⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthSinSqGam_le
  obtain ⟨Bsin, hBsinpos, hSinSmooth, hSinLe, hSinDth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  refine ⟨10 ^ 26 * (1 + Bdth) * (Ci + 1) + (800 * Bsin * Ci ^ 2 + 1) + 1,
    by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have hsmOpen_g : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hsm
  have hqo4 : Work.FTS.VocabO.HQo α 4 g := ⟨hsmOpen_g, hmem4⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  obtain ⟨hFkmem, hFkle⟩ := hN.fkH α hIoc g hqo4 hgal.l12
  have hSqrtPos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hAlphaSqrt : α / Real.sqrt α = Real.sqrt α := by
    rw [div_eq_iff (ne_of_gt hSqrtPos)]
    simpa [pow_two] using (Real.sq_sqrt hα.le).symm
  -- ## The angular moment is an `ℋ⁴`-function of controlled norm
  have hRintint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g)) Work.Spaces.Iz :=
    Work.FTS.Nonlinear.RadialProd.integrable_Rint α (Work.Construction.FK g) hFkmem
  have hRr_le : (∫ z in Work.Spaces.Iz,
        Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g) z)
      ≤ (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h2 : (∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint
        (Work.Construction.FK g) z)
        ≤ Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK g z) :=
      Work.FTS.Nonlinear.RadialProd.Rr_le_HkSq α (Work.Construction.FK g)
    have h3 : Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK g z)
        = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
    rw [h3] at h2
    exact h2.trans (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hFkle 2)
  have hRint_le : ∀ z ∈ Work.Spaces.Iz,
      Work.FTS.Nonlinear.RadialProd.Rint (fun z => Work.FM.Fstar z * Work.Construction.FK g z) z
        ≤ (6400 * 200000 ^ 2)
          * Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g) z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      simp [Work.FTS.Nonlinear.RadialProd.Rint, Work.Spaces.w]
    · exact Work.FTS.Nonlinear.Pieces.Rint_mul_le Work.FM.Fstar (Work.Construction.FK g)
        (by norm_num)
        (fun k hk z hz' =>
          Work.FTS.Nonlinear.Pieces.dzdIter_Fstar_bound k (by omega) z (le_of_lt hz'))
        (fun b hb z hz' => Work.FTS.Nonlinear.Pieces.differentiableAt_dzdIter_Fstar b hz')
        (fun b hb z hz' => Work.FTS.Nonlinear.Pieces.RNP.fk_dzdIter_diff
          hα hα1 hsm hmem6 b hb z hz') hzpos
  -- ## The angular profile
  set aG : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ with haG
  have haG0 : ∀ θ ∈ Work.Spaces.Iθ, |aG θ| ≤ 1 := by
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have h1 : Real.sin θ ^ 2 ≤ 1 := by
      calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one θ) 2
        _ = 1 := by norm_num
    rw [haG, abs_of_nonneg (mul_nonneg (sq_nonneg _) hG.1)]
    calc Real.sin θ ^ 2 * Work.Spaces.Gam α θ ≤ 1 * 1 :=
          mul_le_mul h1 hG.2 hG.1 (by norm_num)
      _ = 1 := by norm_num
  have haG1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => aG θ') 0 θ|
        ≤ Bdth * (Real.sin (2 * θ)) ^ (α / 5) := by
    intro i hi1 hi4 θ hθ
    simpa only [haG] using hdth α hα hα1 i hi1 hi4 θ hθ
  -- ## The pointwise integrand bound
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 4
          (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z)) z θ
        ≤ (6400 * 200000 ^ 2) * Work.FTS.Nonlinear.RadialProd.Rint
            (Work.Construction.FK g) z
          * (1 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * Bdth ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    intro z hz θ hθ
    have h1 := Work.FTS.Nonlinear.Pieces.HkIntegrand_ang_rad_sin_le α aG
      (fun z => Work.FM.Fstar z * Work.Construction.FK g z)
      (B0 := 1) (B1 := Bdth) (κ := α / 5) (by norm_num) hBdthpos.le haG0 haG1 (z := z) hθ
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_right (hRint_le z hz) ?_
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsmE : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
      Work.FTS.Nonlinear.RadialProd.smE_nonneg hθI
    have hs : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    have hr : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) :=
      Real.rpow_nonneg hs _
    positivity
  -- ## The angular exponents
  have hexp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hexp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      Work.Spaces.Iθ := (Work.Spaces.sin_two_rpow _ hexp1 hexp2).1
  have hm1 : ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) ≤ 1000 / (3 * α) := by
    have h := (Work.Spaces.sin_two_rpow _ hexp1 hexp2).2
    have hden : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    have h2 : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
      field_simp
      ring
    linarith [h, le_of_eq h2]
  have hsq := Work.FTS.Nonlinear.Pieces.HkSq_ang_rad_of_le α hα aG
    (fun z θ => Work.FM.Fstar z * Work.Construction.FK g z) (Work.Construction.FK g)
    (B0 := 1) (B1 := Bdth) (κ := α / 5) (M1 := 1000 / (3 * α)) (C := 6400 * 200000 ^ 2)
    (by norm_num) hBdthpos.le (by positivity) (by norm_num) hpt hI1 hm1 hRintint
  -- ## The `N₅^{gs}` estimate
  have hXar : Work.FTS.Nonlin.Xn α
      (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
      ≤ (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth))
          * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α) := by
    set D : ℝ := 10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth) with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hsqb : Work.Spaces.HkSq α 4
        (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
        ≤ (D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2 := by
      have hCpos : (0 : ℝ) < 6400 * 200000 ^ 2 := by norm_num
      have hstep : Work.Spaces.HkSq α 4
          (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
          ≤ (6400 * 200000 ^ 2) * (1 ^ 2 * 10000
              + 4 * Bdth ^ 2 * (1000 / (3 * α))) * ((Ci * Work.FTS.Nonlin.Xn α g) ^ 2) := by
        refine hsq.trans ?_
        exact mul_le_mul_of_nonneg_left hRr_le (by positivity)
      refine hstep.trans ?_
      have hfac : (D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2
          = D ^ 2 * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 / α := by
        rw [mul_pow, div_pow, Real.sq_sqrt hα.le]
        ring
      rw [hfac, hD]
      have hkey : 1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α))
          ≤ (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2 / α
            / (6400 * 200000 ^ 2) := by
        have hcore : 10 ^ 4 * α + 4000 * Bdth ^ 2 / 3
            ≤ 10 ^ 18 * (6400 * 200000 ^ 2) * (1 + Bdth) ^ 2 := by
          have h1 : Bdth ^ 2 ≤ (1 + Bdth) ^ 2 := by nlinarith [hBdthpos.le]
          have h2 : (1 : ℝ) ≤ (1 + Bdth) ^ 2 := by nlinarith [hBdthpos.le]
          nlinarith [h1, h2, hBdthpos.le, hα1, hα]
        rw [le_div_iff₀ hCpos, le_div_iff₀ hα]
        have he : (1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α)))
              * (6400 * 200000 ^ 2) * α
            = (6400 * 200000 ^ 2) * (10 ^ 4 * α + 4000 * Bdth ^ 2 / 3) := by
          field_simp
          try ring
        rw [he]
        have he2 : (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2
            = (6400 * 200000 ^ 2)
              * (10 ^ 18 * (6400 * 200000 ^ 2) * (1 + Bdth) ^ 2) := by
          ring
        rw [he2]
        exact mul_le_mul_of_nonneg_left hcore (by norm_num)
      calc (6400 * 200000 ^ 2) * (1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α)))
            * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2
          ≤ (6400 * 200000 ^ 2)
              * ((10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2 / α
                / (6400 * 200000 ^ 2)) * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hCpos.le) (by positivity)
        _ = (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2
              * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 / α := by
            field_simp
            try ring
    calc Work.FTS.Nonlin.Xn α (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
        = Real.sqrt (Work.Spaces.HkSq α 4
            (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))) := rfl
      _ ≤ Real.sqrt ((D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2) :=
          Real.sqrt_le_sqrt hsqb
      _ = D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α) :=
          Real.sqrt_sq (by positivity)
  have hgs_eq : Work.FTS.Nonlin.N5gs α g = fun z θ =>
      -(α / Work.Spaces.c α) * (aG θ * (Work.FM.Fstar z * Work.Construction.FK g z)) := by
    funext z θ
    rw [Work.FTS.Nonlin.N5gs, Work.Construction.Fstar, haG, Work.FM.Fstar]
    field_simp
    try ring
  have hA : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
      ≤ 10 ^ 26 * (1 + Bdth) * (Ci + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [hgs_eq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
    have hAc : |-(α / Work.Spaces.c α)| ≤ 10 * α := by
      rw [abs_neg, abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
      nlinarith [hc1, hα]
    refine (mul_le_mul hAc hXar (Work.Spaces.HkNorm_nonneg α 4 _) (by positivity)).trans ?_
    have hstep : (10 * α) * ((10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth))
          * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α))
        = (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci
            * (α / Real.sqrt α)) * Work.FTS.Nonlin.Xn α g := by ring
    rw [hstep, hAlphaSqrt]
    have hcoef : 10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci
        ≤ 10 ^ 26 * (1 + Bdth) * (Ci + 1) := by
      nlinarith [hBdthpos.le, hCipos]
    calc (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci * Real.sqrt α)
          * Work.FTS.Nonlin.Xn α g
        = (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (10 ^ 26 * (1 + Bdth) * (Ci + 1))
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- ## The `ℋ⁴`-honesty of `N₅^{gs}`
  have hsmF : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.FM.Fstar z) :=
    Work.FTS.NonlinRows.smoothOpen_radial row25_contDiffOn_Fstar
  have hsmhk : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Spaces.hKer z) :=
    Work.FTS.NonlinRows.smoothOpen_radial row25_contDiffOn_hKer
  have hsmFK : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.Nonlinear.Open.smoothOpen_FK_radial hα hα1 hsm hmem4 hgal.l12 hell.smooth hell.V.1.1
  have hWlF : Work.Spaces.WlInfMem α 4 (fun z _ => Work.FM.Fstar z) := by
    have h := (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 2).1
    have hfun : (fun z (_ : ℝ) => (2 : ℝ) * Work.Spaces.hKer z) = fun z _ => Work.FM.Fstar z := by
      funext z θ
      rw [Work.Spaces.hKer_apply, Work.FM.Fstar]
      ring
    rwa [hfun] at h
  have hWleF : Work.Spaces.WlInf α 4 (fun z _ => Work.FM.Fstar z) ≤ 400 := by
    have h := (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 2).2
    have hfun : (fun z (_ : ℝ) => (2 : ℝ) * Work.Spaces.hKer z) = fun z _ => Work.FM.Fstar z := by
      funext z θ
      rw [Work.Spaces.hKer_apply, Work.FM.Fstar]
      ring
    rw [hfun] at h
    norm_num at h
    exact h
  have hqoFK : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK g z) :=
    ⟨hsmFK, hFkmem⟩
  have hwprod := hN.wprod α hIoc (fun z _ => Work.FM.Fstar z)
    (fun z _ => Work.Construction.FK g z) hsmF hWlF hqoFK
  have hradmem : Work.Spaces.HkMem α 4
      (fun z (_ : ℝ) => Work.FM.Fstar z * Work.Construction.FK g z) := hwprod.1
  have hsmrad : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.FM.Fstar z * Work.Construction.FK g z) :=
    row25_smoothOpen_rad_mul hsmF hsmFK
  have haGsmooth : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => aG θ) := by
    have h := row25_smoothOpen_ang_mul
      (a := fun θ => Real.sin θ ^ 2) (b := fun θ => Work.Spaces.Gam α θ)
      (by
        refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
        have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2)
            = fun p : ℝ × ℝ => (Real.sin p.2) ^ 2 := rfl
        rw [hfun]
        exact ((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn.of_le le_top)
      (row25_smoothOpen_Gam α)
    have hfun : (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)
        = fun (_ : ℝ) (θ : ℝ) => aG θ := by
      funext z θ
      rw [haG]
    rwa [hfun] at h
  have hmemA : Work.Spaces.HkMem α 4
      (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z)) :=
    Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad
      (a := aG) (r := fun z => Work.FM.Fstar z * Work.Construction.FK g z)
      (G := fun θ => (Real.sin (2 * θ)) ^ (α / 5)) (B0 := 1) (B1 := Bdth)
      haGsmooth hsmrad
      (fun θ hθ => Real.rpow_nonneg
        (Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ) _)
      (row25_G_sq_smG_integrable hα hα1) haG0 haG1 hradmem
  have hmemN5gs : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gs α g) := by
    rw [hgs_eq]
    exact Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of (-(α / Work.Spaces.c α)) hmemA
  -- ## The `N₅^{sg}` estimate
  set lam : ℝ := Ci / (2 * Bsin) with hlam
  have hlam_pos : 0 < lam := by rw [hlam]; positivity
  set asq : ℝ → ℝ := fun θ => lam * (-((Real.sin θ) ^ 2)) with hasq
  have hasq_smooth : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => asq θ) := by
    have h := row25_smoothOpen_ang_mul (a := fun _ => lam)
      (b := fun θ => -((Real.sin θ) ^ 2)) (row25_smoothOpen_ang_const lam)
      row25_smoothOpen_neg_sinSq
    have hfun : (fun (_ : ℝ) (θ : ℝ) => lam * -((Real.sin θ) ^ 2))
        = fun (_ : ℝ) (θ : ℝ) => asq θ := by
      funext z θ
      rw [hasq]
    rwa [hfun] at h
  have hasq0 : ∀ θ ∈ Work.Spaces.Iθ, |asq θ| ≤ Ci := by
    intro θ hθ
    have h2 : |(-((Real.sin θ) ^ 2))| ≤ Bsin := by
      simpa using hSinLe θ hθ
    have h3 : lam * Bsin = Ci / 2 := by rw [hlam]; field_simp
    rw [hasq, abs_mul, abs_of_nonneg hlam_pos.le]
    calc lam * |(-((Real.sin θ) ^ 2))| ≤ lam * Bsin :=
          mul_le_mul_of_nonneg_left h2 hlam_pos.le
      _ = Ci / 2 := h3
      _ ≤ Ci := by linarith [hCipos]
  have hasq1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => asq θ') 0 θ| ≤ Ci * Real.sin (2 * θ) := by
    intro i hi1 hi4 θ hθ
    have h1 : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => asq θ')
        = fun z (θ' : ℝ) => lam * (Work.Spaces.DthIter i
            (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) z θ') := by
      rw [hasq]
      exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul i lam
        (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2))
    rw [h1, abs_mul, abs_of_nonneg hlam_pos.le]
    have h2 := hSinDth i hi1 hi4 θ hθ
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    calc lam * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) 0 θ|
        ≤ lam * (Bsin * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left h2 hlam_pos.le
      _ = Ci / 2 * Real.sin (2 * θ) := by rw [hlam]; field_simp; try ring
      _ ≤ Ci * Real.sin (2 * θ) := by nlinarith [hCipos, hsnn]
  have hSmem : Work.Spaces.WlInfMem α 4 (fun z _ => Work.Spaces.hKer z) := by
    have h := (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 1).1
    have hfun : (fun z (_ : ℝ) => (1 : ℝ) * Work.Spaces.hKer z)
        = fun z _ => Work.Spaces.hKer z := by
      funext z θ; ring
    rwa [hfun] at h
  have hSle : Work.Spaces.WlInf α 4 (fun z _ => Work.Spaces.hKer z) ≤ 200 := by
    have h := (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 1).2
    have hfun : (fun z (_ : ℝ) => (1 : ℝ) * Work.Spaces.hKer z)
        = fun z _ => Work.Spaces.hKer z := by
      funext z θ; ring
    rw [hfun] at h
    simpa using h
  have hwprodHK := hN.wprod α hIoc (fun z _ => Work.Spaces.hKer z) g hsmhk hSmem hqo4
  have hsmkg : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.hKer z * g z θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => by
      have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => Work.Spaces.hKer z)).mp
        hsmhk n
      have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hsmOpen_g n
      have hfun : Function.uncurry (fun (z : ℝ) (θ : ℝ) => Work.Spaces.hKer z * g z θ)
          = fun p : ℝ × ℝ => Work.Spaces.hKer p.1 * g p.1 p.2 := rfl
      rw [hfun]
      exact h1.mul h2)
  have ham := hN.angmul α hIoc asq (fun z θ => Work.Spaces.hKer z * g z θ)
    hasq_smooth hasq0 hasq1 hsmkg hwprodHK.1
  have hsg_eq : Work.FTS.Nonlin.N5sg α g
      = fun z θ => (2 * α / lam) * (asq θ * (Work.Spaces.hKer z * g z θ)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.FK_Fstar hα hα1, asq, hasq, lam,
      Work.Spaces.hKer_apply]
    field_simp
    try ring
  have hmemN5sg : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5sg α g) := by
    rw [hsg_eq]
    exact Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of (2 * α / lam) ham.1
  have hB : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
      ≤ 800 * Bsin * Ci ^ 2 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [hsg_eq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
    have hc : |2 * α / lam| = 2 * α / lam := abs_of_pos (by positivity)
    rw [hc]
    -- the chain of interface bounds, all with nonnegative multiplicative factors
    have hs3 : Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (fun z _ => Work.Spaces.hKer z)
          * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * 200 * Work.FTS.Nonlin.Xn α g := by
      have hfac : Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (fun z _ => Work.Spaces.hKer z)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * 200 :=
        mul_le_mul_of_nonneg_left hSle
          (by positivity : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)))
      exact mul_le_mul_of_nonneg_right hfac hX0
    have hs2 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.hKer z * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * 200 * Work.FTS.Nonlin.Xn α g :=
      hwprodHK.2.trans hs3
    have hs1 : Work.FTS.Nonlin.Xn α (fun z θ => asq θ * (Work.Spaces.hKer z * g z θ))
        ≤ Ci * Ci * (Ci * α ^ (-(1 / 2 : ℝ)) * 200 * Work.FTS.Nonlin.Xn α g) :=
      ham.2.trans (mul_le_mul_of_nonneg_left hs2 (by positivity))
    have hs0 : (2 * α / lam)
          * Work.FTS.Nonlin.Xn α (fun z θ => asq θ * (Work.Spaces.hKer z * g z θ))
        ≤ (2 * α / lam)
          * (Ci * Ci * (Ci * α ^ (-(1 / 2 : ℝ)) * 200 * Work.FTS.Nonlin.Xn α g)) :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    refine hs0.trans ?_
    refine le_of_eq ?_
    have hpow : α * α ^ (-(1 / 2 : ℝ)) = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
      rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
      exact h.symm
    rw [hlam]
    calc (2 * α / (Ci / (2 * Bsin)))
          * (Ci * Ci * (Ci * α ^ (-(1 / 2 : ℝ)) * 200 * Work.FTS.Nonlin.Xn α g))
        = (800 * Bsin * Ci ^ 2) * (α * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) := by
          have hCi' : Ci ≠ 0 := ne_of_gt hCipos
          have hB' : Bsin ≠ 0 := ne_of_gt hBsinpos
          field_simp
          ring
      _ = 800 * Bsin * Ci ^ 2 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by rw [hpow]
  -- ## Assembly
  refine ⟨hmemN5gs, hmemN5sg, ?_⟩
  have h1 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
        + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
      ≤ (10 ^ 26 * (1 + Bdth) * (Ci + 1) + 800 * Bsin * Ci ^ 2)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    have h := add_le_add hA hB
    rw [← add_mul] at h
    exact h
  have hnn : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := by positivity
  have h2 : (10 ^ 26 * (1 + Bdth) * (Ci + 1) + 800 * Bsin * Ci ^ 2)
        * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
      ≤ (10 ^ 26 * (1 + Bdth) * (Ci + 1) + (800 * Bsin * Ci ^ 2 + 1) + 1)
        * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    refine mul_le_mul_of_nonneg_right ?_ hnn
    linarith
  linarith [h1, h2]


end Work.FTS.Nonlinear.Open
