/-
# `E4R3/N4C/rows/rowsN5b` — rows 25 and 26 of the honest §8 table

The target `Work.FTS.StrongEps.E4R3.N4C.rows.rowsN5b` proves, from the two interfaces
(`hN : OpenPkg.N4Norm' Ci α₂`, `hE : N4C.N4ExtraH IP α₂ Ct`) and for every honest row context
`CtxT Cs Ce α₂ α g Φs Φg`, the two `N₅`-rows which involve the fundamental model `F_*`:

* row 25: `Xn α (N₅^{gs}) + Xn α (N₅^{sg}) ≤ K·√α·Xn α g`, where
  `N₅^{gs} = -sin²θ·FK(g)·F_*` and `N₅^{sg} = -sin²θ·FK(F_*)·g`;
* row 26: `Xn α (N₅^{ss}) ≤ K·α²`, where `N₅^{ss} = -sin²θ·FK(F_*)·F_*`.

These are the honest (class-`C`) counterparts of `Work.FTS.Nonlinear.Open.Row25` /
`Open.Row26`, whose *frozen* statements carry `GalClass α g` (with `SmoothQuad`) and the frozen
interface `OpenPkg.N4Extra'`.  The differences are:

* the first-argument hypotheses of the `N4Norm'` clauses are the honest class
  `HQo α 4 = SmoothOpen ∧ HkMem α 4` (supplied by `CtxT.hqo4`), and the `L₁₂`-zero hypothesis of
  `fkH` is `CtxT.hL12`;
* the *only* place where the frozen proof genuinely uses `SmoothQuad g` is the differentiability
  of the `D_z`-iterates of the angular moment `FK g`, needed as the `hrdiff` argument of
  `Pieces.Rint_mul_le`.  In the honest class `ClassC α g` supplies exactly the missing input in
  the field `fsm : ∀ m, ContDiffOn ℝ m (Elliptic.Fstar g) (Ioi 0)` (the `z`-smoothness of the
  radial moment), and `Construction.FK g = 3·Elliptic.Fstar g`; the helper `dzdIter_FK_diff_of`
  below converts that into the required differentiability (`contDiffOn_dzdIter_of`).
* the `ℋ⁴`-honesty conjuncts of the frozen rows are *not* part of the target, so the whole
  `HkMem`-half of the frozen `Row25` (the angular × radial product argument) is skipped.

Row 26 is independent of `g, Φs, Φg` and of both interfaces; it is the priced estimate
`StrongPersist.L3Rhs.N5ssPriced`.

Everything below is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.Nonlinear.Open.Row25
import Submission.Work.FTS.StrongPersist.L3Rhs.N5ssPriced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The angular moment `FK g` in the honest class

`Construction.FK F z = ∫_θ F z θ · K(θ) dθ` with `K = 3 sinθ cos²θ`, while
`Elliptic.Fstar F z = ∫_θ F z θ · sinθ cos²θ dθ`; the two differ by the factor `3`.  The
`ClassC`-field `fsm` is stated for `Elliptic.Fstar`, so the identity is all that is needed to
transfer its `z`-smoothness to `FK`. -/

/-- `Construction.FK F = 3 · Elliptic.Fstar F`, pointwise in `z`. -/
theorem FK_eq_three_Fstar (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.FK F z = 3 * Work.Elliptic.Fstar F z := by
  have h1 : Work.Construction.FK F z
      = ∫ θ in Work.Spaces.Iθ, 3 * (F z θ * Work.Elliptic.sinCos2 θ) := by
    rw [Work.Construction.FK]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Spaces.K, Work.Elliptic.sinCos2]
    ring
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * (F z θ * Work.Elliptic.sinCos2 θ))
      = 3 * ∫ θ in Work.Spaces.Iθ, F z θ * Work.Elliptic.sinCos2 θ := by
    rw [MeasureTheory.integral_const_mul]
  rw [h1, h2]
  simp only [Work.Elliptic.Fstar]

/-- **The radial moment of a `ClassC`-profile is `C⁴` on `(0,∞)`.** -/
theorem contDiffOn_FK_of_classC {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) :
    ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0 : ℝ)) := by
  have h4 : ContDiffOn ℝ 4 (fun z => Work.Elliptic.Fstar g z) (Set.Ioi (0 : ℝ)) := h.fsm 4
  have h3 : ContDiffOn ℝ 4 (fun z => 3 * Work.Elliptic.Fstar g z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul h4
  refine h3.congr (fun z _ => ?_)
  exact FK_eq_three_Fstar g z

/-- **Differentiability of the `D_z`-iterates of `FK g` from the `C⁴`-regularity of the
radial moment alone.**  This is `Pieces.RNP.fk_dzdIter_diff` with its `SmoothQuad`/`HkMem`
hypotheses replaced by the conclusion of `contDiffOn_dzdIter_of` on `FK g`. -/
theorem dzdIter_FK_diff_of {g : Fn}
    (h4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0 : ℝ))) :
    ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Construction.FK g)) z := by
  intro b hb z hz
  have hC : ContDiffOn ℝ (4 - b) (Work.Elliptic.DzdIter b (Work.Construction.FK g))
      (Set.Ioi 0) :=
    Work.FTS.Nonlinear.Pieces.RNP.contDiffOn_dzdIter_of h4 b (le_trans hb (by norm_num))
  have hne : ((4 - b : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have hpos : 0 < 4 - b := by omega
    exact_mod_cast (ne_of_gt hpos)
  exact (hC.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-! ## Row 25a: the piece `N₅^{gs} = -sin²θ·FK(g)·F_*` -/

/-- **Row 25a of the honest §8 table**: for every honest context,

  `Xn α (N₅^{gs}) ≤ K·√α·Xn α g`.

Constant `K = 10²⁶(1+B_dθ)(Ci+1)`, with `B_dθ` the constant of `RNP.dthSinSqGam_le`. -/
theorem rowN5gsHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCipos, -⟩ := hN.pos
  obtain ⟨Bdth, hBdthpos, hdth⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthSinSqGam_le
  refine ⟨10 ^ 26 * (1 + Bdth) * (Ci + 1), by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  obtain ⟨hFkmem, hFkle⟩ := hN.fkH α hIoc g hctx.hqo4 hctx.hL12
  have hSqrtPos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hAlphaSqrt : α / Real.sqrt α = Real.sqrt α := by
    rw [div_eq_iff (ne_of_gt hSqrtPos)]
    simpa [pow_two] using (Real.sq_sqrt hα.le).symm
  -- ## The angular moment is an `ℋ⁴`-function of controlled norm
  have hFK4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_FK_of_classC hctx.hg
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
        (fun b hb z hz' => dzdIter_FK_diff_of hFK4 b hb z hz') hzpos
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
  exact hA

/-! ## Row 25b: the piece `N₅^{sg} = -sin²θ·FK(F_*)·g` -/

/-- **Row 25b of the honest §8 table**: for every honest context,

  `Xn α (N₅^{sg}) ≤ K·√α·Xn α g`.

Constant `K = 800·B_sin·Ci²`, with `B_sin` the constant of `RNP24.angProfile_sinSq`. -/
theorem rowN5sgHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCipos, -⟩ := hN.pos
  obtain ⟨Bsin, hBsinpos, _hSinSmooth, hSinLe, hSinDth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  refine ⟨800 * Bsin * Ci ^ 2, by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hqo4 : Work.FTS.VocabO.HQo α 4 g := hctx.hqo4
  -- ## The `N₅^{sg}` estimate
  set lam : ℝ := Ci / (2 * Bsin) with hlam
  have hlam_pos : 0 < lam := by rw [hlam]; positivity
  set asq : ℝ → ℝ := fun θ => lam * (-((Real.sin θ) ^ 2)) with hasq
  have hasq_smooth : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => asq θ) := by
    have h := Work.FTS.Nonlinear.Open.row25_smoothOpen_ang_mul (a := fun _ => lam)
      (b := fun θ => -((Real.sin θ) ^ 2))
      (Work.FTS.Nonlinear.Open.row25_smoothOpen_ang_const lam)
      Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
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
  have hsmhk : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Spaces.hKer z) :=
    Work.FTS.NonlinRows.smoothOpen_radial Work.FTS.Nonlinear.Open.row25_contDiffOn_hKer
  have hwprodHK := hN.wprod α hIoc (fun z _ => Work.Spaces.hKer z) g hsmhk hSmem hqo4
  have hsmkg : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.hKer z * g z θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => by
      have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => Work.Spaces.hKer z)).mp
        hsmhk n
      have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hctx.hSmoothOpen n
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
  exact hB

/-! ## Row 26: the piece `N₅^{ss} = -sin²θ·FK(F_*)·F_*` -/

/-- **Row 26 of the honest §8 table**: `Xn α (N₅^{ss}) ≤ K·α²`.

The piece depends only on `α`, and the priced estimate `StrongPersist.L3Rhs.N5ssPriced`
supplies the bound with a constant independent of all the data. -/
theorem rowN5ssHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2 := by
  obtain ⟨C, hC, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N5ssPriced
  exact ⟨C, hC, fun {α} {g Φs Φg} hctx => (hrow α ⟨hctx.hα, hctx.hα1⟩).2⟩

/-! ## The target -/

theorem rowsN5b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g) + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2 := by
  obtain ⟨K1, hK1, h1⟩ := rowN5gsHon IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rowN5sgHon IP hN hE
  obtain ⟨K3, hK3, h3⟩ := rowN5ssHon IP hN hE
  refine ⟨K1 + K2 + K3, by linarith, ?_⟩
  intro α g Φs Φg hctx
  refine ⟨?_, ?_⟩
  · have h := add_le_add (h1 hctx) (h2 hctx)
    rw [← add_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact le_add_of_nonneg_right hK3.le
    · exact mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 g)
  · exact (h3 hctx).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (add_nonneg hK1.le hK2.le)) (sq_nonneg α))

end Work.FTS.StrongEps.E4R3.N4C.rows
