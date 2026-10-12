import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KzAllC
import Submission.Work.BoseBoxFock.KzOpC_floor_window
import Submission.Work.BoseBoxFock.symR_floor_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.KzAllC2` — the floor, the split and the `symR` row bounds for the
# label-`0` (`All`) instruments

* `quadForm_re_split_of_isRealMap` — the real/imaginary split of the quadratic form of any
  `IsRealMap` operator (`CFockReal.lean`'s realness algebra);
* `KzOpCAll_floor_window` — the `valFSAll` floor for `KzOpCAll` (the `All` analogue of
  `KzOpC_floor_window`);
* `symR_floor_genAll` — the pointwise `symR` floor with the `KzOpCAll` discrepancy
  (the `All` analogue of `symR_floor_gen`).
-/

noncomputable section

open scoped BigOperators Real

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {m : ℕ} [NeZero m]

/-! ## 1. The real/imaginary split of an `IsRealMap` quadratic form -/

/-- **Polarisation split.**  For a real operator `A` (`IsRealMap`, `CFockReal.lean`) and two
real-coordinate vectors `x, y`, the quadratic form of `A` at `x + iy` is the sum of the forms
at `x` and at `y`. -/
theorem quadForm_re_split_of_isRealMap {X : Type*} [DecidableEq X]
    (A : cfock X →ₗ[ℂ] cfock X) (hA : IsRealMap A) (x y : cfock X)
    (hx : ∀ β : X →₀ ℕ, ((toCFock X).symm x β).im = 0)
    (hy : ∀ β : X →₀ ℕ, ((toCFock X).symm y β).im = 0) :
    (inner ℂ (x + Complex.I • y) (A (x + Complex.I • y))).re
      = (inner ℂ x (A x)).re + (inner ℂ y (A y)).re := by
  set xc : (X →₀ ℕ) →₀ ℂ := (toCFock X).symm x with hxc
  set yc : (X →₀ ℕ) →₀ ℂ := (toCFock X).symm y with hyc
  have hxci : ∀ β, (xc β).im = 0 := fun β => by rw [hxc]; exact hx β
  have hyci : ∀ β, (yc β).im = 0 := fun β => by rw [hyc]; exact hy β
  set f : (X →₀ ℕ) →₀ ℂ := xc + Complex.I • yc with hf
  have hfr : ∀ β, (f β).re = (xc β).re := fun β => by
    have h1 := hyci β
    simp only [hf, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Complex.add_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, h1, zero_mul, mul_zero, sub_zero,
      add_zero]
  have hfi : ∀ β, (f β).im = (yc β).re := fun β => by
    have h1 := hxci β
    simp only [hf, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, h1, zero_mul, mul_zero, zero_add,
      one_mul]
  have hxs : xc.support ⊆ f.support := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ ⊢
    intro hf0
    exact hβ (Complex.ext (by rw [Complex.zero_re, ← hfr β, hf0, Complex.zero_re]) (hxci β))
  have hys : yc.support ⊆ f.support := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ ⊢
    intro hf0
    exact hβ (Complex.ext (by rw [Complex.zero_re, ← hfi β, hf0, Complex.zero_im]) (hyci β))
  have hxc' : toCFock X xc = x := by rw [hxc]; exact LinearEquiv.apply_symm_apply _ _
  have hyc' : toCFock X yc = y := by rw [hyc]; exact LinearEquiv.apply_symm_apply _ _
  have hff : toCFock X f = toCFock X xc + Complex.I • toCFock X yc := by
    rw [hf, map_add, map_smul]
  have hL : (inner ℂ (x + Complex.I • y) (A (x + Complex.I • y))).re
      = (inner ℂ (toCFock X f) (A (toCFock X f))).re := by
    rw [hff, ← hxc', ← hyc']
  rw [hL, quadForm_re_expansion A hA f f.support (Finset.Subset.refl _),
    ← hxc', ← hyc']
  rw [quadForm_re_expansion A hA xc f.support hxs,
    quadForm_re_expansion A hA yc f.support hys]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [hfr α, hfr β, hfi α, hfi β, hxci α, hxci β, hyci α, hyci β, zero_mul, mul_zero,
    add_zero]
  ring

/-! ## 2. The `valFSAll` floor -/

theorem KzOpCAll_floor_window (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ C Kw Kχ ρ : ℝ) (hμ : 0 < μ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hKw : 0 ≤ Kw) (hKχ : 0 ≤ Kχ)
    (henv : Work.BoseBoxFock.EnvFactsAt v h fc fu HM μ C)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ Kχ)
    (x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))
    (hre : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
      ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x β).im = 0)
    (hdec : ∃ φ : ℕ → Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
      (∀ j : ℕ, Work.BoseBoxFock.nPlusC (m := (HM μ).m) (φ j) = (j : ℝ) • φ j)
        ∧ x = ∑ j ∈ Finset.range (⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ + 1), φ j) :
    (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖x‖ ^ 2
      ≤ (inner ℂ x (Work.BoseBoxFock.KzOpCAll (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
  classical
  obtain ⟨hell, -, -, -, -, -, -, -, hω0, -, hωval, -, -, -, -, -⟩ := henv
  have hω : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega 0
      + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
    rw [hωval]; linarith
  -- `𝓜 = (HonestBoxFam …).E.bigM ≥ 0`
  have hM0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
    show 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
    exact (Work.BoseBox.bigM_pos_of_params hμ hav).le
  -- ## the condensate-free lift of `x`
  set vc : (Work.BoseB4.Excited (HM μ).m →₀ ℕ) →₀ ℂ :=
    (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x with hvc
  set g : (Work.BoseB4.Excited (HM μ).m →₀ ℕ) →₀ ℝ := vc.mapRange Complex.re (by simp) with hgmr
  set f : Work.BoseB4.RealFock (HM μ).m := Work.BoseBoxFock.ExcLift.liftL g with hflift
  have hsplit : Work.BoseB4.split f = Finsupp.single 0 x := by
    have hV : Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp) g = vc := by
      ext β
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
      exact Work.BoseBoxFock.ExcLift.ofReal_re_of_im_zero (hre β)
    rw [hflift, Work.BoseBoxFock.ExcLift.split_liftL, Work.BoseBoxFock.ExcLift.levelL_eq, hV]
    exact congrArg (Finsupp.single (0 : ℕ))
      (LinearEquiv.apply_symm_apply (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)) x)
  -- ## the degree bound on `supp f`
  have hdeg : ∀ α : Fin (HM μ).m →₀ ℕ, f α ≠ 0 →
      ((Finsupp.degree α : ℕ) : ℝ) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
    have hgβ : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ, g β ≠ 0 →
        ((Finsupp.degree β : ℕ) : ℝ) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by
      intro β hβ
      by_contra hcon
      have hcon' : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
          < ((Finsupp.degree β : ℕ) : ℝ) := not_le.mp hcon
      have hfl : ⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ < Finsupp.degree β := by
        have h1 : ((⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ : ℕ) : ℝ)
            ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := Nat.floor_le hM0
        have h2 : ((⌊(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM⌋₊ : ℕ) : ℝ)
            < ((Finsupp.degree β : ℕ) : ℝ) := lt_of_le_of_lt h1 hcon'
        exact_mod_cast h2
      have hv0 : vc β = 0 := coord_eq_zero_of_floor_lt x hdec β hfl
      have hg0 : g β = 0 := by
        rw [hgmr, Finsupp.mapRange_apply, hv0]; simp
      exact hβ hg0
    simpa only [hflift] using
      support_liftL_degree_le (M := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
        g hgβ
  have hwin : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f :=
    NWindow_of_support_degree v h fc fu HM μ _ f hdeg
  by_cases hx0 : x = 0
  · rw [hx0]; simp
  · -- ## the Rayleigh quotient of the lift
    have hfne : f ≠ 0 := by
      intro hf0
      have h1 : Finsupp.single (0 : ℕ) x = 0 := by rw [← hsplit, hf0, map_zero]
      exact hx0 (Finsupp.single_eq_zero.mp h1)
    have hnormSq : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f = ‖x‖ ^ 2 := by
      show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp f f = ‖x‖ ^ 2
      have h3 : Work.BoseB4.bomb (HM μ).m f f = ‖x‖ ^ 2 := by
        have hsin := Work.BoseB4.Split_inner f f
        rw [hsplit, Work.BoseBoxFock.coreInner_single_zero] at hsin
        have hre2 := congrArg Complex.re hsin
        rw [Work.BoseB4.re_inner_self, Complex.ofReal_re] at hre2
        exact hre2.symm
      exact h3
    have hray := Work.BoseBoxFock.valFSAll_le_rayleigh
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) ρ f
      (Work.BoseBoxFock.bddBelow_valFSAll_honest v h fc fu HM μ ρ hρ hell hω) hwin hfne
    have hIle : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1)
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ :=
      ciInf_le (Work.BoseBoxFock.bddBelow_valFSAll_range_rho v h fc fu HM μ Kw Kχ hμ hav
        hω0 hωval hWω hKχ hχb) ⟨ρ, hρ⟩
    have h1 : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖x‖ ^ 2
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hIle (sq_nonneg _)
    have h2 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ * ‖x‖ ^ 2
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) := by
      have hpos : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f :=
        Work.BoseFixR.normSq_pos _ hfne
      have hne : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f ≠ 0 :=
        ne_of_gt hpos
      have hmul := mul_le_mul_of_nonneg_right hray hpos.le
      rw [div_mul_cancel₀ _ hne] at hmul
      rwa [hnormSq] at hmul
    have htr : Work.BoseB4.bomb (HM μ).m f
        ((Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f)
        = (inner ℂ x (Work.BoseBoxFock.KzOpCAll (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
      exact Work.BoseBoxFock.bomb_KzOpFSAll_level0 (B := Work.BoseK15.corpusBox)
        (kmom := Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        (hkmom := Work.BoseBoxFock.kmomLab_neg (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        (f := (HM μ).f) (g := (HM μ).g) (hf := (HM μ).hf)
        (T := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T)
        (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (gHat0 := 8 * π * BoseGases.a v) (ρ := ρ) hρ (HM μ).hf0
        (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
        (Work.BoseBoxFock.hN_honest v h fc fu HM μ)
        (Work.BoseBoxFock.hNH_BNHHon v h fc fu HM μ)
        (Work.BoseBoxFock.hTa_honest v h fc fu HM μ)
        (Work.BoseBoxFock.hTaDag_honest v h fc fu HM μ) f x hsplit
    have h3 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ)
        = (inner ℂ x (Work.BoseBoxFock.KzOpCAll (HM μ).f (HM μ).g
            (Work.BoseBoxFock.BNHHon v h fc fu HM μ)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * π * BoseGases.a v) ρ x)).re := by
      have hbq : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ)
          = Work.BoseB4.bomb (HM μ).m f
              ((Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f) := by
        show Work.BoseB4.bomb (HM μ).m
            ((Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f) f
          = Work.BoseB4.bomb (HM μ).m f
              ((Work.BoseBoxFock.KzOpFSAll (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ) f)
        exact Work.BoseB4.Bomb_symm _ _
      rw [hbq]
      exact htr
    exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-! ## 3. The `symR` floor with the `KzOpCAll` discrepancy -/

theorem symR_floor_genAll {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell) (hPH : PHs = F.PHset E)
    (hcH : 0 ≤ Work.BoseBoxFock.cHCF E gHat0) (hω0 : 0 ≤ E.W1omega0)
    (hφ : ∀ k : Mode, f k 0 = 0)
    (hgonb : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (hdisc : ∀ r : ℝ, 0 ≤ r →
      Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
        = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2FAll f E gHat0
          + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
          + Work.BoseBoxFock.D0F f E gHat0)
    (K Kc Kχb Wsup : ℝ) (hK0 : 0 ≤ K) (hKc0 : 0 ≤ Kc) (hKχb0 : 0 ≤ Kχb)
    (hWsup : ∀ k : Mode, |E.W1 k + E.W1omega k| ≤ Wsup)
    (hχ2 : (∑ k : Mode, E.hatChi k ^ 2) ≤ 1)
    (hχ2b : (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ Kχb) :
    ∀ r : ℝ, 0 ≤ r → ∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
      (inner ℂ w (Work.BoseBoxFock.nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2 →
      (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re ≤ K * ‖w‖ ^ 2 →
      (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
        ≥ -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
              + (4 * (Work.BoseBoxFock.i3F E)
                  * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt (Kχb * K))) * r
              + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
                  + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
          * ‖w‖ ^ 2 := by
  intro r hr w hKc hK
  have h2 := Work.BoseBoxFock.symR_row_D2FAll f E gHat0 w
  have h1 := Work.BoseBoxFock.symR_row_D1F_gen f g E hℓ hω0 hgonb K Kc Kχb hK0 hKc0 hKχb0
    hχ2 hχ2b w hKc hK
  have h0 := Work.BoseBoxFock.symR_row_D0F f E gHat0 Kc Wsup hℓ hWsup w hKc
  have hL : (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
      = r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2FAll f E gHat0 w)).re
        + r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re
        + (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := by
    rw [hdisc r hr]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    simp only [kfb_inner_addR, kfb_inner_smulR, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hL]
  have hA : r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
      ≤ r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2FAll f E gHat0 w)).re :=
    mul_le_mul_of_nonneg_left h2.ge (sq_nonneg r)
  have hB : r * (-(4 * (Work.BoseBoxFock.i3F E)
        * (|E.W1 0| * Real.sqrt Kc
          + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2)
      ≤ r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re :=
    mul_le_mul_of_nonneg_left h1 hr
  have hC : -(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
        + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2
      ≤ (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := h0
  have hring : -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
        + (4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt (Kχb * K))) * r
        + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
        * ‖w‖ ^ 2
      = r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
        + r * (-(4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc
              + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2)
        + (-(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2) := by
    ring
  rw [hring]
  linarith [hA, hB, hC]

end Work.BoseBoxFock
