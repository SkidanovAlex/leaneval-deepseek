import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.H2W.slot20A
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.Cores.topSlotB_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `Cores/topSlotB_two`: the top angular slot of `∂_θθΨ` in the plain form

The target is the plain-derivative form of the paper's Step 5 for the `B`-half of the
`Tk α 2`-slot,

  `∫_z w(z)² ∫_θ (∂_θ⁴Ψ)² sin(2θ)^{4-γ}  ≤  C |F|_{ℋ²}²`,   `γ = gam α = 1 + α/10`,

for data of the weak class `TT.EllWeakPos α 2 F Ψ` and `0 < α ≤ 1/4`, with a constant that is
universal (`α`-independent).  It is bound (6) of `Cores/NOTES_topSlotsTwo.md`.

The reduction implemented in this file is the paper's Steps 3–5 of the proof of `prop:H2`
(Elgindi, Annals of Math. **194** (2021)):

* **Step 5 for the slice** (`H2W.Step5.s20_step5`, and already proved at the slice level in
  `H2W.sliceStep5Weak`): `∫(u⁗)²σ₄ ≤ C(∫(g'')²σ₄ + ∫(u''')²σ₂ + ∫(u'')²sEta + ∫(u')² + ∫u²)`,
  lifted to the `(z,θ)`-integral gives `s20M4 α Ψ ≤ C(s20J2 + s20M3 + A₂+A₁+A₀)`, where
  `s20M4 α Ψ = ∫∫ 2w²(∂_θ⁴Ψ)²σ₄` is exactly twice the left-hand side of the target;
* **the source and lower-order slots** (`H2W.Step5.s20_source` + `H2W.Step5.s20_step4`), i.e.
  `s20J2 + s20M3 + (A₂+A₁+A₀) ≤ C(pPure Ψ + HkSq α 2 F)`;
* **Step 3** (the radial shift), the one genuinely missing input, isolated below in the
  hypothesis `hpure`: the `j = 2` summand of `pPure`.  The `j = 0` and `j = 1` summands *are*
  proved here from `EllWeak0`: the `j = 1` summand by applying it to the once-shifted datum
  `(D_zF, D_zΨ)`, whose moment conditions are available at level `2`
  (`EllWeakPos_DzIter_one_shift_of_two_le`).

`Work.Spaces.w z = (1+z)²/z²`, `Work.Spaces.gam α = 1 + α/10`.
-/

/-! ## Elementary identities -/

/-- At level `0` the `ℋ`-integrand is the single squared weighted slot. -/
theorem hkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- `pPure` is the sum of the three level-`0` `ℋ`-norms `|∂_θ²(D_z^jΨ)|_{ℋ⁰}`, `j ≤ 2`. -/
theorem pPure_eq_sum_HkSq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.pPure Ψ
      = ∑ j ∈ Finset.range 3,
          Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
  rw [Work.FTS.EllipticEst.H2W.pPure]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  exact (hkIntegrand_zero_eq α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) z θ).symm

/-- **`s20M4` is twice the left-hand side of the target.** -/
theorem s20M4_eq_two_mul (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.s20M4 α Ψ
      = 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))) := by
  rw [Work.FTS.EllipticEst.H2W.s20M4]
  have h1 : (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      = fun z => 2 * ((Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))) := by
    funext z
    rw [show (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        = fun θ => (2 * (Work.Spaces.w z) ^ 2) *
            ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) from rfl]
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [h1, MeasureTheory.integral_const_mul]

/-- The level-`0` `ℋ`-norm of `D_z F` is dominated by the level-`2` `ℋ`-norm of `F` (it is the
`i = 1` summand of `HkIntegrand α 2 F`). -/
theorem HkSq_zero_DzIter_one_le (α : ℝ) {F : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α 2 F) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) ≤ Work.Spaces.HkSq α 2 F := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 F) z θ)))
    h.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 F) z θ))
    (h.1 z hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  rw [hkIntegrand_zero_eq]
  exact Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 1 (by norm_num)

/-! ## Smoothness of the three fields of the weak class on the open quadrant -/

/-- The three `ℋ`-fields of a datum of the weak class are `C^∞` on the open quadrant. -/
theorem smoothOpen_fields {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hθ' => h.1 z hz θ hθ hθ')
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2
  exact ⟨fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hSF n,
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSA n,
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSB n⟩

/-- The weak class is monotone in the level: lowering the level only weakens the `HkMem`
requirements. -/
theorem EllWeakPos_descend {α : ℝ} {k l : ℕ} (hkl : k ≤ l) {F Ψ : ℝ → ℝ → ℝ}
    (hsmF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsmA : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsmB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hsmF h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hsmA h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl hsmB h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      (Work.FTS.EllipticEst.TT.smoothOpen_diagHon hsmB) h.memZPth2⟩

/-! ## The pure-slot bound from `EllWeak0` -/

/-- **`pPure` from `EllWeak0` plus its `j = 2` summand.**

The `j = 0` summand is the second term of `EllWeak0` at the datum `(F, Ψ)`; the `j = 1`
summand is the same at the once-shifted datum `(D_zF, D_zΨ)` (whose moment conditions are
available at level `2`); the `j = 2` summand is the hypothesis `hpure` — the paper's Step 3,
which is not derivable from the class as stated. -/
theorem pPure_le_of_pure_two (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C)
    (hpure : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.pPure Ψ ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C0, hC0, hEst⟩ := h0
  obtain ⟨Cp, hCp, hpure⟩ := hpure
  refine ⟨2 * C0 + Cp, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  obtain ⟨hsmF, hsmA, hsmB⟩ := smoothOpen_fields h
  have hF0 : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ :=
    EllWeakPos_descend (α := α) (k := 0) (l := 2) (by norm_num) hsmF hsmA hsmB h
  have hE0 := hEst α F Ψ hα hα4 hF0
  have hF1 : Work.FTS.EllipticEst.TT.EllWeakPos α 1
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    Work.FTS.EllipticEst.remov.EllWeakPos_DzIter_one_shift_of_two_le (le_refl 2) h
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hθ' => h.1 z hz θ hθ hθ')
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2
  have hF10 : Work.FTS.EllipticEst.TT.EllWeakPos α 0
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    EllWeakPos_descend (α := α) (k := 0) (l := 1) (by norm_num)
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSF.Dz n)
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ.Dz 2)) n)
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ.Dz 2) n)
      hF1
  have hE1 := hEst α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 hF10
  have hJ2 := hpure α F Ψ hα hα4 h
  have hB0 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ C0 * Work.Spaces.HkSq α 2 F := by
    have hle : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ C0 * Work.Spaces.HkSq α 0 F := by
      have hz : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      linarith [hE0, hz]
    have hmono : Work.Spaces.HkSq α 0 F ≤ Work.Spaces.HkSq α 2 F :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h.memF
    calc Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ C0 * Work.Spaces.HkSq α 0 F := hle
      _ ≤ C0 * Work.Spaces.HkSq α 2 F := mul_le_mul_of_nonneg_left hmono hC0.le
  have hB1 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ C0 * Work.Spaces.HkSq α 2 F := by
    have hle : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C0 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) := by
      have hz : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      linarith [hE1, hz]
    have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F)
        ≤ Work.Spaces.HkSq α 2 F := HkSq_zero_DzIter_one_le α h.memF
    calc Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C0 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) := hle
      _ ≤ C0 * Work.Spaces.HkSq α 2 F := mul_le_mul_of_nonneg_left hmono hC0.le
  rw [pPure_eq_sum_HkSq α Ψ]
  have hsplit : (∑ j ∈ Finset.range 3,
        Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 0 Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [hsplit]
  simp only [Work.Spaces.DzIter_zero]
  have hHK : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  linarith [hB0, hB1, hJ2, hHK]

/-! ## The assembly -/

/-- **The target from the three pieces.**

`h5` is the two-dimensional Step 5, `hsum` the domination of the Step-5 right-hand side by
`pPure + |F|²_{ℋ²}`, and `hpure` the pure-slot (Step 3) bound; `EllWeak0` supplies the `j = 0, 1`
summands of `pPure` (via `pPure_le_of_pure_two`). -/
theorem topSlotB_two_of_pieces
    (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C)
    (h5 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20M4 α Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
            + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
            + Work.FTS.EllipticEst.H2W.s20A0 Ψ))
    (hsum : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
          + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
            + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F))
    (hpure : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C5, hC5, h5⟩ := h5
  obtain ⟨Cs, hCs, hsum⟩ := hsum
  obtain ⟨Cp, hCp, hpure⟩ := pPure_le_of_pure_two h0 hpure
  have hCp0 : 0 ≤ Cp := le_of_lt hCp
  refine ⟨(C5 * Cs / 2) * (Cp + 1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hS := h5 α F Ψ hα hα4 h
  have hSm := hsum α F Ψ hα hα4 h
  have hP := hpure α F Ψ hα hα4 h
  have hHK : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hP0 : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ :=
    Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ
  have hS0 : 0 ≤ Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
      + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
    linarith [Work.FTS.EllipticEst.H2W.s20J2_nonneg α F Ψ,
      Work.FTS.EllipticEst.H2W.s20M3_nonneg α Ψ,
      Work.FTS.EllipticEst.H2W.s20A2_nonneg Ψ, Work.FTS.EllipticEst.H2W.s20A1_nonneg Ψ,
      Work.FTS.EllipticEst.H2W.s20A0_nonneg Ψ]
  have hLHS : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)))
      = Work.FTS.EllipticEst.H2W.s20M4 α Ψ / 2 := by
    rw [s20M4_eq_two_mul]
    ring
  rw [hLHS]
  have hPK : Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F
      ≤ (Cp + 1) * Work.Spaces.HkSq α 2 F := by
    nlinarith [hP, hHK]
  have hS' : Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
          + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
      ≤ Cs * ((Cp + 1) * Work.Spaces.HkSq α 2 F) :=
    le_trans hSm (mul_le_mul_of_nonneg_left hPK hCs.le)
  have hS'' : Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ Cs * ((Cp + 1) * Work.Spaces.HkSq α 2 F) := by
    linarith [hS']
  have hM4' : Work.FTS.EllipticEst.H2W.s20M4 α Ψ
      ≤ C5 * (Cs * ((Cp + 1) * Work.Spaces.HkSq α 2 F)) :=
    le_trans hS (mul_le_mul_of_nonneg_left hS'' hC5.le)
  have hstep : Work.FTS.EllipticEst.H2W.s20M4 α Ψ / 2
      ≤ (C5 * Cs * (Cp + 1) / 2) * Work.Spaces.HkSq α 2 F := by
    nlinarith [hM4']
  have hstep2 : (C5 * Cs * (Cp + 1) / 2) * Work.Spaces.HkSq α 2 F
      ≤ ((C5 * Cs / 2) * (Cp + 1) + 1) * Work.Spaces.HkSq α 2 F := by
    have he : (C5 * Cs * (Cp + 1) / 2) = (C5 * Cs / 2) * (Cp + 1) := by ring
    rw [he]
    nlinarith [hHK]
  linarith [hstep, hstep2]


end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.EllipticEst.M4.Slot20A =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING (de-duplication of the `Final/Rep` cone).
--
-- Every declaration of this module is the same declaration as the corresponding one of
-- `Submission.Work.FTS.EllipticEst.H2W.slot20A` (the two bodies are byte-identical modulo their `import` lines).
-- Re-declaring them here would be a duplicate declaration in every module whose import
-- cone contains both — and the `Final/Rep` tree lies on the level-`2` path
-- (`Mine.TopSlotTwo`, `Cores.topSlotsTwo`, `TT.slot20_le`).  The names stay available to
-- every consumer of this module, transitively through the import above.
-- The original import list is kept, so nothing that this module used to re-export
-- transitively is lost.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.truncAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The weight bound `|ψ| ≤ C w²` on `(0,∞)` -/


/-! ## Continuity on the open quadrant -/



/-- `L₀Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_Lzero {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) := by
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl h
  have hC : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => -(Work.Spaces.pthIter 2 Ψ z θ)
      + Work.Spaces.pth (fun z θ : ℝ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl h 2))
        (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 h)
  exact hC

/-! ## AM–GM domination by the level-`0` integrands -/


/-! ## A.e. strong measurability of `A z · |∫_θ Λ(z,θ)|` -/


end Work.FTS.EllipticEst.TT
end
end
