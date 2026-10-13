import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.FTS.PhiStar.Series.Deleg.psiCmodeAux.Basic
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Gegenbauer (eFam lam)
open Work.FTS.EllipticEst (Lzero1)

/-! ### Auxiliary lemmas for the `Lzero1` pairing identity -/

/-- `cos θ > 0` on the open angular interval. -/
private lemma cos_pos_of_Ioo' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩

/-- A `C²` function on the closed angular interval is bounded there. -/
private lemma abs_bound_of_continuousOn {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) :
    ∃ B : ℝ, ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |v θ| ≤ B := by
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))) hv.continuousOn
  exact ⟨B, fun θ hθ => by simpa [Real.norm_eq_abs] using hB θ hθ⟩

/-- **`Lzero1 v` is continuous on the open interval** for `v` of class `C²` on the closed one.
On `(0, π/2)` the two `deriv`-occurrences of `Lzero1` may be replaced by the `derivWithin`
versions on `Icc` (which are continuous there by `ContDiffOn.derivWithin`, twice) and the
`deriv (tan θ · v θ)` by the explicit product-rule expression. -/
private lemma continuousOn_Lzero1 {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) :
    ContinuousOn (Lzero1 v) (Set.Ioo 0 (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hpi2
  have hw1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hw2 : ContDiffOn ℝ 0
      (derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hw1.derivWithin hU (by norm_num)
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  have htan : ContinuousOn Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuousOn_tan_Ioo.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn.pow 2
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ^ 2 ≠ 0 :=
    fun θ hθ => pow_ne_zero 2 (ne_of_gt (cos_pos_of_Ioo' hθ))
  have hmain : ContinuousOn (fun θ : ℝ =>
      -(derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ)
      + (v θ / Real.cos θ ^ 2 + Real.tan θ * derivWithin v (Set.Icc 0 (Real.pi / 2)) θ)
      - 6 * v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hw2.continuousOn.mono hsub).neg).add
      ((((hv.continuousOn.mono hsub).div hcos2 hne).add
        (htan.mul (hw1.continuousOn.mono hsub))))).sub
      (continuousOn_const.mul (hv.continuousOn.mono hsub))
  refine hmain.congr (fun θ hθ => ?_)
  have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
  have hev : derivWithin v (Set.Icc 0 (Real.pi / 2)) =ᶠ[𝓝 θ] deriv v := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hA : deriv (deriv v) θ
      = derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ := by
    have h1 : deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ = deriv (deriv v) θ :=
      hev.deriv_eq
    have h2 : deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ
        = derivWithin (derivWithin v (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) θ :=
      (derivWithin_of_mem_nhds hmem).symm
    exact h1.symm.trans h2
  have hB : deriv (fun t : ℝ => Real.tan t * v t) θ
      = v θ / Real.cos θ ^ 2 + Real.tan θ * deriv v θ := by
    have hdv : HasDerivAt v (deriv v θ) θ :=
      ((hv.mono hsub).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
        (by norm_num) |>.hasDerivAt
    have h1 : deriv (fun t : ℝ => Real.tan t * v t) θ
        = 1 / Real.cos θ ^ 2 * v θ + Real.tan θ * deriv v θ :=
      ((Real.hasDerivAt_tan (ne_of_gt (cos_pos_of_Ioo' hθ))).mul hdv).deriv
    rw [h1]
    ring
  have hC : derivWithin v (Set.Icc 0 (Real.pi / 2)) θ = deriv v θ :=
    derivWithin_of_mem_nhds hmem
  simp only [Lzero1]
  rw [show deriv (fun t : ℝ => deriv v t) θ = deriv (deriv v) θ from rfl, hA, hB, ← hC]

/-- **The primitive `P θ = cos θ · (e_n' v - e_n v')` is continuous on the closed interval.**
All factors except `deriv v` are continuous there, and `deriv v` agrees with
`derivWithin v Icc` on the interior; at the endpoints both terms of the bracket vanish
(`e_n 0 = 0`, `v (π/2) = 0`, `cos (π/2) = 0`). -/
private lemma continuousOn_P_primitive (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0) :
    ContinuousOn (fun θ => Real.cos θ * (deriv (eFam n) θ * v θ - eFam n θ * deriv v θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hpi2
  have hw1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hde : ContinuousOn (deriv (eFam n)) (Set.Icc 0 (Real.pi / 2)) :=
    (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n)).continuous.continuousOn
  have hec : ContinuousOn (fun θ => eFam n θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn
  have hmain : ContinuousOn (fun θ => Real.cos θ * (deriv (eFam n) θ * v θ
      - eFam n θ * derivWithin v (Set.Icc 0 (Real.pi / 2)) θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn.mul
      ((hde.mul hv.continuousOn).sub (hec.mul hw1.continuousOn))
  refine hmain.congr (fun θ hθ => ?_)
  simp only []
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    simp only [h0, Work.FTS.PhiStar.Series.Deleg.eFam_zero n]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      simp only [Real.cos_pi_div_two]
      ring
    · rw [derivWithin_of_mem_nhds (Icc_mem_nhds h h2)]

/-- **The pointwise Wronskian identity** for `e_n` and `v`: on the open interval the derivative
of the primitive `P` is exactly the pairing integrand `(Lzero1 v - lam n · v) · e_n · cos θ`. -/
private lemma hasDerivAt_P_primitive {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' => Real.cos θ' * (deriv (eFam n) θ' * v θ' - eFam n θ' * deriv v θ'))
      ((Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ) θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Ioo' hθ)
  have hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv.mono Set.Ioo_subset_Icc_self
  have hop : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hsm : ContDiff ℝ 3 (eFam n) := Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n
  have he1 : HasDerivAt (eFam n) (deriv (eFam n) θ) θ :=
    (hsm.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have he2 : HasDerivAt (deriv (eFam n)) (deriv (deriv (eFam n)) θ) θ :=
    ((ContDiff.deriv' (n := 2) hsm).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hv1 : HasDerivAt v (deriv v θ) θ :=
    ((hv2.contDiffAt hop).differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffOn ℝ 1 (deriv v) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hv1' : HasDerivAt (deriv v) (deriv (deriv v) θ) θ :=
    ((hd1.contDiffAt hop).differentiableAt (by norm_num)).hasDerivAt
  have h := Work.FTS.PhiStar.Series.Deleg.hasDerivAt_lzero_wronskian (f := eFam n) (g := v)
    hcos he1 he2 hv1 hv1'
  refine h.congr_deriv ?_
  rw [Work.FTS.PhiStar.Series.Deleg.eFam_Lzero1 n hθ]
  ring

/-- **The `Lzero1` pairing identity for a `C²` slice (self-adjointness in the weight `cos θ dθ`).**

For `v` of class `C²` (within the) closed interval `[0, π/2]` with `v 0 = v (π/2) = 0`, and
`e := eFam n`, `lam n = 2n(2n+5)` (the Dirichlet eigenvalue of `Lzero1`, see `eFam_Lzero`),
one has

  `∫_{Iθ} (Lzero1 v) · e_n · cos θ = lam n · ∫_{Iθ} v · e_n · cos θ`.

The extra hypothesis `hbd` (a bound for `Lzero1 v` on the *open* interval) is used only for
integrability bookkeeping: the global `deriv` occurring in `Lzero1` is junk at the two
endpoints `0, π/2`, and `hbd` says the integrand is bounded on `(0, π/2)`, hence an honest
Bochner integrand.  It is supplied by the companion lemma `lzero1_bdd_on_Ioo`; the identity
itself does not need it mathematically.

*Route (for the prover).*  Write `e := eFam n` and
`P θ := -((e θ * deriv v θ - deriv e θ * v θ) * Real.cos θ)`.
For `θ ∈ Set.Ioo 0 (π/2)` both `v` (by `hv.mono Ioo_subset_Icc_self`) and `eFam n`
(`contDiff_eFam n`) are `C²` on a neighbourhood of `θ`, so the product rule gives
`HasDerivAt P (…) θ`; expanding and using the eigen-equation in the form
`Lzero1 (eFam n) θ = lam n * eFam n θ` (from `eFam_Lzero` + `Lzero1_eq_Lzero`, valid because
`Real.cos θ ≠ 0` on the open interval) the derivative is exactly

  `(Lzero1 v θ - lam n * v θ) * e θ * Real.cos θ`.

(This is the same computation as the private `hasDerivAt_primitive` of
`Submission/Work/EllipticEst/ModalSolution/Lzero1_energy_cos_correct.lean`, and as
`Submission/Work/FTS/PhiStar/Series/lzero1Primitive.lean` — do NOT import the latter: it
currently fails to build in this workspace.  Re-prove the ~20-line pointwise identity locally.)

`P` is continuous on `Icc`: all factors but `deriv v` are continuous there (`hv.continuousOn`,
`contDiff_eFam n`), and `deriv v θ = derivWithin v (Icc 0 (π/2)) θ` for `θ ∈ Ioo`
(`derivWithin_of_mem_nhds`, as `Icc ∈ 𝓝 θ`), while `ContDiffOn ℝ 1 (derivWithin v Icc) Icc`
(`hv.derivWithin (uniqueDiffOn_Icc _)`) is continuous on the compact `Icc`.  The endpoint
values are `P 0 = P (π/2) = 0`: at `θ = 0` the junk factor `deriv v 0` is multiplied by
`eFam n 0 = 0`, at `θ = π/2` by `v (π/2) = 0` and by `cos (π/2) = 0`.  Hence
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` gives `∫_0^{π/2} (…) = 0`, provided the
integrand is `IntervalIntegrable` on `(0, π/2)` — that follows from `hbd`, from boundedness of
`v` and `e` on `Icc`, and from the fact that the integrand equals a continuous function on
`Ioo`, the only point of `uIoc 0 (π/2)` outside `Ioo` being `π/2` where the junk is multiplied
by `eFam n (π/2) = 0` and `cos (π/2) = 0`.  Splitting the interval integral of
`(Lzero1 v - lam n * v) * e * cos` with `MeasureTheory.integral_sub` (both pieces integrable by
the same boundedness argument) and converting the interval integral on `0..π/2` into the set
integral over `Iθ` (`MeasureTheory.integral_Icc_eq_integral_Ioc` +
`intervalIntegral.integral_of_le`, cf. `ModalSolution.intervalIntegral_eq_setIntegral`) gives
the claim. -/
theorem lzero1_pair_eFam_c2 (v : ℝ → ℝ) (n : ℕ)
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hbd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam n
        * (∫ θ in Work.Spaces.Iθ,
            v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hpi2.le
  obtain ⟨M, hM⟩ := hbd
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _)
    (hM (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  obtain ⟨Q, hQnn, hQ⟩ := Work.FTS.PhiStar.Series.Deleg.eFam_abs_bound n
  obtain ⟨B, hB⟩ := abs_bound_of_continuousOn hv
  have hBnn : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_refl 0, hle⟩)
  have hLc : ContinuousOn (fun θ => Lzero1 v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_Lzero1 hv
  have hEc : ContinuousOn (fun θ => eFam n θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn
  have hVc : ContinuousOn v (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv.continuousOn.mono Set.Ioo_subset_Icc_self
  have hCc : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  have hMc : ContinuousOn (fun θ => lam n * v θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_const.mul hVc
  -- interval integrability of the two pieces of the split integrand
  have hint1 : IntervalIntegrable (fun θ => Lzero1 v θ * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle
      ((hLc.mul hEc).mul hCc) (M * Q) ?_
    intro θ hθ
    have hb1 : |Lzero1 v θ| ≤ M := hM θ hθ
    have hb2 : |eFam n θ| ≤ Q := hQ θ ⟨hθ.1.le, hθ.2.le⟩
    have hb3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    calc |Lzero1 v θ * eFam n θ * Real.cos θ|
        = |Lzero1 v θ| * |eFam n θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ M * Q * 1 := mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hMnn) hb3
          (abs_nonneg _) (mul_nonneg hMnn hQnn)
      _ = M * Q := by ring
  have hint2 : IntervalIntegrable (fun θ => v θ * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact (hv.continuousOn.mul
      ((Work.FTS.PhiStar.Series.Deleg.contDiff_eFam n).continuous.continuousOn)).mul
      Real.continuous_cos.continuousOn
  -- interval integrability of the difference integrand
  have hintg : IntervalIntegrable
      (fun θ => (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
      volume 0 (Real.pi / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle
      (((hLc.sub hMc).mul hEc).mul hCc) ((M + |lam n| * B) * Q) ?_
    intro θ hθ
    have hb1 : |Lzero1 v θ - lam n * v θ| ≤ M + |lam n| * B := by
      calc |Lzero1 v θ - lam n * v θ| ≤ |Lzero1 v θ| + |lam n * v θ| := abs_sub _ _
        _ = |Lzero1 v θ| + |lam n| * |v θ| := by rw [abs_mul]
        _ ≤ M + |lam n| * B := add_le_add (hM θ hθ)
            (mul_le_mul_of_nonneg_left (hB θ ⟨hθ.1.le, hθ.2.le⟩) (abs_nonneg _))
    have hb2 : |eFam n θ| ≤ Q := hQ θ ⟨hθ.1.le, hθ.2.le⟩
    have hb3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hA : (0 : ℝ) ≤ M + |lam n| * B :=
      add_nonneg hMnn (mul_nonneg (abs_nonneg _) hBnn)
    calc |(Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ|
        = |Lzero1 v θ - lam n * v θ| * |eFam n θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ (M + |lam n| * B) * Q * 1 := mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hA)
          hb3 (abs_nonneg _) (mul_nonneg hA hQnn)
      _ = (M + |lam n| * B) * Q := by ring
  -- the fundamental theorem of calculus for the primitive `P`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (continuousOn_P_primitive v n hv h0 h1)
    (fun x hx => hasDerivAt_P_primitive hv n hx) hintg
  have hP0 : Real.cos 0 * (deriv (eFam n) 0 * v 0 - eFam n 0 * deriv v 0) = 0 := by
    rw [h0, Work.FTS.PhiStar.Series.Deleg.eFam_zero n]
    ring
  have hPpi : Real.cos (Real.pi / 2) * (deriv (eFam n) (Real.pi / 2) * v (Real.pi / 2)
      - eFam n (Real.pi / 2) * deriv v (Real.pi / 2)) = 0 := by
    rw [Real.cos_pi_div_two]
    ring
  have hzero : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ) = 0 := by
    rw [hFTC, hPpi, hP0, sub_self]
  -- splitting the integrand
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), Lzero1 v θ * eFam n θ * Real.cos θ)
        - lam n * (∫ θ in (0 : ℝ)..(Real.pi / 2), v θ * eFam n θ * Real.cos θ) := by
    have hsub : IntervalIntegrable
        (fun θ => lam n * (v θ * eFam n θ * Real.cos θ)) volume 0 (Real.pi / 2) :=
      hint2.const_mul _
    rw [show (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (Lzero1 v θ - lam n * v θ) * eFam n θ * Real.cos θ)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (Lzero1 v θ * eFam n θ * Real.cos θ
              - lam n * (v θ * eFam n θ * Real.cos θ)) from
      intervalIntegral.integral_congr (fun θ _ => by ring)]
    rw [intervalIntegral.integral_sub hint1 hsub, intervalIntegral.integral_const_mul]
  -- converting the interval integral into the set integral over `Iθ`
  have hIθ : ∀ F : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, F θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    intro F
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  rw [hIθ (fun θ => Lzero1 v θ * eFam n θ * Real.cos θ),
    hIθ (fun θ => v θ * eFam n θ * Real.cos θ)]
  linarith [hzero, hsplit]

end Work.FTS.PhiStar.Honesty
