/-
Interior regularity (`bslOp_interiorSmooth`): the *localized* distributional equation, in the
pairing form.

The weak identity for `(V,G)` on `W` (test functions supported in `W`) is tested against the
compactly supported test function `ψ = χ·φ`, and the cut-off data (`χ' ≡ 1`, `σ ≡ 1`,
`tt ≡ tan θ` on the open set `U ⊇ tsupport χ`) is used to rewrite the resulting pairing
identity into the form displayed below.

The mathematical content is the pointwise Leibniz computation `pointwiseIdentityLoc` (the two
`d`-derivatives of `χ·φ` expanded by the product rule; on `U` the multipliers `σ`, `tt`, `χ'`
reduce to `1`, `tan θ`, `1`, and the identity `d₁(tan (· 1)) = 1 + tan²` is used), followed by
the linearity of the Bochner integral.

The pole `cos (x 1) = 0` of `tan` is excluded on `U` by `VT.cosNeZeroOfEqTanOn` (a smooth
function agreeing with `tan (· 1)` on an open set cannot meet the poles of `tan`); this is what
replaces the hypothesis `U ⊆ stripE` of the sibling statement
`LocalEquation.localEquation`.  `VT.kopRepresentative` supplies a continuous compactly supported
representative of `Kop (χ·φ)`, used for the integrability bookkeeping.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.LocalEquationAux
import Submission.Work.EllipticEst.InteriorRegularity.VT.cosNeZeroOfEqTanOn
import Submission.Work.EllipticEst.InteriorRegularity.VT.kopRepresentative

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The pointwise Leibniz computation behind the localized equation: for `ψ = χ·φc` and with the
cut-off data `χ' ≡ 1`, `σ ≡ 1`, `tt ≡ tan θ` on the open set `U ⊇ tsupport χ` (and `U` avoiding
the poles of `tan`), the sum of the eight terms of the local equation vanishes pointwise. -/
private theorem pointwiseIdentityLoc {χ χ' σ tt φc : E2 → ℂ} {U : Set E2}
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hcosU : ∀ x ∈ U, Real.cos (x 1) ≠ 0)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσs : ∀ n : ℕ, ContDiff ℝ n σ) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hφs : ∀ n : ℕ, ContDiff ℝ n φc)
    (hσ1 : ∀ x ∈ U, σ x = 1) (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (x : E2) :
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σ y) * φc y) x
      - χ x * d1 (fun y => (σ y * tt y) * φc y) x
      + χ x * (6 * σ x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + Kop (fun y => χ y * φc y) x = 0 := by
  have hχd : ∀ y : E2, DifferentiableAt ℝ χ y := fun y => (hχs 1).differentiable (by norm_num) y
  have hσd : ∀ y : E2, DifferentiableAt ℝ σ y := fun y => (hσs 1).differentiable (by norm_num) y
  have httd : ∀ y : E2, DifferentiableAt ℝ tt y := fun y => (htts 1).differentiable (by norm_num) y
  have hφd : ∀ y : E2, DifferentiableAt ℝ φc y := fun y => (hφs 1).differentiable (by norm_num) y
  have hd0χd : ∀ y : E2, DifferentiableAt ℝ (d0 χ) y :=
    fun y => (Loc.contDiff_d0 hχs 1).differentiable (by norm_num) y
  have hd1χd : ∀ y : E2, DifferentiableAt ℝ (d1 χ) y :=
    fun y => (Loc.contDiff_d1 hχs 1).differentiable (by norm_num) y
  have hd0φd : ∀ y : E2, DifferentiableAt ℝ (d0 φc) y :=
    fun y => (Loc.contDiff_d0 hφs 1).differentiable (by norm_num) y
  have hd1φd : ∀ y : E2, DifferentiableAt ℝ (d1 φc) y :=
    fun y => (Loc.contDiff_d1 hφs 1).differentiable (by norm_num) y
  have e2 : d0 (fun y => (5 * σ y) * φc y) x = (5 * σ x) * d0 φc x + (5 * d0 σ x) * φc x := by
    rw [Loc.d0_mul (f := fun y => 5 * σ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (5 : ℂ))).mul (hσd x)) (hφd x),
      Loc.d0_const_mul (5 : ℂ) (hσd x)]
  have e3 : d1 (fun y => (σ y * tt y) * φc y) x
      = (σ x * tt x) * d1 φc x + (σ x * d1 tt x + d1 σ x * tt x) * φc x := by
    rw [Loc.d1_mul (f := fun y => σ y * tt y) (g := φc) (x := x) ((hσd x).mul (httd x)) (hφd x),
      Loc.d1_mul (f := σ) (g := tt) (x := x) (hσd x) (httd x)]
  have e4 : d0 (fun y => (2 * d0 χ y) * φc y) x
      = (2 * d0 χ x) * d0 φc x + (2 * d0 (d0 χ) x) * φc x := by
    rw [Loc.d0_mul (f := fun y => 2 * d0 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd0χd x)) (hφd x),
      Loc.d0_const_mul (2 : ℂ) (hd0χd x)]
  have e5 : d1 (fun y => (2 * d1 χ y) * φc y) x
      = (2 * d1 χ x) * d1 φc x + (2 * d1 (d1 χ) x) * φc x := by
    rw [Loc.d1_mul (f := fun y => 2 * d1 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd1χd x)) (hφd x),
      Loc.d1_const_mul (2 : ℂ) (hd1χd x)]
  have eK : Kop (fun y => χ y * φc y) x
      = - (d0 (d0 (fun y => χ y * φc y)) x) - (d1 (d1 (fun y => χ y * φc y)) x)
        - 5 * d0 (fun y => χ y * φc y) x
        + (Real.tan (x 1) : ℂ) * d1 (fun y => χ y * φc y) x
        + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ x * φc x) := by
    rw [show Kop (fun y => χ y * φc y) = fun z : E2 =>
        - d0 (d0 (fun y => χ y * φc y)) z - d1 (d1 (fun y => χ y * φc y)) z
        - 5 * d0 (fun y => χ y * φc y) z
        + (Real.tan (z 1) : ℂ) * d1 (fun y => χ y * φc y) z
        + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
  rw [e2, e3, e4, e5, eK]
  rw [Loc.d0_d0_mul (f := χ) (g := φc) hχd hφd hd0χd hd0φd x,
      Loc.d1_d1_mul (f := χ) (g := φc) hχd hφd hd1χd hd1φd x,
      Loc.d0_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x),
      Loc.d1_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x)]
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat]
  by_cases hx : x ∈ U
  · have hσx : σ x = 1 := hσ1 x hx
    have httx : tt x = (Real.tan (x 1) : ℂ) := htt1 x hx
    have hχ'x : χ' x = 1 := hχ'1 x hx
    have hevσ : σ =ᶠ[𝓝 x] (fun _ : E2 => (1 : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hσ1 y hy
    have hd0σ : d0 σ x = 0 := by rw [Loc.d0_congr hevσ, Loc.d0_const]
    have hd1σ : d1 σ x = 0 := by rw [Loc.d1_congr hevσ, Loc.d1_const]
    have hevtt : tt =ᶠ[𝓝 x] (fun y : E2 => (Real.tan (y 1) : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact htt1 y hy
    have hcos : Real.cos (x 1) ≠ 0 := hcosU x hx
    have hd1tt : d1 tt x = 1 + ((Real.tan (x 1) : ℂ)) ^ 2 := by
      rw [Loc.d1_congr hevtt, Loc.d1_tan' x hcos]
    rw [hσx, httx, hχ'x, hd0σ, hd1σ, hd1tt]
    ring
  · have hxt : x ∉ tsupport χ := fun h => hx (htsU h)
    have hW : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hxW : x ∈ (tsupport χ)ᶜ := hxt
    have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hevχ : χ =ᶠ[𝓝 x] (0 : E2 → ℂ) := Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) hχ0W
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    have hd0χ : d0 χ x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevχ
    have hd1χ : d1 χ x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevχ
    have hevd0χ : d0 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hevd1χ : d1 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hd0d0χ : d0 (d0 χ) x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevd0χ
    have hd1d1χ : d1 (d1 χ) x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevd1χ
    rw [hχx, hd0χ, hd1χ, hd0d0χ, hd1d1χ]
    ring

/-- The pairing form of the localized distributional equation.  From the weak identity for `(V,G)` on `W` one gets, for every test function `φ`, the identity obtained by testing the weak formulation against `χ·φ` and rewriting with the cut-off data (`χ' ≡ 1`, `σ ≡ 1`, `tt ≡ tan θ` on the open `U ⊇ tsupport χ`).

Warning: do NOT import `Submission.Work.EllipticEst.InteriorRegularity.IR.Defs` (it re-declares `stripE` and clashes with `Strip.lean`). The helper lemmas `d0_mul`, `d1_mul`, `d0_add`, `d1_add`, `d0_congr`, `d1_congr`, `d0_eq_zero_of_eventuallyEq_zero`, `d1_eq_zero_of_eventuallyEq_zero`, `d0_d0_mul`, `d1_d1_mul`, `d1_tan`, `d0_const_mul`, `d1_const_mul` in `Submission/Work/EllipticEst/InteriorRegularity/LocalEquation.lean` are proved (that file's `localEquation` itself is not; re-prove the helpers or copy them into a sorry-free file of your own). -/
theorem localEquationLoc {V G : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {W : Set Work.EllipticEst.InteriorRegularity.E2}
    (hweak : ∀ ψ : Work.EllipticEst.InteriorRegularity.E2 → ℂ,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ W →
      ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop ψ x = ∫ x, G x * ψ x)
    {χ χ' σ tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {U : Set Work.EllipticEst.InteriorRegularity.E2}
    (hχc : HasCompactSupport χ) (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχ'c : HasCompactSupport χ') (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσc : HasCompactSupport σ) (hσs : ∀ n : ℕ, ContDiff ℝ n σ)
    (httc : HasCompactSupport tt) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hUsub : U ⊆ W)
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (hσ1 : ∀ x ∈ U, σ x = 1)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hV : MeasureTheory.Integrable V) (hG : MeasureTheory.Integrable G)
    (φ : SchwartzMap Work.EllipticEst.InteriorRegularity.E2 ℂ) :
    (∫ x, (χ x * (Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 (φ : Work.EllipticEst.InteriorRegularity.E2 → ℂ)) x
          + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 (φ : Work.EllipticEst.InteriorRegularity.E2 → ℂ)) x)) * V x)
      = - (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (5 * σ y) * φ y) x) * V x)
        + (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (σ y * tt y) * φ y) x) * V x)
        - (∫ x, (χ x * (6 * σ x) * φ x) * V x)
        + (∫ x,
            (χ' x * (((Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 χ) x + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 χ) x)
              - 5 * Work.EllipticEst.InteriorRegularity.d0 χ x + tt x * Work.EllipticEst.InteriorRegularity.d1 χ x) * φ x)) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d0 χ y) * φ y) x) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d1 χ y) * φ y) x) * V x)
        - (∫ x, (χ x * φ x) * G x) := by
  set φc : E2 → ℂ := (φ : E2 → ℂ) with hφc
  have hφs : ∀ n : ℕ, ContDiff ℝ n φc := by
    intro n
    rw [hφc]
    exact φ.smooth n
  -- the test function `ψ = χ·φc`
  have hψsm : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => χ y * φc y) :=
    fun n => (hχs n).mul (hφs n)
  have hψcs : HasCompactSupport (fun y : E2 => χ y * φc y) := hχc.mul_right
  have hψsupp : Function.support (fun y : E2 => χ y * φc y) ⊆ W := by
    intro y hy
    exact hUsub (htsU (subset_tsupport χ (Function.support_mul_subset_left χ φc hy)))
  have hwk := hweak (fun y : E2 => χ y * φc y) hψsm hψcs hψsupp
  -- integrability of the integrands
  have hVint : ∀ {a : E2 → ℂ}, Continuous a → HasCompactSupport a →
      Integrable (fun x => a x * V x) := by
    intro a ha hac
    simpa only [smul_eq_mul] using
      hV.locallyIntegrable.integrable_smul_left_of_hasCompactSupport ha hac
  have h5σφ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (5 * σ y) * φc y) :=
    fun n => ((contDiff_const (c := (5 : ℂ))).mul (hσs n)).mul (hφs n)
  have hσtt : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (σ y * tt y) * φc y) :=
    fun n => ((hσs n).mul (htts n)).mul (hφs n)
  have h2d0χ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (2 * d0 χ y) * φc y) :=
    fun n => ((contDiff_const (c := (2 : ℂ))).mul (Loc.contDiff_d0 hχs n)).mul (hφs n)
  have h2d1χ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (2 * d1 χ y) * φc y) :=
    fun n => ((contDiff_const (c := (2 : ℂ))).mul (Loc.contDiff_d1 hχs n)).mul (hφs n)
  have hρ : ∀ n : ℕ, ContDiff ℝ n
      (fun x : E2 => (d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) :=
    fun n => (((Loc.contDiff_d0 (Loc.contDiff_d0 hχs) n).add
        (Loc.contDiff_d1 (Loc.contDiff_d1 hχs) n)).sub
      ((contDiff_const (c := (5 : ℂ))).mul (Loc.contDiff_d0 hχs n))).add
      ((htts n).mul (Loc.contDiff_d1 hχs n))
  have hc1 : Continuous (fun x : E2 => χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) :=
    (hχs 0).continuous.mul (((Loc.contDiff_d0 (Loc.contDiff_d0 hφs) 0).continuous).add
      ((Loc.contDiff_d1 (Loc.contDiff_d1 hφs) 0).continuous))
  have hc2 : Continuous (fun x : E2 => χ x * d0 (fun y => (5 * σ y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d0 h5σφ 0).continuous)
  have hc3 : Continuous (fun x : E2 => χ x * d1 (fun y => (σ y * tt y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d1 hσtt 0).continuous)
  have hc4 : Continuous (fun x : E2 => χ x * (6 * σ x) * φc x) :=
    ((hχs 0).continuous.mul ((contDiff_const (c := (6 : ℂ))).mul (hσs 0)).continuous).mul
      (hφs 0).continuous
  have hc5 : Continuous (fun x : E2 => χ' x *
      (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) :=
    (hχ's 0).continuous.mul (((hρ 0).continuous).mul (hφs 0).continuous)
  have hc6 : Continuous (fun x : E2 => χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d0 h2d0χ 0).continuous)
  have hc7 : Continuous (fun x : E2 => χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d1 h2d1χ 0).continuous)
  -- a continuous compactly supported representative of `Kop (χ·φc)`
  obtain ⟨K, hKc, hKcs, hKeq⟩ :=
    kopRepresentative (χ := χ) (φc := φc) (tt := tt) hU hχc htsU hχs hφs htts htt1
  have hInt1 : Integrable (fun x => (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x) :=
    hVint hc1 hχc.mul_right
  have hInt2 : Integrable (fun x => (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x) :=
    hVint hc2 hχc.mul_right
  have hInt3 : Integrable (fun x => (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x) :=
    hVint hc3 hχc.mul_right
  have hInt4 : Integrable (fun x => (χ x * (6 * σ x) * φc x) * V x) :=
    hVint hc4 ((hχc.mul_right (f' := fun x : E2 => 6 * σ x)).mul_right (f' := φc))
  have hInt5 : Integrable
      (fun x => (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
        * V x) :=
    hVint hc5 hχ'c.mul_right
  have hInt6 : Integrable (fun x => (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x) :=
    hVint hc6 hχ'c.mul_right
  have hInt7 : Integrable (fun x => (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x) :=
    hVint hc7 hχ'c.mul_right
  have hInt8 : Integrable (fun x => K x * V x) := hVint hKc hKcs
  -- the pointwise identity
  set B : E2 → ℂ := fun x =>
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σ y) * φc y) x
      - χ x * d1 (fun y => (σ y * tt y) * φc y) x
      + χ x * (6 * σ x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + K x with hBdef
  have hBzero : ∀ x : E2, B x = 0 := by
    intro x
    simp only [hBdef]
    rw [← hKeq x]
    exact pointwiseIdentityLoc hU htsU (cosNeZeroOfEqTanOn hU htts htt1) hχs hχ's hσs htts
      hφs hσ1 htt1 hχ'1 x
  have hzero : ∫ x, B x * V x = 0 := by simp [hBzero]
  have hlin : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, K x * V x) := by
    have hcongr : ∫ x, B x * V x
        = ∫ x, ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x
            + (χ x * (6 * σ x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K x * V x) := by
      rw [show (fun x : E2 => B x * V x)
          = (fun x => ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x
            + (χ x * (6 * σ x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K x * V x)) from funext (fun x => by simp only [hBdef]; ring)]
    rw [hcongr]
    exact Loc.integral_lin8 hInt1 hInt2 hInt3 hInt4 hInt5 hInt6 hInt7 hInt8
  have hIK : (∫ x, K x * V x) = (∫ x, (χ x * φc x) * G x) := by
    rw [show (fun x : E2 => K x * V x) = (fun x => V x * Kop (fun y => χ y * φc y) x) from
      funext (fun x => by rw [← hKeq x]; ring)]
    rw [hwk]
    rw [show (fun x : E2 => G x * (χ x * φc x)) = (fun x => (χ x * φc x) * G x) from
      funext (fun x => by ring)]
  have h1 : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) := by
    rw [hlin, hIK]
  have h2 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) = 0 := by
    rw [← h1]
    exact hzero
  have h3 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
      = - (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        - (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        + (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        - (∫ x, (χ x * φc x) * G x) := by
    linear_combination h2
  exact h3

end Work.EllipticEst.InteriorRegularity.VT
