/-
Interior regularity (`bslOp_interiorSmooth`), the local equation on a weakly solving pair.

This file proves the *local* form of the weak identity `Q0.StripWeakC V G`:  if the weak
identity holds for every test function with topological support in the strip, then for every
Schwartz function `φ` and every cut-off `χ` with `tsupport χ ⊆ W ⊆ stripE`, the localized
pairing

`∫ V · χ · Δφ`

equals the sum of the eight terms displayed in the statement.  The mechanism is
`Loc.pointwise_identity`: the sum of the eight coefficients plus `Kop (χ·φ)` vanishes
pointwise, so integrating against `V` and using the weak identity for the admissible test
function `χ·φ` (whose topological support is contained in `tsupport χ ⊆ stripE`) yields the
identity.

The hypothesis on `V` is only `LocallyIntegrableOn V stripE` (rather than global local
integrability): every integrand on the `V`-side is supported in `tsupport χ`, which is a
compact subset of `stripE`, so local integrability on the strip suffices.  That is the point
of this version of the lemma.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.LocalEquationAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Integrability from local integrability on a set

If `V` is locally integrable on `s` and `g` is continuous with compact support contained in
`closure (support g) ⊆ s`, then `g · V` is integrable.  (The global version,
`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`, is not available under the
weaker hypothesis `LocallyIntegrableOn V s`; the proof is the same, using that
`tsupport g` is a compact subset of `s`.) -/

theorem integrable_mul_of_locallyIntegrableOn {V g : E2 → ℂ} {s : Set E2}
    (hV : MeasureTheory.LocallyIntegrableOn V s) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hsub : tsupport g ⊆ s) :
    Integrable (fun x : E2 => g x * V x) := by
  have hK : IsCompact (tsupport g) := hgc
  have hVK : MeasureTheory.IntegrableOn V (tsupport g) :=
    hV.integrableOn_compact_subset hsub hK
  have hIntK : MeasureTheory.IntegrableOn (fun x : E2 => g x * V x) (tsupport g) :=
    MeasureTheory.IntegrableOn.continuousOn_mul hg.continuousOn hVK hK
  exact hIntK.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])

/-! ## Topological supports of the differentiated cut-off

`tsupport (d0 f) ⊆ tsupport f` for any `f`, and the analogous statements for the
combinations of `χ`-derivatives appearing in the pointwise identity. -/

theorem tsupport_d0_subset (f : E2 → ℂ) : tsupport (d0 f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra h
  exact hx (Loc.d0_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp h))

theorem tsupport_d1_subset (f : E2 → ℂ) : tsupport (d1 f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra h
  exact hx (Loc.d1_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp h))

theorem tsupport_d0_d0_subset (f : E2 → ℂ) : tsupport (d0 (d0 f)) ⊆ tsupport f :=
  (tsupport_d0_subset (d0 f)).trans (tsupport_d0_subset f)

theorem tsupport_d1_d1_subset (f : E2 → ℂ) : tsupport (d1 (d1 f)) ⊆ tsupport f :=
  (tsupport_d1_subset (d1 f)).trans (tsupport_d1_subset f)

/-- The support of the first-order combination
`(d0 d0 χ + d1 d1 χ) - 5 d0 χ + tt · d1 χ` is contained in `tsupport χ`. -/
theorem tsupport_rho_subset (χ tt : E2 → ℂ) :
    tsupport (fun x : E2 => (d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x)
      ⊆ tsupport χ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
  by_contra hxt
  have hevχ : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
  have hd0χ : d0 χ x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevχ
  have hd1χ : d1 χ x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevχ
  have hWc : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  have hevd0χ : d0 χ =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_of_mem (hWc.mem_nhds hxt)
      (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hy))
  have hevd1χ : d1 χ =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_of_mem (hWc.mem_nhds hxt)
      (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hy))
  have hd0d0χ : d0 (d0 χ) x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevd0χ
  have hd1d1χ : d1 (d1 χ) x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevd1χ
  exact hx (by
    change (d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x = 0
    rw [hd0d0χ, hd1d1χ, hd0χ, hd1χ]
    ring)

/-- The support of the operator-shaped combination `-d0d0 f - d1d1 f - 5 d0 f + tt · d1 f
+ (tt² - 5) f` is contained in `tsupport f`. -/
theorem tsupport_combination_subset (tt f : E2 → ℂ) :
    tsupport (fun x : E2 => - d0 (d0 f) x - d1 (d1 f) x - 5 * d0 f x
        + tt x * d1 f x + ((tt x) ^ 2 - 5) * f x) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxt
  have hevf : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
  have hd0f : d0 f x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevf
  have hd1f : d1 f x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevf
  have hWc : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hevd0f : d0 f =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_of_mem (hWc.mem_nhds hxt)
      (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hy))
  have hevd1f : d1 f =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_of_mem (hWc.mem_nhds hxt)
      (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hy))
  have hd0d0f : d0 (d0 f) x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevd0f
  have hd1d1f : d1 (d1 f) x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevd1f
  exact hx (by
    change - d0 (d0 f) x - d1 (d1 f) x - 5 * d0 f x + tt x * d1 f x
      + ((tt x) ^ 2 - 5) * f x = 0
    rw [hd0d0f, hd1d1f, hd0f, hd1f, hevf.eq_of_nhds]
    simp)

/-! ## The local equation -/

theorem localEq {V G : E2 → ℂ} {W : Set E2}
    (hV : MeasureTheory.LocallyIntegrableOn V Work.EllipticEst.InteriorRegularity.stripE)
    (hG : MeasureTheory.LocallyIntegrableOn G Work.EllipticEst.InteriorRegularity.stripE)
    (hweak : Work.EllipticEst.InteriorRegularity.Q0.StripWeakC V G)
    (hW : IsOpen W) (hWsub : W ⊆ Work.EllipticEst.InteriorRegularity.stripE)
    {χ χ' σc tt : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (hχ's : ∀ n : ℕ, ContDiff ℝ n χ') (hχ'c : HasCompactSupport χ')
    (hσs : ∀ n : ℕ, ContDiff ℝ n σc) (hσc : HasCompactSupport σc)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt) (httc : HasCompactSupport tt)
    (htsW : tsupport χ ⊆ W)
    (hχ'1 : ∀ x ∈ W, χ' x = 1) (hσ1 : ∀ x ∈ W, σc x = 1)
    (htt1 : ∀ x ∈ W, tt x = (Real.tan (x 1) : ℂ))
    (φ : SchwartzMap E2 ℂ) :
    (∫ x, (χ x * (Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 (φ : E2 → ℂ)) x + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 (φ : E2 → ℂ)) x)) * V x)
      = - (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (5 * σc y) * φ y) x) * V x)
        + (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (σc y * tt y) * φ y) x) * V x)
        - (∫ x, (χ x * (6 * σc x) * φ x) * V x)
        + (∫ x, (χ' x * (((Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 χ) x + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 χ) x) - 5 * Work.EllipticEst.InteriorRegularity.d0 χ x + tt x * Work.EllipticEst.InteriorRegularity.d1 χ x) * φ x)) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d0 χ y) * φ y) x) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d1 χ y) * φ y) x) * V x)
        - (∫ x, (χ x * φ x) * G x) := by
  set φc : E2 → ℂ := (φ : E2 → ℂ) with hφc
  have hφs : ∀ n : ℕ, ContDiff ℝ n φc := by
    intro n
    rw [hφc]
    exact φ.smooth n
  -- the test function `ψ = χ · φc`, admissible for the weak identity
  have hψsm : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => χ y * φc y) :=
    fun n => (hχs n).mul (hφs n)
  have hψcs : HasCompactSupport (fun y : E2 => χ y * φc y) := hχc.mul_right
  have hχW : tsupport χ ⊆ stripE := htsW.trans hWsub
  have hψsupp : tsupport (fun y : E2 => χ y * φc y) ⊆ stripE :=
    (tsupport_mul_subset_left (f := χ) (g := φc)).trans hχW
  have hwk := hweak (fun y : E2 => χ y * φc y) hψsm hψcs hψsupp
  -- integrability of `a · V` for `a` supported in the strip
  have hVint : ∀ {a : E2 → ℂ}, Continuous a → HasCompactSupport a → tsupport a ⊆ stripE →
      Integrable (fun x : E2 => a x * V x) := by
    intro a ha hac hs
    exact integrable_mul_of_locallyIntegrableOn hV ha hac hs
  -- smoothness of the auxiliaries
  have h5σφ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (5 * σc y) * φc y) :=
    fun n => ((contDiff_const (c := (5 : ℂ))).mul (hσs n)).mul (hφs n)
  have hσtt : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (σc y * tt y) * φc y) :=
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
  -- continuity of the eight coefficients
  have hc1 : Continuous (fun x : E2 => χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) :=
    (hχs 0).continuous.mul (((Loc.contDiff_d0 (Loc.contDiff_d0 hφs) 0).continuous).add
      ((Loc.contDiff_d1 (Loc.contDiff_d1 hφs) 0).continuous))
  have hc2 : Continuous (fun x : E2 => χ x * d0 (fun y => (5 * σc y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d0 h5σφ 0).continuous)
  have hc3 : Continuous (fun x : E2 => χ x * d1 (fun y => (σc y * tt y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d1 hσtt 0).continuous)
  have hc4 : Continuous (fun x : E2 => χ x * (6 * σc x) * φc x) :=
    ((hχs 0).continuous.mul ((contDiff_const (c := (6 : ℂ))).mul (hσs 0)).continuous).mul
      (hφs 0).continuous
  have hc5 : Continuous (fun x : E2 => χ' x *
      (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) :=
    (hχ's 0).continuous.mul (((hρ 0).continuous).mul (hφs 0).continuous)
  have hc6 : Continuous (fun x : E2 => χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d0 h2d0χ 0).continuous)
  have hc7 : Continuous (fun x : E2 => χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d1 h2d1χ 0).continuous)
  -- the corresponding support conditions
  have hf1s : tsupport (fun x : E2 => χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) ⊆ stripE :=
    (tsupport_mul_subset_left (f := χ)
      (g := fun x : E2 => d0 (d0 φc) x + d1 (d1 φc) x)).trans hχW
  have hf2s : tsupport (fun x : E2 => χ x * d0 (fun y => (5 * σc y) * φc y) x) ⊆ stripE :=
    (tsupport_mul_subset_left (f := χ)
      (g := d0 (fun y : E2 => (5 * σc y) * φc y))).trans hχW
  have hf3s : tsupport (fun x : E2 => χ x * d1 (fun y => (σc y * tt y) * φc y) x) ⊆ stripE :=
    (tsupport_mul_subset_left (f := χ)
      (g := d1 (fun y : E2 => (σc y * tt y) * φc y))).trans hχW
  have hf4s : tsupport (fun x : E2 => χ x * (6 * σc x) * φc x) ⊆ stripE :=
    ((tsupport_mul_subset_left (f := fun x : E2 => χ x * (6 * σc x))
        (g := φc)).trans
      ((tsupport_mul_subset_left (f := χ) (g := fun x : E2 => 6 * σc x)).trans hχW))
  have hf5s : tsupport (fun x : E2 => χ' x *
      (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) ⊆ stripE :=
    (tsupport_mul_subset_right (f := χ')
        (g := fun x : E2 =>
          ((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)).trans
      ((tsupport_mul_subset_left
          (f := fun x : E2 => (d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x)
          (g := φc)).trans
        ((tsupport_rho_subset χ tt).trans hχW))
  have hf6s : tsupport (fun x : E2 => χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) ⊆ stripE :=
    (tsupport_mul_subset_right (f := χ')
        (g := d0 (fun y : E2 => (2 * d0 χ y) * φc y))).trans
      ((tsupport_d0_subset (fun y : E2 => (2 * d0 χ y) * φc y)).trans
        ((tsupport_mul_subset_left (f := fun y : E2 => 2 * d0 χ y) (g := φc)).trans
          ((tsupport_mul_subset_right (f := fun _ : E2 => (2 : ℂ)) (g := d0 χ)).trans
            ((tsupport_d0_subset χ).trans hχW))))
  have hf7s : tsupport (fun x : E2 => χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) ⊆ stripE :=
    (tsupport_mul_subset_right (f := χ')
        (g := d1 (fun y : E2 => (2 * d1 χ y) * φc y))).trans
      ((tsupport_d1_subset (fun y : E2 => (2 * d1 χ y) * φc y)).trans
        ((tsupport_mul_subset_left (f := fun y : E2 => 2 * d1 χ y) (g := φc)).trans
          ((tsupport_mul_subset_right (f := fun _ : E2 => (2 : ℂ)) (g := d1 χ)).trans
            ((tsupport_d1_subset χ).trans hχW))))
  -- the `tt`-version of the last term
  set K' : E2 → ℂ := fun x =>
      - d0 (d0 (fun y => χ y * φc y)) x - d1 (d1 (fun y => χ y * φc y)) x
      - 5 * d0 (fun y => χ y * φc y) x
      + tt x * d1 (fun y => χ y * φc y) x
      + ((tt x) ^ 2 - 5) * (fun y => χ y * φc y) x with hK'def
  have hK'tsupp : tsupport K' ⊆ stripE := by
    rw [hK'def]
    exact (tsupport_combination_subset tt (fun y : E2 => χ y * φc y)).trans
      ((tsupport_mul_subset_left (f := χ) (g := φc)).trans hχW)
  have hKopUnfold : Kop (fun y : E2 => χ y * φc y) = fun z : E2 =>
      - d0 (d0 (fun y => χ y * φc y)) z - d1 (d1 (fun y => χ y * φc y)) z
      - 5 * d0 (fun y => χ y * φc y) z
      + (Real.tan (z 1) : ℂ) * d1 (fun y => χ y * φc y) z
      + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (fun y => χ y * φc y) z := rfl
  have hKopEq : ∀ x : E2, Kop (fun y => χ y * φc y) x = K' x := by
    intro x
    by_cases hx : x ∈ W
    · have hT : (Real.tan (x 1) : ℂ) = tt x := (htt1 x hx).symm
      have hT2 : (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) = (tt x) ^ 2 - 5 := by
        rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat, hT]
      simp only [hK'def, hKopUnfold]
      rw [hT, hT2]
    · have hxt : x ∉ tsupport χ := fun h => hx (htsW h)
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxt
      have hWc : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 :=
        fun y hy => image_eq_zero_of_notMem_tsupport hy
      have hevχ : χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
        Filter.eventuallyEq_of_mem (hWc.mem_nhds hxt) hχ0W
      have hevψ : (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] (0 : E2 → ℂ) := by
        filter_upwards [hevχ] with y hy
        simp [hy]
      have hd1ψ : d1 (fun y => χ y * φc y) x = 0 :=
        Loc.d1_eq_zero_of_eventuallyEq_zero hevψ
      simp only [hK'def, hKopUnfold]
      rw [hχx, hd1ψ]
      ring
  have hc8 : Continuous K' := by
    rw [hK'def]
    have h1 : Continuous (fun x : E2 => d0 (d0 (fun y => χ y * φc y)) x) :=
      (Loc.contDiff_d0 (f := d0 (fun y => χ y * φc y))
        (Loc.contDiff_d0 (f := fun y => χ y * φc y) hψsm) 0).continuous
    have h2 : Continuous (fun x : E2 => d1 (d1 (fun y => χ y * φc y)) x) :=
      (Loc.contDiff_d1 (f := d1 (fun y => χ y * φc y))
        (Loc.contDiff_d1 (f := fun y => χ y * φc y) hψsm) 0).continuous
    have h3 : Continuous (fun x : E2 => d0 (fun y => χ y * φc y) x) :=
      (Loc.contDiff_d0 (f := fun y => χ y * φc y) hψsm 0).continuous
    have h4 : Continuous (fun x : E2 => d1 (fun y => χ y * φc y) x) :=
      (Loc.contDiff_d1 (f := fun y => χ y * φc y) hψsm 0).continuous
    have httc' : Continuous tt := (htts 0).continuous
    have h7 : Continuous (fun y : E2 => χ y * φc y) := (hψsm 0).continuous
    have h9 : Continuous (fun x : E2 => (tt x) ^ 2 - 5) :=
      (httc'.pow 2).sub continuous_const
    exact ((((h1.neg.sub h2).sub (continuous_const.mul h3)).add (httc'.mul h4)).add
      (h9.mul h7))
  have hcs8 : HasCompactSupport K' := by
    rw [hK'def]
    have h1 : HasCompactSupport (fun x : E2 => d0 (d0 (fun y => χ y * φc y)) x) :=
      Loc.hasCompactSupport_d0 (Loc.hasCompactSupport_d0 hψcs)
    have h2 : HasCompactSupport (fun x : E2 => d1 (d1 (fun y => χ y * φc y)) x) :=
      Loc.hasCompactSupport_d1 (Loc.hasCompactSupport_d1 hψcs)
    have h3 : HasCompactSupport (fun x : E2 => d0 (fun y => χ y * φc y) x) :=
      Loc.hasCompactSupport_d0 hψcs
    have h4 : HasCompactSupport (fun x : E2 => d1 (fun y => χ y * φc y) x) :=
      Loc.hasCompactSupport_d1 hψcs
    exact ((((h1.neg.sub h2).sub h3.mul_left).add h4.mul_left).add hψcs.mul_left)
  -- the eight summands are integrable
  have hInt1 : Integrable
      (fun x : E2 => (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x) :=
    hVint hc1 hχc.mul_right hf1s
  have hInt2 : Integrable
      (fun x : E2 => (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x) :=
    hVint hc2 hχc.mul_right hf2s
  have hInt3 : Integrable
      (fun x : E2 => (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x) :=
    hVint hc3 hχc.mul_right hf3s
  have hInt4 : Integrable (fun x : E2 => (χ x * (6 * σc x) * φc x) * V x) :=
    hVint hc4 ((hχc.mul_right (f' := fun x : E2 => 6 * σc x)).mul_right (f' := φc)) hf4s
  have hInt5 : Integrable (fun x : E2 =>
      (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x) :=
    hVint hc5 hχ'c.mul_right hf5s
  have hInt6 : Integrable
      (fun x : E2 => (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x) :=
    hVint hc6 hχ'c.mul_right hf6s
  have hInt7 : Integrable
      (fun x : E2 => (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x) :=
    hVint hc7 hχ'c.mul_right hf7s
  have hInt8 : Integrable (fun x : E2 => K' x * V x) := hVint hc8 hcs8 hK'tsupp
  -- the pointwise identity
  set B : E2 → ℂ := fun x =>
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σc y) * φc y) x
      - χ x * d1 (fun y => (σc y * tt y) * φc y) x
      + χ x * (6 * σc x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + K' x with hBdef
  have hBzero : ∀ x : E2, B x = 0 := by
    intro x
    simp only [hBdef]
    rw [← hKopEq x]
    exact Loc.pointwise_identity hW htsW hWsub hχs hχ's hσs htts hφs hσ1 htt1 hχ'1 x
  have hzero : ∫ x, B x * V x = 0 := by simp [hBzero]
  have hlin : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σc x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, K' x * V x) := by
    have hcongr : ∫ x, B x * V x
        = ∫ x, ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x
            + (χ x * (6 * σc x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K' x * V x) := by
      rw [show (fun x : E2 => B x * V x)
          = (fun x => ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x
            + (χ x * (6 * σc x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K' x * V x)) from funext (fun x => by simp only [hBdef]; ring)]
    rw [hcongr]
    exact Loc.integral_lin8 hInt1 hInt2 hInt3 hInt4 hInt5 hInt6 hInt7 hInt8
  have hIK : (∫ x, K' x * V x) = (∫ x, (χ x * φc x) * G x) := by
    rw [show (fun x : E2 => K' x * V x)
        = (fun x => V x * Kop (fun y => χ y * φc y) x) from
      funext (fun x => by rw [← hKopEq x]; ring)]
    rw [hwk]
    rw [show (fun x : E2 => G x * (χ x * φc x)) = (fun x => (χ x * φc x) * G x) from
      funext (fun x => by ring)]
  have h1 : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σc x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) := by
    rw [hlin, hIK]
  have h2 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σc x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) = 0 := by
    rw [← h1]
    exact hzero
  have h3 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
      = - (∫ x, (χ x * d0 (fun y => (5 * σc y) * φc y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φc y) x) * V x)
        - (∫ x, (χ x * (6 * σc x) * φc x) * V x)
        + (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        - (∫ x, (χ x * φc x) * G x) := by
    linear_combination h2
  exact h3

end Work.EllipticEst.InteriorRegularity.Q0
