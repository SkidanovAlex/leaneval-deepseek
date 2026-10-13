import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-! ## Helper lemmas

`IP g h = ∫_z ∫_θ g z θ * h z θ * w2 z * sig θ` with `w2 z = w z ^ 2` and
`sig θ = sin(2θ)^{-η}`.  The proof of the Cauchy–Schwarz inequality for `IP` is Cauchy–Schwarz
twice: on each angular slice (Hölder with `p = q = 2`, `slice_abs_le_aux`) and then in the
radial variable (`z_sqrt_aux`).  Both steps only need the a.e. strong measurability of the
slice functions: `aesm_slice_of_smoothNbhd` for a `SmoothNbhd` profile and `measurable_sig`
for the angular weight. -/

/-- The angular weight `sig θ = sin(2θ)^{-η}` is measurable. -/
theorem measurable_sig : Measurable sig := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- For `z ∈ Iz`, the angular slice `θ ↦ f z θ` of a function smooth on an open neighbourhood
of the closed quadrant is continuous on `Iθ`. -/
theorem continuousOn_slice_Iθ {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ := by
  intro θ hθ
  have hz' : (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioi]; rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
    · rw [Set.mem_Ioo]
      exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
    hf.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hz')
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-- For `z ∈ Iz`, the angular slice of a `SmoothNbhd` profile is a.e. strongly measurable for
the measure `volume.restrict Iθ`. -/
theorem aesm_slice_of_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
  (continuousOn_slice_Iθ hf hz).aestronglyMeasurable measurableSet_Icc

/-- **Weighted Cauchy–Schwarz on a single slice** (Hölder with `p = q = 2`).

For `F, G, κ` a.e. strongly measurable with `κ ≥ 0` on the measurable set `s` and `F²κ`, `G²κ`
integrable on `s`,

  `|∫_s F G κ| ≤ √(∫_s F²κ) · √(∫_s G²κ)`.

Route: apply `Work.Coercivity.holder_two_mul` to `u = |F|√κ`, `v = |G|√κ`, whose squares are
`F²κ`, `G²κ`, and note `|∫_s FGκ| ≤ ∫_s |FGκ| = ∫_s u v`. -/
theorem slice_abs_le_aux {s : Set ℝ} (hs : MeasurableSet s) {F G κ : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict s))
    (hG : AEStronglyMeasurable G (volume.restrict s))
    (hκ : AEStronglyMeasurable κ (volume.restrict s))
    (hκnn : ∀ θ ∈ s, 0 ≤ κ θ)
    (hF2 : IntegrableOn (fun θ => F θ * F θ * κ θ) s)
    (hG2 : IntegrableOn (fun θ => G θ * G θ * κ θ) s) :
    |∫ θ in s, F θ * G θ * κ θ|
      ≤ Real.sqrt (∫ θ in s, F θ * F θ * κ θ) * Real.sqrt (∫ θ in s, G θ * G θ * κ θ) := by
  have hFabs : AEStronglyMeasurable (fun θ => |F θ|) (volume.restrict s) := by
    simpa only [Real.norm_eq_abs] using hF.norm
  have hGabs : AEStronglyMeasurable (fun θ => |G θ|) (volume.restrict s) := by
    simpa only [Real.norm_eq_abs] using hG.norm
  have hsqr : AEStronglyMeasurable (fun θ => Real.sqrt (κ θ)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hκ
  have hu : AEStronglyMeasurable (fun θ => |F θ| * Real.sqrt (κ θ)) (volume.restrict s) :=
    hFabs.mul hsqr
  have hv : AEStronglyMeasurable (fun θ => |G θ| * Real.sqrt (κ θ)) (volume.restrict s) :=
    hGabs.mul hsqr
  have hu2 : Integrable (fun θ => (|F θ| * Real.sqrt (κ θ)) ^ 2) (volume.restrict s) := by
    refine hF2.congr ?_
    filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
    show F θ * F θ * κ θ = (|F θ| * Real.sqrt (κ θ)) ^ 2
    rw [mul_pow, sq_abs, Real.sq_sqrt hθ]
    ring
  have hv2 : Integrable (fun θ => (|G θ| * Real.sqrt (κ θ)) ^ 2) (volume.restrict s) := by
    refine hG2.congr ?_
    filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
    show G θ * G θ * κ θ = (|G θ| * Real.sqrt (κ θ)) ^ 2
    rw [mul_pow, sq_abs, Real.sq_sqrt hθ]
    ring
  have hcs := Work.Coercivity.holder_two_mul (volume.restrict s)
    (fun θ => |F θ| * Real.sqrt (κ θ)) (fun θ => |G θ| * Real.sqrt (κ θ)) hu hv hu2 hv2
  have hbound : ∀ θ ∈ s,
      ‖F θ * G θ * κ θ‖ ≤ (|F θ| * Real.sqrt (κ θ)) * (|G θ| * Real.sqrt (κ θ)) := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hκnn θ hθ)]
    rw [show (|F θ| * Real.sqrt (κ θ)) * (|G θ| * Real.sqrt (κ θ))
          = |F θ| * |G θ| * (Real.sqrt (κ θ) * Real.sqrt (κ θ)) from by ring,
      Real.mul_self_sqrt (hκnn θ hθ)]
  have hAeq : (∫ θ in s, (|F θ| * Real.sqrt (κ θ)) ^ 2) = ∫ θ in s, F θ * F θ * κ θ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
    show (|F θ| * Real.sqrt (κ θ)) ^ 2 = F θ * F θ * κ θ
    rw [mul_pow, sq_abs, Real.sq_sqrt hθ]
    ring
  have hBeq : (∫ θ in s, (|G θ| * Real.sqrt (κ θ)) ^ 2) = ∫ θ in s, G θ * G θ * κ θ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
    show (|G θ| * Real.sqrt (κ θ)) ^ 2 = G θ * G θ * κ θ
    rw [mul_pow, sq_abs, Real.sq_sqrt hθ]
    ring
  calc |∫ θ in s, F θ * G θ * κ θ|
      ≤ ∫ θ in s, (|F θ| * Real.sqrt (κ θ)) * (|G θ| * Real.sqrt (κ θ)) :=
        le_trans (abs_integral_le_integral_abs (f := fun θ => F θ * G θ * κ θ)
            (μ := volume.restrict s))
          (integral_mono_of_nonneg
            (f := fun θ => |F θ * G θ * κ θ|)
            (g := fun θ => (|F θ| * Real.sqrt (κ θ)) * (|G θ| * Real.sqrt (κ θ)))
            (Eventually.of_forall fun θ => abs_nonneg _) hcs.1
            (ae_restrict_of_forall_mem hs hbound))
    _ = |∫ θ in s, (|F θ| * Real.sqrt (κ θ)) * (|G θ| * Real.sqrt (κ θ))| :=
        (abs_of_nonneg (integral_nonneg fun θ =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
            (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))).symm
    _ ≤ Real.sqrt (∫ θ in s, (|F θ| * Real.sqrt (κ θ)) ^ 2)
          * Real.sqrt (∫ θ in s, (|G θ| * Real.sqrt (κ θ)) ^ 2) := hcs.2
    _ = Real.sqrt (∫ θ in s, F θ * F θ * κ θ)
          * Real.sqrt (∫ θ in s, G θ * G θ * κ θ) := by rw [hAeq, hBeq]

/-- **The radial (`z`) Cauchy–Schwarz step.**  For `A`, `B` integrable on `Iz` and nonnegative
there,

  `∫_z √A · √B ≤ √(∫_z A) · √(∫_z B)`. -/
theorem z_sqrt_aux {A B : ℝ → ℝ}
    (hA : IntegrableOn A Work.Spaces.Iz) (hB : IntegrableOn B Work.Spaces.Iz)
    (hAn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ A z) (hBn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ B z) :
    (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, A z)
        * Real.sqrt (∫ z in Work.Spaces.Iz, B z) := by
  have hAsq : Integrable (fun z => (Real.sqrt (A z)) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine hA.congr ?_
    filter_upwards [ae_restrict_of_forall_mem measurableSet_Ici hAn] with z hz
    exact (Real.sq_sqrt hz).symm
  have hBsq : Integrable (fun z => (Real.sqrt (B z)) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine hB.congr ?_
    filter_upwards [ae_restrict_of_forall_mem measurableSet_Ici hBn] with z hz
    exact (Real.sq_sqrt hz).symm
  have hcs := Work.Coercivity.holder_two_mul (volume.restrict Work.Spaces.Iz)
    (fun z => Real.sqrt (A z)) (fun z => Real.sqrt (B z))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable) hAsq hBsq
  have hAeq : (∫ z in Work.Spaces.Iz, (Real.sqrt (A z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, A z := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_forall_mem measurableSet_Ici hAn] with z hz
    exact Real.sq_sqrt hz
  have hBeq : (∫ z in Work.Spaces.Iz, (Real.sqrt (B z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, B z := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_forall_mem measurableSet_Ici hBn] with z hz
    exact Real.sq_sqrt hz
  calc (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z))
      = |∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)| :=
        (abs_of_nonneg (integral_nonneg fun z =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (Real.sqrt (A z)) ^ 2)
          * Real.sqrt (∫ z in Work.Spaces.Iz, (Real.sqrt (B z)) ^ 2) := hcs.2
    _ = Real.sqrt (∫ z in Work.Spaces.Iz, A z)
          * Real.sqrt (∫ z in Work.Spaces.Iz, B z) := by rw [hAeq, hBeq]

/-! ## The main statement -/

/-- **Cauchy–Schwarz for the angular-weight pairing `IP`, with an explicit dominating
function for the `z`-integrand.**

For smooth `g h` whose diagonal pairings are honest (`IPMem g g`, `IPMem h h`): first,
`|IP g h| ≤ √(IP g g) · √(IP h h)`; second, there is an integrable `Gd` with
`|∫_θ g z θ h z θ w²(z) σ θ| ≤ Gd z` for every `z ∈ Iz` and
`∫_z Gd ≤ √(IP g g) · √(IP h h)` — the dominating function is
`Gd z = √(w²(z) ∫_θ g²σ) · √(w²(z) ∫_θ h²σ)`.

Route: the slicewise Cauchy–Schwarz
`|∫_θ g h σ| ≤ √(∫_θ g²σ)·√(∫_θ h²σ)` (either `Work.FTS.H2.CS1D` with `A = |g|√σ`,
`B = |h|√σ`, or the quadratic argument), multiplied by `w²(z) ≥ 0`; then Cauchy–Schwarz in
the `z`-variable applied to `√(w²∫g²σ)` and `√(w²∫h²σ)`, whose squares integrate to
`IP g g`, `IP h h` by `MeasureTheory.integral_mul_const`.  Measurability of the slice
functions `z ↦ ∫_θ g²σ` follows from the joint measurability of the integrands
(`MeasureTheory.StronglyMeasurable.integral_prod_right` or the `lintegral` analogue).
Note `IP`'s integrand is `g z θ * h z θ * w2 z * sig θ` with `w2 = w²`,
`sig θ = sin(2θ)^{-η}`.) -/
theorem IP_abs_le_of_mem {g h : ℝ → ℝ → ℝ} (hgm : Work.Spaces.SmoothNbhd g)
    (hhm : Work.Spaces.SmoothNbhd h) (hg : IPMem g g) (hh : IPMem h h) :
    |IP g h| ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h)
      ∧ ∃ Gd : ℝ → ℝ, MeasureTheory.IntegrableOn Gd Work.Spaces.Iz
          ∧ (∀ z ∈ Work.Spaces.Iz,
              |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ| ≤ Gd z)
          ∧ (∫ z in Work.Spaces.Iz, Gd z) ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h) := by
  -- the three slice integrals: the two diagonal ones and the pairing
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ with hAdef
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * w2 z * sig θ with hBdef
  set C : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ with hCdef
  have hAint : IntegrableOn A Work.Spaces.Iz := by rw [hAdef]; exact hg.2
  have hBint : IntegrableOn B Work.Spaces.Iz := by rw [hBdef]; exact hh.2
  have hAnn : ∀ z, 0 ≤ A z := by
    intro z
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (mul_self_nonneg (g z θ)) (w2_nonneg z)) (sig_nonneg hθ))
  have hBnn : ∀ z, 0 ≤ B z := by
    intro z
    rw [hBdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (mul_self_nonneg (h z θ)) (w2_nonneg z)) (sig_nonneg hθ))
  have hIPgg : IP g g = ∫ z in Work.Spaces.Iz, A z := by rw [IP, hAdef]
  have hIPhh : IP h h = ∫ z in Work.Spaces.Iz, B z := by rw [IP, hBdef]
  have hIPgh : IP g h = ∫ z in Work.Spaces.Iz, C z := by rw [IP, hCdef]
  -- the dominating function `Gd z = √(A z) · √(B z)`
  have hGdint : IntegrableOn (fun z => Real.sqrt (A z) * Real.sqrt (B z)) Work.Spaces.Iz :=
    Work.Coercivity.integrable_sqrt_mul_sqrt (volume.restrict Work.Spaces.Iz) A B
      hAint hBint hAnn hBnn
  -- the pointwise (slicewise) bound
  have hpoint : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ|
        ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have hCeq : (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ)
        = ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * (w2 z * sig θ) :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hAeq : A z = ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * (w2 z * sig θ) := by
      rw [hAdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hBeq : B z = ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * (w2 z * sig θ) := by
      rw [hBdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hCeq, hAeq, hBeq]
    exact slice_abs_le_aux measurableSet_Icc (aesm_slice_of_smoothNbhd hgm hz)
      (aesm_slice_of_smoothNbhd hhm hz)
      ((measurable_sig.const_mul (w2 z)).aestronglyMeasurable)
      (fun θ hθ => mul_nonneg (w2_nonneg z) (sig_nonneg hθ))
      ((hg.1 z hz).congr (Eventually.of_forall fun θ => by ring))
      ((hh.1 z hz).congr (Eventually.of_forall fun θ => by ring))
  -- the bound on the `z`-integral of the dominating function
  have hGdle : (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z))
      ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h) := by
    calc (∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z))
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz, A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, B z) :=
          z_sqrt_aux hAint hBint (fun z _ => hAnn z) (fun z _ => hBnn z)
      _ = Real.sqrt (IP g g) * Real.sqrt (IP h h) := by rw [← hIPgg, ← hIPhh]
  -- the same bound with `C` in place of the explicit integral
  have hC_le : ∀ z ∈ Work.Spaces.Iz,
      |C z| ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    rw [hCdef]
    exact hpoint z hz
  refine ⟨?_, (fun z => Real.sqrt (A z) * Real.sqrt (B z)), hGdint, hpoint, hGdle⟩
  calc |IP g h| = |∫ z in Work.Spaces.Iz, C z| := by rw [hIPgh]
    _ ≤ ∫ z in Work.Spaces.Iz, |C z| :=
        abs_integral_le_integral_abs (f := C) (μ := volume.restrict Work.Spaces.Iz)
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z) :=
        integral_mono_of_nonneg (f := fun z => |C z|)
          (g := fun z => Real.sqrt (A z) * Real.sqrt (B z))
          (Eventually.of_forall fun z => abs_nonneg _) hGdint
          (ae_restrict_of_forall_mem measurableSet_Ici hC_le)
    _ ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h) := hGdle

end Work.FTS.EllipticEst.AngSecond

