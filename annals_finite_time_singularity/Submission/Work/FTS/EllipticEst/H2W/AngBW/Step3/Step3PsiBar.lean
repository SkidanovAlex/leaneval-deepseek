import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.SliceMain
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.SlicePsiMem
import Submission.Work.FTS.EllipticEst.Honest.psi_boundary_vanish
import Submission.Work.FTS.EllipticEst.Honest.slice_ident_honest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The `z`-assembly.**  If the slicewise estimate
`∫ sin²θ (∂_θ(Ψ/cos θ))² σ ≤ ∫ (∂_θθΨ)² σ + 2 ∫ Ψ² σ` holds at every `z > 0`, then the
honest `HkSq`-bound holds with constant `2`. -/
theorem step3PsiBar_of_slice_le (Ψ : ℝ → ℝ → ℝ)
    (hmemΨ : Work.Spaces.HkMem 0 0 Ψ)
    (hmemB : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ))
    (hmemG : Work.Spaces.HkMem 0 0 (fun z θ => Real.sin θ
      * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
    (hsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
          * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ)
        ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) :
    Real.sqrt (Work.Spaces.HkSq 0 0 (fun z θ => Real.sin θ
        * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  set G : ℝ → ℝ → ℝ := fun z θ => Real.sin θ
    * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ with hG
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  have hmemG' : Work.Spaces.HkMem 0 0 G := hmemG
  have hmemB' : Work.Spaces.HkMem 0 0 B := hmemB
  -- the pointwise (in `z`) inequality, weighted by `w²`
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h | h
    · subst h
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      simp [hw0]
    · have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
          ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
        have hG2 : ∀ θ : ℝ, (G z θ) ^ 2 * sg θ = (Real.sin θ) ^ 2
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ := by
          intro θ; rw [hG]; ring
        have hB2 : ∀ θ : ℝ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ
            = (B z θ) ^ 2 * sg θ := by
          intro θ; rw [hB]
        calc (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
            = (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
                * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ) :=
              MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hG2 θ)
          _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := hsl z h
          _ = (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
              rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                  = ∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ from
                MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hB2 θ)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- integrability of the three `z`-integrands
  have hintG : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemG'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemG' hz
  have hintB : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemB'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemB' hz
  have hintP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemΨ.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemΨ hz
  have hintR : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) Work.Spaces.Iz := by
    refine (hintB.add (hintP.const_mul 2)).congr_fun (fun z _ => ?_) measurableSet_Ici
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      ≤ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) :=
    MeasureTheory.setIntegral_mono_on hintG hintR measurableSet_Ici hpt
  have eL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      = Work.Spaces.HkSq 0 0 G := (hkSq_zero_eq_sliceW hmemG').symm
  have eR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
      = Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ))
          + 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
      rw [show (fun z => (Work.Spaces.w z) ^ 2
            * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
              + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
          = (fun z => (Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) from by
        funext z; ring]
      rw [MeasureTheory.integral_add hintB (hintP.const_mul 2),
        MeasureTheory.integral_const_mul]
    rw [hsplit, hkSq_zero_eq_sliceW hmemB', hkSq_zero_eq_sliceW hmemΨ]
  have hmain : Work.Spaces.HkSq 0 0 G ≤ Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    rw [← eL, ← eR]
    exact hmono
  have hBnn : 0 ≤ Work.Spaces.HkSq 0 0 B := HkSq_zero_nonneg 0 B
  have hPnn : 0 ≤ Work.Spaces.HkSq 0 0 Ψ := HkSq_zero_nonneg 0 Ψ
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sqrt_two_lt_three_halves
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 Ψ))
  calc Real.sqrt (Work.Spaces.HkSq 0 0 G)
      ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ) :=
        Real.sqrt_le_sqrt hmain
    _ ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B) + Real.sqrt (2 * Work.Spaces.HkSq 0 0 Ψ) :=
        sqrt_add_le_sqrt_add_sqrt hBnn (by positivity)
    _ = Real.sqrt (Work.Spaces.HkSq 0 0 B)
          + Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) + Real.sqrt (Work.Spaces.HkSq 0 0 B)) := by
        linarith [Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 B)]

/-- **The `I₄`/Ψ̄-bound of Step 2 of `prop:H2`.**  Under the honest slice hypotheses, the
`σ`-weighted `L²`-norm of `sin θ · ∂_θ(Ψ/cos θ)` is controlled by the norms of `Ψ` and of
`∂_θθΨ` (the positivity `I_{4,2}` of Elgindi, Annals 194 (2021), tex 890--905).

Route hint: with `ψ = Ψ/cos θ`, `s = sin(2θ)`, `σ = s^{-η}`, the two integrations by parts of
`Work.FTS.EllipticEst.TanTheta.slice_ident` (`TanTheta/slice_ident.lean`, proved; it needs `u`
of class `C²` on a neighbourhood of `[0,π/2]` with `u(π/2) = 0`) give the slicewise identity
`∫ ((1-η)/2·cos 2θ + 2 sin²θ)(ψ')² σ = -∫ sinθ ψ' Ψ'' σ + ((1-η)/2)∫ cos 2θ ψ² σ`.
Its coefficient is `(1-η)/2 + (1+η)sin²θ ≥ (1+η)sin²θ`, so Cauchy--Schwarz in `θ` and Young in
the two slice quantities `y = (∫ sin²θ ψ'² σ)^{1/2}` and `x = (∫(Ψ'')² σ)^{1/2}` give
`y² ≤ C (y·x + ∫ |cos 2θ| ψ² σ)`; multiplying by `w z ^ 2` and integrating in `z` gives the
statement once `∫|cos 2θ|ψ²σ` is controlled (in the strong class this is `I4_psi_bounds`/
`hardy`-type; here it must come from `HkMem (∂_θθΨ)` and `HkMem Ψ`, e.g. via a weighted Agmon
inequality on the slices — note `∫cos2θ ψ² σ` is very negative near `π/2`, not bounded by
`4∫Ψ²σ`).

The honest class (no `SmoothNbhd`) is what makes this non-trivial: the boundary terms of the
two integrations by parts and the integrability of `sinθ cosθ ψ ψ' σ`, `sinθ cosθ ψ' ψ'' σ`
must be recovered from the three `HkMem` hypotheses (a `θ`-truncation `Ψ·χ_ε` argument in
which `slice_ident` applies verbatim, or weighted one-dimensional Hardy/Agmon inequalities on
the slices).  The hypothesis `HkMem (sinθ · ψ')` is not needed for the *truth* of the estimate
but it removes the degenerate case in which a slice of `sinθ ψ'` fails to be integrable, and
is available to the caller. -/
theorem step3PsiBar : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem 0 0 Ψ →
    Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ) →
    Work.Spaces.HkMem 0 0
      (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) →
    Real.sqrt (Work.Spaces.HkSq 0 0
        (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Ψ hsm h0 h1 hmemΨ hmemB hmemG
  refine step3PsiBar_of_slice_le Ψ hmemΨ hmemB hmemG ?_
  intro z hz
  -- the slice hypotheses
  have hu : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice_of_hsm hsm hz 2
  have hB : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (integrableOn_sq_mul_sig_of_hkMem hmemΨ hz).mono_set Set.Ioo_subset_Icc_self
  have hX : IntegrableOn (fun θ => (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemB hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * sg θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ ^ 2 * sg θ
    rw [pthIter_two_apply]
  have hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemG hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ
      = (Real.sin θ) ^ 2 * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ
    rw [pth_div_apply]
    ring
  obtain ⟨hA, hA'⟩ := slice_psi_mem (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    psi_boundary_vanish (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
  have hident := slice_ident_honest (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
    hv1 hv2 hv3 hv4
  have hpth : ∀ θ : ℝ, Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := fun θ => pth_div_apply Ψ z θ
  have hpth2 : ∀ θ : ℝ, Work.Spaces.pthIter 2 Ψ z θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ := fun θ => pthIter_two_apply Ψ z θ
  simpa only [hpth, hpth2] using
    slice_sq_le_of_ident (fun θ => Ψ z θ) hu hA hA' hB hX hY hident


end Work.FTS.EllipticEst.H2W.AngBW.S3
