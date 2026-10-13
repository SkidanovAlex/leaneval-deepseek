/-
# Coercivity of the `H^k`-norm: `|f|²_{H^{k+1}} ≤ |f|²_{H^k} + |D_θf|²_{H^k} + |D_zf|²_{H^k}`

For a function `f` which is smooth on a neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd f`) and lies in `ℋ^{k+1}` (`Work.Spaces.HkMem α (k+1) f`), the
squared `H^{k+1}`-norm is dominated by the squared `H^k`-norms of `f`, `D_θ f` and `D_z f`:

  `HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (Dth f) + HkSq α k (Dz f)`

for `k ≥ 1`.  This is the elementary "one more derivative is what the previous level
already paid for" step behind the inductive construction of the inner products `ℋ^k` of
the paper (§"Higher order derivatives and the inner product on `ℋ^k`").

The proof has two halves.

**Pointwise.**  Write `HkIntegrand α k f = P_k + M_k`, where
`P_k = ∑_{i≤k} (D_z^i f · w/√sin^{η})²` is the *pure* family and
`M_k = ∑_{1≤i, i+j≤k} (D_z^j D_θ^i f · W)²` the *mixed* family.
* The last pure summand `(D_z^{k+1} f)^2` of `P_{k+1}` is the `i = k` summand of the
  pure family `P_k(D_z f)` of the `D_z`-integrand, since `D_z^k (D_z f) = D_z^{k+1} f`.
* The mixed summands of `M_{k+1}` with `i + j ≤ k` are literally summands of `M_k`.
* The remaining mixed summands have `i + j = k+1`, `i ≥ 1`.  Because `D_z` and `D_θ`
  commute (`Work.Spaces.mixed_comm`, valid on the closed quadrant by `SmoothNbhd f`),
  the summand with `j ≥ 1` is the `(i, j-1)`-summand of `M_k(D_z f)`, and the one with
  `j = 0` — which is `D_θ^{k+1} f`, so that `i = k+1` — is the `(k,0)`-summand of
  `M_k(D_θ f)`; here `1 ≤ k` is used.
That pointwise comparison is `Work.Coercivity.HkIntegrand_succ_le_sum`.

**Integration.**  Under `HkMem` hypotheses the pointwise comparison passes to the
iterated integrals, because the dominating integrands have honest integrals and the
integral of a sum of `HkMem`-integrands splits (`setIntegral_iterated_add`); this is
`HkSq_le_sum_of_integrand_le`.  `HkMem α k f` and the memberships
`HkMem α k (D_θ f)`, `HkMem α k (D_z f)` follow from `HkMem α (k+1) f` by
`Work.Coercivity.HkMem_mono` and `Work.Coercivity.HkMem_dth`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.Coercivity.HkIntegrand_succ_le_sum
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Coercivity.setIntegral_iterated_le_of_pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
-- the `HkMem` hypothesis on the left-hand side of `HkSq_le_sum_of_integrand_le` is part
-- of the natural statement (the left-hand side is an honest iterated integral) even
-- though the proof of that lemma uses only the hypotheses on the right-hand side
set_option linter.unusedVariables false

/-! ## Additivity of the iterated set integral -/

/-- The iterated set integral of a sum of three functions whose `θ`-slices and
`z`-integrals are all integrable is the sum of the three iterated integrals. -/
theorem setIntegral_iterated_add {s t : Set ℝ} (hs : MeasurableSet s) (u v w : ℝ → ℝ → ℝ)
    (hu : (∀ z ∈ s, IntegrableOn (fun θ => u z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, u z θ) s)
    (hv : (∀ z ∈ s, IntegrableOn (fun θ => v z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, v z θ) s)
    (hw : (∀ z ∈ s, IntegrableOn (fun θ => w z θ) t) ∧ IntegrableOn (fun z => ∫ θ in t, w z θ) s) :
    (∫ z in s, ∫ θ in t, (u z θ + v z θ + w z θ))
      = (∫ z in s, ∫ θ in t, u z θ) + (∫ z in s, ∫ θ in t, v z θ)
        + (∫ z in s, ∫ θ in t, w z θ) := by
  have hθ : ∀ z ∈ s, (∫ θ in t, (u z θ + v z θ + w z θ))
      = (∫ θ in t, u z θ) + (∫ θ in t, v z θ) + (∫ θ in t, w z θ) := by
    intro z hz
    rw [integral_add (f := fun θ => u z θ + v z θ) (g := fun θ => w z θ)
      ((hu.1 z hz).add (hv.1 z hz)) (hw.1 z hz)]
    rw [integral_add (hu.1 z hz) (hv.1 z hz)]
  rw [integral_congr_ae (ae_restrict_of_forall_mem hs (fun z hz => hθ z hz))]
  rw [integral_add (f := fun z => (∫ θ in t, u z θ) + (∫ θ in t, v z θ))
    (g := fun z => ∫ θ in t, w z θ) (hu.2.add hv.2) hw.2]
  rw [integral_add hu.2 hv.2]

/-! ## From a pointwise bound of the integrands to a bound of the squared norms -/

/-- **Integration step.**  If the `H^m`-integrand of `f` is pointwise dominated on the
closed quadrant by the sum of the `H^k`-integrands of `g₁, g₂, g₃`, and these four
functions have honest iterated integrals at the levels `m`, resp. `k`, then the
corresponding inequality holds for the squared norms. -/
theorem HkSq_le_sum_of_integrand_le (α : ℝ) (m k : ℕ) {f g₁ g₂ g₃ : ℝ → ℝ → ℝ}
    (h₁ : Spaces.HkMem α m f) (h₂ : Spaces.HkMem α k g₁) (h₃ : Spaces.HkMem α k g₂)
    (h₄ : Spaces.HkMem α k g₃)
    (hle : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      Spaces.HkIntegrand α m f z θ
        ≤ Spaces.HkIntegrand α k g₁ z θ + Spaces.HkIntegrand α k g₂ z θ
          + Spaces.HkIntegrand α k g₃ z θ) :
    Spaces.HkSq α m f ≤ Spaces.HkSq α k g₁ + Spaces.HkSq α k g₂ + Spaces.HkSq α k g₃ := by
  have hIz : MeasurableSet Spaces.Iz := measurableSet_Ici
  have hIθ : MeasurableSet Spaces.Iθ := measurableSet_Icc
  -- the `z`-integral of the summed integrand is integrable: it agrees a.e. with the sum
  -- of the three `z`-integrals, which is integrable by the `HkMem` hypotheses
  have hae : (fun z => ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
        + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ))
      =ᵐ[volume.restrict Spaces.Iz]
      (fun z => (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₁ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₂ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₃ z θ)) := by
    refine ae_restrict_of_forall_mem hIz fun z hz => ?_
    show (∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ + Spaces.HkIntegrand α k g₂ z θ
          + Spaces.HkIntegrand α k g₃ z θ))
      = (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₁ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₂ z θ)
        + (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g₃ z θ)
    rw [integral_add (f := fun θ => Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ) (g := fun θ => Spaces.HkIntegrand α k g₃ z θ)
        ((h₂.1 z hz).add (h₃.1 z hz)) (h₄.1 z hz)]
    rw [integral_add (h₂.1 z hz) (h₃.1 z hz)]
  have hintsum : Integrable (fun z => ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
        + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ))
      (volume.restrict Spaces.Iz) :=
    ((h₂.2.add h₃.2).add h₄.2).congr hae.symm
  -- the pointwise bound of the integrands integrates to a bound of the iterated integrals
  have hbound : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α m f z θ)
      ≤ ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ) := by
    refine integral_mono_of_nonneg ?_ hintsum ?_
    · exact ae_restrict_of_forall_mem hIz (fun z _ =>
        integral_nonneg (fun θ => Spaces.HkIntegrand_nonneg α m f z θ))
    · exact ae_restrict_of_forall_mem hIz (fun z hz =>
        integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθ (fun θ _ => Spaces.HkIntegrand_nonneg α m f z θ))
          (((h₂.1 z hz).add (h₃.1 z hz)).add (h₄.1 z hz))
          (ae_restrict_of_forall_mem hIθ (fun θ hθ => hle z hz θ hθ)))
  calc Spaces.HkSq α m f
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α m f z θ := rfl
    _ ≤ ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (Spaces.HkIntegrand α k g₁ z θ
          + Spaces.HkIntegrand α k g₂ z θ + Spaces.HkIntegrand α k g₃ z θ) := hbound
    _ = Spaces.HkSq α k g₁ + Spaces.HkSq α k g₂ + Spaces.HkSq α k g₃ := by
        rw [setIntegral_iterated_add hIz (fun z θ => Spaces.HkIntegrand α k g₁ z θ)
          (fun z θ => Spaces.HkIntegrand α k g₂ z θ)
          (fun z θ => Spaces.HkIntegrand α k g₃ z θ) ⟨h₂.1, h₂.2⟩ ⟨h₃.1, h₃.2⟩ ⟨h₄.1, h₄.2⟩]
        rfl

/-! ## The target lemma -/

theorem HkSq_succ_le_of_smooth (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkSq α (k + 1) f
      ≤ Spaces.HkSq α k f + Spaces.HkSq α k (Spaces.Dth f) + Spaces.HkSq α k (Spaces.Dz f) := by
  have hf : Spaces.HkMem α k f := HkMem_mono α k hsm h
  obtain ⟨hdth, hdz⟩ := HkMem_dth α hα k hsm h
  refine HkSq_le_sum_of_integrand_le (α := α) (m := k + 1) (k := k) (f := f) (g₁ := f)
    (g₂ := Spaces.Dth f) (g₃ := Spaces.Dz f) h hf hdth hdz ?_
  intro z hz θ hθ
  exact HkIntegrand_succ_le_sum α k hk hsm hz hθ

end Work.Coercivity
