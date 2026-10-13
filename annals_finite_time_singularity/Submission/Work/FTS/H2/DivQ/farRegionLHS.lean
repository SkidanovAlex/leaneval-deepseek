import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.reflSlice_facts
import Submission.Work.FTS.H2.DivQ.nearRegionLHS_i
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### Elementary reflection facts

Everything below is the bookkeeping needed to transfer the *near*-region estimate
(`nearRegionLHS_i`) to the *far* region through the reflection `ρ θ = π/2 - θ`.

The reflection preserves `sin(2θ)`, is measure preserving on `Iθ = [0,π/2]` (which it maps to
itself), and conjugates `D_θ = sin(2θ)∂_θ` to `-D_θ`, so `D_θ^m` picks up the sign `(-1)^m`. -/

/-- The derivative of the reflected slice is minus the reflected derivative. -/
lemma far_deriv_reflSlice_eq (h : ℝ → ℝ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => h (Real.pi / 2 - θ')) θ = -deriv h (Real.pi / 2 - θ) := by
  have hmem : Real.pi / 2 - θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hdh : HasDerivAt h (deriv h (Real.pi / 2 - θ)) (Real.pi / 2 - θ) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)).hasDerivAt
  have hr : HasDerivAt (fun θ' : ℝ => Real.pi / 2 - θ') (-1) θ := by
    have h0 := (hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)
    have hf : ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ)) = fun θ' : ℝ => Real.pi / 2 - θ' := by
      funext θ'; simp
    rw [hf] at h0
    simpa using h0
  have hcomp : deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ
      = deriv h (Real.pi / 2 - θ) * (-1) := by
    simpa [Function.comp_def] using (hdh.comp θ hr).deriv
  rw [hcomp]; ring

lemma far_neg_one_pow_sq (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `D_θ^m` depends only on the germ: functions that agree on an open set have `D_θ^m`
agreeing there as well. -/
lemma far_Dth1Iter_congr_of_isOpen (m : ℕ) {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn f g s) :
    Set.EqOn (Work.Elliptic.Dth1Iter m f) (Work.Elliptic.Dth1Iter m g) s := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      intro θ hθ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      simp only [Work.Elliptic.Dth1]
      congr 1
      exact (Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hθ, ih⟩).deriv_eq

/-- `D_θ^m` is linear: `D_θ^m(-f) = -(D_θ^m f)` globally. -/
lemma far_Dth1Iter_neg_eq (m : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter m (fun θ => -f θ)
      = fun θ => -(Work.Elliptic.Dth1Iter m f θ) := by
  induction m with
  | zero => funext θ; simp
  | succ m ih =>
      ext θ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      simp only [Work.Elliptic.Dth1]
      rw [ih]
      have h1 : (fun x : ℝ => -(Work.Elliptic.Dth1Iter m f x))
          =ᶠ[𝓝 θ] (fun x => (-1 : ℝ) * Work.Elliptic.Dth1Iter m f x) :=
        Filter.Eventually.of_forall (fun x => by ring)
      rw [h1.deriv_eq, deriv_const_mul_field]
      ring

/-- Reflection of `D_θ^m(∂_θ ·)`: the `m`-th angular derivative of the derivative of the
reflected slice is `(-1)^{m+1}` times the reflected `m`-th angular derivative of `∂_θh`. -/
lemma far_Dth1Iter_deriv_reflSlice_eq (m : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ
        = (-1 : ℝ) ^ (m + 1) * Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ) := by
  have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by simp)
  have hrefl := (reflSlice_facts m (h := deriv h) hder).1
  intro θ hθ
  rw [far_Dth1Iter_congr_of_isOpen m isOpen_Ioo
    (fun θ' hθ' => far_deriv_reflSlice_eq h hsm hθ') hθ]
  rw [far_Dth1Iter_neg_eq m (fun θ' => deriv h (Real.pi / 2 - θ'))]
  change -(Work.Elliptic.Dth1Iter m (fun θ' => deriv h (Real.pi / 2 - θ')) θ)
      = (-1 : ℝ) ^ (m + 1) * Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)
  rw [hrefl θ hθ, pow_succ]
  ring

lemma far_sq_Dth1Iter_deriv_reflSlice_eq (m : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        = (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2 := by
  intro θ hθ
  rw [far_Dth1Iter_deriv_reflSlice_eq m hsm θ hθ, mul_pow, far_neg_one_pow_sq (m + 1),
    one_mul]

/-- Reflection of `D_θ^i(·/sin(2·))` on the quotient slice. -/
lemma far_Dth1Iter_divSin_reflSlice_eq (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ
        = (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i
          (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ) := by
  have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hsmF : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.div hsin (fun θ hθ =>
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
  have hfun : (fun θ : ℝ => h (Real.pi / 2 - θ) / Real.sin (2 * θ))
      = (fun θ : ℝ => (fun θ' : ℝ => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) := by
    funext θ
    simp only []
    rw [sin_two_reflSlice]
  have hrefl := (reflSlice_facts i (h := fun θ' : ℝ => h θ' / Real.sin (2 * θ')) hsmF).1
  intro θ hθ
  rw [hfun]
  exact hrefl θ hθ

lemma far_sq_Dth1Iter_divSin_reflSlice_eq (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
        = (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) ^ 2 := by
  intro θ hθ
  rw [far_Dth1Iter_divSin_reflSlice_eq i hsm θ hθ, mul_pow, far_neg_one_pow_sq i, one_mul]

/-! ### Measure-theoretic reflection facts on `Iθ` -/

lemma far_measurePreserving_reflθ :
    MeasureTheory.MeasurePreserving (fun θ : ℝ => Real.pi / 2 - θ) volume volume := by
  have h := (measurePreserving_add_left volume (Real.pi / 2)).comp
    (Measure.measurePreserving_neg volume)
  convert h using 1
  ext x
  simp [sub_eq_add_neg]

lemma far_measurableEmbedding_reflθ : MeasurableEmbedding (fun θ : ℝ => Real.pi / 2 - θ) := by
  have h := (Homeomorph.subLeft (Real.pi / 2) : ℝ ≃ₜ ℝ).measurableEmbedding
  convert h using 1
  ext x
  simp

/-- The reflection maps `Iθ` to itself. -/
lemma far_preimage_Iθ : (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Work.Spaces.Iθ = Work.Spaces.Iθ := by
  ext x
  simp only [Set.mem_preimage, Work.Spaces.Iθ, Set.mem_Icc]
  constructor <;> intro hx <;> constructor <;> linarith [Real.pi_pos, hx.1, hx.2]

/-- Reflection invariance of `IntegrableOn` on `Iθ`. -/
lemma far_integrableOn_reflθ (F : ℝ → ℝ) :
    IntegrableOn (fun θ => F (Real.pi / 2 - θ)) Work.Spaces.Iθ ↔ IntegrableOn F Work.Spaces.Iθ := by
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage far_measurePreserving_reflθ
    far_measurableEmbedding_reflθ (f := F) (s := Work.Spaces.Iθ)
  rw [far_preimage_Iθ] at h
  exact h

/-- Reflection invariance of the integral over `Iθ`. -/
lemma far_integral_reflθ (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, F (Real.pi / 2 - θ)) = ∫ θ in Work.Spaces.Iθ, F θ := by
  have hpp : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1 : (∫ θ in Work.Spaces.Iθ, F (Real.pi / 2 - θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), F (Real.pi / 2 - θ) := by
    rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le hpp,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le hpp,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1, h2]
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
    (d := Real.pi / 2) (f := F)
  simpa using h

/-- Equality on the open interval upgrades to almost-everywhere equality on `Iθ`
(the two endpoints form a null set). -/
lemma far_ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2))) :
    f =ᵐ[volume.restrict Work.Spaces.Iθ] g := by
  have hnull : volume (Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2)) = 0 := by
    have hsub : Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      obtain ⟨hxI, hxO⟩ := hx
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
      simp only [Set.mem_Ioo, not_and_or] at hxO
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hxO with h' | h'
      · left; linarith [hxI.1]
      · right; linarith [hxI.2]
    refine measure_mono_null hsub ?_
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by ext x; simp [or_comm]]
    rw [measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton (Real.pi / 2)⟩
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc,
    MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_ofPred_eq, not_imp] at hx
  exact ⟨hx.1, fun hxO => hx.2 (h hxO)⟩

/-! ### The data integrals of the reflected slice -/

lemma far_integrand_ae (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (fun θ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
    (fun θ => (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c) := by
  refine far_ae_eq_of_eqOn_Ioo ?_
  intro θ hθ
  change (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c
      = (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c
  rw [far_sq_Dth1Iter_deriv_reflSlice_eq m hsm θ hθ, sin_two_reflSlice]

lemma far_integrand_integrable (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ c)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c) Work.Spaces.Iθ := by
  have hbase : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c) Work.Spaces.Iθ :=
    (far_integrableOn_reflθ
      (fun θ' : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ') ^ 2 * (Real.sin (2 * θ')) ^ c)).2 hint
  exact hbase.congr_fun_ae (far_integrand_ae m c hsm).symm

lemma far_integrand_integral_eq (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c)
      = ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c := by
  rw [MeasureTheory.setIntegral_congr_ae (s := Work.Spaces.Iθ) measurableSet_Icc
    ((MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mp
      (far_integrand_ae m c hsm))]
  exact far_integral_reflθ
    (fun θ' : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ') ^ 2 * (Real.sin (2 * θ')) ^ c)

lemma far_data_eta_integrable {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDen : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => h (Real.pi / 2 - θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  simpa using far_integrand_integrable 0 (-(Work.Spaces.eta)) hsm hDen

lemma far_data_gam_integrable (m : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDen : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
  far_integrand_integrable m (-(Work.Spaces.gam α)) hsm hDen

lemma far_data_eta_integral_eq {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => h (Real.pi / 2 - θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  simpa using far_integrand_integral_eq 0 (-(Work.Spaces.eta)) hsm

lemma far_data_gam_integral_eq (m : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  far_integrand_integral_eq m (-(Work.Spaces.gam α)) hsm

/-! ### Transport of the left-hand side to the near region -/

/-- The far-region integral of the level-`i` quotient slice equals the near-region integral of
the level-`i` quotient slice of the *reflected* slice. -/
lemma far_nearLHS_eq (i : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
        (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ => h (Real.pi / 2 - θ) / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hcv := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 8)
    (d := Real.pi / 2)
    (f := fun θ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
  rw [show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring, sub_zero] at hcv
  rw [← hcv]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x hx
  have hxIoo : x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 8)] at hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  change (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(Work.Spaces.gam α))
      = (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) x) ^ 2
        * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α))
  rw [← far_sq_Dth1Iter_divSin_reflSlice_eq i hsm x hxIoo, sin_two_reflSlice]

/-- **The far-region bound for the left-hand side of `DivisionBySin`** (the mirror image of
`nearRegionLHS_i` under `θ ↦ π/2 - θ`).

There is a universal constant `C` such that: for every `0 < α ≤ 1` and every slice `h` of class
`C^∞` on `(0,π/2)` with `h(θ) → 0` at both endpoints and with `∫_{Iθ}(∂_θh)² sin(2θ)^{-η}` honest
(`η = 99/100`, `γ = 1+α/10`, `Iθ = [0,π/2]`, `D_θ^m = Work.Elliptic.Dth1Iter m`), and for every
`1 ≤ i ≤ 4` such that `∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}` is honest for all `1 ≤ m ≤ i`:

  `∫_{3π/8}^{π/2} (D_θ^i (fun θ => h θ / sin(2θ)) θ)² sin(2θ)^{-γ} dθ
      ≤ C (∫_{Iθ}(∂_θh)² sin(2θ)^{-η} + Σ_{1≤m≤i} ∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ})`.

ROUTE.  Apply **`nearRegionLHS_i`** (same workspace, `Submission/Work/FTS/H2/DivQ/nearRegionLHS_i.lean`,
whose data hypothesis is `∀ m ≤ i` — the strengthened `nearRegionLHS` is *not* applicable here) to
the reflected slice `g := fun θ => h (π/2 - θ)`, using `reflSlice_facts`
(`Submission/Work/FTS/H2/DivQ/reflSlice_facts.lean`):

* `sin(2(π/2-θ)) = sin(2θ)`, and `∫_{3π/8}^{π/2}F = ∫_0^{π/8}F∘refl` by the change of variables
  `θ ↦ π/2 - θ` (`intervalIntegral.integral_comp_sub_left`);
* `g/sin(2·) = (h/sin(2·)) ∘ refl`, and `D_θ^i (u ∘ refl) = (-1)^i (D_θ^i u) ∘ refl`
  (`reflSlice_facts`), so the two squared integrands agree under the substitution;
* the data of `g` are those of `h` (`D_θ^m(∂_θg) = -(D_θ^m(∂_θh)) ∘ refl`, from `reflSlice_facts`
  at `i = 1` divided by `sin(2θ) ≠ 0` on `(0,π/2)` and then iterated), and
  `∫_{Iθ} G (π/2-θ) dθ = ∫_{Iθ} G θ dθ` by the second conjunct of `reflSlice_facts`, so the data
  integrals of `g` equal those of `h`;
* `g(θ) → 0` at `0⁺` is the hypothesis `h(θ) → 0` at `(π/2)⁻`. -/
theorem farRegionLHS :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨Cn, hCnpos, hnear⟩ := nearRegionLHS_i
  refine ⟨Cn, hCnpos, ?_⟩
  intro α h hα0 hα1 hsm hT0 hTpi hDenη i hi hDenγ
  -- smoothness of the reflected slice
  have hsmG : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h (Real.pi / 2 - θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.pi / 2 - θ)
        (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const.sub contDiffOn_id
    exact hsm.comp h2 (fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
  -- the reflected slice tends to `0` at `0⁺`
  have hG0 : Filter.Tendsto (fun θ : ℝ => h (Real.pi / 2 - θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0) (𝓝 (Real.pi / 2)) := by
          have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0)
              (𝓝 (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
          simpa using h3
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        simp only [Set.mem_Ioi] at hθ
        exact sub_lt_self _ hθ
    simpa [Function.comp_def] using hTpi.comp h1
  -- integrability of the reflected data
  have hGη := far_data_eta_integrable hsm hDenη
  have hGγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    fun m hm => far_data_gam_integrable m α hsm (hDenγ m hm)
  have hnearG := hnear α (fun θ : ℝ => h (Real.pi / 2 - θ)) hα0 hα1 hsmG hG0 hGη i hi hGγ
  -- transfer of the left-hand side and of the data integrals
  have hLHS := far_nearLHS_eq i α hsm
  have hη := far_data_eta_integral_eq hsm
  have hγ : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      = ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    Finset.sum_congr rfl (fun m _ => far_data_gam_integral_eq m α hsm)
  calc (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
        (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in (0 : ℝ)..(Real.pi / 8),
          (Work.Elliptic.Dth1Iter i (fun θ => h (Real.pi / 2 - θ) / Real.sin (2 * θ)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hLHS
    _ ≤ Cn * ((∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Elliptic.Dth1Iter m (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ'))) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := hnearG
    _ = Cn * ((∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [hη, hγ]

end Work.FTS.H2.DivQ
