import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.HkMem_dth =====
section

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

/-! ## Structural identities for the shifted families -/

/-- The pure family of the `H^k`-integrand of `D_θ f` is the family of mixed derivatives
`D_z^i D_θ f = mixed i 1 f` of `f`. -/
private lemma DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dth f) = Spaces.mixed i 1 f := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero]

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with
the `D_θ`-order raised by one: `D_z^j D_θ^i D_θ f = mixed j (i+1) f`. -/
private lemma mixed_Dth_eq_prv (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth f) = Spaces.mixed j (i + 1) f := by
  simp only [Spaces.mixed]
  have h : Spaces.Dth f = Spaces.DthIter 1 f := rfl
  rw [h, Spaces.DthIter_add_right]

/-- The pure family of the `H^k`-integrand of `D_z f` is the family of pure derivatives
`D_z^{i+1} f` of `f`. -/
private lemma DzIter_Dz_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dz f) = Spaces.DzIter (i + 1) f := by
  rw [Spaces.DzIter_add_right]
  rfl

/-- The mixed family of the `H^k`-integrand of `D_z f` is the mixed family of `f` with
the `D_z`-order raised by one: `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` on the closed
quadrant, by commutation of `D_z` and `D_θ`. -/
private lemma mixed_Dz_eq_prv (j i : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed j i (Spaces.Dz f) z θ = Spaces.mixed (j + 1) i f z θ := by
  simpa using Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`
when `F ≥ 0` (the extra term being `F 0`). -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-! ## Pointwise domination of the shifted integrands -/

/-- **Pointwise domination, `D_θ` case.**  Every summand of the `H^k`-integrand of
`D_θ f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_θ f` are mixed summands of `f` with weight `w/√sin^η ≤ W`, and the mixed
summands `D_z^j D_θ^{i+1} f` are themselves mixed summands of `f` at level `k+1`. -/
theorem HkIntegrand_Dth_le (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.HkIntegrand α k (Spaces.Dth f) z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  have hLHS : Spaces.HkIntegrand α k (Spaces.Dth f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth f) z θ * W) ^ 2
              else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
      ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2 := by
    calc (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * H) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dth_eq i f])
      _ ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hw := Spaces.H_le_Wt α hα z θ hz hθ
          have h1 : (Spaces.mixed i 1 f z θ * H) ^ 2
              = (Spaces.mixed i 1 f z θ) ^ 2 * H ^ 2 := by ring
          have h2 : (Spaces.mixed i 1 f z θ * W) ^ 2
              = (Spaces.mixed i 1 f z θ) ^ 2 * W ^ 2 := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dth_eq_prv j i f]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0))
      = (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using SumRowShift_eq k (fun a b => (Spaces.mixed b a f z θ * W) ^ 2)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-- **Pointwise domination, `D_z` case.**  Every summand of the `H^k`-integrand of
`D_z f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_z f = D_z^{i+1} f` are pure summands of `f` at level `k+1`, and the mixed
summands `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` are mixed summands of `f` at level
`k+1` (commutation of `D_z` and `D_θ`, which needs `SmoothNbhd f`). -/
theorem HkIntegrand_Dz_le (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f)
    (z θ : ℝ) (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.HkIntegrand α k (Spaces.Dz f) z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  have hLHS : Spaces.HkIntegrand α k (Spaces.Dz f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz f) z θ * W) ^ 2
              else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le k
      (fun a => (Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i f])
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dz_eq_prv j i hsm hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using SumShiftZ_le k (fun a b => (Spaces.mixed b a f z θ * W) ^ 2)
      (fun a b => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey]

/-! ## Integrability transfer -/

/-- If the `(k+1)`-integrand of `f` has honest iterated integrals, and the `k`-integrand
of the smooth `g` is pointwise dominated by it on the quadrant, then `g ∈ ℋ^k`.  This is
the assembly step of every membership transfer of this chapter: `SmoothNbhd g` supplies
the a.e. strong measurability of the integrand (`aesm_HkIntegrand_slice`,
`aesm_uncurry_HkIntegrand`) and the domination supplies the integrability. -/
theorem HkMem_of_HkIntegrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hsmg : Spaces.SmoothNbhd g) (h : Spaces.HkMem α (k + 1) f)
    (hle : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      Spaces.HkIntegrand α k g z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ) :
    Spaces.HkMem α k g := by
  have hmesθ : MeasurableSet Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Spaces.Iz := measurableSet_Ici
  have hslice := aesm_HkIntegrand_slice α k hsmg
  have hjoint := aesm_uncurry_HkIntegrand α k hsmg
  constructor
  · intro z hz
    refine Integrable.mono' (h.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Spaces.HkIntegrand_nonneg α k g z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' h.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Spaces.HkIntegrand_nonneg α k g z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ _ => Spaces.HkIntegrand_nonneg α k g z θ))
      (h.1 z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

/-! ## The target lemma -/

theorem HkMem_dth (α : ℝ) (hα : 0 < α) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f)
    (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkMem α k (Spaces.Dth f) ∧ Spaces.HkMem α k (Spaces.Dz f) :=
  ⟨HkMem_of_HkIntegrand_le α k hsm.Dth h (fun z hz θ hθ =>
      HkIntegrand_Dth_le α hα k f z θ hz hθ),
    HkMem_of_HkIntegrand_le α k hsm.Dz h (fun z hz θ hθ =>
      HkIntegrand_Dz_le α k hsm z θ hz hθ)⟩

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L2Coercivity =====
section

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

/-- The restricted product measure `volume.restrict (Iz ×ˢ Iθ)` is the product of the two
restricted measures; this is the bridge that lets us use Mathlib's Fubini and
integrability API (stated for product measures) on the joint integrability hypotheses of
`CoerciveData`, which are stated for `Iz ×ˢ Iθ`. -/
private theorem integrableOn_prod_prv {g : ℝ → ℝ → ℝ}
    (h : IntegrableOn (Function.uncurry g) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => g p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.prod_restrict _ _).symm
  rw [IntegrableOn, hvol] at h
  exact h

/-- The pointwise algebra behind the decomposition of the `L₁₂`-term of `𝓛_Γ`: with
`w = (1+z)²/z²` and `z ≠ 0`, `c ≠ 0`,

`2zΓ/(c(1+z)²) · L · f · w² = 2K f (w/z) L + 2(Γ/c - K) f w (L/z)`.

(Both sides are also `0` at `z = 0`, which is why the identity is applied only a.e.) -/
private theorem split_pointwise {c Γ K L f : ℝ} {z : ℝ} (hc : c ≠ 0) (hz : z ≠ 0) :
    2 * z * Γ / (c * (1 + z) ^ 2) * L * f * Spaces.w z ^ 2
      = 2 * K * f * (Spaces.w z / z * L) + 2 * (Γ / c - K) * f * Spaces.w z * (L / z) := by
  simp only [Spaces.w]
  field_simp
  ring


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.slice_ibp_eta =====
section

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

/-! ## Auxiliary integrability lemmas for the `η`-weighted angular integration by parts -/

/-- `sin(2θ)^{-η}` is integrable on `Iθ`, since `-1 < -η ≤ 0`. -/
theorem integrableOn_sin_two_eta_neg :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have h1 : (-1 : ℝ) < -Work.Spaces.eta := by
    have := Work.Spaces.eta_lt_one
    linarith
  have h2 : -Work.Spaces.eta ≤ 0 := by
    have := Work.Spaces.eta_pos
    linarith
  exact (Work.Spaces.sin_two_rpow (-Work.Spaces.eta) h1 h2).1

/-- The right-hand integrand `cos(2θ)·g²·sin(2θ)^{-η}` of `slice_ibp_eta` is integrable on
`Iθ`: on the compact interval the slice `θ ↦ g z θ` is bounded, and `sin(2θ)^{-η}` is
integrable there. -/
theorem integrableOn_cos_sin_eta_mul_sq (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have hw := integrableOn_sin_two_eta_neg
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) * (g z θ) ^ 2) Work.Spaces.Iθ :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((slice_continuousOn g hg hz).pow 2)
  have h := hw.mul_continuousOn hcont isCompact_Icc
  exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The left-hand integrand `D_θg·g·sin(2θ)^{-η} = sin(2θ)^{1-η}·∂_θg·g` of `slice_ibp_eta`
is integrable on `Iθ`: the factor `sin(2θ)` in `D_θ` cancels the singularity of the weight,
and the two slices are continuous, hence bounded, on the compact interval. -/
theorem integrableOn_dth_mul_g_eta (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.Dth g z θ * g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have hw := integrableOn_sin_two_eta_neg
  have hcont : ContinuousOn (fun θ => Work.Spaces.Dth g z θ * g z θ) Work.Spaces.Iθ := by
    show ContinuousOn (fun θ => (Real.sin (2 * θ) * Work.Spaces.pth g z θ) * g z θ)
      Work.Spaces.Iθ
    exact (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (slice_pth_continuousOn g hg hz)).mul (slice_continuousOn g hg hz)
  have h := hw.mul_continuousOn hcont isCompact_Icc
  exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The derivative of the boundary term `ψ(θ) = sin(2θ)^{1-η}g(z,θ)²`.  This is
`Work.Coercivity.slice_psi_hasDerivAt` with `γ - 1 = η - 1`, i.e. with `α = 10(η-1)`
(note that no positivity of `α` is required there); the derivative is `etaPsi'`. -/
theorem etaPsi_hasDerivAt (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => etaPsi g z θ') (etaPsi' g z θ) θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have h := slice_psi_hasDerivAt (10 * (Work.Spaces.eta - 1)) g hg z θ hz hθ hsin
  have hgam : Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) = Work.Spaces.eta := by
    simp only [Work.Spaces.gam, Work.Spaces.eta]
    norm_num
  have hgam1 : Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) - 1 = Work.Spaces.eta - 1 := by
    rw [hgam]
  have hexp : -(Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) - 1) = 1 - Work.Spaces.eta := by
    rw [hgam1]; ring
  have hexp2 : -(Work.Spaces.gam (10 * (Work.Spaces.eta - 1))) = -Work.Spaces.eta := by rw [hgam]
  convert h using 1
  · ext θ'
    simp only [etaPsi]
    rw [hexp]
  · simp only [etaPsi', etaPsiG, etaPsiH]
    rw [hexp2, hgam1]
    ring

/-! ## The `η`-weighted angular integration by parts -/

theorem slice_ibp_eta (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z) :
    ∫ θ in Spaces.Iθ, Spaces.Dth g z θ * g z θ * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      = (Spaces.eta - 1) * ∫ θ in Spaces.Iθ,
          Real.cos (2 * θ) * (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hG : MeasureTheory.IntegrableOn (etaPsiG g z) Work.Spaces.Iθ :=
    integrableOn_dth_mul_g_eta g hg hz
  have hH : MeasureTheory.IntegrableOn (etaPsiH g z) Work.Spaces.Iθ :=
    integrableOn_cos_sin_eta_mul_sq g hg hz
  have hcont : ContinuousOn (fun θ => etaPsi g z θ) (Set.Icc 0 (π / 2)) :=
    etaPsi_continuousOn g hg hz
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ => etaPsi g z θ) (etaPsi' g z x) x :=
    fun x hx => etaPsi_hasDerivAt g hg hz hx
  have hintG : IntervalIntegrable (etaPsiG g z) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr (hG.mono_set Set.Ioc_subset_Icc_self)
  have hintH : IntervalIntegrable (etaPsiH g z) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr (hH.mono_set Set.Ioc_subset_Icc_self)
  have hint : IntervalIntegrable (etaPsi' g z) volume (0 : ℝ) (π / 2) := by
    have h2 : IntervalIntegrable
        (fun x => 2 * etaPsiG g z x - 2 * (Work.Spaces.eta - 1) * etaPsiH g z x)
        volume (0 : ℝ) (π / 2) :=
      (hintG.const_mul 2).sub (hintH.const_mul (2 * (Work.Spaces.eta - 1)))
    show IntervalIntegrable (fun x => etaPsi' g z x) volume (0 : ℝ) (π / 2)
    simpa only [etaPsi'] using h2
  have hFTC : ∫ x in (0 : ℝ)..(π / 2), etaPsi' g z x = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := π / 2)
      hpi hcont hderiv hint
    simpa [(etaPsi_zero g z).1, (etaPsi_zero g z).2] using h
  have hconv : ∀ f : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
    intro f
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi]
  have hset : ∫ x in Work.Spaces.Iθ, etaPsi' g z x = 0 := by
    rw [hconv]
    exact hFTC
  simp only [etaPsi'] at hset
  rw [MeasureTheory.integral_sub (hG.const_mul 2) (hH.const_mul (2 * (Work.Spaces.eta - 1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hset
  have h2 : 2 * (∫ θ in Work.Spaces.Iθ, etaPsiG g z θ)
      = 2 * ((Work.Spaces.eta - 1) * ∫ θ in Work.Spaces.Iθ, etaPsiH g z θ) := by
    linarith
  exact mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num) h2

end Work.Coercivity
end
end
