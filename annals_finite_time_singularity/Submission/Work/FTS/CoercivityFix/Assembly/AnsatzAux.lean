/-
# `Assembly/AnsatzAux.lean` — regularity, support and integrability of the ansatz

The concrete bumps `psiA z = χ(z - 5/2)` and `hA δ θ = χ((θ - 1/2)/δ)` of the
`RegQ`-counterexample live in the *interior* of the quadrant:

* `vzIter j psiA` is `C^∞` and supported in `[1/2, 9/2]`,
* `vthIter i (hA δ)` is `C^∞` and supported in `[θ₀ - 2δ, θ₀ + 2δ] ⊂ (0, π/2)` for `δ ≤ 1/8`.

Consequently every slot integrand of the `ℋ^k`-integrand of the ansatz is continuous and
compactly supported inside a region where the weights `w` and `sin(2θ)^{-η}`,
`sin(2θ)^{-γ}` are bounded, hence integrable; this module records exactly those facts
(`integrableOn_vzIter_sq`, `integrableOn_vthIter_sq`), which are the side conditions of the
slot evaluations of the counterexample.

The support induction runs through `support_deriv_subset` (`support (deriv f) ⊆ tsupport f`):
`D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` only multiply the derivative by a factor, so they do
not enlarge the closure of the support.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Smoothness of the bumps -/

theorem contDiff_psiA : ContDiff ℝ Work.Stability.smoothOrder psiA := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => z - 5 / 2) :=
    contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Stability.chi (z - 5 / 2)) :=
    Work.Stability.chi_contDiff.comp h
  exact h2

theorem contDiff_vzIter_psiA (j : ℕ) :
    ContDiff ℝ Work.Stability.smoothOrder (vzIter j psiA) :=
  contDiff_vzIter psiA contDiff_psiA j

theorem contDiff_hA (δ : ℝ) : ContDiff ℝ Work.Stability.smoothOrder (hA δ) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => (θ - th0) / δ) :=
    (contDiff_id.sub contDiff_const).div_const δ
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Stability.chi ((θ - th0) / δ)) :=
    Work.Stability.chi_contDiff.comp h
  exact h2

theorem contDiff_vthIter_hA (δ : ℝ) (i : ℕ) :
    ContDiff ℝ Work.Stability.smoothOrder (vthIter i (hA δ)) :=
  contDiff_vthIter (hA δ) (contDiff_hA δ) i

/-! ## The supports -/

theorem support_psiA : Function.support psiA ⊆ Set.Icc (1 / 2 : ℝ) (9 / 2) := by
  intro z hz
  by_contra hcon
  rw [Set.mem_Icc, not_and_or] at hcon
  have hz' : z < 1 / 2 ∨ 9 / 2 < z := hcon.imp not_le.mp not_le.mp
  have hlt : 2 ≤ |z - 5 / 2| := by
    rcases hz' with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have h0 : psiA z = 0 := by rw [psiA, Work.Stability.chi_eq_zero hlt]
  exact hz h0

/-- The iterated `D_z`-derivatives of `psiA` are supported in `[1/2, 9/2]`.  (Only the
*closed* support is inherited: `D_z = z ∂_z` differentiates, so the support can grow to the
closure of the old one, which is what the induction below tracks.) -/
theorem support_vzIter_psiA (j : ℕ) :
    Function.support (vzIter j psiA) ⊆ Set.Icc (1 / 2 : ℝ) (9 / 2) := by
  induction j with
  | zero => simpa [vzIter_zero] using support_psiA
  | succ j ih =>
      intro z hz
      have hz' : z ∈ Function.support (vz (vzIter j psiA)) := by
        simpa [vzIter_succ] using hz
      have hd : deriv (vzIter j psiA) z ≠ 0 := by
        intro h0
        exact hz' (by simp [vz, h0])
      have h2 : z ∈ tsupport (vzIter j psiA) := support_deriv_subset hd
      have h4 : closure (Function.support (vzIter j psiA))
          ⊆ closure (Set.Icc (1 / 2 : ℝ) (9 / 2)) := closure_mono ih
      have h5 : z ∈ closure (Set.Icc (1 / 2 : ℝ) (9 / 2)) := h4 h2
      rwa [closure_Icc] at h5

theorem vzIter_psiA_eq_zero {j : ℕ} {z : ℝ} (hz : z ∉ Set.Icc (1 / 2 : ℝ) (9 / 2)) :
    vzIter j psiA z = 0 :=
  Function.notMem_support.mp fun h => hz (support_vzIter_psiA j h)

theorem support_hA {δ : ℝ} (hδ : 0 < δ) :
    Function.support (hA δ) ⊆ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) := by
  intro θ hθ
  by_contra hcon
  rw [Set.mem_Icc, not_and_or] at hcon
  have hθ' : θ < th0 - 2 * δ ∨ th0 + 2 * δ < θ := hcon.imp not_le.mp not_le.mp
  have hlt : 2 ≤ |(θ - th0) / δ| := by
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
    rcases hθ' with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have h0 : hA δ θ = 0 := by rw [hA, Work.Stability.chi_eq_zero hlt]
  exact hθ h0

/-- The iterated `D_θ`-derivatives of `hA δ` are supported in `[θ₀ - 2δ, θ₀ + 2δ]`. -/
theorem support_vthIter_hA (δ : ℝ) (hδ : 0 < δ) (i : ℕ) :
    Function.support (vthIter i (hA δ)) ⊆ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) := by
  induction i with
  | zero => simpa [vthIter_zero] using support_hA hδ
  | succ i ih =>
      intro θ hθ
      have hθ' : θ ∈ Function.support (vth (vthIter i (hA δ))) := by
        simpa [vthIter_succ] using hθ
      have hd : deriv (vthIter i (hA δ)) θ ≠ 0 := by
        intro h0
        exact hθ' (by simp [vth, h0])
      have h2 : θ ∈ tsupport (vthIter i (hA δ)) := support_deriv_subset hd
      have h4 : closure (Function.support (vthIter i (hA δ)))
          ⊆ closure (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := closure_mono ih
      have h5 : θ ∈ closure (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := h4 h2
      rwa [closure_Icc] at h5

theorem vthIter_hA_eq_zero {δ : ℝ} (hδ : 0 < δ) {i : ℕ} {θ : ℝ}
    (hθ : θ ∉ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :
    vthIter i (hA δ) θ = 0 :=
  Function.notMem_support.mp fun h => hθ (support_vthIter_hA δ hδ i h)

/-! ## The two slot integrability facts -/

/-- `Z_j = ∫_z (D_z^j ψ · w)²` is an honest integral: the integrand is continuous and
supported in the compact `[1/2, 9/2]`, on which `w` is continuous. -/
theorem integrableOn_vzIter_sq (j : ℕ) :
    IntegrableOn (fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc (1 / 2 : ℝ) (9 / 2)) := by
    rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => ?_)
    rcases hz with ⟨h1, h2⟩
    exact pow_ne_zero 2 (by linarith)
  have hcont : ContinuousOn (fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2)
      (Set.Icc (1 / 2 : ℝ) (9 / 2)) :=
    (((contDiff_vzIter_psiA j).continuous.continuousOn).mul hw).pow 2
  have hInt : IntegrableOn (fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2)
      (Set.Icc (1 / 2 : ℝ) (9 / 2)) := hcont.integrableOn_compact isCompact_Icc
  have hzero : ∀ z, z ∉ Set.Icc (1 / 2 : ℝ) (9 / 2) →
      (vzIter j psiA z * Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz
    rw [vzIter_psiA_eq_zero hz]
    simp
  have hglob : Integrable
      (fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2) (volume : Measure ℝ) := by
    have h1 : Integrable ((Set.Icc (1 / 2 : ℝ) (9 / 2)).indicator
        (fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2)) (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hInt
    refine h1.congr ?_
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc (1 / 2 : ℝ) (9 / 2)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  exact hglob.integrableOn

/-- `S^i_q = ∫_θ (D_θ^i h)² sin(2θ)^{-q}` is an honest integral for every real `q`: the
integrand is supported in `[θ₀ - 2δ, θ₀ + 2δ] ⊂ (0, π/2)` where `sin(2θ) > 0`. -/
theorem integrableOn_vthIter_sq (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (i : ℕ) (q : ℝ) :
    IntegrableOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hsin : ∀ θ ∈ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [th0] at h1 h2
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
      have := Real.pi_gt_three
      linarith)
  have hcont : ContinuousOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (vthIter i (hA δ) θ) ^ 2)
        (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :=
      (((contDiff_vthIter_hA δ i).continuous).continuousOn).pow 2
    have hsincont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q))
        (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :=
      (hsincont.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (hsin θ hθ))))
    exact h1.mul h2
  have hInt : IntegrableOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := hcont.integrableOn_compact isCompact_Icc
  have hzero : ∀ θ, θ ∉ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) →
      (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) = 0 := by
    intro θ hθ
    rw [vthIter_hA_eq_zero hδ0 hθ, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have hglob : Integrable
      (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume : Measure ℝ) := by
    have h1 : Integrable ((Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)).indicator
        (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hInt
    refine h1.congr ?_
    filter_upwards with θ
    by_cases hθ : θ ∈ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)
    · rw [Set.indicator_of_mem hθ]
    · rw [Set.indicator_of_notMem hθ, hzero θ hθ]
  exact hglob.integrableOn

end Work.FTS.CoercivityFix.Assembly
