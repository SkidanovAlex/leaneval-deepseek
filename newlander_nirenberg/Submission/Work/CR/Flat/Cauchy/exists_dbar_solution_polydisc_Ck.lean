import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Cauchy.bmPotential_iter_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_top_bound
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Cauchy.bmPotential_holder_CZ

set_option maxHeartbeats 2000000

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal Convolution
open MeasureTheory Set

/-- `∂̄` of a constant multiple. -/
private lemma dbarCoord_const_mul {n : ℕ} (j : Fin n) (c : ℂ) {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hφ : DifferentiableAt ℝ φ z) :
    dbarCoord j (fun y => c * φ y) z = c * dbarCoord j φ z := by
  have h : fderiv ℝ (fun y => c * φ y) z = c • fderiv ℝ φ z := fderiv_const_mul hφ c
  rw [dbarCoord, dbarCoord, h]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Smoothness of the Bochner–Martinelli potential for `C^{k+1}` data with compact support. -/
lemma contDiff_bmPotential_Ck {n : ℕ} (hn : 0 < n) (k : ℕ)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ i, ContDiff ℝ (k + 1) (f i))
    (hsupp : ∀ i, HasCompactSupport (f i)) :
    ContDiff ℝ (k + 1) (bmPotential f) := by
  have hconv : ∀ i, ContDiff ℝ (k + 1)
      (bmKernel i ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f i) := fun i =>
    HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hsupp i) (locallyIntegrable_bmKernel hn i) (hf i)
  rw [bmPotential_eq_neg_conv f]
  exact ContDiff.neg (ContDiff.sum fun i _ => hconv i)

/-- Unfolding of `holderNorm` one step. -/
lemma holderNorm_succ {n : ℕ} (k : ℕ) (α : ℝ) (g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    holderNorm (k + 1) α g Ω
      = holderNorm k α g Ω + (iterDerivNorm (k + 1) g Ω + holderSeminorm (k + 1) α g Ω) := by
  rw [holderNorm, holderNorm, Finset.sum_range_succ]

/-- Unfolding of `holderNorm` at `k = 0`. -/
lemma holderNorm_zero_unfold {n : ℕ} (α : ℝ) (g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    holderNorm 0 α g Ω = iterDerivNorm 0 g Ω + holderSeminorm 0 α g Ω := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- **The flat `∂̄`-Poincaré result on a polydisc in the `C^{k,α}` scale, with a gain
of exactly one derivative.**  For `0 < α < 1` and every `k` there is `C = C(k,r,α)`
such that every closed `(0,1)`-form `f = Σ_j f_j dz̄_j` with `C^{k+1}` components
supported in the half-size polydisc `P = polydisc c (r/2)` admits a solution `u` of
`∂̄_j u = f_j` on `P` with

`‖u‖_{C^{k+1,α}(P)} ≤ C Σ_j ‖f_j‖_{C^{k,α}}`,

the constant being uniform in `f`.  This is the form in which the
Newlander–Nirenberg small-perturbation iteration consumes the `∂̄`-Poincaré
result: at each step one loses nothing and gains exactly one derivative.  The
support hypothesis is the standard one after multiplication by a cutoff. -/
theorem exists_dbar_solution_polydisc_Ck {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {r : Fin n → ℝ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) → IsClosedForm f →
      ∃ u : (Fin n → ℂ) → ℂ,
        (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < r i / 2) → dbarCoord j u z = f j z) ∧
        holderNorm (k + 1) α u (polydisc c (fun j => r j / 2))
          ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) Set.univ := by
  -- the order-zero estimate for the polydisc of twice the radii, obtained from the
  -- Bochner--Martinelli Calderón–Zygmund estimate
  have hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ := by
    obtain ⟨C₀, hC₀, hC₀'⟩ := bmPotential_holder_CZ hn (c := c)
      (r := fun j => 2 * r j) hα hα1 (fun j => by linarith [hr j])
    have hpoly : polydisc c (fun j => 2 * r j / 2) = polydisc c r := by
      congr 1
      ext j
      ring
    refine ⟨C₀, hC₀, fun g hg hgs => ?_⟩
    have h := hC₀' g hg (fun j z hz => hgs j z (by simpa [hpoly] using hz))
    rwa [hpoly] at h
  obtain ⟨C₁, hC₁, hiter⟩ := bmPotential_iter_bound hn hα hα1 hr k hbase
  obtain ⟨C₂, hC₂, htop⟩ := bmPotential_top_bound hn hα hα1 hr k hbase
  obtain ⟨γ, hγ, hsol⟩ := bmPotential_solves_dbar hn hr
  have hf1 : ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
      ∀ j, ContDiff ℝ 1 (f j) :=
    fun f hf j => (hf j).of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
  set K : ℝ := 2 * ((k : ℝ) + 1) * C₁ + 2 * C₂ with hK
  refine ⟨K * ‖γ‖⁻¹ + 1, by have := norm_nonneg (γ⁻¹); positivity, ?_⟩
  intro f hf hsupp hclosed
  have hcs : ∀ j, HasCompactSupport (f j) := fun j =>
    hasCompactSupport_of_halfPolydisc hr (fun z hz => hsupp j z hz)
  refine ⟨fun z => γ⁻¹ * bmPotential f z, ?_, ?_⟩
  · intro j z hz
    have hd : DifferentiableAt ℝ (bmPotential f) z :=
      ((contDiff_bmPotential_Ck hn k hf hcs).differentiable (by simp)).differentiableAt
    rw [dbarCoord_const_mul j γ⁻¹ hd, hsol f (hf1 f hf) hsupp hclosed j z hz, ← mul_assoc,
      inv_mul_cancel₀ hγ, one_mul]
  · set P : Set (Fin n → ℂ) := polydisc c (fun j => r j / 2) with hP
    set S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) Set.univ with hS
    have hlower : holderNorm k α (bmPotential f) P ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
      rw [holderNorm]
      calc ∑ m ∈ Finset.range (k + 1),
              (iterDerivNorm m (bmPotential f) P + holderSeminorm m α (bmPotential f) P)
          ≤ ∑ _m ∈ Finset.range (k + 1), (ENNReal.ofReal (2 * C₁) * S) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            refine (add_le_add (hiter f hf hsupp m hmk).1 (hiter f hf hsupp m hmk).2).trans ?_
            rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₁) (le_of_lt hC₁),
              show C₁ + C₁ = 2 * C₁ by ring]
        _ = ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 * C₁) * S) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
            rw [← ENNReal.ofReal_natCast (k + 1), ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            push_cast
            ring
    have htop' : iterDerivNorm (k + 1) (bmPotential f) P
        + holderSeminorm (k + 1) α (bmPotential f) P ≤ ENNReal.ofReal (2 * C₂) * S := by
      have hh := htop f hf hsupp
      refine (add_le_add hh.1 hh.2).trans ?_
      rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₂) (le_of_lt hC₂),
        show C₂ + C₂ = 2 * C₂ by ring]
    have hbound : holderNorm (k + 1) α (bmPotential f) P ≤ ENNReal.ofReal K * S := by
      rw [holderNorm_succ k α (bmPotential f) P, hK]
      calc holderNorm k α (bmPotential f) P
            + (iterDerivNorm (k + 1) (bmPotential f) P
                + holderSeminorm (k + 1) α (bmPotential f) P)
          ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S + ENNReal.ofReal (2 * C₂) * S :=
            add_le_add hlower htop'
        _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁ + 2 * C₂) * S := by
            rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hcd : ContDiffOn ℝ (k + 1) (bmPotential f) P :=
      (contDiff_bmPotential_Ck hn k hf hcs).contDiffOn
    rw [show (fun z => γ⁻¹ * bmPotential f z) = γ⁻¹ • (fun z => bmPotential f z) from rfl,
      Work.CR.Flat.Holder.holderNorm_smul γ⁻¹ hcd
        ((isOpen_polydisc c (fun j => r j / 2)).uniqueDiffOn)]
    calc ENNReal.ofReal ‖γ⁻¹‖ * holderNorm (k + 1) α (bmPotential f) P
        ≤ ENNReal.ofReal ‖γ⁻¹‖ * (ENNReal.ofReal K * S) :=
          mul_le_mul_right hbound (ENNReal.ofReal ‖γ⁻¹‖)
      _ = ENNReal.ofReal (‖γ⁻¹‖ * K) * S := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg γ⁻¹)]
      _ ≤ ENNReal.ofReal (K * ‖γ‖⁻¹ + 1) * S := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) S
          rw [norm_inv]
          linarith

end Work.CR.Flat.Cauchy
