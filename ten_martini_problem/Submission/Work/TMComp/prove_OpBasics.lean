/-
# Component C1 of the Ten Martini formalisation: `P_OpBasics`

Operator basics for the almost Mathieu operator on `ℓ²(ℤ)`: existence, self-adjointness,
and independence of the spectrum on the phase for irrational frequency.

The proof is assembled here from five delegated lemmas (in sibling modules of `TMComp`):

* `exists_of_coeffs`   : a bounded coefficient sequence yields a bounded operator with the
                         shift-plus-diagonal coordinate formula;
* `isSelfAdjoint_of_coeffs` : such an operator is self-adjoint when the coefficients are real;
* `norm_sub_le_of_coeffs`   : two such operators differ in norm by at most the sup-norm of the
                         difference of their coefficient sequences;
* `shift_unit`         : the shift on `ℓ²(ℤ)` packaged as a unit of the operator algebra;
* `spectrum_perturb`   : the spectrum of a self-adjoint operator perturbs by at most the
                         operator-norm distance.

The mathematical content of the assembly is:
`H_{θ+α} = U H_θ U⁻¹` for the shift `U` (covariance), hence the spectrum is invariant along the
orbit `θ + ℤα`; the orbit is dense modulo `1` (Weyl, `dense_addSubgroupClosure_pair_iff`); and
spectral continuity in the norm turns density into equality of spectra.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Defs
import Submission.Work.TMComp.exists_of_coeffs
import Submission.Work.TMComp.isSelfAdjoint_of_coeffs
import Submission.Work.TMComp.norm_sub_le_of_coeffs
import Submission.Work.TMComp.shift_unit
import Submission.Work.TMComp.spectrum_perturb

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

namespace OpBasics

variable {α lam θ : ℝ}

/-! ### Elementary facts -/

lemma eq_of_coeffs {c : ℤ → ℂ} {H H' : EllTwo →L[ℂ] EllTwo}
    (h : IsJacobiOp c H) (h' : IsJacobiOp c H') : H = H' := by
  refine ContinuousLinearMap.ext fun u => lp.ext (funext fun n => ?_)
  rw [h u n, h' u n]

lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]

lemma amoCoeff_shift (α lam θ : ℝ) (n : ℤ) :
    amoCoeff α lam (θ + α) n = amoCoeff α lam θ (n + 1) := by
  have h : (θ + α) + (n : ℝ) * α = θ + (((n + 1 : ℤ)) : ℝ) * α := by push_cast; ring
  simp only [amoCoeff, h]

lemma amoCoeff_period (α lam θ : ℝ) (k : ℤ) (n : ℤ) :
    amoCoeff α lam (θ + k) n = amoCoeff α lam θ n := by
  simp only [amoCoeff]
  have h : 2 * Real.pi * ((θ + (k : ℝ)) + (n : ℝ) * α)
      = 2 * Real.pi * (θ + (n : ℝ) * α) + k * (2 * Real.pi) := by ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-! ### Existence (part 1 of `P_OpBasics`) -/

theorem amo_exists (α lam θ : ℝ) :
    ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam θ H := by
  have hbound : ∀ n : ℤ, ‖amoCoeff α lam θ n‖ ≤ 2 * |lam| := by
    intro n
    rw [amoCoeff, norm_ofReal, abs_mul, abs_mul]
    have h1 : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)))]
  obtain ⟨H, hH⟩ := exists_of_coeffs (amoCoeff α lam θ) (2 * |lam|) hbound
  exact ⟨H, (isAMO_iff_isJacobiOp α lam θ H).2 hH⟩

theorem amo_isSelfAdjoint {H : EllTwo →L[ℂ] EllTwo} (h : IsAlmostMathieuOperator α lam θ H) :
    IsSelfAdjoint H :=
  isSelfAdjoint_of_coeffs
    (fun n => ⟨2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)), rfl⟩)
    ((isAMO_iff_isJacobiOp α lam θ H).1 h)

noncomputable def amoOp (α lam : ℝ) (θ : ℝ) : EllTwo →L[ℂ] EllTwo :=
  Classical.choose (amo_exists α lam θ)

lemma amoOp_spec (α lam θ : ℝ) : IsAlmostMathieuOperator α lam θ (amoOp α lam θ) :=
  Classical.choose_spec (amo_exists α lam θ)

lemma amoOp_eq {H : EllTwo →L[ℂ] EllTwo} (h : IsAlmostMathieuOperator α lam θ H) :
    H = amoOp α lam θ :=
  eq_of_coeffs ((isAMO_iff_isJacobiOp α lam θ H).1 h)
    ((isAMO_iff_isJacobiOp α lam θ (amoOp α lam θ)).1 (amoOp_spec α lam θ))

noncomputable def specOf (α lam θ : ℝ) : Set ℂ := spectrum ℂ (amoOp α lam θ)

lemma specOf_eq_of_AMO {H : EllTwo →L[ℂ] EllTwo} (h : IsAlmostMathieuOperator α lam θ H) :
    spectrum ℂ H = specOf α lam θ :=
  congrArg (fun K => spectrum ℂ K) (amoOp_eq h)

/-! ### The shift unit and covariance -/

noncomputable def shiftU : (EllTwo →L[ℂ] EllTwo)ˣ := Classical.choose shift_unit

lemma shiftU_val (f : EllTwo) (n : ℤ) :
    ((shiftU : EllTwo →L[ℂ] EllTwo) f) n = f (n + 1) :=
  (Classical.choose_spec shift_unit).1 f n

lemma shiftU_inv_val (f : EllTwo) (n : ℤ) :
    ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) f) n = f (n - 1) :=
  (Classical.choose_spec shift_unit).2 f n

lemma isJacobiOp_shift_conj {H : EllTwo →L[ℂ] EllTwo} (h : IsJacobiOp (amoCoeff α lam θ) H) :
    IsJacobiOp (amoCoeff α lam (θ + α))
      ((shiftU : EllTwo →L[ℂ] EllTwo) * H * ↑(shiftU⁻¹)) := by
  intro u n
  have step1 : (((shiftU : EllTwo →L[ℂ] EllTwo) * H * ↑(shiftU⁻¹)) u) n
      = (H ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u)) (n + 1) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, shiftU_val]
  rw [step1]
  have step2 : (H ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u)) (n + 1)
      = ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u) (n + 1 + 1)
        + ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u) (n + 1 - 1)
        + amoCoeff α lam θ (n + 1) * ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u) (n + 1) :=
    h ((↑(shiftU⁻¹) : EllTwo →L[ℂ] EllTwo) u) (n + 1)
  simp only [step2, shiftU_inv_val, amoCoeff_shift, add_sub_cancel_right]

lemma amoOp_shift (α lam θ : ℝ) :
    amoOp α lam (θ + α) = (shiftU : EllTwo →L[ℂ] EllTwo) * amoOp α lam θ * ↑(shiftU⁻¹) := by
  refine (eq_of_coeffs (c := amoCoeff α lam (θ + α)) ?_ ?_).symm
  · exact isJacobiOp_shift_conj
      ((isAMO_iff_isJacobiOp α lam θ (amoOp α lam θ)).1 (amoOp_spec α lam θ))
  · exact (isAMO_iff_isJacobiOp α lam (θ + α) (amoOp α lam (θ + α))).1
      (amoOp_spec α lam (θ + α))

lemma specOf_shift (α lam θ : ℝ) : specOf α lam (θ + α) = specOf α lam θ := by
  change spectrum ℂ (amoOp α lam (θ + α)) = spectrum ℂ (amoOp α lam θ)
  rw [amoOp_shift, spectrum.units_conjugate]

lemma specOf_period (α lam θ : ℝ) (k : ℤ) : specOf α lam (θ + k) = specOf α lam θ := by
  have h1 : IsAlmostMathieuOperator α lam θ (amoOp α lam (θ + k)) := by
    rw [isAMO_iff_isJacobiOp]
    rw [show amoCoeff α lam θ = amoCoeff α lam (θ + k) from
      funext fun n => (amoCoeff_period α lam θ k n).symm]
    exact (isAMO_iff_isJacobiOp α lam (θ + k) (amoOp α lam (θ + k))).1
      (amoOp_spec α lam (θ + k))
  change spectrum ℂ (amoOp α lam (θ + k)) = spectrum ℂ (amoOp α lam θ)
  rw [amoOp_eq h1]

lemma specOf_add_nat (α lam θ : ℝ) (n : ℕ) :
    specOf α lam (θ + (n : ℝ) * α) = specOf α lam θ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : θ + ((n + 1 : ℕ) : ℝ) * α = (θ + (n : ℝ) * α) + α := by push_cast; ring
      rw [h, specOf_shift, ih]

lemma specOf_sub_nat (α lam θ : ℝ) (n : ℕ) :
    specOf α lam (θ - (n : ℝ) * α) = specOf α lam θ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 := specOf_shift α lam (θ - ((n + 1 : ℕ) : ℝ) * α)
      have h3 : θ - ((n + 1 : ℕ) : ℝ) * α + α = θ - (n : ℝ) * α := by push_cast; ring
      rw [h3] at h2
      rw [← h2, ih]

lemma specOf_add_int (α lam θ : ℝ) (k : ℤ) :
    specOf α lam (θ + (k : ℝ) * α) = specOf α lam θ := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
    subst hn
    push_cast
    exact specOf_add_nat α lam θ _
  · rw [not_le] at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, -k = n := ⟨(-k).toNat, by omega⟩
    have hk' : (k : ℝ) = -(n : ℝ) := by
      have : (k : ℤ) = -(n : ℤ) := by omega
      rw [this]; push_cast; ring
    rw [hk']
    have h : θ + -(n : ℝ) * α = θ - (n : ℝ) * α := by ring
    rw [h]
    exact specOf_sub_nat α lam θ n

/-! ### Closeness of the coefficients -/

lemma amoCoeff_norm_sub_le (α lam φ ψ : ℝ) (n : ℤ) :
    ‖amoCoeff α lam φ n - amoCoeff α lam ψ n‖ ≤ 4 * Real.pi * |lam| * |φ - ψ| := by
  have hsub : amoCoeff α lam φ n - amoCoeff α lam ψ n
      = ((2 * lam * (Real.cos (2 * Real.pi * (φ + (n : ℝ) * α))
          - Real.cos (2 * Real.pi * (ψ + (n : ℝ) * α))) : ℝ) : ℂ) := by
    simp only [amoCoeff]; push_cast; ring
  rw [hsub, norm_ofReal, abs_mul, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  have hcos : |Real.cos (2 * Real.pi * (φ + (n : ℝ) * α))
      - Real.cos (2 * Real.pi * (ψ + (n : ℝ) * α))| ≤ 2 * Real.pi * |φ - ψ| := by
    calc |Real.cos (2 * Real.pi * (φ + (n : ℝ) * α))
            - Real.cos (2 * Real.pi * (ψ + (n : ℝ) * α))|
        ≤ |2 * Real.pi * (φ + (n : ℝ) * α) - 2 * Real.pi * (ψ + (n : ℝ) * α)| :=
          Real.abs_cos_sub_cos_le _ _
      _ = |2 * Real.pi * (φ - ψ)| := by congr 1; ring
      _ = 2 * Real.pi * |φ - ψ| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [h2]
  calc 2 * |lam| * |Real.cos (2 * Real.pi * (φ + (n : ℝ) * α))
          - Real.cos (2 * Real.pi * (ψ + (n : ℝ) * α))|
      ≤ 2 * |lam| * (2 * Real.pi * |φ - ψ|) := by gcongr
    _ = 4 * Real.pi * |lam| * |φ - ψ| := by ring

/-! ### The density of the rotation orbit in `ℝ` -/

lemma exists_int_approx (α : ℝ) (hα : Irrational α) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m k : ℤ, |(m : ℝ) * α + (k : ℝ) - y| < ε := by
  have hd : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using hα
  have hy : y ∈ closure (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) := by
    rw [hd.closure_eq]; exact Set.mem_univ y
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hy ε hε
  obtain ⟨m, k, hmk⟩ := AddSubgroup.mem_closure_pair.1 hz
  refine ⟨m, k, ?_⟩
  have hz' : z = (m : ℝ) * α + (k : ℝ) := by
    rw [← hmk]
    simp [zsmul_eq_mul]
  rw [← hz', abs_sub_comm]
  exact hdist

/-! ### The one-sided spectral closeness lemma -/

lemma spectrum_subset_of_close {φ ψ : ℝ} {H H' : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam φ H) (hH' : IsAlmostMathieuOperator α lam ψ H')
    {γ : ℝ} (hclose : |φ - ψ| < γ / (4 * Real.pi * |lam| + 1)) :
    ∀ z ∈ spectrum ℂ H, ∃ z' ∈ spectrum ℂ H', ‖z - z'‖ ≤ γ := by
  have hK : (0 : ℝ) < 4 * Real.pi * |lam| + 1 := by positivity
  have hnorm : ‖H - H'‖ ≤ (4 * Real.pi * |lam| + 1) * |φ - ψ| :=
    norm_sub_le_of_coeffs
      (c := amoCoeff α lam φ) (c' := amoCoeff α lam ψ)
      (K := (4 * Real.pi * |lam| + 1) * |φ - ψ|)
      (fun n => by
        calc ‖amoCoeff α lam φ n - amoCoeff α lam ψ n‖
            ≤ 4 * Real.pi * |lam| * |φ - ψ| := amoCoeff_norm_sub_le α lam φ ψ n
          _ ≤ (4 * Real.pi * |lam| + 1) * |φ - ψ| := by
              have : (0:ℝ) ≤ |φ - ψ| := abs_nonneg _
              nlinarith)
      ((isAMO_iff_isJacobiOp α lam φ H).1 hH)
      ((isAMO_iff_isJacobiOp α lam ψ H').1 hH')
  have hlt : ‖H - H'‖ < γ := by
    refine lt_of_le_of_lt hnorm ?_
    have h2 : |φ - ψ| * (4 * Real.pi * |lam| + 1) < γ := (lt_div_iff₀ hK).mp hclose
    linarith
  intro z hz
  exact spectrum_perturb H H' (amo_isSelfAdjoint hH) (amo_isSelfAdjoint hH') hz hlt

/-! ### Phase independence -/

theorem specOf_subset (α lam : ℝ) (hα : Irrational α) (θ θ' : ℝ) :
    specOf α lam θ ⊆ specOf α lam θ' := by
  have hK : (0 : ℝ) < 4 * Real.pi * |lam| + 1 := by positivity
  have key : ∀ z ∈ specOf α lam θ, ∀ γ : ℝ, 0 < γ →
      ∃ z' ∈ specOf α lam θ', ‖z - z'‖ ≤ γ := by
    intro z hz γ hγ
    have hδ : 0 < γ / (4 * Real.pi * |lam| + 1) := div_pos hγ hK
    obtain ⟨m, k, hmk⟩ := exists_int_approx α hα (θ' - θ) hδ
    have hclose : |(θ + (m : ℝ) * α) - (θ' - (k : ℝ))| < γ / (4 * Real.pi * |lam| + 1) := by
      have heq : (θ + (m : ℝ) * α) - (θ' - (k : ℝ)) = (m : ℝ) * α + (k : ℝ) - (θ' - θ) := by
        ring
      rw [heq]
      exact hmk
    have hφ : specOf α lam (θ + (m : ℝ) * α) = specOf α lam θ := specOf_add_int α lam θ m
    have hψ : specOf α lam (θ' - (k : ℝ)) = specOf α lam θ' := by
      have h1 : θ' - (k : ℝ) = θ' + (((-k : ℤ)) : ℝ) := by push_cast; ring
      rw [h1, specOf_period]
    have hsub : ∀ z ∈ specOf α lam (θ + (m : ℝ) * α),
        ∃ z' ∈ specOf α lam (θ' - (k : ℝ)), ‖z - z'‖ ≤ γ :=
      spectrum_subset_of_close (amoOp_spec α lam (θ + (m : ℝ) * α))
        (amoOp_spec α lam (θ' - (k : ℝ))) hclose
    rw [hφ, hψ] at hsub
    exact hsub z hz
  intro z hz
  have hcl : z ∈ closure (specOf α lam θ') := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨z', hz', hd⟩ := key z hz (ε / 2) (by linarith)
    exact ⟨z', hz', by rw [dist_eq_norm]; linarith⟩
  have hc : IsClosed (specOf α lam θ') := spectrum.isClosed (amoOp α lam θ')
  exact hc.closure_eq ▸ hcl

end OpBasics

open OpBasics

theorem prove_OpBasics : Work.TMContract.P_OpBasics := by
  refine ⟨?_, ?_, ?_⟩
  · intro α lam θ
    exact amo_exists α lam θ
  · intro α lam θ H h
    exact amo_isSelfAdjoint h
  · intro α lam θ θ' hα H H' h h'
    have h1 : spectrum ℂ H = specOf α lam θ := specOf_eq_of_AMO h
    have h2 : spectrum ℂ H' = specOf α lam θ' := specOf_eq_of_AMO h'
    rw [h1, h2, Set.Subset.antisymm_iff]
    exact ⟨specOf_subset α lam hα θ θ', specOf_subset α lam hα θ' θ⟩

end Work.TMComp

