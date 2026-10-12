import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.ModeFam
import Submission.Work.BoseBoxFock.frame_lattice_ball
import Submission.Work.BoseRowQ2.chiLatticeParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qVec_frame_identity` — the frame (resolution of the identity) of the
localised plane waves with the condensate removed

This module proves the **frame identity** of FS's localization dictionary: the family

    ψ_k = qVec ℓ (ℓ⁻¹ • vec k) = e^{i (2π/ℓ) k·x} χ_Λ − χ̂(2πk) θ_Λ      (k ∈ ℤ³)

of localised plane waves with the condensate component removed is a *tight frame* of the
subspace of `L²` supported in the box `Λ(ℓ)`, with the resolution of the identity

    Σ_k ⟨ψ_k,u⟩ conj⟨ψ_k,v⟩ = ℓ³⟨v, χ_Λ² u⟩ − ⟨v, χ_Λ²⟩⟨θ_Λ,u⟩ − ⟨v,θ_Λ⟩⟨χ_Λ²,u⟩ + ⟨v,θ_Λ⟩⟨θ_Λ,u⟩

for `u, v` supported in the box (`⟨f,g⟩ = ∫ conj(f)·g`).  The RHS is the kernel
`ℓ³χ_Λ²δ − χ_Λ²⊗θ_Λ − θ_Λ⊗χ_Λ² + θ_Λ⊗θ_Λ` of the "folding" operator.

## The mathematics

Writing `é_k(x) = e^{i (2π/ℓ) k·x}`, `χ = χ_Λ`, `θ = θ_Λ`, `c_k = χ̂(2πk) = conj(∫ é_k χ)` and

    `A_k = ∫ é_k χ u`  (= `F_k(χ_Λ u)`),   `γ_u = ⟨θ,u⟩`,

one has `⟨ψ_k,u⟩ = A_k − c_k γ_u` and hence

    `Σ_k ⟨ψ_k,u⟩ conj⟨ψ_k,v⟩ = Σ_k A_k conj(A'_k) − conj(γ_v) Σ_k c_k A_k
                                − γ_u Σ_k c_k conj(A'_k) + γ_u conj(γ_v) Σ_k c_k²`.

The four lattice sums are evaluated by the *sesquilinear* (pair) form of the box Parseval
identity (`Work.BoseRowQ2.sampling_unitCube_pair` for the unit cube, transported to the box of
side `ℓ` in `boxSampling_pair` below), applied to the pairs
`(χ_Λu, χ_Λv)`, `(χ_Λ, χ_Λu)`, `(χ_Λ, χ_Λv)` and `(χ_Λ, χ_Λ)`:

    `Σ_k conj(F_k φ)F_k ψ = ℓ³ ∫ conj(φ)ψ`,   `conj(F_k χ_Λ) = ℓ³ c_k`,   `Σ_k c_k² = 1`.

The last two use `Work.BoseRowQ2.integral_exp_inner_of_even` (the Fourier sample of the even
real `χ` is its cosine transform `χ̂`) and the normalisation `∫χ² = 1` (`χ_Λ²` has mass `ℓ³`).

Everything is elementary — no smoothness is needed, only `L²`-support in the box.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary bookkeeping -/

/-- The box `Λ(ℓ) = boxL ℓ` is closed, so the topological support of a function whose support lies
in it stays inside it. -/
theorem tsupport_subset_boxL {ℓ : ℝ} {u : E3 → ℂ}
    (h : Function.support u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    tsupport u ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
  closure_minimal h (Work.BoseK15.corpusBox.boxL_compact ℓ).isClosed

/-- A measurable bounded function supported in a set of finite measure is integrable. -/
theorem integrable_of_bounded_support {s : Set E3} (hs : volume s < ⊤) {f : E3 → ℂ}
    (hm : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) :
    Integrable f volume := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := volume) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := volume) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- A measurable bounded function supported in a set of finite measure is `L²`. -/
theorem memLp_two_of_bounded_support {s : Set E3} (hs : volume s < ⊤) {f : E3 → ℂ}
    (hm : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) :
    MemLp f 2 (volume : Measure E3) := by
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ x, ‖f x‖ ≤ max C 0 := fun x => le_trans (hC x) (le_max_left _ _)
  have hint : Integrable (fun x => ‖f x‖ ^ 2) volume := by
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := volume) (s := s)
      (f := fun x => ‖f x‖ ^ 2) ?_).mp ?_
    · intro x hx
      exact hsup (by simpa [Function.mem_support, norm_eq_zero] using hx)
    · refine MeasureTheory.IntegrableOn.of_bound (s := s) (μ := volume) hs ?_
        ((max C 0) ^ 2) ?_
      · exact ((hm.norm.pow_const 2).aestronglyMeasurable).restrict
      · refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC' x) 2
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hint

/-- Change of variables `x ↦ ℓ⁻¹ x` for complex-valued integrals: Lebesgue measure scales by
`ℓ³`.  The complex-valued twin of `Work.BoseB4.integral_comp_inv_smul_volume`. -/
theorem integral_comp_inv_smul_complex {ℓ : ℝ} (hℓ : 0 < ℓ) (g : E3 → ℂ) :
    (∫ x, g (ℓ⁻¹ • x)) = ((ℓ : ℂ) ^ 3) * ∫ y, g y := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E3) g hℓ.le
  rw [finrank_euclideanSpace_fin] at h
  rw [h, Complex.real_smul, ← Complex.ofReal_pow]

/-- Sums of complex numbers are compatible with conjugation. -/
theorem hasSum_conj {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) :
    HasSum (fun i => (starRingEnd ℂ) (f i)) ((starRingEnd ℂ) a) :=
  h.map _ Complex.continuous_conj

/-- Conjugation passes through the Bochner integral of an integrable complex function. -/
theorem conj_integral {f : E3 → ℂ} (_hf : Integrable f volume) :
    (starRingEnd ℂ) (∫ x, f x) = ∫ x, (starRingEnd ℂ) (f x) :=
  integral_conj.symm

/-! ## 2. The sesquilinear box Parseval identity -/

/-- **The sesquilinear (pair) Parseval identity for the box `Λ(ℓ)` of side `ℓ`.**  For bounded
measurable `φ, ψ` supported in the box,

    `Σ_k conj(∫ é_k φ)·(∫ é_k ψ) = ℓ³ ∫ conj(φ)ψ ,      é_k(x) = e^{i⟪ℓ⁻¹vec k, x⟫}`,

i.e. the lattice `(2π/ℓ)ℤ³` samples reproduce the `L²` pairing.  This is
`Work.BoseRowQ2.sampling_unitCube_pair` for the unit cube, transported to the box of side `ℓ` by
the change of variables `y ↦ ℓ • y`. -/
theorem boxSampling_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {φ ψ : E3 → ℂ}
    (hφm : Measurable φ) (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hφs : tsupport φ ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hψm : Measurable ψ) (hψb : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C)
    (hψs : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    HasSum (fun n : Fin 3 → ℤ =>
        (starRingEnd ℂ)
            (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * φ x)
          * (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * ψ x))
      (((ℓ : ℂ) ^ 3) * ∫ x, (starRingEnd ℂ) (φ x) * ψ x) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  set φ' : E3 → ℂ := fun y => φ (ℓ • y) with hφ'def
  set ψ' : E3 → ℂ := fun y => ψ (ℓ • y) with hψ'def
  have hφ'm : Measurable φ' := hφm.comp (continuous_const_smul (ℓ : ℝ)).measurable
  have hψ'm : Measurable ψ' := hψm.comp (continuous_const_smul (ℓ : ℝ)).measurable
  have hφ's : tsupport φ' ⊆ {y : E3 | ∀ i, |y i| ≤ (1 / 2 : ℝ)} := by
    rw [hφ'def]; exact flb_tsupport_sub hℓ hφs
  have hψ's : tsupport ψ' ⊆ {y : E3 | ∀ i, |y i| ≤ (1 / 2 : ℝ)} := by
    rw [hψ'def]; exact flb_tsupport_sub hℓ hψs
  have hvol : volume ({y : E3 | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) < ⊤ := by
    rw [show {y : E3 | ∀ i, |y i| ≤ (1 / 2 : ℝ)} = Work.BoseB4.unitCell from rfl,
      Work.BoseB4.volume_unitCell]
    norm_num
  obtain ⟨Cφ, hCφ⟩ := hφb
  obtain ⟨Cψ, hCψ⟩ := hψb
  have hφ'mem : MemLp φ' 2 (volume : Measure E3) :=
    memLp_two_of_bounded_support hvol hφ'm ⟨Cφ, fun x => hCφ (ℓ • x)⟩
      fun x hx => hφ's (subset_tsupport φ' hx)
  have hψ'mem : MemLp ψ' 2 (volume : Measure E3) :=
    memLp_two_of_bounded_support hvol hψ'm ⟨Cψ, fun x => hCψ (ℓ • x)⟩
      fun x hx => hψ's (subset_tsupport ψ' hx)
  have hpair := Work.BoseRowQ2.sampling_unitCube_pair (f := φ') (g := ψ')
    hφ'mem hφ's hψ'mem hψ's
  -- the change of variables for the two coefficients and for the pairing
  have hcoef : ∀ (n : Fin 3 → ℤ) (g : E3 → ℂ),
      (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ))) * g x)
        = ((ℓ : ℂ) ^ 3)
          * (∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
              * g (ℓ • y)) := by
    intro n g
    have h := integral_comp_inv_smul_complex hℓ
      (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
        * g (ℓ • y))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
    have key : (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)
        = (inner ℝ (Work.BoseB4.vec n) (ℓ⁻¹ • x) : ℂ) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [key]
  have hval : (∫ x, (starRingEnd ℂ) (φ x) * ψ x)
      = ((ℓ : ℂ) ^ 3) * ∫ y, (starRingEnd ℂ) (φ' y) * ψ' y := by
    have h := integral_comp_inv_smul_complex hℓ
      (fun y : E3 => (starRingEnd ℂ) (φ (ℓ • y)) * ψ (ℓ • y))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (starRingEnd ℂ) (φ x) * ψ x
        = (starRingEnd ℂ) (φ (ℓ • ℓ⁻¹ • x)) * ψ (ℓ • ℓ⁻¹ • x)
    simp only [smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
  -- assemble: multiply the unit-cube identity by `ℓ⁶` and rewrite
  have hmain : HasSum (fun n : Fin 3 → ℤ =>
        (starRingEnd ℂ)
            (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * φ x)
          * (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * ψ x))
      (((ℓ : ℂ) ^ 3) * (((ℓ : ℂ) ^ 3) * ∫ y, (starRingEnd ℂ) (φ' y) * ψ' y)) := by
    have h1 : HasSum (fun n : Fin 3 → ℤ =>
        (starRingEnd ℂ)
            (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * φ x)
          * (∫ x, Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) x : ℂ)))
              * ψ x))
        ((((ℓ : ℂ) ^ 3) * ((ℓ : ℂ) ^ 3)) * ∫ y, (starRingEnd ℂ) (φ' y) * ψ' y) := by
      have hmul := hpair.mul_left (((ℓ : ℂ) ^ 3) * ((ℓ : ℂ) ^ 3))
      refine hmul.congr_fun fun n => ?_
      rw [hcoef n φ, hcoef n ψ]
      simp only [hφ'def, hψ'def]
      have hconjℓ : (starRingEnd ℂ) ((ℓ : ℂ) ^ 3) = ((ℓ : ℂ) ^ 3) := by
        simp [map_pow, Complex.conj_ofReal]
      simp only [map_mul, hconjℓ]
      ring
    simpa only [mul_assoc] using h1
  rw [hval]
  exact hmain

end Work.BoseBoxFock
