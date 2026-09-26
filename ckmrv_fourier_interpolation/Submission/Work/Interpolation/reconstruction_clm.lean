import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs
import Submission.Work.Sampling.coeffs_continuous_linear
import Submission.Work.Sampling.summable_norm_mul_pow_samples
import Submission.Work.Interpolation.weight_sum_le
import Submission.Work.Interpolation.fourier_seminorm_bound
import Submission.Work.Interpolation.iteratedFDeriv_sample_bound

namespace Work.Interpolation

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap BigOperators
open Filter Topology




lemma coeffs_add (n k₀ : ℕ) [NeZero n] (f g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    coeffs n k₀ (f + g) = coeffs n k₀ f + coeffs n k₀ g := by
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n k₀
  funext i
  rw [← congrFun (hC (f + g)) i, map_add]
  simp only [Pi.add_apply]
  rw [congrFun (hC f) i, congrFun (hC g) i]

lemma coeffs_smul (n k₀ : ℕ) [NeZero n] (a : ℂ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    coeffs n k₀ (a • f) = a • coeffs n k₀ f := by
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n k₀
  funext i
  rw [← congrFun (hC (a • f)) i, map_smul]
  simp only [Pi.smul_apply]
  rw [congrFun (hC f) i]

theorem reconstruction_clm (n k₀ : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin n))
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ i : Set.Ici k₀ × Fin 4, (SchwartzMap.seminorm ℂ k l) (basis i).1
        ≤ C * ((i.1.1 : ℝ) + 1) ^ N) :
    ∃ Λ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ,
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        Λ f = f x - ∑' i : Set.Ici k₀ × Fin 4, (coeffs n k₀ f i) * (basis i).1 x := by
  classical
  obtain ⟨C₀, N₀, hC₀, hgrowth⟩ := growth 0 0
  let L : ℕ := N₀ + 2
  let fam : SeminormFamily ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) (ℕ × ℕ) :=
    schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ
  obtain ⟨s00, C00, hC00, h00⟩ := fourier_seminorm_bound n 0 0
  obtain ⟨s01, C01, hC01, h01⟩ := fourier_seminorm_bound n 0 1
  obtain ⟨s20, C20, hC20, h20⟩ := fourier_seminorm_bound n (2 * L) 0
  obtain ⟨s21, C21, hC21, h21⟩ := fourier_seminorm_bound n (2 * L) 1
  let A0 : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (2 * L, 0), (2 * L, 1)}
  let B : Finset (ℕ × ℕ) := A0 ∪ (s00 ∪ (s01 ∪ (s20 ∪ s21)))
  let K₁ : ℝ := 1 + C00 + C01 + C20 + C21
  let K₂ : ℝ := 2 * K₁
  have hK₁ge : 1 ≤ K₁ := by simp only [K₁]; linarith
  have hK₁nn : 0 ≤ K₁ := le_trans zero_le_one hK₁ge
  have hC00K : C00 ≤ K₁ := by simp only [K₁]; linarith
  have hC01K : C01 ≤ K₁ := by simp only [K₁]; linarith
  have hC20K : C20 ≤ K₁ := by simp only [K₁]; linarith
  have hC21K : C21 ≤ K₁ := by simp only [K₁]; linarith
  have hsub00 : s00 ⊆ B := by intro y hy; simp only [B, A0, Finset.mem_union]; tauto
  have hsub01 : s01 ⊆ B := by intro y hy; simp only [B, A0, Finset.mem_union]; tauto
  have hsub20 : s20 ⊆ B := by intro y hy; simp only [B, A0, Finset.mem_union]; tauto
  have hsub21 : s21 ⊆ B := by intro y hy; simp only [B, A0, Finset.mem_union]; tauto
  have hmem00 : (0, 0) ∈ B := by simp [B, A0]
  have hmem01 : (0, 1) ∈ B := by simp [B, A0]
  have hmem20 : (2 * L, 0) ∈ B := by simp [B, A0]
  have hmem21 : (2 * L, 1) ∈ B := by simp [B, A0]
  have hsup_le : ∀ (a b : ℕ), (a, b) ∈ B → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (SchwartzMap.seminorm ℂ a b) f ≤ B.sup fam f := by
    intro a b hab f
    exact (Finset.le_sup (f := fam) hab) f
  have hfsem : ∀ (a b : ℕ), (a, b) ∈ B → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (SchwartzMap.seminorm ℂ a b) f ≤ K₁ * B.sup fam f := by
    intro a b hab f
    refine (hsup_le a b hab f).trans ?_
    calc B.sup fam f = 1 * B.sup fam f := by ring
      _ ≤ K₁ * B.sup fam f :=
          mul_le_mul hK₁ge le_rfl (apply_nonneg _ _) hK₁nn
  have hfhat : ∀ (a b : ℕ) (s : Finset (ℕ × ℕ)) (C : ℝ), s ⊆ B → C ≤ K₁ →
      (∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (SchwartzMap.seminorm ℂ a b) (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
          ≤ C * s.sup fam f) →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (SchwartzMap.seminorm ℂ a b) (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
          ≤ K₁ * B.sup fam f := by
    intro a b s C hsub hCK hf f
    have h1 : s.sup fam f ≤ B.sup fam f := Finset.sup_mono (f := fam) hsub f
    exact (hf f).trans (mul_le_mul hCK h1 (apply_nonneg _ _) hK₁nn)
  have hhat00 := hfhat 0 0 s00 C00 hsub00 hC00K h00
  have hhat01 := hfhat 0 1 s01 C01 hsub01 hC01K h01
  have hhat20 := hfhat (2 * L) 0 s20 C20 hsub20 hC20K h20
  have hhat21 := hfhat (2 * L) 1 s21 C21 hsub21 hC21K h21
  have hterm : ∀ (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (i : Set.Ici k₀ × Fin 4),
      ‖coeffs n k₀ f i‖ * (1 + (i.1.1 : ℝ))^L ≤ K₂ * B.sup fam f := by
    intro f i
    obtain ⟨k, j⟩ := i
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl
    · have hc : coeffs n k₀ f (k, (0 : Fin 4)) =
          f (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) := by
        simp only [coeffs, Function.uncurry_apply_pair]; push_cast; rfl
      rw [hc]
      have hb := iteratedFDeriv_sample_bound n f 0 L (k:ℕ)
      rw [norm_iteratedFDeriv_zero] at hb
      calc ‖f (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ * (1 + ((k:ℕ):ℝ))^L
          ≤ (SchwartzMap.seminorm ℂ (2*L) 0) f + (SchwartzMap.seminorm ℂ 0 0) f := hb
        _ ≤ K₁ * B.sup fam f + K₁ * B.sup fam f :=
            add_le_add (hfsem (2*L) 0 hmem20 f) (hfsem 0 0 hmem00 f)
        _ = K₂ * B.sup fam f := by simp only [K₂]; ring
    · have hc : coeffs n k₀ f (k, (1 : Fin 4)) =
          (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
            (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) := by
        simp only [coeffs, Function.uncurry_apply_pair]; push_cast; rfl
      rw [hc]
      have hb := iteratedFDeriv_sample_bound n
        (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) 0 L (k:ℕ)
      rw [norm_iteratedFDeriv_zero] at hb
      calc ‖(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
              (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ * (1 + ((k:ℕ):ℝ))^L
          ≤ (SchwartzMap.seminorm ℂ (2*L) 0)
              (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
            + (SchwartzMap.seminorm ℂ 0 0)
              (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) := hb
        _ ≤ K₁ * B.sup fam f + K₁ * B.sup fam f :=
            add_le_add (hhat20 f) (hhat00 f)
        _ = K₂ * B.sup fam f := by simp only [K₂]; ring
    · have hc : coeffs n k₀ f (k, (2 : Fin 4)) =
          fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1) := by
        simp only [coeffs, Function.uncurry_apply_pair]
        push_cast
        rw [Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt f _)]
      rw [hc]
      have hb := iteratedFDeriv_sample_bound n f 1 L (k:ℕ)
      rw [norm_iteratedFDeriv_one] at hb
      have hop : ‖fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1)‖
          ≤ ‖fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ := by
        calc _ ≤ ‖fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖
                * ‖realIncl (n:=n) 1‖ := ContinuousLinearMap.le_opNorm _ _
          _ = _ := by rw [Work.Sampling.realIncl_norm_one, mul_one]
      calc ‖fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1)‖
              * (1 + ((k:ℕ):ℝ))^L
          ≤ ‖fderiv ℝ (⇑f) (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖
              * (1 + ((k:ℕ):ℝ))^L := mul_le_mul_of_nonneg_right hop (by positivity)
        _ ≤ (SchwartzMap.seminorm ℂ (2*L) 1) f + (SchwartzMap.seminorm ℂ 0 1) f := hb
        _ ≤ K₁ * B.sup fam f + K₁ * B.sup fam f :=
            add_le_add (hfsem (2*L) 1 hmem21 f) (hfsem 0 1 hmem01 f)
        _ = K₂ * B.sup fam f := by simp only [K₂]; ring
    · have hc : coeffs n k₀ f (k, (3 : Fin 4)) =
          fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
            (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1) := by
        simp only [coeffs, Function.uncurry_apply_pair]
        push_cast
        rw [Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt _ _)]
      rw [hc]
      have hb := iteratedFDeriv_sample_bound n
        (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) 1 L (k:ℕ)
      rw [norm_iteratedFDeriv_one] at hb
      have hop : ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
            (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1)‖
          ≤ ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
            (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ := by
        calc _ ≤ ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
                (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ * ‖realIncl (n:=n) 1‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = _ := by rw [Work.Sampling.realIncl_norm_one, mul_one]
      calc ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
              (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ)))) (realIncl (n:=n) 1)‖
              * (1 + ((k:ℕ):ℝ))^L
          ≤ ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
              (realIncl (n:=n) (Real.sqrt (2 * ((k:ℕ):ℝ))))‖ * (1 + ((k:ℕ):ℝ))^L :=
            mul_le_mul_of_nonneg_right hop (by positivity)
        _ ≤ (SchwartzMap.seminorm ℂ (2*L) 1)
              (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
            + (SchwartzMap.seminorm ℂ 0 1)
              (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) := hb
        _ ≤ K₁ * B.sup fam f + K₁ * B.sup fam f :=
            add_le_add (hhat21 f) (hhat01 f)
        _ = K₂ * B.sup fam f := by simp only [K₂]; ring
  have hsumm : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      Summable (fun i : Set.Ici k₀ × Fin 4 => coeffs n k₀ f i * (basis i).1 x) := by
    intro f
    have ha := Work.Sampling.rapidlyDecreasing_coeffs n k₀ f
    have h1 : Summable (fun i : Set.Ici k₀ × Fin 4 =>
        ‖coeffs n k₀ f i‖ * (((i.1.1 : ℕ) : ℝ) + 1)^N₀) :=
      Work.Sampling.summable_norm_mul_pow_samples k₀ N₀ (coeffs n k₀ f) ha
    refine Summable.of_norm_bounded (h1.mul_left C₀) ?_
    intro i
    have hci : ‖(basis i).1 x‖ ≤ C₀ * (((i.1.1 : ℕ) : ℝ) + 1)^N₀ := by
      calc ‖(basis i).1 x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) (basis i).1 :=
            SchwartzMap.norm_le_seminorm ℂ _ x
        _ ≤ C₀ * (((i.1.1 : ℕ) : ℝ) + 1)^N₀ := hgrowth i
    rw [norm_mul]
    calc ‖coeffs n k₀ f i‖ * ‖(basis i).1 x‖
        ≤ ‖coeffs n k₀ f i‖ * (C₀ * (((i.1.1 : ℕ) : ℝ) + 1)^N₀) :=
          mul_le_mul_of_nonneg_left hci (norm_nonneg _)
      _ = C₀ * (‖coeffs n k₀ f i‖ * (((i.1.1 : ℕ) : ℝ) + 1)^N₀) := by ring
  let T : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) → ℂ :=
    fun f => ∑' i : Set.Ici k₀ × Fin 4, coeffs n k₀ f i * (basis i).1 x
  let A : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) → ℂ := fun f => f x - T f
  have hAadd : ∀ f g, A (f + g) = A f + A g := by
    intro f g
    have h1 : (fun i : Set.Ici k₀ × Fin 4 => coeffs n k₀ (f + g) i * (basis i).1 x)
        = fun i => coeffs n k₀ f i * (basis i).1 x + coeffs n k₀ g i * (basis i).1 x := by
      funext i
      rw [congrFun (coeffs_add n k₀ f g) i, Pi.add_apply]
      ring
    simp only [A, T, add_apply]
    rw [h1, Summable.tsum_add (hsumm f) (hsumm g)]
    ring
  have hAsmul : ∀ (a : ℂ) f, A (a • f) = a • A f := by
    intro a f
    have h1 : (fun i : Set.Ici k₀ × Fin 4 => coeffs n k₀ (a • f) i * (basis i).1 x)
        = fun i => a * (coeffs n k₀ f i * (basis i).1 x) := by
      funext i
      rw [congrFun (coeffs_smul n k₀ a f) i, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [A, T, smul_apply]
    rw [h1, tsum_mul_left, smul_eq_mul]
    ring
  have hbound : ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ‖A f‖ ≤ C * s.sup fam f := by
    refine ⟨B, 1 + 8 * K₂ * C₀, by positivity, ?_⟩
    intro f
    have hwS : Summable (fun i : Set.Ici k₀ × Fin 4 => 1 / (1 + (i.1.1 : ℝ))^2) :=
      (weight_sum_le k₀).1
    have hcomp : Summable (fun i : Set.Ici k₀ × Fin 4 =>
        (K₂ * C₀ * B.sup fam f) * (1 / (1 + (i.1.1 : ℝ))^2)) := hwS.mul_left _
    have hdom : ∀ i : Set.Ici k₀ × Fin 4,
        ‖coeffs n k₀ f i * (basis i).1 x‖ ≤
          (K₂ * C₀ * B.sup fam f) * (1 / (1 + (i.1.1 : ℝ))^2) := by
      intro i
      have h1 : ‖coeffs n k₀ f i‖ ≤ K₂ * B.sup fam f / (1 + (i.1.1 : ℝ))^L := by
        rw [le_div_iff₀ (by positivity)]
        exact hterm f i
      have h2 : ‖(basis i).1 x‖ ≤ C₀ * (1 + (i.1.1 : ℝ))^N₀ := by
        calc ‖(basis i).1 x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) (basis i).1 :=
              SchwartzMap.norm_le_seminorm ℂ _ x
          _ ≤ C₀ * ((i.1.1 : ℝ) + 1)^N₀ := hgrowth i
          _ = C₀ * (1 + (i.1.1 : ℝ))^N₀ := by rw [add_comm]
      rw [norm_mul]
      calc ‖coeffs n k₀ f i‖ * ‖(basis i).1 x‖
          ≤ (K₂ * B.sup fam f / (1 + (i.1.1 : ℝ))^L) * (C₀ * (1 + (i.1.1 : ℝ))^N₀) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (K₂ * C₀ * B.sup fam f) * (1 / (1 + (i.1.1 : ℝ))^2) := by
            have hk : (0:ℝ) < 1 + (i.1.1 : ℝ) := by positivity
            rw [show L = N₀ + 2 from rfl, pow_add]
            field_simp
    have hsum' : Summable (fun i : Set.Ici k₀ × Fin 4 => ‖coeffs n k₀ f i * (basis i).1 x‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hdom hcomp
    have hTs : ∑' i : Set.Ici k₀ × Fin 4, ‖coeffs n k₀ f i * (basis i).1 x‖
        ≤ 8 * K₂ * C₀ * B.sup fam f := by
      calc ∑' i : Set.Ici k₀ × Fin 4, ‖coeffs n k₀ f i * (basis i).1 x‖
          ≤ ∑' i : Set.Ici k₀ × Fin 4,
              (K₂ * C₀ * B.sup fam f) * (1 / (1 + (i.1.1 : ℝ))^2) :=
            Summable.tsum_le_tsum hdom hsum' hcomp
        _ = (K₂ * C₀ * B.sup fam f)
              * ∑' i : Set.Ici k₀ × Fin 4, 1 / (1 + (i.1.1 : ℝ))^2 := tsum_mul_left
        _ ≤ (K₂ * C₀ * B.sup fam f) * 8 :=
            mul_le_mul_of_nonneg_left (weight_sum_le k₀).2 (by positivity)
        _ = 8 * K₂ * C₀ * B.sup fam f := by ring
    have hT : ‖T f‖ ≤ 8 * K₂ * C₀ * B.sup fam f := by
      simp only [T]
      calc ‖∑' i : Set.Ici k₀ × Fin 4, coeffs n k₀ f i * (basis i).1 x‖
          ≤ ∑' i : Set.Ici k₀ × Fin 4, ‖coeffs n k₀ f i * (basis i).1 x‖ :=
            norm_tsum_le_tsum_norm (hsumm f).norm
        _ ≤ 8 * K₂ * C₀ * B.sup fam f := hTs
    have hfx : ‖f x‖ ≤ B.sup fam f :=
      (SchwartzMap.norm_le_seminorm ℂ f x).trans (hsup_le 0 0 hmem00 f)
    simp only [A]
    calc ‖f x - T f‖ ≤ ‖f x‖ + ‖T f‖ := norm_sub_le _ _
      _ ≤ B.sup fam f + 8 * K₂ * C₀ * B.sup fam f := add_le_add hfx hT
      _ = (1 + 8 * K₂ * C₀) * B.sup fam f := by ring
  exact ⟨SchwartzMap.mkCLMtoNormedSpace A hAadd hAsmul hbound, fun f => rfl⟩

end Work.Interpolation
