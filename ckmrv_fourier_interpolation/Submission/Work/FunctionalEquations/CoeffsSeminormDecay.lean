import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.CoeffsSeminormDecayFamily
import Submission.Work.FunctionalEquations.SeminormCompare

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap NNReal

noncomputable section

/-- The four samples at a point with `k = 0`. -/
lemma coeffs_zero_eq {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k₀ : ℕ) (k : Set.Ici k₀) (hk : k.1 = 0) :
    coeffs n k₀ f (k, 0) = f 0 ∧
    coeffs n k₀ f (k, 1) = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) 0 ∧
    coeffs n k₀ f (k, 2) = fderiv ℝ (⇑f) 0 (realIncl (n := n) 1) ∧
    coeffs n k₀ f (k, 3)
      = fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) 0 (realIncl (n := n) 1) := by
  have hs0 : Real.sqrt (2 * (k.1 : ℝ)) = 0 := by simp [hk]
  have hx0 : realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))) = 0 := by
    rw [hs0, Work.Sampling.realIncl_eq_smul, zero_smul]
  have hr0 : realIncl (n := n) 0 = 0 := by
    rw [Work.Sampling.realIncl_eq_smul, zero_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [coeffs, Function.uncurry_apply_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, hx0]
  · simp only [coeffs, Function.uncurry_apply_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, hx0]
  · simp only [coeffs, Function.uncurry_apply_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, hs0]
    exact Work.Sampling.deriv_comp_realIncl (by rw [hr0]; exact SchwartzMap.hasFDerivAt f 0)
  · simp only [coeffs, Function.uncurry_apply_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, hs0]
    exact Work.Sampling.deriv_comp_realIncl
      (by rw [hr0]
          exact SchwartzMap.hasFDerivAt (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) 0)

/-- The value of `coeffs` does not depend on the starting index `k₀`. -/
lemma coeffs_eq_of_val {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k₀ : ℕ)
    (a : Set.Ici k₀) (b : Set.Ici 1) (h : a.1 = b.1) (j : Fin 4) :
    coeffs n k₀ f (a, j) = coeffs n 1 f (b, j) := by
  simp only [coeffs, Function.uncurry_apply_pair]
  rw [h]

/-- **Polynomial decay of the CKMRV samples** in the pair of Schwartz seminorms
`(p,0)` and `(0,p)`, uniform in the Schwartz function `f`. -/
theorem CoeffsSeminormDecay {n : ℕ} [NeZero n] (k₀ N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ (f : 𝓢(E n, ℂ)) (i : SampleIdx k₀),
      ((i.1.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f i‖
        ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) := by
  obtain ⟨s, Cfam, hCfam0, hfam⟩ := CoeffsSeminormDecayFamily n N
  obtain ⟨t, Ct, hCt0, ht⟩ := coeffsSeminormDecay_fourierSeminorm (n := n) 0 0
  obtain ⟨u, Cu, hCu0, hu⟩ := coeffsSeminormDecay_fourierSeminorm (n := n) 0 1
  set S : Finset (ℕ × ℕ) := s ∪ t ∪ u with hSdef
  set p : ℕ := max (S.sup (fun q => q.1 + q.2)) 1 with hpdef
  obtain ⟨Csc, hCsc0, hsc⟩ := SeminormCompare (n := n) p
  set K : ℝ := max (max (max Cfam (max Ct Cu)) Csc) 1 with hKdef
  set C : ℝ := K * K with hCdef
  have h1K : (1 : ℝ) ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one h1K
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hCfamK : Cfam ≤ K := by
    rw [hKdef]
    calc Cfam ≤ max Cfam (max Ct Cu) := le_max_left _ _
      _ ≤ max (max Cfam (max Ct Cu)) Csc := le_max_left _ _
      _ ≤ max (max (max Cfam (max Ct Cu)) Csc) 1 := le_max_left _ _
  have hCtK : Ct ≤ K := by
    rw [hKdef]
    calc Ct ≤ max Ct Cu := le_max_left _ _
      _ ≤ max Cfam (max Ct Cu) := le_max_right _ _
      _ ≤ max (max Cfam (max Ct Cu)) Csc := le_max_left _ _
      _ ≤ max (max (max Cfam (max Ct Cu)) Csc) 1 := le_max_left _ _
  have hCuK : Cu ≤ K := by
    rw [hKdef]
    calc Cu ≤ max Ct Cu := le_max_right _ _
      _ ≤ max Cfam (max Ct Cu) := le_max_right _ _
      _ ≤ max (max Cfam (max Ct Cu)) Csc := le_max_left _ _
      _ ≤ max (max (max Cfam (max Ct Cu)) Csc) 1 := le_max_left _ _
  have hCscK : Csc ≤ K := by
    rw [hKdef]
    calc Csc ≤ max (max Cfam (max Ct Cu)) Csc := le_max_right _ _
      _ ≤ max (max (max Cfam (max Ct Cu)) Csc) 1 := le_max_left _ _
  have hKK : K ≤ C := by rw [hCdef]; nlinarith
  have hCfamC : Cfam ≤ C := le_trans hCfamK hKK
  have hCtC : Ct ≤ C := le_trans hCtK hKK
  have hCuC : Cu ≤ C := le_trans hCuK hKK
  have hCscC : Csc ≤ C := le_trans hCscK hKK
  -- bound for the finite supremum over `S`
  have hSbound : ∀ f : 𝓢(E n, ℂ),
      (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ Csc * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) := by
    intro f
    refine Seminorm.finset_sup_apply_le (by positivity) (fun q hq => ?_)
    have hqp : q.1 + q.2 ≤ p := by
      rw [hpdef]
      exact le_trans (Finset.le_sup (f := fun q : ℕ × ℕ => q.1 + q.2) hq) (le_max_left _ _)
    have h := hsc f q.1 q.2 hqp
    change (SchwartzMap.seminorm ℂ q.1 q.2) f ≤
      Csc * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)
    exact h
  have hsub_le : ∀ (r : Finset (ℕ × ℕ)), r ⊆ S →
      r.sup (schwartzSeminormFamily ℂ (E n) ℂ) ≤ S.sup (schwartzSeminormFamily ℂ (E n) ℂ) := by
    intro r hr
    exact Finset.sup_le (fun q hq =>
      Finset.le_sup (f := schwartzSeminormFamily ℂ (E n) ℂ) (hr hq))
  have hsub : ∀ (r : Finset (ℕ × ℕ)), r ⊆ S →
      ∀ f : 𝓢(E n, ℂ), (r.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    fun r hr f => Seminorm.le_def.mp (hsub_le r hr) f
  have hsS : s ⊆ S := by rw [hSdef]; intro x hx; simp [hx]
  have htS : t ⊆ S := by rw [hSdef]; intro x hx; simp [hx]
  have huS : u ⊆ S := by rw [hSdef]; intro x hx; simp [hx]
  have hpair : ∀ f : 𝓢(E n, ℂ),
      (0 : ℝ) ≤ (SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f :=
    fun f => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  refine ⟨C, hCnn, p, ?_⟩
  intro f i
  obtain ⟨k, j⟩ := i
  have keySNN : (0 : ℝ) ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := apply_nonneg _ _
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ K → c * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
      ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) := by
    intro c hc0 hcK
    calc c * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ K * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hcK keySNN
      _ ≤ K * (Csc * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)) :=
          mul_le_mul_of_nonneg_left (hSbound f) hK0
      _ = (K * Csc) * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) := by ring
      _ ≤ (K * K) * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCscK hK0) (hpair f)
      _ = C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f) := by rw [hCdef]
  rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
  · obtain ⟨h0, h1, h2, h3⟩ := coeffs_zero_eq f k₀ k hk0
    have hw : ((k.1 : ℝ) + 1) ^ N = 1 := by rw [hk0]; norm_num
    fin_cases j
    · change ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 0)‖
          ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)
      rw [h0, hw, one_mul]
      exact le_trans (SchwartzMap.norm_le_seminorm ℂ f 0)
        (le_trans (hsc f 0 0 (by omega)) (mul_le_mul_of_nonneg_right hCscC (hpair f)))
    · change ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 1)‖
          ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)
      rw [h1, hw, one_mul]
      exact le_trans (SchwartzMap.norm_le_seminorm ℂ
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) 0)
        (le_trans (ht f) (le_trans (mul_le_mul_of_nonneg_left (hsub t htS f) hCt0)
          (key Ct hCt0 hCtK)))
    · change ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 2)‖
          ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)
      rw [h2, hw, one_mul]
      refine le_trans ?_ (le_trans (hsc f 0 1 (by omega))
        (mul_le_mul_of_nonneg_right hCscC (hpair f)))
      refine le_trans ?_ (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f 1 0)
      rw [norm_iteratedFDeriv_one]
      calc ‖fderiv ℝ (⇑f) 0 (realIncl (n := n) 1)‖
          ≤ ‖fderiv ℝ (⇑f) 0‖ * ‖realIncl (n := n) 1‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (⇑f) 0‖ := by rw [Work.Sampling.realIncl_norm_one, mul_one]
    · change ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 3)‖
          ≤ C * ((SchwartzMap.seminorm ℂ p 0) f + (SchwartzMap.seminorm ℂ 0 p) f)
      rw [h3, hw, one_mul]
      refine le_trans ?_ (le_trans (hu f)
        (le_trans (mul_le_mul_of_nonneg_left (hsub u huS f) hCu0) (key Cu hCu0 hCuK)))
      refine le_trans ?_ (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ
        (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) 1 0)
      rw [norm_iteratedFDeriv_one]
      calc ‖(fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) 0)
              (realIncl (n := n) 1)‖
          ≤ ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) 0‖ *
              ‖realIncl (n := n) 1‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) 0‖ := by
            rw [Work.Sampling.realIncl_norm_one, mul_one]
  · have hk1 : 1 ≤ k.1 := hkpos
    have hcoeff : coeffs n k₀ f (k, j) = coeffs n 1 f (⟨k.1, hk1⟩, j) :=
      coeffs_eq_of_val f k₀ k ⟨k.1, hk1⟩ rfl j
    rw [hcoeff]
    exact le_trans (hfam f (⟨k.1, hk1⟩, j))
      (le_trans (mul_le_mul_of_nonneg_left (hsub s hsS f) hCfam0)
        (key Cfam hCfam0 hCfamK))

end

end Work.FunctionalEquations
