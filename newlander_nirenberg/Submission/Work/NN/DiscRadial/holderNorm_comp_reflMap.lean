import Mathlib
import Submission.Work.NN.DiscRadial.DiscRadialAux
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_div_norm
import Submission.Work.NN.DiscRadial.holderNorm_comp_univ_contDiffOn

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.DiscRadial

open Work.NN.Final Work.NN.Final.ChartComp

/-! ## Infrastructure -/

lemma natCast_le_top_nat (m : ℕ) : ((m : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

lemma isOpen_annR (b : ℝ) : IsOpen (annR b) := by
  have h1 : IsOpen {z : ℂ | (1:ℝ) < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {z : ℂ | ‖z‖ < 1 + 2/b} := isOpen_lt continuous_norm continuous_const
  exact h1.inter h2

lemma annR_ne_zero {b : ℝ} {z : ℂ} (hz : z ∈ annR b) : z ≠ 0 := by
  rintro rfl
  obtain ⟨h1, _⟩ := hz
  simp only [norm_zero] at h1
  linarith

/-! ## Iterated derivatives of a continuous linear map are constant -/

section ClmConst

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedFDeriv_clm_sub_eq_zero (L : E →L[ℝ] F) {n : ℕ} (hn : 1 ≤ n) (x y : E) :
    iteratedFDeriv ℝ n (fun z => L z) x - iteratedFDeriv ℝ n (fun z => L z) y = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : (fun z : E => fderiv ℝ (fun w => L w) z) = fun _ => L := by
    funext z
    rw [ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_succ_eq_comp_right (f := fun z : E => L z) (x := x) (n := m),
    iteratedFDeriv_succ_eq_comp_right (f := fun z : E => L z) (x := y) (n := m), hf]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [iteratedFDeriv_zero_eq_comp]
  · rw [iteratedFDeriv_const_of_ne (by omega : m ≠ 0) L]
    simp

lemma norm_iteratedFDeriv_clm_le (L : E →L[ℝ] F) (m : ℕ) (hm : 1 ≤ m) (z : E) :
    ‖iteratedFDeriv ℝ m (fun z => L z) z‖ ≤ ‖L‖ := by
  have hf : fderiv ℝ (fun z => L z) = fun _ => L := by
    ext1 v; simp only [ContinuousLinearMap.fderiv]
  rcases m with _ | _ | k
  · exact absurd hm (by omega)
  · rw [← norm_iteratedFDeriv_fderiv (f := fun z => L z) (x := z) (n := 0), hf,
      norm_iteratedFDeriv_zero]
  · rw [← norm_iteratedFDeriv_fderiv (f := fun z => L z) (x := z) (n := k + 1), hf,
      iteratedFDeriv_const_of_ne (by omega) L]
    simp

end ClmConst

/-! ## Norm bounds for pairings of multilinear maps -/

section ProdLemmas

variable {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℝ (M i)] {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_prod_le_max (A : ContinuousMultilinearMap ℝ M F)
    (B : ContinuousMultilinearMap ℝ M G) : ‖A.prod B‖ ≤ max ‖A‖ ‖B‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A.prod B)
    (M := max ‖A‖ ‖B‖) (le_max_of_le_left (norm_nonneg A)) fun v => ?_
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖A v‖ ≤ ‖A‖ * ∏ i, ‖v i‖ := A.le_opNorm v
      _ ≤ max ‖A‖ ‖B‖ * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  · calc ‖B v‖ ≤ ‖B‖ * ∏ i, ‖v i‖ := B.le_opNorm v
      _ ≤ max ‖A‖ ‖B‖ * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

lemma norm_prod_sub_prod_le (A A' : ContinuousMultilinearMap ℝ M F)
    (B B' : ContinuousMultilinearMap ℝ M G) :
    ‖A.prod B - A'.prod B'‖ ≤ max ‖A - A'‖ ‖B - B'‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A.prod B - A'.prod B')
    (M := max ‖A - A'‖ ‖B - B'‖) (le_max_of_le_left (norm_nonneg _)) fun v => ?_
  have h1 : ‖(A - A') v‖ ≤ ‖A - A'‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ v
  have h2 : ‖(B - B') v‖ ≤ ‖B - B'‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ v
  have h3 : (0:ℝ) ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.prod_apply,
    ContinuousMultilinearMap.prod_apply, Prod.mk_sub_mk, Prod.norm_def]
  rw [max_mul_of_nonneg _ _ h3]
  exact max_le_max h1 h2

end ProdLemmas

/-! ## The chain rule for the `snd`-composite -/

section SndComp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*} [Fintype ι]
  {M₁ : ι → Type*} [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace ℝ (M₁ i)]

lemma comp_clm_sub (g g' : ContinuousMultilinearMap ℝ M₁ G) (f : ∀ i, E →L[ℝ] M₁ i) :
    g.compContinuousLinearMap f - g'.compContinuousLinearMap f
      = (g - g').compContinuousLinearMap f := by
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

end SndComp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma iteratedFDeriv_comp_snd {φ : ℂ → ℂ} (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ {z : ℂ | z ≠ 0})
    (p : X × ℂ) (hp : p.2 ≠ 0) (k : ℕ) :
    iteratedFDeriv ℝ k (fun q : X × ℂ => φ q.2) p
      = (iteratedFDeriv ℝ k φ p.2).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.snd ℝ X ℂ) := by
  have hfun : (fun q : X × ℂ => φ q.2) = φ ∘ ⇑(ContinuousLinearMap.snd ℝ X ℂ) := rfl
  rw [hfun]
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hpre : (ContinuousLinearMap.snd ℝ X ℂ) ⁻¹' ({0}ᶜ : Set ℂ) = {q : X × ℂ | q.2 ≠ 0} := rfl
  have hU : IsOpen ((ContinuousLinearMap.snd ℝ X ℂ) ⁻¹' ({0}ᶜ : Set ℂ)) :=
    hs.preimage (ContinuousLinearMap.snd ℝ X ℂ).continuous
  have hmem : (ContinuousLinearMap.snd ℝ X ℂ) p ∈ ({0}ᶜ : Set ℂ) := by
    rw [show (ContinuousLinearMap.snd ℝ X ℂ) p = p.2 from rfl]; exact hp
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := ContinuousLinearMap.snd ℝ X ℂ) (f := φ) (s := ({0}ᶜ : Set ℂ))
    (show ContDiffOn ℝ (⊤ : ℕ∞) φ ({0}ᶜ : Set ℂ) from hφ)
    hs.uniqueDiffOn (by rw [hpre]; exact hU.uniqueDiffOn) (x := (p : X × ℂ)) hmem
    (i := k) (natCast_le_top_nat k)
  have hp' : p ∈ (ContinuousLinearMap.snd ℝ X ℂ) ⁻¹' ({0}ᶜ : Set ℂ) := by
    rw [hpre]; exact hp
  rw [show iteratedFDerivWithin ℝ k (φ ∘ ⇑(ContinuousLinearMap.snd ℝ X ℂ))
        ((ContinuousLinearMap.snd ℝ X ℂ) ⁻¹' ({0}ᶜ : Set ℂ)) p
      = iteratedFDeriv ℝ k (φ ∘ ⇑(ContinuousLinearMap.snd ℝ X ℂ)) p from
        (iteratedFDerivWithin_of_isOpen k hU) hp'] at key
  rw [show iteratedFDerivWithin ℝ k φ ({0}ᶜ : Set ℂ) ((ContinuousLinearMap.snd ℝ X ℂ) p)
      = iteratedFDeriv ℝ k φ p.2 from by
        rw [show (ContinuousLinearMap.snd ℝ X ℂ) p = p.2 from rfl]
        exact (iteratedFDerivWithin_of_isOpen k hs) hp] at key
  exact key

lemma norm_iteratedFDeriv_comp_snd_le {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ {z : ℂ | z ≠ 0})
    (p : X × ℂ) (hp : p.2 ≠ 0) {k : ℕ} :
    ‖iteratedFDeriv ℝ k (fun q : X × ℂ => φ q.2) p‖ ≤ ‖iteratedFDeriv ℝ k φ p.2‖ := by
  rw [iteratedFDeriv_comp_snd hφ p hp k]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_fin]
  have h1 : ‖ContinuousLinearMap.snd ℝ X ℂ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ X ℂ
  have h2 : ‖ContinuousLinearMap.snd ℝ X ℂ‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
  exact mul_le_of_le_one_right (norm_nonneg _) h2

lemma norm_iteratedFDeriv_comp_snd_sub {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ {z : ℂ | z ≠ 0})
    (p q : X × ℂ) (hp : p.2 ≠ 0) (hq : q.2 ≠ 0) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun r : X × ℂ => φ r.2) p
      - iteratedFDeriv ℝ k (fun r : X × ℂ => φ r.2) q‖
      ≤ ‖iteratedFDeriv ℝ k φ p.2 - iteratedFDeriv ℝ k φ q.2‖ := by
  rw [iteratedFDeriv_comp_snd hφ p hp k, iteratedFDeriv_comp_snd hφ q hq k, comp_clm_sub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_fin]
  have h1 : ‖ContinuousLinearMap.snd ℝ X ℂ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ X ℂ
  have h2 : ‖ContinuousLinearMap.snd ℝ X ℂ‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
  exact mul_le_of_le_one_right (norm_nonneg _) h2

lemma norm_iteratedFDeriv_fst_le {k : ℕ} (hk : 1 ≤ k) (p : X × ℂ) :
    ‖iteratedFDeriv ℝ k (fun q : X × ℂ => q.1) p‖ ≤ 1 := by
  have h := norm_iteratedFDeriv_clm_le (ContinuousLinearMap.fst ℝ X ℂ) k hk p
  exact h.trans (ContinuousLinearMap.norm_fst_le ℝ X ℂ)

/-! ## `discRefl` written in terms of the direction map -/

lemma discRefl_eq_formula (b : ℝ) (z : ℂ) :
    discRefl b z = (((1 + b : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ)) - ((b : ℝ) : ℂ) * z) := by
  rw [discRefl, Complex.real_smul]
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    push_cast
    field_simp
    ring

lemma contDiffAt_div_norm (w : ℂ) (hw : w ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) w := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => ‖u‖) w :=
    (contDiffAt_norm ℝ (x := w) hw).of_le le_top
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => ((‖u‖ : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w h1
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => (((‖u‖ : ℝ) : ℂ))⁻¹) w :=
    h2.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => u * (((‖u‖ : ℝ) : ℂ))⁻¹) w :=
    contDiffAt_id.mul h3
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards with u
  rw [div_eq_mul_inv]

/-- Derivative bounds for `discRefl` on the region `‖z‖ ≥ 1/2`. -/
lemma discRefl_deriv_bound {b : ℝ} (hb : 0 ≤ b) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧ ∀ k : ℕ, 1 ≤ k → ∀ z : ℂ, 1/2 ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ k (discRefl b) z‖ ≤ D k := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_iteratedFDeriv_div_norm
  refine ⟨fun k => (1 + b) * (C k * 2 ^ k) + b, ?_, fun k hk z hz => ?_⟩
  · intro k
    have h1 : 0 ≤ C k * 2 ^ k := mul_nonneg (le_of_lt (hC0 k)) (by positivity)
    have h2 : 0 ≤ (1 + b) * (C k * 2 ^ k) := mul_nonneg (by linarith) h1
    linarith
  · have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp only [norm_zero] at hz; linarith
    have hnorm1 : (1:ℝ) / ‖z‖ ≤ 2 := by
      rw [div_le_iff₀ (norm_pos_iff.mpr hz0)]; linarith
    set c1 : ℂ := ((1 + b : ℝ) : ℂ) with hc1
    set c2 : ℂ := ((b : ℝ) : ℂ) with hc2
    have hnormc1 : ‖c1‖ = 1 + b := by
      rw [hc1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hnormc2 : ‖c2‖ = b := by
      rw [hc2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    have hFcd : ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) z :=
      (contDiffAt_div_norm z hz0).of_le (natCast_le_top_nat k)
    have h1cd : ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun u : ℂ => c1 * (u / ((‖u‖ : ℝ) : ℂ))) z :=
      (contDiffAt_const (c := c1)).mul hFcd
    have h2cd : ContDiffAt ℝ (k : WithTop ℕ∞) (fun u : ℂ => c2 * u) z :=
      (contDiffAt_const (c := c2)).mul contDiffAt_id
    have hsub : discRefl b
        = (fun u : ℂ => c1 * (u / ((‖u‖ : ℝ) : ℂ))) - (fun u : ℂ => c2 * u) := by
      funext u
      rw [Pi.sub_apply, hc1, hc2]
      exact discRefl_eq_formula b u
    rw [hsub, iteratedFDeriv_sub_apply h1cd h2cd]
    have h1v : iteratedFDeriv ℝ k (fun u : ℂ => c1 * (u / ((‖u‖ : ℝ) : ℂ))) z
        = c1 • iteratedFDeriv ℝ k (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) z := by
      have heq : (fun u : ℂ => c1 * (u / ((‖u‖ : ℝ) : ℂ)))
          = c1 • (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) := by
        funext u; rw [Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact iteratedFDeriv_const_smul_apply' (a := c1) hFcd
    have h2v : iteratedFDeriv ℝ k (fun u : ℂ => c2 * u) z
        = c2 • iteratedFDeriv ℝ k (fun u : ℂ => u) z := by
      have heq : (fun u : ℂ => c2 * u) = c2 • (fun u : ℂ => u) := by
        funext u; rw [Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact iteratedFDeriv_const_smul_apply' (a := c2) contDiffAt_id
    rw [h1v, h2v]
    have hidb : ‖iteratedFDeriv ℝ k (fun u : ℂ => u) z‖ ≤ 1 := by
      have h := norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℂ) k hk z
      simpa using h
    have hFb : ‖iteratedFDeriv ℝ k (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) z‖
        ≤ C k * 2 ^ k := by
      refine (hC k z hz0).trans ?_
      have h2 : (1 / ‖z‖) ^ k ≤ (2:ℝ) ^ k := pow_le_pow_left₀ (by positivity) hnorm1 k
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt (hC0 k))
    have hA : ‖c1 • iteratedFDeriv ℝ k (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) z
          - c2 • iteratedFDeriv ℝ k (fun u : ℂ => u) z‖
        ≤ (1 + b) * (C k * 2 ^ k) + b := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, hnormc1, hnormc2]
      have h1 : (1 + b) * ‖iteratedFDeriv ℝ k (fun u : ℂ => u / ((‖u‖ : ℝ) : ℂ)) z‖
          ≤ (1 + b) * (C k * 2 ^ k) := mul_le_mul_of_nonneg_left hFb (by linarith)
      have h2 : b * ‖iteratedFDeriv ℝ k (fun u : ℂ => u) z‖ ≤ b * 1 :=
        mul_le_mul_of_nonneg_left hidb hb
      linarith
    exact hA

/-- Hölder bounds for the iterated derivatives of `discRefl` on the annulus `annR b`. -/
lemma discRefl_holder_bound {b : ℝ} {D : ℕ → ℝ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hDnn : ∀ k, 0 ≤ D k)
    (hD : ∀ k : ℕ, 1 ≤ k → ∀ z : ℂ, 1/2 ≤ ‖z‖ → ‖iteratedFDeriv ℝ k (discRefl b) z‖ ≤ D k) :
    ∃ E : ℕ → ℝ, ∀ k : ℕ, 1 ≤ k → ∀ z w : ℂ, z ∈ annR b → w ∈ annR b →
      ‖iteratedFDeriv ℝ k (discRefl b) z - iteratedFDeriv ℝ k (discRefl b) w‖
        ≤ E k * ‖z - w‖ ^ α := by
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (discRefl b) {z : ℂ | z ≠ 0} :=
    (contDiffOn_discRefl b).of_le le_top
  have hsne : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (x := (0:ℂ))
  refine ⟨fun k => max (D (k+1)) (2 * D k * 2 ^ α), fun k hk z w hz hw => ?_⟩
  have hz12 : (1/2 : ℝ) ≤ ‖z‖ := le_of_lt (by linarith [hz.1] : (1:ℝ)/2 < ‖z‖)
  have hw12 : (1/2 : ℝ) ≤ ‖w‖ := le_of_lt (by linarith [hw.1] : (1:ℝ)/2 < ‖w‖)
  have hEk2 : (0:ℝ) ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  by_cases hnear : ‖z - w‖ ≤ (1/2 : ℝ)
  · -- near: mean value inequality on a small ball around the midpoint
    set mid : ℂ := (z + w) / 2 with hmid
    have hzm : z - mid = ((1:ℂ)/2) * (z - w) := by rw [hmid]; ring
    have hwm : w - mid = ((1:ℂ)/2) * (w - z) := by rw [hmid]; ring
    have hnormhalf : ‖((1:ℂ)/2)‖ = (1/2 : ℝ) := by norm_num
    have hzmem : z ∈ closedBall mid (1/4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, hzm, norm_mul, hnormhalf]
      linarith
    have hwmem : w ∈ closedBall mid (1/4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, hwm, norm_mul, hnormhalf, norm_sub_rev]
      linarith
    have hball_norm : ∀ u ∈ closedBall mid (1/4 : ℝ), (1/2 : ℝ) ≤ ‖u‖ := by
      intro u hu
      have hu1 : ‖u - mid‖ ≤ 1/4 := by
        rw [mem_closedBall, dist_eq_norm] at hu; exact hu
      have hu2 : ‖z - u‖ ≤ (1/2 : ℝ) := by
        have hsplit : z - u = (z - mid) + (mid - u) := by ring
        rw [hsplit]
        have h1 : ‖z - mid‖ ≤ 1/4 := by
          rw [hzm, norm_mul, hnormhalf]; linarith
        have h2 : ‖mid - u‖ ≤ 1/4 := by rw [norm_sub_rev]; exact hu1
        linarith [norm_add_le (z - mid) (mid - u)]
      have h3 : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
        calc ‖z‖ = ‖(z - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
      linarith [hz.1, hu2]
    have hcd : ∀ u ∈ closedBall mid (1/4 : ℝ), ContDiffAt ℝ (⊤ : ℕ∞) (discRefl b) u := by
      intro u hu
      have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hu
        have hb := hball_norm 0 hu
        simp only [norm_zero] at hb
        linarith
      exact hφ.contDiffAt (hsne.mem_nhds hu0)
    have hdiff : ∀ u ∈ closedBall mid (1/4 : ℝ),
        DifferentiableAt ℝ (fun v : ℂ => iteratedFDeriv ℝ k (discRefl b) v) u := by
      intro u hu
      have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞)
          (fun v : ℂ => iteratedFDeriv ℝ k (discRefl b) v) u :=
        (hcd u hu).iteratedFDeriv_right (i := k) (by norm_num)
      exact h1.differentiableAt (by norm_num)
    have hbd : ∀ u ∈ closedBall mid (1/4 : ℝ),
        ‖fderiv ℝ (fun v : ℂ => iteratedFDeriv ℝ k (discRefl b) v) u‖ ≤ D (k+1) := by
      intro u hu
      rw [norm_fderiv_iteratedFDeriv]
      exact hD (k+1) (by omega) u (hball_norm u hu)
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (s := closedBall mid (1/4 : ℝ))
      (f := fun v : ℂ => iteratedFDeriv ℝ k (discRefl b) v) (C := D (k+1))
      hdiff hbd (convex_closedBall mid (1/4)) hzmem hwmem
    have hle : ‖z - w‖ ≤ ‖z - w‖ ^ α := by
      rcases eq_or_ne z w with h | h
      · subst h
        rw [sub_self, norm_zero, Real.zero_rpow hα.ne']
      · have hpos : (0:ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
        have h1 : ‖z - w‖ ^ α * ‖z - w‖ ^ (1 - α) = ‖z - w‖ := by
          rw [← Real.rpow_add hpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
        have h2 : ‖z - w‖ ^ (1 - α) ≤ 1 :=
          Real.rpow_le_one (norm_nonneg _) (by linarith) (sub_nonneg.mpr hα1)
        calc ‖z - w‖ = ‖z - w‖ ^ α * ‖z - w‖ ^ (1 - α) := h1.symm
          _ ≤ ‖z - w‖ ^ α * 1 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) α)
          _ = ‖z - w‖ ^ α := mul_one _
    calc ‖iteratedFDeriv ℝ k (discRefl b) z - iteratedFDeriv ℝ k (discRefl b) w‖
        = ‖iteratedFDeriv ℝ k (discRefl b) w - iteratedFDeriv ℝ k (discRefl b) z‖ :=
          norm_sub_rev _ _
      _ ≤ D (k+1) * ‖w - z‖ := hmvt
      _ = D (k+1) * ‖z - w‖ := by rw [norm_sub_rev]
      _ ≤ D (k+1) * ‖z - w‖ ^ α := mul_le_mul_of_nonneg_left hle (hDnn (k+1))
      _ ≤ max (D (k+1)) (2 * D k * 2 ^ α) * ‖z - w‖ ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hEk2
  · -- far: boundedness of the derivatives on the annulus
    have hfar : (1/2 : ℝ) < ‖z - w‖ := not_le.mp hnear
    have hone : (1:ℝ) ≤ 2 ^ α * ‖z - w‖ ^ α := by
      have h2 : (1/2 : ℝ) ^ α ≤ ‖z - w‖ ^ α :=
        Real.rpow_le_rpow (by norm_num) (le_of_lt hfar) hα.le
      have h3 : (2:ℝ) ^ α * (1/2 : ℝ) ^ α = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num : (0:ℝ) ≤ 1/2)]
        norm_num
      nlinarith [h2, h3, Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) α]
    have h1 : ‖iteratedFDeriv ℝ k (discRefl b) z - iteratedFDeriv ℝ k (discRefl b) w‖
        ≤ 2 * D k := by
      have h2 := hD k hk z hz12
      have h3 := hD k hk w hw12
      linarith [norm_sub_le (iteratedFDeriv ℝ k (discRefl b) z)
        (iteratedFDeriv ℝ k (discRefl b) w)]
    calc ‖iteratedFDeriv ℝ k (discRefl b) z - iteratedFDeriv ℝ k (discRefl b) w‖
        ≤ 2 * D k := h1
      _ = 2 * D k * 1 := by ring
      _ ≤ 2 * D k * (2 ^ α * ‖z - w‖ ^ α) := by
          refine mul_le_mul_of_nonneg_left hone ?_
          linarith [hDnn k]
      _ = (2 * D k * 2 ^ α) * ‖z - w‖ ^ α := by ring
      _ ≤ max (D (k+1)) (2 * D k * 2 ^ α) * ‖z - w‖ ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hEk2

/-- Lipschitz bound for `discRefl` on the annulus, from a bound on its first derivative. -/
lemma discRefl_lipschitz {b : ℝ} (hb : 2 ≤ b) {D : ℕ → ℝ}
    (hD : ∀ k : ℕ, 1 ≤ k → ∀ z : ℂ, 1/2 ≤ ‖z‖ → ‖iteratedFDeriv ℝ k (discRefl b) z‖ ≤ D k) :
    ∃ Lφ : ℝ, ∀ z w : ℂ, z ∈ annR b → w ∈ annR b →
      ‖discRefl b z - discRefl b w‖ ≤ Lφ * ‖z - w‖ := by
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (discRefl b) {z : ℂ | z ≠ 0} :=
    (contDiffOn_discRefl b).of_le le_top
  have hsne : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (x := (0:ℂ))
  refine ⟨max (D 1) 4, fun z w hz hw => ?_⟩
  have hnormb : ∀ v : ℂ, v ∈ annR b → ‖discRefl b v‖ < 1 := by
    intro v hv
    obtain ⟨h1, h2⟩ := hv
    have hv0 : v ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
    rw [norm_discRefl b hv0]
    have hb' : 0 < b := by linarith
    have hδ : 0 < ‖v‖ - 1 := by linarith
    have hbδ : 0 < b * (‖v‖ - 1) := mul_pos hb' hδ
    have hlt : b * (‖v‖ - 1) < 2 := by
      have hb2 : b * (1 + 2 / b) = b + 2 := by field_simp
      nlinarith [h2, hb', hb2]
    rw [abs_lt]
    constructor <;> linarith
  by_cases hnear : ‖z - w‖ ≤ (1/2 : ℝ)
  · set mid : ℂ := (z + w) / 2 with hmid
    have hzm : z - mid = ((1:ℂ)/2) * (z - w) := by rw [hmid]; ring
    have hwm : w - mid = ((1:ℂ)/2) * (w - z) := by rw [hmid]; ring
    have hnormhalf : ‖((1:ℂ)/2)‖ = (1/2 : ℝ) := by norm_num
    have hzmem : z ∈ closedBall mid (1/4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, hzm, norm_mul, hnormhalf]
      linarith
    have hwmem : w ∈ closedBall mid (1/4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, hwm, norm_mul, hnormhalf, norm_sub_rev]
      linarith
    have hball_norm : ∀ u ∈ closedBall mid (1/4 : ℝ), (1/2 : ℝ) ≤ ‖u‖ := by
      intro u hu
      have hu1 : ‖u - mid‖ ≤ 1/4 := by
        rw [mem_closedBall, dist_eq_norm] at hu; exact hu
      have hu2 : ‖z - u‖ ≤ (1/2 : ℝ) := by
        have hsplit : z - u = (z - mid) + (mid - u) := by ring
        rw [hsplit]
        have h1 : ‖z - mid‖ ≤ 1/4 := by
          rw [hzm, norm_mul, hnormhalf]; linarith
        have h2 : ‖mid - u‖ ≤ 1/4 := by rw [norm_sub_rev]; exact hu1
        linarith [norm_add_le (z - mid) (mid - u)]
      have h3 : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
        calc ‖z‖ = ‖(z - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
      linarith [hz.1, hu2]
    have hdiff : ∀ u ∈ closedBall mid (1/4 : ℝ), DifferentiableAt ℝ (discRefl b) u := by
      intro u hu
      have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hu
        have hb' := hball_norm 0 hu
        simp only [norm_zero] at hb'
        linarith
      have hcd : ContDiffAt ℝ (1 : WithTop ℕ∞) (discRefl b) u :=
        (hφ.contDiffAt (hsne.mem_nhds hu0)).of_le (natCast_le_top_nat 1)
      exact hcd.differentiableAt (by norm_num)
    have hbd : ∀ u ∈ closedBall mid (1/4 : ℝ), ‖fderiv ℝ (discRefl b) u‖ ≤ D 1 := by
      intro u hu
      rw [← norm_iteratedFDeriv_one]
      exact hD 1 le_rfl u (hball_norm u hu)
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (s := closedBall mid (1/4 : ℝ))
      (f := discRefl b) (C := D 1) hdiff hbd (convex_closedBall mid (1/4)) hzmem hwmem
    calc ‖discRefl b z - discRefl b w‖ = ‖discRefl b w - discRefl b z‖ := norm_sub_rev _ _
      _ ≤ D 1 * ‖w - z‖ := hmvt
      _ = D 1 * ‖z - w‖ := by rw [norm_sub_rev]
      _ ≤ max (D 1) 4 * ‖z - w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have hzw : (1/2 : ℝ) < ‖z - w‖ := not_le.mp hnear
    have h1 : ‖discRefl b z‖ ≤ 1 := le_of_lt (hnormb z hz)
    have h2 : ‖discRefl b w‖ ≤ 1 := le_of_lt (hnormb w hw)
    calc ‖discRefl b z - discRefl b w‖ ≤ ‖discRefl b z‖ + ‖discRefl b w‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * (2 * ‖z - w‖) := by linarith
      _ = 4 * ‖z - w‖ := by ring
      _ ≤ max (D 1) 4 * ‖z - w‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- **Data for the composition estimate with `reflMap`.**  From Lipschitz, derivative and
Hölder bounds for `discRefl` on the annulus `annR b`, we obtain the corresponding data for the
map `reflMap b` on the sets `U ×ˢ annR b` (uniformly in the open set `U`). -/
lemma reflMap_holder_data_of_discRefl {α : ℝ} (hα : 0 ≤ α) {b : ℝ} {Lφ : ℝ} {Dφ Eφ : ℕ → ℝ}
    (hLφ : ∀ z w : ℂ, z ∈ annR b → w ∈ annR b →
      ‖discRefl b z - discRefl b w‖ ≤ Lφ * ‖z - w‖)
    (hDφ : ∀ k : ℕ, 1 ≤ k → ∀ z : ℂ, z ∈ annR b → ‖iteratedFDeriv ℝ k (discRefl b) z‖ ≤ Dφ k)
    (hEφ : ∀ k : ℕ, 1 ≤ k → ∀ z w : ℂ, z ∈ annR b → w ∈ annR b →
      ‖iteratedFDeriv ℝ k (discRefl b) z - iteratedFDeriv ℝ k (discRefl b) w‖
        ≤ Eφ k * ‖z - w‖ ^ α) :
    (∃ L : ℝ, ∀ (U : Set X), IsOpen U → ∀ p ∈ U ×ˢ annR b, ∀ q ∈ U ×ˢ annR b,
        ‖reflMap b p - reflMap b q‖ ≤ L * ‖p - q‖) ∧
    (∃ D : ℕ → ℝ, ∀ (U : Set X), IsOpen U → ∀ (k : ℕ), 1 ≤ k → ∀ p ∈ U ×ˢ annR b,
        ‖iteratedFDerivWithin ℝ k (reflMap b) (U ×ˢ annR b) p‖ ≤ D k) ∧
    (∃ E : ℕ → ℝ, ∀ (U : Set X), IsOpen U → ∀ (k : ℕ), 1 ≤ k → ∀ p ∈ U ×ˢ annR b,
        ∀ q ∈ U ×ˢ annR b,
        ‖iteratedFDerivWithin ℝ k (reflMap b) (U ×ˢ annR b) p
          - iteratedFDerivWithin ℝ k (reflMap b) (U ×ˢ annR b) q‖
          ≤ E k * ‖p - q‖ ^ α) ∧
    (∀ (U : Set X), IsOpen U → ∀ m : ℕ,
        ContDiffOn ℝ (m : WithTop ENat) (reflMap b) (U ×ˢ annR b)) := by
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (discRefl b) {z : ℂ | z ≠ 0} :=
    (contDiffOn_discRefl b).of_le le_top
  have hsne : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (x := (0:ℂ))
  have hsm : ∀ (U : Set X), IsOpen U → ∀ m : ℕ,
      ContDiffOn ℝ (m : WithTop ENat) (reflMap b) (U ×ˢ annR b) := by
    intro U hU m p hp
    rw [Set.mem_prod] at hp
    have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun q : X × ℂ => q.1) p :=
      (ContinuousLinearMap.fst ℝ X ℂ).contDiff.contDiffAt
    have h2 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun q : X × ℂ => discRefl b q.2) p :=
      ((hφ.of_le (natCast_le_top_nat m)).contDiffAt
        (hsne.mem_nhds (annR_ne_zero hp.2))).comp p
        ((ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffAt)
    exact (h1.prodMk h2).contDiffWithinAt
  refine ⟨?_, ?_, ?_, hsm⟩
  · refine ⟨max 1 Lφ, ?_⟩
    intro U hU p hp q hq
    rw [Set.mem_prod] at hp hq
    have h1 : ‖reflMap b p - reflMap b q‖
        = max ‖p.1 - q.1‖ ‖discRefl b p.2 - discRefl b q.2‖ := by
      rw [show reflMap b p - reflMap b q
          = (p.1 - q.1, discRefl b p.2 - discRefl b q.2) from rfl, Prod.norm_def]
    have h2 : ‖p - q‖ = max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by
      rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.mk_sub_mk p.1 q.1 p.2 q.2, Prod.norm_def]
    rw [h1, h2]
    have hmax1 : (0:ℝ) ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    have hLmax : (1:ℝ) ≤ max 1 Lφ := le_max_left _ _
    have hLmax0 : (0:ℝ) ≤ max 1 Lφ := le_trans zero_le_one hLmax
    refine max_le ?_ ?_
    · calc ‖p.1 - q.1‖ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_left _ _
        _ ≤ max 1 Lφ * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ :=
            le_mul_of_one_le_left hmax1 hLmax
    · rcases lt_or_ge (0:ℝ) Lφ with hpos | hneg
      · calc ‖discRefl b p.2 - discRefl b q.2‖ ≤ Lφ * ‖p.2 - q.2‖ := hLφ p.2 q.2 hp.2 hq.2
          _ ≤ max 1 Lφ * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ :=
              mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) hLmax0
      · have h0 : ‖discRefl b p.2 - discRefl b q.2‖ ≤ 0 := by
          refine (hLφ p.2 q.2 hp.2 hq.2).trans ?_
          exact mul_nonpos_of_nonpos_of_nonneg hneg (norm_nonneg _)
        exact h0.trans (mul_nonneg hLmax0 hmax1)
  · refine ⟨fun k => 1 + max (Dφ k) 0, ?_⟩
    intro U hU k hk p hp
    rw [Set.mem_prod] at hp
    have hs : IsOpen (U ×ˢ annR b) := hU.prod (isOpen_annR b)
    have hpne : p.2 ≠ 0 := annR_ne_zero hp.2
    have hpφ : ContDiffAt ℝ (k : WithTop ℕ∞) (fun q : X × ℂ => discRefl b q.2) p :=
      ((hφ.contDiffAt (hsne.mem_nhds hpne)).of_le (natCast_le_top_nat k)).comp p
        ((ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffAt)
    have hpf : ContDiffAt ℝ (k : WithTop ℕ∞) (fun q : X × ℂ => q.1) p :=
      (ContinuousLinearMap.fst ℝ X ℂ).contDiff.contDiffAt
    have hpair : iteratedFDeriv ℝ k (reflMap b) p
        = (iteratedFDeriv ℝ k (fun q : X × ℂ => q.1) p).prod
          (iteratedFDeriv ℝ k (fun q : X × ℂ => discRefl b q.2) p) := by
      have h3 := iteratedFDeriv_prodMk (x := p) (f := fun q : X × ℂ => q.1)
        (g := fun q : X × ℂ => discRefl b q.2) hpf hpφ (i := k) le_rfl
      exact h3
    rw [iteratedFDerivWithin_of_isOpen k hs hp, hpair]
    refine (norm_prod_le_max _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine (norm_iteratedFDeriv_fst_le hk p).trans ?_
      exact le_add_of_nonneg_right (le_max_right _ _)
    · refine ((norm_iteratedFDeriv_comp_snd_le hφ p hpne).trans (hDφ k hk p.2 hp.2)).trans ?_
      have h := le_max_left (Dφ k) 0
      linarith
  · refine ⟨fun k => max (Eφ k) 0, ?_⟩
    intro U hU k hk p hp q hq
    rw [Set.mem_prod] at hp hq
    have hs : IsOpen (U ×ˢ annR b) := hU.prod (isOpen_annR b)
    have hpne : p.2 ≠ 0 := annR_ne_zero hp.2
    have hqne : q.2 ≠ 0 := annR_ne_zero hq.2
    have hA : iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) p
        = iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) q := by
      have h := iteratedFDeriv_clm_sub_eq_zero (ContinuousLinearMap.fst ℝ X ℂ) hk p q
      exact sub_eq_zero.mp h
    have hBb : ‖iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) p
        - iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) q‖
        ≤ ‖iteratedFDeriv ℝ k (discRefl b) p.2 - iteratedFDeriv ℝ k (discRefl b) q.2‖ :=
      norm_iteratedFDeriv_comp_snd_sub hφ p q hpne hqne k
    have hpφ : ContDiffAt ℝ (k : WithTop ℕ∞) (fun r : X × ℂ => discRefl b r.2) p :=
      ((hφ.contDiffAt (hsne.mem_nhds hpne)).of_le (natCast_le_top_nat k)).comp p
        ((ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffAt)
    have hqφ : ContDiffAt ℝ (k : WithTop ℕ∞) (fun r : X × ℂ => discRefl b r.2) q :=
      ((hφ.contDiffAt (hsne.mem_nhds hqne)).of_le (natCast_le_top_nat k)).comp q
        ((ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffAt)
    have hpf : ContDiffAt ℝ (k : WithTop ℕ∞) (fun r : X × ℂ => r.1) p :=
      (ContinuousLinearMap.fst ℝ X ℂ).contDiff.contDiffAt
    have hqf : ContDiffAt ℝ (k : WithTop ℕ∞) (fun r : X × ℂ => r.1) q :=
      (ContinuousLinearMap.fst ℝ X ℂ).contDiff.contDiffAt
    have hpairp : iteratedFDeriv ℝ k (reflMap b) p
        = (iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) p).prod
          (iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) p) := by
      have h3 := iteratedFDeriv_prodMk (x := p) (f := fun r : X × ℂ => r.1)
        (g := fun r : X × ℂ => discRefl b r.2) hpf hpφ (i := k) le_rfl
      exact h3
    have hpairq : iteratedFDeriv ℝ k (reflMap b) q
        = (iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) q).prod
          (iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) q) := by
      have h3 := iteratedFDeriv_prodMk (x := q) (f := fun r : X × ℂ => r.1)
        (g := fun r : X × ℂ => discRefl b r.2) hqf hqφ (i := k) le_rfl
      exact h3
    have hpq : ‖p.2 - q.2‖ ≤ ‖p - q‖ := by
      rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.mk_sub_mk p.1 q.1 p.2 q.2, Prod.norm_def]
      exact le_max_right _ _
    rw [iteratedFDerivWithin_of_isOpen k hs hp, iteratedFDerivWithin_of_isOpen k hs hq,
      hpairp, hpairq]
    calc ‖(iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) p).prod
            (iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) p)
          - (iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) q).prod
            (iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) q)‖
        ≤ max ‖iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) p
            - iteratedFDeriv ℝ k (fun r : X × ℂ => r.1) q‖
          ‖iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) p
            - iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) q‖ :=
          norm_prod_sub_prod_le _ _ _ _
      _ = ‖iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) p
            - iteratedFDeriv ℝ k (fun r : X × ℂ => discRefl b r.2) q‖ := by
          rw [hA, sub_self, norm_zero, max_eq_right (norm_nonneg _)]
      _ ≤ ‖iteratedFDeriv ℝ k (discRefl b) p.2 - iteratedFDeriv ℝ k (discRefl b) q.2‖ := hBb
      _ ≤ max (Eφ k) 0 * ‖p - q‖ ^ α := by
          by_cases hE0 : 0 ≤ Eφ k
          · refine (hEφ k hk p.2 q.2 hp.2 hq.2).trans ?_
            have h1 : ‖p.2 - q.2‖ ^ α ≤ ‖p - q‖ ^ α :=
              Real.rpow_le_rpow (norm_nonneg _) hpq hα
            have h2 : Eφ k ≤ max (Eφ k) 0 := le_max_left _ _
            have h3 : (0:ℝ) ≤ ‖p - q‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
            calc Eφ k * ‖p.2 - q.2‖ ^ α ≤ Eφ k * ‖p - q‖ ^ α :=
                  mul_le_mul_of_nonneg_left h1 hE0
              _ ≤ max (Eφ k) 0 * ‖p - q‖ ^ α := mul_le_mul_of_nonneg_right h2 h3
          · push_neg at hE0
            have h3 : Eφ k * ‖p.2 - q.2‖ ^ α ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_lt hE0) (Real.rpow_nonneg (norm_nonneg _) α)
            have h4 : max (Eφ k) 0 = 0 := max_eq_right (le_of_lt hE0)
            rw [h4]
            simp only [zero_mul]
            exact (hEφ k hk p.2 q.2 hp.2 hq.2).trans h3

/-- **Composition of the Hölder norm with the radial reflection.** -/
theorem holderNorm_comp_reflMap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (b : ℝ) (hb : 2 ≤ b) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X), IsOpen U → ∀ g : X × ℂ → ℂ,
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1)) →
        Work.CR.Flat.holderNorm k α (fun p => g (Work.NN.DiscRadial.reflMap b p))
            (U ×ˢ Work.NN.DiscRadial.annR b)
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) := by
  obtain ⟨D, hDnn, hD⟩ := discRefl_deriv_bound (b := b) (by linarith)
  obtain ⟨E, hE⟩ := discRefl_holder_bound (b := b) (D := D) hα hα1 hDnn hD
  obtain ⟨Lφ, hLφ⟩ := discRefl_lipschitz (b := b) hb hD
  have hDann : ∀ k : ℕ, 1 ≤ k → ∀ z : ℂ, z ∈ annR b →
      ‖iteratedFDeriv ℝ k (discRefl b) z‖ ≤ D k :=
    fun k hk z hz => hD k hk z (by have := hz.1; linarith)
  have hdata := reflMap_holder_data_of_discRefl (X := X) (α := α) (le_of_lt hα) (b := b)
    (Lφ := Lφ) (Dφ := D) (Eφ := E) hLφ hDann hE
  obtain ⟨L, hL⟩ := hdata.1
  obtain ⟨D', hD'⟩ := hdata.2.1
  obtain ⟨E', hE'⟩ := hdata.2.2.1
  have hsm := hdata.2.2.2
  obtain ⟨C, hCpos, hC⟩ := holderNorm_comp_univ_contDiffOn (X := X × ℂ) (Y := X × ℂ)
    (α := α) (hα := hα) (L := L) (D := D') (E := E')
  refine ⟨C, hCpos, ?_⟩
  intro k U hU g hg
  have hs : IsOpen (U ×ˢ annR b) := hU.prod (isOpen_annR b)
  have ht : IsOpen (U ×ˢ Metric.ball (0 : ℂ) 1) := hU.prod Metric.isOpen_ball
  have hst : Set.MapsTo (reflMap b) (U ×ˢ annR b) (U ×ˢ Metric.ball (0 : ℂ) 1) := by
    intro p hp
    rw [Set.mem_prod] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [reflMap, Metric.mem_ball, dist_zero_right]
    exact norm_reflMap_snd_lt_one (by linarith) hp.2
  exact hC k (reflMap b) (U ×ˢ annR b) (U ×ˢ Metric.ball (0 : ℂ) 1) g
    (fun m => hsm U hU m) hs ht hst (hL U hU) (hD' U hU) (hE' U hU) (hg k le_rfl)

end Work.NN.DiscRadial
