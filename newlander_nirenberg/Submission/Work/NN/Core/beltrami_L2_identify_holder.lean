/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Identifying the solution of the Beltrami equation with the fixed point of the potential equation

This is the lemma `Work.NN.Core.beltrami_L2_identify_holder`: for `δ` small enough, if
`W ∈ C¹_c` solves the small Beltrami equation `∂̄W = c ∂W + G` and `F ∈ C^{0,α}_c` solves the
potential equation `F = Γ⁻¹ c ∂(bmPotential F) + G`, then `∂̄W = F`.

The proof: put `V := ∂̄W` and `E := V - F`.  From the Bochner–Martinelli identity
`bmPotential (∂̄W) = Γ W` one gets `∂_j (bmPotential V) = Γ ∂_j W`, hence `V` satisfies the same
potential equation as `F`, and therefore `E = Γ⁻¹ c ∂ (bmPotential E)`.  The `L²` Calderón–Zygmund
bound for `∂bmPotential` (applied to `E`) and the pointwise Cauchy–Schwarz estimate give
`‖E‖² ≤ (n δ C / |Γ|)² ‖E‖²` in `L²`; for `δ` small this forces `E = 0` a.e., hence `E = 0`
everywhere by continuity.
-/
import Mathlib
import Submission.Work.NN.Core.czB_L2_bounded
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord
import Submission.Work.NN.Core.beltrami_theta_aux
import Submission.Work.NN.Core.bmDefect_gain_smooth
import Submission.Work.NN.Core.czB_L2_bounded_C0
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder

open scoped NNReal ENNReal Topology
open MeasureTheory Set

namespace Work.NN.Core

variable {n : ℕ}

variable {n : ℕ}

lemma hasCompactSupport_comp_add {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : HasCompactSupport f)
    (z : Fin n → ℂ) : HasCompactSupport (fun x => f (z + x)) :=
  hf.comp_homeomorph (Homeomorph.addLeft z)

lemma bmPot_sub {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hfs : ∀ j, HasCompactSupport (f j))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, HasCompactSupport (g j)) (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.bmPot (fun j w => f j w - g j w) z
      = Work.CR.Flat.Cauchy.bmPot f z - Work.CR.Flat.Cauchy.bmPot g z := by
  have key : ∀ k : Fin n,
      (∫ x, Work.CR.Flat.Cauchy.bmKernel k x * (f k (z + x) - g k (z + x)))
        = (∫ x, Work.CR.Flat.Cauchy.bmKernel k x * f k (z + x))
          - (∫ x, Work.CR.Flat.Cauchy.bmKernel k x * g k (z + x)) := by
    intro k
    rw [← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); ring
    · exact integrable_bmKernel_mul hn k ((hf k).comp (continuous_const.add continuous_id))
        (hasCompactSupport_comp_add (hfs k) z)
    · exact integrable_bmKernel_mul hn k ((hg k).comp (continuous_const.add continuous_id))
        (hasCompactSupport_comp_add (hgs k) z)
  simp only [Work.CR.Flat.Cauchy.bmPot]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_sub_distrib]

lemma bmPotential_sub {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hfs : ∀ j, HasCompactSupport (f j))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    Work.CR.Flat.Cauchy.bmPotential (fun j w => f j w - g j w)
      = fun z => Work.CR.Flat.Cauchy.bmPotential f z - Work.CR.Flat.Cauchy.bmPotential g z := by
  funext z
  rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot,
    Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  exact bmPot_sub hn hf hfs hg hgs z

lemma exists_radius_family {ι : Type*} [Fintype ι]
    {f : ι → (Fin n → ℂ) → ℂ} (hf : ∀ i, HasCompactSupport (f i)) :
    ∃ R : ℝ, 0 < R ∧ ∀ i z, R ≤ ‖z‖ → f i z = 0 := by
  classical
  have h : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → f i z = 0 := fun i => by
    obtain ⟨r, hrpos, hr⟩ := (hf i).exists_pos_le_norm
    exact ⟨r, hrpos, fun z hz => hr z hz⟩
  choose R hRpos hR using h
  refine ⟨(∑ i, (R i + 1)) + 1, by
    have : 0 ≤ ∑ i, (R i + 1) := Finset.sum_nonneg (fun i _ => by linarith [hRpos i])
    linarith, fun i z hz => ?_⟩
  refine hR i z (le_trans ?_ hz)
  calc R i ≤ R i + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ ∑ j, (R j + 1) :=
        Finset.single_le_sum (f := fun j => R j + 1) (fun j _ => by linarith [hRpos j])
          (Finset.mem_univ i)
    _ ≤ (∑ j, (R j + 1)) + 1 := le_add_of_nonneg_right zero_le_one

lemma norm_sq_sum_le {n : ℕ} {Γ : ℂ} (hΓ : Γ ≠ 0) {δ : ℝ}
    {c : Fin n → Fin n → ℂ} (hc : ∀ j l, ‖c j l‖ ≤ δ) {d : Fin n → ℂ} :
    ∑ j : Fin n, ‖Γ⁻¹ * (∑ l, c j l * d l)‖ ^ 2
      ≤ (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ) ^ 2 * ∑ l, ‖d l‖ ^ 2 := by
  have hstep : ∀ j : Fin n,
      ‖Γ⁻¹ * (∑ l, c j l * d l)‖ ^ 2 ≤ (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ ^ 2) * ∑ l, ‖d l‖ ^ 2 := by
    intro j
    have hcs : ‖(∑ l, c j l * d l)‖ ^ 2 ≤ (∑ l, ‖c j l‖ ^ 2) * (∑ l, ‖d l‖ ^ 2) := by
      have h1 : ‖(∑ l, c j l * d l)‖ ≤ ∑ l, ‖c j l * d l‖ := norm_sum_le _ _
      have h2 : ‖(∑ l, c j l * d l)‖ ^ 2 ≤ (∑ l, ‖c j l * d l‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (∑ l, ‖c j l * d l‖) ^ 2 ≤ (∑ l, ‖c j l‖ ^ 2) * (∑ l, ‖d l‖ ^ 2) := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖c j l‖) (fun l => ‖d l‖)
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul] using h
      exact h2.trans h3
    have hc2 : (∑ l, ‖c j l‖ ^ 2) ≤ (n : ℝ) * δ ^ 2 := by
      calc (∑ l : Fin n, ‖c j l‖ ^ 2) ≤ ∑ _l : Fin n, δ ^ 2 :=
            Finset.sum_le_sum (fun l _ => pow_le_pow_left₀ (norm_nonneg _) (hc j l) 2)
        _ = (n : ℝ) * δ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖Γ⁻¹ * (∑ l, c j l * d l)‖ ^ 2
        = (‖Γ‖ ^ 2)⁻¹ * ‖(∑ l, c j l * d l)‖ ^ 2 := by
          rw [norm_mul, norm_inv, mul_pow, inv_pow]
      _ ≤ (‖Γ‖ ^ 2)⁻¹ * ((∑ l, ‖c j l‖ ^ 2) * (∑ l, ‖d l‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left hcs ?_
          positivity
      _ ≤ (‖Γ‖ ^ 2)⁻¹ * (((n : ℝ) * δ ^ 2) * (∑ l, ‖d l‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hc2
            (Finset.sum_nonneg (fun l _ => pow_nonneg (norm_nonneg _) 2))
      _ = (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ ^ 2) * ∑ l, ‖d l‖ ^ 2 := by ring
  calc ∑ j : Fin n, ‖Γ⁻¹ * (∑ l, c j l * d l)‖ ^ 2
      ≤ ∑ _j : Fin n, (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ ^ 2) * ∑ l, ‖d l‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => hstep j)
    _ = (n : ℝ) * ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ ^ 2) * ∑ l, ‖d l‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ) ^ 2 * ∑ l, ‖d l‖ ^ 2 := by ring


/-- The main step, given the two analytic inputs: the `L²` Calderón–Zygmund bound for the
Bochner–Martinelli transform of continuous compactly supported data (`czB_L2_bounded_continuous`)
and the `C¹`-regularity of the potential of `C^{0,α}` compactly supported data
(`contDiff_one_bmPotential_of_holder`). -/
theorem beltrami_L2_identify_holder_aux {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (L2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Continuous (ψ j)) → (∀ j, HasCompactSupport (ψ j)) →
      ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential ψ) →
      (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖ψ j z‖ ^ 2)
    (bmFC1 : ∀ (F : Fin n → (Fin n → ℂ) → ℂ), (∀ j, HasCompactSupport (F j)) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
      ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ)
        (W : (Fin n → ℂ) → ℂ) (F : Fin n → (Fin n → ℂ) → ℂ),
        (∀ k j, ContDiff ℝ ⊤ (c k j)) →
        (∀ k j, HasCompactSupport (c k j)) →
        (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ k, ContDiff ℝ 1 (G k)) →
        (∀ k, HasCompactSupport (G k)) →
        (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) →
        ContDiff ℝ 1 W → HasCompactSupport W →
        (∀ k z, Work.CR.Flat.dbarCoord k W z
            = (∑ j, c k j z * Work.CR.Flat.dCoord j W z) + G k z) →
        (∀ j, HasCompactSupport (F j)) →
        (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
        (∀ j z, F j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (∑ l,
            c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z) →
        ∀ j z, Work.CR.Flat.dbarCoord j W z = F j z := by
  obtain ⟨C, hC0, hL2⟩ := L2
  set Γ : ℂ := Work.CR.Flat.Cauchy.bmGamma n with hΓdef
  have hΓne : Γ ≠ 0 := by
    rw [hΓdef]
    exact Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  set δ0 : ℝ := min 1 (‖Γ‖ / (2 * ((n : ℝ) * C + 1))) with hδ0def
  have hδ0pos : 0 < δ0 := lt_min one_pos (by positivity)
  refine ⟨δ0, hδ0pos, ?_⟩
  intro c G W F hc_sm hc_cs hc_supp hc_small hG_sm hG_cs hG_fin hW_sm hW_cs hW_eq hF_cs hF_fin hF_eq
  have hδ0Γ : δ0 * (2 * ((n : ℝ) * C + 1)) ≤ ‖Γ‖ := by
    have h := min_le_right (1 : ℝ) (‖Γ‖ / (2 * ((n : ℝ) * C + 1)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hc_le : ∀ k j z, ‖c k j z‖ ≤ δ0 := by
    intro k j z
    have h1 : ENNReal.ofReal ‖c k j z‖ ≤ Work.CR.Flat.iterDerivNorm 0 (c k j) Set.univ := by
      rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := c k j) (s := Set.univ) (x := z)]
      exact Work.CR.Flat.le_iterDerivNorm 0 (c k j) Set.univ (Set.mem_univ z)
    have h2 : Work.CR.Flat.iterDerivNorm 0 (c k j) Set.univ
        ≤ Work.CR.Flat.holderNorm 0 α (c k j) Set.univ :=
      Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (c k j) Set.univ (Nat.zero_le 0)
    have h3 : ENNReal.ofReal ‖c k j z‖ ≤ ENNReal.ofReal δ0 := h1.trans (h2.trans (hc_small k j))
    exact (ENNReal.ofReal_le_ofReal_iff hδ0pos.le).mp h3
  have hFcont : ∀ j, Continuous (F j) := fun j =>
    Work.NN.Core.continuous_of_holderNorm_zero_lt_top hα0 (hF_fin j)
  have hVcont : ∀ j, Continuous (fun z => Work.CR.Flat.dbarCoord j W z) := fun j =>
    Work.NN.Core.continuous_dbarCoord j hW_sm
  have hVcs : ∀ j, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord j W z) := fun j =>
    Work.NN.Core.hasCompactSupport_dbarCoordAux hW_cs j
  set V : Fin n → (Fin n → ℂ) → ℂ := fun j z => Work.CR.Flat.dbarCoord j W z with hVdef
  set E : Fin n → (Fin n → ℂ) → ℂ := fun j z => V j z - F j z with hEdef
  have hVE : ∀ j z, E j z = Work.CR.Flat.dbarCoord j W z - F j z := fun j z => rfl
  have hEcont : ∀ j, Continuous (E j) := fun j => (hVcont j).sub (hFcont j)
  have hEcs : ∀ j, HasCompactSupport (E j) := fun j => (hVcs j).sub (hF_cs j)
  have hbmV : Work.CR.Flat.Cauchy.bmPotential V = fun z => Γ * W z := by
    funext z
    exact (Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul hn hW_sm hW_cs z).symm
  have hbmE_fun : Work.CR.Flat.Cauchy.bmPotential E
      = fun z => Γ * W z - Work.CR.Flat.Cauchy.bmPotential F z := by
    rw [hEdef, bmPotential_sub hn hVcont hVcs hFcont hF_cs, hbmV]
  obtain ⟨RF, hRFpos, hRF⟩ := exists_radius_family (n := n) (ι := Fin n) hF_cs
  obtain ⟨Rρ, hRρpos, hRρ⟩ : ∃ R : ℝ, 0 < R ∧ ∀ j : Fin n, ρ j < R := by
    refine ⟨(∑ j, (ρ j + 1)) + 1, by
      have : 0 ≤ ∑ j : Fin n, (ρ j + 1) := Finset.sum_nonneg (fun j _ => by linarith [hρ j])
      linarith, fun j => ?_⟩
    calc ρ j ≤ ρ j + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ ∑ i, (ρ i + 1) :=
          Finset.single_le_sum (f := fun i => ρ i + 1) (fun i _ => by linarith [hρ i])
            (Finset.mem_univ j)
      _ < (∑ i, (ρ i + 1)) + 1 := by linarith
  set R : ℝ := max RF (max Rρ 1) + 1 with hRdef
  have hRFle : RF ≤ R := by
    have h1 : RF ≤ max RF (max Rρ 1) := le_max_left _ _
    rw [hRdef]; linarith
  have hRρle : Rρ ≤ R := by
    have h1 : Rρ ≤ max Rρ 1 := le_max_left _ _
    have h2 : max Rρ 1 ≤ max RF (max Rρ 1) := le_max_right _ _
    rw [hRdef]; linarith
  have hρR : ∀ j, ρ j < R := fun j => lt_of_lt_of_le (hRρ j) hRρle
  have hFsuppR : ∀ j z, R ≤ ‖z‖ → F j z = 0 := fun j z hz => hRF j z (le_trans hRFle hz)
  have hRpos : 0 < R := by
    have h1 : 0 < max RF (max Rρ 1) := lt_of_lt_of_le hRFpos (le_max_left _ _)
    rw [hRdef]; linarith
  have hFdiff' : ∀ z ∈ Work.CR.Flat.polydisc 0 (fun _ : Fin n => 2 * R / 2),
      DifferentiableAt ℝ (fun z => Work.CR.Flat.Cauchy.bmPotential F z) z :=
    Work.NN.Core.bmPotential_differentiableAt_holder hn hα0 hα1
      (c := 0) (r := fun _ : Fin n => 2 * R) (fun _ => by linarith)
      (fun j => hF_fin j)
      (fun j z hz => by
        obtain ⟨i, hi⟩ := hz
        exact hFsuppR j z (le_trans (by simpa using hi)
          (by simpa using norm_le_pi_norm z i)))
  have hFdiff : ∀ z ∈ Work.CR.Flat.polydisc 0 (fun _ : Fin n => R),
      DifferentiableAt ℝ (fun z => Work.CR.Flat.Cauchy.bmPotential F z) z := by
    intro z hz
    exact hFdiff' z (by
      simp only [Work.CR.Flat.mem_polydisc] at hz ⊢
      intro i
      simpa using hz i)
  have hEeq : ∀ j z, E j z
      = Γ⁻¹ * (∑ l, c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z) := by
    intro j z
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
    · have hzR : z ∈ Work.CR.Flat.polydisc 0 (fun _ : Fin n => R) := fun i =>
        lt_trans (hz i) (hρR i)
      have hdiffV : DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPotential V) z := by
        rw [hbmV]
        exact ((hW_sm.differentiable (by norm_num)).differentiableAt).const_mul Γ
      have hdiffF : DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPotential F) z := hFdiff z hzR
      have hfdV : fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential V) z = Γ • fderiv ℝ W z := by
        rw [hbmV]
        exact fderiv_const_mul ((hW_sm.differentiable (by norm_num)).differentiableAt) Γ
      have hfdE : fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential E) z
          = fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential V) z
            - fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential F) z := by
        have hfun : Work.CR.Flat.Cauchy.bmPotential E
            = fun y => Work.CR.Flat.Cauchy.bmPotential V y
              - Work.CR.Flat.Cauchy.bmPotential F y := by
          rw [hbmE_fun, hbmV]
        rw [hfun]
        exact fderiv_sub hdiffV hdiffF
      have hdcoord : ∀ l, Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z
          = Γ * Work.CR.Flat.dCoord l W z
            - Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z := by
        intro l
        simp only [Work.CR.Flat.dCoord, hfdE, hfdV, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have hkey : ∀ l, Work.CR.Flat.dCoord l W z
            - Γ⁻¹ * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z
          = Γ⁻¹ * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z := by
        intro l
        rw [hdcoord l]
        field_simp
        try ring
      rw [hVE j z, hW_eq j z, hF_eq j z]
      have hflatten : (∑ l, c j l z * Work.CR.Flat.dCoord l W z + G j z)
            - (Γ⁻¹ * (∑ l, c j l z
                * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z)
          = ∑ l, c j l z * (Work.CR.Flat.dCoord l W z
              - Γ⁻¹ * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) := by
        rw [add_sub_add_right_eq_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hflatten]
      have hgoal : (∑ l, c j l z * (Work.CR.Flat.dCoord l W z
              - Γ⁻¹ * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z))
          = Γ⁻¹ * (∑ l, c j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hkey l]
        ring
      exact hgoal
    · simp only [Work.CR.Flat.mem_polydisc] at hz
      push_neg at hz
      have hcz : ∀ l, c j l z = 0 := by
        intro l
        by_contra hne
        obtain ⟨i, hi⟩ := hz
        exact not_le.mpr (by simpa using hc_supp j l z hne i) hi
      rw [hVE j z, hW_eq j z, hF_eq j z,
        Finset.sum_eq_zero (fun l _ => by rw [hcz l, zero_mul]),
        Finset.sum_eq_zero (fun l _ => by rw [hcz l, zero_mul]),
        Finset.sum_eq_zero (fun l _ => by rw [hcz l, zero_mul])]
      ring
  have hbmE_C1 : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential E) := by
    rw [hbmE_fun]
    exact (contDiff_const.mul hW_sm).sub (bmFC1 F hF_cs hF_fin)
  have hQ : (∫⁻ z : Fin n → ℂ, ∑ i : Fin n,
        ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖E j z‖ ^ 2 :=
    hL2 E hEcont hEcs hbmE_C1
  set qE : ℝ≥0∞ := ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖E j z‖ ^ 2 with hqEdef
  set qD : ℝ≥0∞ := ∫⁻ z : Fin n → ℂ, ∑ i : Fin n,
    ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 with hqDdef
  have hqD : qD ≤ ENNReal.ofReal (C ^ 2) * qE := hQ
  have hpt : ∀ z, (∑ j : Fin n, ENNReal.ofReal ‖E j z‖ ^ 2)
      ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
        * ∑ i : Fin n,
            ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 := by
    intro z
    have h1 : (∑ j : Fin n, ‖E j z‖ ^ 2)
        ≤ ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
          * ∑ i : Fin n,
              ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 := by
      have h := norm_sq_sum_le (n := n) hΓne (δ := δ0) (c := fun j l => c j l z)
        (fun j l => hc_le j l z)
        (d := fun i => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z)
      calc (∑ j : Fin n, ‖E j z‖ ^ 2)
          = ∑ j : Fin n, ‖Γ⁻¹ * (∑ l, c j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hEeq j z]
        _ ≤ _ := h
    have h2 : ENNReal.ofReal (∑ j : Fin n, ‖E j z‖ ^ 2)
        = ∑ j : Fin n, ENNReal.ofReal ‖E j z‖ ^ 2 := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2)]
      exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_pow (norm_nonneg _) 2
    rw [← h2]
    calc ENNReal.ofReal (∑ j : Fin n, ‖E j z‖ ^ 2)
        ≤ ENNReal.ofReal (((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ∑ i : Fin n,
                ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ENNReal.ofReal (∑ i : Fin n,
                ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ∑ i : Fin n,
                ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => ENNReal.ofReal_pow (norm_nonneg _) 2)
  have hqED : qE ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2) * qD := by
    rw [hqEdef, hqDdef]
    calc ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖E j z‖ ^ 2
        ≤ ∫⁻ z : Fin n → ℂ, ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ∑ i : Fin n,
                ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 :=
          lintegral_mono (fun z => hpt z)
      _ = ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ∫⁻ z : Fin n → ℂ, ∑ i : Fin n,
                ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential E) z‖ ^ 2 :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hqE_fin : qE < ⊤ := by
    rw [hqEdef]
    have hmeas : ∀ j : Fin n, Measurable (fun z : Fin n → ℂ => ENNReal.ofReal ‖E j z‖ ^ 2) := by
      intro j
      have h : Measurable (fun z : Fin n → ℂ => ENNReal.ofReal (‖E j z‖ ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((hEcont j).norm.pow 2).measurable
      rwa [funext (fun z => ENNReal.ofReal_pow (norm_nonneg (E j z)) 2)] at h
    rw [MeasureTheory.lintegral_finsetSum Finset.univ (fun j _ => hmeas j)]
    refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
    have hint : Integrable (fun z : Fin n → ℂ => ‖E j z‖ ^ 2) volume :=
      Continuous.integrable_of_hasCompactSupport ((hEcont j).norm.pow 2)
        (HasCompactSupport.mono' (hEcs j) (fun z hz => by
          rw [Function.mem_support] at hz
          by_contra hzc
          exact hz (by rw [image_eq_zero_of_notMem_tsupport hzc, norm_zero,
            zero_pow (by norm_num : (2:ℕ) ≠ 0)])))
    refine lt_of_eq_of_lt ?_ (Integrable.lintegral_lt_top hint)
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun z =>
      (ENNReal.ofReal_pow (norm_nonneg (E j z)) 2).symm)
  have hmain : qE ≤ ENNReal.ofReal ((1 : ℝ) / 4) * qE := by
    have h1 : qE ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2) * qD := hqED
    have h2 : ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2) * qD
        ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
          * (ENNReal.ofReal (C ^ 2) * qE) :=
      mul_le_mul_right (a := ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)) hqD
    have h3 : ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
          * (ENNReal.ofReal (C ^ 2) * qE)
        = (ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ENNReal.ofReal (C ^ 2)) * qE := by rw [mul_assoc]
    have h4 : ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2) * ENNReal.ofReal (C ^ 2)
        ≤ ENNReal.ofReal ((1 : ℝ) / 4) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hCnn : 0 ≤ C := hC0
      have hkey : (n : ℝ) * δ0 * C ≤ ‖Γ‖ / 2 := by
        have h5 : (n : ℝ) * C ≤ (n : ℝ) * C + 1 := by linarith
        have h6 : (n : ℝ) * C * δ0 ≤ ((n : ℝ) * C + 1) * δ0 :=
          mul_le_mul_of_nonneg_right h5 hδ0pos.le
        have h7 : ((n : ℝ) * C + 1) * δ0 ≤ ‖Γ‖ / 2 := by
          have h8 := hδ0Γ
          rw [mul_comm δ0] at h8
          linarith
        have h9 : (n : ℝ) * δ0 * C = (n : ℝ) * C * δ0 := by ring
        rw [h9]
        exact h6.trans h7
      have hpos : (0 : ℝ) ≤ (n : ℝ) * δ0 * C := by positivity
      have hsq : ((n : ℝ) * δ0 * C) ^ 2 ≤ (‖Γ‖ / 2) ^ 2 :=
        pow_le_pow_left₀ hpos hkey 2
      have hΓ2 : 0 < ‖Γ‖ ^ 2 := by positivity
      calc (‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2 * C ^ 2
          = (‖Γ‖ ^ 2)⁻¹ * (((n : ℝ) * δ0) ^ 2 * C ^ 2) := by ring
        _ = (‖Γ‖ ^ 2)⁻¹ * (((n : ℝ) * δ0 * C) ^ 2) := by ring
        _ ≤ (‖Γ‖ ^ 2)⁻¹ * ((‖Γ‖ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 1 / 4 := by
            field_simp
            ring
    calc qE ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2) * qD := h1
      _ ≤ ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * (ENNReal.ofReal (C ^ 2) * qE) := h2
      _ = (ENNReal.ofReal ((‖Γ‖ ^ 2)⁻¹ * ((n : ℝ) * δ0) ^ 2)
            * ENNReal.ofReal (C ^ 2)) * qE := h3
      _ ≤ ENNReal.ofReal ((1 : ℝ) / 4) * qE := mul_le_mul_left (a := qE) h4
  have hqE0 : qE = 0 := by
    have hlt := hqE_fin
    have hne_top : ENNReal.ofReal ((1 : ℝ) / 4) * qE ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlt.ne
    have h1 : qE.toReal ≤ (ENNReal.ofReal ((1 : ℝ) / 4) * qE).toReal :=
      (ENNReal.toReal_le_toReal hlt.ne hne_top).mpr hmain
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/4)] at h1
    have h2 : qE.toReal = 0 := by
      have h0 : 0 ≤ qE.toReal := ENNReal.toReal_nonneg
      linarith
    rcases (ENNReal.toReal_eq_zero_iff qE).mp h2 with h | h
    · exact h
    · exact absurd h hlt.ne
  have hE0 : ∀ j, E j = 0 := by
    intro j
    have h1 : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal ‖E j z‖ ^ 2) = 0 := by
      refine le_antisymm ?_ bot_le
      rw [← hqE0]
      refine lintegral_mono (fun z => ?_)
      exact Finset.single_le_sum (f := fun i => ENNReal.ofReal ‖E i z‖ ^ 2)
        (fun i _ => (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ‖E i z‖ ^ 2))
        (Finset.mem_univ j)
    have h3 : (fun z : Fin n → ℂ => ENNReal.ofReal ‖E j z‖ ^ 2) =ᵐ[volume] 0 := by
      rw [← lintegral_eq_zero_iff']
      · exact h1
      · have h : Measurable (fun z : Fin n → ℂ => ENNReal.ofReal ‖E j z‖ ^ 2) := by
          have h' : Measurable (fun z : Fin n → ℂ => ENNReal.ofReal (‖E j z‖ ^ 2)) :=
            ENNReal.measurable_ofReal.comp ((hEcont j).norm.pow 2).measurable
          rwa [funext (fun z => ENNReal.ofReal_pow (norm_nonneg (E j z)) 2)] at h'
        exact h.aemeasurable
    have h4 : E j =ᵐ[volume] 0 := by
      filter_upwards [h3] with z hz
      have hz' : ENNReal.ofReal (‖E j z‖ ^ 2) = 0 := by
        simpa [ENNReal.ofReal_pow (norm_nonneg (E j z))] using hz
      have hz'' : ‖E j z‖ ^ 2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hz') (by positivity)
      simpa using hz''
    exact (Continuous.ae_eq_iff_eq volume (hEcont j) continuous_const).mp h4
  intro j z
  have h := congrFun (hE0 j) z
  rw [hEdef, hVdef] at h
  simpa using sub_eq_zero.mp h

theorem beltrami_L2_identify_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ)
        (W : (Fin n → ℂ) → ℂ) (F : Fin n → (Fin n → ℂ) → ℂ),
        (∀ k j, ContDiff ℝ ⊤ (c k j)) →
        (∀ k j, HasCompactSupport (c k j)) →
        (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ k, ContDiff ℝ 1 (G k)) →
        (∀ k, HasCompactSupport (G k)) →
        (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) →
        ContDiff ℝ 1 W → HasCompactSupport W →
        (∀ k z, Work.CR.Flat.dbarCoord k W z
            = (∑ j, c k j z * Work.CR.Flat.dCoord j W z) + G k z) →
        (∀ j, HasCompactSupport (F j)) →
        (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
        (∀ j z, F j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (∑ l,
            c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z) →
        ∀ j z, Work.CR.Flat.dbarCoord j W z = F j z := by
  obtain ⟨C, hC0, hL2⟩ := Work.NN.Core.czB_L2_bounded_C0 (n := n) hn
  exact beltrami_L2_identify_holder_aux hn hα0 hα1 hρ ⟨C, hC0, hL2⟩
    (fun F hF hFfin => Work.NN.Core.contDiff_one_bmPotential_of_holder hn hα0 hα1 hF hFfin)

end Work.NN.Core
