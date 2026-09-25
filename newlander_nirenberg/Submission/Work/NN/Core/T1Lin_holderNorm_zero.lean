import Mathlib
import Submission.Work.NN.Core.dbarHonestOneCk
import Submission.Work.NN.Core.ratioRecUHolderNormLevel
import Submission.Work.NN.Core.dataOfHolderNormLevel
import Submission.Work.NN.Core.HonestAux

/-!
# The level-`0` a priori estimate for the operator `T1Lin`

`Work.NN.Core.T1_holderNorm_le` (`Submission/Work/NN/Core/dbarHonestOneCk.lean`) gives the
`C^{k,α}` estimate for the explicit telescoping solution operator `T1Lin` for every `k ≥ 1`.
The present file supplies the missing level-`k = 0` case, which is what the local solvability
construction needs (`Work.NN.Core.dbarLocalSolver`).

The proof is the same three-ingredient assembly as at level `k ≥ 1`:

* the telescoping estimate `Work.NN.Core.ratioRecUHolderNormLevel` for `Geom.recU` on the
  equation polydisc `polydisc 0 (fun _ => thre η)`;
* the datum estimate, i.e. the level-`0` analogue `dataOfHolderNormLevel_zero_le` of
  `Work.NN.Core.dataOfHolderNormLevel` (that one is stated only for `k ≥ 1`);
* the composition with the inverse dilation `Ψ (scale η ρ)` as a continuous linear map
  `Work.NN.Core.PsiCLM`, via `Work.NN.Final.holderNorm_comp_linear`.

-/

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

theorem dataOfHolderNormLevel_zero_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        ∑ j, Work.CR.Flat.holderNorm 0 α (Work.NN.Ratio.dataOf η ρ f j)
              (Work.CR.Flat.polydisc 0 (fun _ => Work.NN.Ratio.thrb η))
          ≤ ENNReal.ofReal C *
              ∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc 0 ρ) := by
  let S : Fin n → ℝ := Work.NN.Ratio.scale η ρ
  have hPopen : IsOpen (polydisc (0 : Fin n → ℂ) ρ) := isOpen_polydisc _ _
  have hcomp : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) u (polydisc 0 ρ) →
      holderNorm k α (fun z => u (diagCLM S z)) (⇑(diagCLM S) ⁻¹' polydisc 0 ρ)
        ≤ ENNReal.ofReal C * holderNorm k α u (polydisc 0 ρ) :=
    fun k => Work.NN.Final.holderNorm_comp_linear (n := n) k hα0 (diagCLM S) hPopen
  choose Cf hCf using hcomp
  have hCfpos : ∀ k, 0 < Cf k := fun k => (hCf k).1
  have hCfbd : ∀ (k : ℕ) (u : (Fin n → ℂ) → ℂ), ContDiffOn ℝ (k : ℕ∞) u (polydisc 0 ρ) →
      holderNorm k α (fun z => u (diagCLM S z)) (⇑(diagCLM S) ⁻¹' polydisc 0 ρ)
        ≤ ENNReal.ofReal (Cf k) * holderNorm k α u (polydisc 0 ρ) :=
    fun k u hu => (hCf k).2 u hu
  refine ⟨(∑ l, ‖S l‖) * Cf 0 + 1, ?_, ?_⟩
  · have h1 : 0 < Cf 0 := hCfpos 0
    have h2 : 0 ≤ ∑ l, ‖S l‖ := Finset.sum_nonneg fun l _ => norm_nonneg _
    have h3 : 0 ≤ (∑ l, ‖S l‖) * Cf 0 := mul_nonneg h2 (le_of_lt h1)
    linarith
  · intro f hf
    have hstep : ∀ j, holderNorm 0 α (Work.NN.Ratio.dataOf η ρ f j)
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
        ≤ ENNReal.ofReal ((∑ l, ‖S l‖) * Cf 0 + 1) * holderNorm 0 α (f j) (polydisc 0 ρ) := by
      intro j
      have hΩbopen : IsOpen (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) :=
        isOpen_polydisc _ _
      have hPreopen : IsOpen (⇑(diagCLM S) ⁻¹' polydisc 0 ρ) :=
        hPopen.preimage (diagCLM S).continuous
      have hsub : polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)
          ⊆ ⇑(diagCLM S) ⁻¹' polydisc 0 ρ := by
        intro y hy
        have hyT : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrT η) :=
          polydisc_mono (fun l => le_of_lt (Work.NN.Ratio.thrb_lt_thrT h0)) hy
        exact Work.NN.Ratio.phi_mem_polydisc h0 h1 hρ hyT
      have hcongr : holderNorm 0 α (Work.NN.Ratio.dataOf η ρ f j)
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
          = holderNorm 0 α (fun y => (S j : ℂ) * f j (Work.NN.Ratio.Phi S y))
            (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) := by
        refine holderNorm_congr_gen (fun y hy => ?_)
        have hyT : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrT η) :=
          polydisc_mono (fun l => le_of_lt (Work.NN.Ratio.thrb_lt_thrT h0)) hy
        rw [Work.NN.Ratio.dataOf_apply, Work.NN.Ratio.polCut_eq_one_of_Phi h0 h1 hρ hyT,
          one_mul]
      have hsmul : (fun y => (S j : ℂ) * f j (Work.NN.Ratio.Phi S y))
          = (S j : ℂ) • (fun y => f j (Work.NN.Ratio.Phi S y)) := rfl
      have hcont : ContDiffOn ℝ (0 : ℕ∞) (fun y => f j (Work.NN.Ratio.Phi S y))
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) := by
        have hmaps : Set.MapsTo (Work.NN.Ratio.Phi S)
            (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) (polydisc 0 ρ) :=
          fun y hy => by
            have hyT : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrT η) :=
              polydisc_mono (fun l => le_of_lt (Work.NN.Ratio.thrb_lt_thrT h0)) hy
            exact Work.NN.Ratio.phi_mem_polydisc h0 h1 hρ hyT
        exact ((hf j).of_le (by norm_num)).comp
          (((Work.NN.Ratio.contDiff_Phi S).of_le (Work.NN.Ratio.le_infty 0)).contDiffOn) hmaps
      rw [hcongr, hsmul,
        Work.CR.Flat.Holder.holderNorm_smul (S j : ℂ) hcont hΩbopen.uniqueDiffOn]
      calc ENNReal.ofReal ‖(S j : ℂ)‖ * holderNorm 0 α (fun y => f j (Work.NN.Ratio.Phi S y))
              (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
          ≤ ENNReal.ofReal ‖(S j : ℂ)‖ *
              (ENNReal.ofReal (Cf 0) * holderNorm 0 α (f j) (polydisc 0 ρ)) := by
            refine mul_le_mul_right ?_ _
            exact le_trans
              (holderNorm_mono_set hPreopen hΩbopen hsub 0 α (fun y => f j (diagCLM S y)))
              (hCfbd 0 (f j) ((hf j).of_le (by norm_num)))
        _ = ENNReal.ofReal (‖(S j : ℂ)‖ * Cf 0) * holderNorm 0 α (f j) (polydisc 0 ρ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
        _ ≤ ENNReal.ofReal ((∑ l, ‖S l‖) * Cf 0 + 1) * holderNorm 0 α (f j) (polydisc 0 ρ) := by
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have hle : ‖S j‖ ≤ ∑ l, ‖S l‖ :=
              Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ j)
            have hmul : ‖S j‖ * Cf 0 ≤ (∑ l, ‖S l‖) * Cf 0 :=
              mul_le_mul_of_nonneg_right hle (le_of_lt (hCfpos 0))
            rw [Complex.norm_real]
            linarith
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hstep j)

/-- **The level-`0` a priori estimate for the operator `T1Lin` of the Newlander--Nirenberg
construction**, as requested: for `0 < α < 1` there is a constant `C > 0` such that for every
datum `f` of class `C^1` on `polydisc 0 ρ`,

  `‖T1Lin η hη0 hηhalf hρ f‖_{C^{0,α}(polydisc 0 ρ'')} ≤ C · ∑_j ‖f j‖_{C^{0,α}(polydisc 0 ρ)}`,

whenever `ρ'' j < thre η * scale η ρ j` for every `j`.  This is the `k = 0` case of the
family `Work.NN.Core.T1_holderNorm_le`, which is proved there only for `k ≥ 1`; the closedness
of the datum is not needed for the estimate (it is still needed to *solve* `∂̄ u = f`). -/
theorem T1Lin_holderNorm_zero {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) {ρ ρ'' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hρ'' : ∀ j, 0 < ρ'' j)
    (hgeo : ∀ j, ρ'' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        Work.CR.Flat.holderNorm 0 α (Work.NN.Core.T1Lin η hη0 hηhalf hρ f)
            (Work.CR.Flat.polydisc 0 ρ'')
          ≤ ENNReal.ofReal C *
              ∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ :
      ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
        ∀ (k : ℕ) (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) →
          holderNorm k α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU g z)
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η))
            ≤ ENNReal.ofReal (C k) *
                ∑ j, holderNorm k α (g j) (polydisc 0 (fun _ => Work.NN.Ratio.thrb η)) := by
    have h := ratioRecUHolderNormLevel (n := n) hα hα1 (Work.NN.Ratio.geomOf η hη0 hηhalf)
    simpa only [Work.NN.Ratio.geomOf_e, Work.NN.Ratio.geomOf_b] using h
  obtain ⟨C₂, hC₂pos, hC₂⟩ := dataOfHolderNormLevel_zero_le (n := n) hα hα1 hη0 hηhalf hρ
  let ex : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ u : (Fin n → ℂ) → ℂ, ContDiffOn ℝ k u (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) →
        holderNorm k α (fun z => u (PsiCLM (Work.NN.Ratio.scale η ρ) z))
            (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η)))
          ≤ ENNReal.ofReal c *
              holderNorm k α u (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := fun k =>
    Work.NN.Final.holderNorm_comp_linear (n := n) k hα
      (PsiCLM (Work.NN.Ratio.scale η ρ)) (isOpen_polydisc 0 (fun _ => Work.NN.Ratio.thre η))
  refine ⟨Classical.choose (ex 0) * C₁ 0 * C₂ + 1, ?_, ?_⟩
  · have h1 : 0 < Classical.choose (ex 0) := (Classical.choose_spec (ex 0)).1
    have h2 : 0 < C₁ 0 := hC₁pos 0
    have h3 : 0 < C₂ := hC₂pos
    positivity
  · intro f hf
    have hmem : f ∈ contOnPd0 n ρ := fun j => (hf j).continuousOn
    have hdat_sm : ∀ j, ContDiff ℝ ((0:ℕ) : WithTop ℕ∞) (Work.NN.Ratio.dataOf η ρ f j) :=
      fun j => contDiff_dataOfHonest (η := η) hη0 hηhalf hρ (m := 0)
        (fun j => (hf j).of_le (by norm_num)) j
    have hU_sm : ContDiffOn ℝ ((0:ℕ) : WithTop ℕ∞)
        (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z)
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
      have h := Work.NN.Ratio.contDiffOn_recU (G := Work.NN.Ratio.geomOf η hη0 hηhalf)
        (m := 0) (f := Work.NN.Ratio.dataOf η ρ f)
        (dataOf_contDiffOn (η := η) hη0 hηhalf hρ (m := 0)
          (fun j => (hf j).of_le (by norm_num)))
      simpa only [Work.NN.Ratio.geomOf_e] using h
    have hdil := (Classical.choose_spec (ex 0)).2
      (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f) z) hU_sm
    have hsub : polydisc 0 ρ'' ⊆ PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := by
      intro z hz
      rw [Set.mem_preimage, PsiCLM_apply]
      exact psi_mem_thre hη0 hηhalf hρ hgeo hz
    have hopen : IsOpen (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
        (polydisc 0 (fun _ => Work.NN.Ratio.thre η))) :=
      (isOpen_polydisc 0 (fun _ => Work.NN.Ratio.thre η)).preimage
        (PsiCLM (Work.NN.Ratio.scale η ρ)).continuous
    have hmono := holderNorm_mono_set hopen (isOpen_polydisc 0 ρ'') hsub 0 α
      (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU (Work.NN.Ratio.dataOf η ρ f)
        (PsiCLM (Work.NN.Ratio.scale η ρ) z))
    have hrec := hC₁ 0 (Work.NN.Ratio.dataOf η ρ f) hdat_sm
    have hdat := hC₂ f hf
    rw [T1Lin_apply η hη0 hηhalf hρ f hmem]
    calc holderNorm 0 α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (Work.NN.Ratio.Psi (Work.NN.Ratio.scale η ρ) z))
          (polydisc 0 ρ'')
        = holderNorm 0 α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (PsiCLM (Work.NN.Ratio.scale η ρ) z))
          (polydisc 0 ρ'') := by
          refine holderNorm_congr_gen fun z _ => ?_
          rw [PsiCLM_apply]
      _ ≤ holderNorm 0 α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
            (Work.NN.Ratio.dataOf η ρ f) (PsiCLM (Work.NN.Ratio.scale η ρ) z))
          (PsiCLM (Work.NN.Ratio.scale η ρ) ⁻¹'
            (polydisc 0 (fun _ => Work.NN.Ratio.thre η))) := hmono
      _ ≤ ENNReal.ofReal (Classical.choose (ex 0)) *
            holderNorm 0 α (fun z => (Work.NN.Ratio.geomOf η hη0 hηhalf).recU
              (Work.NN.Ratio.dataOf η ρ f) z)
              (polydisc 0 (fun _ => Work.NN.Ratio.thre η)) := hdil
      _ ≤ ENNReal.ofReal (Classical.choose (ex 0)) *
            (ENNReal.ofReal (C₁ 0) *
              ∑ j, holderNorm 0 α (Work.NN.Ratio.dataOf η ρ f j)
                (polydisc 0 (fun _ => Work.NN.Ratio.thrb η))) :=
          mul_le_mul' le_rfl hrec
      _ ≤ ENNReal.ofReal (Classical.choose (ex 0)) *
            (ENNReal.ofReal (C₁ 0) *
              (ENNReal.ofReal C₂ * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hdat)
      _ = ENNReal.ofReal (Classical.choose (ex 0) * C₁ 0 * C₂) *
            ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
          have hbc : ENNReal.ofReal (C₁ 0) *
                (ENNReal.ofReal C₂ * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ))
              = ENNReal.ofReal (C₁ 0 * C₂) *
                  ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hC₁pos 0))]
          rw [hbc, ← mul_assoc,
            ← ENNReal.ofReal_mul (le_of_lt (Classical.choose_spec (ex 0)).1), mul_assoc]
      _ ≤ ENNReal.ofReal (Classical.choose (ex 0) * C₁ 0 * C₂ + 1) *
            ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have h1 : 0 < Classical.choose (ex 0) := (Classical.choose_spec (ex 0)).1
          have h2 : 0 < C₁ 0 := hC₁pos 0
          have h3 : 0 < C₂ := hC₂pos
          have h4 : 0 ≤ Classical.choose (ex 0) * C₁ 0 * C₂ := by positivity
          linarith

end Work.NN.Core
