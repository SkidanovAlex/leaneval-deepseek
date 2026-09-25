import Mathlib
import Submission.Work.NN.Ratio.Scale
import Submission.Work.NN.Ratio.PullBack
import Submission.Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Core.HonestAux

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set
open Work.CR.Flat

/-- The diagonal map `y ↦ (l ↦ S l * y l)` as a continuous linear map.

It is the continuous linear map underlying the dilation `Work.NN.Ratio.Phi S`, and it is the
object to which `Work.NN.Final.holderNorm_comp_linear` is applied to transfer `C^{k,α}`
estimates from the polydisc `polydisc 0 ρ` (where the datum is given) to the tracking polydisc
`polydisc 0 (fun _ => thrb η)` (where the cutoff is one and the datum is read). -/
noncomputable def diagCLM {n : ℕ} (S : Fin n → ℝ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) where
  toFun := fun y l => (S l : ℂ) * y l
  map_add' := by intro x y; funext l; simp [mul_add]
  map_smul' := by
    intro c x; funext l
    simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring
  cont := by
    rw [continuous_pi_iff]
    intro l
    exact continuous_const.mul (continuous_apply l)

theorem dataOfHolderNormLevel {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        ∑ j, Work.CR.Flat.holderNorm k α (Work.NN.Ratio.dataOf η ρ f j)
              (Work.CR.Flat.polydisc 0 (fun _ => Work.NN.Ratio.thrb η))
          ≤ ENNReal.ofReal (C k) *
              ∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc 0 ρ) := by
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
  refine ⟨fun k => (∑ l, ‖S l‖) * Cf k + 1, ?_, ?_⟩
  · intro k
    have h1 : 0 < Cf k := hCfpos k
    have h2 : 0 ≤ ∑ l, ‖S l‖ := Finset.sum_nonneg fun l _ => norm_nonneg _
    have h3 : 0 ≤ (∑ l, ‖S l‖) * Cf k := mul_nonneg h2 (le_of_lt h1)
    linarith
  · intro k hk f hf
    have hstep : ∀ j, holderNorm k α (Work.NN.Ratio.dataOf η ρ f j)
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
        ≤ ENNReal.ofReal ((∑ l, ‖S l‖) * Cf k + 1) * holderNorm k α (f j) (polydisc 0 ρ) := by
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
      -- On the tracking polydisc the cutoff is `1`, so `dataOf` is the rescaled datum.
      have hcongr : holderNorm k α (Work.NN.Ratio.dataOf η ρ f j)
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
          = holderNorm k α (fun y => (S j : ℂ) * f j (Work.NN.Ratio.Phi S y))
            (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) := by
        refine holderNorm_congr_gen (fun y hy => ?_)
        have hyT : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrT η) :=
          polydisc_mono (fun l => le_of_lt (Work.NN.Ratio.thrb_lt_thrT h0)) hy
        rw [Work.NN.Ratio.dataOf_apply, Work.NN.Ratio.polCut_eq_one_of_Phi h0 h1 hρ hyT,
          one_mul]
      have hsmul : (fun y => (S j : ℂ) * f j (Work.NN.Ratio.Phi S y))
          = (S j : ℂ) • (fun y => f j (Work.NN.Ratio.Phi S y)) := rfl
      have hcont : ContDiffOn ℝ (k : ℕ∞) (fun y => f j (Work.NN.Ratio.Phi S y))
          (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) := by
        have hmaps : Set.MapsTo (Work.NN.Ratio.Phi S)
            (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η)) (polydisc 0 ρ) :=
          fun y hy => by
            have hyT : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrT η) :=
              polydisc_mono (fun l => le_of_lt (Work.NN.Ratio.thrb_lt_thrT h0)) hy
            exact Work.NN.Ratio.phi_mem_polydisc h0 h1 hρ hyT
        exact (hf j).comp
          (((Work.NN.Ratio.contDiff_Phi S).of_le (Work.NN.Ratio.le_infty k)).contDiffOn) hmaps
      rw [hcongr, hsmul,
        Work.CR.Flat.Holder.holderNorm_smul (S j : ℂ) hcont hΩbopen.uniqueDiffOn]
      calc ENNReal.ofReal ‖(S j : ℂ)‖ * holderNorm k α (fun y => f j (Work.NN.Ratio.Phi S y))
              (polydisc (0 : Fin n → ℂ) (fun _ => Work.NN.Ratio.thrb η))
          ≤ ENNReal.ofReal ‖(S j : ℂ)‖ *
              (ENNReal.ofReal (Cf k) * holderNorm k α (f j) (polydisc 0 ρ)) := by
            refine mul_le_mul_right ?_ _
            exact le_trans
              (holderNorm_mono_set hPreopen hΩbopen hsub k α (fun y => f j (diagCLM S y)))
              (hCfbd k (f j) (hf j))
        _ = ENNReal.ofReal (‖(S j : ℂ)‖ * Cf k) * holderNorm k α (f j) (polydisc 0 ρ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
        _ ≤ ENNReal.ofReal ((∑ l, ‖S l‖) * Cf k + 1) * holderNorm k α (f j) (polydisc 0 ρ) := by
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have hle : ‖S j‖ ≤ ∑ l, ‖S l‖ :=
              Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ j)
            have hmul : ‖S j‖ * Cf k ≤ (∑ l, ‖S l‖) * Cf k :=
              mul_le_mul_of_nonneg_right hle (le_of_lt (hCfpos k))
            rw [Complex.norm_real]
            linarith
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hstep j)

end Work.NN.Core
