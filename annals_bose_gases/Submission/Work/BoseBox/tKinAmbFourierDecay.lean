import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BSKinetic.swap_p_abox_tBamp
import Submission.Work.BoseBox.boxP_bigBox_abs_le
import Submission.Work.BoseBox.chiBigUnifData
import Submission.Work.BoseBox.tBampDecayUniform
import Submission.Work.BoseBox.tBamp_boxQInd_eq_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.tKinAmbFourierDecay` — uniform `(1+‖p‖)⁻³` decay of the sliding amplitude

The `C`-node side condition `CWordIntegrable` (`Submission/Work/BoseBox/CNodeDefs.lean`) needs the
`u`-integrand of the localised kinetic word to be integrable on the bounded localisation region
`coverU ℓ L`.  The word is a `p`-integral of the windowed amplitude
`tBamp (chiBig ℓ u) p (Q_{Λ(u),i}Ψ) i x`, so the integrability is a *domination* statement: a bound
`C/(1+‖p‖)³` on the amplitude, **uniform in `u ∈ coverU ℓ L`** (the region is bounded, so the
sliding window's support radius is uniformly bounded), in `x ∈ box N L`, in the slot `i` and in
`p`.  This file proves that bound.

## Where the uniformity comes from

The sliding window is `chiBig ℓ u = chiScale ℓ(· − ℓu)`, a *translation* of the fixed bump
`chiScale ℓ`; the support radius of `chiBig ℓ u` is therefore `R₀ + ‖ℓu‖`, and `u ∈ coverU ℓ L`
forces `ℓu ∈ ombox L − acube ℓ`, a bounded set (`chiBigUnifData`).  The derivative data of the
complexified window are *translation invariant* (`iteratedFDeriv_comp_add_left`), so a single `G`
bounds them for every `u`.  On the state side `fourier_decay_mul_update` needs the derivative data
of the *fixed* state `Ψ` on the ball of radius `S`, which is `complexified_iteratedFDeriv_bound`.

With those uniform data `tBampDecayUniform` gives one constant for the whole family.  Two
applications (the state `Ψ` and the constant state `1`) plus the exact decomposition of the
FS-faithful projection (`tBamp_boxQInd_eq_sub`)

  `Q_{Λ(u),i}Ψ = 1_{Λ(u)}·Ψ − P_{Λ(u),i}Ψ`,

whose mean term `P_{Λ(u),i}Ψ ≤ ‖Ψ‖_∞ ≤ M 0` (`boxP_bigBox_abs_le`), give the claim.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real

namespace Work.BoseBox

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem tKinAmbFourierDecay {N : ℕ} {L ℓ : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Work.BoseBox.coverU ℓ L,
      ∀ x ∈ _root_.BoseGases.box N L, ∀ i : Fin N, ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.SmallBoxTBWord.tBamp (Work.BoseBox.chiBig ℓ u) p
        (Work.UBBInputs8.boxQInd (ℓ ^ 3) (Work.BoseBox.bigBox ℓ u) i Ψ) i x‖
        ≤ C / (1 + ‖p‖) ^ 3 := by
  classical
  -- ## 0. The regime: `ℓ`, `L` positive
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- ## 1. Uniform window data on the localisation region
  obtain ⟨R, G, hR, hGnn, hχsupp, hχG⟩ := chiBigUnifData (ℓ := ℓ) (L := L) hℓ hL
  -- ## 2. A common radius `S` for the configurations of the corner box
  obtain ⟨B, hB⟩ := (Submission.BoseGases.acube_isBounded (2 * L) (by linarith)).exists_norm_le
  set S : ℝ := max R (max B 1) with hSdef
  have hRS : R ≤ S := le_max_left _ _
  have hBS : B ≤ S := le_trans (le_max_left B 1) (le_max_right R (max B 1))
  have hS1 : (1 : ℝ) ≤ S := le_trans (le_max_right B 1) (le_max_right R (max B 1))
  have hSnn : 0 ≤ S := le_trans zero_le_one hS1
  -- ## 3. Derivative data of `Ψ` (and of the constant state) on the ball of radius `S`
  obtain ⟨M, hMnn, hMb⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) (S := S) hSnn hΨ
  obtain ⟨M₁, hM₁nn, hM₁b⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) (S := S) hSnn
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Submission.BoseGases.X N => (1 : ℝ)))
  -- ## 4. Smoothness of the windows (uniformly in `u`), of `Ψ` and of `1`
  have hχsmooth : ∀ u : EuclideanSpace ℝ (Fin 3), ContDiff ℝ (⊤ : ℕ∞) (chiBig ℓ u) :=
    fun u => Work.BSKinetic.SwapTBAmp.contDiff_chiBig (ℓ := ℓ) hℓne u
  have hχcont : ∀ u : EuclideanSpace ℝ (Fin 3), Continuous (chiBig ℓ u) :=
    fun u => (hχsmooth u).continuous
  have hχcs : ∀ u : EuclideanSpace ℝ (Fin 3), HasCompactSupport (chiBig ℓ u) :=
    fun u => Work.BSKinetic.SwapTBAmp.hasCompactSupport_chiBig (ℓ := ℓ) hℓne u
  have hχcd : ∀ u : EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ 3 (fun z : EuclideanSpace ℝ (Fin 3) => (chiBig ℓ u z : ℂ)) :=
    fun u => Complex.ofRealCLM.contDiff.comp
      ((hχsmooth u).of_le (WithTop.coe_le_coe.mpr le_top))
  have hΨcd : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Ψ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΨ.of_le (WithTop.coe_le_coe.mpr le_top))
  have h1cd : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => ((1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Submission.BoseGases.X N => (1 : ℝ))).of_le
        (WithTop.coe_le_coe.mpr le_top))
  -- ## 5. Uniform decay of the amplitude of the *state* and of the *window*
  obtain ⟨C₁, hC₁nn, hC₁⟩ := tBampDecayUniform (N := N) hR hRS
    (χ := fun t : {u : EuclideanSpace ℝ (Fin 3) // u ∈ coverU ℓ L} => chiBig ℓ t.1)
    (Φ := fun _ : {u : EuclideanSpace ℝ (Fin 3) // u ∈ coverU ℓ L} => Ψ)
    (G := G) (M := M)
    (fun t => hχcd t.1) (fun t z => hχsupp t.1 t.2 z) (fun t k hk z => hχG t.1 t.2 k hk z)
    (fun _ => hΨcd) (fun _ k hk y hy => hMb k hk y hy)
  obtain ⟨C₂, hC₂nn, hC₂⟩ := tBampDecayUniform (N := N) hR hRS
    (χ := fun t : {u : EuclideanSpace ℝ (Fin 3) // u ∈ coverU ℓ L} => chiBig ℓ t.1)
    (Φ := fun _ : {u : EuclideanSpace ℝ (Fin 3) // u ∈ coverU ℓ L} =>
      (fun _ : Submission.BoseGases.X N => (1 : ℝ)))
    (G := G) (M := M₁)
    (fun t => hχcd t.1) (fun t z => hχsupp t.1 t.2 z) (fun t k hk z => hχG t.1 t.2 k hk z)
    (fun _ => h1cd) (fun _ k hk y hy => hM₁b k hk y hy)
  -- ## 6. The configurations of the corner box lie in the ball of radius `S`
  have hboxnorm : ∀ y : Submission.BoseGases.X N, y ∈ _root_.BoseGases.box N L →
      ∀ j : Fin N, ‖y j‖ ≤ B := by
    intro y hy j
    refine hB (y j) ?_
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have h1 : (y j).ofLp m ∈ Set.Icc 0 L := (Submission.BoseGases.mem_box_iff N L y).mp hy j m
    rw [Set.mem_Icc] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2, hL]
  have hSS : ∀ x : Submission.BoseGases.X N, x ∈ _root_.BoseGases.box N L →
      ∀ j : Fin N, ‖x j‖ ≤ S := fun x hx j => le_trans (hboxnorm x hx j) hBS
  -- ## 7. The state is bounded by `M 0` on the corner box
  have hM0 : ∀ y : Submission.BoseGases.X N, y ∈ _root_.BoseGases.box N L → |Ψ y| ≤ M 0 := by
    intro y hy
    have h := hMb 0 (by norm_num) y (hSS y hy)
    simpa [norm_iteratedFDeriv_zero, Complex.norm_real, Real.norm_eq_abs] using h
  -- ## 8. The box mean is bounded by the sup of the state
  have hmean : ∀ (u : EuclideanSpace ℝ (Fin 3)) (i : Fin N) (x : Submission.BoseGases.X N),
      ‖((Work.SmallBoxTBWord.boxP (ℓ ^ 3) (bigBox ℓ u) i Ψ (Function.update x i 0) : ℝ) : ℂ)‖
        ≤ M 0 := by
    intro u i x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact boxP_bigBox_abs_le hℓ (hMnn 0) hsupp hM0 u i (Function.update x i 0)
  -- ## 9. Assembly
  refine ⟨C₁ + M 0 * C₂, add_nonneg hC₁nn (mul_nonneg (hMnn 0) hC₂nn), ?_⟩
  intro u hu x hx i p
  have hxS : ∀ j : Fin N, ‖x j‖ ≤ S := hSS x hx
  have hdec := tBamp_boxQInd_eq_sub (volA := ℓ ^ 3) (A := bigBox ℓ u) (χ := chiBig ℓ u)
    Ψ i p x 0 (fun z hz => Work.BSKinetic.chiBig_eq_zero_of_notMem_bigBox (ℓ := ℓ) hℓ u z hz)
    (hχcont u) (hχcs u) hΨ.continuous
  rw [hdec]
  have hb1 := hC₁ ⟨u, hu⟩ x hxS i p
  have hb2 := hC₂ ⟨u, hu⟩ x hxS i p
  have hm := hmean u i x
  calc
    ‖Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p Ψ i x
        - ((Work.SmallBoxTBWord.boxP (ℓ ^ 3) (bigBox ℓ u) i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p
              (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p Ψ i x‖
        + ‖((Work.SmallBoxTBWord.boxP (ℓ ^ 3) (bigBox ℓ u) i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p
              (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖ := norm_sub_le _ _
    _ = ‖Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p Ψ i x‖
        + ‖((Work.SmallBoxTBWord.boxP (ℓ ^ 3) (bigBox ℓ u) i Ψ (Function.update x i 0) : ℝ) : ℂ)‖
          * ‖Work.SmallBoxTBWord.tBamp (chiBig ℓ u) p
              (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖ := by rw [norm_mul]
    _ ≤ C₁ / (1 + ‖p‖) ^ 3 + M 0 * (C₂ / (1 + ‖p‖) ^ 3) :=
        add_le_add hb1 (mul_le_mul hm hb2 (norm_nonneg _) (hMnn 0))
    _ = (C₁ + M 0 * C₂) / (1 + ‖p‖) ^ 3 := by rw [← mul_div_assoc, ← add_div]

end Work.BoseBox
