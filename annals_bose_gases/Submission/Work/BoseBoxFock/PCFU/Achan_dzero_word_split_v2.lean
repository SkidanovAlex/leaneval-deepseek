import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.Achan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_word_split
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_word_split_v2
import Submission.Work.ESYRound5.Energy.pairSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `Work.BoseBoxFock.PCFU.Achan_dzero_word_split_v2`

The `(A)`-channel word split: the `k = 0` term of the `(A)`-frame `KfrU` is *exactly* the
localised two-body kernel `wLoc ℓ (g₀) 0 (xᵢ) (xⱼ)` weighted by `ℓ³`, the rest of the frame
staying as an explicit remainder.

    ∫_x Θ x·χ_Λ(x i)χ_Λ(x j)·KfrU(x_j − x_i)·lowSlot(…)(x)
      = ℓ³ ∫_{abox} Θ x·wLoc ℓ (g₀) 0 (x i) (x j)·lowSlot(…)(x)
        + ∫_x Θ x·χ_Λ(x i)χ_Λ(x j)·(KfrU(x_j − x_i) − ℓ³·W₁(x_j − x_i))·lowSlot(…)(x) .

The proof is a pure re-association (`KfrU = ℓ³ W₁ + (KfrU − ℓ³ W₁)`) together with the
**pointwise** identity

    wLoc ℓ (g₀) 0 (x i) (x j) = χ_Λ(x i)·W₁(x i − x j)·χ_Λ(x j)   (`wLoc_g0_eq`)

and the **evenness** `W₁(x j − x i) = W₁(x i − x j)` (`Work.BoseFixR.isEven_W1fun`, which is
where the hypothesis `IsRadial v` is used — `KfrU` itself is even, but the word factor
`wLoc … 0 (x i) (x j)` carries the *other* orientation).

The only non-elementary input is the integrability of the windowed kernel
`(a,b) ↦ χ_Λ a·W₁(b − a)·χ_Λ b` on `ℝ³ × ℝ³` (`chiW1_integrable`, the exact cancellation
`(χ⋆χ)(·/ℓ) = ℓ³ convScale ℓ`), which is transported to the `N`-particle box by the
two-slot peel `integrableOn_abox_comp_pair_coord`.
-/

/-- **`KfrU` is continuous** (a finite sum of plane waves). -/
lemma az_continuous_KfrU {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Continuous (fun z : E3 => Work.BoseBoxFock.PCFU.KfrU v h μ fu N z) := by
  unfold Work.BoseBoxFock.PCFU.KfrU
  fun_prop

/-- **`KfrU` is bounded** (the triangle inequality on the finite sum). -/
lemma az_KfrU_norm_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N z‖ ≤ C := by
  refine ⟨∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|,
    Finset.sum_nonneg fun k _ => abs_nonneg _, fun z => ?_⟩
  unfold Work.BoseBoxFock.PCFU.KfrU
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

/-- **The abstract `(A)`-channel word split.**  With `ℓ`, `κ` abstract box parameters, the
`(A)`-frame `KfrU` is split into its `k = 0` part `ℓ³·W₁` (which is exactly the localised
two-body kernel `wLoc`) and the remainder. -/
lemma az_word_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hvrad : _root_.BoseGases.IsRadial v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {ℓ κ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x : Submission.BoseGases.X n, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
      = ((ℓ : ℂ)) ^ 3
          * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Θ x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                    - ((ℓ : ℂ)) ^ 3
                      * ((Work.BoseFixR.W1fun v h ℓ (x j - x i) : ℝ) : ℂ))
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ)) := by
  classical
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  -- ## 0. Work in the peeled form `Fin (M + 2)` (so that the two-slot peel applies).
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hlt : n < 2 := not_le.mp hc
    exact hij (Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega))
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  -- ## 1. Abbreviations.
  let Ψ : Submission.BoseGases.X (M + 2) → ℝ :=
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
  let Γ : Submission.BoseGases.X (M + 2) → ℝ := Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ
  let χ : E3 → ℝ := fun z => Work.BoseK15.corpusBox.chiLam ℓ z
  let Wf : E3 → ℝ := fun z => Work.BoseFixR.W1fun v h ℓ z
  let Kf : E3 → ℂ := fun z => Work.BoseBoxFock.PCFU.KfrU v h μ fu N z
  let F1 : Submission.BoseGases.X (M + 2) → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ) * Kf (x j - x i)
      * ((Γ x : ℝ) : ℂ)
  let Q : Submission.BoseGases.X (M + 2) → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ)
      * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
      * ((Γ x : ℝ) : ℂ)
  let F3 : Submission.BoseGases.X (M + 2) → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ)
      * (Kf (x j - x i) - ((ℓ : ℂ)) ^ 3 * ((Wf (x j - x i) : ℝ) : ℂ))
      * ((Γ x : ℝ) : ℂ)
  change (∫ x : Submission.BoseGases.X (M + 2), F1 x)
      = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox (M + 2) ℓ, Q x)
        + (∫ x : Submission.BoseGases.X (M + 2), F3 x)
  -- ## 2. Basic facts about the ingredients.
  obtain ⟨hΓm, D, hD0, hΓb⟩ := lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := μ) (ℓ := ℓ)
    (κ := κ) (Cθ := Cθ) (i := i) (j := j) hℓ hκ hCθ0 hΘm hCθ
  obtain ⟨CK, hCK0, hCKb⟩ := az_KfrU_norm_le (v := v) h μ fu N
  have hKfm : Continuous Kf := az_continuous_KfrU (v := v) h μ fu N
  set cχ : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hcχdef
  have hcχ0 : (0 : ℝ) ≤ cχ := by rw [hcχdef]; positivity
  have hχabs : ∀ z : E3, |χ z| ≤ cχ := by
    intro z
    rw [hcχdef]
    simpa only [χ] using chiLam_abs_le ℓ z
  have hΘ0 : ∀ x : Submission.BoseGases.X (M + 2),
      x ∉ Submission.BoseGases.abox (M + 2) ℓ → Θ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hΘs (Function.mem_support.mpr hne))
  -- ## 3. The windowed pair kernel is integrable, on `ℝ³ × ℝ³` and on the box.
  let Wp : E3 → E3 → ℝ := fun a b => χ a * Wf (b - a) * χ b
  have hWpair : Integrable (fun p : E3 × E3 => Wp p.1 p.2) (volume.prod volume) := by
    have hbase := Work.BoseBoxFock.PCFU.chiW1_integrable (v := v) h hℓ
    refine hbase.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Wp, Wf, χ, Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi,
      Submission.BoseGases.chiScale]
    rw [show p.1 - p.2 = -(p.2 - p.1) from by abel,
      Work.BoseFixR.isEven_W1fun h hvrad ℓ (p.2 - p.1)]
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  have hpairOn : IntegrableOn (fun x : Submission.BoseGases.X (M + 2) => Wp (x i) (x j))
      (Submission.BoseGases.abox (M + 2) ℓ) volume := by
    have h := Work.ESYRound5.Energy.integrableOn_abox_comp_pair_coord (M := M) hℓ.le i b'
      (W := Wp) hWpair.integrableOn
    simpa only [hb'] using h
  -- ## 4. The `ℝ`-valued pairing and its `ℂ`-forms.
  have hRealOn : IntegrableOn
      (fun x : Submission.BoseGases.X (M + 2) => Wp (x i) (x j) * (Θ x * Γ x))
      (Submission.BoseGases.abox (M + 2) ℓ) volume := by
    rw [IntegrableOn] at hpairOn ⊢
    refine hpairOn.mul_bdd (g := fun x => Θ x * Γ x) (c := Cθ * D)
      ((hΘm.mul hΓm).aestronglyMeasurable.restrict) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCθ x) (hΓb x) (abs_nonneg _) hCθ0
  have hRealOnC : IntegrableOn (fun x : Submission.BoseGases.X (M + 2) =>
      ((Wp (x i) (x j) * (Θ x * Γ x) : ℝ) : ℂ))
      (Submission.BoseGases.abox (M + 2) ℓ) volume := by
    rw [IntegrableOn] at hRealOn ⊢
    exact hRealOn.ofReal
  have hWIntOn : IntegrableOn (fun x : Submission.BoseGases.X (M + 2) =>
      ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ)
        * ((Wf (x j - x i) : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ))
      (Submission.BoseGases.abox (M + 2) ℓ) volume :=
    hRealOnC.congr_fun (fun x _ => by
      simp only [Wp]
      push_cast
      ring) (Submission.BoseGases.abox_measurable (M + 2) ℓ)
  have hWInt : Integrable (fun x : Submission.BoseGases.X (M + 2) =>
      ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ)
        * ((Wf (x j - x i) : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ))
      (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) := by
    rw [IntegrableOn] at hWIntOn
    exact hWIntOn
  -- ## 5. The `wLoc`-form on the box (the pointwise `wLoc`-identity + evenness of `W₁`).
  have hQOn : IntegrableOn Q (Submission.BoseGases.abox (M + 2) ℓ) volume :=
    hWIntOn.congr_fun (fun x _ => by
      simp only [Q]
      rw [wLoc_g0_eq v h ℓ (x i) (x j)]
      simp only [χ, Wf]
      rw [show x i - x j = -(x j - x i) from by abel,
        Work.BoseFixR.isEven_W1fun h hvrad ℓ (x j - x i)]
      push_cast
      ring) (Submission.BoseGases.abox_measurable (M + 2) ℓ)
  have hQInt : Integrable Q (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) := by
    rw [IntegrableOn] at hQOn
    exact hQOn
  -- ## 6. The two full integrands.
  have hχim : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (M + 2) => ((χ (x i) : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      ((chiLam_continuous ℓ).comp (continuous_apply i))).aestronglyMeasurable
  have hχjm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (M + 2) => ((χ (x j) : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      ((chiLam_continuous ℓ).comp (continuous_apply j))).aestronglyMeasurable
  have hKfae : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (M + 2) => Kf (x j - x i)) volume :=
    (hKfm.comp ((continuous_apply j).sub (continuous_apply i))).aestronglyMeasurable
  have hΓae : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (M + 2) => ((Γ x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hΓm.aestronglyMeasurable
  have hΘint : Integrable (fun x : Submission.BoseGases.X (M + 2) => ((Θ x : ℝ) : ℂ)) volume :=
    integrable_of_support_abox (n := M + 2) (ℓ := ℓ) (C := Cθ) hℓ
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hΘm.aestronglyMeasurable)
      (fun x => le_trans (le_of_eq (RCLike.norm_ofReal (Θ x))) (hCθ x))
      (fun x hx => by rw [hΘ0 x hx, Complex.ofReal_zero])
  have hbounds : ∀ x : Submission.BoseGases.X (M + 2),
      ‖((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ) * Kf (x j - x i) * ((Γ x : ℝ) : ℂ)‖
        ≤ cχ * cχ * CK * D := by
    intro x
    have e1 : ‖(((χ (x i)) : ℝ) : ℂ)‖ = |χ (x i)| := RCLike.norm_ofReal _
    have e2 : ‖(((χ (x j)) : ℝ) : ℂ)‖ = |χ (x j)| := RCLike.norm_ofReal _
    have e3 : ‖(((Γ x) : ℝ) : ℂ)‖ = |Γ x| := RCLike.norm_ofReal _
    rw [norm_mul, norm_mul, norm_mul, e1, e2, e3]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul (hχabs (x i)) (hχabs (x j)) (abs_nonneg _) hcχ0)
        (hCKb _) (norm_nonneg _) (mul_nonneg hcχ0 hcχ0))
      (hΓb x) (abs_nonneg _) (mul_nonneg (mul_nonneg hcχ0 hcχ0) hCK0)
  have hF1Int : Integrable F1 volume := by
    have h := hΘint.mul_bdd
      (g := fun x => ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ) * Kf (x j - x i)
        * ((Γ x : ℝ) : ℂ))
      (c := cχ * cχ * CK * D) (((hχim.mul hχjm).mul hKfae).mul hΓae)
      (Filter.Eventually.of_forall hbounds)
    exact h.congr (Filter.Eventually.of_forall fun x => by simp only [F1]; ring)
  have hF1IntOn : Integrable F1 (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) :=
    hF1Int.integrableOn
  have hF3IntOn : Integrable F3 (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) := by
    have hA : Integrable (fun x : Submission.BoseGases.X (M + 2) =>
        ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ) * ((χ (x j) : ℝ) : ℂ)
          * (((ℓ : ℂ)) ^ 3 * ((Wf (x j - x i) : ℝ) : ℂ)) * ((Γ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) :=
      (hWInt.const_mul (((ℓ : ℂ)) ^ 3)).congr
        (Filter.Eventually.of_forall fun x => by ring)
    have h := hF1IntOn.sub hA
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [F1, F3, Pi.sub_apply]; ring)
  -- ## 7. Everything is supported in the box.
  have hF1zero : ∀ x : Submission.BoseGases.X (M + 2),
      x ∉ Submission.BoseGases.abox (M + 2) ℓ → F1 x = 0 := by
    intro x hx
    have h0 : Θ x = 0 := hΘ0 x hx
    simp only [F1, h0, Complex.ofReal_zero, zero_mul]
  have hF3zero : ∀ x : Submission.BoseGases.X (M + 2),
      x ∉ Submission.BoseGases.abox (M + 2) ℓ → F3 x = 0 := by
    intro x hx
    have h0 : Θ x = 0 := hΘ0 x hx
    simp only [F3, h0, Complex.ofReal_zero, zero_mul]
  have hRed1 : (∫ x : Submission.BoseGases.X (M + 2), F1 x)
      = ∫ x in Submission.BoseGases.abox (M + 2) ℓ, F1 x := by
    rw [← integral_indicator (Submission.BoseGases.abox_measurable (M + 2) ℓ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Submission.BoseGases.abox (M + 2) ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hF1zero x hx]
  have hRed3 : (∫ x : Submission.BoseGases.X (M + 2), F3 x)
      = ∫ x in Submission.BoseGases.abox (M + 2) ℓ, F3 x := by
    rw [← integral_indicator (Submission.BoseGases.abox_measurable (M + 2) ℓ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Submission.BoseGases.abox (M + 2) ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hF3zero x hx]
  -- ## 8. The pointwise identity.
  have hpt : ∀ x : Submission.BoseGases.X (M + 2), F1 x = ((ℓ : ℂ)) ^ 3 * Q x + F3 x := by
    intro x
    simp only [F1, Q, F3, χ, Wf]
    rw [wLoc_g0_eq v h ℓ (x i) (x j)]
    rw [show x i - x j = -(x j - x i) from by abel,
      Work.BoseFixR.isEven_W1fun h hvrad ℓ (x j - x i)]
    push_cast
    ring
  -- ## 9. Assembly.
  have hQsm : Integrable (fun x : Submission.BoseGases.X (M + 2) => ((ℓ : ℂ)) ^ 3 * Q x)
      (volume.restrict (Submission.BoseGases.abox (M + 2) ℓ)) :=
    hQInt.const_mul (((ℓ : ℂ)) ^ 3)
  calc (∫ x : Submission.BoseGases.X (M + 2), F1 x)
      = ∫ x in Submission.BoseGases.abox (M + 2) ℓ, F1 x := hRed1
    _ = ∫ x in Submission.BoseGases.abox (M + 2) ℓ, (((ℓ : ℂ)) ^ 3 * Q x + F3 x) :=
        setIntegral_congr_fun (Submission.BoseGases.abox_measurable (M + 2) ℓ)
          (fun x _ => hpt x)
    _ = (∫ x in Submission.BoseGases.abox (M + 2) ℓ, ((ℓ : ℂ)) ^ 3 * Q x)
          + ∫ x in Submission.BoseGases.abox (M + 2) ℓ, F3 x := integral_add hQsm hF3IntOn
    _ = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox (M + 2) ℓ, Q x)
          + ∫ x in Submission.BoseGases.abox (M + 2) ℓ, F3 x := by rw [integral_const_mul]
    _ = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox (M + 2) ℓ, Q x)
          + ∫ x : Submission.BoseGases.X (M + 2), F3 x := by rw [← hRed3]

theorem Achan_dzero_word_split_v2 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
          * ((Work.BoseBoxFix.lowSlot fc
                (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Θ x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
                      (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                    - ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
                      * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                          (x j - x i) : ℝ) : ℂ))
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ)) :=
  az_word_split hij h hvrad fc fu μ N hℓ hκ Θ hΘm hΘb hΘs

end Work.BoseBoxFock.PCFU
