import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.isClosedForm_dbarCoord
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
import Submission.Work.CR.Flat.Cauchy.dbar_interior_oneshot_C0
import Submission.Work.CR.Flat.Holder.holderNorm_comp_add
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.NN.Final.iterDerivNorm_comp_smul
import Submission.Work.NN.Final.holderNormCongr
import Submission.Work.NN.Ratio.Cut
import Submission.Work.NN.Ratio.Setup
import Submission.Work.NN.Newton.ThinLocal.scalingF
import Submission.Work.NN.Newton.ThinLocal.scalingU

namespace Work.NN.Newton.ThinLocal

open scoped NNReal ENNReal ContDiff
open Set

/-! ## Small localisation helpers for the thin-local gain -/

/-- Chain rule for the flat `∂̄`-operator under the rescaling `ζ ↦ c + s • ζ`:
`∂̄_j (u ∘ (c + s • ·)) ζ = s · ∂̄_j u (c + s • ζ)`. -/
private lemma dbarCoord_comp_shift {n : ℕ} (j : Fin n) (s : ℝ) (c : (Fin n → ℂ))
    {u : (Fin n → ℂ) → ℂ} {ζ : Fin n → ℂ} (hu : DifferentiableAt ℝ u (c + s • ζ)) :
    Work.CR.Flat.dbarCoord j (fun ζ' => u (c + s • ζ')) ζ
      = (s : ℂ) * Work.CR.Flat.dbarCoord j u (c + s • ζ) := by
  have hvec : ∀ z' : Fin n → ℂ, (fun i => c i + (s : ℂ) * z' i) = c + s • z' := by
    intro z'; funext i; simp [Complex.real_smul]
  have hfn : (fun z' : Fin n → ℂ => u (fun i => c i + (s : ℂ) * z' i))
      = (fun ζ' => u (c + s • ζ')) := funext fun z' => by rw [hvec z']
  have h := Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine (n := n) (a := fun _ => s) (b := c) j
    (U := u) (z := ζ) (by rw [hvec ζ]; exact hu)
  rw [hfn, hvec ζ] at h
  simpa using h

/-- Localisation of the flat `∂̄`-operator: a cutoff `ψ` which is `1` on the polydisc of radius
`5` about the origin can be dropped from `ψ · v` as far as `∂̄` on the polydisc of radius `4`
is concerned. -/
private lemma dbarCoord_mul_eqOn {n : ℕ} (j : Fin n) (v ψ : (Fin n → ℂ) → ℂ)
    (hψ : ∀ ζ ∈ Work.CR.Flat.polydisc 0 (fun _ => 5), ψ ζ = 1) :
    Set.EqOn (fun ζ => Work.CR.Flat.dbarCoord j (fun ζ' => ψ ζ' * v ζ') ζ)
      (fun ζ => Work.CR.Flat.dbarCoord j v ζ)
      (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
  intro ζ hζ
  have hmem : ζ ∈ Work.CR.Flat.polydisc 0 (fun _ => 5) := fun i => lt_trans (hζ i) (by norm_num)
  have hnhds : (fun ζ' => ψ ζ' * v ζ') =ᶠ[nhds ζ] v := by
    filter_upwards [(Work.CR.Flat.isOpen_polydisc 0 (fun _ => 5)).mem_nhds hmem] with w hw
    rw [hψ w hw, one_mul]
  change (1/2 : ℂ) * (fderiv ℝ (fun ζ' => ψ ζ' * v ζ') ζ (Pi.single j 1)
      + Complex.I * fderiv ℝ (fun ζ' => ψ ζ' * v ζ') ζ (Pi.single j Complex.I))
    = (1/2 : ℂ) * (fderiv ℝ v ζ (Pi.single j 1)
      + Complex.I * fderiv ℝ v ζ (Pi.single j Complex.I))
  rw [hnhds.fderiv_eq]

/-- `∂̄` of a smooth function is smooth. -/
private lemma contDiff_dbarCoord {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (fun z => Work.CR.Flat.dbarCoord j u z) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ u z (Pi.single j 1)) := hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ u z (Pi.single j Complex.I)) :=
    hfd.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞ (fun z => (1/2 : ℂ) * (fderiv ℝ u z (Pi.single j 1)
      + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))) :=
    contDiff_const.mul (h1.add (contDiff_const.mul h2))
  rw [show (fun z => Work.CR.Flat.dbarCoord j u z)
      = (fun z => (1/2 : ℂ) * (fderiv ℝ u z (Pi.single j 1)
          + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))) from rfl]
  exact h3

/-- **Local `C^{1,α} → C^{2,α}` gain at scale `s`, with a constant `K/s³`.**

If `u` is globally smooth, bounded by `B`, and solves `∂̄_j u = f_j` on the polydisc of radius `4s`
about `c` (`0 < s ≤ 1`), then the `C^{2,α}` norm of `u` on the polydisc of radius `2s` about `c`
is bounded by `(K/s³)` times the sum of the (dilated) `C^{1,α}` norms of `f` on the polydisc of
radius `4s` plus `B`; `K` depends only on `n` and `α`. -/
theorem localGain {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Work.NN.Core.Cn n → ℂ) (f : Fin n → Work.NN.Core.Cn n → ℂ)
        (c : Work.NN.Core.Cn n) (s B : ℝ),
      0 < s → s ≤ 1 → (∀ m : ℕ, ContDiff ℝ m u) →
      (∀ j z, (∀ i, ‖z i - c i‖ < 4 * s) → Work.CR.Flat.dbarCoord j u z = f j z) →
      (∀ z, ‖u z‖ ≤ B) →
      Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc c (fun _ => 2 * s)) ≤
        ENNReal.ofReal (K / s ^ 3) *
          ((∑ j, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
              (Work.CR.Flat.polydisc c (fun _ => 4 * s))) + ENNReal.ofReal B) := by
  -- ## the interior `C^{0,α}` estimate at the unit scale
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.CR.Flat.Cauchy.dbar_interior_oneshot_C0 (n := n) hn (c := 0)
      (ρi := fun _ => 2) (ρo := fun _ => 4) (by intro j; norm_num) (by intro j; norm_num)
      hα0 hα1 1
  refine ⟨C₁, hC₁pos, ?_⟩
  intro u f c s B hs hs1 hu heq hbound
  -- ## the cutoff and the localised function
  set ψ : (Fin n → ℂ) → ℂ := Work.NN.Ratio.polydiscCut (fun _ => 5) (fun _ => 6) with hψ
  have hψsm : ContDiff ℝ ∞ ψ := by
    rw [hψ]; exact Work.NN.Ratio.contDiff_polydiscCut _ _
  have hψone : ∀ ζ ∈ Work.CR.Flat.polydisc 0 (fun _ => 5), ψ ζ = 1 := by
    intro ζ hζ
    rw [hψ]
    exact Work.NN.Ratio.polydiscCut_eq_one (fun _ => by norm_num) (fun _ => by norm_num)
      (fun j => le_of_lt (by simpa using hζ j))
  have hψle : ∀ ζ, ‖ψ ζ‖ ≤ 1 := by
    intro ζ
    rw [hψ]
    exact Work.NN.Ratio.norm_polydiscCut_le_one _ _ ζ
  have hutop : ContDiff ℝ ∞ u := contDiff_infty.mpr hu
  have hlin : ContDiff ℝ ∞ (fun ζ : Fin n → ℂ => c + s • ζ) := by fun_prop
  have huc : ContDiff ℝ ∞ (fun ζ : Fin n → ℂ => u (c + s • ζ)) := hutop.comp hlin
  set Ũ : (Fin n → ℂ) → ℂ := fun ζ => ψ ζ * u (c + s • ζ) with hŨ
  have hŨsm : ContDiff ℝ ∞ Ũ := by rw [hŨ]; exact hψsm.mul huc
  have hdbarŨ : ∀ j : Fin n, ContDiff ℝ ∞ (fun z => Work.CR.Flat.dbarCoord j Ũ z) :=
    fun j => contDiff_dbarCoord j hŨsm
  have hclosed : Work.CR.Flat.IsClosedForm (fun j => fun z => Work.CR.Flat.dbarCoord j Ũ z) :=
    Work.CR.Flat.Polydisc.isClosedForm_dbarCoord Ũ (fun z => (hŨsm.contDiffAt).of_le (by simp))
  have hŨb : ∀ z, ‖Ũ z‖ ≤ B := by
    intro z
    rw [hŨ]
    calc ‖ψ z * u (c + s • z)‖ = ‖ψ z‖ * ‖u (c + s • z)‖ := norm_mul _ _
      _ ≤ 1 * B := mul_le_mul (hψle z) (hbound _) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  -- ## the interior estimate at the unit scale, applied to the localised data
  have honeshot := hC₁ Ũ (fun j z => Work.CR.Flat.dbarCoord j Ũ z) B
    (hŨsm.of_le (by simp)) (fun j => (hdbarŨ j).of_le (by simp)) hclosed
    (fun j z hz => rfl) (fun z hz => hŨb z)
  -- ## comparison of the left hand sides (translation, dilation, localisation)
  have hleft : Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc c (fun _ => 2 * s)) ≤
      ENNReal.ofReal (1 / s ^ 3) *
        Work.CR.Flat.holderNorm 2 α Ũ (Work.CR.Flat.polydisc 0 (fun _ => 2)) := by
    have h1 : Work.CR.Flat.holderNorm 2 α (fun w : Fin n → ℂ => u (c + w))
          (Work.CR.Flat.polydisc 0 (fun _ => 2 * s))
        = Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc c (fun _ => 2 * s)) := by
      rw [Work.CR.Flat.Holder.holderNorm_comp_add, Work.CR.Flat.Cauchy.polydisc_translate_image]
    have h2 : Work.CR.Flat.holderNorm 2 α (fun w : Fin n → ℂ => u (c + w))
          (Work.CR.Flat.polydisc 0 (fun _ => 2 * s))
        ≤ ENNReal.ofReal (1 / s ^ 3) *
            Work.CR.Flat.holderNorm 2 α (fun ζ : Fin n → ℂ => u (c + s • ζ))
              (Work.CR.Flat.polydisc 0 (fun _ => 2)) :=
      scalingU hα1 hs hs1 (fun w : Fin n → ℂ => u (c + w))
    have h3 : Work.CR.Flat.holderNorm 2 α (fun ζ : Fin n → ℂ => u (c + s • ζ))
          (Work.CR.Flat.polydisc 0 (fun _ => 2))
        = Work.CR.Flat.holderNorm 2 α Ũ (Work.CR.Flat.polydisc 0 (fun _ => 2)) := by
      refine Work.NN.Final.holderNorm_congr_of_eqOn ?_ 2 α
      intro ζ hζ
      have hmem : ζ ∈ Work.CR.Flat.polydisc 0 (fun _ => 5) :=
        fun i => lt_trans (hζ i) (by norm_num)
      show u (c + s • ζ) = Ũ ζ
      rw [hŨ]
      show u (c + s • ζ) = ψ ζ * u (c + s • ζ)
      rw [hψone ζ hmem, one_mul]
    calc Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc c (fun _ => 2 * s))
        = Work.CR.Flat.holderNorm 2 α (fun w : Fin n → ℂ => u (c + w))
            (Work.CR.Flat.polydisc 0 (fun _ => 2 * s)) := h1.symm
      _ ≤ ENNReal.ofReal (1 / s ^ 3) *
            Work.CR.Flat.holderNorm 2 α (fun ζ : Fin n → ℂ => u (c + s • ζ))
              (Work.CR.Flat.polydisc 0 (fun _ => 2)) := h2
      _ = ENNReal.ofReal (1 / s ^ 3) *
            Work.CR.Flat.holderNorm 2 α Ũ (Work.CR.Flat.polydisc 0 (fun _ => 2)) := by rw [h3]
  -- ## comparison of the right hand sides
  have hright : (∑ j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord j Ũ z)
        (Work.CR.Flat.polydisc 0 (fun _ => 4)))
      ≤ ∑ j : Fin n, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
          (Work.CR.Flat.polydisc c (fun _ => 4 * s)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h𝔥 : Set.EqOn (fun z : Fin n → ℂ => Work.CR.Flat.dbarCoord j Ũ z)
        (fun z : Fin n → ℂ => Work.CR.Flat.dbarCoord j (fun ζ => u (c + s • ζ)) z)
        (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
      have hh := dbarCoord_mul_eqOn (n := n) j (fun ζ : Fin n → ℂ => u (c + s • ζ)) ψ hψone
      rwa [← hŨ] at hh
    have h𝔤 : Set.EqOn (fun z : Fin n → ℂ => Work.CR.Flat.dbarCoord j (fun ζ => u (c + s • ζ)) z)
        (fun z : Fin n → ℂ => (s : ℂ) * f j (c + s • z))
        (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
      intro z hz
      have hd : DifferentiableAt ℝ u (c + s • z) := ((hu 1).differentiable (by norm_num)).differentiableAt
      show Work.CR.Flat.dbarCoord j (fun ζ => u (c + s • ζ)) z = (s : ℂ) * f j (c + s • z)
      rw [dbarCoord_comp_shift j s c hd]
      congr 1
      refine heq j (c + s • z) fun i => ?_
      have hzi : ‖z i‖ < 4 := by simpa using hz i
      have hci : (c + s • z) i - c i = s • (z i) := by simp
      rw [hci, norm_smul, Real.norm_of_nonneg hs.le]
      nlinarith
    have hcont : ContDiffOn ℝ (1 : ℕ∞) (fun z : Fin n → ℂ => f j (c + s • z))
        (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
      have hfP : ContDiffOn ℝ (1 : ℕ∞) (f j) (Work.CR.Flat.polydisc c (fun _ => 4 * s)) := by
        have hdu : ContDiffOn ℝ (1 : ℕ∞) (fun z => Work.CR.Flat.dbarCoord j u z)
            (Work.CR.Flat.polydisc c (fun _ => 4 * s)) :=
          ((contDiff_dbarCoord j hutop).of_le (by simp)).contDiffOn
        exact hdu.congr fun z hz => (heq j z hz).symm
      refine hfP.comp ?_ fun z hz => ?_
      · have hsm : ContDiff ℝ (1 : ℕ∞) (fun z : Fin n → ℂ => c + s • z) := by fun_prop
        exact hsm.contDiffOn
      · intro i
        have hzi : ‖z i‖ < 4 := by simpa using hz i
        have hci : (c + s • z) i - c i = s • (z i) := by simp
        rw [hci, norm_smul, Real.norm_of_nonneg hs.le]
        nlinarith
    have hstep1 : Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord j Ũ z)
          (Work.CR.Flat.polydisc 0 (fun _ => 4))
        = Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => (s : ℂ) * f j (c + s • z))
            (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
      rw [Work.NN.Final.holderNorm_congr_of_eqOn h𝔥 1 α,
        Work.NN.Final.holderNorm_congr_of_eqOn h𝔤 1 α]
    have hstep2 : Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => (s : ℂ) * f j (c + s • z))
          (Work.CR.Flat.polydisc 0 (fun _ => 4))
        = ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => f j (c + s • z))
            (Work.CR.Flat.polydisc 0 (fun _ => 4)) := by
      rw [show (fun z : Fin n → ℂ => (s : ℂ) * f j (c + s • z))
          = (s : ℂ) • (fun z : Fin n → ℂ => f j (c + s • z)) from rfl]
      rw [Work.CR.Flat.Holder.holderNorm_smul (k := 1) (α := α) (c := (s : ℂ)) hcont
        (Work.CR.Flat.isOpen_polydisc 0 (fun _ => 4)).uniqueDiffOn]
      congr 1
      rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hstep3 : Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => f j (c + s • z))
          (Work.CR.Flat.polydisc 0 (fun _ => 4))
        ≤ Work.CR.Flat.holderNorm 1 α (f j) (Work.CR.Flat.polydisc c (fun _ => 4 * s)) := by
      refine (scalingF hα0 hs hs1 (fun w : Fin n → ℂ => f j (c + w))).trans ?_
      rw [Work.CR.Flat.Holder.holderNorm_comp_add, Work.CR.Flat.Cauchy.polydisc_translate_image]
    calc Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord j Ũ z)
          (Work.CR.Flat.polydisc 0 (fun _ => 4))
        = Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => (s : ℂ) * f j (c + s • z))
            (Work.CR.Flat.polydisc 0 (fun _ => 4)) := hstep1
      _ = ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => f j (c + s • z))
            (Work.CR.Flat.polydisc 0 (fun _ => 4)) := hstep2
      _ ≤ ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
            (Work.CR.Flat.polydisc c (fun _ => 4 * s)) :=
          mul_le_mul_of_nonneg_left hstep3 (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal s)
  -- ## assembly
  calc Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc c (fun _ => 2 * s))
      ≤ ENNReal.ofReal (1 / s ^ 3) *
          Work.CR.Flat.holderNorm 2 α Ũ (Work.CR.Flat.polydisc 0 (fun _ => 2)) := hleft
    _ ≤ ENNReal.ofReal (1 / s ^ 3) *
          (ENNReal.ofReal C₁ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 1 α
              (fun z => Work.CR.Flat.dbarCoord j Ũ z) (Work.CR.Flat.polydisc 0 (fun _ => 4)))
            + ENNReal.ofReal B)) := mul_le_mul_of_nonneg_left honeshot (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / s ^ 3))
    _ ≤ ENNReal.ofReal (1 / s ^ 3) *
          (ENNReal.ofReal C₁ * ((∑ j : Fin n, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α
              (f j) (Work.CR.Flat.polydisc c (fun _ => 4 * s))) + ENNReal.ofReal B)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add hright le_rfl) (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal C₁))
          (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / s ^ 3))
    _ = ENNReal.ofReal (C₁ / s ^ 3) *
          ((∑ j : Fin n, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
              (Work.CR.Flat.polydisc c (fun _ => 4 * s))) + ENNReal.ofReal B) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf

end Work.NN.Newton.ThinLocal
