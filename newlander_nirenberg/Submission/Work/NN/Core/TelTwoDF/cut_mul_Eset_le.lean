/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Boundedness of the parametric cutoffs on the `C^{k,α}` scale

This file proves `Work.NN.Core.TelTwoDF.cut_mul_Eset_le`: on the tracking polydisc `Eset G s`
the multiplication by any of the three cutoffs `kappa G s`, `kappabar G s`, `1 - kappa G s` is
bounded on the `C^{k,α}` scale, with a single constant depending only on `G`, `k`, `α`.

The proof is the Leibniz-type bound `Work.CR.Flat.Holder.holderNorm_mul_le`
(`‖χ·f‖ ≤ ((k:ENNReal)+1) 2^(k+1) ‖χ‖ ‖f‖`), applied with finiteness of `‖χ‖` on `Eset G s`
supplied by `holderNorm_ne_top_Eset` (the three cutoffs are `C^∞`).
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The sum of the `C^{k,α}` norms, on the fibre `Eset G s`, of the three cutoffs at the
coordinate `s`. -/
private def cutNorm (n : ℕ) (k : ℕ) (α : ℝ) (G : Geom n) : Fin n → ℝ≥0∞ :=
  fun s => Work.CR.Flat.holderNorm k α (kappa G s) (Eset G (s : ℕ))
    + Work.CR.Flat.holderNorm k α (kappabar G s) (Eset G (s : ℕ))
    + Work.CR.Flat.holderNorm k α (fun y => 1 - kappa G s y) (Eset G (s : ℕ))

/-- The constant of the estimate: the Leibniz factor times the total cutoff norm, plus `1`. -/
private def cutConst (n : ℕ) (k : ℕ) (α : ℝ) (G : Geom n) : ℝ≥0∞ :=
  ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * (∑ s : Fin n, cutNorm n k α G s) + 1

/-- The cutoff `kappa G s` has finite `C^{k,α}`-norm on its tracking polydisc. -/
private lemma holderNorm_kappa_ne_top {n : ℕ} {α : ℝ} {k : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : Geom n) (s : Fin n) :
    Work.CR.Flat.holderNorm k α (kappa G s) (Eset G (s : ℕ)) ≠ ⊤ :=
  holderNorm_ne_top_Eset G (s : ℕ) hα0 hα1
    ((contDiff_kappa G s).of_le (by exact_mod_cast le_top))

/-- The `∂̄`-cutoff `kappabar G s` has finite `C^{k,α}`-norm on its tracking polydisc. -/
private lemma holderNorm_kappabar_ne_top {n : ℕ} {α : ℝ} {k : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : Geom n) (s : Fin n) :
    Work.CR.Flat.holderNorm k α (kappabar G s) (Eset G (s : ℕ)) ≠ ⊤ :=
  holderNorm_ne_top_Eset G (s : ℕ) hα0 hα1
    ((contDiff_kappabar G s).of_le (by exact_mod_cast le_top))

/-- The complementary cutoff `1 - kappa G s` has finite `C^{k,α}`-norm on `Eset G s`. -/
private lemma holderNorm_cutc_ne_top {n : ℕ} {α : ℝ} {k : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : Geom n) (s : Fin n) :
    Work.CR.Flat.holderNorm k α (fun y => 1 - kappa G s y) (Eset G (s : ℕ)) ≠ ⊤ :=
  holderNorm_ne_top_Eset G (s : ℕ) hα0 hα1
    ((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top))

private lemma cutNorm_ne_top {n : ℕ} {α : ℝ} {k : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : Geom n) (s : Fin n) : cutNorm n k α G s ≠ ⊤ := by
  simp only [cutNorm]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨holderNorm_kappa_ne_top hα0 hα1 G s,
      holderNorm_kappabar_ne_top hα0 hα1 G s⟩, holderNorm_cutc_ne_top hα0 hα1 G s⟩

private lemma cutConst_ne_top {n : ℕ} {α : ℝ} {k : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : Geom n) : cutConst n k α G ≠ ⊤ := by
  simp only [cutConst]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ?_ ?_, ENNReal.one_ne_top⟩
  · exact ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩)
      (ENNReal.pow_ne_top (by norm_num))
  · exact ENNReal.sum_ne_top.mpr fun s _ => cutNorm_ne_top hα0 hα1 G s

/-- The Leibniz-type bound for a bounded multiplier on the tracking polydisc: applied to two
`C^k` functions one of which has finite `C^{k,α}`-norm there. -/
private lemma holderNorm_cut_mul_le {n : ℕ} {α : ℝ} {k : ℕ} (G : Geom n) (s : Fin n)
    {χ f : (Fin n → ℂ) → ℂ}
    (hχ : ContDiffOn ℝ (k : ℕ∞) χ (Eset G (s : ℕ)))
    (hχne : Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) ≠ ⊤)
    (hf : ContDiffOn ℝ (k : ℕ∞) f (Eset G (s : ℕ)))
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hBf : Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≤ B) :
    Work.CR.Flat.holderNorm k α (fun y => χ y * f y) (Eset G (s : ℕ))
      ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1)
          * Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) * B := by
  have hΩ : UniqueDiffOn ℝ (Eset G (s : ℕ)) := (isOpen_Eset G (s : ℕ)).uniqueDiffOn
  have hfn : Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hBf
  calc Work.CR.Flat.holderNorm k α (fun y => χ y * f y) (Eset G (s : ℕ))
      ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ))
          * Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) :=
        Work.CR.Flat.Holder.holderNorm_mul_le hχ hf hΩ hχne hfn
    _ ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1)
          * Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) * B := by
        gcongr

/-- The single cutoff-factor bound: `‖χ·f‖ ≤ cutConst · B` for `χ` the cutoff, its `∂̄`, or its
complement. -/
private lemma cut_mul_cutConst_le {n : ℕ} {α : ℝ} {k : ℕ}
    (G : Geom n) (s : Fin n) {χ f : (Fin n → ℂ) → ℂ}
    (hχ : ContDiffOn ℝ (k : ℕ∞) χ (Eset G (s : ℕ)))
    (hχle : Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) ≤ cutNorm n k α G s)
    (hχne : Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) ≠ ⊤)
    (hf : ContDiffOn ℝ (k : ℕ∞) f (Eset G (s : ℕ)))
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hBf : Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≤ B) :
    Work.CR.Flat.holderNorm k α (fun y => χ y * f y) (Eset G (s : ℕ))
      ≤ cutConst n k α G * B := by
  have hb := holderNorm_cut_mul_le (G := G) (s := s) hχ hχne hf hB hBf
  calc Work.CR.Flat.holderNorm k α (fun y => χ y * f y) (Eset G (s : ℕ))
      ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1)
          * Work.CR.Flat.holderNorm k α χ (Eset G (s : ℕ)) * B := hb
    _ ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutNorm n k α G s * B := by gcongr
    _ ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * (∑ t : Fin n, cutNorm n k α G t) * B := by
        gcongr
        exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s)
    _ ≤ cutConst n k α G * B := by
        have h2 : ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * (∑ t : Fin n, cutNorm n k α G t)
            ≤ cutConst n k α G := by
          simp only [cutConst]
          exact le_add_right le_rfl
        gcongr

/-- **Multiplication by the parametric cutoffs is bounded on the `C^{k,α}` scale, on the tracking
polydiscs.**

For the cutoffs `kappa G s` (`= sharpCut (G.a s) (G.b s) (z s)`), their `∂̄`-derivatives
`kappabar G s` and the complementary cutoffs `1 - kappa G s` (all smooth, hence of finite
`C^{k,α}`-norm on the bounded polydisc `Eset G s`), there is a single constant `L : ENNReal` with
`L ≠ ⊤` (depending only on `G`, `k`, `α`) such that for every `f` of class `C^k` whose `C^{k,α}`-norm
on `Eset G s` is bounded by a finite `B : ENNReal`,

  `‖χ · f‖_{C^{k,α}(Eset G s)} ≤ L · B`

for `χ` any of `kappa G s`, `kappabar G s`, `1 - kappa G s`.

Route: `Work.CR.Flat.Holder.holderNorm_mul_le`
(`‖χ f‖ ≤ ((k:ENNReal)+1) * 2^(k+1) ‖χ‖ ‖f‖`) with finiteness of `‖χ‖` from
`holderNorm_ne_top_Eset` (`EstimateDefs`; the cutoffs are `C^∞` since
`Work.NN.Core.contDiff_sharpCut` gives smoothness of `sharpCut` and `contDiff_kappabar` in
`TelTwoDF/Defs.lean` that of its `∂̄`), and `IsOpen.uniqueDiffOn` for `isOpen_Eset`.  Take `L` to
be `((k:ENNReal)+1) * 2^(k+1)` times the sum, over the finitely many `s : Fin n`, of the three
cutoff norms on `Eset G s`, plus `1`. -/
theorem cut_mul_Eset_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    (G : Work.NN.Core.TelTwoDF.Geom n) :
    ∃ L : ENNReal, L ≠ ⊤ ∧
      (∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
        Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ B →
        Work.CR.Flat.holderNorm k α (fun y => Work.NN.Core.TelTwoDF.kappa G s y * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ L * B) ∧
      (∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
        Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ B →
        Work.CR.Flat.holderNorm k α (fun y => Work.NN.Core.TelTwoDF.kappabar G s y * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ L * B) ∧
      (∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
        Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ B →
        Work.CR.Flat.holderNorm k α (fun y => (1 - Work.NN.Core.TelTwoDF.kappa G s y) * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ L * B) := by
  have hα1' : α ≤ 1 := le_of_lt hα1
  refine ⟨cutConst n k α G, cutConst_ne_top hα0 hα1' G, ?_, ?_, ?_⟩
  · intro s f hf B hB hBf
    refine cut_mul_cutConst_le G s
      ((contDiff_kappa G s).of_le (by exact_mod_cast le_top)).contDiffOn ?_
      (holderNorm_kappa_ne_top hα0 hα1' G s) hf.contDiffOn hB hBf
    simp only [cutNorm]
    exact le_add_right (le_add_right le_rfl)
  · intro s f hf B hB hBf
    refine cut_mul_cutConst_le G s
      ((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).contDiffOn ?_
      (holderNorm_kappabar_ne_top hα0 hα1' G s) hf.contDiffOn hB hBf
    simp only [cutNorm]
    exact le_add_right (le_add_left le_rfl)
  · intro s f hf B hB hBf
    refine cut_mul_cutConst_le G s
      ((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).contDiffOn ?_
      (holderNorm_cutc_ne_top hα0 hα1' G s) hf.contDiffOn hB hBf
    simp only [cutNorm]
    exact le_add_left le_rfl

end Work.NN.Core.TelTwoDF
