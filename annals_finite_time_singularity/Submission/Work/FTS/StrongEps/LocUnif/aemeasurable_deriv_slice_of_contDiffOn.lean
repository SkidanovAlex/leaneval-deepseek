/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of the squared `z`-slice derivative against a closed rectangle

The integrand `(z, θ) ↦ (∂_z u(z, θ))² · (w(z, θ))²` of the `H^k`-weighted norms is
`AEMeasurable` for `volume` restricted to the closed rectangle `[a,b] × [c,d]`, as soon as
the profile `u` is `C¹` on the *open* rectangle `(a,b) × (c,d)` and the weight `w` is
continuous on the closed rectangle.  No measurability of `u` off the open rectangle is
needed (there the slice derivative is unconstrained): the closed rectangle differs from the
open one by a Lebesgue-null set.

Proof, the standard one:

* on the open rectangle `S = (a,b) × (c,d)` the slice derivative
  `deriv (fun z' => u z' θ) z` is the Fréchet derivative of `Function.uncurry u` in the
  direction `(1,0)` (`Work.Spaces.pz_eq_fderiv`), and `p ↦ fderiv ℝ (uncurry u) p` is
  continuous on `S` because `S` is open and `uncurry u` is `C¹` there
  (`ContDiffOn.continuousOn_fderiv_of_isOpen`);
* hence the integrand agrees on `S` with a function that is continuous on `S`, so it is
  `AEMeasurable` for `volume.restrict S`;
* `T \ S ⊆ ({a,b} × univ) ∪ (univ × {c,d})` is null, so `volume.restrict T =
  volume.restrict S` and the measurability transfers to the closed rectangle.

The result is the `ρ`-instance of the sibling lemma
`Work.FTS.StrongEps.LocUnif.aemeasurable_derivSq_mul_of_contDiffOn_one`, proved here
directly so that this module is self-contained.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.LocUnif.rho_bounds
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

/-- The closed rectangle differs from the open one by a null set: any point of
`[a,b] × [c,d]` that is not in `(a,b) × (c,d)` has one of its coordinates at an endpoint. -/
private lemma volume_diff_box_Icc_Ioo (a b c d : ℝ) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
        ((Set.Icc a b ×ˢ Set.Icc c d) \ (Set.Ioo a b ×ˢ Set.Ioo c d)) = 0 := by
  have hsub : (Set.Icc a b ×ˢ Set.Icc c d) \ (Set.Ioo a b ×ˢ Set.Ioo c d)
      ⊆ ({a, b} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({c, d} : Set ℝ)) := by
    rintro ⟨x, y⟩ hp
    rw [Set.mem_sdiff, Set.mem_prod, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo, Set.mem_Icc,
      Set.mem_Icc] at hp
    obtain ⟨⟨hx, hy⟩, hnot⟩ := hp
    have hcase : (x = a ∨ x = b) ∨ (y = c ∨ y = d) := by
      rcases not_and_or.mp hnot with hA | hB
      · left
        rcases lt_or_ge a x with h | h
        · rcases lt_or_ge x b with h' | h'
          · exact absurd ⟨h, h'⟩ hA
          · exact Or.inr (le_antisymm hx.2 h')
        · exact Or.inl (le_antisymm h hx.1)
      · right
        rcases lt_or_ge c y with h | h
        · rcases lt_or_ge y d with h' | h'
          · exact absurd ⟨h, h'⟩ hB
          · exact Or.inr (le_antisymm hy.2 h')
        · exact Or.inl (le_antisymm h hy.1)
    rcases hcase with (h | h) | (h | h)
    · exact Or.inl ⟨by simp [h], trivial⟩
    · exact Or.inl ⟨by simp [h], trivial⟩
    · exact Or.inr ⟨trivial, by simp [h]⟩
    · exact Or.inr ⟨trivial, by simp [h]⟩
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  constructor
  · have h : (MeasureTheory.volume : Measure ℝ) ({a, b} : Set ℝ) = 0 := by
      rw [show ({a, b} : Set ℝ) = {a} ∪ {b} from rfl, measure_union_null_iff]
      exact ⟨measure_singleton a, measure_singleton b⟩
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, h]; simp
  · have h : (MeasureTheory.volume : Measure ℝ) ({c, d} : Set ℝ) = 0 := by
      rw [show ({c, d} : Set ℝ) = {c} ∪ {d} from rfl, measure_union_null_iff]
      exact ⟨measure_singleton c, measure_singleton d⟩
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, h]; simp

theorem aemeasurable_deriv_slice_of_contDiffOn {a b c d : ℝ} {u w : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hw : ContinuousOn (Function.uncurry w) (Set.Icc a b ×ˢ Set.Icc c d)) :
    AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  classical
  set S : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo c d with hS
  set T : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hT
  have hSopen : IsOpen S := by rw [hS]; exact isOpen_Ioo.prod isOpen_Ioo
  have hST : S ⊆ T := by
    rw [hS, hT]; exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  -- On the open rectangle the slice derivative is the continuous Fréchet derivative.
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p) S :=
    hsm.continuousOn_fderiv_of_isOpen hSopen le_rfl
  have hev : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p (1, 0)) S :=
    hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) S)
  have hwS : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) S := hw.mono hST
  have hreal : ContinuousOn (fun p : ℝ × ℝ =>
      (fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2) S :=
    (hev.pow 2).mul (hwS.pow 2)
  have hGcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2)) S :=
    ENNReal.continuous_ofReal.comp_continuousOn hreal
  have hAeS : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict S) := hGcont.aemeasurable hSopen.measurableSet
  -- On `S` the two integrands agree, by the identification of the slice derivative.
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal
      ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      =ᵐ[MeasureTheory.volume.restrict S] (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2)) := by
    filter_upwards [self_mem_ae_restrict hSopen.measurableSet] with p hp
    have hdiff : DifferentiableAt ℝ (Function.uncurry u) p :=
      (hsm.contDiffAt (hSopen.mem_nhds hp)).differentiableAt (by norm_num)
    have hkey : deriv (fun z' => u z' p.2) p.1
        = fderiv ℝ (Function.uncurry u) p (1, 0) := by
      have h1 := Work.Spaces.pz_eq_fderiv (G := u) hdiff
      simpa only [Work.Spaces.pz] using h1
    rw [hkey]
  -- The closed rectangle only differs from the open one on a null set.
  have hle : MeasureTheory.volume.restrict T = MeasureTheory.volume.restrict S := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    exact ⟨volume_diff_box_Icc_Ioo a b c d,
      by rw [Set.sdiff_eq_empty.mpr hST, measure_empty]⟩
  rw [hle]
  exact hAeS.congr hae.symm

end Work.FTS.StrongEps.LocUnif
