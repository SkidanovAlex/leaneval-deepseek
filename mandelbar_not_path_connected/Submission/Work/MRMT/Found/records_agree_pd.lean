/-
Work.MRMT.Found — well-definedness of the principal solution, in the collision-free
("pd") vocabulary.

`Work.MRMT.Found.records_agree` proves the same statement, but its proof goes through
`Work.MRMT.QC.principal_unique`; here everything is done with the two modules that avoid the
`principal_unique` / `eq_zero_of_beltrami_of_decay` collision:

* `Work.MRMT.Found.principalData_weakDeriv_clean2` supplies, for an admissible `μ`, a function
  `D ∈ L²_loc` which is a weak `∂`-derivative of `φ` and such that `μ D` is a weak
  `∂̄`-derivative of `φ`;
* `Work.MRMT.Found.eq_zero_of_beltrami_pd` is the uniqueness (Liouville) theorem for continuous
  solutions of the Beltrami equation with `O(1/‖z‖)` decay, stated for *weak* Wirtinger
  derivatives.

Applying the second to `h = φ - φ'`, `p = D - D'`, `q = μ D - μ D'` gives `φ = φ'`.  The only
bookkeeping is that the weak `∂̄`-derivative calculus and the closure of `L²_loc` under
differences/multiplication by an a.e. bounded field are stated here (they are used by
`records_agree` in the form `Work.MRMT.QC.IsDbarDeriv.sub` / `Work.MRMT.QC.MemL2LocOn.sub`,
which live in the module we are avoiding).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.WeakDerivClean
import Submission.Work.MRMT.Found.principalData_aux
import Submission.Work.MRMT.Found.beurlingL2_eq_cauchyTransform_dz
import Submission.Work.MRMT.Found.eq_zero_of_beltrami_pd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## The weak `∂̄`-derivative calculus in the collision-free vocabulary -/

/-- Closure of `IsDbarDeriv` under subtraction (the analogue of `IsDzDeriv.sub_pd`, which
`Work.MRMT.Found.principalData_aux` already provides). -/
theorem IsDbarDeriv.sub_pd {f f' g g' : ℂ → ℂ} (h : IsDbarDeriv f g) (h' : IsDbarDeriv f' g') :
    IsDbarDeriv (f - f') (g - g') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1.sub h1', h2.sub h2', fun φ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := h3 φ
  obtain ⟨ha', hb', hc'⟩ := h3' φ
  have e1 : (fun z => (f - f') z * dzbar (φ : ℂ → ℂ) z)
      = fun z => f z * dzbar (φ : ℂ → ℂ) z - f' z * dzbar (φ : ℂ → ℂ) z := by
    funext z; simp only [Pi.sub_apply]; ring
  have e2 : (fun z => (g - g') z * (φ : ℂ → ℂ) z)
      = fun z => g z * (φ : ℂ → ℂ) z - g' z * (φ : ℂ → ℂ) z := by
    funext z; simp only [Pi.sub_apply]; ring
  refine ⟨by rw [e1]; exact ha.sub ha', by rw [e2]; exact hb.sub hb', ?_⟩
  rw [e1, e2, integral_sub ha ha', integral_sub hb hb', hc, hc']
  ring

/-! ## Closure properties of `L²_loc` -/

/-- `L²_loc` is closed under differences. -/
theorem memL2Loc_sub_pd {f g : ℂ → ℂ} (hf : MemL2Loc f) (hg : MemL2Loc g)
    (hfm : AEStronglyMeasurable f (volume : Measure ℂ))
    (hgm : AEStronglyMeasurable g (volume : Measure ℂ)) :
    MemL2Loc (f - g) := by
  intro K hK
  have h1 : Integrable (fun z => ‖f z‖ ^ 2)
      ((volume : Measure ℂ).restrict (K ∩ Set.univ)) := hf K hK
  have h2 : Integrable (fun z => ‖g z‖ ^ 2)
      ((volume : Measure ℂ).restrict (K ∩ Set.univ)) := hg K hK
  rw [Set.inter_univ] at h1 h2 ⊢
  have hdom : Integrable (fun z => 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2)
      ((volume : Measure ℂ).restrict K) :=
    (h1.const_mul 2).add (h2.const_mul 2)
  refine (hdom.mono' ?_ ?_)
  · exact (((hfm.mono_measure Measure.restrict_le_self).sub
      (hgm.mono_measure Measure.restrict_le_self)).norm.pow 2)
  · filter_upwards with z
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖(f - g) z‖ ^ 2 = ‖f z - g z‖ ^ 2 := rfl
      _ ≤ (‖f z‖ + ‖g z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ 2 * (‖f z‖ ^ 2 + ‖g z‖ ^ 2) := add_sq_le
      _ = 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by ring

/-- Multiplication by an a.e. bounded, a.e. strongly measurable field preserves `L²_loc`. -/
theorem memL2Loc_mul_pd {μ f : ℂ → ℂ} {k : ℝ} (hf : MemL2Loc f)
    (hμm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (hfm : AEStronglyMeasurable f (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    MemL2Loc (fun z => μ z * f z) := by
  intro K hK
  have h1 : Integrable (fun z => ‖f z‖ ^ 2)
      ((volume : Measure ℂ).restrict (K ∩ Set.univ)) := hf K hK
  rw [Set.inter_univ] at h1 ⊢
  have hdom : Integrable (fun z => (max k 0) ^ 2 * ‖f z‖ ^ 2)
      ((volume : Measure ℂ).restrict K) :=
    h1.const_mul ((max k 0) ^ 2)
  refine (hdom.mono' ?_ ?_)
  · exact (((hμm.mono_measure Measure.restrict_le_self).mul
      (hfm.mono_measure Measure.restrict_le_self)).norm.pow 2)
  · filter_upwards [Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) hb] with z hz
    rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hz.trans (le_max_left k 0)) 2

/-! ## Two records agree -/

/-- **Well-definedness of the principal solution.**  Any two records of the principal solution
for the same admissible Beltrami coefficient have the same homeomorphism. -/
theorem records_agree_pd {μ : ℂ → ℂ} (hμ : Admissible μ) (d d' : PrincipalData μ) :
    (d.φ : ℂ → ℂ) = (d'.φ : ℂ → ℂ) := by
  obtain ⟨D₁, hD₁loc, hD₁dz, hD₁dzbar⟩ := principalData_weakDeriv_clean2 hμ d
  obtain ⟨D₂, hD₂loc, hD₂dz, hD₂dzbar⟩ := principalData_weakDeriv_clean2 hμ d'
  have hD₁ea : AEStronglyMeasurable D₁ (volume : Measure ℂ) := hD₁dz.2.1.aestronglyMeasurable
  have hD₂ea : AEStronglyMeasurable D₂ (volume : Measure ℂ) := hD₂dz.2.1.aestronglyMeasurable
  -- weak derivatives of the difference
  have hp : IsDzDeriv (fun z => (d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z) (D₁ - D₂) :=
    IsDzDeriv.sub_pd hD₁dz hD₂dz
  have hq : IsDbarDeriv (fun z => (d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z)
      ((fun z => μ z * D₁ z) - (fun z => μ z * D₂ z)) :=
    IsDbarDeriv.sub_pd hD₁dzbar hD₂dzbar
  -- local square integrability
  have hpL : MemL2Loc (D₁ - D₂) := memL2Loc_sub_pd hD₁loc hD₂loc hD₁ea hD₂ea
  obtain ⟨kb, hkb, hbb⟩ := hμ.bound
  have hqL : MemL2Loc ((fun z => μ z * D₁ z) - (fun z => μ z * D₂ z)) := by
    have heq : ((fun z => μ z * D₁ z) - (fun z => μ z * D₂ z))
        = fun z => μ z * (D₁ - D₂) z := by
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact memL2Loc_mul_pd hpL hμ.meas (hD₁ea.sub hD₂ea) hbb
  have hrel : ∀ᵐ z ∂(volume : Measure ℂ),
      ((fun z => μ z * D₁ z) - (fun z => μ z * D₂ z)) z = μ z * (D₁ - D₂) z :=
    Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring
  -- the decay of the difference
  have hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖(fun z => (d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z) z‖ ≤ C / ‖z‖ := by
    refine ⟨max d.C 0 + max d'.C 0, max (max d.R d'.R) 1, by positivity, fun z hz => ?_⟩
    have hzR : d.R ≤ ‖z‖ := (le_max_left d.R d'.R).trans ((le_max_left _ _).trans hz)
    have hzR' : d'.R ≤ ‖z‖ := (le_max_right d.R d'.R).trans ((le_max_left _ _).trans hz)
    have hz1 : 1 ≤ ‖z‖ := (le_max_right (max d.R d'.R) 1).trans hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    calc ‖(d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z‖
        = ‖((d.φ : ℂ → ℂ) z - z) - ((d'.φ : ℂ → ℂ) z - z)‖ := by ring_nf
      _ ≤ ‖(d.φ : ℂ → ℂ) z - z‖ + ‖(d'.φ : ℂ → ℂ) z - z‖ := norm_sub_le _ _
      _ ≤ d.C / ‖z‖ + d'.C / ‖z‖ := add_le_add (d.decay z hzR) (d'.decay z hzR')
      _ ≤ max d.C 0 / ‖z‖ + max d'.C 0 / ‖z‖ :=
          add_le_add (div_le_div_of_nonneg_right (le_max_left _ _) hzpos.le)
            (div_le_div_of_nonneg_right (le_max_left _ _) hzpos.le)
      _ = (max d.C 0 + max d'.C 0) / ‖z‖ := by ring
  -- apply the uniqueness theorem
  have hzero := eq_zero_of_beltrami_pd
    (h := fun z => (d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z)
    (p := D₁ - D₂) (q := (fun z => μ z * D₁ z) - (fun z => μ z * D₂ z))
    (μ := μ) (k := kb) ((d.φ).continuous.sub (d'.φ).continuous) hp hq hpL hqL hkb hbb hrel hdec
  funext z
  have h1 : (d.φ : ℂ → ℂ) z - (d'.φ : ℂ → ℂ) z = 0 := congrFun hzero z
  exact sub_eq_zero.mp h1

end Work.MRMT.Found
