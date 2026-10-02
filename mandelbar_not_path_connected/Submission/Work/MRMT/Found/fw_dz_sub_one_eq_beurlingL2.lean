/-
Work.MRMT.Found — **`∂F − 1 = S(∂̄F)` for a `C¹` map with `1/‖z‖` normalisation**.

For a `C¹` map `F : ℂ → ℂ` whose `∂̄`-derivative is compactly supported and square integrable
and which satisfies the principal normalisation `F z = z + O(1/‖z‖)` at infinity, the Wirtinger
derivative `∂F` differs from the constant `1` by the Beurling transform `S(∂̄F)` of `∂̄F`, almost
everywhere.

## Route of the proof

* `Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar` gives `F z - z = C(∂̄F)` a.e., i.e.
  `F − id` agrees a.e. with the Cauchy transform of `∂̄F`;
* `F` is `C¹`, so its distributional `∂`-derivative is the pointwise one
  (`Work.MRMT.Weyl.isDzDeriv_dz`), and the distributional `∂`-derivative of `id` is the constant
  `1` (`Work.MRMT.Sobolev.isDzDeriv_id`); subtracting
  (`Work.MRMT.QC.IsDzDeriv.sub`) gives `∂(F − id) = ∂F − 1` distributionally;
* `isDzDeriv_cauchyTransform_eq_beurlingL2` gives `∂(C(∂̄F)) = S(∂̄F)` distributionally
  (compact support and `L²` of `∂̄F` are the hypotheses `hs` and `hLp`);
* the distributional `∂`-relation is insensitive to changing the representing function on a null
  set (`Work.MRMT.Found.isDzDeriv_congr_ae_lhs`), so `S(∂̄F)` is a weak `∂`-derivative of `F − id`
  as well;
* uniqueness of the weak `∂`-derivative (`Work.MRMT.QC.is_dz_deriv_unique`) identifies
  `∂F − 1` with `S(∂̄F)` a.e.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2
import Submission.Work.MRMT.QC.principal_unique
import Submission.Work.MRMT.Sobolev.isDzDeriv_id_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-- The distributional `∂`-relation only depends on the *first* function up to a.e. equality
(the companion of `Work.MRMT.Found.isDzDeriv_congr_ae`, which handles the second one): the
integrals defining `Work.MRMT.IsDzDeriv` are unchanged when `f` is replaced by an a.e. equal
function `f'`, and being locally integrable is likewise an a.e. notion. -/
theorem isDzDeriv_congr_ae_lhs {f f' g : ℂ → ℂ} (h : Work.MRMT.IsDzDeriv f g)
    (hff' : f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] f') :
    Work.MRMT.IsDzDeriv f' g := by
  obtain ⟨hf, hg, hm⟩ := h
  refine ⟨hf.congr hff', hg, fun φ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hm φ
  have hdeg : (fun z => f z * Work.MRMT.dz (φ : ℂ → ℂ) z) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)]
      (fun z => f' z * Work.MRMT.dz (φ : ℂ → ℂ) z) :=
    hff'.mono (fun z hz => by simp only [hz])
  refine ⟨h1.congr hdeg, h2, ?_⟩
  exact (integral_congr_ae hdeg).symm.trans h3

theorem fw_dz_sub_one_eq_beurlingL2 {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖)
    (hs : HasCompactSupport (fun z => Work.MRMT.dzbar F z))
    (hLp : MeasureTheory.MemLp (fun z => Work.MRMT.dzbar F z) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    (fun z => Work.MRMT.dz F z - 1) =ᵐ[MeasureTheory.volume]
      (((Work.MRMT.beurlingL2
          (hLp.toLp (fun z => Work.MRMT.dzbar F z)) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ)) := by
  -- `F` is `C¹`, so its distributional `∂`-derivative is the pointwise one
  have hFdb : Work.MRMT.IsDzDeriv F (fun z => Work.MRMT.dz F z) :=
    Work.MRMT.Weyl.isDzDeriv_dz hF (by norm_num)
  -- the distributional `∂`-derivative of the identity is the constant `1`
  have hid : Work.MRMT.IsDzDeriv (fun z : ℂ => z) (fun _ => (1 : ℂ)) :=
    Work.MRMT.Sobolev.isDzDeriv_id
  -- hence `∂(F − id) = ∂F − 1` distributionally
  have hsub : Work.MRMT.IsDzDeriv (fun z => F z - z) (fun z => Work.MRMT.dz F z - 1) :=
    Work.MRMT.QC.IsDzDeriv.sub hFdb hid
  -- `F − id` agrees a.e. with the Cauchy transform of `∂̄F`
  have hct : (fun z => F z - z) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)]
      Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) :=
    Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar hF hs hdec
  -- `∂(C(∂̄F)) = S(∂̄F)` distributionally
  have hcts : Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w))
      (((Work.MRMT.beurlingL2 (hLp.toLp (fun z => Work.MRMT.dzbar F z))) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) :=
    Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2 hLp hs
  -- so `S(∂̄F)` is also a weak `∂`-derivative of `F − id`
  have hcts' : Work.MRMT.IsDzDeriv (fun z => F z - z)
      (((Work.MRMT.beurlingL2 (hLp.toLp (fun z => Work.MRMT.dzbar F z))) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) :=
    isDzDeriv_congr_ae_lhs hcts hct.symm
  -- uniqueness of the weak `∂`-derivative finishes
  exact Work.MRMT.QC.is_dz_deriv_unique hsub hcts'

end Work.MRMT.Found
