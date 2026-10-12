import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open MeasureTheory

namespace Work.BoseBoxFock.L1Tails

/-- Smoothness and compact support of the folded kernel `foldH H u = ∫_y H (u+y) y dy` for a
smooth kernel `H` supported in `boxL ℓ × boxL ℓ` (the input needed to expand the periodisation
`latPerC ℓ (foldH H)` in an absolutely convergent Fourier series).
Route: since `H (u+y) y = 0` for `y ∉ boxL ℓ` (`hHs`), the fold is a parameter integral over the
*fixed* compact `y`-set `boxL ℓ`, and all derivatives are dominated by the sup of the corresponding
derivative of `H` on the compact set `(closedBall u₀ 1 + boxL ℓ) × boxL ℓ`; differentiate under the
integral sign repeatedly (`hasFDerivAt_integral_of_dominated_loc_of_lip`, or with a smooth cutoff
`ψ ≡ 1` on `boxL ℓ` inserted in `y` to make the integrand supported in the fixed `supp ψ`), obtaining
`∀ n : ℕ, ContDiff ℝ n (foldH H)` and then `ContDiff ℝ ⊤ (foldH H)` (which unfolds as
`∀ m : ℕ, m ≤ ⊤ → ContDiff ℝ m (foldH H)`; the `⊤`-assembly step is `fun m _ => h m`).  Note the
differentiated integrands also vanish for `y ∉ boxL ℓ`.  `HasCompactSupport` follows from
`Function.support (foldH H) ⊆ boxL ℓ - boxL ℓ` (if `H (u+y) y ≠ 0` then `u + y ∈ boxL ℓ` and
`y ∈ boxL ℓ`) and the compactness of `boxL ℓ`. -/
theorem foldH_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.L1Tails.foldH H)
      ∧ HasCompactSupport (Work.BoseBoxFock.L1Tails.foldH H) := by
  classical
  -- the fixed compact `y`-set on which everything lives
  set K : Set (EuclideanSpace ℝ (Fin 3)) := Work.BoseK15.corpusBox.boxL ℓ with hKdef
  have hKc : IsCompact K := Work.BoseK15.corpusBox.boxL_compact ℓ
  -- joint smoothness of the integrand `(u, y) ↦ H (u + y) y`
  have hφ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => (z.1 + z.2, z.2)) :=
    (contDiff_fst.add contDiff_snd).prodMk contDiff_snd
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun u y : EuclideanSpace ℝ (Fin 3) => H (u + y) y)) := by
    have h := hH.comp hφ
    exact h
  constructor
  · -- smoothness: the fold is the parametric integral over the *fixed* compact set `K`, so
    -- smoothness of parametric integrals over a compact set applies degree by degree
    rw [contDiff_iff_forall_nat_le]
    intro m _
    have hset := Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_aux
      (P := EuclideanSpace ℝ (Fin 3)) hKc m ℂ
      (fun u y : EuclideanSpace ℝ (Fin 3) => H (u + y) y)
      (hFsmooth.of_le (by exact_mod_cast le_top))
    -- the `K`-restricted integral is the full integral, since the integrand vanishes off `K`
    have hfold : (fun u : EuclideanSpace ℝ (Fin 3) =>
          ∫ y in K, (fun u y : EuclideanSpace ℝ (Fin 3) => H (u + y) y) u y) = foldH H := by
      funext u
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        by_contra hcon
        exact hy (hHs (u + y) y hcon).2)
    rw [hfold] at hset
    simpa using hset
  · -- compact support: `u ∈ support (foldH H)` forces `u = (u + y) + (-1) • y` with both
    -- `u + y` and `y` in `K`, i.e. `u ∈ K + (-1) • K`, which is compact
    have hsub : Function.support (foldH H) ⊆ K + ((-1 : ℝ) • K) := by
      intro u hu
      by_contra hmem
      refine hu ?_
      have hzero : (fun y : EuclideanSpace ℝ (Fin 3) => H (u + y) y) = fun _ => (0 : ℂ) := by
        funext y
        by_contra hcon
        exact hmem ⟨u + y, (hHs (u + y) y hcon).1, (-1 : ℝ) • y,
          ⟨y, (hHs (u + y) y hcon).2, rfl⟩, by rw [neg_one_smul]; abel⟩
      simp only [foldH]
      rw [hzero]
      simp
    exact HasCompactSupport.of_support_subset_isCompact
      (hKc.add (IsCompact.smul (-1 : ℝ) hKc)) hsub

end Work.BoseBoxFock.L1Tails
