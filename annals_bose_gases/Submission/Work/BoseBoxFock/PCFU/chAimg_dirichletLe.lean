import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dirichletPeel
import Submission.Work.BoseBoxFock.PCFU.taperSlotOne
import Submission.Work.BoseBoxFock.PCFU.windowedDirichlet_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAimg_dirichletLe`

The windowed fibre Dirichlet bound on the box: the Dirichlet energy of the slot-`i` windowed
fibre `w ↦ χ_ℓ(w)·Φ(kcInsN m i (w,r))`, integrated over the `m`-particle box, is bounded by
twice the `χ_ℓ²`-weighted *fibre* Dirichlet energy of `Φ` over the `(m+1)`-particle box plus the
price `2 (M/ℓ)² ∫ Φ²` of the window.

The proof is a two-line assembly of two already-available corpus results:

* `dirichletPeel` — the peel of the slot-`i` fibre out of the `(m+1)`-particle box: the box
  integral of the windowed fibre Dirichlet integrand equals the iterated integral over
  `abox m ℓ ∋ r` and `E3 ∋ w` of the fibre derivative `∂_w (χ_ℓ(w) Φ(kcInsN m i (w,r)))`;
* `windowedDirichlet_le` — the Leibniz/product-rule bound for that same box integrand, which
  splits `∂(χ_ℓ · Φ∘update)` into the `χ_ℓ`-weighted fibre derivative of `Φ` plus the window
  term controlled by `hMd`, and uses `∑_k c_k² ≤ ‖L‖²` for a linear functional on `ℝ³`.

Inserting the hypothesis `hkin` (the weighted fibre Dirichlet energy is at most `Ck`) and
rewriting `(M/ℓ)² = M² (ℓ²)⁻¹` finishes the bound.
-/

namespace Work.BoseBoxFock.PCFU

theorem chAimg_dirichletLe {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin (m + 1)}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {Ck M : ℝ} (hCk : 0 ≤ Ck) (hM : 0 ≤ M)
    (hMd : ∀ (x w : EuclideanSpace ℝ (Fin 3)),
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w| ≤ (M / ℓ) * ‖w‖)
    (hkin : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
            Φ (Function.update x i z)) (x i)
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)) ≤ Ck) :
    (∫ r in Submission.BoseGases.abox m ℓ,
        Work.BoseBoxFock.PCFU.slotDir (fun w : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ w * Φ (Submission.BoseGases.kcInsN m i (w, r)))
      ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)))
      ≤ 2 * Ck + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ *
          ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2 := by
  -- consolidate the double restriction to the box appearing on the left
  rw [MeasureTheory.Measure.restrict_restrict_of_subset (Set.Subset.refl _)]
  -- unfold the fibre Dirichlet energy `slotDir`
  simp only [Work.BoseBoxFock.PCFU.slotDir]
  -- peel the slot-`i` fibre out of the `(m+1)`-particle box
  rw [← Work.BoseBoxFock.PCFU.dirichletPeel (n := m) i hℓ hΦ]
  -- the Leibniz bound for the windowed fibre
  refine le_trans (Work.BoseBoxFock.PCFU.windowedDirichlet_le (n := m + 1) i hℓ hM hMd hΦ) ?_
  have hconv : (M / ℓ) ^ 2 = M ^ 2 * (ℓ ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  rw [hconv]
  linarith [hkin]

end Work.BoseBoxFock.PCFU
