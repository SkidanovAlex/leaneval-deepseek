import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imagesFibre
import Submission.Work.BoseBoxFock.pairGc23Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreEnergyDefs` — the intermediate densities of the fibre-energy bound

The target `Work.BoseBoxFock.imgFibreEnergyLe` bounds the χ-weighted Dirichlet energy
`pairEnergy ℓ (imgFibreC ℓ p F₁ G)` of the position-space fibre

    imgFibre ℓ p F₁ G u v = ℓ⁻³ ∫_{x'}∫_{s∈boxL} F₁(insertCoord2 p s v x')·G(insertCoord2 p u v x')

by the product of the two states' box contents.  The proof is two Cauchy–Schwarz inequalities in
the `(x', s)`-variables, which produce the two *densities* consumed by
`Work.BoseBoxFock.pairEnergy_le_of_integral_bounds_chi_param`:

* `imgFibreMF ℓ p F v = ∫_{x'}∫_{s∈boxL} F(insertCoord2 p s v x')²`
  (the `u`-free factor; the `p.1`-slot carries the *dummy* `s`, the `p.2`-slot the frozen `v`),
* `imgFibreMG ℓ p G u = ∫_{x'}∫_{s∈boxL} G(insertCoord2 p u s x')²`
  (the `v`-free factor; by hypothesis `G` is invariant under `p.2`-updates, so the `p.2`-slot may be
  filled by the dummy `s`),
* `imgFibreDG ℓ p G u = ∫_{x'}∫_{s∈boxL} Σ_j (∂_{p.1,j}G)(insertCoord2 p u s x')²`
  (the χ-weighted Dirichlet density of `G`; again the `p.2`-slot carries the dummy `s`).

The two identities that make these the right objects are *measure preserving insertions* along
`splitEquiv` (`Submission/Work/BoseBoxFock/blockTwo3_aux.lean`):
`(x', s, v) ↦ insertCoord2 p s v x'` and `(x', u, s) ↦ insertCoord2 p u s x'` are measure
preserving bijections of the triple box onto `abox n ℓ`, whence

    ∫_{v∈boxL} imgFibreMF ℓ p F v = imgFibreN ℓ F ,   ∫_{u∈boxL} χ_ℓ(u)² imgFibreDG ℓ p G u = imgFibreDχ ℓ p G .

Both are delegated (they are pure measure theory), as is the derivative of the fibre.

`sorry`-free (definitions only).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The `u`-free Cauchy–Schwarz factor of the fibre: the `L²`-content of `F` in the two inserted
slots, with the `p.1`-slot averaged over the box and the `p.2`-slot frozen at `v`. -/
noncomputable def imgFibreMF {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F : Xn n → ℝ) (v : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
    (F (insertCoord2 p s v x')) ^ 2

/-- The `v`-free Cauchy–Schwarz factor of the fibre: the `L²`-content of `G` in the two inserted
slots, with the `p.1`-slot frozen at `u` and the `p.2`-slot averaged over the box.  (For a
`p.2`-invariant `G` this is the same as freezing the `p.2`-slot — that is the use hypothesis
`hGind`.) -/
noncomputable def imgFibreMG {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (G : Xn n → ℝ) (u : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
    (G (insertCoord2 p u s x')) ^ 2

/-- The χ-weighted Dirichlet density of `G`: the `p.1`-slot of the inserted configuration carries
the fibre variable `u`, the `p.2`-slot the dummy `s`. -/
noncomputable def imgFibreDG {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (G : Xn n → ℝ) (u : E3) : ℝ :=
  ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
    ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2

/-- `imgFibreMF` is nonnegative. -/
theorem imgFibreMF_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) (v : E3) :
    0 ≤ imgFibreMF ℓ p F v :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- `imgFibreMG` is nonnegative. -/
theorem imgFibreMG_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ) (u : E3) :
    0 ≤ imgFibreMG ℓ p G u :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- `imgFibreDG` is nonnegative. -/
theorem imgFibreDG_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (G : Xn n → ℝ) (u : E3) :
    0 ≤ imgFibreDG ℓ p G u :=
  integral_nonneg fun _ => integral_nonneg fun _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

end Work.BoseBoxFock
