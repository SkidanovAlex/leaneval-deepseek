import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSmoothAux
import Submission.Work.BoseBoxFock.imagesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesFibre` — the position-space fibre of the images words

The two words of the target (`q1WordK`, `q4WordK`) at the `χχ`-images kernel `imgKernel ℓ W` can be
written as **`boxL × boxL`-pairings of the kernel against a fibre**, exactly in the shape consumed
by the corpus's PROVED images-pairing bound
`Work.BoseBoxFock.L1Tails.chiChiImages_pairing_boxSmooth` — which needs only the fibre's
*smoothness on the box* and its **Dirichlet energy**, and never a supremum of the weight `W`.
(The latter is what makes the bound applicable at the honest weights `W1fun`/`W1omegaFun`, which are
`L¹` but neither bounded nor `L²` — `FINDING_PotPairRows_exists.md` §9.1/§9.2.)

For a pair `p` and functions `F₁ G : X n → ℝ`, the fibre is

    `imgFibre ℓ p F₁ G u v = ℓ⁻³∫_{x'}∫_{s∈boxL} F₁ (insertCoord2 p s v x')·G (insertCoord2 p u v x')`

so that, with `F₁ = aQ ℓ p.2 Φ`, `G = aP ℓ p.2 (aQ ℓ p.1 Φ)` (resp. `F₁ = aP ℓ p.2 Φ`,
`G = aQ ℓ p.2 (aQ ℓ p.1 Φ)`) the pair term of `q1WordK` (resp. `q4WordK`) equals
`∫_{boxL}∫_{boxL} imgKernel ℓ W u v · (that fibre)`; the peel identity is
`Work.BoseBoxFock.imgFibre_peel`.

Everything here is definitional; the three analytic properties of the fibre (the peel identity, its
`BoxSmooth`-ness, and its Dirichlet bound) are delegated separately.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **The position-space fibre of the images words**: freeze the two slots `p.1`, `p.2` of the
configuration at `u`, `v`, average the `p.1`-slot over `boxL` (that is the `aP ℓ p.1`-mean), and
integrate out the remaining coordinates. -/
noncomputable def imgFibre {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Xn n → ℝ) (u v : E3) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) *
    ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ∫ s in boxL ℓ, F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x')

/-- The `L²` content of `F` on the box. -/
noncomputable def imgFibreN {n : ℕ} (ℓ : ℝ) (F : Xn n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, (F x) ^ 2

/-- The `p.1`-slot Dirichlet content of `F` on the box. -/
noncomputable def imgFibreD₁ {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2

/-- Both-slot Dirichlet content of `F` on the box. -/
noncomputable def imgFibreD₂ {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    ∑ j : Fin 3, ((fderiv ℝ F x (slotDirVec p.1 j)) ^ 2
      + (fderiv ℝ F x (slotDirVec p.2 j)) ^ 2)

/-- The complex-valued form of the fibre (the shape consumed by `BoxSmooth`/`pairEnergy`). -/
noncomputable def imgFibreC {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Xn n → ℝ) (u v : E3) : ℂ :=
  ((imgFibre ℓ p F₁ G u v : ℝ) : ℂ)

/-- **The mirror fibre** (the `p.2`-slot peel): the average is over the `p.2`-slot.  Needed for the
one `q4` piece whose free factor is not `p.2`-independent (`F₁ = aP ℓ p.1 Φ` is `p.1`-independent,
which is what makes its Dirichlet bound true). -/
noncomputable def imgFibre₂ {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Xn n → ℝ) (u v : E3) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) *
    ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x')

/-- The complex-valued form of the mirror fibre. -/
noncomputable def imgFibre₂C {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Xn n → ℝ) (u v : E3) : ℂ :=
  ((imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ)

/-! ## The *weighted* Dirichlet content

The `w`-derivative of `pairEnergy` is weighted by `χ_ℓ(w)`; consequently the derivation of the
fibre-energy bound (Cauchy–Schwarz in the peeled slot) produces the **`χ`-weighted** Dirichlet
content of the free factor, not the unweighted one.  This is the same phenomenon as in
`pairRowDirChi`: the unweighted `pinDir` is *not* controlled by `IsLowB` (a state concentrated in
a corner of the box has `pinDir/normB ≍ 1/δ² → ∞`), while the `χ`-weighted content is
(`pinDirChiExp`).  Hence the fibre-energy lemmas are stated with `imgFibreDχ`. -/

/-- The `p.1`-slot **`χ`-weighted** Dirichlet content of `F` on the box. -/
noncomputable def imgFibreDχ {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2
      * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2

/-- `imgFibreDχ` is nonnegative. -/
theorem imgFibreDχ_nonneg {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (F : Xn n → ℝ) :
    0 ≤ imgFibreDχ ℓ p F :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- `imgFibreN` is nonnegative. -/
theorem imgFibreN_nonneg {n : ℕ} (ℓ : ℝ) (F : Xn n → ℝ) : 0 ≤ imgFibreN ℓ F :=
  integral_nonneg fun x => sq_nonneg _

end Work.BoseBoxFock
