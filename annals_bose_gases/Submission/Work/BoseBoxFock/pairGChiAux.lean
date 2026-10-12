import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGFibre
import Submission.Work.BoseBoxFock.pairRowDirChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGChiAux` — the χ-weighted Dirichlet assembly of the `pairG` fibres

`FINDING_PotPairRows_exists.md` §11 records the obstruction of the plain D2 estimate: the row
pairing's Dirichlet energy `pairEnergy ℓ G` is **`χ_ℓ`-weighted in its first variable**,

    pairEnergy ℓ G = ∫_{box}∫_{box} ( Σ_j‖∂_j(χ_ℓ(w)·G w y)‖² + ℓ⁻²‖χ_ℓ(w)·G w y‖² ) ,

so it vanishes on fibres supported in the corners of the box (where `χ_ℓ = 0`), whereas the bound
`pairG_dir_leB` routes it through the **unweighted** state content `pinDir`.  The state content that
the row can actually see is `pinDirChi` (`pairRowDirChi`), and the transport is the pointwise product
rule

    ∂_j(χ·G) = (∂_jχ)·G + χ·∂_jG ,   ‖∂_j(χ·G)‖² ≤ 2‖χ‖²·‖∂_jG‖² + 2‖G‖²·‖∂_jχ‖² ,

in which the *Dirichlet* term keeps the full weight `‖χ_ℓ(w)‖²` (only the boundary term is estimated
by `Kc ⊇ ‖χ_ℓ‖²`).  Integrating, the pair energy is bounded by

    (2·Kg + ℓ⁻²·Kc)·∫∫‖G‖² + 2·∫∫ χ_ℓ(w)²·Σ_j‖∂_jG‖² ,

i.e. by the **mass** and the **χ-weighted Dirichlet content**, with constant `2` on the latter.

This module contains

* `chiS_sq` — `‖χ_ℓ w‖² = chiScale ℓ w ^ 2` (the bridge between the complexified window and the real
  one that the hypotheses of `pairG_dir_leB_chi` are stated with);
* `LHSIntegrand_le_chi` — the pointwise product-rule bound with the weight kept;
* `pairEnergy_le_of_box_bounds_chi` — the assembly at fixed mass/Dirichlet budgets `A`, `B`;
* `pairEnergy_le_of_integral_bounds_chi` — the generic form with pointwise dominants `P`, `Q`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **The bridge between the complexified window and the real one**: `‖χ_ℓ w‖² = chiScale ℓ w ²`. -/
theorem chiS_sq (ℓ : ℝ) (w : E3) :
    ‖chiS ℓ w‖ ^ 2 = (Submission.BoseGases.chiScale ℓ w) ^ 2 := by
  rw [chiS_eq, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- **The pointwise product-rule bound with the weight kept**: the windowed derivative keeps the
factor `‖χ_ℓ w‖²` in front of the Dirichlet sum, while the boundary term `(∂_jχ_ℓ)·G` is estimated
by `Kc ⊇ ‖χ_ℓ‖²`. -/
theorem LHSIntegrand_le_chi {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ} {Kg Kc : ℝ} {w y : E3}
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc)
    (hder : DifferentiableAt ℝ (fun w' => G w' y) w) :
    (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ w * G w y‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G w y‖ ^ 2 + 2 * ‖chiS ℓ w‖ ^ 2 * ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  have hchi : DifferentiableAt ℝ (chiS ℓ) w := (differentiable_chiS ℓ).differentiableAt
  have hper : ∀ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ 2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
          + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2 := by
    intro j
    have hd : HasFDerivAt (fun w' => chiS ℓ w' * G w' y)
        ((chiS ℓ w) • fderiv ℝ (fun w' => G w' y) w
          + (G w y) • fderiv ℝ (chiS ℓ) w) w :=
      hchi.hasFDerivAt.mul hder.hasFDerivAt
    have hval : fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))
        = chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
          + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ)) := by
      rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hval]
    have h1 : ‖chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
          + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖
          + ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ :=
      (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    have h2 : (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖
          + ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        ≤ 2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
              (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
          + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
              (EuclideanSpace.single j (1 : ℝ))‖) ^ 2 := by
      nlinarith [sq_nonneg (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
              (EuclideanSpace.single j (1 : ℝ))‖
            - ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hS : (0 : ℝ) ≤ ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have h2 : (∑ j : Fin 3,
      (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2))
      = 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * Kg * ‖G w y‖ ^ 2 := by
    have h1 : (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        ≤ ∑ j : Fin 3, (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
              + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    rw [h2] at h1
    have h4 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ 2 * Kg * ‖G w y‖ ^ 2 := by
      have h5 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ 2 * ‖G w y‖ ^ 2 * Kg :=
        mul_le_mul_of_nonneg_left (hKg w) (by positivity)
      linarith [h5]
    linarith [h1, h4]
  have hlast : (ℓ ^ 2)⁻¹ * ‖chiS ℓ w * G w y‖ ^ 2 ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    have h3 : (0 : ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
    calc (ℓ ^ 2)⁻¹ * (‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2)
        = (ℓ ^ 2)⁻¹ * ‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2 := by ring
      _ ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hKc w) h3
  have hsum' : (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * Kg * ‖G w y‖ ^ 2 := hsum
  linarith [hsum', hlast]

/-- **The χ-weighted assembly lemma.**  If the fibre `G` has box-squared mass `A` and χ-weighted
Dirichlet content `B`, then

    pairEnergy ℓ G ≤ (2·Kg + ℓ⁻²·Kc)·A + 2·B .

The point of the χ-weight is that the second summand is `2·∫∫ χ_ℓ(w)²·Σ_j‖∂_jG‖²` (and *not*
`2·Kc·∫∫Σ_j‖∂_jG‖²`), so the corners of the box (where `χ_ℓ` vanishes) are free. -/
theorem pairEnergy_le_of_box_bounds_chi {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ} {A B Kg Kc : ℝ}
    (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc)
    (hIntLHS : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ))
    (hIntG : IntegrableOn (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ))
    (hIntWQ : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) (boxL ℓ ×ˢ boxL ℓ))
    (hderiv : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)),
        DifferentiableAt ℝ (fun w' => G w' z.2) z.1)
    (hmass : ∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2 ≤ A)
    (hdirW : ∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤ B) :
    L1Tails.pairEnergy ℓ G ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * B := by
  set F : E3 × E3 → ℝ := fun z => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2 with hFdef
  set H : E3 × E3 → ℝ := fun z => (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
      + 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) with hHdef
  have hPt : ∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => G w' z.2) z.1 → F z ≤ H z := by
    rintro ⟨w, y⟩ hz
    have h1 := LHSIntegrand_le_chi hℓ hKg hKc hz
    have h2 : 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = 2 * (‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := by
      ring
    rw [hFdef, hHdef]
    linarith [h1]
  have hAG : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)), F z ≤ H z :=
    hderiv.mono fun z hz => hPt z hz
  have hF0 : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)), 0 ≤ F z :=
    Filter.Eventually.of_forall fun z => by
      rw [hFdef]
      have h3 : (0 : ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
      positivity
  have hGint : Integrable (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2)
      (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := hIntG
  have hWQint : Integrable (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := hIntWQ
  have hHint : Integrable H (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := by
    rw [hHdef]
    exact (hGint.const_mul _).add (hWQint.const_mul 2)
  have hmono : ∫ z, F z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ))
      ≤ ∫ z, H z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)) :=
    integral_mono_of_nonneg hF0 hHint hAG
  have hHval : (∫ z in boxL ℓ ×ˢ boxL ℓ, H z)
      = (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2)
        + 2 * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' z.2) z.1
              (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := by
    show (∫ z, H z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ))) = _
    rw [show H = (fun z : E3 × E3 => (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
        + 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3, ‖fderiv ℝ (fun w' => G w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2))) from hHdef]
    rw [integral_add (hGint.const_mul _) (hWQint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hlin' : (∫ z in boxL ℓ ×ˢ boxL ℓ, F z) = L1Tails.pairEnergy ℓ G := by
    rw [show (∫ z in boxL ℓ ×ˢ boxL ℓ, F z)
        = ∫ z in boxL ℓ ×ˢ boxL ℓ, F z ∂(volume.prod volume) from rfl]
    rw [MeasureTheory.setIntegral_prod F hIntLHS]
    unfold L1Tails.pairEnergy
    rw [hFdef]
    rfl
  have hcoef1 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc := by positivity
  have hfinal : ∫ z in boxL ℓ ×ˢ boxL ℓ, F z
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * B := by
    calc ∫ z in boxL ℓ ×ˢ boxL ℓ, F z
        ≤ ∫ z in boxL ℓ ×ˢ boxL ℓ, H z := hmono
      _ = (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2)
          + 2 * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
              ‖fderiv ℝ (fun w' => G w' z.2) z.1
                (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := hHval
      _ ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * B :=
          add_le_add (mul_le_mul_of_nonneg_left hmass hcoef1)
            (mul_le_mul_of_nonneg_left hdirW (by norm_num))
  rw [← hlin']
  exact hfinal

/-- **Generic χ-weighted assembly**: if the fibre `G` is pointwise dominated by `P` in mass and by
`Q` in its Dirichlet sum, and the *χ-weighted* integral of `Q` is at most `B`, then the pair energy
is at most `C·(A + B)`. -/
theorem pairEnergy_le_of_integral_bounds_chi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : E3 → E3 → ℂ} {P Q : E3 × E3 → ℝ} {A B : ℝ},
      0 ≤ A → 0 ≤ B → (∀ z, 0 ≤ P z) → (∀ z, 0 ≤ Q z) →
      (∀ z : E3 × E3, ‖G z.1 z.2‖ ^ 2 ≤ P z) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Q z) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => G w' z.2) z.1) →
      Continuous (Function.uncurry G) →
      IntegrableOn P (boxL ℓ ×ˢ boxL ℓ) →
      IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * Q z) (boxL ℓ ×ˢ boxL ℓ) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, P z) ≤ A →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z) ≤ B →
      L1Tails.pairEnergy ℓ G ≤ C * (A + B) := by
  obtain ⟨Kg, hKg0, hKg⟩ := exists_chiS_grad_bound ℓ hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2,
    le_max_of_le_left (add_nonneg (by linarith) (by positivity)), ?_⟩
  intro G P Q A B hA0 hB0 hP0 hQ0 hval hdb hder hcont hPint hWQint hP hQ
  have hc1 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc := add_nonneg (by linarith) (by positivity)
  have hFpt : ∀ z : E3 × E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z + 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) := by
    intro z
    have h1 := LHSIntegrand_le_chi hℓ hKg hKc (hder z)
    have h2 : 2 * ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := by
      ring
    have h3 : 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2))
        ≤ 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdb z) (by positivity)) (by norm_num)
    have h4 : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
        ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z := mul_le_mul_of_nonneg_left (hval z) hc1
    linarith [h1, h3, h4]
  have hWQ0 : ∀ z : E3 × E3, 0 ≤ ‖chiS ℓ z.1‖ ^ 2 * Q z :=
    fun z => mul_nonneg (by positivity) (hQ0 z)
  have hSint : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hWQint ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).aestronglyMeasurable
      · exact (aesm_dirIntegrand hcont).mono_measure Measure.restrict_le_self
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => by positivity))]
      exact mul_le_mul_of_nonneg_left (hdb z) (by positivity)
  have hFpt' : ∀ z : E3 × E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z + 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) := hFpt
  have hFint : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono'
      ((hPint.const_mul (2 * Kg + (ℓ ^ 2)⁻¹ * Kc)).add (hWQint.const_mul 2))
      ((aesm_LHSIntegrand hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hFpt' z
  have hGsqint : IntegrableOn (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hPint
      ((aestronglyMeasurable_fibre hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hval z
  have hmass : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2) ≤ A :=
    (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hPint
      (Eventually.of_forall fun z => hval z)).trans hP
  have hdirW : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) ≤ B :=
    (integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => by positivity)) hWQint
      (Eventually.of_forall fun z =>
        mul_le_mul_of_nonneg_left (hdb z) (by positivity))).trans hQ
  have hmain := pairEnergy_le_of_box_bounds_chi (ℓ := ℓ) hℓ hKg0 hKc0 hA0 hB0 hKg hKc
    hFint hGsqint hSint (Eventually.of_forall fun z => hder z) hmass hdirW
  nlinarith [hmain, hA0, hB0, le_max_left (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2,
    le_max_right (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2]

end Work.BoseBoxFock
