/-
# The `Re τ = -1` mirror of the CKMRV §5 layer continuation: definitions

CKMRV Proposition 4.6 continues the generating function `F₂` from the `Γ(2)`-fundamental domain
`𝒟` to a neighbourhood of its closure.  `Submission/Work/LayerCont/` builds the *left* half of
this, at `Re τ = 1`: the pole `z = τ - 1` of the kernel crosses the contour `z = it` there, and
the deformed objects `layerLowCont`, `layerTruncCont` (together with `layerLowCoinc`, which
handles the removable `S`-branch coincidence `ST⁻¹τ = -1/(τ-1)`) are holomorphic across
`Re τ = 1` and agree with the paper's layer on `{Re τ < 1} ∩ 𝒟`
(`Work.LayerCont.layerTruncContinuation`).

This directory builds the **mirror** at `Re τ = -1`, i.e. the reflected region `U'`.  The
analytic structure is the reflection of the left one through the anti-holomorphic isometry
`ρ : τ ↦ -τ̄` (`τ ↦ 1 + i s₀` becomes `τ ↦ -1 + i s₀`, `T⁻¹τ = τ - 1` becomes `Tτ = τ + 1`,
`S T⁻¹τ = -1/(τ-1)` becomes `S T τ = -1/(τ+1)`) — but the *layer functions themselves* are not
reflection-symmetric, so the construction has to be carried out on the right side:

* the moving pole is now `z = τ + 1` (`Work.Asymptotics.tauAddOne`);
* the contour has to be indented into `Re z > 0` (`Work.Asymptotics.detourRight`), so that the
  removable coincidence `STτ = -1/(τ+1)` (which has `Re < 0` for `Re τ > -1`) is *avoided*;
* the residue picked up by the right detour around the pole `z = τ + 1` is
  `e^{iπr²(τ+1)}` (`Work.LayerCont.Right.resCorrRight`), because the second-variable residue of
  the kernel at the pole `Tτ` is `-1/(2π)`
  (`Work.Residues.hasResidue_Kfun_second` is the `T⁻¹` case `+1/(2π)`; the `T` case follows from
  `Work.Asymptotics.AfunFun_vadd_int_of_jprime_ne` with `n = 1`, giving
  `AfunFun τ (τ+1) = (1/2π)j'(τ+1)` and hence residue `-1/(2π)` after the sign of the cleared
  identity `K·(jτ - jz) = AfunFun`).  Note that this is the residue *value*
  `2πi·Res(kerForm)`; the corrected layer adds `+sinSqC r · resCorrRight r τ`, exactly as in the
  left case, because the right detour sweeps the pole in the counterclockwise sense;
* the agreement with the paper's layer `paperLayer` holds on `{Re τ > -1} ∩ 𝒟`, and the
  capstone `Work.LayerCont.Right.layerRightContinuation` is the mirror of
  `Work.LayerCont.layerTruncContinuation`.

## Main definitions

* `negOnePlusI s₀ hs₀` — the centre `-1 + i s₀` of the ball;
* `rightRect c A ξ z` — the *right* rectangle `[0,ξ] × [c-A,c+A]`;
* `tauAddOne τ = τ + 1`, `tauCoincRight τ = STτ = -1/(τ+1)`;
* `resCorrRight r τ = e^{iπr²(τ+1)}`;
* `layerLowPieceRight`, `layerLowCoincRight`, `layerTruncPieceRight`, `layerTruncContRight`.
-/
import Mathlib
import Submission.Work.LayerCont.TruncDefs
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.AfunFun_vadd_int_of_jprime_ne

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.LayerCont.Right

open UpperHalfPlane MeasureTheory
open scoped Manifold Topology

/-! ## The centre of the ball and the right rectangle -/

/-- The point `-1 + i s₀` of `ℍ`, the centre of the ball on which the layer is continued
across `Re τ = -1` (the reflection of `Work.Asymptotics.onePlusI s₀ hs₀`). -/
def negOnePlusI (s₀ : ℝ) (hs₀ : 0 < s₀) : UpperHalfPlane :=
  ⟨(-1 : ℂ) + (s₀ : ℂ) * Complex.I, by simpa using hs₀⟩

@[simp] lemma negOnePlusI_re (s₀ : ℝ) (hs₀ : 0 < s₀) : (negOnePlusI s₀ hs₀).re = -1 := by
  simp [negOnePlusI]

@[simp] lemma negOnePlusI_im (s₀ : ℝ) (hs₀ : 0 < s₀) : (negOnePlusI s₀ hs₀).im = s₀ := by
  simp [negOnePlusI]

lemma negOnePlusI_coe (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ((negOnePlusI s₀ hs₀ : UpperHalfPlane) : ℂ) = (-1 : ℂ) + (s₀ : ℂ) * Complex.I := rfl

/-- **The right rectangle** `[0,ξ] × [c-A,c+A]`: the mirror of `Work.Asymptotics.leftRect`,
swept by `Work.Asymptotics.detourRight`. -/
def rightRect (c A ξ : ℝ) (z : UpperHalfPlane) : Prop :=
  0 ≤ z.re ∧ z.re ≤ ξ ∧ c - A ≤ z.im ∧ z.im ≤ c + A

/-- The right rectangle as a subset of `ℂ`. -/
def rightRectℂ (c A ξ : ℝ) : Set ℂ :=
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ ξ ∧ c - A ≤ z.im ∧ z.im ≤ c + A}

/-- The open right rectangle `(0,ξ) × (c-A,c+A)` of the complex plane. -/
def openRightRectℂ (c A ξ : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < ξ ∧ c - A < z.im ∧ z.im < c + A}

lemma mem_rightRectℂ {c A ξ : ℝ} {z : ℂ} :
    z ∈ rightRectℂ c A ξ ↔ 0 ≤ z.re ∧ z.re ≤ ξ ∧ c - A ≤ z.im ∧ z.im ≤ c + A := Iff.rfl

lemma mem_openRightRectℂ {c A ξ : ℝ} {z : ℂ} :
    z ∈ openRightRectℂ c A ξ ↔ 0 < z.re ∧ z.re < ξ ∧ c - A < z.im ∧ z.im < c + A := Iff.rfl

lemma rightRect_iff {c A ξ : ℝ} {z : UpperHalfPlane} :
    rightRect c A ξ z ↔ rightRectℂ c A ξ (z : ℂ) := by
  simp only [rightRect, rightRectℂ, Set.mem_ofPred_eq]
  exact Iff.rfl

lemma rightRect_subset_im_pos {c A ξ : ℝ} (hcA : 0 < c - A) {z : ℂ} (hz : z ∈ rightRectℂ c A ξ) :
    0 < z.im := lt_of_lt_of_le hcA hz.2.2.1

lemma openRightRectℂ_subset_rightRectℂ (c A ξ : ℝ) :
    openRightRectℂ c A ξ ⊆ rightRectℂ c A ξ := by
  intro z hz
  simp only [openRightRectℂ, rightRectℂ, Set.mem_ofPred_eq] at hz ⊢
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

lemma isOpen_openRightRectℂ (c A ξ : ℝ) : IsOpen (openRightRectℂ c A ξ) := by
  have h : openRightRectℂ c A ξ = Set.Ioo (0 : ℝ) ξ ×ℂ Set.Ioo (c - A) (c + A) := by
    ext z
    simp only [openRightRectℂ, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
    tauto
  rw [h]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

/-! ## The translate `τ + 1` and the coincidence `ST τ` -/

/-- The point `τ + 1` of `ℍ`, the mirror of `Work.Asymptotics.tauSubOne`.  This is the moving
pole `z = T τ` of the kernel on the right side. -/
abbrev tauAddOne (τ : UpperHalfPlane) : UpperHalfPlane := (1 : ℝ) +ᵥ τ

lemma tauAddOne_coe (τ : UpperHalfPlane) : ((tauAddOne τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
  rw [tauAddOne, UpperHalfPlane.coe_vadd]
  push_cast
  ring

lemma tauAddOne_re (τ : UpperHalfPlane) : (tauAddOne τ).re = τ.re + 1 := by
  have h := congrArg Complex.re (tauAddOne_coe τ)
  simpa [UpperHalfPlane.coe_re] using h

lemma tauAddOne_im (τ : UpperHalfPlane) : (tauAddOne τ).im = τ.im := by
  have h := congrArg Complex.im (tauAddOne_coe τ)
  simpa [UpperHalfPlane.coe_im] using h

/-- The *removable coincidence* `ST τ = -1/(τ+1)` of the right half-plane: the mirror of
`Work.Asymptotics.tauCoinc`.  Its residue vanishes, but it sits on the imaginary axis when
`Re τ = -1`, so the contour has to be indented into `Re z > 0` (where it never lies when
`Re τ > -1`). -/
def tauCoincRight (τ : UpperHalfPlane) : UpperHalfPlane :=
  (ModularGroup.S * ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ

lemma tauCoincRight_coe (τ : UpperHalfPlane) :
    ((tauCoincRight τ : UpperHalfPlane) : ℂ) = -1 / ((τ : ℂ) + 1) := by
  rw [tauCoincRight, UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num

/-- **For `Re τ > -1` the removable coincidence lies strictly to the left of the axis.** Hence it
is not in either of the two (right) rectangles swept by `Work.Asymptotics.detourRight`. -/
lemma tauCoincRight_re_neg (τ : UpperHalfPlane) (h : -1 < τ.re) : (tauCoincRight τ).re < 0 := by
  have hne : (τ : ℂ) + 1 ≠ 0 := by
    intro h0
    have h1 : (τ : ℂ) = -1 := by linear_combination h0
    have h2 : τ.im = 0 := by rw [← UpperHalfPlane.coe_im, h1]; simp
    exact absurd h2 (ne_of_gt τ.im_pos)
  have hb : ((τ : ℂ) + 1).re = τ.re + 1 := by simp
  rw [← UpperHalfPlane.coe_re, tauCoincRight_coe,
    show (-1 : ℂ) / ((τ : ℂ) + 1) = -(((τ : ℂ) + 1)⁻¹) by rw [inv_eq_one_div, neg_div],
    Complex.neg_re, Complex.inv_re, hb, ← Complex.sq_norm,
    show -((τ.re + 1) / ‖(τ : ℂ) + 1‖ ^ 2) = (-(τ.re + 1)) / ‖(τ : ℂ) + 1‖ ^ 2 by ring]
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos (norm_pos_iff.mpr hne) 2)

/-! ## The residue correction and the layer pieces -/

/-- The residue correction of the right detour, i.e. (the negative of) the value
`2πi·Res_{z=τ+1}(K(τ,z)e^{iπr²z}/i)` of the residue of the contour `1`-form at the pole
`z = τ + 1`.  The second-variable residue of the kernel at `z = τ+1 = Tτ` is `-1/(2π)` (the
`T` companion of `Work.Residues.hasResidue_Kfun_second`, which gives `+1/(2π)` at `z = τ-1`), so
`2πi·Res_{z=τ+1}(K e^{iπr²z}/i) = -e^{iπr²(τ+1)} = -resCorrRight r τ`; the right detour encloses
the pole in the counterclockwise sense, whence the corrected layer `layerTruncContRight` receives
the *positive* correction `+ sinSqC r * resCorrRight r τ`.  This is the mirror of
`Work.Asymptotics.resCorr r τ = e^{iπr²(τ-1)}`. -/
def resCorrRight (r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((τ : ℂ) + 1))


/-! ## The residue of the kernel at the pole `z = τ + 1`

This is the `T` companion of `Work.Residues.hasResidue_Kfun_second` (which computes the
second-variable residue `+1/(2π)` at the pole `z = τ - 1 = T⁻¹τ`).  The value at the pole
`z = τ + 1 = T τ` is its negative, `-1/(2π)`: this is what makes the residue correction of the
*right* detour equal to `resCorrRight r τ = e^{iπr²(τ+1)}` in the corrected layer
`layerTruncContRight`.  The proof is the mirror of
`Work.Asymptotics.kerFormAux.dlc_tendsto_residue`'s input: the cleared identity
`K(τ,ζ)(jτ - jζ) = AfunFun ℓ d τ ζ` (`Work.Asymptotics.Kfun_mul_slope_eq_AfunFun`) together with
the value `AfunFun ℓ d τ (τ+1) = (1/2π)·j'(τ+1)`
(`Work.Asymptotics.AfunFun_vadd_int_of_jprime_ne` with `n = 1`) fed into
`Work.Residues.hasResidue_of_cleared`. -/

/-- **The residue of the second variable of the kernel at `z = τ + 1` is `-1/(2π)`.** -/
theorem hasResidue_Kfun_tauAddOne (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hne : Work.Residues.jprime τ ≠ 0) :
    Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ ζ)
      (tauAddOne τ) (-(1 / (2 * Real.pi))) := by
  have hne' : Work.Residues.jprime (tauAddOne τ) ≠ 0 := by
    rw [tauAddOne, Work.Residues.jprime_vadd_one]; exact hne
  have hj : Work.Kernels.jInvariantFun (tauAddOne τ) = Work.Kernels.jInvariantFun τ := by
    rw [tauAddOne]
    exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ
  have hA : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : UpperHalfPlane => - Work.Asymptotics.AfunFun ℓ d τ ζ) (tauAddOne τ) :=
    (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ _).neg
  have hmain := Work.Residues.hasResidue_of_cleared
    (f := fun ζ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ ζ)
    (A := fun ζ : UpperHalfPlane => - Work.Asymptotics.AfunFun ℓ d τ ζ)
    (z := τ) (z₀ := tauAddOne τ) (c := Work.Residues.jprime (tauAddOne τ))
    hA hj (Work.Residues.tendsto_slope_jprime _) hne'
    (by
      filter_upwards [self_mem_nhdsWithin,
        (Work.Residues.tendsto_slope_jprime (tauAddOne τ)).eventually
          (eventually_ne_nhds hne')]
        with ζ hζ hζne
      have hslope : (Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun (tauAddOne τ)) /
          ((ζ : ℂ) - ((tauAddOne τ : UpperHalfPlane) : ℂ)) ≠ 0 := hζne
      have hjnz : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
        intro h0
        exact hslope (by rw [hj, h0, sub_self, zero_div])
      rw [show Work.Kernels.Kfun ℓ d τ ζ * (Work.Kernels.jInvariantFun ζ
              - Work.Kernels.jInvariantFun τ)
          = -(Work.Kernels.Kfun ℓ d τ ζ * (Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun ζ)) by ring,
        Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ hjnz])
  have hval : (- Work.Asymptotics.AfunFun ℓ d τ (tauAddOne τ))
      / Work.Residues.jprime (tauAddOne τ) = -(1 / (2 * Real.pi)) := by
    have h1 : Work.Asymptotics.AfunFun ℓ d τ (tauAddOne τ)
        = (1 / (2 * Real.pi)) * Work.Residues.jprime (tauAddOne τ) := by
      have h := Work.Asymptotics.AfunFun_vadd_int_of_jprime_ne ℓ d hd τ 1 hne
      rw [show (((1 : ℤ) : ℝ)) = 1 from by norm_num] at h
      rw [h]
      norm_num
    rw [h1, neg_div, mul_div_assoc, div_self hne', mul_one]
  rw [hval] at hmain
  exact hmain

/-- `resCorrRight` differs from `resCorr` only by the constant `e^{2πir²}` (the two residues are
those at the two translates `τ + 1`, `τ - 1` of the same orbit). -/
lemma resCorrRight_eq_resCorr (r : ℝ) (τ : UpperHalfPlane) :
    resCorrRight r τ
      = Work.Asymptotics.resCorr r τ * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) ^ 2) := by
  rw [resCorrRight, Work.Asymptotics.resCorr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The low piece of the right contour: `(0,1]` with the interval `(t₀⁻¹-A₂, t₀⁻¹+A₂)` removed
(the height swept by the removable coincidence `STτ` when the pole height is `t₀ > 1`). -/
def layerLowPieceRight (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A₂ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∫ t in (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t

/-- **The right-hand coincidence-removed low piece**: the mirror of `Work.LayerCont.layerLowCoinc`.
The interval `I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` (the height of the removable coincidence `STτ`) is removed
from the low range and replaced by the *residue-free* right detour at that height. -/
def layerLowCoincRight (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A₂ ξ₂ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r *
    (layerLowPieceRight ℓ d t₀ A₂ r τ
      + Work.Asymptotics.detourRight ℓ d r t₀⁻¹ A₂ ξ₂ τ)

/-- The truncated piece of the right contour: `[1,∞)` with the interval `(t₀-A₁, t₀+A₁)` removed
(the height swept by the moving pole `τ+1` when the pole height is `t₀ > 1`), with the cusp model
`Aexp` subtracted. -/
def layerTruncPieceRight (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A₁ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A₁) (t₀ + A₁),
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
      * Work.Asymptotics.gaussWeight r t

/-- **The continuation of `layerTrunc` across `Re τ = -1`**: the mirror of
`Work.LayerCont.layerTruncCont`.  The removed interval is replaced by the right detour at height
`t₀` (which encloses the pole `τ+1` and therefore contributes the residue `resCorrRight`), the
`Aexp` part of the removed interval is subtracted (its detour is a closed-contour integral of an
entire function), and the residue correction `sinSqC r · resCorrRight r τ` is added. -/
def layerTruncContRight (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A₁ ξ₁ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r
      * (layerTruncPieceRight ℓ d t₀ A₁ r τ
          + Work.Asymptotics.detourRight ℓ d r t₀ A₁ ξ₁ τ
          - ∫ t in Set.Ioo (t₀ - A₁) (t₀ + A₁),
              Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
                * Work.Asymptotics.gaussWeight r t)
    + Work.Asymptotics.sinSqC r * resCorrRight r τ

/-- `resCorrRight` is entire in `τ` (it is `exp` of an affine function). -/
lemma mdifferentiable_resCorrRight (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => resCorrRight r τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (by fun_prop : DifferentiableOn ℂ (fun z : ℂ =>
    Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z + 1))) {z : ℂ | 0 < z.im}).congr ?_
  intro z hz
  show resCorrRight r (UpperHalfPlane.ofComplex z)
      = Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z + 1))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

/-- The identity `resCorrRight r τ = e^{iπr²(τ+1)}` in the form used by the contour identities. -/
lemma resCorrRight_eq (r : ℝ) (τ : UpperHalfPlane) :
    resCorrRight r τ
      = Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (((tauAddOne τ : UpperHalfPlane) : ℂ))) := by
  rw [resCorrRight, tauAddOne_coe]

end Work.LayerCont.Right
