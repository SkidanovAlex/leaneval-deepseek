import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.NormSymAux
import Submission.Work.BoseBoxFock.kinFTDerivPlancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Δ³ (kinFT u) = - kinFT (‖·‖⁶ u)`

`Submission.BoseGases.kinFT u p = ∫_y e^{-i⟪p,y⟫} u y dy` is the `p`-convention Fourier
transform, and `Work.BoseBoxFock.lap3 f = ∑_{a b c} ∂_{e_a}²∂_{e_b}²∂_{e_c}² f` is the
Laplacian cubed (the `27`-term sum of `NormSymAux.lean`).  The main result of this file is

`Work.BoseBoxFock.lap3_kinFT`:
`lap3 (fun p => kinFT u p) = fun p => - kinFT (fun z => ‖z‖⁶ u z) p`
for `u` smooth with compact support — the identity that converts the sixth-order derivative
of the Fourier transform into multiplication by the sixth power of the modulus, i.e. the
one-body statement involving the symbol `F(√-Δ) = ‖√-Δ‖⁶ = (-Δ)³`.

## Route

* `kinFT_fderiv_dir` (`kinFTDerivPlancherel.lean`): `∂_w (kinFT g)(p) = kinFT (z ↦ -i⟪w,z⟫ g z) p`
  for `g` smooth compactly supported;
* the multiplier of a *list* of directions, `kinMult L z = ∏_{v ∈ L} (-i⟪v,z⟫)`, and the
  iteration `dIter (kinFT u) L p = kinFT (fun z => kinMult L z * u z) p` (`dIter_kinFT`);
* linearity of `kinFT` under finite sums (`kinFT_finsetSum`, `kinFT_sum3_mul`), which lets
  the `27`-term sum be taken inside the integral;
* the polynomial identities `kinMult (lap3List a b c) z = -z_a²z_b²z_c²`
  (`kinMult_lap3List`) and `∑_{a b c} z_a²z_b²z_c² = ‖z‖⁶` (`sum_lap3_mul`), hence
  `∑_{a b c} kinMult (lap3List a b c) z = -‖z‖⁶` (`sum_kinMult_lap3List`);
* `kinFT_neg_mul`, which turns the minus into the minus in front of the integral.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The multiplier of a list of directions -/

/-- The multiplier attached to a list of directions: iterating "differentiate the Fourier
transform" multiplies the argument by `-i⟪v,z⟫` for each direction `v` of the list, the head of
the list being the outermost derivative.  `kinMult [] z = 1`. -/
noncomputable def kinMult : List E3 → E3 → ℂ
  | [] => fun _ => 1
  | v :: L => fun z => (-Complex.I * ((inner ℝ v z : ℝ) : ℂ)) * kinMult L z

@[simp] lemma kinMult_nil : kinMult [] = fun _ => (1 : ℂ) := rfl

@[simp] lemma kinMult_cons (v : E3) (L : List E3) :
    kinMult (v :: L) = fun z => (-Complex.I * ((inner ℝ v z : ℝ) : ℂ)) * kinMult L z := rfl

lemma kinMult_eq_prod (L : List E3) (z : E3) :
    kinMult L z = (L.map (fun v => -Complex.I * ((inner ℝ v z : ℝ) : ℂ))).prod := by
  induction L with
  | nil => simp
  | cons v L ih => simp [List.prod_cons, ih]

/-- The multiplier of a list of directions is smooth (it is a polynomial). -/
lemma contDiff_kinMult (L : List E3) : ContDiff ℝ (⊤ : ENat) (kinMult L) := by
  induction L with
  | nil => rw [kinMult_nil]; exact contDiff_const
  | cons v L ih =>
      rw [kinMult_cons]
      refine (contDiff_const.mul ?_).mul ih
      exact Complex.ofRealCLM.contDiff.comp (innerSL ℝ v).contDiff

/-- The multiplier of a list of directions, times a compactly supported `u`, is compactly
supported. -/
lemma hasCompactSupport_kinMult_mul {u : E3 → ℂ} (L : List E3) (huc : HasCompactSupport u) :
    HasCompactSupport (fun z => kinMult L z * u z) :=
  HasCompactSupport.mul_left (f := kinMult L) huc

/-- Integrability of the `kinFT` integrand of a multiplier times `u`. -/
lemma integrable_exp_kinMult_mul {u : E3 → ℂ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (huc : HasCompactSupport u) (p : E3) (L : List E3) :
    Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (kinMult L z * u z)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (Complex.continuous_exp.comp ?_).mul ((contDiff_kinMult L).continuous.mul hu.continuous)
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (innerSL ℝ p).continuous)).neg
  · exact HasCompactSupport.mul_left
      (f := fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
      (hasCompactSupport_kinMult_mul L huc)

/-! ## 2. The iteration of the derivative identity -/

/-- **Iterated derivative of `kinFT`.**  For `u` smooth with compact support and any list of
directions `L`, the iterated directional derivative of `kinFT u` equals `kinFT` of the product
of `u` with the multiplier `kinMult L`. -/
lemma dIter_kinFT {u : E3 → ℂ} (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u)
    (L : List E3) (p : E3) :
    dIter (fun p => Submission.BoseGases.kinFT u p) L p
      = Submission.BoseGases.kinFT (fun z => kinMult L z * u z) p := by
  induction L generalizing p with
  | nil =>
      rw [dIter_nil, kinMult_nil]
      congr 1
      funext z
      simp
  | cons v L ih =>
      show fderiv ℝ (dIter (fun p => Submission.BoseGases.kinFT u p) L) p v
          = Submission.BoseGases.kinFT (fun z => kinMult (v :: L) z * u z) p
      rw [show (dIter (fun p => Submission.BoseGases.kinFT u p) L)
          = fun q => Submission.BoseGases.kinFT (fun z => kinMult L z * u z) q from
        funext (fun q => ih q)]
      rw [kinFT_fderiv_dir (contDiff_kinMult L |>.mul hu)
        (hasCompactSupport_kinMult_mul L huc) p v]
      congr 1
      funext z
      simp only [kinMult_cons]
      ring

/-! ## 3. Linearity of `kinFT` in its argument -/

/-- `kinFT` of a negated multiplier: the minus comes out. -/
lemma kinFT_neg_mul (c u : E3 → ℂ) (p : E3) :
    Submission.BoseGases.kinFT (fun z => (- c z) * u z) p
      = - Submission.BoseGases.kinFT (fun z => c z * u z) p := by
  simp only [Submission.BoseGases.kinFT]
  rw [← integral_neg]
  congr 1
  funext z
  ring

/-- **Linearity of `kinFT` under a finite sum.**  The `kinFT` of a finite sum of multipliers
times `u` is the finite sum of the `kinFT`s. -/
lemma kinFT_finsetSum {ι : Type*} [Fintype ι] {F : ι → E3 → ℂ} {u : E3 → ℂ} {p : E3}
    (hF : ∀ i, Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (F i z * u z))) :
    (∑ i, Submission.BoseGases.kinFT (fun z => F i z * u z) p)
      = Submission.BoseGases.kinFT (fun z => (∑ i, F i z) * u z) p := by
  have hpt : (fun z : E3 =>
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((∑ i, F i z) * u z))
      = fun z : E3 => ∑ i,
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (F i z * u z) := by
    funext z
    rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Submission.BoseGases.kinFT]
  rw [hpt]
  exact (integral_finsetSum Finset.univ (f := fun i (z : E3) =>
    Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (F i z * u z))
    (fun i _ => hF i)).symm

/-- **Linearity of `kinFT` under the `27`-term sum.**  The triple sum of the `kinFT`s of the
`lap3` multipliers — written as a single sum over the product index type in the proof — is the
`kinFT` of the sum of the multipliers, times `u`. -/
lemma kinFT_sum3_mul {u : E3 → ℂ} (p : E3)
    (hF : ∀ a b c : Fin 3, Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (kinMult (lap3List a b c) z * u z))) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        Submission.BoseGases.kinFT (fun z => kinMult (lap3List a b c) z * u z) p)
      = Submission.BoseGases.kinFT
          (fun z => (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
            kinMult (lap3List a b c) z) * u z) p := by
  have hconv : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        Submission.BoseGases.kinFT (fun z => kinMult (lap3List a b c) z * u z) p)
      = ∑ x : (Fin 3 × Fin 3) × Fin 3,
          Submission.BoseGases.kinFT
            (fun z => kinMult (lap3List x.1.1 x.1.2 x.2) z * u z) p := by
    simp only [Fintype.sum_prod_type]
  rw [hconv]
  rw [kinFT_finsetSum (F := fun x : (Fin 3 × Fin 3) × Fin 3 =>
        fun z : E3 => kinMult (lap3List x.1.1 x.1.2 x.2) z)
      (hF := fun x => hF x.1.1 x.1.2 x.2)]
  congr 1
  funext z
  simp only [Fintype.sum_prod_type]

/-! ## 4. The polynomial identities -/

/-- The multiplier of `lap3List a b c` is `-z_a²z_b²z_c²`. -/
lemma kinMult_lap3List (a b c : Fin 3) (z : E3) :
    kinMult (lap3List a b c) z
      = -((((inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
            (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
            (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2 : ℝ)) : ℂ) := by
  have hI : Complex.I ^ 6 = -1 := by
    have h : Complex.I ^ 6
        = (Complex.I * Complex.I) * (Complex.I * Complex.I) * (Complex.I * Complex.I) := by
      ring
    rw [h, Complex.I_mul_I]
    norm_num
  simp only [lap3List, kinMult_cons, kinMult_nil]
  push_cast
  ring_nf
  rw [hI]
  ring

/-- `∑_{a b c} z_a² z_b² z_c² = ‖z‖⁶`, i.e. `(∑_a z_a²)³ = ‖z‖⁶` for the standard basis. -/
lemma sum_lap3_mul (z : E3) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
      (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
      (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2) = ‖z‖ ^ 6 := by
  have h3 : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
      (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
      (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2)
      = (∑ a : Fin 3, (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2) *
        ((∑ b : Fin 3, (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2) *
        (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2)) := by
    calc ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
          (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
          (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2
        = ∑ a : Fin 3, ∑ b : Fin 3,
            ((inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2) *
            (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2) := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
            rw [← Finset.mul_sum]
      _ = ∑ a : Fin 3,
            (∑ b : Fin 3, (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2) *
            (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [← Finset.sum_mul]
      _ = ∑ a : Fin 3,
            ((inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (∑ b : Fin 3, (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2)) *
            (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [← Finset.mul_sum]
      _ = ∑ a : Fin 3, (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
            ((∑ b : Fin 3, (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2) *
            (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2)) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            ring
      _ = (∑ a : Fin 3, (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2) *
            ((∑ b : Fin 3, (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2) *
            (∑ c : Fin 3, (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2)) := by
            rw [← Finset.sum_mul]
  rw [h3, sum_inner_single_sq]
  ring

/-- **The `27`-term multiplier sum.**  `∑_{a b c} kinMult (lap3List a b c) z = -‖z‖⁶`. -/
lemma sum_kinMult_lap3List (z : E3) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, kinMult (lap3List a b c) z)
      = -(((‖z‖ ^ 6 : ℝ)) : ℂ) := by
  have h1 : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, kinMult (lap3List a b c) z)
      = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          -((((inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2 : ℝ)) : ℂ) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => kinMult_lap3List a b c z)))
  have h2 : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          -((((inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2 : ℝ)) : ℂ))
      = -(((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
             (inner ℝ (EuclideanSpace.single a (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single b (1 : ℝ)) z) ^ 2 *
             (inner ℝ (EuclideanSpace.single c (1 : ℝ)) z) ^ 2 : ℝ)) : ℂ) := by
    push_cast
    simp only [Finset.sum_neg_distrib]
  rw [h1, h2, sum_lap3_mul z]

/-! ## 5. The theorem -/

/-- **`Δ³` of the Fourier transform.**  For `u : ℝ³ → ℂ` smooth with compact support,
applying the Laplacian cubed to `p ↦ kinFT u p` multiplies the argument of the transform by
`-‖·‖⁶`. -/
theorem lap3_kinFT {u : EuclideanSpace ℝ (Fin 3) → ℂ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (huc : HasCompactSupport u) :
    Work.BoseBoxFock.lap3 (fun p => Submission.BoseGases.kinFT u p)
      = fun p => - Submission.BoseGases.kinFT (fun z => ((‖z‖ ^ 6 : ℝ) : ℂ) * u z) p := by
  funext p
  show (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          dIter (fun p => Submission.BoseGases.kinFT u p) (lap3List a b c) p)
      = - Submission.BoseGases.kinFT (fun z => ((‖z‖ ^ 6 : ℝ) : ℂ) * u z) p
  rw [show (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          dIter (fun p => Submission.BoseGases.kinFT u p) (lap3List a b c) p)
      = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          Submission.BoseGases.kinFT (fun z => kinMult (lap3List a b c) z * u z) p) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun c _ => dIter_kinFT hu huc (lap3List a b c) p)))]
  rw [kinFT_sum3_mul p (fun a b c => integrable_exp_kinMult_mul hu huc p (lap3List a b c))]
  rw [show (fun z : E3 => (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          kinMult (lap3List a b c) z) * u z)
      = fun z : E3 => (-(((‖z‖ ^ 6 : ℝ)) : ℂ)) * u z from by
        funext z
        rw [sum_kinMult_lap3List z]]
  exact kinFT_neg_mul (fun z => ((‖z‖ ^ 6 : ℝ) : ℂ)) u p

end Work.BoseBoxFock
