import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.sampling_unitCube_L2
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chiLatticeParseval` — the lattice Parseval identity of the corpus `χ`

The theorem proved here is the **correlation form of Parseval's identity** for the corpus
localization function `Submission.BoseGases.chi` (the smooth bump supported in the unit cube
`[-1/2,1/2]³` with `∫χ² = 1`, presented as `Work.BoseK15.corpusBox`):

    `∑_{m ∈ ℤ³} χ̂(2πm)·χ̂(2π(m+n)) = χ̂²(2πn)`

where `χ̂(p) = ∫ χ(x)cos⟪p,x⟫ dx` is the cosine transform of `χ` and
`χ̂²(p) = ∫ χ²(x)cos⟪p,x⟫ dx` that of `χ²` (`Work.BoseB4.BoxData.hatChi`, `hatChiSq`).

## The mathematics

Because `χ` is supported in a fundamental domain of the unit torus `𝕋³ = (ℝ/ℤ)³`, the
periodization `A(x) = Σ_k χ(x+k)` is a smoothing of `χ` (`A = χ` on the box), and
`χ̂(2πm) = ∫_{[0,1]³} A(x) e^{-2πi m·x} dx` are precisely the Fourier coefficients of `A`.
The identity is then the statement that the Fourier coefficients of the product `A²` (which is
the periodization of `χ²`, since the translates of `χ` do not overlap) are the *correlations*
`Σ_m \hat A(m)\hat A(m+n)` of the coefficients of `A` — the convolution theorem on the torus,
equivalently Parseval applied to the pair `(χ, χ·e^{-2πin·x})`.

## The formalisation

Everything happens on the unit torus `𝕋³ = UnitAddTorus (Fin 3)`, where Mathlib provides the
orthonormal Fourier basis (`UnitAddTorus.mFourierBasis`) and Parseval in the sesquilinear form
(`UnitAddTorus.hasSum_prod_mFourierCoeff`).  The dictionary between the torus and the box is
`Work.BoseBoxFock.torusLift` (`Submission/Work/BoseBoxFock/SamplingDefs.lean`, together with
`sampling_unitCube_L2`, where the norm-square case of the same computation is proved).  The
pieces are:

* `Work.BoseRowQ2.sampling_unitCube_pair` — the **pair** (sesquilinear) form of the box
  Parseval identity `∑_n conj(∫ e^{-i⟪2πn,y⟫}f)·(∫ e^{-i⟪2πn,y⟫}g) = ∫ conj(f)g` for `f, g ∈ L²`
  supported in the unit cube (`Work.BoseBoxFock.sampling_unitCube_L2` is the `f = g` case);
* `Work.BoseRowQ2.integral_exp_inner_of_even` — for a continuous compactly supported **even**
  real `F`, the complex Fourier sample is the cosine transform:
  `∫ e^{-i⟪p,y⟫}·↑(F y) = ↑(∫ F y·cos⟪p,y⟫)`;
* the assembly, which applies the pair identity to `f = ↑χ` and `g = e^{-i⟪2πn,·⟫}·↑χ`, uses
  `vec (m+n) = vec m + vec n` to shift the coefficients, and takes real parts.

-/

noncomputable section

open MeasureTheory

namespace Work.BoseRowQ2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] instMeasureSpaceUnitAddCircle

set_option linter.unusedVariables false

/-! ## 1. Elementary facts: the lattice vector and the support/`L²` of `χ` -/

/-- The dual-lattice vector `vec` is additive: `vec (m+n) = vec m + vec n`
(`Work.BoseB4.vec n = 2πn`). -/
lemma vec_add (m n : Fin 3 → ℤ) :
    Work.BoseB4.vec (m + n) = Work.BoseB4.vec m + Work.BoseB4.vec n := by
  ext i
  simp [Work.BoseB4.vec]
  ring

/-- The complexified corpus `χ` has its topological support in the closed unit cube
`[-1/2,1/2]³`, in the form used by the torus-lift API. -/
lemma tsupport_chiOfReal_subset_box :
    tsupport (fun y : E3 => (Submission.BoseGases.chi y : ℂ))
      ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)} := by
  have hsub : Function.support (fun y : E3 => (Submission.BoseGases.chi y : ℂ))
      ⊆ Work.BoseB4.unitCell := by
    intro y hy
    exact Work.BoseK15.chi_support_subset_unitCell
      (by simpa [Function.mem_support] using hy)
  have h := closure_minimal hsub Work.BoseB4.isClosed_unitCell
  intro y hy i
  exact h hy i

/-- The twisted function `y ↦ e^{-i⟪2πn,y⟫}·χ(y)` is supported where `χ` is. -/
lemma tsupport_twisted_subset (n : Fin 3 → ℤ) :
    tsupport (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
        * (Submission.BoseGases.chi y : ℂ))
      ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)} :=
  subset_trans tsupport_mul_subset_right tsupport_chiOfReal_subset_box

/-- The complexified corpus `χ` is `L²` (continuity plus compact support). -/
lemma memLp_chiOfReal : MemLp (fun y : E3 => (Submission.BoseGases.chi y : ℂ)) 2
    (volume : Measure E3) :=
  (Complex.continuous_ofReal.comp Submission.BoseGases.chi_continuous).memLp_of_hasCompactSupport
    (Submission.BoseGases.chi_hasCompactSupport.comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp))

/-- The twisted function `y ↦ e^{-i⟪2πn,y⟫}·χ(y)` is `L²`. -/
lemma memLp_twisted (n : Fin 3 → ℤ) : MemLp (fun y : E3 =>
    Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
      * (Submission.BoseGases.chi y : ℂ)) 2 (volume : Measure E3) := by
  refine Continuous.memLp_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))))).mul
      (Complex.continuous_ofReal.comp Submission.BoseGases.chi_continuous)
  · exact (Submission.BoseGases.chi_hasCompactSupport.comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_left
      (f := fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))))

/-! ## 2. The complex Fourier sample of an even function -/

/-- An **even** real function has vanishing sine transform: the integrand of
`∫ F y·sin⟪p,y⟫ dy` is odd, so the change of variables `y ↦ -y` gives `I = -I`. -/
lemma integral_mul_sin_inner_eq_zero {F : E3 → ℝ} (heven : ∀ x, F (-x) = F x) (p : E3) :
    (∫ y : E3, F y * Real.sin (inner ℝ p y)) = 0 := by
  have hodd : ∀ y : E3,
      F (-y) * Real.sin (inner ℝ p (-y)) = -(F y * Real.sin (inner ℝ p y)) := by
    intro y
    rw [heven y, inner_neg_right, Real.sin_neg]
    ring
  have h1 : (∫ y : E3, F (-y) * Real.sin (inner ℝ p (-y)))
      = ∫ y : E3, F y * Real.sin (inner ℝ p y) :=
    MeasureTheory.integral_neg_eq_self (fun y : E3 => F y * Real.sin (inner ℝ p y)) volume
  rw [funext hodd] at h1
  rw [integral_neg] at h1
  exact (self_eq_neg).mp h1.symm

/-- **The complex Fourier sample of an even function is its cosine transform.**  For a continuous
compactly supported even real `F` and any `p`,

    `∫ y, e^{-i⟪p,y⟫}·↑(F y) = ↑(∫ y, F y·cos⟪p,y⟫)`.

The imaginary part is `-∫ F·sin⟪p,y⟫ = 0` by evenness (`integral_mul_sin_inner_eq_zero`); the
real part is the cosine transform. -/
theorem integral_exp_inner_of_even {F : E3 → ℝ} (hF : Continuous F) (hcs : HasCompactSupport F)
    (heven : ∀ x, F (-x) = F x) (p : E3) :
    (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (F y : ℂ))
      = ((∫ y : E3, F y * Real.cos (inner ℝ p y) : ℝ) : ℂ) := by
  -- splitting the phase into its real and imaginary parts
  have hdecomp : ∀ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (F y : ℂ)
      = ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ)
        - Complex.I * ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ) := by
    intro y
    have hI : Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
        = ((Real.cos (inner ℝ p y) : ℂ)) - ((Real.sin (inner ℝ p y) : ℂ)) * Complex.I := by
      rw [show -(Complex.I * (inner ℝ p y : ℂ)) = (-(inner ℝ p y) : ℝ) * Complex.I by
            push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
        Real.sin_neg]
      push_cast
      ring
    rw [hI]
    push_cast
    ring
  -- integrability of the two pieces (continuity + compact support)
  have hcs_cos : HasCompactSupport
      (fun y : E3 => ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ)) :=
    (hcs.mul_right (f' := fun y : E3 => Real.cos (inner ℝ p y))).comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcs_sin : HasCompactSupport
      (fun y : E3 => ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ)) :=
    (hcs.mul_right (f' := fun y : E3 => Real.sin (inner ℝ p y))).comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcont_cos : Continuous (fun y : E3 => ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (hF.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id)))
  have hcont_sin : Continuous (fun y : E3 => ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (hF.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id)))
  have hcosI : Integrable (fun y : E3 => ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ)) volume :=
    hcont_cos.integrable_of_hasCompactSupport hcs_cos
  have hsinI : Integrable
      (fun y : E3 => Complex.I * ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ)) volume :=
    (hcont_sin.integrable_of_hasCompactSupport hcs_sin).const_mul Complex.I
  have hmain : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (F y : ℂ))
      = (∫ y : E3, ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ))
        - Complex.I * (∫ y : E3, ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp), integral_sub hcosI hsinI,
      integral_const_mul]
  have hcos_eq : (∫ y : E3, ((F y * Real.cos (inner ℝ p y) : ℝ) : ℂ))
      = ((∫ y : E3, F y * Real.cos (inner ℝ p y) : ℝ) : ℂ) := integral_ofReal
  have hsin_eq : (∫ y : E3, ((F y * Real.sin (inner ℝ p y) : ℝ) : ℂ))
      = ((∫ y : E3, F y * Real.sin (inner ℝ p y) : ℝ) : ℂ) := integral_ofReal
  rw [hmain, hcos_eq, hsin_eq, integral_mul_sin_inner_eq_zero heven p]
  simp

/-! ## 3. The pair (sesquilinear) form of the box Parseval identity -/

/-- A function supported in the closed unit cube vanishes at every point outside it. -/
private lemma eq_zero_of_notMem_boxIcc {h : E3 → ℂ}
    (hsupp : tsupport h ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)})
    {x : Fin 3 → ℝ} (hx : x ∉ Work.BoseBoxFock.boxIcc) : h (WithLp.toLp 2 x) = 0 := by
  by_contra hne
  have hmem : WithLp.toLp 2 x ∈ tsupport h :=
    subset_tsupport h (Function.mem_support.mpr hne)
  exact hx (Work.BoseBoxFock.mem_boxIcc.mpr fun i => by simpa using hsupp hmem i)

/-- **The torus lift is an isometry, sesquilinear form**: for `f, g` supported in the closed unit
cube, `∫_{𝕋³} conj(lift f)·(lift g) = ∫_{ℝ³} conj(f)·g`.  This is the pair version of
`Work.BoseBoxFock.integral_torusLift_normSq`. -/
lemma integral_torusLift_pair {f g : E3 → ℂ}
    (hfsupp : tsupport f ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)})
    (hgsupp : tsupport g ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)}) :
    (∫ t : UnitAddTorus (Fin 3),
        (starRingEnd ℂ) (Work.BoseBoxFock.torusLift f t) * Work.BoseBoxFock.torusLift g t
        ∂Work.BoseBoxFock.torusVol)
      = ∫ y : E3, (starRingEnd ℂ) (f y) * g y := by
  have h1 : (∫ t : UnitAddTorus (Fin 3),
        (starRingEnd ℂ) (Work.BoseBoxFock.torusLift f t) * Work.BoseBoxFock.torusLift g t
        ∂Work.BoseBoxFock.torusVol)
      = ∫ x in Work.BoseBoxFock.boxIoc,
          (starRingEnd ℂ) (Work.BoseBoxFock.torusLift f (Work.BoseBoxFock.torusProj x))
            * Work.BoseBoxFock.torusLift g (Work.BoseBoxFock.torusProj x) := by
    rw [Work.BoseBoxFock.torusVol_eq_volume, Work.BoseBoxFock.boxIoc_eq_halfBox]
    exact UnitAddTorus.integral_preimage (d := Fin 3)
      (fun t : UnitAddTorus (Fin 3) =>
        (starRingEnd ℂ) (Work.BoseBoxFock.torusLift f t) * Work.BoseBoxFock.torusLift g t)
      (fun _ => (-(1 / 2) : ℝ))
  have h2 : (∫ x in Work.BoseBoxFock.boxIoc,
        (starRingEnd ℂ) (Work.BoseBoxFock.torusLift f (Work.BoseBoxFock.torusProj x))
          * Work.BoseBoxFock.torusLift g (Work.BoseBoxFock.torusProj x))
      = ∫ x in Work.BoseBoxFock.boxIoc,
          (starRingEnd ℂ) (f (WithLp.toLp 2 x)) * g (WithLp.toLp 2 x) := by
    refine setIntegral_congr_fun Work.BoseBoxFock.measurableSet_boxIoc fun x hx => ?_
    rw [Work.BoseBoxFock.torusLift_apply_proj (g := f) hx,
      Work.BoseBoxFock.torusLift_apply_proj (g := g) hx]
  have h3 : (∫ x in Work.BoseBoxFock.boxIoc,
        (starRingEnd ℂ) (f (WithLp.toLp 2 x)) * g (WithLp.toLp 2 x))
      = ∫ x : Fin 3 → ℝ, (starRingEnd ℂ) (f (WithLp.toLp 2 x)) * g (WithLp.toLp 2 x) := by
    rw [setIntegral_congr_set Work.BoseBoxFock.boxIoc_ae_eq_boxIcc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [eq_zero_of_notMem_boxIcc hfsupp hx, map_zero, zero_mul]
  rw [h1, h2, h3, ← Work.BoseBoxFock.integral_toLp
    (fun y : E3 => (starRingEnd ℂ) (f y) * g y)]

/-- **The box Parseval identity in sesquilinear form.**  For `f, g ∈ L²(ℝ³)` supported in the
closed unit cube `[-1/2,1/2]³`, the pairing of their Fourier samples on the lattice `2πℤ³` is the
`L²` pairing of `f` and `g`:

    `∑_n conj(∫ e^{-i⟪2πn,y⟫}f)·(∫ e^{-i⟪2πn,y⟫}g) = ∫ conj(f)·g`.

This is the pair version of `Work.BoseBoxFock.sampling_unitCube_L2` (the case `f = g`), with
the same proof; it is a direct transcription of Mathlib's torus Parseval
`UnitAddTorus.hasSum_prod_mFourierCoeff` through the torus lift
`Work.BoseBoxFock.torusLift`. -/
theorem sampling_unitCube_pair {f g : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3))
    (hfsupp : tsupport f ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)})
    (hg : MemLp g 2 (volume : Measure E3))
    (hgsupp : tsupport g ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)}) :
    HasSum (fun n : Fin 3 → ℤ =>
        (starRingEnd ℂ)
            (∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * f y)
          * (∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y))
      (∫ y, (starRingEnd ℂ) (f y) * g y) := by
  have hPf : MemLp (Work.BoseBoxFock.torusLift f) 2 Work.BoseBoxFock.torusVol :=
    Work.BoseBoxFock.torusLift_memLp_of_memLp hf
  have hPg : MemLp (Work.BoseBoxFock.torusLift g) 2 Work.BoseBoxFock.torusVol :=
    Work.BoseBoxFock.torusLift_memLp_of_memLp hg
  have hsum := UnitAddTorus.hasSum_prod_mFourierCoeff (d := Fin 3)
    (hPf.toLp (Work.BoseBoxFock.torusLift f)) (hPg.toLp (Work.BoseBoxFock.torusLift g))
  -- the limit: the torus pairing is the `L²` pairing on the cube
  have hRHS : (∫ t : UnitAddTorus (Fin 3),
        (starRingEnd ℂ) ((hPf.toLp (Work.BoseBoxFock.torusLift f)) t)
          * ((hPg.toLp (Work.BoseBoxFock.torusLift g)) t))
      = ∫ y : E3, (starRingEnd ℂ) (f y) * g y := by
    rw [← integral_torusLift_pair hfsupp hgsupp]
    refine integral_congr_ae ?_
    filter_upwards [hPf.coeFn_toLp, hPg.coeFn_toLp] with t ht1 ht2
    rw [ht1, ht2]
  -- the summands: the coefficients are the integrals of the statement
  have hfun : ∀ n : Fin 3 → ℤ,
      (starRingEnd ℂ)
          (∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * f y)
        * (∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y)
      = (starRingEnd ℂ)
          (UnitAddTorus.mFourierCoeff
            (⇑(hPf.toLp (Work.BoseBoxFock.torusLift f))) n)
        * (UnitAddTorus.mFourierCoeff
            (⇑(hPg.toLp (Work.BoseBoxFock.torusLift g))) n) := by
    intro n
    rw [← Work.BoseBoxFock.mFourierCoeff_torusLift hPf hfsupp n,
      ← Work.BoseBoxFock.mFourierCoeff_torusLift hPg hgsupp n]
  have hsum2 := hsum.congr_fun hfun
  exact hRHS ▸ hsum2

/-! ## 4. The lattice Parseval identity -/

/-- The elementary exponential identity behind the shift `m ↦ m + n` of the lattice index. -/
private lemma exp_inner_mul (m n : Fin 3 → ℤ) (y : E3) :
    Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ)))
      * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec (m + n)) y : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [vec_add, inner_add_left]
  push_cast
  ring

theorem chiLatticeParseval (n : Fin 3 → ℤ) :
    (∑' m : Fin 3 → ℤ,
        Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)
          * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (m + n)))
      = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n) := by
  set f : E3 → ℂ := fun y => (Submission.BoseGases.chi y : ℂ) with hfdef
  set g : E3 → ℂ := fun y =>
    Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * f y with hgdef
  have hgsupp : tsupport g ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)} := by
    rw [hgdef]
    exact tsupport_twisted_subset n
  have hgmem : MemLp g 2 (volume : Measure E3) := by
    rw [hgdef]
    exact memLp_twisted n
  have hfmem : MemLp f 2 (volume : Measure E3) := by
    rw [hfdef]
    exact memLp_chiOfReal
  have hfsupp : tsupport f ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)} := by
    rw [hfdef]
    exact tsupport_chiOfReal_subset_box
  have hpair := sampling_unitCube_pair hfmem hfsupp hgmem hgsupp
  -- the coefficient of `f`: the cosine transform of `χ`
  have hself : ∀ k : Fin 3 → ℤ,
      (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec k) y : ℂ))) * f y)
        = ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec k) : ℝ) : ℂ) := by
    intro k
    have h := integral_exp_inner_of_even (F := Submission.BoseGases.chi)
      Submission.BoseGases.chi_continuous Submission.BoseGases.chi_hasCompactSupport
      Submission.BoseGases.chi_even (Work.BoseB4.vec k)
    simpa [hfdef, Work.BoseB4.BoxData.hatChi] using h
  -- the coefficients of `g`: shifted by `n`
  have hshift : ∀ m : Fin 3 → ℤ,
      (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ))) * g y)
        = ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (m + n)) : ℝ) : ℂ) := by
    intro m
    have h1 : (∫ y : E3,
          Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ))) * g y)
        = (∫ y : E3,
            Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec (m + n)) y : ℂ))) * f y) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hgdef]
      rw [← mul_assoc, exp_inner_mul m n y]
    rw [h1, hself (m + n)]
  -- the limit: the cosine transform of `χ²`
  have hR : (∫ y : E3, (starRingEnd ℂ) (f y) * g y)
      = ((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n) : ℝ) : ℂ) := by
    have hpt : (fun y : E3 => (starRingEnd ℂ) (f y) * g y)
        = fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ)))
            * (((Submission.BoseGases.chi y) ^ 2 : ℝ) : ℂ) := by
      funext y
      simp only [hfdef, hgdef]
      rw [Complex.conj_ofReal]
      push_cast
      ring
    rw [hpt]
    have hcs2 : HasCompactSupport (fun y : E3 => (Submission.BoseGases.chi y) ^ 2) :=
      Submission.BoseGases.chi_hasCompactSupport.comp_left
        (g := fun r : ℝ => r ^ 2) (by norm_num)
    have h := integral_exp_inner_of_even (F := fun y : E3 => (Submission.BoseGases.chi y) ^ 2)
      (Submission.BoseGases.chi_continuous.pow 2) hcs2
      (fun x => by rw [Submission.BoseGases.chi_even]) (Work.BoseB4.vec n)
    simpa [Work.BoseB4.BoxData.hatChiSq] using h
  rw [hR] at hpair
  have hpair' : HasSum (fun m : Fin 3 → ℤ =>
      (starRingEnd ℂ) (((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m) : ℝ)) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (m + n)) : ℝ)) : ℂ))
      (((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n) : ℝ)) : ℂ) := by
    refine hpair.congr_fun fun m => ?_
    rw [hself m, hshift m]
  have hre := Complex.hasSum_re hpair'
  have hfinal : HasSum (fun m : Fin 3 → ℤ =>
      Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)
        * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (m + n)))
      (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n)) := by
    simpa [Complex.conj_ofReal] using hre
  exact hfinal.tsum_eq

end Work.BoseRowQ2
