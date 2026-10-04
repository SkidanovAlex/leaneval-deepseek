import Mathlib
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.memLp_comp_rep
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.mFourier_mk_eq_fourierExp
import Submission.Work.Diff.STE.integral_pullback_norm_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parseval's identity on the unit cube

`Work.Diff.STE.B3.parseval_cube` is the equality half of the Fourier theory of the cube
(the companion `Work.Diff.STE.bessel_continuous` is the inequality half):

  `∫_{unitCube} ‖g‖² = ∑' k, ‖fourierCoeff g k‖²`

for a **continuous** `g : (ι → ℝ) → ℂ`.  No periodicity is assumed: the target function only
has to be square integrable on the cube, which continuity guarantees.

The proof is a transport from the compact torus, where Mathlib already knows Parseval
(`UnitAddTorus.hasSum_sq_mFourierCoeff`, proved from the Hilbert basis `mFourierBasis`):

* the `Ioc`-representative `rep : UnitAddTorus ι → (ι → ℝ)`, `rep t = fun i ↦ (equivIoc 1 0 (t i)).1`
  identifies the torus (with its Haar probability measure) with the cube up to a null set
  (`Work.Diff.STE.measurePreserving_rep`), and `g ∘ rep` is square integrable on the torus
  (`Work.Diff.STE.memLp_comp_rep`); the corresponding `L²` integrals agree
  (`Work.Diff.STE.integral_pullback_norm_sq`);
* the Fourier coefficients of the pulled back `L²`-class coincide with the cube Fourier
  coefficients `fourierCoeff g k = ∫_{unitCube} exp (-2πi k·x) g x`: the torus coefficient is the
  integral of `mFourier (-k) • (g ∘ rep)`, and `UnitAddTorus.mFourierCoeff_eq_integral` together
  with `mFourier_mk_eq_fourierExp` and `(equivIoc 1 0) ↑x = x` on `(0,1]` rewrites it into the
  cube integral.

Everything is `L²`-based, so at no point is pointwise convergence of the Fourier series used.
-/

noncomputable section

open MeasureTheory

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- On the cube, the `Ioc`-representative map `UnitAddTorus ι → (ι → ℝ)` (viewed through the
quotient map `x ↦ (fun i ↦ (x i : UnitAddCircle))`) is the identity. -/
lemma rep_mk (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) :
    (fun i => (AddCircle.equivIoc (1 : ℝ) (0 : ℝ) ((x i : ℝ) : UnitAddCircle)).1) = x := by
  funext i
  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (by simpa using hx i))

/-- The Fourier coefficient of the pullback `g ∘ rep` of a function `g` on the cube, computed in
the torus `L²` theory, is the cube Fourier coefficient `Work.Diff.STE.fourierCoeff g k`. -/
lemma mFourierCoeff_comp_rep_eq_fourierCoeff (g : (ι → ℝ) → ℂ) (k : ι → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) k
      = Work.Diff.STE.fourierCoeff g k := by
  classical
  -- Mathlib's torus theory uses the normalised Haar measure on `ℝ / ℤ` as volume.
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k (fun _ => 0)]
  rw [Work.Diff.STE.fourierCoeff]
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)}
      = Work.Diff.STE.unitCube (ι := ι) := by
    ext x; simp [Work.Diff.STE.unitCube, Set.mem_pi]
  rw [hset]
  refine setIntegral_congr_fun
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)) ?_
  intro x hx
  have hx' : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Work.Diff.STE.unitCube, Set.mem_pi] using hx
  simp only [smul_eq_mul]
  rw [Work.Diff.STE.mFourier_mk_eq_fourierExp, rep_mk x hx']

/-- **Parseval's identity on the unit cube.**  For a continuous `g : (ι → ℝ) → ℂ` (no periodicity
assumed), the `L²` norm squared of `g` on the cube `(0,1]^ι` is the sum of the squared absolute
values of its Fourier coefficients. -/
theorem parseval_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℂ)
    (hg : Continuous g) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2)
      = ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 := by
  classical
  -- Mathlib's torus Fourier theory uses the normalised Haar measure on `ℝ / ℤ` as volume; with
  -- that instance the product volume on `UnitAddTorus ι` *is* the measure of
  -- `Work.Diff.STE.memLp_comp_rep` / `Work.Diff.STE.integral_pullback_norm_sq`.
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  have hmem : MemLp g 2 (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.BesselCont.memLp_of_continuous g hg
  have hFmem : MemLp (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) 2
      (volume : Measure (UnitAddTorus ι)) := Work.Diff.STE.memLp_comp_rep hmem
  -- the `L²` class of the pullback and the pullback function itself agree a.e.
  have hu : ⇑((MemLp.toLp
        (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem))
      =ᵐ[volume] (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) :=
    MemLp.coeFn_toLp hFmem
  -- Parseval on the torus
  have hhas := UnitAddTorus.hasSum_sq_mFourierCoeff
    ((MemLp.toLp (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem))
  have hcoeff : ∀ k : ι → ℤ,
      UnitAddTorus.mFourierCoeff ((MemLp.toLp
        (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem)) k
        = Work.Diff.STE.fourierCoeff g k := by
    intro k
    rw [← mFourierCoeff_comp_rep_eq_fourierCoeff g k]
    refine integral_congr_ae ?_
    filter_upwards [hu] with t ht
    rw [ht]
  -- the two `L²` integrals agree
  have hint : ∫ t : UnitAddTorus ι, ‖(MemLp.toLp
          (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem) t‖ ^ 2
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2 := by
    rw [integral_congr_ae (by
      filter_upwards [hu] with t ht
      rw [ht])]
    exact Work.Diff.STE.integral_pullback_norm_sq g hg.aestronglyMeasurable
  calc (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2)
      = ∫ t : UnitAddTorus ι, ‖(MemLp.toLp
          (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem) t‖ ^ 2 :=
        hint.symm
    _ = ∑' k : ι → ℤ, ‖UnitAddTorus.mFourierCoeff ((MemLp.toLp
          (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hFmem)) k‖ ^ 2 :=
        hhas.tsum_eq.symm
    _ = ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 :=
        tsum_congr (fun k => by rw [hcoeff k])

end Work.Diff.STE.B3
