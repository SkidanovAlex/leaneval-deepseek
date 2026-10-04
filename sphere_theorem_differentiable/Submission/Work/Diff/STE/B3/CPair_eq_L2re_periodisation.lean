import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.periodicIntegralLeCube
import Submission.Work.Diff.STE.B3.integral_unitCube_eq_centreCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CPair` is the `L²` pairing of the periodised components

`Work.Diff.STE.B3Data.CPair i p q` is the component pairing `Σ_{a b} ∫_{(-1/2,1/2]^n} p_{a b} q_{a b}`
of two families of real functions supported in the *open* centred cube `(-1/2,1/2)^n`, while
`Work.Diff.STE.L2re f g = Re ∫_{(0,1]^n} f · conj g` is the `L²` pairing over the positive unit
cube.  The identity

`CPair i p q = Σ_{a b} L2re (periodisation p_{a b}) (periodisation q_{a b})`

is the statement that the two pairings agree.  It is the bridge between Layer B3's component
vocabulary and the whole Fourier theory of Layer A, which knows only `1`-periodic functions on the
flat torus.

The proof is purely measure-theoretic, and — importantly — needs **no** smoothness (not even
continuity) of `p`, `q`:

* `(0,1]^n` and `(-1/2,1/2]^n` are both fundamental domains of the translation action of `ℤ^n`, and
  the integrand `P · conj Q` (a product of periodisations) is invariant under lattice translations,
  so the integrals over the two cubes agree (`IsAddFundamentalDomain.setIntegral_eq`, which handles
  non-integrable functions: both sides are then `0`);
* the open and the half-open centred cube agree up to a null set
  (`Measure.pi_Ioo_ae_eq_pi_Ioc`), and on the open cube the periodisation of a function supported
  there equals the function itself (`periodization_eq_self`), so the integrand may be replaced by
  the product of the localised functions a.e.;
* finally, on the real-valued functions the complexified integrand has real part the product of the
  real parts, and `integral_ofReal` (`∫ ↑f = ↑∫ f`, unconditional) finishes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The open centred cube `(-1/2,1/2)^ι`. -/
private abbrev ocube : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))

/-- The half-open centred cube `(-1/2,1/2]^ι`, the fundamental domain `B3Data.centreCube`. -/
private abbrev ccube : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))

private lemma measurableSet_ocube : MeasurableSet (ocube (ι := ι)) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

private lemma measurableSet_ccube : MeasurableSet (ccube (ι := ι)) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

/-- The open and the half-open centred cube agree up to a null set. -/
private lemma ocube_ae_eq_ccube :
    ocube (ι := ι) =ᵐ[(volume : Measure (ι → ℝ))] ccube := by
  have h := MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Ioc
    (μ := fun _ : ι => (volume : Measure ℝ)) (s := Set.univ)
    (f := fun _ : ι => (-(1 / 2 : ℝ))) (g := fun _ : ι => (1 / 2 : ℝ))
  show (Set.pi Set.univ fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      =ᵐ[MeasureTheory.Measure.pi fun _ : ι => (volume : Measure ℝ)]
    (Set.pi Set.univ fun _ : ι => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
  exact h

/-- The union of the coordinate hyperplanes `z i = 1/2` is null. -/
private lemma volume_setOf_exists_coord_eq_half :
    (volume : Measure (ι → ℝ)) {z | ∃ i, z i = (1 / 2 : ℝ)} = 0 := by
  have hsingle : ∀ i : ι, (volume : Measure (ι → ℝ)) {z | z i = (1 / 2 : ℝ)} = 0 := by
    intro i
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i (1 / 2)
  rw [show {z : ι → ℝ | ∃ i, z i = (1 / 2 : ℝ)}
      = ⋃ i, {z : ι → ℝ | z i = (1 / 2 : ℝ)} from by
    ext z
    simp]
  exact MeasureTheory.measure_iUnion_null hsingle

/-- Almost every point of the half-open centred cube lies in the open one. -/
private lemma ae_mem_ocube : ∀ᵐ z ∂(volume.restrict (ccube (ι := ι))), z ∈ ocube (ι := ι) := by
  rw [MeasureTheory.ae_iff]
  show (volume.restrict (ccube (ι := ι))) ((ocube (ι := ι))ᶜ) = 0
  rw [MeasureTheory.Measure.restrict_apply (measurableSet_ocube (ι := ι)).compl]
  refine MeasureTheory.measure_mono_null ?_ (volume_setOf_exists_coord_eq_half (ι := ι))
  intro z hz
  obtain ⟨hznot, hzc⟩ := hz
  rw [Set.mem_compl_iff] at hznot
  simp only [ocube, Set.mem_pi, Set.mem_univ, true_implies] at hznot
  push_neg at hznot
  obtain ⟨i, hi⟩ := hznot
  refine ⟨i, ?_⟩
  simp only [ccube, Set.mem_pi, Set.mem_univ, true_implies] at hzc
  have h1 : z i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := hzc i
  rw [Set.mem_Ioc] at h1
  have h2 : ¬ (z i < (1 / 2 : ℝ)) := fun hlt => hi ⟨h1.1, hlt⟩
  exact le_antisymm h1.2 (not_lt.mp h2)

/-- Complexifying a real function supported in the open cube gives a complex function supported in
the open cube. -/
private lemma support_ofReal {f : (ι → ℝ) → ℝ} (hf : Function.support f ⊆ ocube (ι := ι)) :
    Function.support (fun z => ((f z : ℝ) : ℂ)) ⊆ ocube (ι := ι) := by
  intro z hz
  apply hf
  simp only [Function.mem_support] at hz ⊢
  intro hfz
  exact hz (by rw [hfz]; simp)

/-- **The component pairing over the centred cube is the `L²` pairing of the periodisations.**
For two real functions supported in the open centred cube, the integral of their product over the
centred cube is the real part of the `L²` pairing of their periodisations over the positive unit
cube. -/
private lemma integral_ccube_mul_eq_L2re_periodisation
    (f g : (ι → ℝ) → ℝ)
    (hf : Function.support f ⊆ ocube (ι := ι))
    (hg : Function.support g ⊆ ocube (ι := ι)) :
    (∫ z in ccube (ι := ι), f z * g z)
      = Complex.re (∫ z in Work.Diff.STE.unitCube (ι := ι),
          (∑' m : ι → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))
            * star (∑' m : ι → ℤ, ((g (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))) := by
  classical
  let F : (ι → ℝ) → ℂ := fun z => ((f z : ℝ) : ℂ)
  let G : (ι → ℝ) → ℂ := fun z => ((g z : ℝ) : ℂ)
  let PF : (ι → ℝ) → ℂ := fun z => ∑' m : ι → ℤ, F (z + Work.Diff.STE.iVec m)
  let PG : (ι → ℝ) → ℂ := fun z => ∑' m : ι → ℤ, G (z + Work.Diff.STE.iVec m)
  have hPFper : Work.Diff.STE.Periodic1 PF := Work.Diff.STE.periodization_periodic F
  have hPGper : Work.Diff.STE.Periodic1 PG := Work.Diff.STE.periodization_periodic G
  have hFsupp : Function.support F ⊆ ocube (ι := ι) := support_ofReal hf
  have hGsupp : Function.support G ⊆ ocube (ι := ι) := support_ofReal hg
  have haeF : PF =ᵐ[volume.restrict (ccube (ι := ι))] F := by
    filter_upwards [ae_mem_ocube (ι := ι)] with z hz
    exact Work.Diff.STE.periodization_eq_self hFsupp
      (fun i => Set.mem_pi.mp hz i (Set.mem_univ i))
  have haeG : PG =ᵐ[volume.restrict (ccube (ι := ι))] G := by
    filter_upwards [ae_mem_ocube (ι := ι)] with z hz
    exact Work.Diff.STE.periodization_eq_self hGsupp
      (fun i => Set.mem_pi.mp hz i (Set.mem_univ i))
  -- the integral over the positive cube is the integral over the centred cube
  have hstep1 : (∫ z in Work.Diff.STE.unitCube (ι := ι), PF z * star (PG z))
      = ∫ z in ccube (ι := ι), PF z * star (PG z) := by
    have hper : ∀ (n : ι → ℤ) (x : ι → ℝ),
        (fun z : ι → ℝ => PF z * star (PG z)) (n +ᵥ x)
          = (fun z : ι → ℝ => PF z * star (PG z)) x := by
      intro n x
      change PF ((fun i => (n i : ℝ)) + x) * star (PG ((fun i => (n i : ℝ)) + x))
        = PF x * star (PG x)
      rw [Work.Diff.STE.B3.Periodic1.add_intVec hPFper n x,
        Work.Diff.STE.B3.Periodic1.add_intVec hPGper n x]
    have hmain := MeasureTheory.IsAddFundamentalDomain.setIntegral_eq
      (isAddFundamentalDomain_cube_Ioc (ι := ι) 0)
      (isAddFundamentalDomain_cube_Ioc (ι := ι) (-(1 / 2)))
      (f := fun z : ι → ℝ => PF z * star (PG z)) hper
    have hone : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
    rw [hone] at hmain
    simpa [Work.Diff.STE.unitCube, ccube] using hmain
  -- on the centred cube the periodisations are the functions themselves
  have hstep2 : (∫ z in ccube (ι := ι), PF z * star (PG z))
      = ∫ z in ccube (ι := ι), F z * star (G z) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeF, haeG] with z h1 h2
    rw [h1, h2]
  -- the complexified integrand is the complexification of the real product
  have hpt : (fun z : ι → ℝ => F z * star (G z))
      = (fun z : ι → ℝ => ((f z * g z : ℝ) : ℂ)) := by
    funext z
    show ((f z : ℝ) : ℂ) * star (((g z : ℝ) : ℂ)) = ((f z * g z : ℝ) : ℂ)
    simp [Complex.ofReal_mul]
  have hstep3 : (∫ z in ccube (ι := ι), F z * star (G z))
      = ((∫ z in ccube (ι := ι), f z * g z : ℝ) : ℂ) := by
    rw [hpt]
    exact integral_ofReal
  rw [hstep1, hstep2, hstep3, Complex.ofReal_re]

/-- **The component pairing is the `L²` pairing of the periodised components**, component-wise
form: the sum over the matrix indices of the integrals over the centred cube equals the sum of the
`L²` pairings of the periodisations. -/
private lemma sum_CPair_eq_L2re_periodisation
    {n : ℕ} (p q : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hp : ∀ a b, Function.support (p a b) ⊆ ocube (ι := Fin n))
    (hq : ∀ a b, Function.support (q a b) ⊆ ocube (ι := Fin n)) :
    (∑ a, ∑ b, ∫ z in ccube (ι := Fin n), p a b z * q a b z)
      = ∑ a, ∑ b, Complex.re (∫ z in Work.Diff.STE.unitCube (ι := Fin n),
          (∑' m : Fin n → ℤ, ((p a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))
            * star (∑' m : Fin n → ℤ, ((q a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact integral_ccube_mul_eq_L2re_periodisation (p a b) (q a b) (hp a b) (hq a b)

theorem CPair_eq_L2re_periodisation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {ι₀ : Type*} [Fintype ι₀]
    (i : ι₀)
    (p q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hps : ∀ a b, Function.support (p a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hqs : ∀ a b, Function.support (q a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    Work.Diff.STE.B3Data.CPair (E := E) i p q
      = ∑ a, ∑ b, Work.Diff.STE.L2re
          (fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((p a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))
          (fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((q a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)) := by
  classical
  rw [Work.Diff.STE.B3Data.CPair]
  simp only [Work.Diff.STE.L2re]
  exact sum_CPair_eq_L2re_periodisation p q hps hqs

end Work.Diff.STE.B3
