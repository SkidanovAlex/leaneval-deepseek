import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PV_algebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SlotProjAux` — infrastructure for the slot projections

This module collects the definitions and the elementary (measure-theoretic and topological)
lemmas that the proof of `Work.BoseBoxFock.slotProj_idem_and_comm` needs.

* `slotInt e S Φ x` is the *general* slot projection: it is definitionally equal to
  `slotProj e S Φ x` (see `slotProj_eq_slotInt`) but written with `Function.updateFinset`, which
  is the form in which the Fubini/composition arguments are carried out.
* `slotProj1 e i Φ x` is the *single slot* projection (the slot `i` only).
* `Eeq hi` is the measure preserving splitting `(↑S → Ω) × Ω ≃ᵐ ↑(S ∪ {i}) → Ω` used by the
  "peel one slot" identity, together with its evaluation lemmas, the configuration identity
  `updateFinset_Eeq` and the product identity `prod_Eeq`.
* `continuous_slotInt_integrand`, `hasCompactSupport_slotInt_integrand` and
  `integrable_slotInt_integrand` are the regularity inputs of the Fubini arguments.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The slot projections -/

/-- The general slot projection: the integral over the slots of `S` of the product of the
projection kernels against `Φ` evaluated at the configuration in which the slots of `S` are
replaced.  It is definitionally the `slotProj` of `SlotProjDefs` (with `ι = Fin n`). -/
def slotInt {m : ℕ} (e : Fin m → Ω → ℂ) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Φ : (ι → Ω) → ℂ) (x : ι → Ω) : ℂ :=
  ∫ z : S → Ω, (∏ i : S, PV e (x i.1) (z i)) * Φ (Function.updateFinset x S z)

/-- `slotInt` is `slotProj`. -/
theorem slotProj_eq_slotInt {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (x : Fin n → Ω) : slotProj e S Φ x = slotInt e S Φ x := rfl

/-- `slotInt` is `slotProj`, as an identity of functions. -/
theorem slotProj_eq_slotInt_fun {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) : slotProj e S Φ = slotInt e S Φ :=
  funext fun x => slotProj_eq_slotInt e S Φ x

/-- The single-slot projection: only the slot `i` is integrated against the kernel `PV`. -/
def slotProj1 {m : ℕ} (e : Fin m → Ω → ℂ) {ι : Type*} [DecidableEq ι] (i : ι)
    (Φ : (ι → Ω) → ℂ) (x : ι → Ω) : ℂ :=
  ∫ w : Ω, PV e (x i) w * Φ (Function.update x i w)

/-- The empty slot projection is the identity. -/
theorem slotInt_empty {m : ℕ} (e : Fin m → Ω → ℂ) {ι : Type*} [DecidableEq ι]
    (Φ : (ι → Ω) → ℂ) : slotInt e (∅ : Finset ι) Φ = Φ := by
  funext x
  have hvol : (volume : Measure ((↑(∅ : Finset ι)) → Ω)).real Set.univ = 1 := by
    rw [volume_pi, Measure.real, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.toReal_one]
  rw [slotInt]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Function.updateFinset_empty]
  rw [integral_unique]
  rw [hvol, one_smul]

/-! ## 2. Elementary facts about the projection kernel `PV` -/

/-- `PV e a ·` is continuous when the modes are. -/
theorem continuous_PV_snd {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l)) (a : Ω) :
    Continuous (fun y : Ω => PV e a y) := by
  simp only [PV]
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_star.comp (he l)))

/-- `PV e a y` vanishes when all the modes vanish at `y`. -/
theorem PV_eq_zero_of_factors {m : ℕ} (e : Fin m → Ω → ℂ) {a y : Ω}
    (h : ∀ l, e l y = 0) : PV e a y = 0 := by
  simp only [PV, h, star_zero, mul_zero, Finset.sum_const_zero]

/-- The product of the projection kernels over a finite set of slots is compactly supported. -/
theorem hasCompactSupport_prod_PV {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) {ι : Type*} (S : Finset ι) (x : ι → Ω) :
    HasCompactSupport (fun z : ↑S → Ω => ∏ i : ↑S, PV e (x i.1) (z i)) := by
  classical
  refine HasCompactSupport.intro'
    (isCompact_univ_pi (fun _ : ↑S => isCompact_iUnion (fun l : Fin m => (hec l).isCompact)))
    (isClosed_set_pi (fun _ _ => (isCompact_iUnion (fun l : Fin m => (hec l).isCompact)).isClosed))
    ?_
  intro z hz
  have hz' : ∃ i : ↑S, z i ∉ (⋃ l : Fin m, tsupport (e l)) := by
    by_contra h
    exact hz (by rw [Set.mem_univ_pi]; intro i; exact not_not.mp (not_exists.mp h i))
  obtain ⟨i, hi⟩ := hz'
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  exact PV_eq_zero_of_factors e
    (fun l => image_eq_zero_of_notMem_tsupport (fun h => hi (Set.mem_iUnion.mpr ⟨l, h⟩)))

/-! ## 3. The splitting equivalence -/

/-- The measure preserving splitting of the slots of `S ∪ {i}` (`i ∉ S`) into the slots of `S`
and the extra slot `i`. -/
def Eeq {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S) :
    ((↑S → Ω) × Ω) ≃ᵐ (↑(S ∪ {i}) → Ω) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (↑S → Ω))
      (MeasurableEquiv.funUnique (↑({i} : Finset ι)) Ω).symm).trans
    (MeasurableEquiv.piFinsetUnion (fun _ : ι => Ω) (Finset.disjoint_singleton_right.mpr hi))

theorem Eeq_unfold {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (z' : ↑S → Ω) (w : Ω) :
    Eeq hi (z', w) =
      MeasurableEquiv.piFinsetUnion (fun _ : ι => Ω) (Finset.disjoint_singleton_right.mpr hi)
        (z', (MeasurableEquiv.funUnique (↑({i} : Finset ι)) Ω).symm w) := rfl

/-- The evaluation of `Eeq` on the slots of `S`. -/
theorem Eeq_apply_mem {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (z' : ↑S → Ω) (w : Ω) {u : ι} (hu : u ∈ S) (hu' : u ∈ S ∪ {i}) :
    Eeq hi (z', w) ⟨u, hu'⟩ = z' ⟨u, hu⟩ := by
  rw [Eeq_unfold]
  change Equiv.piFinsetUnion (fun _ : ι => Ω) (Finset.disjoint_singleton_right.mpr hi)
      (z', (MeasurableEquiv.funUnique (↑({i} : Finset ι)) Ω).symm w) ⟨u, hu'⟩ = z' ⟨u, hu⟩
  exact Equiv.piFinsetUnion_left _ _ hu hu'

/-- The evaluation of `Eeq` on the extra slot. -/
theorem Eeq_apply_i {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (z' : ↑S → Ω) (w : Ω) (hu : i ∈ S ∪ {i}) :
    Eeq hi (z', w) ⟨i, hu⟩ = w := by
  rw [Eeq_unfold]
  change Equiv.piFinsetUnion (fun _ : ι => Ω) (Finset.disjoint_singleton_right.mpr hi)
      (z', (MeasurableEquiv.funUnique (↑({i} : Finset ι)) Ω).symm w) ⟨i, hu⟩ = w
  rw [Equiv.piFinsetUnion_right _ _ (Finset.mem_singleton_self i) hu]
  rfl

/-- `Eeq` preserves the volume. -/
theorem Eeq_measurePreserving {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S) :
    MeasurePreserving (Eeq hi) (volume : Measure ((↑S → Ω) × Ω))
      (volume : Measure (↑(S ∪ {i}) → Ω)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinsetUnion (fun _ : ι => Ω)
      (Finset.disjoint_singleton_right.mpr hi))
      (volume : Measure ((↑S → Ω) × (↑({i} : Finset ι) → Ω)))
      (volume : Measure (↑(S ∪ {i}) → Ω)) := volume_preserving_piFinsetUnion _ _
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (↑S → Ω))
        (MeasurableEquiv.funUnique (↑({i} : Finset ι)) Ω).symm)
      (volume : Measure ((↑S → Ω) × Ω))
      (volume : Measure ((↑S → Ω) × (↑({i} : Finset ι) → Ω))) :=
    MeasurePreserving.prod (MeasurePreserving.id _) (volume_preserving_funUnique _ _).symm
  exact h1.comp h2

/-- **The configuration identity of the peel**: reassembling the slots of `S ∪ {i}` through
`Eeq` is the same as updating the slots of `S` and then the slot `i`. -/
theorem updateFinset_Eeq {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (x : ι → Ω) (z' : ↑S → Ω) (w : Ω) :
    Function.updateFinset x (S ∪ {i}) (Eeq hi (z', w)) =
      Function.update (Function.updateFinset x S z') i w := by
  rw [eq_comm, Function.update_updateFinset (π := fun _ : ι => Ω) hi]
  rfl

/-- **The product identity of the peel**: the product of the kernels over the slots of `S ∪ {i}`
evaluated at `Eeq hi (z', w)` splits into the product over `S` and the factor of the extra slot. -/
theorem prod_Eeq {m : ℕ} (e : Fin m → Ω → ℂ) {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {i : ι} (hi : i ∉ S) (x : ι → Ω) (z' : ↑S → Ω) (w : Ω) :
    (∏ u : ↑(S ∪ {i}), PV e (x u.1) (Eeq hi (z', w) u)) =
      (∏ u : ↑S, PV e (x u.1) (z' u)) * PV e (x i) w := by
  set e' := Equiv.Finset.union S {i} (Finset.disjoint_singleton_right.mpr hi) with he'
  have h := Fintype.prod_equiv e'
    (fun p : ↑S ⊕ ↑({i} : Finset ι) => PV e (x (e' p).1) (Eeq hi (z', w) (e' p)))
    (fun u : ↑(S ∪ {i}) => PV e (x u.1) (Eeq hi (z', w) u))
    (fun p => rfl)
  rw [← h, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Equiv.Finset.union_inl]
    rw [Eeq_apply_mem hi z' w a.2 (Finset.mem_union_left {i} a.2)]
  · rw [Fintype.prod_subsingleton
      (fun b : ↑({i} : Finset ι) => PV e (x (e' (Sum.inr b)).1) (Eeq hi (z', w) (e' (Sum.inr b))))
      ⟨i, Finset.mem_singleton_self i⟩]
    rw [Equiv.Finset.union_inr]
    rw [Eeq_apply_i hi z' w (Finset.mem_union_right S (Finset.mem_singleton_self i))]

/-! ## 4. Regularity of the slot integrands -/

/-- The integrand of `slotInt` is continuous. -/
theorem continuous_slotInt_integrand {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (Φ : (ι → Ω) → ℂ) (hΦ : Continuous Φ)
    (x : ι → Ω) :
    Continuous (fun z : ↑S → Ω =>
      (∏ i : ↑S, PV e (x i.1) (z i)) * Φ (Function.updateFinset x S z)) := by
  refine Continuous.mul
    (continuous_finsetProd _ (fun i _ => (continuous_PV_snd e he (x i.1)).comp (continuous_apply i)))
    (hΦ.comp ?_)
  refine continuous_pi (fun j => ?_)
  simp only [Function.updateFinset_def]
  split_ifs with hj
  · exact continuous_apply _
  · exact continuous_const

/-- The integrand of `slotInt` is compactly supported. -/
theorem hasCompactSupport_slotInt_integrand {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Φ : (ι → Ω) → ℂ) (x : ι → Ω) :
    HasCompactSupport (fun z : ↑S → Ω =>
      (∏ i : ↑S, PV e (x i.1) (z i)) * Φ (Function.updateFinset x S z)) :=
  (hasCompactSupport_prod_PV e hec S x).mul_right

/-- The integrand of `slotInt` is integrable. -/
theorem integrable_slotInt_integrand {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Φ : (ι → Ω) → ℂ) (hΦ : Continuous Φ) (x : ι → Ω) :
    Integrable (fun z : ↑S → Ω =>
      (∏ i : ↑S, PV e (x i.1) (z i)) * Φ (Function.updateFinset x S z)) volume :=
  (continuous_slotInt_integrand e he S Φ hΦ x).integrable_of_hasCompactSupport
    (hasCompactSupport_slotInt_integrand e hec S Φ x)

/-! ## 5. Integrability of a compactly supported kernel against a bounded state -/

/-- A continuous compactly supported function times a bounded measurable function is integrable. -/
theorem integrable_mul_of_continuous_hasCompactSupport_of_bounded {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {g f : X → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hfm : AEStronglyMeasurable f μ) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => g x * f x) μ := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hg.bounded_above_of_compact_support hgc
  refine Integrable.mono'
    (g := (tsupport g).indicator (fun _ => max Cg 0 * max C 0))
    ?_ ((hg.aestronglyMeasurable).mul hfm) ?_
  · rw [integrable_indicator_iff (isClosed_tsupport g).measurableSet]
    exact integrableOn_const (hgc.measure_lt_top.ne)
  · filter_upwards with x
    by_cases hx : x ∈ tsupport g
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul ((hCg x).trans (le_max_left _ _)) ((hC x).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    · rw [Set.indicator_of_notMem hx, norm_mul,
        image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul]

/-- `PV e` is continuous in its two arguments. -/
theorem continuous_PV_uncurry {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l)) :
    Continuous (fun p : Ω × Ω => PV e p.1 p.2) := by
  simp only [PV]
  exact continuous_finsetSum _
    (fun l _ => ((he l).comp continuous_fst).mul ((continuous_star.comp (he l)).comp continuous_snd))

end Work.BoseBoxFock
