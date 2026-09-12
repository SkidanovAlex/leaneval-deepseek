import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Submission.LatticeDefs
import Submission.CovDual

noncomputable section

open scoped BigOperators RealInnerProductSpace NNReal ENNReal
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter
open Submission.LatticeDefs

namespace Submission.CovShort

section Cubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def funBox (ι : Type*) [Fintype ι] (r : ℝ) : Set (ι → ℝ) := {w | ∀ i, |w i| ≤ r}

lemma volume_funBox (ι : Type*) [Fintype ι] {r : ℝ} (hr : 0 ≤ r) :
    volume (funBox ι r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  have hbox : funBox ι r = Set.univ.pi (fun _ : ι => Set.Icc (-r) r) := by
    ext w
    constructor
    · intro h i _hi; exact Set.mem_Icc.mpr (abs_le.mp (h i))
    · intro h i; exact abs_le.mpr (Set.mem_Icc.mp (h i (by simp)))
  rw [hbox, MeasureTheory.volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const]
  have h2r : 0 ≤ 2 * r := by positivity
  have hrr : r - -r = 2 * r := by ring
  rw [hrr, ← ENNReal.ofReal_pow h2r]
  congr 1

lemma measurableSet_funBox (ι : Type*) [Fintype ι] (r : ℝ) :
    MeasurableSet (funBox ι r) := by
  rw [show funBox ι r = Set.univ.pi (fun _ : ι => Set.Icc (-r) r) by
    ext w
    constructor
    · intro h i _hi; exact Set.mem_Icc.mpr (abs_le.mp (h i))
    · intro h i; exact abs_le.mpr (Set.mem_Icc.mp (h i (by simp)))]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)

variable {ι : Type*} [Fintype ι]

def eucCube (o : OrthonormalBasis ι ℝ E) (r : ℝ) : Set E :=
  {x : E | ∀ i : ι, |(o.repr x) i| ≤ r}

lemma box_preimage (o : OrthonormalBasis ι ℝ E) (r : ℝ) :
    o.repr ⁻¹' ({z : EuclideanSpace ℝ ι | ∀ i, |z i| ≤ r} : Set (EuclideanSpace ℝ ι)) = eucCube o r := by
  rfl

lemma funBox_of_symm (r : ℝ) :
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm ⁻¹' (funBox ι r) =
      {z : EuclideanSpace ℝ ι | ∀ i, |z i| ≤ r} := by
  rfl

lemma volume_eucCube (o : OrthonormalBasis ι ℝ E) {r : ℝ} (hr : 0 ≤ r) :
    volume (eucCube o r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  let box : Set (EuclideanSpace ℝ ι) := {z | ∀ i, |z i| ≤ r}
  have hcube : o.repr ⁻¹' box = eucCube o r := rfl
  let f : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
  have hfbox : f ⁻¹' funBox ι r = box := by rfl
  have hboxMeas : NullMeasurableSet box := by
    rw [← hfbox]
    exact (f.measurable (measurableSet_funBox ι r)).nullMeasurableSet
  calc
    volume (eucCube o r) = volume (o.repr ⁻¹' box) := by rw [hcube]
    _ = volume (box : Set (EuclideanSpace ℝ ι)) := by
        rw [(o.measurePreserving_repr).measure_preimage hboxMeas]
    _ = volume ((f ⁻¹' funBox ι r) : Set (EuclideanSpace ℝ ι)) := by rw [hfbox]
    _ = volume (funBox ι r : Set (ι → ℝ)) := by
        rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := ι)).measure_preimage
          (measurableSet_funBox ι r).nullMeasurableSet]
    _ = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := volume_funBox ι hr

lemma measurableSet_eucCube (o : OrthonormalBasis ι ℝ E) (r : ℝ) :
    MeasurableSet (eucCube o r) := by
  let box : Set (EuclideanSpace ℝ ι) := {z | ∀ i, |z i| ≤ r}
  have hboxMeas : MeasurableSet box := by
    dsimp [box]
    rw [← funBox_of_symm r]
    exact (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable (measurableSet_funBox ι r)
  have hm : Measurable (o.repr : E → EuclideanSpace ℝ ι) :=
    (LinearIsometryEquiv.continuous o.repr).measurable
  change MeasurableSet (o.repr ⁻¹' box)
  exact hm hboxMeas

lemma convex_eucCube (o : OrthonormalBasis ι ℝ E) (r : ℝ) : Convex ℝ (eucCube o r) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  intro i
  have hx1 : |(o.repr x) i| ≤ r := hx i
  have hy1 : |(o.repr y) i| ≤ r := hy i
  have hmapi : (o.repr (a • x + b • y) i) = a * (o.repr x) i + b * (o.repr y) i := by
    simp [map_add, map_smul, mul_comm, mul_left_comm, mul_assoc]
  rw [hmapi]
  have hcalc : |a * (o.repr x) i + b * (o.repr y) i| ≤
      a * |(o.repr x) i| + b * |(o.repr y) i| := by
    calc
      |a * (o.repr x) i + b * (o.repr y) i| ≤ |a * (o.repr x) i| + |b * (o.repr y) i| := abs_add_le _ _
      _ = a * |(o.repr x) i| + b * |(o.repr y) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h1 : a * |(o.repr x) i| ≤ a * r := mul_le_mul_of_nonneg_left hx1 ha
  have h2 : b * |(o.repr y) i| ≤ b * r := mul_le_mul_of_nonneg_left hy1 hb
  have h3 : a * r + b * r = r := by
    rw [← add_mul, hab, one_mul]
  linarith

lemma symm_eucCube (o : OrthonormalBasis ι ℝ E) (r : ℝ) : ∀ x ∈ eucCube o r, -x ∈ eucCube o r := by
  intro x hx i
  simpa using hx i

lemma mem_eucCube_norm_le (o : OrthonormalBasis ι ℝ E) {r : ℝ} (hr : 0 ≤ r)
    {x : E} (hx : x ∈ eucCube o r) :
    ‖x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * r := by
  have hsq : ‖x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * r ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : ι, ((o.repr x) i) ^ 2 := by
        rw [← (LinearIsometryEquiv.norm_map o.repr x)]
        rw [EuclideanSpace.real_norm_sq_eq]
      _ ≤ ∑ i : ι, r ^ 2 := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hc : |(o.repr x) i| ≤ r := hx i
        rw [← sq_abs]
        calc |(o.repr x) i| ^ 2 = |(o.repr x) i| * |(o.repr x) i| := by ring
          _ ≤ r * r := mul_le_mul hc hc (abs_nonneg _) hr
          _ = r ^ 2 := by ring
      _ = (Fintype.card ι : ℝ) * r ^ 2 := by simp
  have hb : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * r := by positivity
  have hsq2 : (Real.sqrt (Fintype.card ι : ℝ) * r) ^ 2 = (Fintype.card ι : ℝ) * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt]
    ring
    positivity
  exact (sq_le_sq₀ (norm_nonneg x) hb).mp (by simpa [hsq2] using hsq)


end Cubes

section Minkowski

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Minkowski: a full-rank lattice has a nonzero vector of norm ≤ `2 √d · covol^(1/d)`. -/
lemma exists_short_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hd : 1 ≤ finrank ℝ E) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧
      ‖v‖ ≤ 2 * Real.sqrt (finrank ℝ E : ℝ) *
        (ZLattice.covolume L) ^ ((1 : ℝ) / (finrank ℝ E : ℝ)) := by
  classical
  let d : ℕ := finrank ℝ E
  let C : ℝ := ZLattice.covolume L
  let e : ℝ := (1 : ℝ) / (d : ℝ)
  let R : ℝ := 2 * C ^ e
  let o := stdOrthonormalBasis ℝ E
  have hd0n : 0 < d := by dsimp [d]; exact lt_of_lt_of_le zero_lt_one hd
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd0n
  have hC0 : 0 < C := by dsimp [C]; exact ZLattice.covolume_pos (μ := volume) L
  have hCnonneg : 0 ≤ C := le_of_lt hC0
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hR : 0 ≤ R := le_of_lt hRpos
  let bz : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let F : Set E := ZSpan.fundamentalDomain (bz.ofZLatticeBasis ℝ)
  have hspan : span ℤ (Set.range (bz.ofZLatticeBasis ℝ)) = L :=
    Module.Basis.ofZLatticeBasis_span ℝ L bz
  have hfund : IsAddFundamentalDomain L.toAddSubgroup F volume := by
    have hf0 := ZSpan.isAddFundamentalDomain' (bz.ofZLatticeBasis ℝ) volume
    have hAsp : L.toAddSubgroup =
        (span ℤ (Set.range (bz.ofZLatticeBasis ℝ))).toAddSubgroup :=
      congrArg Submodule.toAddSubgroup hspan.symm
    rw [hAsp]
    exact hf0
  have hcov : (volume F).toReal = C := by
    dsimp [F, C]
    exact (covol_eq_fund L bz).symm
  have hFin : (volume F) ≠ ⊤ := by
    intro ht
    have : (volume F).toReal = 0 := by simp [ht]
    rw [hcov] at this
    linarith
  have hF : (volume F) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hFin, hcov]
  have hvolS : volume (eucCube o R) = ENNReal.ofReal ((2 * R) ^ d) := by
    have h := volume_eucCube o hR
    simpa [d] using h
  have he : e * (d : ℝ) = 1 := by
    dsimp [e]
    field_simp [hd0.ne']
  have hpowC : (C ^ e) ^ d = C ^ (e * (d : ℝ)) := by
    rw [← Real.rpow_natCast (C ^ e) d]
    rw [Real.rpow_mul hCnonneg e (d : ℝ)]
  have hpow1 : (2 * R) ^ d = (4 : ℝ) ^ d * C := by
    calc
      (2 * R) ^ d = (4 * C ^ e) ^ d := by
        dsimp [R]
        ring
      _ = (4 : ℝ) ^ d * (C ^ e) ^ d := by rw [mul_pow]
      _ = (4 : ℝ) ^ d * C ^ (e * (d : ℝ)) := by rw [hpowC]
      _ = (4 : ℝ) ^ d * C := by rw [he, Real.rpow_one]
  have h1 : 2 ≤ (2 : ℝ) ^ d := by
    have hle : (1 : ℕ) ≤ d := by exact_mod_cast hd0n
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle)
  have h2d : 1 < (2 : ℝ) ^ d := by linarith
  have h4 : (4 : ℝ) ^ d = (2 : ℝ) ^ d * (2 : ℝ) ^ d := by
    rw [show (4 : ℝ) = (2 : ℝ) * (2 : ℝ) by norm_num, mul_pow]
  have h4gt : (2 : ℝ) ^ d < (4 : ℝ) ^ d := by
    have hlt : 1 * (2 : ℝ) ^ d < (2 : ℝ) ^ d * (2 : ℝ) ^ d :=
      mul_lt_mul_of_pos_right h2d (by positivity)
    rw [h4]
    linarith
  have hreal : C * (2 : ℝ) ^ d < (2 * R) ^ d := by
    rw [hpow1]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_lt_mul_of_pos_right h4gt hC0)
  have hLHS : (volume F) * (2 : ℝ≥0∞) ^ d = ENNReal.ofReal (C * (2 : ℝ) ^ d) := by
    have h2e : (2 : ℝ≥0∞) ^ d = ENNReal.ofReal ((2 : ℝ) ^ d) := by
      norm_num [ENNReal.ofReal_pow]
    rw [hF, h2e, ← ENNReal.ofReal_mul hCnonneg]
  have hineq : (volume F) * (2 : ℝ≥0∞) ^ d < volume (eucCube o R) := by
    rw [hLHS, hvolS]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (2 * R) ^ d)).mpr hreal
  have hcnt : Countable L.toAddSubgroup := by
    change Countable L
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxS⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) hfund (symm_eucCube o R) (convex_eucCube o R) hineq
  have hxmem : (x : E) ∈ L := by
    simpa [Submodule.mem_toAddSubgroup] using hxL
  have hnx : ‖(x : E)‖ ≤ 2 * Real.sqrt (d : ℝ) * C ^ e := by
    have hb := mem_eucCube_norm_le o hR (by simpa using hxS)
    have hcard : (Fintype.card (Fin (finrank ℝ E)) : ℝ) = (d : ℝ) := by
      rw [Fintype.card_fin]
    have hb' : ‖(x : E)‖ ≤ Real.sqrt (d : ℝ) * R := by
      simpa [hcard] using hb
    dsimp [R] at hb' ⊢
    nlinarith [Real.sqrt_nonneg (d : ℝ), hCnonneg]
  refine ⟨(x : E), hxmem, ?_, ?_⟩
  · exact fun h => hx0 (Subtype.ext h)
  · dsimp [d, C, e] at hnx ⊢
    exact hnx

end Minkowski

section ShortVec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Submission.CovDual

/-- Covolume of the ℤ-span of a real basis equals the volume of its fundamental domain. -/
lemma covolume_span_basis {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = (volume.real (ZSpan.fundamentalDomain b)) := by
  classical
  let bz : Basis ι ℤ (span ℤ (Set.range b)) := b.restrictScalars ℤ
  have h := ZLattice.covolume_eq_det_mul_measureReal (L := span ℤ (Set.range b)) (μ := volume) bz b
  have hfun : ((↑) : span ℤ (Set.range b) → E) ∘ bz = b := by
    funext i
    exact (Module.Basis.restrictScalars_apply ℤ b i)
  have hdet : |b.det (((↑) : span ℤ (Set.range b) → E) ∘ bz)| = 1 := by
    rw [hfun]
    rw [Basis.det_self]
    norm_num
  rw [h, hdet]
  simp

/-- A shortest nonzero vector of the lattice. -/
lemma exists_shortest_vector (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hd : 1 ≤ finrank ℝ E) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ ∀ u : E, u ∈ L → u ≠ 0 → ‖v‖ ≤ ‖u‖ := by
  classical
  let bz : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let b := bz.ofZLatticeBasis ℝ
  obtain ⟨wE, hwmem, hw0, _⟩ := exists_short_lattice L hd
  have hsp : span ℤ (Set.range b) = L := Module.Basis.ofZLatticeBasis_span ℝ L bz
  have hb : Set.Finite (Metric.closedBall (0 : E) ‖wE‖ ∩ (L : Set E)) := by
    rw [← hsp]
    exact ZSpan.setFinite_inter b (Metric.isBounded_closedBall)
  let S : Set E := {u : E | u ∈ L ∧ u ≠ 0 ∧ ‖u‖ ≤ ‖wE‖}
  have hSfin : S.Finite := by
    refine hb.subset ?_
    intro u hu
    exact ⟨by simpa using hu.2.2, hu.1⟩
  have hSn : S.Nonempty := ⟨wE, by simp [S, hwmem, hw0]⟩
  rcases Set.exists_min_image S (fun u : E => ‖u‖) hSfin hSn with ⟨v, hvS, hvmin⟩
  refine ⟨v, hvS.1, hvS.2.1, ?_⟩
  intro u huL hu0
  by_cases hle : ‖u‖ ≤ ‖wE‖
  · exact hvmin u ⟨huL, hu0, hle⟩
  · have hwle : ‖wE‖ ≤ ‖u‖ := by linarith
    exact le_trans hvS.2.2 hwle

/-- For a shortest vector, any lattice point on its real line is an integer multiple. -/
lemma shortest_pure_exists {L : Submodule ℤ E} {v : E} (hvL : v ∈ L)
    (hmin : ∀ u : E, u ∈ L → u ≠ 0 → ‖v‖ ≤ ‖u‖) (hv0 : v ≠ 0) :
    ∀ (y : E), y ∈ L → y ∈ span ℝ ({v} : Set E) → ∃ n : ℤ, y = (n : ℤ) • v := by
  intro y hyL hyRs
  rcases (mem_span_singleton.mp hyRs) with ⟨c, hc⟩
  let k : ℤ := Int.floor c
  let s : ℝ := Int.fract c
  have hcdec : c = (k : ℝ) + s := by
    dsimp [k, s]
    exact (Int.floor_add_fract c).symm
  have hcast : ((k : ℤ) • v) = ((k : ℝ) • v) := (Int.cast_smul_eq_zsmul (R := ℝ) k v).symm
  have hkL : (k : ℤ) • v ∈ L := Submodule.smul_mem L (k : ℤ) hvL
  have hzmem : y - (k : ℤ) • v ∈ L := Submodule.sub_mem L hyL hkL
  have hys : y - (k : ℤ) • v = s • v := by
    calc
      y - (k : ℤ) • v = (c : ℝ) • v - (k : ℝ) • v := by rw [← hc, hcast]
      _ = (c - (k : ℝ)) • v := by rw [← sub_smul]
      _ = s • v := by
        congr 1


  have hmemS : s • v ∈ L := by simpa [hys] using hzmem
  by_cases hs : s = 0
  · refine ⟨k, ?_⟩
    rw [← hc, hcdec, hs]
    simpa using hcast.symm
  · exfalso
    have hs0 : 0 < s := by
      dsimp [s]
      exact lt_of_le_of_ne (Int.fract_nonneg c) (Ne.symm hs)
    have hs1 : s < 1 := by
      dsimp [s]
      exact Int.fract_lt_one c
    have hnorm : ‖s • v‖ < ‖v‖ := by
      have hnorm' : ‖s • v‖ = s * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      rw [hnorm']
      simpa using (mul_lt_mul_of_pos_right hs1 (norm_pos_iff.mpr hv0))
    have hne : s • v ≠ 0 := by
      intro hz
      have hv0' : v = 0 := by
        calc
          v = (1 : ℝ) • v := by simp
          _ = (s⁻¹ * s) • v := by
            congr 1
            field_simp [hs0]
          _ = s⁻¹ • (s • v) := by rw [← smul_smul]
          _ = s⁻¹ • 0 := by rw [hz]
          _ = 0 := by simp
      exact hv0 hv0'
    exact (lt_irrefl ‖v‖) (lt_of_le_of_lt (hmin (s • v) hmemS hne) hnorm)

/-- A shortest vector is primitive: lattice points in its real span lie in its ℤ-span. -/
lemma shortest_pure {L : Submodule ℤ E} {v : E} (hvL : v ∈ L)
    (hmin : ∀ u : E, u ∈ L → u ≠ 0 → ‖v‖ ≤ ‖u‖) (hv0 : v ≠ 0) :
    ∀ (y : E), y ∈ L → y ∈ span ℝ ({v} : Set E) → y ∈ span ℤ ({v} : Set E) := by
  intro y hyL hyRs
  rcases shortest_pure_exists hvL hmin hv0 y hyL hyRs with ⟨n, hn⟩
  exact Submodule.mem_span_singleton.mpr ⟨n, hn.symm⟩

/-- Short nonzero vector whose norm is ≤ 4·finrank, given the dual has first minimum ≥ 1. -/
lemma shortVector_of_hmin (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hmin : ∀ ⦃y : E⦄, y ∈ ldual E L → y ≠ 0 → 1 ≤ ‖y‖)
    (hd : 1 ≤ finrank ℝ E) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ (∀ u : E, u ∈ L → u ≠ 0 → ‖v‖ ≤ ‖u‖) ∧
      ‖v‖ ≤ 4 * (finrank ℝ E : ℝ) := by
  classical
  let d : ℕ := finrank ℝ E
  let e : ℝ := (1 : ℝ) / (d : ℝ)
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let bz : Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let b := bz.ofZLatticeBasis ℝ
  let db := (euclForm E).dualBasis (euclForm_nondegenerate E) b
  have hd0n : 0 < d := by dsimp [d]; exact lt_of_lt_of_le zero_lt_one hd
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd0n
  have hspan : span ℤ (Set.range b) = L := Module.Basis.ofZLatticeBasis_span ℝ L bz
  have hdual : ldual E L = span ℤ (Set.range db) := by
    rw [← hspan]
    exact ldual_span_basis b
  have hmuB : volume.real (ZSpan.fundamentalDomain b) = ZLattice.covolume L := by
    exact (covol_eq_fund L bz).symm
  -- D := covolume of the dual span-lattice
  have hcovD : ZLattice.covolume (span ℤ (Set.range db)) = volume.real (ZSpan.fundamentalDomain db) :=
    covolume_span_basis db
  have hduality : (ZLattice.covolume L) * (ZLattice.covolume (span ℤ (Set.range db))) = 1 := by
    rw [← hmuB, hcovD]
    exact covolume_dual_basis b
  -- dual side: short nonzero w ∈ ldual E L
  obtain ⟨wE, hwL', hw0, hwbd⟩ := exists_short_lattice (span ℤ (Set.range db)) hd
  have hwdual : wE ∈ ldual E L := by
    rwa [hdual]  -- hmm direction
  have hw1 : 1 ≤ ‖wE‖ := hmin hwdual hw0
  -- norm bounds with rpow
  have hwle : ‖wE‖ ≤ 2 * Real.sqrt (d : ℝ) *
      (ZLattice.covolume (span ℤ (Set.range db))) ^ e := by
    simpa [d, e] using hwbd
  have hpowd0 : 0 < (2 : ℝ) * Real.sqrt (d : ℝ) := by positivity
  -- D := covol(dual): from 1 ≤ ‖wE‖ ≤ 2√d·D^e get D^e ≥ 1/(2√d), C^e ≤ 2√d
  let Cdual : ℝ := ZLattice.covolume (span ℤ (Set.range db))
  have hCdual0 : 0 < Cdual := by
    dsimp [Cdual]
    exact ZLattice.covolume_pos (μ := volume) (span ℤ (Set.range db))
  have hCe : (ZLattice.covolume L) ^ e ≤ 2 * Real.sqrt (d : ℝ) := by
    let C : ℝ := ZLattice.covolume L
    let D : ℝ := Cdual
    have hC0 : 0 < C := by dsimp [C]; exact ZLattice.covolume_pos (μ := volume) L
    have hD0 : 0 < D := by dsimp [D, Cdual]; exact ZLattice.covolume_pos (μ := volume) (span ℤ (Set.range db))
    have hCD : C * D = 1 := by
      dsimp [C, D, Cdual]
      exact hduality
    have hCinv : C = D⁻¹ := eq_inv_of_mul_eq_one_left hCD
    have h1 : 1 ≤ (2 * Real.sqrt (d : ℝ)) * D ^ e := by
      exact le_trans hw1 (by
        simpa [D, Cdual, d, e] using hwle)
    have hq : 0 < D ^ e := Real.rpow_pos_of_pos hD0 e
    have hlinv : (D ^ e)⁻¹ ≤ 2 * Real.sqrt (d : ℝ) := by
      have hm : (1 : ℝ) * (D ^ e)⁻¹ ≤ ((2 * Real.sqrt (d : ℝ)) * (D ^ e)) * (D ^ e)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (le_of_lt hq))
      have hsq : ((2 * Real.sqrt (d : ℝ)) * (D ^ e)) * (D ^ e)⁻¹ = (2 * Real.sqrt (d : ℝ)) := by
        field_simp [hq.ne']
      simpa [hsq] using hm
    have hCe' : C ^ e ≤ 2 * Real.sqrt (d : ℝ) := by
      rw [hCinv]
      have hpow : (D⁻¹) ^ e = (D ^ e)⁻¹ := by
        have hnonneg : 0 ≤ D⁻¹ := inv_nonneg.mpr (le_of_lt hD0)
        have hprod : (D⁻¹) ^ e * (D ^ e) = 1 := by
          rw [← Real.mul_rpow hnonneg (le_of_lt hD0)]
          rw [inv_mul_cancel₀ hD0.ne']
          rw [Real.one_rpow]
        exact eq_inv_of_mul_eq_one_left hprod
      rw [hpow]
      exact hlinv
    simpa [C] using hCe' 
  obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_vector L hd
  obtain ⟨uE, huL, hu0, hubd⟩ := exists_short_lattice L hd
  have hvu : ‖v‖ ≤ ‖uE‖ := hvmin uE huL hu0
  have hule : ‖uE‖ ≤ 2 * Real.sqrt (d : ℝ) * (ZLattice.covolume L) ^ e := by
    simpa [d, e] using hubd
  have hvb : ‖v‖ ≤ 4 * (d : ℝ) := by
    have hsqrt : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ))
    calc
      ‖v‖ ≤ 2 * Real.sqrt (d : ℝ) * (ZLattice.covolume L) ^ e := le_trans hvu hule
      _ ≤ 2 * Real.sqrt (d : ℝ) * (2 * Real.sqrt (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hCe (by positivity)
      _ = 4 * (d : ℝ) := by
        rw [show 2 * Real.sqrt (d : ℝ) * (2 * Real.sqrt (d : ℝ)) =
            4 * (Real.sqrt (d : ℝ)) ^ 2 by ring]
        rw [hsqrt]
  refine ⟨v, hvL, hv0, hvmin, ?_⟩
  dsimp [d] at hvb ⊢
  exact hvb

end ShortVec

end Submission.CovShort
