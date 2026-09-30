import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Torsion.exists_fibreNormLike
import Submission.Work.Thom.Continuous

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The geometric model of the Thom space `Th γ = OnePoint (TotalSpace γ)`

The target `Work.ThomBordism.Grassmann.ThomSpaceTorsionDetected` is about the metric-free Thom space
`T = OnePoint E`, `E = (tautologicalBundle k m).TotalSpace`.  This file fixes the geometric
vocabulary used by the comparison of the (co)homology of `T` with the relative cohomology of the
Thom pair `(E, E∖0)`:

* `fibN` — the *only* structure on the fibres that is used: a continuous, fibrewise-norm-like
  function `E → ℝ`, extracted from `exists_fibreNormLike` (`fibN_continuous`, `fibN_nonneg`,
  `fibN_smul`, `fibN_eq_zero_iff`, `isCompact_fibN_le_one`);
* `far c ⊆ T` — the "beyond radius `c`" part `{f > c} ∪ {∞}`, an *open* neighbourhood of `∞`
  (`isOpen_far`) whose complement `{f ≤ c}` is compact (`isCompact_fibN_le`);
* `near c ⊆ T` — the "inside radius `c`" part `{f < c}` (`isOpen_near`);
* the covering relation `near c ∪ far 1 = univ` for `1 < c` (`near_union_far`) and the description of
  the overlap `near 2 ∩ far 1 = {1 < f < 2}` (`near_inter_far`);
* the homeomorphism `near c ≃ₜ {f < c}` (and its relative form) induced by the open embedding
  `OnePoint.some` (`homeoNear`, `homeoNearInterFar`).

The remaining geometric facts — contractibility of `far 1` (equivalently the vanishing of its
positive-degree cohomology, by the scaling homotopy `p ↦ (1-t)⁻¹ • p` whose continuity at `∞` is
exactly the properness of `f`) and the radial deformation retractions of `{f < 2}` onto the zero
section — are stated with the help of this vocabulary in the companion files of this directory.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The total space of the tautological oriented bundle. -/
abbrev TM (k m : ℕ) : Type := (tautologicalBundle k m).TotalSpace

/-- The one-point compactification, the "metric-free" Thom space of the chapter. -/
abbrev TP (k m : ℕ) : Type := OnePoint (tautologicalBundle k m).TotalSpace

/-- **The fibrewise-norm-like function** on the total space of the tautological bundle: a chosen
witness of `exists_fibreNormLike`.  All the scaling/radial geometry of the chapter is expressed in
terms of it. -/
noncomputable def fibN (k m : ℕ) : TM k m → ℝ := Classical.choose (exists_fibreNormLike k m)

theorem fibN_spec (k m : ℕ) :
    Continuous (fibN k m) ∧ (∀ p : TM k m, 0 ≤ fibN k m p) ∧
      (∀ (c : ℝ) (p : TM k m), 0 ≤ c → fibN k m ⟨p.1, c • p.2⟩ = c * fibN k m p) ∧
      (∀ p : TM k m, fibN k m p = 0 ↔ p.2 = 0) ∧ IsCompact {p : TM k m | fibN k m p ≤ 1} :=
  Classical.choose_spec (exists_fibreNormLike k m)

theorem fibN_continuous (k m : ℕ) : Continuous (fibN k m) := (fibN_spec k m).1

theorem fibN_nonneg (k m : ℕ) (p : TM k m) : 0 ≤ fibN k m p := (fibN_spec k m).2.1 p

theorem fibN_smul (k m : ℕ) {c : ℝ} (hc : 0 ≤ c) (p : TM k m) :
    fibN k m ⟨p.1, c • p.2⟩ = c * fibN k m p := (fibN_spec k m).2.2.1 c p hc

theorem fibN_eq_zero_iff (k m : ℕ) (p : TM k m) : fibN k m p = 0 ↔ p.2 = 0 :=
  (fibN_spec k m).2.2.2.1 p

theorem isCompact_fibN_le_one (k m : ℕ) : IsCompact {p : TM k m | fibN k m p ≤ 1} :=
  (fibN_spec k m).2.2.2.2

/-- The sublevel sets at radius `≤ 1` are compact: they are closed subsets of `{fibN ≤ 1}`. -/
theorem isCompact_fibN_le_of_le_one (k m : ℕ) {c : ℝ} (hc : c ≤ 1) :
    IsCompact {p : TM k m | fibN k m p ≤ c} := by
  refine (isCompact_fibN_le_one k m).of_isClosed_subset
    (isClosed_le (fibN_continuous k m) continuous_const) ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  exact le_trans hp hc

/-- **Fibrewise rescaling** of the total space: `p ↦ ⟨p.1, c • p.2⟩` is continuous (a special case
of `Work.Thom.continuous_smul_section`). -/
theorem continuous_scale (k m : ℕ) (c : ℝ) :
    Continuous fun p : TM k m => (⟨p.1, c • p.2⟩ : TM k m) :=
  Work.Thom.continuous_smul_section (tautologicalBundle k m) (ContinuousMap.id _)
    (ContinuousMap.const _ c)

/-- The scaling map `p ↦ ⟨p.1, c • p.2⟩` is continuous. -/
theorem continuous_scaleFun (k m : ℕ) (c : ℝ) :
    Continuous (fun p : TM k m => (⟨p.1, c • p.2⟩ : TM k m)) := continuous_scale k m c

/-- **The sublevel sets of `fibN` are compact**, for every radius: for `c ≤ 1` they are closed
subsets of the compact `{fibN ≤ 1}`, and for `c > 0` the level set `{fibN ≤ c}` is the image of
`{fibN ≤ 1}` under the continuous fibrewise scaling by `c`. -/
theorem isCompact_fibN_le (k m : ℕ) (c : ℝ) : IsCompact {p : TM k m | fibN k m p ≤ c} := by
  rcases lt_or_ge c 1 with hc | hc
  · exact isCompact_fibN_le_of_le_one k m hc.le
  · have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
    have himg : (fun p : TM k m => (⟨p.1, c • p.2⟩ : TM k m)) '' {p : TM k m | fibN k m p ≤ 1}
        = {p : TM k m | fibN k m p ≤ c} := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rw [Set.mem_ofPred_eq] at hq ⊢
        rw [fibN_smul k m hcpos.le q]
        exact mul_le_of_le_one_right hcpos.le hq
      · intro hp
        rw [Set.mem_ofPred_eq] at hp
        refine ⟨⟨p.1, c⁻¹ • p.2⟩, ?_, ?_⟩
        · rw [Set.mem_ofPred_eq, fibN_smul k m (inv_nonneg.mpr hcpos.le) p]
          rw [inv_mul_le_iff₀ hcpos]
          simpa using hp
        · show (⟨p.1, c • (c⁻¹ • p.2)⟩ : TM k m) = p
          rw [smul_inv_smul₀ (ne_of_gt hcpos)]
    rw [← himg]
    exact (isCompact_fibN_le_one k m).image (continuous_scale k m c)

/-- `fibN` is bounded above on compact subsets of the total space. -/
theorem exists_fibN_bound_of_compact (k m : ℕ) (K : Set (TM k m)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ p ∈ K, fibN k m p ≤ M := by
  rcases Set.eq_empty_or_nonempty K with h | h
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨p₀, -, hmax⟩ := hK.exists_isMaxOn h (fibN_continuous k m).continuousOn
    exact ⟨fibN k m p₀, fun p hp => hmax hp⟩

/-- **The "beyond radius `c`" part of the Thom space**: the points of the total space with
`fibN > c`, together with the point at infinity. -/
def far (k m : ℕ) (c : ℝ) : Set (OnePoint (tautologicalBundle k m).TotalSpace) :=
  OnePoint.some '' {p : TM k m | c < fibN k m p} ∪ {OnePoint.infty}

/-- **The "inside radius `c`" part of the Thom space**: the points of the total space with
`fibN < c`. -/
def near (k m : ℕ) (c : ℝ) : Set (OnePoint (tautologicalBundle k m).TotalSpace) :=
  OnePoint.some '' {p : TM k m | fibN k m p < c}

theorem some_mem_far_iff (k m : ℕ) (c : ℝ) (p : TM k m) :
    OnePoint.some p ∈ far k m c ↔ c < fibN k m p := by
  constructor
  · rintro (⟨q, hq, hqp⟩ | h)
    · rw [← Option.some.inj hqp]; exact hq
    · exact absurd h (by simp)
  · exact fun h => Or.inl ⟨p, h, rfl⟩

theorem some_mem_near_iff (k m : ℕ) (c : ℝ) (p : TM k m) :
    OnePoint.some p ∈ near k m c ↔ fibN k m p < c := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← Option.some.inj hqp]; exact hq
  · exact fun h => ⟨p, h, rfl⟩

theorem infty_mem_far (k m : ℕ) (c : ℝ) : (OnePoint.infty : TP k m) ∈ far k m c :=
  Or.inr rfl

theorem infty_notMem_near (k m : ℕ) (c : ℝ) : (OnePoint.infty : TP k m) ∉ near k m c := by
  rintro ⟨p, -, h⟩
  exact Option.some_ne_none p h

theorem some_preimage_far (k m : ℕ) (c : ℝ) :
    OnePoint.some ⁻¹' (far k m c) = {p : TM k m | c < fibN k m p} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, some_mem_far_iff]

theorem some_preimage_near (k m : ℕ) (c : ℝ) :
    OnePoint.some ⁻¹' (near k m c) = {p : TM k m | fibN k m p < c} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, some_mem_near_iff]

/-- **`far c` is open** in the one-point compactification for `c ≤ 1`: its complement is the image
of the compact set `{fibN ≤ c}`. -/
theorem isOpen_far_of_le_one (k m : ℕ) {c : ℝ} (hc : c ≤ 1) : IsOpen (far k m c) := by
  rw [OnePoint.isOpen_def]
  refine ⟨fun _ => ?_, ?_⟩
  · rw [some_preimage_far]
    rw [show {p : TM k m | c < fibN k m p}ᶜ = {p : TM k m | fibN k m p ≤ c} from by
      ext p; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]]
    exact isCompact_fibN_le_of_le_one k m hc
  · rw [some_preimage_far]
    exact isOpen_lt continuous_const (fibN_continuous k m)

/-- **`far 1` is open**. -/
theorem isOpen_far_one (k m : ℕ) : IsOpen (far k m 1) := isOpen_far_of_le_one k m le_rfl

/-- **`near c` is open**: it is the image of the open set `{fibN < c}` under the open embedding
`OnePoint.some`. -/
theorem isOpen_near (k m : ℕ) (c : ℝ) : IsOpen (near k m c) := by
  rw [OnePoint.isOpen_def]
  refine ⟨fun h => absurd h (infty_notMem_near k m c), ?_⟩
  rw [some_preimage_near]
  exact isOpen_lt (fibN_continuous k m) continuous_const

/-- `near c` and `far 1` cover the Thom space, for `1 < c`. -/
theorem near_union_far (k m : ℕ) {c : ℝ} (hc : 1 < c) : near k m c ∪ far k m 1 = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x = OnePoint.infty
    · exact Or.inr (Or.inr hx)
    · obtain ⟨p, rfl⟩ : ∃ p : TM k m, OnePoint.some p = x := by
        cases x with
        | infty => exact absurd rfl hx
        | coe p => exact ⟨p, rfl⟩
      rw [Set.mem_union, some_mem_near_iff, some_mem_far_iff]
      by_cases h : fibN k m p < c
      · exact Or.inl h
      · exact Or.inr (lt_of_lt_of_le hc (le_of_not_gt h))

/-- The overlap of the two sets of the cover: `near 2 ∩ far 1 = {1 < fibN < 2}`. -/
theorem near_inter_far (k m : ℕ) :
    near k m 2 ∩ far k m 1
      = OnePoint.some '' {p : TM k m | 1 < fibN k m p ∧ fibN k m p < 2} := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with ⟨p, hp, rfl⟩
    exact ⟨p, ⟨(some_mem_far_iff k m 1 p).mp h2, hp⟩, rfl⟩
  · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact ⟨(some_mem_near_iff k m 2 p).mpr hp2, (some_mem_far_iff k m 1 p).mpr hp1⟩

/-- `near c` is contained in the range of the open embedding `OnePoint.some`. -/
theorem near_subset_range (k m : ℕ) (c : ℝ) :
    near k m c ⊆ Set.range (OnePoint.some : TM k m → OnePoint (tautologicalBundle k m).TotalSpace) :=
  fun x hx => by rcases hx with ⟨p, -, rfl⟩; exact ⟨p, rfl⟩

/-- The preimage of `near c` under `OnePoint.some`. -/
theorem some_preimage_near_eq (k m : ℕ) (c : ℝ) :
    OnePoint.some ⁻¹' (near k m c) = {p : TM k m | fibN k m p < c} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, some_mem_near_iff]

theorem near_inter_far_subset_range (k m : ℕ) :
    near k m 2 ∩ far k m 1
      ⊆ Set.range (OnePoint.some : TM k m → OnePoint (tautologicalBundle k m).TotalSpace) :=
  fun x hx => by rcases hx.1 with ⟨p, -, rfl⟩; exact ⟨p, rfl⟩

theorem some_preimage_near_inter_far_eq (k m : ℕ) :
    OnePoint.some ⁻¹' (near k m 2 ∩ far k m 1)
      = {p : TM k m | 1 < fibN k m p ∧ fibN k m p < 2} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, some_mem_near_iff,
    some_mem_far_iff]
  tauto

/-- **The homeomorphism `{fibN < c} ≃ₜ near c`** induced by the open embedding
`OnePoint.some`, built from `IsEmbedding.homeomorphOfSubsetRange` so that its values are
transparent. -/
noncomputable def homeoNear (k m : ℕ) (c : ℝ) :
    ↥{p : TM k m | fibN k m p < c} ≃ₜ ↥(near k m c) :=
  (Homeomorph.setCongr (some_preimage_near_eq k m c).symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange (near_subset_range k m c))

theorem homeoNear_apply_coe (k m : ℕ) (c : ℝ)
    (p : ↥{p : TM k m | fibN k m p < c}) :
    ((homeoNear k m c p : ↥(near k m c)) : OnePoint (tautologicalBundle k m).TotalSpace)
      = OnePoint.some p.val := by
  unfold homeoNear
  rw [Homeomorph.trans_apply, Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe]
  rfl

/-- **The homeomorphism `{1 < fibN < 2} ≃ₜ near 2 ∩ far 1`** induced by `OnePoint.some`. -/
noncomputable def homeoNearInterFar (k m : ℕ) :
    ↥{p : TM k m | 1 < fibN k m p ∧ fibN k m p < 2} ≃ₜ ↥(near k m 2 ∩ far k m 1) :=
  (Homeomorph.setCongr (some_preimage_near_inter_far_eq k m).symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange
      (near_inter_far_subset_range k m))

theorem homeoNearInterFar_apply_coe (k m : ℕ)
    (p : ↥{p : TM k m | 1 < fibN k m p ∧ fibN k m p < 2}) :
    ((homeoNearInterFar k m p : ↥(near k m 2 ∩ far k m 1)) :
      OnePoint (tautologicalBundle k m).TotalSpace) = OnePoint.some p.val := by
  unfold homeoNearInterFar
  rw [Homeomorph.trans_apply, Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe]
  rfl

end

end Work.ThomBordism.Grassmann.Torsion