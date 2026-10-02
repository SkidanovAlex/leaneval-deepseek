import Mathlib
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The slab structure on the punctured total space of a real vector bundle

This file sets up the vocabulary for the proof that the punctured total space `E ∖ 0` of a real
vector bundle over a paracompact Hausdorff base is paracompact (the target of
`Submission/Work/Gen/puncturedParacompactT2.lean`).

The proof goes through the general topological lemma `Work.Gen.paracompactSpace_of_compact_slabs`
(in `Submission/Work/Gen/paracompactSpace_of_compact_slabs.lean`): a space `X` with a continuous map
`π : X → B` to a paracompact base, together with a family of "slabs" `K j ⊆ O j` (`j : ℤ`) such that

* the `K j` cover `X`,
* each `K j ∩ π ⁻¹' {b}` is compact, and the tube property holds,
* the slabs "escape to infinity": every point has a neighbourhood meeting only finitely many of
  the open enlargements `O j`,

is paracompact.

For a vector bundle `Z` the slabs are dyadically indexed on a **weighted fibrewise norm**.  The
bundle is *not* assumed Euclidean, so there is no canonical fibrewise norm; instead one uses

`slabNu Z φ p = ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖`,

where `φ i : C(B, ℝ)` is a chart-subordinate partition of unity (non-negative functions whose
support closures lie in the chart set `Z.baseSet i`) and `(Z.localTriv i p).2` is the fibre
coordinate of `p` in the chart `i`.  The support condition is what makes `slabNu` continuous, even
though the fibre coordinate in a chart whose base set does not contain `p.1` is defined by junk.

## Main definitions

* `Work.Gen.Punct Z` — the punctured total space `E ∖ 0`, as a subspace of the total space;
* `Work.Gen.punctProj Z` — the projection `E ∖ 0 → B`;
* `Work.Gen.slabNu Z φ` — the weighted norm `ν`;
* `Work.Gen.slabTot Z φ j` — the slab `{p : 2^j ≤ ν p ≤ 2^(j+1)}` in the total space;
* `Work.Gen.slabTotOpen Z φ j` — its open enlargement `{p : 2^j/2 < ν p < 2·2^(j+1)}`;
* `Work.Gen.slabK Z φ j`, `Work.Gen.slabO Z φ j` — the same inside the punctured space.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom
open scoped Topology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-- The punctured total space `E ∖ 0` of a real bundle, as a subspace of the total space. -/
abbrev Punct (Z : RealBundle B F ι) : Type _ := ↥(Work.Thom.zeroComplement Z)

/-- The projection of the punctured total space onto the base. -/
def punctProj (Z : RealBundle B F ι) : C(Punct Z, B) :=
  ⟨fun x => (x : Z.TotalSpace).1, Z.continuous_proj.comp continuous_subtype_val⟩

@[simp] theorem punctProj_apply (Z : RealBundle B F ι) (x : Punct Z) :
    punctProj Z x = (x : Z.TotalSpace).1 := rfl

variable [Fintype ι]

/-- The weighted fibrewise norm `ν p = ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖`. -/
def slabNu (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (p : Z.TotalSpace) : ℝ :=
  ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖

/-- The slab `{p : 2^j ≤ ν p ≤ 2^(j+1)}` of the total space. -/
def slabTot (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) : Set Z.TotalSpace :=
  {p | (2 : ℝ) ^ j ≤ slabNu Z φ p ∧ slabNu Z φ p ≤ (2 : ℝ) ^ (j + 1)}

/-- The open enlargement `{p : 2^j/2 < ν p < 2·2^(j+1)}` of the slab `slabTot Z φ j`. -/
def slabTotOpen (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) : Set Z.TotalSpace :=
  {p | (2 : ℝ) ^ j / 2 < slabNu Z φ p ∧ slabNu Z φ p < 2 * (2 : ℝ) ^ (j + 1)}

/-- The slab of the punctured total space. -/
def slabK (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) : Set (Punct Z) :=
  {x | (x : Z.TotalSpace) ∈ slabTot Z φ j}

/-- The open enlargement of the slab of the punctured total space. -/
def slabO (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) : Set (Punct Z) :=
  {x | (x : Z.TotalSpace) ∈ slabTotOpen Z φ j}

@[simp] theorem mem_slabTot (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ)
    (p : Z.TotalSpace) :
    p ∈ slabTot Z φ j ↔ (2 : ℝ) ^ j ≤ slabNu Z φ p ∧ slabNu Z φ p ≤ (2 : ℝ) ^ (j + 1) :=
  Iff.rfl

@[simp] theorem mem_slabTotOpen (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ)
    (p : Z.TotalSpace) :
    p ∈ slabTotOpen Z φ j ↔
      (2 : ℝ) ^ j / 2 < slabNu Z φ p ∧ slabNu Z φ p < 2 * (2 : ℝ) ^ (j + 1) :=
  Iff.rfl

@[simp] theorem mem_slabK (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) (x : Punct Z) :
    x ∈ slabK Z φ j ↔ (2 : ℝ) ^ j ≤ slabNu Z φ (x : Z.TotalSpace) ∧
      slabNu Z φ (x : Z.TotalSpace) ≤ (2 : ℝ) ^ (j + 1) :=
  Iff.rfl

@[simp] theorem mem_slabO (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) (x : Punct Z) :
    x ∈ slabO Z φ j ↔ (2 : ℝ) ^ j / 2 < slabNu Z φ (x : Z.TotalSpace) ∧
      slabNu Z φ (x : Z.TotalSpace) < 2 * (2 : ℝ) ^ (j + 1) :=
  Iff.rfl

theorem slabK_eq_preimage (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) :
    slabK Z φ j = Subtype.val ⁻¹' slabTot Z φ j := rfl

theorem slabO_eq_preimage (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) :
    slabO Z φ j = Subtype.val ⁻¹' slabTotOpen Z φ j := rfl

/-- Every slab is contained in its open enlargement. -/
theorem slabTot_subset_slabTotOpen (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) :
    slabTot Z φ j ⊆ slabTotOpen Z φ j := by
  intro p hp
  rw [mem_slabTot] at hp
  rw [mem_slabTotOpen]
  have h1 : (0:ℝ) < (2:ℝ) ^ j := zpow_pos (by norm_num) j
  have h2 : (0:ℝ) < (2:ℝ) ^ (j + 1) := zpow_pos (by norm_num) (j + 1)
  constructor <;> linarith [hp.1, hp.2]

theorem slabK_subset_slabO (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (j : ℤ) :
    slabK Z φ j ⊆ slabO Z φ j := fun x hx => slabTot_subset_slabTotOpen Z φ j hx

/-! ## Elementary properties of `slabNu` -/

/-- The fibre component of a point of the total space, as an element of the model fibre. -/
noncomputable def slabVec (Z : RealBundle B F ι) (p : Z.TotalSpace) : F :=
  (show F from (p.2 : Z.Fiber p.1))

/-- The fibre component vanishes exactly on the zero section. -/
theorem slabVec_eq_zero_iff (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    slabVec Z p = 0 ↔ p ∉ Work.Thom.zeroComplement Z := by
  constructor
  · intro h hmem
    exact (Work.Thom.mem_zeroComplement p).mp hmem h
  · intro hp
    by_contra hne
    exact hp ((Work.Thom.mem_zeroComplement p).mpr hne)

theorem slabVec_ne_zero_iff (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    slabVec Z p ≠ 0 ↔ p ∈ Work.Thom.zeroComplement Z := by
  constructor
  · intro h
    by_contra hc
    exact h ((slabVec_eq_zero_iff Z p).mpr hc)
  · intro hp hsv
    exact (slabVec_eq_zero_iff Z p).mp hsv hp

@[simp] theorem slabNu_mk (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (b : B) (v : F) :
    slabNu Z φ (⟨b, v⟩ : Z.TotalSpace) =
      ∑ i, φ i b * ‖Z.coordChange (Z.indexAt b) i b v‖ := by
  simp only [slabNu, VectorBundleCore.localTriv_apply]

/-- **Homogeneity of `slabNu` in the fibre**: `ν` of a scaled vector is `|c| · ν`. -/
theorem slabNu_smul (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (b : B) (c : ℝ) (v : F) :
    slabNu Z φ (⟨b, c • v⟩ : Z.TotalSpace) = |c| * slabNu Z φ (⟨b, v⟩ : Z.TotalSpace) := by
  rw [slabNu_mk, slabNu_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  ring

/-- Homogeneity of `slabNu` in the fibre, in the form used for the tube property. -/
theorem slabNu_smul' (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (b : B) (c : ℝ) (v : F) :
    slabNu Z φ (⟨b, c • v⟩ : Z.TotalSpace) = |c| * slabNu Z φ (⟨b, v⟩ : Z.TotalSpace) :=
  slabNu_smul Z φ b c v

theorem slabNu_nonneg (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (hnn : ∀ i b, 0 ≤ φ i b)
    (p : Z.TotalSpace) : 0 ≤ slabNu Z φ p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hnn i p.1) (norm_nonneg _)

/-- In a chart containing `p.1`, the fibre coordinate vanishes exactly at the zero section. -/
theorem localTriv_snd_eq_zero_iff (Z : RealBundle B F ι) (i : ι) (p : Z.TotalSpace)
    (hp : p.1 ∈ Z.baseSet i) :
    (Z.localTriv i p).2 = 0 ↔ slabVec Z p = 0 := by
  rw [slabVec_eq_zero_iff, Work.Thom.mem_zeroComplement]
  have h : (Z.localTriv i p).2 = ((Z.localTriv i).linearEquivAt ℝ p.1 hp) (show F from p.2) := by
    rw [Bundle.Trivialization.linearEquivAt_apply]
  rw [h, LinearEquiv.map_eq_zero_iff]
  simp

/-- The fibre coordinate in any chart vanishes off the punctured total space. -/
theorem localTriv_snd_eq_zero_of_slabVec_eq_zero (Z : RealBundle B F ι) (i : ι)
    (p : Z.TotalSpace) (hp : slabVec Z p = 0) : (Z.localTriv i p).2 = 0 := by
  have hzero : (show F from (p.2 : Z.Fiber p.1)) = 0 := hp
  have h1 : Z.coordChange (Z.indexAt p.1) i p.1 (show F from (p.2 : Z.Fiber p.1)) =
      Z.coordChange (Z.indexAt p.1) i p.1 0 := congrArg _ hzero
  rw [map_zero] at h1
  rw [VectorBundleCore.localTriv_apply]
  exact h1

/-- `ν` vanishes exactly on the zero section. -/
theorem slabNu_eq_zero_iff (Z : RealBundle B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (p : Z.TotalSpace) :
    slabNu Z φ p = 0 ↔ slabVec Z p = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, 0 < φ i p.1 := by
      by_contra hc
      push Not at hc
      have hsum : ∑ i, φ i p.1 = 0 :=
        Finset.sum_eq_zero fun i _ => le_antisymm (hc i) (hnn i p.1)
      have := hpos p.1
      rw [hsum] at this
      exact lt_irrefl 0 this
    have hbs : p.1 ∈ Z.baseSet i :=
      hφ i (subset_tsupport (φ i) (Function.mem_support.mpr hi.ne'))
    have hcoord : (Z.localTriv i p).2 ≠ 0 :=
      fun hq => hne ((localTriv_snd_eq_zero_iff Z i p hbs).mp hq)
    have hterm : 0 < φ i p.1 * ‖(Z.localTriv i p).2‖ :=
      mul_pos hi (norm_pos_iff.mpr hcoord)
    have hle : φ i p.1 * ‖(Z.localTriv i p).2‖ ≤ slabNu Z φ p := by
      have := Finset.single_le_sum (f := fun j => φ j p.1 * ‖(Z.localTriv j p).2‖)
        (fun j _ => mul_nonneg (hnn j p.1) (norm_nonneg _)) (Finset.mem_univ i)
      simpa only [slabNu] using this
    rw [h] at hle
    exact lt_irrefl 0 (lt_of_lt_of_le hterm hle)
  · intro hp
    simp only [slabNu]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [localTriv_snd_eq_zero_of_slabVec_eq_zero Z i p hp, norm_zero, mul_zero]

/-- `ν` is positive exactly on the punctured total space. -/
theorem slabNu_pos (Z : RealBundle B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (p : Z.TotalSpace) :
    0 < slabNu Z φ p ↔ slabVec Z p ≠ 0 := by
  rcases eq_or_lt_of_le (slabNu_nonneg Z φ hnn p) with h | h
  · have h0 : slabNu Z φ p = 0 := h.symm
    rw [h0, (slabNu_eq_zero_iff Z φ hφ hnn hpos p).mp h0]
    simp
  · exact ⟨fun _ => fun hsv => (ne_of_gt h) ((slabNu_eq_zero_iff Z φ hφ hnn hpos p).mpr hsv),
      fun _ => h⟩

theorem slabNu_pos_of_mem (Z : RealBundle B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (x : Punct Z) :
    0 < slabNu Z φ (x : Z.TotalSpace) :=
  (slabNu_pos Z φ hφ hnn hpos _).mpr ((slabVec_ne_zero_iff Z _).mpr x.2)

/-! ## The dyadic slab of a point, and escape to infinity -/

/-- `logb 2 (2^j) = j` for an integer exponent. -/
theorem logb_two_zpow (j : ℤ) : Real.logb 2 ((2:ℝ) ^ j) = (j : ℝ) := by
  have h : ((2:ℝ) ^ j) = (2:ℝ) ^ ((j : ℝ)) := (Real.rpow_intCast 2 j).symm
  rw [h, Real.logb_rpow (b := 2) (by norm_num) (by norm_num)]

/-- `2 * 2^(j+1) = 2^(j+2)`. -/
theorem two_mul_zpow_two (j : ℤ) : 2 * (2:ℝ) ^ (j + 1) = (2:ℝ) ^ (j + 2) := by
  have h : (2:ℝ) ^ (j + 2) = 2 * (2:ℝ) ^ (j + 1) := by
    rw [show (j : ℤ) + 2 = 1 + (j + 1) by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
      zpow_one]
  rw [h]

/-- For every positive real `t` there is a dyadic slab `[2^j, 2^(j+1)]` containing it. -/
theorem exists_zpow_le_and_le (t : ℝ) (ht : 0 < t) :
    ∃ j : ℤ, (2:ℝ) ^ j ≤ t ∧ t ≤ (2:ℝ) ^ (j + 1) := by
  refine ⟨⌊Real.logb 2 t⌋, ?_, ?_⟩
  · have h := Real.rpow_logb (b := 2) (by norm_num) (by norm_num) ht
    have hle : (2:ℝ) ^ (⌊Real.logb 2 t⌋ : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 t) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)
    rw [h, Real.rpow_intCast] at hle
    exact hle
  · have h := Real.rpow_logb (b := 2) (by norm_num) (by norm_num) ht
    have hlt : Real.logb 2 t < (((⌊Real.logb 2 t⌋ : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast
      exact Int.lt_floor_add_one _
    have hle : (2:ℝ) ^ (Real.logb 2 t) ≤ (2:ℝ) ^ (((⌊Real.logb 2 t⌋ : ℤ) + 1 : ℤ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
    rw [h] at hle
    rwa [Real.rpow_intCast] at hle

/-- The slabs cover the punctured total space. -/
theorem exists_mem_slabK (Z : RealBundle B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (x : Punct Z) :
    ∃ j : ℤ, x ∈ slabK Z φ j := by
  obtain ⟨j, h1, h2⟩ := exists_zpow_le_and_le (slabNu Z φ (x : Z.TotalSpace))
    (slabNu_pos_of_mem Z φ hφ hnn hpos x)
  exact ⟨j, h1, h2⟩

/-- The open enlargements of the slabs escape: every point has a neighbourhood meeting only
finitely many of them. -/
theorem escape_slabO (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (hcont : Continuous (slabNu Z φ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (x : Punct Z) :
    ∃ U ∈ 𝓝 x, {j : ℤ | (U ∩ slabO Z φ j).Nonempty}.Finite := by
  have hcont' : Continuous fun y : Punct Z => slabNu Z φ (y : Z.TotalSpace) :=
    hcont.comp continuous_subtype_val
  set t : ℝ := slabNu Z φ (x : Z.TotalSpace) with ht
  have htpos : 0 < t := slabNu_pos_of_mem Z φ hφ hnn hpos x
  refine ⟨{y : Punct Z | slabNu Z φ (y : Z.TotalSpace) < 2 * t} ∩
    {y : Punct Z | t / 2 < slabNu Z φ (y : Z.TotalSpace)}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt hcont' continuous_const).inter (isOpen_lt continuous_const hcont')
    · constructor <;> simp only [Set.mem_setOf_eq] <;> rw [ht] <;> linarith
  · refine Set.Finite.subset
      (Finset.finite_toSet (Finset.Icc (⌈Real.logb 2 (t / 2) - 2⌉ : ℤ) ⌊Real.logb 2 (4 * t)⌋)) ?_
    rintro j ⟨y, hyU, hyO⟩
    obtain ⟨hy1, hy2⟩ := hyU
    rw [mem_slabO] at hyO
    have ht2 : (0:ℝ) < t / 2 := by linarith
    have h4t : (0:ℝ) < 4 * t := by linarith
    -- upper bound
    have hub : (j : ℝ) < Real.logb 2 (4 * t) := by
      have h : (2:ℝ) ^ j / 2 < 2 * t := lt_trans hyO.1 hy1
      have hlt : (2:ℝ) ^ j < 4 * t := by linarith
      have h1 : (0:ℝ) < (2:ℝ) ^ j := zpow_pos (by norm_num) j
      have := Real.logb_lt_logb (b := 2) (by norm_num) h1 hlt
      rwa [logb_two_zpow] at this
    have hub' : j ≤ ⌊Real.logb 2 (4 * t)⌋ := Int.le_floor.mpr hub.le
    -- lower bound
    have hlb : Real.logb 2 (t / 2) - 2 < (j : ℝ) := by
      have h : t / 2 < 2 * (2:ℝ) ^ (j + 1) := lt_trans hy2 hyO.2
      rw [two_mul_zpow_two] at h
      have h1 : (0:ℝ) < (2:ℝ) ^ (j + 2) := zpow_pos (by norm_num) (j + 2)
      have hlog := Real.logb_lt_logb (b := 2) (by norm_num) ht2 h
      rw [logb_two_zpow] at hlog
      push_cast at hlog
      linarith
    have hlb' : (⌈Real.logb 2 (t / 2) - 2⌉ : ℤ) ≤ j := Int.ceil_le.mpr hlb.le
    exact Finset.mem_Icc.mpr ⟨hlb', hub'⟩

end

end Work.Gen
