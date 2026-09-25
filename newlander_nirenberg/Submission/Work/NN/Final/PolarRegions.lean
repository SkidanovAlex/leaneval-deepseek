/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The regions and the logarithmic chart of the polar (iterated radial) Seeley construction

For a fixed coordinate `j : Fin n` the polar Seeley construction extends a function `G` in the
`j`-th coordinate.  Its value at a point `z` is built from the values of `G` at points with the
*same* transverse coordinates `i ≠ j` and with the `j`-th coordinate brought to a modulus `≤ ρ j`
("inside"); the natural regions are therefore

* `inRegion ρ j` — the transverse coordinates `i < j` strictly inside (`‖z i‖ < ρ i`), the `j`-th
  coordinate inside (`‖z j‖ < ρ j`), the coordinates `i > j` below `2 * ρ i`;
* `outRegion ρ j` — as `inRegion`, but the `j`-th coordinate only has to be `< 2 * ρ j`;
* `halfRegion ρ j` — as `inRegion`, but the `j`-th coordinate only has to be `≤ ρ j`: the
  one-sided closure of `inRegion`, which is where the input of the extension is evaluated (the
  extension is one-sidedly `C^k` there in the applications);

together with the flat ("logarithmic") picture

* `flatRegion ρ j ε` — the same transverse constraints, with the `j`-th coordinate in the
  punctured annulus `ε < ‖z j‖ < 3 * ρ j`;
* `polarChart ρ j z = (z, log (ρ j / ‖z j‖))`, sending a point of the annulus to the point of the
  flat space `(Fin n → ℂ) × ℝ` whose second coordinate is the log-radius;
* `flatPoint ρ j p = update p.1 j ((ρ j * exp (-p.2) / ‖p.1 j‖) • p.1 j)`, whose `j`-th coordinate
  lies on the ray of `p.1 j` at radius `ρ j * exp (-p.2)` (so on the boundary face
  `‖z j‖ = ρ j` for `p.2 = 0`);
* `flatPull ρ j G p = G (flatPoint ρ j p)`, the pullback along which the polar radial extension
  in the `j`-th coordinate is the *flat* Seeley extension `seeleyExt a b (flatPull ρ j G)`
  evaluated at `polarChart ρ j z` (see `radialExt_eq_seeleyExt`).
-/
import Mathlib
import Submission.Work.NN.Final.SeeleyDefs
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.PolarDefs

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-- The region where the input of the one step of the polar construction in the `j`-th
coordinate is evaluated: the coordinates `i < j` strictly inside, the `j`-th coordinate inside,
the coordinates `i > j` below `2 ρ i`. -/
def inRegion (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ < ρ j ∧ (∀ i, j < i → ‖z i‖ < 2 * ρ i)}

/-- The region where the output of one step of the polar construction in the `j`-th coordinate is
controlled: as `inRegion`, but the `j`-th coordinate only has to be `< 2 ρ j`. -/
def outRegion (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ < 2 * ρ j ∧ (∀ i, j < i → ‖z i‖ < 2 * ρ i)}

/-- The one-sided closure of `inRegion` in the `j`-th coordinate: where the input of the step is
evaluated (the values on the face `‖z j‖ = ρ j` are the one-sided limits). -/
def halfRegion (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ ≤ ρ j ∧ (∀ i, j < i → ‖z i‖ < 2 * ρ i)}

/-- The parameter region of the flat (logarithmic) picture in the `j`-th coordinate: the same
transverse constraints, with the `j`-th coordinate in the punctured annulus `ε < ‖z j‖ < 3 ρ j`
(an open neighbourhood of the unit circle, on which the direction `z j / ‖z j‖` is smooth). -/
def flatRegion (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ) : Set (Fin n → ℂ) :=
  {w | (∀ i, i < j → ‖w i‖ < ρ i) ∧ (ε < ‖w j‖ ∧ ‖w j‖ < 3 * ρ j) ∧ (∀ i, j < i → ‖w i‖ < 2 * ρ i)}

/-- The logarithmic chart in the `j`-th coordinate: the point together with the log-radius
`log (ρ j / ‖z j‖)`. -/
def polarChart (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (z : Fin n → ℂ) : (Fin n → ℂ) × ℝ :=
  (z, Real.log (ρ j / ‖z j‖))

/-- The fiberwise point map of the flat picture: the point whose `j`-th coordinate lies on the
ray of `w j` at radius `ρ j * exp (-t)`. -/
def flatPoint (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (p : (Fin n → ℂ) × ℝ) : Fin n → ℂ :=
  Function.update p.1 j (((ρ j * Real.exp (-p.2) / ‖p.1 j‖ : ℝ) : ℂ) * p.1 j)

/-- The pullback of a function on the polydisc along the fiberwise point map of the flat
picture. -/
def flatPull (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (G : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) × ℝ → ℂ :=
  fun p => G (flatPoint n ρ j p)

@[simp] lemma polarChart_apply (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (z : Fin n → ℂ) :
    polarChart n ρ j z = (z, Real.log (ρ j / ‖z j‖)) := rfl

@[simp] lemma flatPull_apply (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (G : (Fin n → ℂ) → ℂ)
    (p : (Fin n → ℂ) × ℝ) : flatPull n ρ j G p = G (flatPoint n ρ j p) := rfl

/-- Membership in `inRegion`, unfolded. -/
@[simp] lemma mem_inRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {z : Fin n → ℂ} :
    z ∈ inRegion n ρ j ↔ (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ < ρ j ∧
      (∀ i, j < i → ‖z i‖ < 2 * ρ i) := Iff.rfl

/-- Membership in `outRegion`, unfolded. -/
@[simp] lemma mem_outRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {z : Fin n → ℂ} :
    z ∈ outRegion n ρ j ↔ (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ < 2 * ρ j ∧
      (∀ i, j < i → ‖z i‖ < 2 * ρ i) := Iff.rfl

/-- Membership in `halfRegion`, unfolded. -/
@[simp] lemma mem_halfRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {z : Fin n → ℂ} :
    z ∈ halfRegion n ρ j ↔ (∀ i, i < j → ‖z i‖ < ρ i) ∧ ‖z j‖ ≤ ρ j ∧
      (∀ i, j < i → ‖z i‖ < 2 * ρ i) := Iff.rfl

/-- Membership in `flatRegion`, unfolded. -/
@[simp] lemma mem_flatRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} {w : Fin n → ℂ} :
    w ∈ flatRegion n ρ j ε ↔ (∀ i, i < j → ‖w i‖ < ρ i) ∧ (ε < ‖w j‖ ∧ ‖w j‖ < 3 * ρ j) ∧
      (∀ i, j < i → ‖w i‖ < 2 * ρ i) := Iff.rfl

lemma inRegion_subset_outRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} :
    inRegion n ρ j ⊆ outRegion n ρ j := by
  intro z hz
  rw [mem_inRegion] at hz
  rw [mem_outRegion]
  refine ⟨hz.1, ?_, hz.2.2⟩
  have hpos : 0 < ρ j := lt_of_le_of_lt (norm_nonneg _) hz.2.1
  linarith [hz.2.1]

lemma inRegion_subset_halfRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} :
    inRegion n ρ j ⊆ halfRegion n ρ j := by
  intro z hz
  rw [mem_inRegion] at hz
  rw [mem_halfRegion]
  exact ⟨hz.1, le_of_lt hz.2.1, hz.2.2⟩

lemma isOpen_inRegion (n : ℕ) {ρ : Fin n → ℝ} {hρ : ∀ i, 0 < ρ i} (j : Fin n) :
    IsOpen (inRegion n ρ j) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i}
        = ⋂ i ∈ {i : Fin n | i < j}, {z : Fin n → ℂ | ‖z i‖ < ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ‖z j‖ < ρ j} :=
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
  have h3 : IsOpen {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i}
        = ⋂ i ∈ {i : Fin n | j < i}, {z : Fin n → ℂ | ‖z i‖ < 2 * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : inRegion n ρ j =
      {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} ∩ {z : Fin n → ℂ | ‖z j‖ < ρ j} ∩
        {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    ext z; simp only [mem_inRegion, mem_inter_iff, mem_setOf_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3

lemma isOpen_outRegion (n : ℕ) {ρ : Fin n → ℝ} {hρ : ∀ i, 0 < ρ i} (j : Fin n) :
    IsOpen (outRegion n ρ j) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i}
        = ⋂ i ∈ {i : Fin n | i < j}, {z : Fin n → ℂ | ‖z i‖ < ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ‖z j‖ < 2 * ρ j} :=
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
  have h3 : IsOpen {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i}
        = ⋂ i ∈ {i : Fin n | j < i}, {z : Fin n → ℂ | ‖z i‖ < 2 * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : outRegion n ρ j =
      {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} ∩ {z : Fin n → ℂ | ‖z j‖ < 2 * ρ j} ∩
        {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    ext z; simp only [mem_outRegion, mem_inter_iff, mem_setOf_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3

lemma isOpen_flatRegion (n : ℕ) {ρ : Fin n → ℝ} {hρ : ∀ i, 0 < ρ i} (j : Fin n) (ε : ℝ) :
    IsOpen (flatRegion n ρ j ε) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i}
        = ⋂ i ∈ {i : Fin n | i < j}, {z : Fin n → ℂ | ‖z i‖ < ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ε < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j} :=
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply j))).inter
      (isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const)
  have h3 : IsOpen {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i}
        = ⋂ i ∈ {i : Fin n | j < i}, {z : Fin n → ℂ | ‖z i‖ < 2 * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : flatRegion n ρ j ε =
      {z : Fin n → ℂ | ∀ i, i < j → ‖z i‖ < ρ i} ∩
        {z : Fin n → ℂ | ε < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j} ∩
        {z : Fin n → ℂ | ∀ i, j < i → ‖z i‖ < 2 * ρ i} := by
    ext z; simp only [mem_flatRegion, mem_inter_iff, mem_setOf_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3


/-! ## The one-sided regions of the iteration -/

/-- The one-sided region of the `j`-th step: the coordinates `i ≤ j` are only required to satisfy
`‖z i‖ ≤ ρ i` (the faces of these coordinates are still to be extended, so only one-sided
smoothness is available), while the coordinates `i > j` are strictly below `2 ρ i`.  This is the
region where the input of the `j`-th step has to be `C^k` (one-sidedly on the faces
`‖z i‖ = ρ i`, `i ≤ j`). -/
def oneSidedRegion (n : ℕ) (ρ : Fin n → ℝ) (j : ℕ) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) ≤ j → ‖z i‖ ≤ ρ i) ∧
    (∀ i : Fin n, j < (i : ℕ) → ‖z i‖ < 2 * ρ i)}

/-- The intermediate region of the iteration: `V k = {z | (∀ i < k, ‖z i‖ < ρ i) ∧
(∀ i ≥ k, ‖z i‖ < 2 * ρ i)}`.  The step extending the `j`-th coordinate maps a bound on the norm
over `V (j+1)` to a bound on the norm over `V j`. -/
def stepRegion (n : ℕ) (ρ : Fin n → ℝ) (k : ℕ) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) < k → ‖z i‖ < ρ i) ∧
    (∀ i : Fin n, k ≤ (i : ℕ) → ‖z i‖ < 2 * ρ i)}

@[simp] lemma mem_oneSidedRegion {n : ℕ} {ρ : Fin n → ℝ} {j : ℕ} {z : Fin n → ℂ} :
    z ∈ oneSidedRegion n ρ j ↔ (∀ i : Fin n, (i : ℕ) ≤ j → ‖z i‖ ≤ ρ i) ∧
      (∀ i : Fin n, j < (i : ℕ) → ‖z i‖ < 2 * ρ i) := Iff.rfl

@[simp] lemma mem_stepRegion {n : ℕ} {ρ : Fin n → ℝ} {k : ℕ} {z : Fin n → ℂ} :
    z ∈ stepRegion n ρ k ↔ (∀ i : Fin n, (i : ℕ) < k → ‖z i‖ < ρ i) ∧
      (∀ i : Fin n, k ≤ (i : ℕ) → ‖z i‖ < 2 * ρ i) := Iff.rfl

/-- The `j`-th step region is the outer region of the `j`-th coordinate. -/
lemma stepRegion_eq_outRegion {n : ℕ} {ρ : Fin n → ℝ} (j : Fin n) :
    stepRegion n ρ (j : ℕ) = outRegion n ρ j := by
  ext z
  rw [mem_stepRegion, mem_outRegion]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i hi, h2 j le_rfl, fun i hi => h2 i (le_of_lt hi)⟩
  · rintro ⟨h1, hj, h3⟩
    refine ⟨fun i hi => h1 i hi, fun i hi => ?_⟩
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact h3 i hlt
    · rw [← Fin.ext heq]; exact hj

/-- The `(j+1)`-st step region is the inner region of the `j`-th coordinate. -/
lemma stepRegion_succ_eq_inRegion {n : ℕ} {ρ : Fin n → ℝ} (j : Fin n) :
    stepRegion n ρ ((j : ℕ) + 1) = inRegion n ρ j := by
  ext z
  rw [mem_stepRegion, mem_inRegion]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Nat.lt_succ_of_lt hi), h1 j (Nat.lt_succ_self _),
      fun i hi => h2 i (Nat.succ_le_of_lt hi)⟩
  · rintro ⟨h1, hj, h3⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact h1 i hlt
      · rw [Fin.ext heq]; exact hj
    · exact h3 i (Nat.lt_of_succ_le hi)

/-- The step region at `0` is the polydisc of multiradius `2 ρ`. -/
lemma stepRegion_zero {n : ℕ} (ρ : Fin n → ℝ) : stepRegion n ρ 0 = pd n ρ 2 := by
  ext z
  rw [mem_stepRegion, mem_pd]
  constructor
  · rintro ⟨-, h2⟩ i
    exact h2 i (Nat.zero_le _)
  · intro h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ => h i⟩

/-- The step region at `n` is the polydisc of multiradius `ρ`. -/
lemma stepRegion_last {n : ℕ} (ρ : Fin n → ℝ) : stepRegion n ρ n = pd n ρ 1 := by
  ext z
  rw [mem_stepRegion, mem_pd]
  constructor
  · rintro ⟨h1, -⟩ i
    simpa using h1 i i.isLt
  · intro h
    exact ⟨fun i _ => by simpa using h i, fun i hi => absurd hi (not_le.mpr i.isLt)⟩


/-! ## The explicit iteration -/

/-- The explicit iteration of the one-coordinate extensions in the coordinates `t, t+1, …, n-1`
(the coordinate `t` being applied outermost).  `iterateFrom n ρ a b 0 G` is the function that
`iterExt n ρ a b G` defines by folding over `List.finRange n`. -/
def iterateFrom (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (t : ℕ) (G : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  if h : t < n then radialExt n ρ a b ⟨t, h⟩ (iterateFrom n ρ a b (t + 1) G) else G
  termination_by n - t
  decreasing_by omega

@[simp] lemma iterateFrom_of_lt {n : ℕ} {ρ : Fin n → ℝ} {a b : ℕ → ℝ} {t : ℕ} (h : t < n)
    (G : (Fin n → ℂ) → ℂ) :
    iterateFrom n ρ a b t G = radialExt n ρ a b ⟨t, h⟩ (iterateFrom n ρ a b (t + 1) G) := by
  rw [iterateFrom]; exact dif_pos h

@[simp] lemma iterateFrom_of_le {n : ℕ} {ρ : Fin n → ℝ} {a b : ℕ → ℝ} {t : ℕ} (h : n ≤ t)
    (G : (Fin n → ℂ) → ℂ) : iterateFrom n ρ a b t G = G := by
  rw [iterateFrom]; exact dif_neg (not_lt.mpr h)


/-- The `j`-th step region is the outer region of the `j`-th coordinate (natural-number index). -/
lemma stepRegion_eq_outRegion' {n : ℕ} {ρ : Fin n → ℝ} {j : ℕ} (hj : j < n) :
    stepRegion n ρ j = outRegion n ρ ⟨j, hj⟩ := by
  have h := stepRegion_eq_outRegion (n := n) (ρ := ρ) ⟨j, hj⟩
  simpa using h

/-- The `(j+1)`-st step region is the inner region of the `j`-th coordinate
(natural-number index). -/
lemma stepRegion_succ_eq_inRegion' {n : ℕ} {ρ : Fin n → ℝ} {j : ℕ} (hj : j < n) :
    stepRegion n ρ (j + 1) = inRegion n ρ ⟨j, hj⟩ := by
  have h := stepRegion_succ_eq_inRegion (n := n) (ρ := ρ) ⟨j, hj⟩
  simpa using h

end Work.NN.Final
