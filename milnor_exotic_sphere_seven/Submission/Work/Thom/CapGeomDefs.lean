import Mathlib
import Submission.Work.Thom.ModelGeometry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The geometry of the cap map: definitions

This module fixes the notation for the proof of `Work.Thom.capRelCohIso`: the identification of the
Thom pair of rank `n` with the sphere-bundle pair of rank `n + 1` over the lower region.

We work on `EuclideanSpace ℝ (Fin (n+1))`, the ambient space of the unit sphere
`MSph (n+1) = {v | ‖v‖ = 1}`.

* `lastC n v` — the last coordinate of `v`;
* `sphLe n c`, `sphLt n c`, `sphGt n c`, `sphEq n` — the subsets of the unit sphere cut out by
  conditions on the last coordinate, as subsets of the *ambient* space: for instance
  `sphLe n c = {v | ‖v‖ = 1 ∧ lastC n v ≤ c}`.  The key point is that `mLower n` is
  *definitionally* `sphLe n (1/2)`, so the pair of the statement can be described by these sets
  without any rewriting;
* `flLe n c`, `flLt n c`, `flGt n c`, `flEq n` — the same conditions as subsets of the subtype
  `MSph (n+1)`;
* `scaleVec`/`scalePt` — the **scaling family** `Φ_λ` on the unit sphere, the map sending `v` to the
  unit vector with the same first `n` coordinates and last coordinate `λ · lastC n v`
  (`λ > 0`), i.e. `v ↦ ‖(strip v, λ · last v)‖⁻¹ • (strip v, λ · last v)`.  It is the basic tool for
  the homotopies below: `Φ_1 = id` and `|lastC (Φ_λ v)| ≤ |lastC v|` for `λ ∈ [0,1]`, so it pushes
  the sphere into the lower region and can be used to retract the region `{last < 1/2}` onto
  `{last ≤ 0}`, and to retract `{-1/2 < last < 1/2}` onto the equator;
* `eqProj` — the equator projection `Φ_0`, `v ↦ ‖strip v‖⁻¹ • (strip v, 0)`;
* `capBig`/`stripBig` — the cap map seen as a map `MBall n → ↥(flGt n (-1/2))` (into the open cap
  `{last > -1/2}`, which contains its image) and the projection back.
-/

namespace Work.Thom

noncomputable section

/-! ## The last coordinate -/

/-- The last coordinate of a point of `ℝ^{n+1}`. -/
def lastC (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := v.ofLp (Fin.last n)

theorem continuous_lastC (n : ℕ) : Continuous (lastC n) := by
  unfold lastC; fun_prop

@[simp] theorem lastC_snocLp (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    lastC n (Work.Morse.snocLp y t) = t := Work.Morse.snocLp_ofLp_last y t

@[simp] theorem strip_snocLp (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Work.Morse.strip (Work.Morse.snocLp y t) = y := by
  apply PiLp.ext
  intro i
  rw [Work.Morse.strip_ofLp, Work.Morse.snocLp_ofLp_castSucc]

@[simp] theorem strip_zero (n : ℕ) :
    Work.Morse.strip (0 : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
  apply PiLp.ext
  intro i
  simp [Work.Morse.strip_ofLp]

@[simp] theorem snocLp_zero_zero (n : ℕ) :
    Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (0 : ℝ) = 0 := by
  have h := Work.Morse.snocLp_strip (0 : EuclideanSpace ℝ (Fin (n + 1)))
  simpa using h

@[simp] theorem lastC_zero (n : ℕ) :
    lastC n (0 : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
  rw [lastC]
  simp

theorem abs_lastC_le_norm (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    |lastC n v| ≤ ‖v‖ := by
  rw [lastC]
  simpa using PiLp.norm_apply_le (p := 2) v (Fin.last n)

theorem abs_lastC_le_one (n : ℕ) (v : MSph (n + 1)) : |lastC n v.1| ≤ 1 := by
  have h := abs_lastC_le_norm n v.1
  rw [show ‖v.1‖ = 1 from v.2] at h
  exact h

theorem lastC_ne_of_abs_lt_one (n : ℕ) (v : MSph (n + 1)) (h : |lastC n v.1| < 1) :
    lastC n v.1 ≠ 1 ∧ lastC n v.1 ≠ -1 := by
  constructor <;> intro hc <;> rw [hc] at h <;> norm_num at h

/-! ## The sphere cut out by conditions on the last coordinate -/

/-- The closed cap `{‖v‖ = 1 ∧ lastC v ≤ c}` of the unit sphere, as a subset of the ambient space.
`mLower n` is definitionally `sphLe n (1/2)`. -/
def sphLe (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ lastC n v ≤ c}

/-- The open cap `{‖v‖ = 1 ∧ lastC v < c}`. -/
def sphLt (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ lastC n v < c}

/-- The cap `{‖v‖ = 1 ∧ c < lastC v}`. -/
def sphGt (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ c < lastC n v}

/-- The equator `{‖v‖ = 1 ∧ lastC v = 0}`. -/
def sphEq (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ lastC n v = 0}

/-- `mLower n` is the closed cap `{last ≤ 1/2}`: this is definitional. -/
theorem mLower_eq_sphLe (n : ℕ) : mLower n = sphLe n (1 / 2) := rfl

@[simp] theorem mem_sphLe (n : ℕ) (c : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    v ∈ sphLe n c ↔ ‖v‖ = 1 ∧ lastC n v ≤ c := Iff.rfl

@[simp] theorem mem_sphLt (n : ℕ) (c : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    v ∈ sphLt n c ↔ ‖v‖ = 1 ∧ lastC n v < c := Iff.rfl

@[simp] theorem mem_sphGt (n : ℕ) (c : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    v ∈ sphGt n c ↔ ‖v‖ = 1 ∧ c < lastC n v := Iff.rfl

@[simp] theorem mem_sphEq (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    v ∈ sphEq n ↔ ‖v‖ = 1 ∧ lastC n v = 0 := Iff.rfl

/-! ## The same conditions inside the sphere subtype -/

/-- The closed cap `{lastC ≤ c}` inside `MSph (n+1)`. -/
def flLe (n : ℕ) (c : ℝ) : Set (MSph (n + 1)) := {v | lastC n v.1 ≤ c}

/-- The open cap `{lastC < c}` inside `MSph (n+1)`. -/
def flLt (n : ℕ) (c : ℝ) : Set (MSph (n + 1)) := {v | lastC n v.1 < c}

/-- The cap `{c < lastC}` inside `MSph (n+1)`. -/
def flGt (n : ℕ) (c : ℝ) : Set (MSph (n + 1)) := {v | c < lastC n v.1}

/-- The equator `{lastC = 0}` inside `MSph (n+1)`. -/
def flEq (n : ℕ) : Set (MSph (n + 1)) := {v | lastC n v.1 = 0}

@[simp] theorem mem_flLe (n : ℕ) (c : ℝ) (v : MSph (n + 1)) :
    v ∈ flLe n c ↔ lastC n v.1 ≤ c := Iff.rfl

@[simp] theorem mem_flLt (n : ℕ) (c : ℝ) (v : MSph (n + 1)) :
    v ∈ flLt n c ↔ lastC n v.1 < c := Iff.rfl

@[simp] theorem mem_flGt (n : ℕ) (c : ℝ) (v : MSph (n + 1)) :
    v ∈ flGt n c ↔ c < lastC n v.1 := Iff.rfl

@[simp] theorem mem_flEq (n : ℕ) (v : MSph (n + 1)) :
    v ∈ flEq n ↔ lastC n v.1 = 0 := Iff.rfl

/-! ## The scaling family -/

/-- The vector `(strip v, λ · lastC v)`, i.e. `v` with its last coordinate scaled by `λ`. -/
def scaleV (n : ℕ) (lam : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  Work.Morse.snocLp (Work.Morse.strip v) (lam * lastC n v)

@[simp] theorem lastC_scaleV (n : ℕ) (lam : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    lastC n (scaleV n lam v) = lam * lastC n v := by
  rw [scaleV, lastC_snocLp]

@[simp] theorem strip_scaleV (n : ℕ) (lam : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    Work.Morse.strip (scaleV n lam v) = Work.Morse.strip v := by
  rw [scaleV, strip_snocLp]

theorem norm_scaleV_sq (n : ℕ) (lam : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖scaleV n lam v‖ ^ 2 = ‖Work.Morse.strip v‖ ^ 2 + (lam * lastC n v) ^ 2 := by
  rw [scaleV, Work.Morse.snocLp_norm_sq]

theorem norm_strip_sq_of_unit (n : ℕ) (v : MSph (n + 1)) :
    ‖Work.Morse.strip v.1‖ ^ 2 = 1 - (lastC n v.1) ^ 2 := by
  have h := Work.Morse.snocLp_norm_sq (Work.Morse.strip v.1) (v.1.ofLp (Fin.last n))
  rw [Work.Morse.snocLp_strip, show ‖v.1‖ = 1 from v.2] at h
  simp only [lastC] at h ⊢
  linarith [h]

theorem norm_scaleV_sq_of_unit (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) :
    ‖scaleV n lam v.1‖ ^ 2 = 1 - (lastC n v.1) ^ 2 + (lam * lastC n v.1) ^ 2 := by
  rw [norm_scaleV_sq, norm_strip_sq_of_unit]

/-- The normalised scalar multiple of a non-zero vector is a unit vector. -/
theorem norm_inv_smul (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) (h : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- The scaled point, `Φ_λ v`: the unit vector with the same first `n` coordinates as `v` and last
coordinate `λ · lastC v`, normalised.  The hypothesis is that the vector is non-zero; it holds
whenever `λ > 0` or `|lastC v| < 1`. -/
def scalePt (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0) : MSph (n + 1) :=
  ⟨‖scaleV n lam v.1‖⁻¹ • scaleV n lam v.1, by
    show ‖‖scaleV n lam v.1‖⁻¹ • scaleV n lam v.1‖ = 1
    exact norm_inv_smul n _ h⟩

theorem scalePt_val (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0) :
    (scalePt n lam v h).1 = ‖scaleV n lam v.1‖⁻¹ • scaleV n lam v.1 := rfl

theorem scalePt_congr (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h h' : scaleV n lam v.1 ≠ 0) :
    scalePt n lam v h = scalePt n lam v h' := rfl

theorem lastC_scalePt (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0) :
    lastC n (scalePt n lam v h).1 = (lam * lastC n v.1) / ‖scaleV n lam v.1‖ := by
  rw [scalePt_val]
  show (‖scaleV n lam v.1‖⁻¹ • scaleV n lam v.1).ofLp (Fin.last n)
    = (lam * lastC n v.1) / ‖scaleV n lam v.1‖
  rw [PiLp.smul_apply]
  have h0 : (scaleV n lam v.1).ofLp (Fin.last n) = lam * lastC n v.1 := by
    rw [← lastC, lastC_scaleV]
  rw [h0, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem scaleV_ne_zero_of_pos (n : ℕ) (lam : ℝ) (hlam : 0 < lam) (v : MSph (n + 1)) :
    scaleV n lam v.1 ≠ 0 := by
  intro h
  have h1 : Work.Morse.strip v.1 = 0 := by
    have hh := congrArg (fun w => Work.Morse.strip w) h
    simp only [scaleV] at hh
    rw [strip_snocLp, strip_zero] at hh
    exact hh
  have h2 : lam * lastC n v.1 = 0 := by
    have hh := congrArg (fun w => lastC n w) h
    rw [lastC_scaleV] at hh
    simpa using hh.symm
  have h3 : lastC n v.1 = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' hlam.ne'
    · exact h'
  have hzero : v.1 = 0 := by
    have h3' : v.1.ofLp (Fin.last n) = 0 := h3
    rw [← Work.Morse.snocLp_strip v.1, h1, h3']
    exact snocLp_zero_zero n
  have : ‖v.1‖ = 0 := by rw [hzero]; simp
  rw [v.2] at this
  norm_num at this

theorem scaleV_ne_zero_of_abs_lt (n : ℕ) (lam : ℝ) (v : MSph (n + 1))
    (h : |lastC n v.1| < 1) : scaleV n lam v.1 ≠ 0 := by
  intro h0
  have h1 : Work.Morse.strip v.1 = 0 := by
    have hh := congrArg (fun w => Work.Morse.strip w) h0
    simp only [scaleV] at hh
    rw [strip_snocLp, strip_zero] at hh
    exact hh
  have h2 : ‖Work.Morse.strip v.1‖ ^ 2 = 0 := by rw [h1]; simp
  have h3 : (lastC n v.1) ^ 2 = 1 := by
    have hsq := norm_strip_sq_of_unit n v
    rw [h2] at hsq
    linarith
  have h4 : |lastC n v.1| = 1 := by
    rcases sq_eq_one_iff.mp h3 with h' | h' <;> rw [h'] <;> norm_num
  linarith [h4]

theorem scaleV_zero_ne_zero (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) :
    scaleV n 0 v.1 ≠ 0 := by
  intro h0
  apply h
  have hh := congrArg (fun w => Work.Morse.strip w) h0
  simp only [scaleV] at hh
  rw [strip_snocLp, strip_zero] at hh
  exact hh

/-- The equator projection `Φ_0`. -/
def eqProj (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) : MSph (n + 1) :=
  scalePt n 0 v (scaleV_zero_ne_zero n v h)

theorem eqProj_val (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) :
    (eqProj n v h).1 = ‖scaleV n 0 v.1‖⁻¹ • scaleV n 0 v.1 := rfl

theorem lastC_eqProj (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) :
    lastC n (eqProj n v h).1 = 0 := by
  rw [eqProj_val]
  show (‖scaleV n 0 v.1‖⁻¹ • scaleV n 0 v.1).ofLp (Fin.last n) = 0
  rw [PiLp.smul_apply]
  have h0 : (scaleV n 0 v.1).ofLp (Fin.last n) = 0 := by
    rw [← lastC, lastC_scaleV]
    simp
  rw [h0, smul_zero]

theorem strip_ne_zero_iff (n : ℕ) (v : MSph (n + 1)) :
    Work.Morse.strip v.1 ≠ 0 ↔ |lastC n v.1| < 1 := by
  constructor
  · intro h
    by_contra h'
    have h' : 1 ≤ |lastC n v.1| := not_lt.mp h'
    have h1 : |lastC n v.1| = 1 := le_antisymm (abs_lastC_le_one n v) h'
    have h2 : (lastC n v.1) ^ 2 = 1 := by
      rw [← sq_abs, h1]
      norm_num
    have h3 : ‖Work.Morse.strip v.1‖ ^ 2 = 0 := by
      rw [norm_strip_sq_of_unit, h2]
      norm_num
    have h4 : ‖Work.Morse.strip v.1‖ = 0 := sq_eq_zero_iff.mp h3
    exact h (norm_eq_zero.mp h4)
  · intro h hz
    have h2 : ‖Work.Morse.strip v.1‖ ^ 2 = 0 := by rw [hz]; simp
    have h3 : (lastC n v.1) ^ 2 = 1 := by
      have hsq := norm_strip_sq_of_unit n v
      rw [h2] at hsq
      linarith
    have h4 : |lastC n v.1| = 1 := by
      rcases sq_eq_one_iff.mp h3 with h' | h' <;> rw [h'] <;> norm_num
    linarith [h4]

/-! ## The cap map into the open cap and the projection back -/

/-- The cap map, as a map from the closed ball into the open cap `{last > -1/2}` of the sphere. -/
def capBig (n : ℕ) : C(MBall n, ↥(flGt n (-(1 / 2)))) :=
  ⟨fun q => ⟨⟨capMap n q.1, capMap_mem_mSph n q.2⟩, by
      show -(1 / 2) < lastC n (capMap n q.1)
      rw [lastC, capMap_last]
      have hq : ‖q.1‖ ≤ 1 := q.2
      have h : (0 : ℝ) ≤ 1 - ‖q.1‖ ^ 2 := by
        nlinarith [norm_nonneg q.1]
      have := Real.sqrt_nonneg (1 - ‖q.1‖ ^ 2)
      linarith⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      ((continuous_capMap n).comp continuous_subtype_val) _) _⟩

/-- The projection of the open cap `{last > -1/2}` onto the closed ball, `v ↦ strip v`. -/
def stripBig (n : ℕ) : C(↥(flGt n (-(1 / 2))), MBall n) :=
  ⟨fun w => ⟨Work.Morse.strip w.1.1, by
      show ‖Work.Morse.strip w.1.1‖ ≤ 1
      have h1 : ‖Work.Morse.strip w.1.1‖ ^ 2 = 1 - (lastC n w.1.1) ^ 2 :=
        norm_strip_sq_of_unit n w.1
      nlinarith [norm_nonneg (Work.Morse.strip w.1.1)]⟩,
    Continuous.subtype_mk
      ((Work.Cohomology.continuous_strip n).comp
        (continuous_subtype_val.comp continuous_subtype_val)) _⟩

end

end Work.Thom
