import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-!
# The pair `(B × Dⁿ, B × Sⁿ⁻¹)` is a deformation retract of `(B × ℝⁿ, B × Sⁿ⁻¹)`

The inclusion of the closed unit ball `MBall n = {v : ℝⁿ | ‖v‖ ≤ 1}` in `ℝⁿ` is a homotopy
equivalence whose homotopy inverse is the radial projection onto the ball,

`clamp v = (max 1 ‖v‖)⁻¹ • v`.

Since `clamp` fixes the unit sphere `mSph n` pointwise, the inclusion is a homotopy equivalence of
the *pairs* `(B × MBall n, B × mSph n) → (B × ℝⁿ, B × mSph n)` for every space `B`; and because a
homotopy equivalence of pairs induces a bijection on relative cohomology
(`Work.Thom.bijective_relCohMap_of_homotopyEquiv`), the pullback

`H^m(B × ℝⁿ, B × mSph n; ℤ) → H^m(B × MBall n, B × mSph n; ℤ)`

is bijective in every degree.  This is the statement `Work.Thom.bijective_relCohMap_discFull`.

The file proves it by constructing the relevant homotopy equivalences:

* `Work.Thom.DiscFull.discFullHomotopyEquiv` — the pair inclusion `B × MBall n → B × ℝⁿ`, with
  homotopy inverse the radial projection, the homotopy being the linear interpolation of the
  radial scaling `(t,p) ↦ (p.1, ((1-t)·(max 1 ‖p.2‖)⁻¹ + t) • p.2)`;
* `Work.Thom.DiscFull.spherePairHomeomorph` — the homeomorphism
  `B × Sⁿ⁻¹ → B × Sⁿ⁻¹` between the two boundary subspaces (the inclusion is bijective there,
  because `‖v‖ = 1` implies `v ∈ MBall n`);
* the main theorem, obtained from these two by
  `Work.Thom.bijective_relCohMap_of_homotopyEquiv`.
-/

namespace Work.Thom

namespace DiscFull

open scoped Topology

noncomputable section

variable (n : ℕ)

/-! ## The radial projection onto the closed unit ball -/

/-- The **radial coefficient** `(max 1 ‖v‖)⁻¹` of a vector: `1` on the closed unit ball and
`‖v‖⁻¹` outside it.  (This is the map `Work.Thom.radialCoeff` of
`Submission/Work/Thom/discSub_homotopyEquiv.lean`, for the trivial bundle over a point.) -/
def clampCoeff (v : EuclideanSpace ℝ (Fin n)) : ℝ := (max 1 ‖v‖)⁻¹

theorem clampCoeff_pos (v : EuclideanSpace ℝ (Fin n)) : 0 < clampCoeff n v :=
  inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖v‖))

theorem clampCoeff_nonneg (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ clampCoeff n v :=
  (clampCoeff_pos n v).le

theorem clampCoeff_eq_one_of_norm_le {v : EuclideanSpace ℝ (Fin n)} (h : ‖v‖ ≤ 1) :
    clampCoeff n v = 1 := by
  rw [clampCoeff, max_eq_left h, inv_one]

/-- The **radial projection** of `ℝⁿ` onto the closed unit ball, `v ↦ (max 1 ‖v‖)⁻¹ • v`. -/
def clampPoint (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := clampCoeff n v • v

/-- The radial projection does not increase the norm beyond `1`. -/
theorem norm_clampPoint_le_one (v : EuclideanSpace ℝ (Fin n)) : ‖clampPoint n v‖ ≤ 1 := by
  rw [clampPoint, norm_smul, Real.norm_eq_abs, abs_of_nonneg (clampCoeff_nonneg n v)]
  rcases le_total ‖v‖ 1 with h | h
  · calc clampCoeff n v * ‖v‖ ≤ 1 * 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ (le_max_left 1 ‖v‖)) h (norm_nonneg v) zero_le_one
      _ = 1 := by norm_num
  · have hn : (0 : ℝ) < ‖v‖ := lt_of_lt_of_le zero_lt_one h
    rw [clampCoeff, max_eq_right h, inv_mul_cancel₀ hn.ne']

theorem clampPoint_mem_mBall (v : EuclideanSpace ℝ (Fin n)) : clampPoint n v ∈ mBall n :=
  norm_clampPoint_le_one n v

/-- The radial projection as a map into the closed unit ball. -/
def clamp (v : EuclideanSpace ℝ (Fin n)) : MBall n :=
  ⟨clampPoint n v, clampPoint_mem_mBall n v⟩

@[simp] theorem clamp_coe (v : EuclideanSpace ℝ (Fin n)) :
    (clamp n v : EuclideanSpace ℝ (Fin n)) = clampPoint n v := rfl

/-- On the closed unit ball the radial projection is the identity. -/
theorem clampPoint_eq_self_of_norm_le {v : EuclideanSpace ℝ (Fin n)} (h : ‖v‖ ≤ 1) :
    clampPoint n v = v := by
  rw [clampPoint, clampCoeff_eq_one_of_norm_le n h, one_smul]

theorem clamp_coe_eq_self_of_norm_le (v : EuclideanSpace ℝ (Fin n)) (h : ‖v‖ ≤ 1) :
    (clamp n v : EuclideanSpace ℝ (Fin n)) = v := clampPoint_eq_self_of_norm_le n h

theorem continuous_clampCoeff : Continuous (clampCoeff n) :=
  (continuous_const.max continuous_norm).inv₀
    (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖v‖)))

theorem continuous_clampPoint : Continuous (clampPoint n) :=
  (continuous_clampCoeff n).smul continuous_id

theorem continuous_clamp : Continuous (clamp n) :=
  (continuous_clampPoint n).subtype_mk (clampPoint_mem_mBall n)

/-- A vector of norm `1` lies in the closed unit ball. -/
theorem norm_le_one_of_mem_mSph {v : EuclideanSpace ℝ (Fin n)} (h : v ∈ mSph n) : ‖v‖ ≤ 1 :=
  le_of_eq h

/-! ## The homotopy equivalence `B × MBall n → B × ℝⁿ` -/

/-- The inclusion of the closed ball bundle in the trivial bundle, `(b, v) ↦ (b, v)`. -/
def discFullIncl (B : Type) [TopologicalSpace B] :
    C(B × MBall n, B × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun q => (q.1, q.2.1), continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

/-- The radial retraction of the trivial bundle onto the closed ball bundle. -/
def discFullRetract (B : Type) [TopologicalSpace B] :
    C(B × EuclideanSpace ℝ (Fin n), B × MBall n) :=
  ⟨fun p => (p.1, clamp n p.2), continuous_fst.prodMk ((continuous_clamp n).comp continuous_snd)⟩

/-- The linear interpolation of the radial scaling, at time `t`:
`(b, v) ↦ (b, ((1-t)·(max 1 ‖v‖)⁻¹ + t) • v)`.  At `t = 0` this is the radial retraction and at
`t = 1` the identity. -/
def homotopyMap (B : Type) [TopologicalSpace B] :
    C(unitInterval × (B × EuclideanSpace ℝ (Fin n)), B × EuclideanSpace ℝ (Fin n)) where
  toFun x := (x.2.1, ((1 - (x.1 : ℝ)) * clampCoeff n x.2.2 + (x.1 : ℝ)) • x.2.2)
  continuous_toFun := by
    have ht : Continuous fun x : unitInterval × (B × EuclideanSpace ℝ (Fin n)) => (x.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hv : Continuous fun x : unitInterval × (B × EuclideanSpace ℝ (Fin n)) => x.2.2 :=
      continuous_snd.comp continuous_snd
    have hcoef : Continuous fun x : unitInterval × (B × EuclideanSpace ℝ (Fin n)) =>
        (1 - (x.1 : ℝ)) * clampCoeff n x.2.2 + (x.1 : ℝ) :=
      ((continuous_const.sub ht).mul ((continuous_clampCoeff n).comp hv)).add ht
    exact (continuous_fst.comp continuous_snd).prodMk (hcoef.smul hv)

/-- **The inclusion of the closed ball bundle `B × Dⁿ` in the trivial bundle `B × ℝⁿ` is a
homotopy equivalence**, with homotopy inverse the radial retraction; the composite
`clamp ∘ incl` is *equal* to the identity of `B × Dⁿ` (the radial coefficient is `1` there), and
`incl ∘ clamp` is homotopic to the identity by linear interpolation of the radial scaling. -/
def discFullHomotopyEquiv (B : Type) [TopologicalSpace B] :
    ContinuousMap.HomotopyEquiv (B × MBall n) (B × EuclideanSpace ℝ (Fin n)) where
  toFun := discFullIncl n B
  invFun := discFullRetract n B
  left_inv := by
    have heq : (discFullRetract n B).comp (discFullIncl n B) = ContinuousMap.id (B × MBall n) := by
      apply ContinuousMap.ext
      intro q
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact clamp_coe_eq_self_of_norm_le n q.2.1 q.2.2
    simpa only [heq] using ContinuousMap.Homotopic.refl (ContinuousMap.id (B × MBall n))
  right_inv := by
    refine ⟨ContinuousMap.Homotopy.mk (homotopyMap n B) ?_ ?_⟩
    · intro p
      apply Prod.ext
      · rfl
      · show ((1 - ((0 : unitInterval) : ℝ)) * clampCoeff n p.2 + ((0 : unitInterval) : ℝ)) • p.2
          = (clamp n p.2 : EuclideanSpace ℝ (Fin n))
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
        simp [clampPoint]
    · intro p
      apply Prod.ext
      · rfl
      · show ((1 - ((1 : unitInterval) : ℝ)) * clampCoeff n p.2 + ((1 : unitInterval) : ℝ)) • p.2
          = p.2
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
        simp

/-! ## The two boundary subspaces are homeomorphic -/

/-- **The inclusion of the boundary pair `B × Sⁿ⁻¹ ⊆ B × Dⁿ` in the boundary pair
`B × Sⁿ⁻¹ ⊆ B × ℝⁿ` is a homeomorphism**: on the unit sphere the radial projection is the identity,
and a unit vector already lies in the closed ball. -/
def spherePairHomeomorph (B : Type) [TopologicalSpace B] :
    ↥{q : B × MBall n | q.2.1 ∈ mSph n} ≃ₜ
      ↥{z : B × EuclideanSpace ℝ (Fin n) | z.2 ∈ mSph n} where
  toFun a := ⟨(a.1.1, a.1.2.1), a.2⟩
  invFun z := ⟨(z.1.1, ⟨z.1.2, norm_le_one_of_mem_mSph n z.2⟩), z.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ (fun a => a.2)
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun z => z.2)
    have h1 : Continuous fun z : ↥{z : B × EuclideanSpace ℝ (Fin n) | z.2 ∈ mSph n} =>
        (z.1.2 : EuclideanSpace ℝ (Fin n)) := continuous_snd.comp continuous_subtype_val
    have h2 : Continuous fun z : ↥{z : B × EuclideanSpace ℝ (Fin n) | z.2 ∈ mSph n} =>
        (⟨z.1.2, norm_le_one_of_mem_mSph n z.2⟩ : MBall n) :=
      h1.subtype_mk (fun z => norm_le_one_of_mem_mSph n z.2)
    exact (continuous_fst.comp continuous_subtype_val).prodMk h2

end

end DiscFull

open DiscFull

/-- **The inclusion of the disc-bundle pair in the trivial bundle induces a bijection on relative
cohomology.**  For every space `B` and every `n`, the pair map

`(B × Dⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × Sⁿ⁻¹)`

is a homotopy equivalence of pairs (the radial projection onto the ball is a homotopy inverse which
fixes the sphere pointwise), hence the pullback `H^m(B × ℝⁿ, B × Sⁿ⁻¹; ℤ) → H^m(B × Dⁿ, B × Sⁿ⁻¹; ℤ)`
is bijective in every degree `m`. -/
theorem bijective_relCohMap_discFull (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((relCohMap (⟨fun q : B × MBall n => (q.1, q.2.1),
            continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
            C(B × MBall n, B × EuclideanSpace ℝ (Fin n)))
          {q : B × MBall n | q.2.1 ∈ mSph n}
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
          (fun q hq => hq) ℤ m).hom) := by
  exact EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv
    {q : B × MBall n | q.2.1 ∈ mSph n}
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
    (⟨fun q : B × MBall n => (q.1, q.2.1),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
      C(B × MBall n, B × EuclideanSpace ℝ (Fin n)))
    (fun q hq => hq)
    (discFullHomotopyEquiv n B) rfl
    ((spherePairHomeomorph n B).toHomotopyEquiv)
    (fun _ => rfl) m

end Work.Thom
