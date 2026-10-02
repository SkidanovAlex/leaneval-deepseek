import Mathlib
import Submission.Work.Thom.SuspensionStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The model geometry of the suspension step for the trivial bundle

The induction that constructs the Thom class of the trivial bundle of rank `n` uses, at each step,
the following concrete geometry in the model fibre `EuclideanSpace ℝ (Fin (n+1)) = ℝ^{n+1}`:

* `Work.Thom.mBall n`, `Work.Thom.mSph n` — the closed unit ball and the unit sphere;
* `Work.Thom.mLower n` — the "lower region" of the unit sphere, `{v : ‖v‖ = 1, v_n ≤ 1/2}`, a closed
  disc containing the equator;
* `Work.Thom.capMap n` — the **cap map**, the graph of the upper hemisphere,
  `w ↦ (w, √(1 - ‖w‖²))`: a homeomorphism of the closed unit ball of `ℝⁿ` onto the closed upper
  hemisphere of the unit sphere of `ℝ^{n+1}`, carrying the unit sphere of `ℝⁿ` onto the equator.

The point of the last named map is that it is the map of pairs
`(B × ball n, B × sph (n-1)) → (B × sph (n+1), B × lower n)` used in the suspension step: the
"small" pair is the Thom pair of the bundle of one lower rank.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/
def mBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {v | ‖v‖ ≤ 1}

/-- The unit sphere of `EuclideanSpace ℝ (Fin n)`. -/
def mSph (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {v | ‖v‖ = 1}

/-- The **lower region** of the unit sphere of `EuclideanSpace ℝ (Fin (n+1))`: the unit vectors
whose last coordinate is at most `1/2`.  It is a closed disc, hence contractible, and it contains
the equator `EuclideanSpace ℝ (Fin n) × {0}`. -/
def mLower (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ v.ofLp (Fin.last n) ≤ 1 / 2}

/-- The **equator** of the unit sphere of `EuclideanSpace ℝ (Fin (n+1))`: the unit vectors with
last coordinate `0`. -/
def mEquator (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {v | ‖v‖ = 1 ∧ v.ofLp (Fin.last n) = 0}

/-- The **cap map**: the graph of the upper hemisphere. -/
def capMap (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) w.ofLp (Real.sqrt (1 - ‖w‖ ^ 2)))

theorem capMap_ofLp (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    (capMap n w).ofLp = Fin.snoc (α := fun _ => ℝ) w.ofLp (Real.sqrt (1 - ‖w‖ ^ 2)) :=
  WithLp.ofLp_toLp _ _

@[simp] theorem capMap_castSucc (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (capMap n w).ofLp i.castSucc = w.ofLp i := by
  rw [capMap_ofLp, Fin.snoc_castSucc]

@[simp] theorem capMap_last (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    (capMap n w).ofLp (Fin.last n) = Real.sqrt (1 - ‖w‖ ^ 2) := by
  rw [capMap_ofLp]
  exact Fin.snoc_last (α := fun _ => ℝ) (x := Real.sqrt (1 - ‖w‖ ^ 2)) (p := w.ofLp)

theorem norm_capMap (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ ≤ 1) :
    ‖capMap n w‖ ^ 2 = ‖w‖ ^ 2 + (1 - ‖w‖ ^ 2) := by
  have hnn : (0:ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h1 : ‖capMap n w‖ ^ 2 = ∑ i, ‖(capMap n w).ofLp i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∑ i, ‖(capMap n w).ofLp i‖ ^ 2
      = ∑ i : Fin n, ‖w.ofLp i‖ ^ 2 + (Real.sqrt (1 - ‖w‖ ^ 2)) ^ 2 := by
    rw [Fin.sum_univ_castSucc (f := fun i => ‖(capMap n w).ofLp i‖ ^ 2)]
    simp only [capMap_castSucc, capMap_last, Real.norm_eq_abs, sq_abs]
  have h3 : ∑ i : Fin n, ‖w.ofLp i‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)).symm
  have h4 : (Real.sqrt (1 - ‖w‖ ^ 2)) ^ 2 = 1 - ‖w‖ ^ 2 := Real.sq_sqrt hnn
  rw [h1, h2, h3, h4]

theorem capMap_mem_mSph (n : ℕ) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ mBall n) :
    capMap n w ∈ mSph (n + 1) := by
  have h1 : ‖w‖ ≤ 1 := hw
  have h2 : (0:ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h3 := norm_capMap n w h1
  have h4 : ‖w‖ ^ 2 + (1 - ‖w‖ ^ 2) = 1 := by ring
  have h5 : ‖capMap n w‖ ^ 2 = 1 := by rw [h3, h4]
  show ‖capMap n w‖ = 1
  nlinarith [norm_nonneg (capMap n w)]

theorem capMap_last_nonneg (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    0 ≤ (capMap n w).ofLp (Fin.last n) := by
  rw [capMap_last]; exact Real.sqrt_nonneg _

theorem capMap_last_eq_zero (n : ℕ) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ mSph n) :
    (capMap n w).ofLp (Fin.last n) = 0 := by
  rw [capMap_last, hw]
  norm_num

theorem capMap_mem_equator (n : ℕ) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ mSph n) :
    capMap n w ∈ mEquator n :=
  ⟨capMap_mem_mSph n (by show ‖w‖ ≤ 1; rw [hw]), capMap_last_eq_zero n hw⟩

theorem equator_subset_mLower (n : ℕ) : mEquator n ⊆ mLower n := by
  intro v hv
  obtain ⟨h1, h2⟩ := hv
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem continuous_capMap (n : ℕ) : Continuous (capMap n) := by
  change Continuous fun w : EuclideanSpace ℝ (Fin n) =>
    WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) w.ofLp (Real.sqrt (1 - ‖w‖ ^ 2)))
  fun_prop

/-- The closed ball of `EuclideanSpace ℝ (Fin n)`, as a topological space. -/
abbrev MBall (n : ℕ) : Type := {q : EuclideanSpace ℝ (Fin n) // q ∈ mBall n}

/-- The unit sphere of `EuclideanSpace ℝ (Fin n)`, as a topological space. -/
abbrev MSph (n : ℕ) : Type := {q : EuclideanSpace ℝ (Fin n) // q ∈ mSph n}

/-- The **cap map as a map of pairs**, `(B × ball n, B × sph n) → (B × ℝ^{n+1}, B × lower n)`. -/
def capMapPair (B : Type) [TopologicalSpace B] (n : ℕ) :
    C(B × MBall n, B × EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun q => (q.1, capMap n q.2),
    continuous_fst.prodMk ((continuous_capMap n).comp
      ((continuous_subtype_val).comp (continuous_snd :
        Continuous fun q : B × MBall n => q.2)))⟩

/-- The cap map as a map of pairs, seen on the sphere components. -/
theorem capMapPair_mem_mLower {B : Type} [TopologicalSpace B] (n : ℕ) (q : B × MBall n)
    (hq : q.2.1 ∈ mSph n) : (capMapPair B n q).2 ∈ mLower n := by
  show capMap n (q.2 : EuclideanSpace ℝ (Fin n)) ∈ mLower n
  exact equator_subset_mLower n (capMap_mem_equator n hq)

/-- The cap map as a map of pairs into the **sphere bundle** `B × sph (n+1)`, with the lower
region as the subspace. -/
def capMapPairSph (B : Type) [TopologicalSpace B] (n : ℕ) : C(B × MBall n, B × MSph (n + 1)) :=
  ⟨fun q => (q.1, ⟨capMap n q.2, capMap_mem_mSph n q.2.2⟩),
    continuous_fst.prodMk (Continuous.subtype_mk
      ((continuous_capMap n).comp ((continuous_subtype_val).comp (continuous_snd :
        Continuous fun q : B × MBall n => q.2)))
      (fun q => capMap_mem_mSph n q.2.2))⟩

end

end Work.Thom
