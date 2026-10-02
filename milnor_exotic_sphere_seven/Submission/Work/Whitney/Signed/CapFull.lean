import Mathlib
import Submission.Work.Whitney.Signed.CapBasics

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The caps as maps of pairs into `Y × ℝᵏ⁺¹`

`Work.Whitney.capX` and `Work.Whitney.lowerCapX` map `Y × Dᵏ` into `tcmX Y k 1 = Y × (ℝᵏ × ℝ)`.
Composing with the coordinate identification `Work.Whitney.tcmF` (a map onto `Y × ℝᵏ⁺¹`) gives the
canonical **upper** and **lower** caps `capFull` and `lowerCapFull` into `Y × ℝᵏ⁺¹`, whose images
are the upper hemisphere and the lower hemisphere of the unit sphere `Y × Sᵏ`.

The three sets of the suspension picture are

* `capFull`'s image — the upper hemisphere, the "cap";
* `BandFull Y k = {p | p.2 ∈ mLower k}` — the lower band (a closed disc of the sphere, containing
  the equator and the lower hemisphere), which is where `Work.Thom.stepSph` is *relative*;
* `LowerHemi Y k = {p | p.2 ∈ mLower k ∧ (last coordinate of p.2) ≤ 0}` — the closed lower
  hemisphere, on which the `0`-cochain `Work.Whitney.gammaSharp` (the indicator of
  `{last ≥ 0}`) vanishes at every vertex strictly inside it (its image meets `{last = 0}` only on
  the equator).

These are the sets in which the "filler" of the rank-one model product formula is phrased: a
`(k+1)`-chain whose boundary is `cap_* B + L` with `L` carried by `LowerHemi` (resp. `BandFull`).
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The **upper cap** into `Y × ℝᵏ⁺¹`: the graph of the upper hemisphere, over the ball. -/
def capFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    C(Y × MBall k, Y × EuclideanSpace ℝ (Fin (k + 1))) :=
  ⟨fun q => (q.1, capMap k q.2.1),
    continuous_fst.prodMk ((continuous_capMap k).comp
      (continuous_subtype_val.comp continuous_snd))⟩

/-- The **lower cap** into `Y × ℝᵏ⁺¹`: the graph of the lower hemisphere, over the ball. -/
def lowerCapFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    C(Y × MBall k, Y × EuclideanSpace ℝ (Fin (k + 1))) :=
  ⟨fun q => (q.1, lowerCapMap k q.2.1),
    continuous_fst.prodMk ((continuous_lowerCapMap k).comp
      (continuous_subtype_val.comp continuous_snd))⟩

/-- The **lower band** of the unit sphere of `ℝᵏ⁺¹` over `Y`: the points whose fibre coordinate
lies in `Work.Thom.mLower k`.  (The band as a subset of the *total* space `Y × ℝᵏ⁺¹`; the band as a
subset of the sphere bundle is `Work.Thom.SphB Y k`.) -/
def BandFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    Set (Y × EuclideanSpace ℝ (Fin (k + 1))) :=
  {p | p.2 ∈ mLower k}

/-- The **closed lower hemisphere** over `Y`: the points of the unit sphere whose last coordinate is
`≤ 0`.  (`Work.Thom.capMap`'s mirror image; it is where the lower cap lands.) -/
def LowerHemi (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    Set (Y × EuclideanSpace ℝ (Fin (k + 1))) :=
  {p | p.2 ∈ mLower k ∧ p.2.ofLp (Fin.last k) ≤ 0}

/-- The lower band, pulled back to `tcmX Y k 1` by the coordinate identification. -/
def BandTcm (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set (tcmX Y k 1) :=
  (tcmF Y k 1) ⁻¹' BandFull Y k

/-- The closed lower hemisphere, pulled back to `tcmX Y k 1` by the coordinate identification. -/
def LowerHemiTcm (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set (tcmX Y k 1) :=
  (tcmF Y k 1) ⁻¹' LowerHemi Y k

/-- The lower band is contained in the sphere bundle. -/
theorem BandFull_subset_Sph (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    BandFull Y k ⊆ Sph Y (k + 1) := fun _ hp => hp.1

/-- The closed lower hemisphere is contained in the sphere bundle. -/
theorem LowerHemi_subset_Sph (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    LowerHemi Y k ⊆ Sph Y (k + 1) := fun _ hp => hp.1.1

/-- The closed lower hemisphere is contained in the band. -/
theorem LowerHemi_subset_BandFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    LowerHemi Y k ⊆ BandFull Y k := fun _ hp => hp.1

/-- **The upper cap is `capX` in `tcmF`-coordinates.** -/
theorem tcmF_comp_capX_eq_capFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    (tcmF Y k 1).comp (capX Y k) = capFull Y k := by
  apply ContinuousMap.ext
  intro q
  exact tcmF_capX_apply Y k q

/-- **The lower cap is `lowerCapX` in `tcmF`-coordinates.** -/
theorem tcmF_comp_lowerCapX_eq_lowerCapFull (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    (tcmF Y k 1).comp (lowerCapX Y k) = lowerCapFull Y k := by
  apply ContinuousMap.ext
  intro q
  exact tcmF_lowerCapX_apply Y k q

/-- The upper cap lands on the sphere. -/
theorem capFull_image_subset_Sph (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    ∀ q, capFull Y k q ∈ Sph Y (k + 1) :=
  fun q => capMap_mem_mSph k q.2.2

/-- The lower cap lands in the closed lower hemisphere. -/
theorem lowerCapFull_image_subset_LowerHemi (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    ∀ q, lowerCapFull Y k q ∈ LowerHemi Y k := by
  intro q
  simp only [lowerCapFull, ContinuousMap.coe_mk]
  refine ⟨⟨lowerCapMap_mem_mSph k q.2.2, ?_⟩, ?_⟩
  · rw [lowerCapMap_last]
    have h : 0 ≤ Real.sqrt (1 - ‖(q.2 : EuclideanSpace ℝ (Fin k))‖ ^ 2) := Real.sqrt_nonneg _
    linarith
  · rw [lowerCapMap_last]
    have h : 0 ≤ Real.sqrt (1 - ‖(q.2 : EuclideanSpace ℝ (Fin k))‖ ^ 2) := Real.sqrt_nonneg _
    linarith

/-- The **lower cap lands in the closed lower hemisphere** of `tcmX Y k 1`. -/
theorem lowerCapX_image_subset_LowerHemiTcm (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    ∀ q, lowerCapX Y k q ∈ LowerHemiTcm Y k := by
  intro q
  show tcmF Y k 1 (lowerCapX Y k q) ∈ LowerHemi Y k
  rw [tcmF_lowerCapX_apply]
  exact lowerCapFull_image_subset_LowerHemi Y k q

/-- The **open lower hemisphere** in `tcmX Y k 1`-coordinates: the points whose last coordinate is
(strictly) negative.  Together with `Work.Whitney.tcmA` it covers the closed lower hemisphere, and
on a simplex carried by it the `0`-cochain `Work.Whitney.gammaSharp` vanishes at every vertex (in
particular at the back vertex, which is the one entering the Alexander–Whitney product with a
degree-`0` second factor). -/
def LowerOpenTcm (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set (tcmX Y k 1) :=
  {x | lastCoord Y k x < 0}

end

end Work.Whitney
