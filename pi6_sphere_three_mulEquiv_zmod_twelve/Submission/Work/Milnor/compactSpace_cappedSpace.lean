import Mathlib
import Submission.Work.Milnor.CapCompact
import Submission.Work.Milnor.Topology

set_option synthInstance.maxHeartbeats 400000

/-!
# Compactness of the capped space `X = D(ξ) ∪_e D⁸`

The glued space `cappedSpace D` of a compact capping datum `D` (i.e. a datum satisfying
`IsCompactCapping e D`) is compact.  The point of the compact (as opposed to the non-compact)
capping is the *inverting* radius function `r(ν) = (ν - 1/2)⁻¹`: it sends the far end `ν → ∞` of
the collar to the *origin* of the second piece `ℝ⁸`, so that the whole glued space is covered by
the two compact cores

* the closed unit disc bundle `{ν ≤ 1} ⊆ Vk (-2)`, itself covered by the unit boxes
  `{‖x‖ ≤ 1, ‖y‖ ≤ 1}` in the two charts of the vector bundle `ξ` (the two charts of `Vk (-2)`
  are glued at infinity), and
* the closed ball `{‖z‖ ≤ 2} ⊆ ℝ⁸`.

A point `p` of the collar with `ν p > 1` is glued to `(ν p - 1/2)⁻¹ • e(ψ p)`, which lies in the
ball of radius `2`; conversely a point `z` of `ℝ⁸` with `‖z‖ > 2` is glued to `capFunInvK e z`,
whose fibre norm is `‖z‖⁻¹ + 1/2 < 1`.  Hence the glued space is the continuous image of the
compact set `capCore (-2) ⊔ {‖z‖ ≤ 2}`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor
open scoped Classical

noncomputable section

/-! ## The unit box in the model space -/

/-- The "unit box" `{‖x‖ ≤ 1, ‖y‖ ≤ 1}` in the model space `MSpace8 = ℝ⁴ × ℍ`. -/
def capBox : Set MSpace8 := {p | ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1}

theorem isCompact_capBox : IsCompact capBox := by
  have h : capBox = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 ×ˢ
      Metric.closedBall (0 : Quaternion ℝ) 1 := by
    ext p
    simp [capBox, Metric.mem_closedBall, dist_zero_right]
  rw [h]
  exact IsCompact.prod (isCompact_closedBall _ 1) (isCompact_closedBall _ 1)

/-- The closed unit disc bundle `{ν ≤ 1}` of `Vk k`, covered by the images of the unit box in the
two charts of the vector bundle. -/
def capCore (k : ℤ) : Set (Vk k) := (vData k).ιX '' capBox ∪ (vData k).ιY '' capBox

/-! ## The two clutching maps send the far end of the base into the unit box -/

/-- The norm of the fibre coordinate is preserved by the inverse twisting `y ↦ q⁻ᵐ y q` for `q` of
norm one. -/
theorem norm_vTwistInv (m : ℤ) {q : Quaternion ℝ} (hq : ‖q‖ = 1) (y : Quaternion ℝ) :
    ‖vTwistInv m q y‖ = ‖y‖ := by
  rw [vTwistInv, norm_mul, norm_mul, norm_zpow, hq, one_zpow, one_mul, mul_one]

theorem vMap_mem_capBox (k : ℤ) {p : MSpace8} (h1 : 1 < ‖p.1‖) (h2 : ‖p.2‖ ≤ 1) :
    vMap k p ∈ capBox := by
  refine ⟨?_, ?_⟩
  · show ‖(invBase p.1 : EuclideanSpace ℝ (Fin 4))‖ ≤ 1
    rw [norm_invBase]
    exact inv_le_one_of_one_le₀ (le_of_lt h1)
  · show ‖(vTwist (-k) ((unitDir p.1 : QS3) : Quaternion ℝ) p.2)‖ ≤ 1
    rw [norm_vTwist (-k) (norm_unitDir_coe p.1)]
    exact h2

theorem vMapInv_mem_capBox (k : ℤ) {p : MSpace8} (h1 : 1 < ‖p.1‖) (h2 : ‖p.2‖ ≤ 1) :
    vMapInv k p ∈ capBox := by
  refine ⟨?_, ?_⟩
  · show ‖(invBase p.1 : EuclideanSpace ℝ (Fin 4))‖ ≤ 1
    rw [norm_invBase]
    exact inv_le_one_of_one_le₀ (le_of_lt h1)
  · show ‖(vTwistInv (-k) ((unitDir p.1 : QS3) : Quaternion ℝ) p.2)‖ ≤ 1
    rw [norm_vTwistInv (-k) (norm_unitDir_coe p.1)]
    exact h2

/-! ## The closed unit disc bundle is covered by the two unit boxes -/

theorem fibreBall_subset (k : ℤ) :
    {z : Vk k | fibreNormFun k z ≤ 1} ⊆ capCore k := by
  intro z hz
  obtain ⟨a, rfl⟩ := Quotient.exists_rep z
  rcases a with p | p
  · -- first chart
    have hz' : ‖p.2‖ ≤ 1 := by
      have : (⟦Sum.inl p⟧ : Vk k) = (vData k).ιX p := rfl
      rw [this] at hz
      simpa using hz
    by_cases h1 : ‖p.1‖ ≤ 1
    · exact Or.inl ⟨p, ⟨h1, hz'⟩, rfl⟩
    · push Not at h1
      have hp0 : p ∈ (vData k).U := by
        show p.1 ≠ 0
        intro h0; rw [h0, norm_zero] at h1; norm_num at h1
      exact Or.inr ⟨vMap k p, vMap_mem_capBox k h1 hz',
        ((vData k).ιX_eq_ιY_iff.mpr ⟨hp0, rfl⟩).symm⟩
  · -- second chart
    have hz' : ‖p.2‖ ≤ 1 := by
      have : (⟦Sum.inr p⟧ : Vk k) = (vData k).ιY p := rfl
      rw [this] at hz
      simpa using hz
    by_cases h1 : ‖p.1‖ ≤ 1
    · exact Or.inr ⟨p, ⟨h1, hz'⟩, rfl⟩
    · push Not at h1
      have hp0 : p.1 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h1; norm_num at h1
      refine Or.inl ⟨vMapInv k p, vMapInv_mem_capBox k h1 hz', ?_⟩
      exact (vData k).ιX_eq_ιY_iff.mpr
        ⟨by show invBase p.1 ≠ 0; exact invBase_ne_zero hp0, (vMap_inv k hp0).2⟩

/-! ## The main theorem -/

theorem compactSpace_cappedSpace
    (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel)
    (D : Work.Milnor.CapData) (hD : Work.Milnor.IsCompactCapping e D) :
    CompactSpace (Work.Milnor.cappedSpace D) := by
  obtain ⟨hU, _, hφ⟩ := hD
  -- the two compact cores
  have hA : IsCompact (capCore (-2)) :=
    (isCompact_capBox.image (vData (-2)).continuous_ιX).union
      (isCompact_capBox.image (vData (-2)).continuous_ιY)
  have hB : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) 2) :=
    isCompact_closedBall _ 2
  have hKc : IsCompact
      (Sum.inl '' capCore (-2)
        ∪ Sum.inr '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) 2) :=
    (hA.image continuous_inl).union (hB.image continuous_inr)
  -- the two cores cover the glued space
  have hcover : (Set.univ : Set (cappedSpace D)) ⊆
      D.q '' (Sum.inl '' capCore (-2)
        ∪ Sum.inr '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) 2) := by
    rintro z -
    obtain ⟨a, rfl⟩ := Quotient.exists_rep z
    rcases a with p | y
    · -- a point of the disc bundle
      by_cases hp : fibreNormFun (-2) p ≤ 1
      · exact ⟨Sum.inl p, Or.inl ⟨p, fibreBall_subset (-2) hp, rfl⟩, rfl⟩
      · push Not at hp
        have hpcol : p ∈ collar (-2) := mem_collar.mpr (by linarith)
        have hn : ‖capFunK e p‖ ≤ 2 := by
          rw [norm_capFunK e hpcol]
          have h1 : (fibreNormFun (-2) p - 1 / 2)⁻¹ < (1 / 2 : ℝ)⁻¹ :=
            (inv_lt_inv₀ (by linarith) (by norm_num)).mpr (by linarith)
          have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
          linarith
        have hpU : p ∈ D.U := by rw [hU]; exact hpcol
        refine ⟨Sum.inr (capFunK e p), Or.inr ⟨capFunK e p, ?_, rfl⟩, ?_⟩
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hn
        · change D.ιY (capFunK e p) = D.ιX p
          exact (D.ιX_eq_ιY_iff.mpr ⟨hpU, hφ ⟨p, hpU⟩⟩).symm
    · -- a point of ℝ⁸
      by_cases hy : ‖y‖ ≤ 2
      · exact ⟨Sum.inr y, Or.inr ⟨y, by rw [Metric.mem_closedBall, dist_zero_right]; exact hy, rfl⟩, rfl⟩
      · push Not at hy
        have hy0 : y ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hy; norm_num at hy
        have hcol : capFunInvK e y ∈ collar (-2) := capFunInvK_mem e hy0
        have hn : fibreNormFun (-2) (capFunInvK e y) ≤ 1 := by
          rw [fibreNormFun_capFunInvK e hy0]
          have h1 : ‖y‖⁻¹ < (2 : ℝ)⁻¹ :=
            (inv_lt_inv₀ (norm_pos_iff.mpr hy0) (by norm_num)).mpr hy
          have h2 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
          linarith
        have hyU : capFunInvK e y ∈ D.U := by rw [hU]; exact hcol
        refine ⟨Sum.inl (capFunInvK e y), Or.inl ⟨capFunInvK e y, fibreBall_subset (-2) hn, rfl⟩, ?_⟩
        change D.ιX (capFunInvK e y) = D.ιY y
        exact D.ιX_eq_ιY_iff.mpr
          ⟨hyU, by rw [hφ ⟨capFunInvK e y, hyU⟩, capFunK_capFunInvK e hy0]⟩
  exact isCompact_univ_iff.mp (by
    rw [← Set.eq_univ_of_univ_subset hcover]
    exact hKc.image D.continuous_q)

end

end Work.Milnor
