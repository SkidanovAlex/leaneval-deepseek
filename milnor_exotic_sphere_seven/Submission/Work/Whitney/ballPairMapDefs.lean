import Mathlib
import Submission.Work.Thom.ModelGeometry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The explicit map of pairs `(Δᵖ, ∂Δᵖ) → (Dᵖ, Sᵖ⁻¹)`

This file sets up the concrete map used by `Work.Whitney.ballPairMap`: the cone map from the
standard `p`-simplex onto the closed unit ball of `ℝᵖ`, which sends the boundary of the simplex onto
the unit sphere and its interior onto the open ball.

The construction is the "distance-to-the-boundary normalised" radial map.  With `c := 1/(p+1)` the
barycentre of `stdSimplex ℝ (Fin (p+1))`, `m z := minᵢ zᵢ` the smallest barycentric coordinate and
the level `t z := 1 - (p+1) m z` (so `t = 0` at the barycentre, `t = 1` exactly on the boundary),
the map is

  `ballPairVal p z = (t z · ‖d z‖⁻¹) • d z`,  where `d z := (z 0 - c, …, z (p-1) - c)`,

i.e. the unit vector of the displacement `z - c` (projected to the first `p` coordinates) scaled by
the level.  Its norm is exactly `t z`, so it lands in the closed ball, lies on the sphere exactly on
the boundary of the simplex, and (this is the content of
`Work.Whitney.ballPairMapSurjective.ballPairVal_surjective`) it is onto.

The three facts about `t` that drive everything:
* `0 ≤ t ≤ 1` on the simplex (`ballPairLev_mem`), because `0 ≤ m z ≤ c`;
* `t z = 1 ↔ ∃ i, z i = 0` (`ballPairLev_eq_one_iff`), i.e. `t = 1` exactly on the boundary;
* `‖ballPairVal p z‖ = t z` (`norm_ballPairVal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Whitney

open Work.Thom
open Filter
open scoped Topology

noncomputable section

/-- The barycentric coordinate of the centre of `stdSimplex ℝ (Fin (p+1))`, i.e. `1/(p+1)`. -/
def ballPairCtr (p : ℕ) : ℝ := (((p+1 : ℕ)) : ℝ)⁻¹

/-- The smallest barycentric coordinate of a point of `ℝ^{p+1}`. -/
def ballPairMin (p : ℕ) (z : Fin (p+1) → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (p+1))).inf' Finset.univ_nonempty z

/-- The **cone level** `1 - (p+1) · minᵢ zᵢ`: it vanishes at the barycentre and equals `1` exactly
on the boundary of the simplex. -/
def ballPairLev (p : ℕ) (z : Fin (p+1) → ℝ) : ℝ :=
  1 - ((p+1 : ℕ) : ℝ) * ballPairMin p z

/-- The displacement of `z` from the barycentre, in the first `p` coordinates. -/
def ballPairDis (p : ℕ) (z : Fin (p+1) → ℝ) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i : Fin p => z i.castSucc - ballPairCtr p)

/-- The fibre component of the ball-pair map: the level times the unit vector of the displacement
from the barycentre. -/
def ballPairVal (p : ℕ) (z : Fin (p+1) → ℝ) : EuclideanSpace ℝ (Fin p) :=
  (ballPairLev p z * (‖ballPairDis p z‖)⁻¹) • ballPairDis p z

/-! ### The minimum of the barycentric coordinates -/

/-- The minimum of the coordinates is attained. -/
theorem ballPairMin_attained (p : ℕ) (z : Fin (p+1) → ℝ) :
    ∃ i : Fin (p+1), ballPairMin p z = z i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z
  exact ⟨i, hi⟩

/-- The minimum of the coordinates is a lower bound for each of them. -/
theorem ballPairMin_le (p : ℕ) (z : Fin (p+1) → ℝ) (i : Fin (p+1)) :
    ballPairMin p z ≤ z i :=
  Finset.inf'_le z (Finset.mem_univ i)

/-- The minimum of the barycentric coordinates is nonnegative. -/
theorem ballPairMin_nonneg (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    0 ≤ ballPairMin p (z : Fin (p+1) → ℝ) := by
  obtain ⟨i, hi⟩ := ballPairMin_attained p (z : Fin (p+1) → ℝ)
  rw [hi]
  exact z.2.1 i

/-- The minimum of the barycentric coordinates is at most their average `1/(p+1)`. -/
theorem ballPairMin_le_ctr (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ballPairMin p (z : Fin (p+1) → ℝ) ≤ ballPairCtr p := by
  have hle : ((p+1 : ℕ) : ℝ) * ballPairMin p (z : Fin (p+1) → ℝ) ≤ 1 := by
    calc ((p+1 : ℕ) : ℝ) * ballPairMin p (z : Fin (p+1) → ℝ)
        = ∑ _i : Fin (p+1), ballPairMin p (z : Fin (p+1) → ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin (p+1), (z : Fin (p+1) → ℝ) i :=
          Finset.sum_le_sum (fun i _ => ballPairMin_le p (z : Fin (p+1) → ℝ) i)
      _ = 1 := z.2.2
  rw [ballPairCtr, inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < ((p+1 : ℕ) : ℝ))]
  linarith [hle]

/-- The level lies in `[0,1]` on the simplex. -/
theorem ballPairLev_mem (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    0 ≤ ballPairLev p (z : Fin (p+1) → ℝ) ∧ ballPairLev p (z : Fin (p+1) → ℝ) ≤ 1 := by
  have h0 := ballPairMin_nonneg p z
  have hc := ballPairMin_le_ctr p z
  have hN : (0:ℝ) ≤ ((p+1 : ℕ) : ℝ) := by positivity
  have hNc : ((p+1 : ℕ) : ℝ) * ballPairCtr p = 1 := by
    rw [ballPairCtr]
    exact mul_inv_cancel₀ (by positivity)
  have h1 : ((p+1 : ℕ) : ℝ) * ballPairMin p (z : Fin (p+1) → ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hc hN
    linarith [this, hNc]
  constructor
  · rw [ballPairLev]; linarith
  · have h2 : 0 ≤ ((p+1 : ℕ) : ℝ) * ballPairMin p (z : Fin (p+1) → ℝ) := mul_nonneg hN h0
    rw [ballPairLev]; linarith

/-- The minimum of the barycentric coordinates vanishes exactly on the boundary of the simplex. -/
theorem ballPairMin_eq_zero_iff (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ballPairMin p (z : Fin (p+1) → ℝ) = 0 ↔ ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := ballPairMin_attained p (z : Fin (p+1) → ℝ)
    exact ⟨i, by rw [← hi, h]⟩
  · rintro ⟨i, hi⟩
    exact le_antisymm (by rw [← hi]; exact ballPairMin_le p (z : Fin (p+1) → ℝ) i)
      (ballPairMin_nonneg p z)

/-- **The level equals `1` exactly on the boundary of the simplex.** -/
theorem ballPairLev_eq_one_iff (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ballPairLev p (z : Fin (p+1) → ℝ) = 1 ↔ ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0 := by
  have hiff : ballPairLev p (z : Fin (p+1) → ℝ) = 1 ↔
      ((p+1 : ℕ) : ℝ) * ballPairMin p (z : Fin (p+1) → ℝ) = 0 := by
    rw [ballPairLev]
    constructor <;> intro h <;> linarith
  rw [hiff]
  constructor
  · intro h2
    have hmin : ballPairMin p (z : Fin (p+1) → ℝ) = 0 :=
      (mul_eq_zero.mp h2).resolve_left (by positivity)
    exact (ballPairMin_eq_zero_iff p z).mp hmin
  · intro h
    rw [(ballPairMin_eq_zero_iff p z).mpr h, mul_zero]

/-! ### The displacement and the fibre component -/

/-- If the displacement from the barycentre vanishes, so does the level. -/
theorem ballPairLev_eq_zero_of_dis_eq_zero (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (h : ballPairDis p (z : Fin (p+1) → ℝ) = 0) :
    ballPairLev p (z : Fin (p+1) → ℝ) = 0 := by
  have hco : ∀ i : Fin p, (z : Fin (p+1) → ℝ) i.castSucc = ballPairCtr p := by
    intro i
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin p) => x.ofLp i) h
    have h3 : (z : Fin (p+1) → ℝ) i.castSucc - ballPairCtr p = 0 := by
      simpa [ballPairDis] using h2
    linarith
  have hsum : (∑ i : Fin p, (z : Fin (p+1) → ℝ) i.castSucc)
      + (z : Fin (p+1) → ℝ) (Fin.last p) = 1 := by
    have h' := z.2.2
    rw [Fin.sum_univ_castSucc] at h'
    exact h'
  have h1 : (∑ i : Fin p, (z : Fin (p+1) → ℝ) i.castSucc) = (p : ℝ) * ballPairCtr p := by
    rw [Finset.sum_congr rfl (fun i _ => hco i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [h1] at hsum
  have hNc : ((p+1 : ℕ) : ℝ) * ballPairCtr p = 1 := by
    rw [ballPairCtr]
    exact mul_inv_cancel₀ (by positivity)
  have hp1 : (((p+1 : ℕ)) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  have hNc' := hNc
  rw [hp1] at hNc'
  have hc1 : (p : ℝ) * ballPairCtr p + ballPairCtr p = 1 := by nlinarith [hNc']
  have hlast : (z : Fin (p+1) → ℝ) (Fin.last p) = ballPairCtr p := by linarith [hsum, hc1]
  have hmin : ballPairMin p (z : Fin (p+1) → ℝ) = ballPairCtr p := by
    refine le_antisymm ?_ ?_
    · exact le_trans (ballPairMin_le p (z : Fin (p+1) → ℝ) (Fin.last p)) (le_of_eq hlast)
    · refine Finset.le_inf' Finset.univ_nonempty (z : Fin (p+1) → ℝ) (fun i _ => ?_)
      exact Fin.lastCases (le_of_eq hlast.symm) (fun j => le_of_eq (hco j).symm) i
  rw [ballPairLev, hmin]
  linarith [hNc]

/-- **The norm of the fibre component is the level.** -/
theorem norm_ballPairVal (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ‖ballPairVal p (z : Fin (p+1) → ℝ)‖ = ballPairLev p (z : Fin (p+1) → ℝ) := by
  by_cases h : ballPairLev p (z : Fin (p+1) → ℝ) = 0
  · rw [ballPairVal, h, zero_mul, zero_smul, norm_zero]
  · have hlev : 0 < ballPairLev p (z : Fin (p+1) → ℝ) :=
      lt_of_le_of_ne (ballPairLev_mem p z).1 (Ne.symm h)
    have hd : ballPairDis p (z : Fin (p+1) → ℝ) ≠ 0 :=
      fun hd => h (ballPairLev_eq_zero_of_dis_eq_zero p z hd)
    have hn : ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    calc ‖ballPairVal p (z : Fin (p+1) → ℝ)‖
        = ‖ballPairLev p (z : Fin (p+1) → ℝ) * (‖ballPairDis p (z : Fin (p+1) → ℝ)‖)⁻¹‖
            * ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ := by rw [ballPairVal, norm_smul]
      _ = ballPairLev p (z : Fin (p+1) → ℝ) * (‖ballPairDis p (z : Fin (p+1) → ℝ)‖)⁻¹
            * ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ := by
          rw [Real.norm_of_nonneg
            (mul_nonneg (le_of_lt hlev) (inv_nonneg.mpr (norm_nonneg _)))]
      _ = ballPairLev p (z : Fin (p+1) → ℝ) := by
          rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]

/-- The fibre component lies in the closed unit ball. -/
theorem ballPairVal_mem_ball (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ballPairVal p (z : Fin (p+1) → ℝ) ∈ mBall p := by
  show ‖ballPairVal p (z : Fin (p+1) → ℝ)‖ ≤ 1
  rw [norm_ballPairVal]
  exact (ballPairLev_mem p z).2

/-- The fibre component lies on the unit sphere exactly on the boundary of the simplex. -/
theorem ballPairVal_mem_sph_iff (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    ballPairVal p (z : Fin (p+1) → ℝ) ∈ mSph p ↔
      ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0 := by
  show ‖ballPairVal p (z : Fin (p+1) → ℝ)‖ = 1 ↔ _
  rw [norm_ballPairVal]
  exact ballPairLev_eq_one_iff p z

/-! ### Continuity -/

theorem continuous_ballPairMin (p : ℕ) : Continuous (ballPairMin p) := by
  unfold ballPairMin
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem continuous_ballPairLev (p : ℕ) : Continuous (ballPairLev p) := by
  unfold ballPairLev
  exact continuous_const.sub (continuous_const.mul (continuous_ballPairMin p))

theorem continuous_ballPairDis (p : ℕ) : Continuous (ballPairDis p) := by
  unfold ballPairDis
  exact (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).comp
    (continuous_pi (fun i => (continuous_apply i.castSucc).sub continuous_const))

/-- Continuity of the fibre component at a point of the simplex where the displacement from the
barycentre does not vanish (the general case). -/
theorem continuousAt_ballPairVal_simplex_of_ne (p : ℕ) (z₀ : stdSimplex ℝ (Fin (p+1)))
    (h : ballPairDis p (z₀ : Fin (p+1) → ℝ) ≠ 0) :
    ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ)) z₀ := by
  have hlev : ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) =>
      ballPairLev p (z : Fin (p+1) → ℝ)) z₀ :=
    ((continuous_ballPairLev p).comp continuous_subtype_val).continuousAt
  have hdis : ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) =>
      ballPairDis p (z : Fin (p+1) → ℝ)) z₀ :=
    ((continuous_ballPairDis p).comp continuous_subtype_val).continuousAt
  have hinv : ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) =>
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖)⁻¹) z₀ :=
    hdis.norm.inv₀ (norm_ne_zero_iff.mpr h)
  exact (hlev.mul hinv).smul hdis

/-- Continuity of the fibre component at the barycentre, where the displacement vanishes: the norm
of the map is the level, which tends to `0`. -/
theorem continuousAt_ballPairVal_simplex_of_eq (p : ℕ) (z₀ : stdSimplex ℝ (Fin (p+1)))
    (h : ballPairDis p (z₀ : Fin (p+1) → ℝ) = 0) :
    ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ)) z₀ := by
  have hlev0 : ballPairLev p (z₀ : Fin (p+1) → ℝ) = 0 := ballPairLev_eq_zero_of_dis_eq_zero p z₀ h
  have hval0 : ballPairVal p (z₀ : Fin (p+1) → ℝ) = 0 := by
    rw [ballPairVal, h, hlev0, zero_mul, zero_smul]
  have hlevcont : ContinuousAt (fun z : stdSimplex ℝ (Fin (p+1)) =>
      ballPairLev p (z : Fin (p+1) → ℝ)) z₀ :=
    ((continuous_ballPairLev p).comp continuous_subtype_val).continuousAt
  have h2 : Tendsto (fun z : stdSimplex ℝ (Fin (p+1)) =>
      ballPairLev p (z : Fin (p+1) → ℝ)) (𝓝 z₀) (𝓝 0) := by
    simpa only [hlev0] using hlevcont.tendsto
  have h3 : Tendsto (fun z : stdSimplex ℝ (Fin (p+1)) =>
      ‖ballPairVal p (z : Fin (p+1) → ℝ)‖) (𝓝 z₀) (𝓝 0) :=
    h2.congr' (Filter.Eventually.of_forall fun z => (norm_ballPairVal p z).symm)
  have ht : Tendsto (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ))
      (𝓝 z₀) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr h3
  show Tendsto (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ))
    (𝓝 z₀) (𝓝 (ballPairVal p (z₀ : Fin (p+1) → ℝ)))
  rw [hval0]
  exact ht

/-- Continuity of the fibre component on the simplex. -/
theorem continuous_ballPairVal_simplex (p : ℕ) :
    Continuous (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases h : ballPairDis p (z₀ : Fin (p+1) → ℝ) = 0
  · exact continuousAt_ballPairVal_simplex_of_eq p z₀ h
  · exact continuousAt_ballPairVal_simplex_of_ne p z₀ h

end

end Work.Whitney
