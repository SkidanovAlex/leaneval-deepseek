import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.CapCoord
import Submission.Work.KT.merCoord_norm_sq
import Submission.Work.KT.continuous_merCoord

/-!
# The closed cap `{tgtHeight ≤ 1/2}` of `Tgt m = S^{2m}` is contractible

`capTminus m = {x : Tgt m | tgtHeight m x ≤ 1/2}` is a closed disc of dimension `2m`, so it is
contractible, and in fact contractible to *any* of its points.

The contraction is written down explicitly in the coordinates `tgtCoords m x = (a, s) ∈ Eu m × ℝ`
introduced in `Submission/Work/KT/CapCoord.lean` (`s = tgtHeight m x` is the height, and
`‖a‖ ^ 2 + s ^ 2 = 1`).  The meridian formula `merCoord m η (a, s)` slides the point along its
meridian to the height `-1 + η (s + 1)`, staying on the unit sphere and — for `η ≤ 1` — inside the
cap `{s ≤ 1/2}`.  For `η = 1` it is the identity and for `η = 0` it is the south pole `(0, -1)`,
which gives the first half of the homotopy: the cap is contracted to its south pole.  The second
half moves the south pole to `t0` along the meridian of `t0` (the same formula, with source `t0`
and the parameter running from `0` to `1`).  The two halves are glued at the south pole, where the
parameter is `0` for both, so the resulting homotopy is continuous by `continuous_if_le`.
-/

namespace Work.KT

noncomputable section

open scoped Topology

/-! ## The norm of a meridian point -/

lemma norm_toLp_merCoord (m : ℕ) {z : Eu m × ℝ} {η : ℝ}
    (hz : ‖z.1‖ ^ 2 + z.2 ^ 2 = 1) (hs : z.2 ≤ 1 / 2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ‖(WithLp.toLp 2 (merCoord m η z) : WithLp 2 (Eu m × ℝ))‖ = 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (merCoord m η z))
  rw [WithLp.toLp_fst, WithLp.toLp_snd] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [merCoord_norm_sq m hz hs hη0 hη1] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (merCoord m η z))]

lemma mem_sphere_merCoord (m : ℕ) (x : Tgt m) (η : ℝ) (hx : tgtHeight m x ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    euclTgtIso m (WithLp.toLp 2 (merCoord m η (tgtCoords m x))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 1))) 1 := by
  rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact norm_toLp_merCoord m (norm_sq_tgtCoords m x) hx hη0 hη1

lemma mem_cap_merCoord (m : ℕ) (x : Tgt m) (η : ℝ) (hx : tgtHeight m x ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    tgtHeight m ⟨euclTgtIso m (WithLp.toLp 2 (merCoord m η (tgtCoords m x))),
        mem_sphere_merCoord m x η hx hη0 hη1⟩ ≤ 1 / 2 := by
  have hz2 : -1 ≤ (tgtCoords m x).2 := by
    have h := norm_sq_tgtCoords m x
    nlinarith [norm_nonneg (tgtCoords m x).1, h]
  have hkey : (merCoord m η (tgtCoords m x)).2 ≤ 1 / 2 := merCoord_snd_le m hz2 hx hη0 hη1
  simpa [tgtHeight] using hkey

/-! ## The meridian contraction -/

/-- The meridian contraction of the cap: at parameter `η`, the point `x` of the cap is moved along
its meridian to the height `-1 + η (tgtHeight m x + 1)`.  `η = 1` gives `x` back and `η = 0` gives
the south pole. -/
def merPt (m : ℕ) (x : Tgt m) (η : ℝ) (hx : tgtHeight m x ≤ 1 / 2) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) : capTminus m :=
  ⟨⟨euclTgtIso m (WithLp.toLp 2 (merCoord m η (tgtCoords m x))),
      mem_sphere_merCoord m x η hx hη0 hη1⟩,
   mem_cap_merCoord m x η hx hη0 hη1⟩

lemma continuous_merPt (m : ℕ) {X : Type*} [TopologicalSpace X] (x : X → Tgt m) (η : X → ℝ)
    (hx : Continuous x) (hη : Continuous η) (hxcap : ∀ p, tgtHeight m (x p) ≤ 1 / 2)
    (hη0 : ∀ p, 0 ≤ η p) (hη1 : ∀ p, η p ≤ 1) :
    Continuous fun p => merPt m (x p) (η p) (hxcap p) (hη0 p) (hη1 p) := by
  have hcoord : Continuous fun p => tgtCoords m (x p) := (continuous_tgtCoords m).comp hx
  have hsub : Continuous fun p : X =>
      (⟨(η p, tgtCoords m (x p)), hxcap p⟩ : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2}) :=
    Continuous.subtype_mk (hη.prodMk hcoord) (fun p => hxcap p)
  have hmer : Continuous fun p => merCoord m (η p) (tgtCoords m (x p)) :=
    (continuous_merCoord m).comp hsub
  have htoLp : Continuous fun p => (WithLp.toLp 2 (merCoord m (η p) (tgtCoords m (x p))) :
      WithLp 2 (Eu m × ℝ)) := (WithLp.prod_continuous_toLp 2 (Eu m) ℝ).comp hmer
  have hval : Continuous fun p =>
      euclTgtIso m (WithLp.toLp 2 (merCoord m (η p) (tgtCoords m (x p)))) :=
    (euclTgtIso m).continuous.comp htoLp
  exact Continuous.subtype_mk
    (Continuous.subtype_mk hval
      (fun p => mem_sphere_merCoord m (x p) (η p) (hxcap p) (hη0 p) (hη1 p)))
    (fun p => mem_cap_merCoord m (x p) (η p) (hxcap p) (hη0 p) (hη1 p))

/-! ## The two halves of the homotopy -/

lemma etaOne_nonneg (t : unitInterval) : 0 ≤ max 0 (1 - 2 * (t : ℝ)) := le_max_left _ _

lemma etaOne_le_one (t : unitInterval) : max 0 (1 - 2 * (t : ℝ)) ≤ 1 :=
  max_le zero_le_one (by linarith [t.2.1])

lemma etaTwo_nonneg (t : unitInterval) : 0 ≤ max 0 (2 * (t : ℝ) - 1) := le_max_left _ _

lemma etaTwo_le_one (t : unitInterval) : max 0 (2 * (t : ℝ) - 1) ≤ 1 :=
  max_le zero_le_one (by linarith [t.2.2])

/-- First half of the homotopy: contract `x` to the south pole along its own meridian. -/
def capBranch1Fun (m : ℕ) (p : capTminus m × unitInterval) : capTminus m :=
  merPt m (p.1 : Tgt m) (max 0 (1 - 2 * (p.2 : ℝ))) p.1.2 (etaOne_nonneg p.2) (etaOne_le_one p.2)

/-- Second half of the homotopy: move the south pole to `t0` along the meridian of `t0`. -/
def capBranch2Fun (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTminus m)
    (p : capTminus m × unitInterval) : capTminus m :=
  merPt m t0 (max 0 (2 * (p.2 : ℝ) - 1)) ht0 (etaTwo_nonneg p.2) (etaTwo_le_one p.2)

lemma continuous_capBranch1Fun (m : ℕ) : Continuous (capBranch1Fun m) := by
  exact continuous_merPt m (fun p : capTminus m × unitInterval => (p.1 : Tgt m))
    (fun p => max 0 (1 - 2 * (p.2 : ℝ)))
    (continuous_subtype_val.comp continuous_fst) (by fun_prop)
    (fun p => p.1.2) (fun p => etaOne_nonneg p.2) (fun p => etaOne_le_one p.2)

lemma continuous_capBranch2Fun (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTminus m) :
    Continuous (capBranch2Fun m t0 ht0) := by
  exact continuous_merPt m (fun _ : capTminus m × unitInterval => t0)
    (fun p => max 0 (2 * (p.2 : ℝ) - 1))
    continuous_const (by fun_prop)
    (fun _ => ht0) (fun p => etaTwo_nonneg p.2) (fun p => etaTwo_le_one p.2)

/-! ## The values at the two ends -/

lemma capBranch1_zero (m : ℕ) (x : capTminus m) :
    capBranch1Fun m (x, (0 : unitInterval)) = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [capBranch1Fun, merPt]
  have hmax : max 0 (1 - 2 * (((0 : unitInterval)) : ℝ)) = 1 := by
    rw [show (((0 : unitInterval)) : ℝ) = 0 by simp]
    norm_num
  have hne : (tgtCoords m (x : Tgt m)).2 ≠ 1 := by
    have h : (tgtCoords m (x : Tgt m)).2 ≤ 1 / 2 := x.2
    linarith
  rw [hmax, merCoord_one m hne, euclTgtIso_toLp_tgtCoords]

lemma capBranch2_one (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTminus m) (x : capTminus m) :
    capBranch2Fun m t0 ht0 (x, (1 : unitInterval)) = ⟨t0, ht0⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [capBranch2Fun, merPt]
  have hmax : max 0 (2 * (((1 : unitInterval)) : ℝ) - 1) = 1 := by
    rw [show (((1 : unitInterval)) : ℝ) = 1 by simp]
    norm_num
  have hne : (tgtCoords m t0).2 ≠ 1 := by
    have h : (tgtCoords m t0).2 ≤ 1 / 2 := ht0
    linarith
  rw [hmax, merCoord_one m hne, euclTgtIso_toLp_tgtCoords]

/-- At the middle of the homotopy both halves give the south pole, so they glue. -/
lemma capBranch_eq_half (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTminus m)
    (p : capTminus m × unitInterval) (hp : (p.2 : ℝ) = 1 / 2) :
    capBranch1Fun m p = capBranch2Fun m t0 ht0 p := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [capBranch1Fun, capBranch2Fun, merPt]
  have h1 : max 0 (1 - 2 * (p.2 : ℝ)) = 0 := by rw [hp]; norm_num
  have h2 : max 0 (2 * (p.2 : ℝ) - 1) = 0 := by rw [hp]; norm_num
  rw [h1, h2, merCoord_zero, merCoord_zero]

/-! ## The contraction -/

/-- The closed cap `capTminus m = {tgtHeight ≤ 1/2}` of `Tgt m = S^{2m}` is contractible to any of
its points, by an explicit homotopy staying inside the cap: there is a continuous
`H : capTminus m × [0,1] → capTminus m` with `H (x,0) = x` and `H (x,1) = t0`. -/
theorem capTminus_contract (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTminus m) :
    ∃ H : C(capTminus m × unitInterval, capTminus m),
      (∀ x, H (x, 0) = x) ∧ ∀ x, H (x, 1) = ⟨t0, ht0⟩ := by
  classical
  have hcont : Continuous fun p : capTminus m × unitInterval =>
      if (p.2 : ℝ) ≤ 1 / 2 then capBranch1Fun m p else capBranch2Fun m t0 ht0 p := by
    refine continuous_if_le (f := fun p : capTminus m × unitInterval => (p.2 : ℝ))
      (g := fun _ : capTminus m × unitInterval => (1 : ℝ) / 2) (by fun_prop) continuous_const
      (continuous_capBranch1Fun m).continuousOn
      (continuous_capBranch2Fun m t0 ht0).continuousOn ?_
    intro p hp
    exact capBranch_eq_half m t0 ht0 p hp
  refine ⟨⟨_, hcont⟩, ?_, ?_⟩
  · intro x
    show (if (((0 : unitInterval) : ℝ) ≤ 1 / 2) then capBranch1Fun m (x, 0)
      else capBranch2Fun m t0 ht0 (x, 0)) = x
    rw [if_pos (by norm_num)]
    exact capBranch1_zero m x
  · intro x
    show (if (((1 : unitInterval) : ℝ) ≤ 1 / 2) then capBranch1Fun m (x, 1)
      else capBranch2Fun m t0 ht0 (x, 1)) = ⟨t0, ht0⟩
    rw [if_neg (by norm_num)]
    exact capBranch2_one m t0 ht0 x

end

end Work.KT
