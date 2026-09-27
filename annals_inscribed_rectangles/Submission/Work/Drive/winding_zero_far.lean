import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.degree_homotopic

namespace Work.Drive

open Submission.Collision (dirC)

/-- **The winding number vanishes for points outside a ball containing the curve.**

If every point of the curve is closer to `c` than `p` is, then `winding γ hγ hp = 0`.  Indeed the
sup-norm on `ℝ × ℝ` gives a coordinate `i` with `|p i - c i| = dist p c > dist (γ t) c ≥ |γ t i - c i|`
for every `t`, so every vector `γ t - p` has its `i`-th coordinate on the same side of `0` as
`c i - p i`; all the vectors therefore lie in an open half-space, which is convex and does not contain
`0`, so the direction map is homotopic to a constant and its degree vanishes.

Proof ingredients: `Degree` theory in `Submission/Work/Drive/WindingNumber.lean`,
`degree_homotopic` for homotopy invariance, `degree_const` for the degree of a constant; the
homotopy is the straight line from `dirCurve γ hγ p hp` to the constant map with value the direction of
`c - p` (which also lies in the half-space).  The hypothesis `hp` is in fact implied by `h`, and is
kept only so that `winding` is stated with its usual argument. -/
theorem winding_zero_far {γ : UnitAddCircle → ℝ × ℝ} (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) {c : ℝ × ℝ} (h : ∀ t : UnitAddCircle, dist (γ t) c < dist p c) :
    winding γ hγ hp = 0 := by
  -- a coordinate functional separating `γ t - p` from `0` for every `t`
  obtain ⟨ℓ, hℓlt⟩ : ∃ ℓ : (ℝ × ℝ) →L[ℝ] ℝ,
      ∀ t : UnitAddCircle, |ℓ (γ t - c)| < |ℓ (c - p)| := by
    rcases le_total (dist p.1 c.1) (dist p.2 c.2) with hle | hle
    · refine ⟨ContinuousLinearMap.snd ℝ ℝ ℝ, fun t => ?_⟩
      show |(γ t - c).2| < |(c - p).2|
      rw [Prod.snd_sub, Prod.snd_sub]
      calc |(γ t).2 - c.2| = dist (γ t).2 c.2 := (Real.dist_eq _ _).symm
        _ ≤ max (dist (γ t).1 c.1) (dist (γ t).2 c.2) := le_max_right _ _
        _ = dist (γ t) c := Prod.dist_eq.symm
        _ < dist p c := h t
        _ = dist p.2 c.2 := by rw [Prod.dist_eq, max_eq_right hle]
        _ = |p.2 - c.2| := Real.dist_eq _ _
        _ = |c.2 - p.2| := abs_sub_comm _ _
    · refine ⟨ContinuousLinearMap.fst ℝ ℝ ℝ, fun t => ?_⟩
      show |(γ t - c).1| < |(c - p).1|
      rw [Prod.fst_sub, Prod.fst_sub]
      calc |(γ t).1 - c.1| = dist (γ t).1 c.1 := (Real.dist_eq _ _).symm
        _ ≤ max (dist (γ t).1 c.1) (dist (γ t).2 c.2) := le_max_left _ _
        _ = dist (γ t) c := Prod.dist_eq.symm
        _ < dist p c := h t
        _ = dist p.1 c.1 := by rw [Prod.dist_eq, max_eq_left hle]
        _ = |p.1 - c.1| := Real.dist_eq _ _
        _ = |c.1 - p.1| := abs_sub_comm _ _
  -- the straight-line homotopy from `γ t - p` to `c - p`, which never vanishes
  let q : unitInterval × UnitAddCircle → ℝ × ℝ :=
    fun x => (1 - (x.1 : ℝ)) • (γ x.2 - p) + (x.1 : ℝ) • (c - p)
  have hqcont : Continuous q := by
    unfold q
    fun_prop
  have hqne : ∀ x : unitInterval × UnitAddCircle, q x ≠ 0 := by
    rintro ⟨s, t⟩ h0
    have ha : |ℓ (γ t - c)| < |ℓ (c - p)| := hℓlt t
    have hkey : ℓ (q (s, t)) = (1 - (s : ℝ)) * ℓ (γ t - c) + ℓ (c - p) := by
      have h1 : γ t - p = (γ t - c) + (c - p) := by abel
      simp only [q, h1, map_add, map_smul]
      ring
    have hzero : (1 - (s : ℝ)) * ℓ (γ t - c) + ℓ (c - p) = 0 := by
      rw [← hkey, h0, map_zero]
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hle1 : |1 - (s : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hbound : |(1 - (s : ℝ)) * ℓ (γ t - c)| ≤ |ℓ (γ t - c)| := by
      calc |(1 - (s : ℝ)) * ℓ (γ t - c)| = |1 - (s : ℝ)| * |ℓ (γ t - c)| := abs_mul _ _
        _ ≤ 1 * |ℓ (γ t - c)| := mul_le_mul_of_nonneg_right hle1 (abs_nonneg _)
        _ = |ℓ (γ t - c)| := one_mul _
    have habs : |ℓ (c - p)| = |(1 - (s : ℝ)) * ℓ (γ t - c)| := by
      have hneg : ℓ (c - p) = -((1 - (s : ℝ)) * ℓ (γ t - c)) := by linarith
      rw [hneg, abs_neg]
    linarith
  -- the induced homotopy of the direction maps
  let F : unitInterval × UnitAddCircle → UnitAddCircle := fun x => dirC (q x)
  have hFcont : Continuous F := by
    have hcomp : ContinuousOn (dirC ∘ q) Set.univ :=
      Submission.Configuration.continuousOn_dirC.comp hqcont.continuousOn (fun x _ => hqne x)
    exact continuousOn_univ.mp hcomp
  have hhom : (⟨dirCurve γ hγ p hp, continuous_dirCurve γ hγ p hp⟩ :
      C(UnitAddCircle, UnitAddCircle)).Homotopic
      ⟨fun _ : UnitAddCircle => dirC (c - p), continuous_const⟩ := by
    refine ⟨ContinuousMap.Homotopy.mk ⟨F, hFcont⟩ ?_ ?_⟩
    · intro t
      change F ((0 : unitInterval), t) = dirCurve γ hγ p hp t
      have h1 : F ((0 : unitInterval), t) = dirC (γ t - p) := by
        show dirC (q ((0 : unitInterval), t)) = dirC (γ t - p)
        rw [show q ((0 : unitInterval), t) = γ t - p from by simp [q]]
      rw [h1]
      rfl
    · intro t
      change F ((1 : unitInterval), t) = dirC (c - p)
      show dirC (q ((1 : unitInterval), t)) = dirC (c - p)
      rw [show q ((1 : unitInterval), t) = c - p from by simp [q]]
  have hdeg := degree_homotopic hhom
  show winding γ hγ hp = 0
  rw [winding]
  exact hdeg.trans (degree_const (dirC (c - p)))

end Work.Drive
