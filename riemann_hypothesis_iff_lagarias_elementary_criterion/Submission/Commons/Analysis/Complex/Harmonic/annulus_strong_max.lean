import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Topology.Connected.Clopen
import Submission.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn
import Submission.Commons.Analysis.Complex.Harmonic.annulus_preconnected

open Set Metric Complex InnerProductSpace
open scoped Topology Real

namespace Commons.Analysis.Complex.Harmonic

/-- Given a point `q` of the open annulus at which the harmonic function `u` equals its
maximum `u p`, there is a ball around `q` contained in the open annulus on which `u`
equals `u p`.  (Choose a small ball around `q` inside the open annulus, where the
pointwise bound `u ≤ u p` holds, and apply the strong maximum principle on that ball.) -/
private theorem annulus_eqOn_ball_of_eq {u : ℂ → ℝ} {r R : ℝ} {p q : ℂ}
    (hu : HarmonicOnNhd u {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R})
    (hmax : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → u z ≤ u p)
    (hq : r < ‖q‖) (hqR : ‖q‖ < R) (huq : u q = u p) :
    ∃ ρ > 0, ∀ x ∈ ball q ρ, r < ‖x‖ ∧ ‖x‖ < R ∧ u x = u p := by
  let ρ : ℝ := min (‖q‖ - r) (R - ‖q‖)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (sub_pos.mpr hq) (sub_pos.mpr hqR)
  have hball_sub : ball q ρ ⊆ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
    intro x hx
    have hxρ : ‖x - q‖ < ρ := by simpa [dist_eq_norm, dist_comm] using hx
    have hρ1 : ρ ≤ ‖q‖ - r := by dsimp [ρ]; exact min_le_left _ _
    have hρ2 : ρ ≤ R - ‖q‖ := by dsimp [ρ]; exact min_le_right _ _
    constructor
    · have hq_le : ‖q‖ ≤ ‖x‖ + ‖x - q‖ := by
        calc
          ‖q‖ = ‖x + (q - x)‖ := by rw [show x + (q - x) = q by ring]
          _ ≤ ‖x‖ + ‖q - x‖ := norm_add_le x (q - x)
          _ = ‖x‖ + ‖x - q‖ := by rw [← neg_sub, norm_neg]
      have hxr' : ‖x - q‖ < ‖q‖ - r := lt_of_lt_of_le hxρ hρ1
      linarith
    · have hx_le : ‖x‖ ≤ ‖x - q‖ + ‖q‖ := by
        calc
          ‖x‖ = ‖(x - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - q‖ + ‖q‖ := norm_add_le (x - q) q
      calc
        ‖x‖ ≤ ‖x - q‖ + ‖q‖ := hx_le
        _ < ρ + ‖q‖ := by linarith
        _ ≤ R := by linarith
  have hu_ball : HarmonicOnNhd u (ball q ρ) := hu.mono hball_sub
  have hle : ∀ z ∈ ball q ρ, u z ≤ u q := by
    intro z hz
    have hzA := hball_sub hz
    have hzmax : u z ≤ u p := hmax z (le_of_lt hzA.1) (le_of_lt hzA.2)
    rwa [huq]
  have heq : ∀ z ∈ ball q ρ, u z = u q := harmonic_eqOn_ball_of_isMaxOn hρ0 hu_ball hle
  refine ⟨ρ, hρ0, ?_⟩
  intro x hx
  refine ⟨(hball_sub hx).1, (hball_sub hx).2, ?_⟩
  exact (heq x hx).trans huq

/-- **Strong maximum principle for harmonic functions on an open annulus.**
If `u : ℂ → ℝ` is harmonic on the open annulus `{z | r < ‖z‖ ∧ ‖z‖ < R}`
and attains its maximum over the whole closed annulus at an interior point
`p`, then `u` is constant on the open annulus.  (Mean-value property on
small circles around points of `{u = u p}`, openness/closeness of that set
inside the connected open annulus.) -/
theorem annulus_strong_max {u : ℂ → ℝ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOnNhd u {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R})
    {p : ℂ} (hp : r < ‖p‖) (hpR : ‖p‖ < R)
    (hmax : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → u z ≤ u p) :
    ∀ z : ℂ, r < ‖z‖ → ‖z‖ < R → u z = u p := by
  classical
  let M : ℝ := u p
  have hM : u p = M := rfl
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  let S : Set ℂ := {z : ℂ | z ∈ A ∧ u z = M}
  have hpA : p ∈ A := by dsimp [A]; exact ⟨hp, hpR⟩
  /- The set `S` of points of the annulus where `u = u p` is open (in `ℂ`): around each
     of its points the annulus-maximum lemma gives a whole ball of equal values. -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro q hq
    rcases hq with ⟨hqA, huqM⟩
    have hq1 : r < ‖q‖ := (show q ∈ A from hqA).1
    have hq2 : ‖q‖ < R := (show q ∈ A from hqA).2
    obtain ⟨ρ, hρ, hball⟩ := annulus_eqOn_ball_of_eq (u := u) (r := r) (R := R) (p := p) (q := q)
      hu hmax hq1 hq2 (by simpa [M] using huqM)
    refine ⟨ρ, hρ, ?_⟩
    intro x hx
    exact ⟨⟨(hball x hx).1, (hball x hx).2.1⟩, by simpa [M] using (hball x hx).2.2⟩
  /- Restrict to the connected topological space `B` of the points of the open annulus;
     in `B`, the set of points with `u = u p` is open (preimage of `S`) and closed
     (preimage of the singleton `{M}` under the continuous map `u`), and nonempty
     (it contains `p`).  Connectedness forces it to be everything. -/
  let B : Type := {z : ℂ // r < ‖z‖ ∧ ‖z‖ < R}
  let val : B → ℂ := fun x => x.1
  have hpre : PreconnectedSpace B := by
    dsimp [B]
    exact annulus_preconnected hr hrR
  let S' : Set B := {x : B | u (val x) = M}
  have hS'_eq_preimage : S' = val ⁻¹' S := by
    ext x
    dsimp [S', val, S]
    constructor <;> intro hx
    · exact ⟨(show x.1 ∈ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} from x.2), hx⟩
    · exact hx.2
  have hS'_open : IsOpen S' := by
    rw [hS'_eq_preimage]
    exact hS_open.preimage continuous_subtype_val
  have hS'_closed : IsClosed S' := by
    have hcont : Continuous fun x : B => u x.1 := by
      dsimp [B]
      exact hu.continuousOn.domRestrict
    have hS' : S' = (fun x : B => u x.1) ⁻¹' {M} := by
      ext x
      dsimp [S', val]
      simp
    rw [hS']
    exact isClosed_singleton.preimage hcont
  have hS'_ne : S'.Nonempty := by
    refine ⟨⟨p, hp, hpR⟩, ?_⟩
    rfl
  have hS'_univ : S' = univ := IsClopen.eq_univ ⟨hS'_closed, hS'_open⟩ hS'_ne
  intro z hz1 hz2
  have hzS' : (⟨z, hz1, hz2⟩ : B) ∈ S' := by
    rw [hS'_univ]
    trivial
  have hu_zM : u z = M := by
    exact hzS'
  simpa [M] using hu_zM

end Commons.Analysis.Complex.Harmonic
