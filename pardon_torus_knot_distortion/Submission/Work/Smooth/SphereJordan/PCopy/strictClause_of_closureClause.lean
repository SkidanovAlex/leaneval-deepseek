import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.PCopy.interior_closure_V_eq
import Submission.Work.Smooth.SphereJordan.PCopy.Setup

namespace Work.Smooth.SphereJordan

/-!
# The strict clause from the closed clause

Let `S : PlaneSchoenflies γ` be a plane Schoenflies datum for a simple closed curve `γ` whose trace
lies in the open unit disc (`hball`), and let `Θ` be a homeomorphism of the model disc `𝔻` fixing
its boundary circle pointwise (`hfix`).  Suppose the *closed* clause

`x ∈ closure S.V ↔ ‖Θ x‖ ≤ 1/2`

holds for every `x : 𝔻`.  Then the *strict* clause `x ∈ S.V ↔ ‖Θ x‖ < 1/2` holds as well.

The two facts that make this work are

* `interior (closure S.V) = S.V` (`Work.Smooth.SphereJordan.pcinterior_closure_V_eq`), so `S.V` is
  recovered from `closure S.V` by taking interiors;
* the interior, in the model disc, of the closed half-disc `{‖·‖ ≤ 1/2}` is the open half-disc
  `{‖·‖ < 1/2}` (`pcinterior_halfDisc` below).

Indeed, writing `B := {x : 𝔻 | (x : ℂ) ∈ closure S.V}` and `A := {x : 𝔻 | (x : ℂ) ∈ S.V}`, the
closed clause says `B = Θ ⁻¹' {‖·‖ ≤ 1/2}`; hence, since `Θ` is a homeomorphism,

`interior B = Θ ⁻¹' {‖·‖ < 1/2} = {x : 𝔻 | ‖Θ x‖ < 1/2}`.

On the other hand `interior B = A`: the inclusion `⊆` holds because `x ∈ interior B` forces
`‖x‖ < 1` — a point of `B` on the unit circle would be a boundary point of the disc, fixed by `Θ`
through `hfix`, hence would satisfy `‖Θ x‖ = 1`, contradicting the closed clause `‖Θ x‖ ≤ 1/2` —
and away from the boundary circle an open neighbourhood in `𝔻` is an open neighbourhood in `ℂ`, so
`x ∈ interior (closure S.V) = S.V`; while the inclusion `⊇` holds because `A` is the preimage under
the continuous map `x ↦ (x : ℂ)` of the open set `interior (closure S.V)`, and `A ⊆ B`.
-/

/-- In the model disc `𝔻`, the interior of the closed half-disc `{‖z‖ ≤ 1/2}` is the open half-disc
`{‖z‖ < 1/2}`.  The point of the statement is that a point at distance exactly `1/2` from the
centre is not interior: the radial point `(1 + δ) z` with `0 < δ ≤ 1` stays in `𝔻` and is
arbitrarily close to `z`. -/
theorem pcinterior_halfDisc :
    interior {y : Work.Smooth.SphereJordan.Disc | ‖(y : ℂ)‖ ≤ (1 : ℝ) / 2}
      = {y : Work.Smooth.SphereJordan.Disc | ‖(y : ℂ)‖ < (1 : ℝ) / 2} := by
  apply Set.Subset.antisymm
  · intro y hy
    have hyK : y ∈ ({y : Disc | ‖(y : ℂ)‖ ≤ (1:ℝ) / 2} : Set Disc) := interior_subset hy
    have hyKn : ‖(y : ℂ)‖ ≤ (1:ℝ)/2 := hyK
    by_contra hlt
    rw [Set.mem_setOf_eq, not_lt] at hlt
    have hyabs : ‖(y : ℂ)‖ = 1 / 2 := le_antisymm hyKn hlt
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
      (isOpen_interior (s := {y : Disc | ‖(y : ℂ)‖ ≤ (1:ℝ)/2})) y hy
    have hεsubK : Metric.ball y ε ⊆ {y : Disc | ‖(y:ℂ)‖ ≤ (1:ℝ)/2} := hεsub.trans interior_subset
    have hδpos : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    have hδle : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
    have hycn : ‖(((1 + min (ε/2) 1 : ℝ) : ℂ) * (y : ℂ))‖ = (1 + min (ε/2) 1) * (1/2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < 1 + min (ε/2) 1), hyabs]
    have hycle : ‖(((1 + min (ε/2) 1 : ℝ) : ℂ) * (y : ℂ))‖ ≤ 1 := by
      rw [hycn]; nlinarith [min_le_right (ε/2) 1]
    let y' : Disc := ⟨(((1 + min (ε/2) 1 : ℝ) : ℂ) * (y : ℂ)), by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hycle⟩
    have hy'val : ((y' : Disc) : ℂ) = (((1 + min (ε/2) 1 : ℝ) : ℂ) * (y : ℂ)) := rfl
    have hmem : y' ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, hy'val]
      have hsplit : (((1 + min (ε/2) 1 : ℝ) : ℂ) * (y : ℂ)) - (y : ℂ)
          = (((min (ε/2) 1 : ℝ) : ℂ)) * (y : ℂ) := by push_cast; ring
      rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, hyabs]
      nlinarith [hδle, hε]
    have hmemK : y' ∈ ({y : Disc | ‖(y:ℂ)‖ ≤ (1:ℝ)/2} : Set Disc) := hεsubK hmem
    have hmemKn : ‖((y' : Disc) : ℂ)‖ ≤ (1:ℝ)/2 := hmemK
    rw [hy'val, hycn] at hmemKn
    nlinarith [hδpos]
  · intro y hy
    have hK'sub : {y : Disc | ‖(y:ℂ)‖ < (1:ℝ)/2} ⊆ {y : Disc | ‖(y:ℂ)‖ ≤ (1:ℝ)/2} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact le_of_lt hz
    have hK'open : IsOpen {y : Disc | ‖(y:ℂ)‖ < (1:ℝ)/2} :=
      isOpen_lt (f := fun y : Disc => ‖(y:ℂ)‖) (g := fun _ => (1:ℝ)/2)
        continuous_subtype_val.norm continuous_const
    exact interior_maximal hK'sub hK'open hy

theorem pcstrictClause_of_closureClause (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc}
    (hfix : ∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ)
    (hcl : ∀ x : Work.Smooth.SphereJordan.Disc,
      (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
      ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :
    ∀ x : Work.Smooth.SphereJordan.Disc,
      (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ S.V) ↔
      ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2 := by
  have hInt := pcinterior_halfDisc
  have hB : {x : Disc | (x:ℂ) ∈ closure S.V}
      = Θ ⁻¹' ({y : Disc | ‖(y:ℂ)‖ ≤ (1:ℝ)/2} : Set Disc) := by
    ext x
    exact hcl x
  have hIntB : interior {x : Disc | (x:ℂ) ∈ closure S.V}
      = {x : Disc | ‖((Θ x : Disc) : ℂ)‖ < (1:ℝ)/2} := by
    rw [hB, ← Homeomorph.preimage_interior Θ ({y : Disc | ‖(y:ℂ)‖ ≤ (1:ℝ)/2} : Set Disc), hInt]
    rfl
  have hAeq : {x : Disc | (x:ℂ) ∈ S.V} = {x : Disc | (x:ℂ) ∈ interior (closure S.V)} := by
    rw [pcinterior_closure_V_eq S]
  have hAB : {x : Disc | (x:ℂ) ∈ S.V} ⊆ interior {x : Disc | (x:ℂ) ∈ closure S.V} := by
    have hopen : IsOpen {x : Disc | (x:ℂ) ∈ S.V} := by
      rw [hAeq]
      exact isOpen_interior.preimage continuous_subtype_val
    exact interior_maximal (fun x hx => subset_closure hx) hopen
  have hBA : interior {x : Disc | (x:ℂ) ∈ closure S.V} ⊆ {x : Disc | (x:ℂ) ∈ S.V} := by
    intro x hx
    have hxC : ‖((Θ x : Disc) : ℂ)‖ < (1:ℝ)/2 := by
      have hh : x ∈ ({x : Disc | ‖((Θ x : Disc) : ℂ)‖ < (1:ℝ)/2} : Set Disc) := by
        rw [← hIntB]; exact hx
      exact hh
    have hnormx : ‖(x:ℂ)‖ < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      have hxle : ‖(x:ℂ)‖ ≤ 1 := by
        have h2 := x.2; rwa [Metric.mem_closedBall, dist_zero_right] at h2
      have heq : ‖(x:ℂ)‖ = 1 := le_antisymm hxle hcon
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq x heq
      have hxfix : Θ x = x := by rw [← hθ]; exact hfix θ
      have h1 : ‖((Θ x : Disc) : ℂ)‖ = 1 := by rw [hxfix]; exact heq
      rw [h1] at hxC
      linarith
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
      (isOpen_interior (s := {x : Disc | (x:ℂ) ∈ closure S.V})) x hx
    have hρpos : 0 < min ε (1 - ‖(x:ℂ)‖) := lt_min hε (by linarith)
    have hballsub : Metric.ball (x:ℂ) (min ε (1 - ‖(x:ℂ)‖)) ⊆ closure S.V := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hzlt : ‖z‖ < 1 := by
        have h1 : ‖z‖ ≤ ‖z - (x:ℂ)‖ + ‖(x:ℂ)‖ := by
          have h2 := norm_add_le (z - (x:ℂ)) (x:ℂ)
          rwa [sub_add_cancel] at h2
        have h3 : ‖z - (x:ℂ)‖ < 1 - ‖(x:ℂ)‖ := lt_of_lt_of_le hz (min_le_right _ _)
        linarith
      let z' : Disc := ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hzlt⟩
      have hz'val : ((z' : Disc) : ℂ) = z := rfl
      have hmem : z' ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, hz'val]
        exact lt_of_lt_of_le hz (min_le_left _ _)
      have hthis : z' ∈ interior {x : Disc | (x:ℂ) ∈ closure S.V} := hεsub hmem
      have hthis2 : ((z' : Disc) : ℂ) ∈ closure S.V := by
        simpa only [Set.mem_setOf_eq] using interior_subset hthis
      rwa [hz'val] at hthis2
    have hmem : (x:ℂ) ∈ interior (closure S.V) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Metric.ball_mem_nhds (x:ℂ) hρpos) hballsub
    rwa [pcinterior_closure_V_eq S] at hmem
  intro x
  have h1 : x ∈ ({x : Disc | (x:ℂ) ∈ S.V} : Set Disc)
      ↔ x ∈ ({x : Disc | ‖((Θ x : Disc) : ℂ)‖ < (1:ℝ)/2} : Set Disc) := by
    rw [← hIntB]
    exact ⟨fun hx => hAB hx, fun hx => hBA hx⟩
  exact h1

end Work.Smooth.SphereJordan
