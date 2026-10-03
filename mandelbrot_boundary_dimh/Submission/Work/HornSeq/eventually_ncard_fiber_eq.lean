import Mathlib
import Submission.Work.Horn.fiber_finite
import Submission.Work.Horn.eventually_ncard_eq_of_local_trivialization
import Submission.Work.Horn.exists_ball_injOn_and_mapsTo
import Submission.Work.Horn.exists_pos_le_half_dist

/-!
# The number of `B`-preimages is locally constant at a regular value

`Work.HornSeq.eventually_ncard_fiber_eq`.  For `B` open and preconnected, `f` holomorphic on `B`
and non-locally-constant at `c ∈ B`, `f` "proper" over compact subsets of `B`
(`hprop`), and `w ∈ B` a **regular value** with respect to `B`
(`∀ z ∈ B, f z = w → deriv f z ≠ 0`), the cardinality of the fibre `B ∩ f ⁻¹' {t}` is constant
for `t` in a neighbourhood of `w`.

Proof.  `S := B ∩ f ⁻¹' {w}` is finite (`Work.Horn.fiber_finite`).  At each `x ∈ S` the inverse
function theorem (`Work.Horn.exists_ball_injOn_and_mapsTo`) gives a ball `ball x (ρ x) ⊆ B` on
which `f` is injective and whose image contains a ball around `w`; choosing `ρ x` below half the
distance to the other points of `S` (`Work.Horn.exists_pos_le_half_dist`) makes the balls
pairwise disjoint.  Then `Work.Horn.eventually_ncard_eq_of_local_trivialization` counts the
fibres of `t` near `w` as exactly one point per ball and nothing outside (properness).
-/

namespace Work.HornSeq

open Filter Metric

theorem eventually_ncard_fiber_eq {B : Set ℂ} {f : ℂ → ℂ} {c w : ℂ}
    (hB : IsOpen B) (hpre : IsPreconnected B) (hf : DifferentiableOn ℂ f B)
    (hcB : c ∈ B) (hnc : ¬ ∀ᶠ z in nhds c, f z = f c)
    (hprop : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hw : w ∈ B) (hcrit : ∀ z ∈ B, f z = w → deriv f z ≠ 0) :
    ∀ᶠ t in nhds w, (B ∩ f ⁻¹' {t}).ncard = (B ∩ f ⁻¹' {w}).ncard := by
  classical
  -- the fibre of `w` is finite
  have hSfin : (B ∩ f ⁻¹' {w}).Finite :=
    Work.Horn.fiber_finite hB hpre hf hcB hnc hprop hw
  set S : Finset ℂ := hSfin.toFinset with hSdef
  have hSset : (S : Set ℂ) = B ∩ f ⁻¹' {w} := by
    rw [hSdef]; exact hSfin.coe_toFinset
  have hS : ∀ z : ℂ, z ∈ (S : Set ℂ) ↔ z ∈ B ∧ f z = w := by
    intro z; rw [hSset]; simp
  -- uniform separation radius for the points of `S`
  obtain ⟨m, hmpos, hmhalf⟩ := Work.Horn.exists_pos_le_half_dist S
  -- local inverse-function data at each point of `S`, shrunk below `m`
  have hex : ∀ x : ℂ, ∃ ρx δx : ℝ, x ∈ (S : Set ℂ) →
      0 < ρx ∧ ρx < m x ∧ 0 < δx ∧ Metric.ball x ρx ⊆ B ∧
      Set.InjOn f (Metric.ball x ρx) ∧
      (∀ u : ℂ, ‖u - w‖ < δx → ∃ v ∈ Metric.ball x ρx, f v = u) := by
    intro x
    by_cases hx : x ∈ (S : Set ℂ)
    · obtain ⟨hxB, hfx⟩ := (hS x).mp hx
      have hne : deriv f x ≠ 0 := hcrit x hxB hfx
      obtain ⟨ρ, hρpos, hρlt, δ, hδpos, hsub, hinj, hloc⟩ :=
        Work.Horn.exists_ball_injOn_and_mapsTo hB hf hxB hne (hmpos x hx)
      have hloc' : ∀ u : ℂ, ‖u - w‖ < δ → ∃ v ∈ Metric.ball x ρ, f v = u := by
        intro u hu
        rw [← hfx] at hu
        exact hloc u hu
      exact ⟨ρ, δ, fun _ => ⟨hρpos, hρlt, hδpos, hsub, hinj, hloc'⟩⟩
    · exact ⟨1, 1, fun h => absurd h hx⟩
  choose ρ δ hspec using hex
  have hρpos : ∀ x ∈ S, 0 < ρ x := fun x hx => (hspec x hx).1
  have hρlt : ∀ x ∈ S, ρ x < m x := fun x hx => (hspec x hx).2.1
  have hδpos : ∀ x ∈ S, 0 < δ x := fun x hx => (hspec x hx).2.2.1
  have hρsub : ∀ x ∈ S, Metric.ball x (ρ x) ⊆ B := fun x hx => (hspec x hx).2.2.2.1
  have hrinj : ∀ x ∈ S, Set.InjOn f (Metric.ball x (ρ x)) :=
    fun x hx => (hspec x hx).2.2.2.2.1
  have hlocal : ∀ x ∈ S, ∀ u : ℂ, ‖u - w‖ < δ x → ∃ v ∈ Metric.ball x (ρ x), f v = u :=
    fun x hx => (hspec x hx).2.2.2.2.2
  -- the balls are pairwise disjoint, because the radii are below half the separations
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      Disjoint (Metric.ball x (ρ x)) (Metric.ball y (ρ y)) := by
    intro x hx y hy hxy
    rw [Set.disjoint_left]
    intro z hzx hzy
    have h1 : dist x y ≤ dist x z + dist z y := dist_triangle x z y
    have h3 : dist z x < ρ x := Metric.mem_ball.mp hzx
    have h4 : dist z y < ρ y := Metric.mem_ball.mp hzy
    have h5 : ρ x < m x := hρlt x hx
    have h6 : ρ y < m y := hρlt y hy
    have h7 : m x ≤ dist x y / 2 := hmhalf x hx y hy hxy
    have h8 : m y ≤ dist y x / 2 := hmhalf y hy x hx (Ne.symm hxy)
    have h9 : dist y x = dist x y := dist_comm y x
    have h10 : dist x z = dist z x := dist_comm x z
    linarith
  have hmain : ∀ᶠ t in nhds w, (B ∩ f ⁻¹' {t}).ncard = S.card :=
    Work.Horn.eventually_ncard_eq_of_local_trivialization hB hf.continuousOn hprop hw S hS
      ρ hρpos hρsub hdisj hrinj δ hδpos hlocal
  have hcardw : (B ∩ f ⁻¹' {w}).ncard = S.card := by
    rw [Set.ncard_eq_toFinset_card (B ∩ f ⁻¹' {w}) hSfin, ← hSdef]
  filter_upwards [hmain] with t ht
  rw [ht, hcardw]

end Work.HornSeq
