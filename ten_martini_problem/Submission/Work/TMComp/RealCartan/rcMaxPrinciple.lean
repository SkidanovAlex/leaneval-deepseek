import Mathlib
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcLevelSet_const
import Submission.Work.TMComp.RealCartan.rcFrontier_connectedComponentIn_subset

/-!
# Maximum principle for functions satisfying the circle mean value inequality

Let `Ω ⊆ ℂ` be open and bounded, `V : ℂ → ℝ` continuous, satisfying the sub-mean-value
inequality on circles
`V z ≤ circleAverage V z r` whenever `closedBall z r ⊆ Ω` (`r > 0`), and bounded by `C` on the
frontier of `Ω`.  Then `V ≤ C` on all of `Ω`.

The proof is the standard one: assume `V z₀ > C` for some `z₀ ∈ Ω`, take `A` to be the connected
component of `z₀` in `Ω`, and let `M = max_{cl A} V`, attained at `z*`.  Since `V ≤ C` on the
frontier, `V z* > C` forces `z* ∈ Ω`, and then `z* ∈ A` (a small ball around `z*` inside `Ω`,
being preconnected and meeting `A`, lies inside the component `A`).  On the preconnected open set
`A` the level set `{V = M}` is open and closed, whence `V ≡ M` on `A`; finally a point of the
nonempty frontier of `A`, which lies in the frontier of `Ω` and is a limit point of `A`, would
have to satisfy both `V = M` and `V ≤ C < M`, a contradiction.
-/

open Metric Set

namespace Work.TMComp.RealCartan

/-- The frontier of a connected component of a bounded set is nonempty. -/
private theorem frontier_connectedComponentIn_nonempty {F : Set ℂ} (hFbdd : Bornology.IsBounded F)
    {x : ℂ} (hx : x ∈ F) : (frontier (connectedComponentIn F x)).Nonempty := by
  have hAne : connectedComponentIn F x ≠ univ := by
    intro hAu
    obtain ⟨r, hr⟩ := (hFbdd.subset (connectedComponentIn_subset F x)).subset_closedBall (0 : ℂ)
    have hp : (((max r 0 + 1 : ℝ)) : ℂ) ∈ Metric.closedBall (0 : ℂ) (max r 0) :=
      closedBall_subset_closedBall (le_max_left r 0) (hr (by rw [hAu]; exact mem_univ _))
    rw [Metric.mem_closedBall, dist_zero_right] at hp
    have h2 : ‖(((max r 0 + 1 : ℝ)) : ℂ)‖^2 = (max r 0 + 1)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg ((((max r 0 + 1 : ℝ)) : ℂ)), le_max_right r 0, le_max_left r 0]
  rw [nonempty_iff_ne_empty]
  intro hempty
  rw [frontier_eq_empty_iff] at hempty
  rcases hempty with h | h
  · exact (connectedComponentIn_nonempty_iff.mpr hx).ne_empty h
  · exact hAne h

theorem rcMaxPrinciple {Ω : Set ℂ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    {V : ℂ → ℝ} (hVc : Continuous V) {C : ℝ}
    (hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r)
    (hbd : ∀ ζ ∈ frontier Ω, V ζ ≤ C) :
    ∀ z ∈ Ω, V z ≤ C := by
  intro z0 hz0
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : C < V z0`.
  set A : Set ℂ := connectedComponentIn Ω z0 with hA
  have hApre : IsPreconnected A := isPreconnected_connectedComponentIn
  have hAsub : A ⊆ Ω := connectedComponentIn_subset Ω z0
  have hAz0 : z0 ∈ A := mem_connectedComponentIn hz0
  have hAbdd : Bornology.IsBounded A := hbdd.subset hAsub
  -- A small ball around a point of `A`, contained in `Ω`, is contained in `A`.
  have hAbal : ∀ a ∈ A, ∃ ρ > 0, Metric.closedBall a ρ ⊆ A := by
    intro a ha
    obtain ⟨ε, hεpos, hεU⟩ := Metric.isOpen_iff.mp hΩ a (hAsub ha)
    refine ⟨ε / 2, by linarith, ?_⟩
    have hsubΩ : Metric.closedBall a (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    have hsub : Metric.closedBall a (ε / 2) ⊆ connectedComponentIn Ω a :=
      isPreconnected_closedBall.subset_connectedComponentIn
        (Metric.mem_closedBall_self (by linarith)) hsubΩ
    have ha' : a ∈ connectedComponentIn Ω z0 := hA ▸ ha
    rw [← connectedComponentIn_eq ha', ← hA] at hsub
    exact hsub
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro a ha
    obtain ⟨ρ, hρ, hρA⟩ := hAbal a ha
    exact ⟨ρ, hρ, fun x hx => hρA (Metric.ball_subset_closedBall hx)⟩
  -- Maximum of `V` on the closure of `A`.
  obtain ⟨zstar, hzs_cl, hzs_max⟩ :=
    hAbdd.isCompact_closure.exists_isMaxOn ⟨z0, subset_closure hAz0⟩ hVc.continuousOn
  have hz0_le : V z0 ≤ V zstar := hzs_max (subset_closure hAz0)
  have hmaxgt : C < V zstar := lt_of_lt_of_le hcon hz0_le
  -- `zstar` lies in `Ω`.
  have hzsΩ : zstar ∈ Ω := by
    by_contra h
    have h1 : zstar ∈ closure Ω := closure_mono hAsub hzs_cl
    have h2 : zstar ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨h1, h⟩
    have h3 : V zstar ≤ C := hbd zstar h2
    linarith
  -- `zstar` lies in `A`.
  have hzs_A : zstar ∈ A := by
    obtain ⟨ε, hεpos, hεU⟩ := Metric.isOpen_iff.mp hΩ zstar hzsΩ
    rw [Metric.mem_closure_iff] at hzs_cl
    obtain ⟨a, haA, hadist⟩ := hzs_cl (ε / 2) (by linarith)
    have hda : dist a zstar < ε / 2 := by rw [dist_comm]; exact hadist
    have hsubΩ : Metric.closedBall a (ε / 2) ⊆ Ω := by
      intro x hx
      apply hεU
      rw [Metric.mem_ball]
      rw [Metric.mem_closedBall] at hx
      have := dist_triangle x a zstar
      linarith
    have hsub : Metric.closedBall a (ε / 2) ⊆ connectedComponentIn Ω a :=
      isPreconnected_closedBall.subset_connectedComponentIn
        (Metric.mem_closedBall_self (by linarith)) hsubΩ
    have ha' : a ∈ connectedComponentIn Ω z0 := hA ▸ haA
    rw [← connectedComponentIn_eq ha', ← hA] at hsub
    apply hsub
    rw [Metric.mem_closedBall]
    linarith
  -- The level set `{V = V zstar}` is all of `A`.
  have hAle : ∀ w ∈ A, V w ≤ V zstar := fun w hw => hzs_max (subset_closure hw)
  have hVmeanA : ∀ z ∈ A, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ A →
      V z ≤ Real.circleAverage V z r :=
    fun z hz r hr hrA => hVmean z (hAsub hz) r hr (hrA.trans hAsub)
  have hconst : ∀ w ∈ A, V w = V zstar :=
    rcLevelSet_const hAopen hApre hVc hAle hVmeanA hzs_A rfl
  -- A frontier point of `A` is a frontier point of `Ω`, and a limit of points of `A`.
  obtain ⟨x, hx⟩ := frontier_connectedComponentIn_nonempty hAbdd hzs_A
  rw [hApre.connectedComponentIn hzs_A] at hx
  have hxΩ : x ∈ frontier Ω :=
    rcFrontier_connectedComponentIn_subset hΩ z0 (hA ▸ hx)
  have hxC : V x ≤ C := hbd x hxΩ
  have hxcl : x ∈ closure A := frontier_subset_closure hx
  have hclosed : IsClosed {y : ℂ | V y = V zstar} := isClosed_eq hVc continuous_const
  have hsubS : A ⊆ {y : ℂ | V y = V zstar} := fun y hy => hconst y hy
  have hclosure : closure A ⊆ {y : ℂ | V y = V zstar} := by
    rw [← hclosed.closure_eq]; exact closure_mono hsubS
  have hxV : V x = V zstar := hclosure hxcl
  linarith

end Work.TMComp.RealCartan
