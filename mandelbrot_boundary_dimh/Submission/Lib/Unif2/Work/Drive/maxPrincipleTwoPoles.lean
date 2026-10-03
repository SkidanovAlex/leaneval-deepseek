import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localRemovability
import Submission.Lib.Unif2.MaxPrincipleRegion
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic

/-!
# The maximum principle with two removable singularities

`Work.Drive.maxPrincipleTwoPoles`: a harmonic function on `U \ {a, b}` which is bounded near each
of the two punctures and has frontier limsup at most `c` is at most `c` on `U \ {a, b}`.

The two punctures are removable (`Work.SimplyConnected.ABS.exists_extension_of_punctured_chartBall`,
whence `Work.Drive.exists_update_harmonicOnXAt_of_bounded_punctured`), so `v` extends to a
function `W` harmonic on `U`; `W` is subharmonic, and
`Submission.SubharmonicOnX.le_of_frontier_limsup` gives `W ≤ c` on `U`.
-/

open Filter Set
open scoped Topology Manifold

noncomputable section

namespace Work.Drive

/-- **Update across a chart-ball extension.** -/
theorem harmonicOnXAt_update_of_chartBall_extension {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [DecidableEq X] {q : X} {u : X → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.ball ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) {h : ℂ → ℝ}
    (hharm : ∀ z : ℂ, ‖z - (chartAt ℂ q) q‖ < ρ → InnerProductSpace.HarmonicAt h z)
    (heq : ∀ z : ℂ, ‖z - (chartAt ℂ q) q‖ < ρ → z ≠ (chartAt ℂ q) q →
      h z = u ((chartAt ℂ q).symm z)) :
    Submission.HarmonicOnXAt (Function.update u q (h ((chartAt ℂ q) q))) q := by
  classical
  have hqsrc : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  rw [Submission.HarmonicOnXAt]
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp
    (hharm ((chartAt ℂ q) q) (by rw [sub_self, norm_zero]; exact hρ))
  filter_upwards [Metric.ball_mem_nhds ((chartAt ℂ q) q) hρ] with z hz
  by_cases hzq : z = (chartAt ℂ q) q
  · rw [hzq]
    show h ((chartAt ℂ q) q) =
      Function.update u q (h ((chartAt ℂ q) q)) ((chartAt ℂ q).symm ((chartAt ℂ q) q))
    rw [(chartAt ℂ q).left_inv hqsrc, Function.update_self]
  · have hzt : z ∈ (chartAt ℂ q).target := htgt hz
    have hzs : (chartAt ℂ q).symm z ≠ q := fun hh =>
      hzq (by rw [← (chartAt ℂ q).right_inv hzt, hh])
    rw [heq z (by simpa [Metric.mem_ball, dist_eq_norm] using hz) hzq, Function.comp_apply,
      Function.update_of_ne hzs]

/-- **A single removable singularity, locally.** -/
theorem exists_update_harmonicOnXAt_of_bounded_punctured {X : Type*} [TopologicalSpace X]
    [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {q : X} {u : X → ℝ} {V : Set X} (hV : V ∈ 𝓝 q)
    (hu : Submission.HarmonicOnX u (V \ {q}))
    (hb : ∃ M : ℝ, ∀ x ∈ V, x ≠ q → |u x| ≤ M) :
    ∃ A : ℝ, Submission.HarmonicOnXAt (Function.update u q A) q := by
  classical
  obtain ⟨M, hM⟩ := hb
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ q
  have hqsrc : q ∈ c.source := mem_chart_source ℂ q
  have hqtgt : c q ∈ c.target := c.map_source hqsrc
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hqtgt)
  have hlim : Filter.Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    have h := (c.continuousAt_symm hqtgt).tendsto
    rwa [c.left_inv hqsrc] at h
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp (hlim.eventually hV)
  set ρ : ℝ := min ρ₁ ρ₂ with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  have hρ_le₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρ_le₂ : ρ ≤ ρ₂ := min_le_right _ _
  have htgt : Metric.ball (c q) ρ ⊆ c.target := (Metric.ball_subset_ball hρ_le₂).trans hρ₂sub
  have hballV : ∀ z : ℂ, z ∈ Metric.ball (c q) ρ → c.symm z ∈ V := fun z hz =>
    hρ₁sub (Metric.ball_subset_ball hρ_le₁ hz)
  have hchartBallV : Submission.chartBall c (c q) ρ ⊆ V := by
    intro x hx
    rw [Submission.mem_chartBall] at hx
    have h1 : c.symm (c x) ∈ V := hballV (c x) hx.2
    rwa [c.left_inv hx.1] at h1
  have hu' : Submission.HarmonicOnX u (Submission.chartBall c (c q) ρ \ {q}) :=
    fun x hx => hu x ⟨hchartBallV hx.1, hx.2⟩
  have hb' : ∀ x ∈ Submission.chartBall c (c q) ρ, x ≠ q → |u x| ≤ M :=
    fun x hx hxq => hM x (hchartBallV hx) hxq
  obtain ⟨h, hharm, heq⟩ := Work.SimplyConnected.ABS.exists_extension_of_punctured_chartBall
    (u := u) (ζ := q) (ρ := ρ) (M := M) hρpos htgt hu' hb'
  exact ⟨h (c q), harmonicOnXAt_update_of_chartBall_extension hρpos htgt hharm heq⟩

/-- **Maximum principle on a relatively compact region with two removable singularities.** If `v` is
harmonic on `U \ {a,b}`, bounded near `a` and near `b`, and has limsup at most `c` at every frontier
point of `U` (read in the trace filter on `U`), then `v ≤ c` on `U \ {a,b}`.

Route: the boundedness near `a` and `b` makes the two punctures removable
(`Submission.Work.Potential.removable_singularity_bounded_harmonic`,
`Submission.Work.Potential.removable_singularity_of_bounded_near`,
`Submission.Work.Drive.harmonicOnX_extension_off_pair`), so `v` extends to a function harmonic at
`a` and `b` as well; then apply the maximum principle with frontier limsup,
`Submission.SubharmonicOnX.le_of_frontier_limsup` (in `Submission.MaxPrincipleRegion`), to the
extension (harmonic functions are subharmonic). Those modules may be imported by the proof. -/

theorem maxPrincipleTwoPoles {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hU : IsOpen U) {a b : X} (ha : a ∈ U) (hb : b ∈ U)
    {v : X → ℝ} (hv : Submission.HarmonicOnX v (U \ {a, b}))
    (hbda : ∃ C : ℝ, Filter.Eventually (fun z : X => |v z| ≤ C) (nhdsWithin a (U \ {a})))
    (hbdb : ∃ C : ℝ, Filter.Eventually (fun z : X => |v z| ≤ C) (nhdsWithin b (U \ {b})))
    (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty) {c : ℝ}
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
      Filter.Eventually (fun z : X => v z ≤ c + ε) (nhdsWithin ξ U)) :
    ∀ z ∈ U, z ≠ a → z ≠ b → v z ≤ c := by
  classical
  -- (1) remove the singularity at `a`
  obtain ⟨Ca, hCa⟩ := hbda
  rw [eventually_nhdsWithin_iff] at hCa
  obtain ⟨Sa, hSa, hSab⟩ := Filter.eventually_iff_exists_mem.mp hCa
  have hVa_avoid : ({b}ᶜ ∪ {a} : Set X) ∈ 𝓝 a := by
    by_cases hab : a = b
    · subst hab
      rw [Set.compl_union_self]
      exact Filter.univ_mem
    · exact Filter.mem_of_superset
        (isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hab))
        Set.subset_union_left
  set Va : Set X := Sa ∩ U ∩ ({b}ᶜ ∪ {a}) with hVadef
  have hVa : Va ∈ 𝓝 a := inter_mem (inter_mem hSa (hU.mem_nhds ha)) hVa_avoid
  have huVa : Submission.HarmonicOnX v (Va \ {a}) := by
    intro x hx
    have hxVa : x ∈ Va := hx.1
    have hxne : x ≠ a := by simpa using hx.2
    have hxU : x ∈ U := hxVa.1.2
    have hxb : x ≠ b := by
      rcases hxVa.2 with h | h
      · simpa using h
      · exact absurd (by simpa using h) hxne
    exact hv x ⟨hxU, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxne, hxb⟩⟩
  have hbVa : ∃ M : ℝ, ∀ x ∈ Va, x ≠ a → |v x| ≤ M := by
    refine ⟨Ca, fun x hx hxne => ?_⟩
    have hxU : x ∈ U := hx.1.2
    exact hSab x hx.1.1 ⟨hxU, hxne⟩
  obtain ⟨A, hA⟩ := exists_update_harmonicOnXAt_of_bounded_punctured (V := Va) hVa huVa hbVa
  let W₁ : X → ℝ := Function.update v a A
  have hA' : Submission.HarmonicOnXAt W₁ a := hA
  have hW₁_off : ∀ x : X, x ≠ a → W₁ x = v x := fun x hx => Function.update_of_ne hx A v
  -- (2) remove the singularity at `b`
  obtain ⟨Cb, hCb⟩ := hbdb
  rw [eventually_nhdsWithin_iff] at hCb
  obtain ⟨Sb, hSb, hSbb⟩ := Filter.eventually_iff_exists_mem.mp hCb
  have hVb_avoid : ({a}ᶜ ∪ {b} : Set X) ∈ 𝓝 b := by
    by_cases hba : b = a
    · subst hba
      rw [Set.compl_union_self]
      exact Filter.univ_mem
    · exact Filter.mem_of_superset
        (isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hba))
        Set.subset_union_left
  set Vb : Set X := Sb ∩ U ∩ ({a}ᶜ ∪ {b}) with hVbdef
  have hVb : Vb ∈ 𝓝 b := inter_mem (inter_mem hSb (hU.mem_nhds hb)) hVb_avoid
  have huVb : Submission.HarmonicOnX W₁ (Vb \ {b}) := by
    intro x hx
    have hxVb : x ∈ Vb := hx.1
    have hxne : x ≠ b := by simpa using hx.2
    have hxU : x ∈ U := hxVb.1.2
    have hxa : x ≠ a := by
      rcases hxVb.2 with h | h
      · simpa using h
      · exact absurd (by simpa using h) hxne
    rcases eq_or_ne x a with h | h
    · rw [h]; exact hA'
    · exact Work.Potential.harmonicOnXAt_of_eq_off h hW₁_off
        (hv x ⟨hxU, by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h, hxne⟩⟩)
  have hbVb : ∃ M : ℝ, ∀ x ∈ Vb, x ≠ b → |W₁ x| ≤ M := by
    refine ⟨Cb, fun x hx hxne => ?_⟩
    have hxU : x ∈ U := hx.1.2
    have hxa : x ≠ a := by
      rcases hx.2 with h | h
      · simpa using h
      · exact absurd (by simpa using h) hxne
    rw [hW₁_off x hxa]
    exact hSbb x hx.1.1 ⟨hxU, hxne⟩
  obtain ⟨B, hB⟩ := exists_update_harmonicOnXAt_of_bounded_punctured (V := Vb) hVb huVb hbVb
  let W : X → ℝ := Function.update W₁ b B
  have hB' : Submission.HarmonicOnXAt W b := hB
  have hWoff : ∀ x : X, x ≠ a → x ≠ b → W x = v x := by
    intro x hxa hxb
    show Function.update W₁ b B x = v x
    rw [Function.update_of_ne hxb]
    show W₁ x = v x
    exact hW₁_off x hxa
  -- `W` is harmonic (hence subharmonic) on `U`
  have hWU : Submission.HarmonicOnX W U := by
    intro y hy
    by_cases hyb : y = b
    · rw [hyb]; exact hB'
    · have hharm_y : Submission.HarmonicOnXAt W₁ y := by
        by_cases hya : y = a
        · rw [hya]; exact hA'
        · exact Work.Potential.harmonicOnXAt_of_eq_off (z₀ := a) (y := y) hya hW₁_off
            (hv y ⟨hy, by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨hya, hyb⟩⟩)
      exact Work.Potential.harmonicOnXAt_of_eq_off (u := W₁) (U := W) (z₀ := b) (y := y)
        hyb (fun x hx => Function.update_of_ne hx B W₁) hharm_y
  have hsubW : Submission.SubharmonicOnX W U :=
    hWU.subharmonic (fun y hy => ((hWU y hy).continuousAt).continuousWithinAt)
  -- the limsup condition transfers to `W`
  have hlimW : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, W z ≤ c + ε := by
    intro ξ hξ ε hε
    have hain : a ∈ interior U := by rw [hU.interior_eq]; exact ha
    have hbin : b ∈ interior U := by rw [hU.interior_eq]; exact hb
    have hξa : ξ ≠ a := fun h => hξ.2 (h ▸ hain)
    have hξb : ξ ≠ b := fun h => hξ.2 (h ▸ hbin)
    have hcl : IsClosed ({a, b} : Set X) := (Set.Finite.insert a (Set.finite_singleton b)).isClosed
    have hmem : ({a, b} : Set X)ᶜ ∈ 𝓝 ξ :=
      hcl.isOpen_compl.mem_nhds (by simp [hξa, hξb])
    have hev : ∀ᶠ z in 𝓝 ξ, W z = v z := by
      filter_upwards [hmem] with z hz
      exact hWoff z (fun h => hz (by simp [h])) (fun h => hz (by simp [h]))
    have hev' : ∀ᶠ z in 𝓝[U] ξ, W z = v z := Filter.Eventually.filter_mono nhdsWithin_le_nhds hev
    exact ((hlim ξ hξ ε hε).and hev').mono (fun z hz => by rw [hz.2]; exact hz.1)
  -- the maximum principle for `W`
  have hle := Submission.SubharmonicOnX.le_of_frontier_limsup hU hsubW hcomp hne (a := c) hlimW
  intro z hzU hza hzb
  calc v z = W z := (hWoff z hza hzb).symm
    _ ≤ c := hle z hzU

end Work.Drive
