import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.Smooth.Jordan.All

namespace Work.BoxShrink.PinchOff

noncomputable section

open Set Metric

/-! ## Lattice arithmetic for the period lattice

The period lattice `periodLattice = range (periodPt · ·)` of the parameter plane (`2π(ℤ + iℤ)`) is
an additive subgroup of `ℂ`; we only need the closure facts. -/

theorem periodPt_add (a b c d : ℤ) :
    periodPt a b + periodPt c d = periodPt (a + c) (b + d) := by
  apply Complex.ext <;> simp [periodPt] <;> ring

theorem zero_mem_periodLattice : (0 : ℂ) ∈ periodLattice := by
  rw [mem_periodLattice]; exact ⟨0, 0, periodPt_zero⟩

theorem neg_mem_periodLattice {ν : ℂ} (hν : ν ∈ periodLattice) : -ν ∈ periodLattice := by
  rw [mem_periodLattice] at hν ⊢
  obtain ⟨a, b, rfl⟩ := hν
  exact ⟨-a, -b, by apply Complex.ext <;> simp [periodPt]⟩

theorem add_mem_periodLattice {ν w : ℂ} (hν : ν ∈ periodLattice) (hw : w ∈ periodLattice) :
    ν + w ∈ periodLattice := by
  rw [mem_periodLattice] at hν hw ⊢
  obtain ⟨a, b, rfl⟩ := hν
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, (periodPt_add a b c d).symm⟩

theorem sub_mem_periodLattice {ν w : ℂ} (hν : ν ∈ periodLattice) (hw : w ∈ periodLattice) :
    ν - w ∈ periodLattice := by
  simpa [sub_eq_add_neg] using add_mem_periodLattice hν (neg_mem_periodLattice hw)

/-! ## The periodic push

Fix a compact set `K` (the curve), a radius `ε > 0` and a push `ψ`.  A lattice vector `ν` is a
*witness* for `z` when `z - ν` lies within `ε` of `K`; when the witnesses are unique (which the
separation hypothesis on the lattice translates of the curve will guarantee) we may define the
periodic push `periodicPush K ε ψ z = ψ (z - ν) + ν`. -/

/-- `ν` is a lattice witness for `z` (relative to `K` and `ε`). -/
def PushWitness (K : Set ℂ) (ε : ℝ) (z ν : ℂ) : Prop :=
  ν ∈ periodLattice ∧ Metric.infDist (z - ν) K < ε

theorem pushWitness_def {K : Set ℂ} {ε : ℝ} {z ν : ℂ} :
    PushWitness K ε z ν ↔ ν ∈ periodLattice ∧ Metric.infDist (z - ν) K < ε := Iff.rfl

/-- The lattice-periodic push: push by `ψ` around the (unique) witness of `z`, and do nothing when
there is no witness. -/
noncomputable def periodicPush (K : Set ℂ) (ε : ℝ) (ψ : ℂ → ℂ) : ℂ → ℂ := by
  classical
  exact fun z => if h : ∃ ν, PushWitness K ε z ν then
    ψ (z - Classical.choose h) + Classical.choose h else z

theorem periodicPush_of_witness {K : Set ℂ} {ε : ℝ} {ψ : ℂ → ℂ} {z ν : ℂ}
    (huniq : ∀ z ν μ, PushWitness K ε z ν → PushWitness K ε z μ → ν = μ)
    (hν : PushWitness K ε z ν) :
    periodicPush K ε ψ z = ψ (z - ν) + ν := by
  unfold periodicPush
  rw [dif_pos (show ∃ ν, PushWitness K ε z ν from ⟨ν, hν⟩)]
  rw [huniq z _ ν (Classical.choose_spec _) hν]

theorem periodicPush_of_not {K : Set ℂ} {ε : ℝ} {ψ : ℂ → ℂ} {z : ℂ}
    (h : ¬ ∃ ν, PushWitness K ε z ν) : periodicPush K ε ψ z = z := by
  unfold periodicPush
  rw [dif_neg h]

/-- Translation invariance of `Metric.infDist`: the distance from `x` to the translate
`{z | z - ν ∈ S}` is the distance from `x - ν` to `S`. -/
theorem infDist_shiftSet {x ν : ℂ} {S : Set ℂ} :
    Metric.infDist x {z' : ℂ | z' - ν ∈ S} = Metric.infDist (x - ν) S := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp [Metric.infDist_empty]
  · have hT : ({z' : ℂ | z' - ν ∈ S}).Nonempty := by
      obtain ⟨s, hs⟩ := hS
      exact ⟨s + ν, show s + ν - ν ∈ S from by rw [add_sub_cancel_right]; exact hs⟩
    refine le_antisymm ?_ ?_
    · exact (Metric.le_infDist hS).mpr fun s hs => by
        have h1 : Metric.infDist x {z' : ℂ | z' - ν ∈ S} ≤ dist x (s + ν) :=
          Metric.infDist_le_dist_of_mem (y := s + ν)
            (show s + ν - ν ∈ S from by rw [add_sub_cancel_right]; exact hs)
        have h2 : dist x (s + ν) = dist (x - ν) s := by
          rw [dist_eq_norm, dist_eq_norm, show x - (s + ν) = (x - ν) - s from by ring]
        exact h1.trans h2.le
    · exact (Metric.le_infDist hT).mpr fun t ht => by
        have h1 : Metric.infDist (x - ν) S ≤ dist (x - ν) (t - ν) :=
          Metric.infDist_le_dist_of_mem ht
        have h2 : dist (x - ν) (t - ν) = dist x t := by
          rw [dist_eq_norm, dist_eq_norm, show (x - ν) - (t - ν) = x - t from by ring]
        exact h1.trans h2.le

/-- **Assembling a single push `ψ` for one Jordan curve into a lattice-periodic push for all its
translates.**

`c` is a simple closed plane curve with separation datum `h` (`h.U` the unbounded side, `h.V` the
bounded side, and `trace ⊆ closure h.V`, which holds for any genuine Jordan separation and is
supplied by `PlaneSchoenflies.range_e`), and `ψ` is a push of the plane off `c` with the properties
(for a fixed `ε > 0`): it moves points by at most `ε`, it fixes every point at distance `≥ ε` from
the curve, and it sends every point of `h.U` and every point of the curve into `h.U` (this is the
conclusion of `Work.BoxShrink.PinchOff.jordan_push`).

Suppose moreover that `ρ > 0` with `ε < ρ` and that the lattice translates of the *closures* of the
bounded side are separated: points of distinct translates are at distance `≥ 2ρ` (this is the
uniform gap coming from the covering of the torus).

Then there is a single continuous `Ψ : ℂ → ℂ` which

* moves points by at most `ε`;
* is lattice-periodic in the sense `Ψ (z + w) = Ψ z + w` for `w` in the lattice;
* is the identity away from the translates of the curve (`Ψ z = z` unless `z` is within `ε` of some
  translate of the curve);
* and, for `z` which is within `ε` of some translate `range c.γ + ν` and which lies in no translate
  of the bounded side `h.V`, the value `Ψ z` lies in the unbounded side translated by the *same*
  `ν`, is within `2ρ` of `closure h.V + ν`, and lies in no translate of `closure h.V`.

Construction: `Ψ z := ψ (z - ν) + ν` where `ν` is the (unique, by `hsep` and `trace ⊆ closure h.V`
and `2ε < 2ρ`) lattice vector with `Metric.infDist (z - ν) (range c.γ) < ε`, and `Ψ z := z` if there
is none.  The estimate `Metric.infDist (Ψ z) (closure h.V + ν) ≤ 2ε < 2ρ` with the separation then
excludes all translates `closure h.V + μ`, `μ ≠ ν`, and `μ = ν` is excluded because
`Ψ z - ν ∈ h.U` and `U ∩ closure h.V = ∅` (an open set disjoint from `V` misses its closure). -/
theorem exists_periodic_push
    {c : Work.Smooth.Jordan.PlaneCurve} (h : Work.Smooth.Jordan.PlaneSeparation c)
    (htrace : Set.range c.γ ⊆ closure h.V)
    {ψ : ℂ → ℂ} (hψc : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hψ1 : ∀ z : ℂ, ‖ψ z - z‖ ≤ ε)
    (hψ2 : ∀ z : ℂ, ε ≤ Metric.infDist z (Set.range c.γ) → ψ z = z)
    (hψ3 : ∀ z : ℂ, (z ∈ h.U ∨ ∃ θ : ℝ, z = c.γ θ) → ψ z ∈ h.U)
    {ρ : ℝ} (hρ : 0 < ρ) (hερ : ε < ρ)
    (hsep : ∀ ν μ : ℂ, ν ∈ Work.BoxShrink.PinchOff.periodLattice →
      μ ∈ Work.BoxShrink.PinchOff.periodLattice → ν ≠ μ →
      ∀ x y : ℂ, x - ν ∈ closure h.V → y - μ ∈ closure h.V → 2 * ρ ≤ dist x y) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧
      (∀ z : ℂ, ‖Ψ z - z‖ ≤ ε) ∧
      (∀ w : ℂ, w ∈ Work.BoxShrink.PinchOff.periodLattice → ∀ z : ℂ, Ψ (z + w) = Ψ z + w) ∧
      (∀ z : ℂ, Ψ z = z ∨ ∃ ν ∈ Work.BoxShrink.PinchOff.periodLattice,
        Metric.infDist (z - ν) (Set.range c.γ) < ε) ∧
      (∀ z : ℂ, (∃ ν ∈ Work.BoxShrink.PinchOff.periodLattice,
          Metric.infDist (z - ν) (Set.range c.γ) < ε) →
        (∀ μ : ℂ, z - μ ∉ h.V) →
        ∃ ν ∈ Work.BoxShrink.PinchOff.periodLattice,
          (∃ u : ℂ, u ∈ h.U ∧ Ψ z = u + ν) ∧
          Metric.infDist (Ψ z) ({z' : ℂ | z' - ν ∈ closure h.V}) < 2 * ρ ∧
          ¬ ∃ μ ∈ Work.BoxShrink.PinchOff.periodLattice, Ψ z - μ ∈ closure h.V) := by
  classical
  have hδpos : 0 < ρ - ε := by linarith
  have hneK : (Set.range c.γ).Nonempty := ⟨c.γ 0, ⟨0, rfl⟩⟩
  have hUdisj : Disjoint h.U (closure h.V) := Disjoint.closure_right h.disjoint_UV h.isOpen_U
  let Ψ : ℂ → ℂ := periodicPush (Set.range c.γ) ε ψ
  -- ### Separation of witnesses
  have hwit_sep : ∀ z₁ z₂ ν₁ ν₂ : ℂ, PushWitness (Set.range c.γ) ε z₁ ν₁ →
      PushWitness (Set.range c.γ) ε z₂ ν₂ → ν₁ ≠ ν₂ → 2 * (ρ - ε) ≤ dist z₁ z₂ := by
    intro z₁ z₂ ν₁ ν₂ hw₁ hw₂ hne'
    obtain ⟨hν₁, hd₁⟩ := hw₁
    obtain ⟨hν₂, hd₂⟩ := hw₂
    obtain ⟨x, hx, hxd⟩ := (Metric.infDist_lt_iff hneK).mp hd₁
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff hneK).mp hd₂
    have hxV : x + ν₁ - ν₁ ∈ closure h.V := by
      rw [add_sub_cancel_right]; exact htrace hx
    have hyV : y + ν₂ - ν₂ ∈ closure h.V := by
      rw [add_sub_cancel_right]; exact htrace hy
    have hbig := hsep ν₁ ν₂ hν₁ hν₂ hne' (x + ν₁) (y + ν₂) hxV hyV
    have h1 : dist (x + ν₁) z₁ < ε := by
      have he : dist (x + ν₁) z₁ = dist (z₁ - ν₁) x := by
        rw [dist_eq_norm, dist_eq_norm, show x + ν₁ - z₁ = -(z₁ - ν₁ - x) from by ring, norm_neg]
      rw [he]; exact hxd
    have h2 : dist z₂ (y + ν₂) < ε := by
      have he : dist z₂ (y + ν₂) = dist (z₂ - ν₂) y := by
        rw [dist_eq_norm, dist_eq_norm, show z₂ - (y + ν₂) = z₂ - ν₂ - y from by ring]
      rw [he]; exact hyd
    have h3 : dist (x + ν₁) (y + ν₂) < 2 * ε + dist z₁ z₂ := by
      have ht1 := dist_triangle (x + ν₁) z₁ (y + ν₂)
      have ht2 := dist_triangle z₁ z₂ (y + ν₂)
      linarith
    linarith
  have hwit_uniq : ∀ z ν μ, PushWitness (Set.range c.γ) ε z ν →
      PushWitness (Set.range c.γ) ε z μ → ν = μ := by
    intro z ν μ hν hμ
    by_contra hne'
    have h := hwit_sep z z ν μ hν hμ hne'
    rw [dist_self] at h
    linarith
  -- ### The defining formula
  have hΨ_of : ∀ z ν, PushWitness (Set.range c.γ) ε z ν → Ψ z = ψ (z - ν) + ν :=
    fun z ν hν => periodicPush_of_witness hwit_uniq hν
  have hΨ_not : ∀ z, ¬ (∃ ν, PushWitness (Set.range c.γ) ε z ν) → Ψ z = z :=
    fun z hz => periodicPush_of_not hz
  -- ### `Ψ` moves points by at most `ε`
  have hΨ1 : ∀ z : ℂ, ‖Ψ z - z‖ ≤ ε := by
    intro z
    by_cases hz : ∃ ν, PushWitness (Set.range c.γ) ε z ν
    · obtain ⟨ν, hν⟩ := hz
      rw [hΨ_of z ν hν]
      have : ψ (z - ν) + ν - z = ψ (z - ν) - (z - ν) := by ring
      rw [this]
      exact hψ1 (z - ν)
    · rw [hΨ_not z hz, sub_self, norm_zero]
      exact hε.le
  -- ### Lattice periodicity
  have hΨper : ∀ w : ℂ, w ∈ periodLattice → ∀ z : ℂ, Ψ (z + w) = Ψ z + w := by
    intro w hw z
    by_cases hz : ∃ ν, PushWitness (Set.range c.γ) ε z ν
    · obtain ⟨ν, hν⟩ := hz
      have hνw : PushWitness (Set.range c.γ) ε (z + w) (ν + w) := by
        refine ⟨add_mem_periodLattice hν.1 hw, ?_⟩
        have he : z + w - (ν + w) = z - ν := by ring
        rw [he]; exact hν.2
      rw [hΨ_of (z + w) (ν + w) hνw, hΨ_of z ν hν]
      have he : z + w - (ν + w) = z - ν := by ring
      rw [he]; ring
    · have hnot : ¬ ∃ ν, PushWitness (Set.range c.γ) ε (z + w) ν := by
        rintro ⟨μ, hμ⟩
        exact hz ⟨μ - w, sub_mem_periodLattice hμ.1 hw, by
          have he : z - (μ - w) = z + w - μ := by ring
          rw [he]; exact hμ.2⟩
      rw [hΨ_not (z + w) hnot, hΨ_not z hz]
  -- ### `Ψ` is the identity away from the translates of the curve
  have hΨ_or : ∀ z : ℂ, Ψ z = z ∨ ∃ ν ∈ periodLattice,
      Metric.infDist (z - ν) (Set.range c.γ) < ε := by
    intro z
    by_cases hz : ∃ ν, PushWitness (Set.range c.γ) ε z ν
    · right
      obtain ⟨ν, hν⟩ := hz
      exact ⟨ν, hν.1, hν.2⟩
    · exact Or.inl (hΨ_not z hz)
  -- ### The geometric conclusion on the translates of the bounded side
  have hΨmain : ∀ z : ℂ, (∃ ν ∈ periodLattice,
        Metric.infDist (z - ν) (Set.range c.γ) < ε) →
      (∀ μ : ℂ, z - μ ∉ h.V) →
      ∃ ν ∈ periodLattice,
        (∃ u : ℂ, u ∈ h.U ∧ Ψ z = u + ν) ∧
        Metric.infDist (Ψ z) ({z' : ℂ | z' - ν ∈ closure h.V}) < 2 * ρ ∧
        ¬ ∃ μ ∈ periodLattice, Ψ z - μ ∈ closure h.V := by
    intro z hz hnotV
    obtain ⟨ν, hνΛ, hνd⟩ := hz
    have hνW : PushWitness (Set.range c.γ) ε z ν := ⟨hνΛ, hνd⟩
    have hval : Ψ z = ψ (z - ν) + ν := hΨ_of z ν hνW
    -- `z - ν` lies in the unbounded side or on the curve
    have hzν : z - ν ∈ h.U ∨ ∃ θ : ℝ, z - ν = c.γ θ := by
      by_cases htr : z - ν ∈ Set.range c.γ
      · right; obtain ⟨θ, hθ⟩ := htr; exact ⟨θ, hθ.symm⟩
      · left
        have hmem : z - ν ∈ h.U ∪ h.V := by rw [h.union_eq]; exact htr
        exact hmem.resolve_right (hnotV ν)
    have hψU : ψ (z - ν) ∈ h.U := hψ3 (z - ν) hzν
    have hneShift : ({z' : ℂ | z' - ν ∈ closure h.V}).Nonempty := by
      obtain ⟨v, hv⟩ := h.nonempty_V
      exact ⟨v + ν, show v + ν - ν ∈ closure h.V from by
        rw [add_sub_cancel_right]; exact subset_closure hv⟩
    have hinf : Metric.infDist (Ψ z) ({z' : ℂ | z' - ν ∈ closure h.V}) < 2 * ρ := by
      have heq : Metric.infDist (Ψ z) ({z' : ℂ | z' - ν ∈ closure h.V}) =
          Metric.infDist (ψ (z - ν)) (closure h.V) := by
        rw [infDist_shiftSet, hval]
        simp only [add_sub_cancel_right]
      rw [heq]
      have h1 : Metric.infDist (ψ (z - ν)) (closure h.V) ≤
          Metric.infDist (z - ν) (closure h.V) + ε := by
        have hh := Metric.infDist_le_infDist_add_dist (s := closure h.V)
          (x := ψ (z - ν)) (y := z - ν)
        have h2 : dist (ψ (z - ν)) (z - ν) ≤ ε := by
          rw [dist_eq_norm]; exact hψ1 (z - ν)
        linarith
      have h2 : Metric.infDist (z - ν) (closure h.V) ≤
          Metric.infDist (z - ν) (Set.range c.γ) :=
        Metric.infDist_le_infDist_of_subset htrace hneK
      linarith
    refine ⟨ν, hνΛ, ⟨⟨ψ (z - ν), hψU, hval⟩, hinf, ?_⟩⟩
    rintro ⟨μ, hμΛ, hμV⟩
    by_cases hμν : μ = ν
    · have hmem : Ψ z - μ ∈ h.U := by simpa [hval, hμν] using hψU
      exact (Set.disjoint_left.mp hUdisj) hmem hμV
    · obtain ⟨u, huV, hud⟩ := (Metric.infDist_lt_iff hneShift).mp hinf
      have hbig : 2 * ρ ≤ dist u (Ψ z) :=
        hsep ν μ hνΛ hμΛ (Ne.symm hμν) u (Ψ z) huV hμV
      rw [dist_comm] at hud
      linarith
  -- ### Continuity
  have hloc : ∀ z : ℂ, ∃ ν ∈ periodLattice, ∃ η : ℝ, 0 < η ∧
      (fun w : ℂ => ψ (w - ν) + ν) =ᶠ[nhds z] Ψ := by
    intro z
    by_cases hcase : ∃ z₀ ∈ Metric.ball z (ρ - ε), ∃ ν₀,
        PushWitness (Set.range c.γ) ε z₀ ν₀
    · obtain ⟨z₀, hz₀, ν₀, hν₀⟩ := hcase
      rw [Metric.mem_ball, dist_comm] at hz₀
      refine ⟨ν₀, hν₀.1, ρ - ε, hδpos, ?_⟩
      have hball : Metric.ball z (ρ - ε) ∈ nhds z := Metric.ball_mem_nhds z hδpos
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball] at hw
      by_cases hwU : ∃ ν, PushWitness (Set.range c.γ) ε w ν
      · obtain ⟨μ, hμ⟩ := hwU
        have hμeq : μ = ν₀ := by
          by_contra hne'
          have hsep' := hwit_sep w z₀ μ ν₀ hμ hν₀ hne'
          have hdd : dist w z₀ < 2 * (ρ - ε) := by
            have ht := dist_triangle w z z₀
            linarith
          linarith
        subst hμeq
        rw [hΨ_of w μ hμ]
      · have h2 : ψ (w - ν₀) = w - ν₀ := by
          refine hψ2 (w - ν₀) ?_
          by_contra hlt
          exact hwU ⟨ν₀, hν₀.1, lt_of_not_ge hlt⟩
        rw [h2, hΨ_not w hwU]
        ring
    · refine ⟨0, zero_mem_periodLattice, ρ - ε, hδpos, ?_⟩
      have hball : Metric.ball z (ρ - ε) ∈ nhds z := Metric.ball_mem_nhds z hδpos
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball] at hw
      have hwU : ¬ ∃ ν, PushWitness (Set.range c.γ) ε w ν := by
        rintro ⟨ν, hν⟩
        exact hcase ⟨w, hw, ν, hν⟩
      have h2 : ψ (w - 0) = w - 0 := by
        refine hψ2 (w - 0) ?_
        by_contra hlt
        exact hwU ⟨0, zero_mem_periodLattice, lt_of_not_ge hlt⟩
      rw [h2, hΨ_not w hwU]
      ring
  have hcont : Continuous Ψ := by
    rw [continuous_iff_continuousAt]
    intro z
    obtain ⟨ν₀, _, η, hη, hev⟩ := hloc z
    have hg : Continuous fun w : ℂ => ψ (w - ν₀) + ν₀ :=
      (hψc.comp (continuous_id.sub continuous_const)).add continuous_const
    exact hg.continuousAt.congr hev
  exact ⟨Ψ, hcont, hΨ1, hΨper, hΨ_or, hΨmain⟩

end

end Work.BoxShrink.PinchOff
