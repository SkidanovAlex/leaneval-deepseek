import Mathlib.Analysis.Normed.Order.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology

open Set Filter
open scoped _root_.Topology

/-- **Closed-graph limit lemma.**  Let `s ⊆ X × Y` be closed, `φ a → x₀` along a filter `F`, and
`u a` cluster at `y` along `F`.  If `(φ a, u a) ∈ s` eventually, then `(x₀, y) ∈ s`.

This is the standard "limits of a graph lie in the closed graph" argument, stated for an arbitrary
pair of maps out of a common index type. -/
theorem mem_of_mapClusterPt_of_tendsto {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set (X × Y)} (hs : IsClosed s) {F : Filter α} {φ : α → X} {u : α → Y} {x₀ : X} {y : Y}
    (hφ : Tendsto φ F (𝓝 x₀)) (hy : MapClusterPt y F u)
    (h : ∀ᶠ a in F, (φ a, u a) ∈ s) : (x₀, y) ∈ s := by
  refine hs.mem_of_mapClusterPt ?_ h
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rw [nhds_prod_eq, mem_prod_iff] at hU
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := hU
  have h1 : ∀ᶠ a in F, φ a ∈ U₁ := hφ.eventually hU₁
  have h2 : ∃ᶠ a in F, u a ∈ U₂ := hy.frequently hU₂
  exact (h2.and_eventually h1).mono fun a ⟨hua, hφa⟩ => hsub ⟨hφa, hua⟩

/-- **Roots stay in any prescribed interval, locally.**  For a continuous strictly monotone
family `t ↦ g (x, t)` whose root at `x` is `T x`, and any interval `(a, b) ∋ T x₀`, all roots
`T x` for `x` near `x₀` lie in `(a, b)`. -/
theorem eventually_root_mem_Ioo {X : Type*} [TopologicalSpace X] {g : X × ℝ → ℝ}
    (hg : Continuous g) (hmono : ∀ x, StrictMono fun t => g (x, t))
    {c : X → ℝ} (hc : Continuous c) {T : X → ℝ} (hT : ∀ x, g (x, T x) = c x)
    (x₀ : X) {a b : ℝ} (ha : a < T x₀) (hb : T x₀ < b) :
    ∀ᶠ x in 𝓝 x₀, T x ∈ Ioo a b := by
  have h1 : g (x₀, a) < c x₀ := (hmono x₀ ha).trans_eq (hT x₀)
  have h2 : c x₀ < g (x₀, b) := (hT x₀).symm.trans_lt (hmono x₀ hb)
  have hv1 : (0 : ℝ) < c x₀ - g (x₀, a) := sub_pos.mpr h1
  have hv2 : (0 : ℝ) < g (x₀, b) - c x₀ := sub_pos.mpr h2
  have hev1 : ∀ᶠ x in 𝓝 x₀, g (x, a) < c x := by
    have hcont : Continuous fun x : X => c x - g (x, a) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually
      (isOpen_Ioi.mem_nhds (show c x₀ - g (x₀, a) ∈ Ioi (0 : ℝ) from hv1))] with x hx
    exact sub_pos.mp hx
  have hev2 : ∀ᶠ x in 𝓝 x₀, c x < g (x, b) := by
    have hcont : Continuous fun x : X => g (x, b) - c x := by fun_prop
    filter_upwards [hcont.continuousAt.eventually
      (isOpen_Ioi.mem_nhds (show g (x₀, b) - c x₀ ∈ Ioi (0 : ℝ) from hv2))] with x hx
    exact sub_pos.mp hx
  filter_upwards [hev1, hev2] with x hx1 hx2
  exact ⟨((hmono x).lt_iff_lt).mp (by rw [hT x]; exact hx1),
    ((hmono x).lt_iff_lt).mp (by rw [hT x]; exact hx2)⟩

/-- **Continuity of the root of a strictly monotone family.**  Let `g : X × ℝ → ℝ` be continuous
and such that for every `x` the function `t ↦ g (x, t)` is strictly increasing.  If a continuous
function `c` admits roots, i.e. there is `T : X → ℝ` with `g (x, T x) = c x` for all `x`, then `T`
is continuous.

(Uniqueness of the root on each level is what does the work: any limit point of a sequence of roots
`T (x n)` with `x n → x` is again a root at `x`, hence equal to `T x`, and the roots cannot escape
to infinity because `c x n → c x` while `t ↦ g (x n, t)` is uniformly monotone on compact time
intervals.) -/
theorem continuous_root_of_strictMono {X : Type*} [TopologicalSpace X] {g : X × ℝ → ℝ}
    (hg : Continuous g) (hmono : ∀ x, StrictMono fun t => g (x, t))
    {c : X → ℝ} (hc : Continuous c) {T : X → ℝ} (hT : ∀ x, g (x, T x) = c x) :
    Continuous T := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hmem : ∀ᶠ x in 𝓝 x₀, T x ∈ Icc (T x₀ - 1) (T x₀ + 1) :=
    (eventually_root_mem_Ioo hg hmono hc hT x₀ (by linarith) (by linarith)).mono
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  refine (isCompact_Icc (a := T x₀ - 1) (b := T x₀ + 1)).tendsto_nhds_of_unique_mapClusterPt
    hmem ?_
  intro y _ hy
  have hgraph : IsClosed {p : X × ℝ | g p = c p.1} :=
    isClosed_eq hg (hc.comp continuous_fst)
  have hroot : g (x₀, y) = c x₀ :=
    mem_of_mapClusterPt_of_tendsto hgraph tendsto_id hy
      (Filter.Eventually.of_forall fun a => hT a)
  exact (hmono x₀).injective (by rw [hroot, hT x₀])

end Commons.Topology