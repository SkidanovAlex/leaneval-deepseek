import Mathlib
import Submission.Commons.Topology.Plane.nullhomotopic_loop_of_continuous_argument
import Submission.Commons.Topology.Plane.loop_winding_of_bounded_component

/-!
# No continuous argument on the complement of a closed set with a bounded component

We prove that if `K ⊆ ℂ` is closed, `0 ∈ K`, and the connected component of `0` in `K` is
bounded, then `Kᶜ` admits no continuous branch of the argument: there is no continuous
`θ : Kᶜ → ℝ` with `exp (θ z * I) = z / ‖z‖`.

Scratch development towards the full proof.  So far formalised:

* `norm_exp_mul_I`, `norm_rho_mul_exp` : norms of points of the circle of radius `ρ`;
* `circle_meets_of_continuous_argument` : if a continuous argument exists on `Kᶜ`, then no
  circle centred at the origin is disjoint from `K` (the "holonomy" argument).

## Structure of the intended proof, and the remaining gap

Write `C := connectedComponentIn K 0`.  The intended proof has two halves.

**(1) Easy half (formalised below).**  If a continuous argument `θ` existed on `Kᶜ`, then for
every `ρ > 0` the circle of radius `ρ` would meet `K`
(`circle_meets_of_continuous_argument`).  Equivalently every loop in `Kᶜ` has vanishing
winding number about `0`, i.e. the radial map `z ↦ z / ‖z‖ : Kᶜ → ℂ \ {0}` is null-homotopic
(the homotopy is `(s, z) ↦ exp ((1 - s) * θ z * I)`).

**(2) Geometric core (missing).**  The *converse* statement: if `C` is bounded, then `Kᶜ`
contains an essential loop, equivalently the inclusion `Kᶜ ↪ ℂ \ {0}` is **not**
null-homotopic, equivalently every continuous `θ` on `Kᶜ` leads to a contradiction by the
holonomy argument of (1).

Known facts that constrain the geometry of the core (all provable, see the discussion below):

* `C` is bounded iff `∃ ρ > 0, C ∩ sphere 0 ρ = ∅`.
* if `∃ ρ > 0, K ∩ sphere 0 ρ = ∅` then that circle is itself an essential loop, so the
  only interesting case is that `K` meets every circle;
* a connected component `D` of a closed set is closed, and if `x ∈ K` has `0` in the closure
  of its component `D`, then `D ∪ {0}` is connected and contained in `K`, hence `D ⊆ C`;
  consequently **no component of `K` other than `C` has `0` in its closure**.

### Correction found while developing the core (important!)

The naive "tube around `C`" statement is **false**: if `C` is a component of a compact `X`,
then `X \ C` is *open* in `X`, hence not compact, and other components can sneak arbitrarily
close to `C` (example: `X = {0} ∪ {1/n}`, `C = {0}`; every tube about `{0}` contains some
`1/n`).  The correct statement is *quantitative*: for each `ε > 0` the set

  `X_ε := X ∩ {z : ε ≤ dist z C}`

is compact (closed in the compact `X`) and disjoint from `C`, so by
`exists_pos_infDist_of_isCompact_of_isClosed` it stays at positive distance `δ_ε > 0` from `C`.
The winding loop must therefore be built as a limit/spiral through the shrinking gaps between
`C` and the components accumulating on it, using this quantitative separation at each scale —
this is exactly the Janiszewski-type planar topology that has to be built here.

The missing statement (an instance of the classical duality "a point of a bounded complementary
domain of a closed set is wound around by a loop in the complement", provable from
Janiszewski/Borsuk plane separation) is exactly the geometric content, and is *equivalent* to
`Commons.Topology.Jordan.nonnull_loop_of_bounded_component` (whose prover reduces it to this
file's target via the covering theory of `Commons.Topology.Covering`).  Once that geometric
core is available (in the "inclusion is not null-homotopic" form), the two halves above give
the theorem: `θ` would make the inclusion null-homotopic via (1).
-/

namespace Commons.Topology.Jordan
open Set
open _root_.Metric
open scoped Topology

lemma preconnected_subset_ball_of_disjoint_sphere {C : Set ℂ} (hC : IsPreconnected C)
    (h0 : (0 : ℂ) ∈ C) {ρ : ℝ} (hρ : 0 < ρ) (h : C ∩ sphere (0 : ℂ) ρ = ∅) :
    C ⊆ ball (0 : ℂ) ρ := by
  have himg : IsPreconnected ((fun z : ℂ => ‖z‖) '' C) :=
    hC.image _ continuous_norm.continuousOn
  have hord : ((fun z : ℂ => ‖z‖) '' C).OrdConnected := himg.ordConnected
  intro z hz
  have hzimg : ‖z‖ ∈ (fun z : ℂ => ‖z‖) '' C := ⟨z, hz, rfl⟩
  have h0img : (0 : ℝ) ∈ (fun z : ℂ => ‖z‖) '' C := ⟨0, h0, by simp⟩
  have hρnot : ρ ∉ (fun z : ℂ => ‖z‖) '' C := by
    rintro ⟨w, hwC, hw⟩
    have hmem : w ∈ C ∩ sphere (0 : ℂ) ρ :=
      ⟨hwC, by rw [mem_sphere, dist_eq_norm, sub_zero]; exact hw⟩
    rw [h] at hmem
    exact hmem
  by_contra hcon
  rw [mem_ball, dist_eq_norm, sub_zero] at hcon
  have hle : ρ ≤ ‖z‖ := le_of_not_gt hcon
  exact hρnot (hord.out h0img hzimg ⟨le_of_lt hρ, hle⟩)

/-- A connected component of a closed subset of `ℂ` is closed in `ℂ`. -/
lemma isClosed_connectedComponentIn {K : Set ℂ} (hK : IsClosed K) (x : ℂ) :
    IsClosed (connectedComponentIn K x) := by
  rcases em (x ∈ K) with hx | hx
  · rw [connectedComponentIn_eq_image hx]
    exact hK.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- **The component of `0` is the component of `0` in the intersection with a ball enclosing
it.** -/
lemma connectedComponentIn_inter_closedBall_eq {K : Set ℂ} (h0 : (0 : ℂ) ∈ K) {ρ : ℝ}
    (hρ : 0 < ρ) (h : connectedComponentIn K 0 ∩ sphere (0 : ℂ) ρ = ∅) :
    connectedComponentIn (K ∩ closedBall (0 : ℂ) ρ) 0 = connectedComponentIn K 0 := by
  apply Subset.antisymm
  · exact connectedComponentIn_mono 0 (fun z hz => hz.1)
  · have hsub : connectedComponentIn K 0 ⊆ K ∩ closedBall (0 : ℂ) ρ := by
      intro z hz
      refine ⟨connectedComponentIn_subset K 0 hz, ?_⟩
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      have hzb := preconnected_subset_ball_of_disjoint_sphere
        (C := connectedComponentIn K 0) isPreconnected_connectedComponentIn
        (mem_connectedComponentIn (F := K) h0) hρ h hz
      rw [mem_ball, dist_eq_norm, sub_zero] at hzb
      exact le_of_lt hzb
    exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn (F := K) h0) hsub

/-- **If the component `C` of `0` misses the sphere of radius `ρ`, it is compact** (it is closed
in `ℂ` and lies in the open ball of radius `ρ`). -/
lemma isCompact_connectedComponentIn_of_disjoint_sphere {K : Set ℂ} (hK : IsClosed K)
    (h0 : (0 : ℂ) ∈ K) {ρ : ℝ} (hρ : 0 < ρ)
    (h : connectedComponentIn K 0 ∩ sphere (0 : ℂ) ρ = ∅) :
    IsCompact (connectedComponentIn K 0) := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_connectedComponentIn hK 0, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ρ)).subset ?_
  intro z hz
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  have hzb := preconnected_subset_ball_of_disjoint_sphere
    (C := connectedComponentIn K 0) isPreconnected_connectedComponentIn
    (mem_connectedComponentIn (F := K) h0) hρ h hz
  rw [mem_ball, dist_eq_norm, sub_zero] at hzb
  exact le_of_lt hzb

/-- The exponential of `s * I` has norm one. -/
lemma norm_exp_mul_I (s : ℝ) : ‖Complex.exp ((s : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : ((s : ℂ) * Complex.I).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- The point `ρ * exp (s * I)` on the circle of radius `ρ`. -/
lemma norm_rho_mul_exp (ρ s : ℝ) : ‖(ρ : ℂ) * Complex.exp ((s : ℂ) * Complex.I)‖ = |ρ| := by
  rw [norm_mul, norm_exp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **If `Kᶜ` admits a continuous argument then no circle centred at `0` avoids `K`.**

For a free circle of radius `ρ`, the function `s ↦ (θ (ρ exp (s I)) - s) / 2π` would be a
continuous `ℤ`-valued function on the connected space `ℝ`, hence constant; but its values at
`s` and `s + 2π` differ by `1`. -/
lemma circle_meets_of_continuous_argument {K : Set ℂ} (_hK : IsClosed K) (_h0 : (0 : ℂ) ∈ K)
    (hθ : ∃ θ : C({z : ℂ // z ∈ Kᶜ}, ℝ),
      ∀ z, Complex.exp ((θ z : ℝ) * Complex.I) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)))
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ z ∈ K, ‖z‖ = ρ := by
  obtain ⟨θ, hθ⟩ := hθ
  by_contra hcon
  push Not at hcon
  have hmem : ∀ s : ℝ, ((ρ : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) ∈ Kᶜ := by
    intro s
    simp only [mem_compl_iff]
    intro hs
    refine hcon _ hs ?_
    rw [norm_rho_mul_exp, abs_of_pos hρ]
  let F : ℝ → ℝ := fun s => θ ⟨(ρ : ℂ) * Complex.exp ((s : ℂ) * Complex.I), hmem s⟩
  have hFcont : Continuous F :=
    Continuous.comp θ.continuous (Continuous.subtype_mk (by fun_prop) _)
  have hmem2 : ∀ s : ℝ, F s - s ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    intro s
    rw [AddSubgroup.mem_zmultiples_iff]
    have hnorm : ‖(ρ : ℂ) * Complex.exp ((s : ℂ) * Complex.I)‖ = ρ := by
      rw [norm_rho_mul_exp, abs_of_pos hρ]
    have h := hθ ⟨(ρ : ℂ) * Complex.exp ((s : ℂ) * Complex.I), hmem s⟩
    have h1 : Complex.exp ((F s : ℝ) * Complex.I) = Complex.exp ((s : ℝ) * Complex.I) := by
      rw [h, hnorm]
      have hρc : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
    refine ⟨n, ?_⟩
    have hcast : ((F s : ℝ) : ℂ) = (((s + (n : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) := by
      have h2 := congrArg (fun z : ℂ => z * Complex.I) hn
      have h3 : -(((F s : ℝ)) : ℂ) =
          -(((s : ℝ) : ℂ)) + -((n : ℂ) * (2 * (Real.pi : ℂ))) := by
        simpa [mul_add, add_mul, mul_assoc, Complex.I_mul_I] using h2
      have h4 : ((F s : ℝ) : ℂ) = ((s : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
        linear_combination -h3
      rw [h4]; push_cast; ring
    have hreal : F s = s + n * (2 * Real.pi) := Complex.ofReal_inj.mp hcast
    rw [zsmul_eq_mul, hreal]
    ring
  let G : ℝ → (AddSubgroup.zmultiples (2 * Real.pi) : Type) := fun s => ⟨F s - s, hmem2 s⟩
  have hGcont : Continuous G := Continuous.subtype_mk (hFcont.sub continuous_id) _
  have hconst : ∀ s : ℝ, G s = G 0 := fun s =>
    PreconnectedSpace.constant (α := ℝ) (Y := (AddSubgroup.zmultiples (2 * Real.pi) : Type))
      (inferInstance : PreconnectedSpace ℝ) hGcont
  have hsame : G (2 * Real.pi) = G 0 := hconst (2 * Real.pi)
  have hval : F (2 * Real.pi) - 2 * Real.pi = F 0 - 0 := congrArg Subtype.val hsame
  have hFeq : F (2 * Real.pi) = F 0 := by
    have hpt : (ρ : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = (ρ : ℂ) := by
      have harg : (((2 * Real.pi : ℝ)) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_two_pi_mul_I, mul_one]
    have hpt0 : (ρ : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = (ρ : ℂ) := by simp
    have hsub : (⟨(ρ : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I),
          hmem (2 * Real.pi)⟩ : {z : ℂ // z ∈ Kᶜ}) =
        ⟨(ρ : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I), hmem 0⟩ :=
      Subtype.ext (hpt.trans hpt0.symm)
    exact congrArg θ hsub
  rw [hFeq] at hval
  linarith [Real.pi_pos]

/-- **A compact set and a disjoint nonempty closed set in `ℂ` have positive distance.**

Consequently there is a "tube" around a compact set `C` avoiding any disjoint nonempty closed
set `D`.  This is the first quantitative ingredient of the geometric core: it will be applied
to `C = connectedComponentIn K 0` (compact, when bounded) and to the rest of `K`. -/
lemma exists_pos_infDist_of_isCompact_of_isClosed {C D : Set ℂ} (hC : IsCompact C)
    (hCne : C.Nonempty) (hD : IsClosed D) (hDne : D.Nonempty) (h : Disjoint C D) :
    ∃ δ > 0, ∀ x ∈ C, δ ≤ Metric.infDist x D := by
  have hpos : ∀ x ∈ C, 0 < Metric.infDist x D := fun x hx =>
    (hD.notMem_iff_infDist_pos hDne).mp fun hxD => Set.disjoint_left.mp h hx hxD
  obtain ⟨x₀, hx₀C, hmin⟩ :=
    hC.exists_isMinOn hCne (Metric.continuous_infDist_pt D).continuousOn
  exact ⟨Metric.infDist x₀ D, hpos x₀ hx₀C, fun x hx => hmin hx⟩

/-- **Quantitative separation at scale `ε`.**

If `X ⊆ ℂ` is compact and `C ⊆ X` is closed and nonempty, then for every `ε > 0` the part
`X_ε = X ∩ {z : ε ≤ infDist z C}` of `X` at distance at least `ε` from `C` is compact (it is
closed in the compact `X`), disjoint from `C`, and hence stays at positive distance from `C`.

This is the scale-by-scale control used by the winding-loop construction: the "far" part of
`X` at every scale is a compact set disjoint from `C`. -/
lemma exists_compact_separation_at_scale {X C : Set ℂ} (hX : IsCompact X) (hC : IsClosed C)
    (hCne : C.Nonempty) (h : C ⊆ X) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (X ∩ {z : ℂ | ε ≤ Metric.infDist z C}) ∧
      Disjoint (X ∩ {z : ℂ | ε ≤ Metric.infDist z C}) C ∧
      ∃ δ > 0, ∀ x ∈ X ∩ {z : ℂ | ε ≤ Metric.infDist z C}, δ ≤ Metric.infDist x C := by
  have hclosed : IsClosed {z : ℂ | ε ≤ Metric.infDist z C} :=
    isClosed_le continuous_const (Metric.continuous_infDist_pt C)
  have hK : IsCompact (X ∩ {z : ℂ | ε ≤ Metric.infDist z C}) := hX.inter_right hclosed
  have hle : ∀ c ∈ C, Metric.infDist c C = 0 := fun c hc =>
    le_antisymm (by simpa using Metric.infDist_le_dist_of_mem (x := c) hc) (Metric.infDist_nonneg)
  have hdisj : Disjoint (X ∩ {z : ℂ | ε ≤ Metric.infDist z C}) C := by
    rw [Set.disjoint_left]
    rintro c ⟨-, hcε⟩ hc
    have hcε' : ε ≤ Metric.infDist c C := hcε
    rw [hle c hc] at hcε'
    linarith
  refine ⟨hK, hdisj, ?_⟩
  rcases eq_empty_or_nonempty (X ∩ {z : ℂ | ε ≤ Metric.infDist z C}) with hem | hne
  · refine ⟨ε, hε, ?_⟩
    intro x hx
    rw [hem] at hx
    exact absurd hx (by simp)
  · exact exists_pos_infDist_of_isCompact_of_isClosed hK hne hC hCne hdisj

/-- **`K` cannot fill every circle.**

If the component of `0` in `K` is bounded, then `K` misses some circle centred at the origin.
Indeed, if `K` contained every such circle then `K = ℂ`, so the component of `0` would be all
of `ℂ`, contradicting boundedness.  Thus (in the presence of a continuous argument, which
already forces every circle to meet `K`) the circle `S_r` always meets `K` but is never
contained in it — the starting point of the loop construction. -/
lemma exists_sphere_not_subset_of_isBounded {K : Set ℂ} (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ r > 0, ¬ sphere (0 : ℂ) r ⊆ K := by
  by_contra hcon
  push Not at hcon
  have hKall : K = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z = 0
    · simpa [hz] using h0
    · refine hcon ‖z‖ (norm_pos_iff.mpr hz) ?_
      rw [mem_sphere, dist_zero_right]
  rw [hKall] at hbdd
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ] at hbdd
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
  have h1 : max C 0 + 1 ≤ C := by
    have := hC (((max C 0 + 1 : ℝ)) : ℂ) (Set.mem_univ _)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  have := le_max_left C 0
  linarith

/-- **Geometric core (the one remaining gap).**

If `K ⊆ ℂ` is closed, `0 ∈ K`, and the component of `0` in `K` is bounded, then `Kᶜ` contains
an *essential* loop: a loop `γ` in `Kᶜ`, with a basepoint `t₀`, such that no homotopy from `γ`
to the constant loop at `γ t₀` can avoid `0`.  Equivalently the inclusion `Kᶜ ↪ ℂ \ {0}` is
not null-homotopic.

This is the classical planar-topology statement (Janiszewski/Borsuk duality: a point of a
bounded complementary domain of a closed set is wound around by a loop in the complement), to
be built from the rungs in this file: `C` is compact and a component of the compact set
`K ∩ closedBall 0 ρ` (`connectedComponentIn_inter_closedBall_eq`,
`isCompact_connectedComponentIn_of_disjoint_sphere`), the free part of each circle is nonempty
and has arcs ending on `K` (`exists_sphere_not_subset_of_isBounded`,
`circle_meets_of_continuous_argument`), and the far part of `K` at each scale is compact and
separated from `C` (`exists_compact_separation_at_scale`). -/
theorem exists_essential_loop_of_bounded_component {K : Set ℂ} (hK : IsClosed K)
    (h0 : (0 : ℂ) ∈ K) (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ t ∈ Kᶜ) ∧ ∃ t₀ : Circle,
      ¬ ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ) := by
  exact Commons.Topology.Plane.loop_winding_of_bounded_component hK h0 hbdd

/-- **A component of a proper open subset of `ℝ` has its closure meeting the complement.**

If `F ⊆ ℝ` is open, `s ∈ F`, and `F ≠ univ`, then the closure of the connected component of
`s` in `F` meets `Fᶜ`: the free interval "ends" on the complement.

This is the interval form of the free-arc lemma for a circle: it works on the real line, where
`LocallyConnectedSpace ℝ` is available, instead of on `Metric.sphere 0 r`, where it is not.
(The proof: the closure of the component is preconnected and contains `s`, so if it avoided the
complement it would lie in `F` and hence in the component, making the component closed; it is
also open, so it is a clopen subset of the preconnected `ℝ`, hence all of `ℝ`.) -/
theorem closure_component_meets_compl_of_isOpen {F : Set ℝ} (hF : IsOpen F) {s : ℝ}
    (hs : s ∈ F) (hne : Fᶜ.Nonempty) : (closure (connectedComponentIn F s) ∩ Fᶜ).Nonempty := by
  by_contra hcon
  set J : Set ℝ := connectedComponentIn F s with hJ
  have hsJ : s ∈ J := mem_connectedComponentIn hs
  have hJsub : J ⊆ F := connectedComponentIn_subset F s
  have hcl_sub : closure J ⊆ F := by
    intro y hy
    by_contra hyF
    exact hcon ⟨y, hy, hyF⟩
  have hJcl : closure J ⊆ J :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn.closure
      (subset_closure hsJ) hcl_sub
  have hJclosed : IsClosed J := closure_subset_iff_isClosed.mp hJcl
  have hJopen : IsOpen J := hF.connectedComponentIn
  have hJall : J = Set.univ := by
    rcases isClopen_iff.mp (⟨hJclosed, hJopen⟩ : IsClopen J) with h | h
    · rw [h] at hsJ
      exact absurd hsJ (by simp)
    · exact h
  obtain ⟨y, hy⟩ := hne
  exact hy (hJsub (hJall ▸ Set.mem_univ y))

/-- The parametrization `circleMap 0 r`, `r > 0`, is surjective onto the sphere of radius
`r`. -/
lemma circleMap_surj_sphere {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) r) :
    ∃ s : ℝ, circleMap (0 : ℂ) r s = z := by
  have hnorm : ‖z‖ = r := by
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact hz
  refine ⟨z.arg, ?_⟩
  rw [circleMap_zero, ← hnorm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- **The free arc of a circle about the origin ends on `K`** (parametrized form).

If `K ⊆ ℂ` is closed, `r > 0`, the circle of radius `r` meets `K` but is not contained in it,
then some point `s` of `ℝ` whose image under the parametrization `circleMap 0 r` is free has
the property that the connected component of `s` in the (open) free part of `ℝ` has closure
meeting the preimage of `K`: the free interval ends on `K`.

This is the interval form of the free-arc lemma; it quotes the real line, where
`LocallyConnectedSpace ℝ` is available, rather than the sphere subtype (where no such instance
exists in Mathlib). -/
theorem circle_free_arc_ends_in_K {K : Set ℂ} (hK : IsClosed K) {r : ℝ} (hr : 0 < r)
    (hne : (Metric.sphere (0 : ℂ) r ∩ K).Nonempty)
    (hfree : ∃ z ∈ Metric.sphere (0 : ℂ) r, z ∉ K) :
    ∃ s : ℝ, circleMap (0 : ℂ) r s ∉ K ∧
      (closure (connectedComponentIn {s' : ℝ | circleMap (0 : ℂ) r s' ∉ K} s)
        ∩ {s' : ℝ | circleMap (0 : ℂ) r s' ∈ K}).Nonempty := by
  obtain ⟨z, hz, hzK⟩ := hfree
  obtain ⟨s, hs⟩ := circleMap_surj_sphere hr hz
  have hsF : circleMap (0 : ℂ) r s ∉ K := by
    rw [hs]; exact hzK
  have hFopen : IsOpen {s' : ℝ | circleMap (0 : ℂ) r s' ∉ K} :=
    hK.isOpen_compl.preimage (continuous_circleMap 0 r)
  have hne' : ({s' : ℝ | circleMap (0 : ℂ) r s' ∉ K}ᶜ).Nonempty := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨s', hs'⟩ := circleMap_surj_sphere hr hw.1
    refine ⟨s', ?_⟩
    rw [mem_compl_iff]
    simp only [Set.mem_setOf_eq, not_not]
    rw [hs']
    exact hw.2
  refine ⟨s, hsF, ?_⟩
  have hmain := closure_component_meets_compl_of_isOpen hFopen hsF hne'
  have hEq : ({s' : ℝ | circleMap (0 : ℂ) r s' ∉ K}ᶜ : Set ℝ) =
      {s' : ℝ | circleMap (0 : ℂ) r s' ∈ K} := by
    ext s'
    simp
  rwa [hEq] at hmain

/-- **A bounded component of an open subset of `ℝ` is an open interval whose endpoints are
outside the open set.**

More precisely, for `F ⊆ ℝ` open, `s ∈ F` and `J = connectedComponentIn F s` bounded, there are
`a < s < b` with `J = Ioo a b` and `a, b ∉ F`. -/
theorem exists_Ioo_eq_connectedComponentIn {F : Set ℝ} (hF : IsOpen F) {s : ℝ} (hs : s ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F s)) :
    ∃ a b : ℝ, a < s ∧ s < b ∧ connectedComponentIn F s = Ioo a b ∧ a ∉ F ∧ b ∉ F := by
  set J : Set ℝ := connectedComponentIn F s with hJ
  have hJopen : IsOpen J := hF.connectedComponentIn
  have hJord : J.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  have hsJ : s ∈ J := mem_connectedComponentIn hs
  have hbddB : BddBelow J := hbdd.bddBelow
  have hbddA : BddAbove J := hbdd.bddAbove
  have hne : J.Nonempty := ⟨s, hsJ⟩
  -- points just below and just above `s` lie in `J`
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hJopen s hsJ
  have hbelow : s - ε / 2 ∈ J := by
    apply hε
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have habove : s + ε / 2 ∈ J := by
    apply hε
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hlt1 : sInf J < s := lt_of_le_of_lt (csInf_le hbddB hbelow) (by linarith)
  have hlt2 : s < sSup J := lt_of_lt_of_le (by linarith) (le_csSup hbddA habove)
  refine ⟨sInf J, sSup J, hlt1, hlt2, ?_, ?_, ?_⟩
  · refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      refine ⟨?_, ?_⟩
      · rcases lt_or_eq_of_le (csInf_le hbddB hx) with h | h
        · exact h
        · exfalso
          obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hJopen x hx
          have hmem : x - δ / 2 ∈ J := by
            apply hδ
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor <;> linarith
          have := csInf_le hbddB hmem
          rw [← h] at this
          linarith
      · rcases lt_or_eq_of_le (le_csSup hbddA hx) with h | h
        · exact h
        · exfalso
          obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hJopen x hx
          have hmem : x + δ / 2 ∈ J := by
            apply hδ
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor <;> linarith
          have := le_csSup hbddA hmem
          rw [← h] at this
          linarith
    · rintro t ⟨ht1, ht2⟩
      obtain ⟨x, hxJ, hxt⟩ := exists_lt_of_csInf_lt hne ht1
      obtain ⟨y, hyJ, hty⟩ := exists_lt_of_lt_csSup hne ht2
      exact hJord.out hxJ hyJ ⟨le_of_lt hxt, le_of_lt hty⟩
  · intro haF
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hF (sInf J) haF
    obtain ⟨x, hxJ, hxlt⟩ := exists_lt_of_csInf_lt hne (show sInf J < sInf J + δ by linarith)
    have htF : sInf J - δ / 2 ∈ F := by
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hseg : Set.Icc (sInf J - δ / 2) x ⊆ F := by
      intro u hu
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    have hpre : IsPreconnected (Set.Icc (sInf J - δ / 2) x) := (convex_Icc _ _).isPreconnected
    have hx_ge : sInf J - δ / 2 ≤ x := by
      have := csInf_le hbddB hxJ
      linarith
    have hsub : Set.Icc (sInf J - δ / 2) x ⊆ connectedComponentIn F x :=
      hpre.subset_connectedComponentIn ⟨hx_ge, le_rfl⟩ hseg
    rw [← connectedComponentIn_eq hxJ] at hsub
    have hmem : sInf J - δ / 2 ∈ J := hsub ⟨le_rfl, by linarith⟩
    have := csInf_le hbddB hmem
    linarith
  · intro hbF
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hF (sSup J) hbF
    obtain ⟨x, hxJ, hxgt⟩ := exists_lt_of_lt_csSup hne (show sSup J - δ < sSup J by linarith)
    have htF : sSup J + δ / 2 ∈ F := by
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hseg : Set.Icc x (sSup J + δ / 2) ⊆ F := by
      intro u hu
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    have hpre : IsPreconnected (Set.Icc x (sSup J + δ / 2)) := (convex_Icc _ _).isPreconnected
    have hx_le : x ≤ sSup J + δ / 2 := by
      have := le_csSup hbddA hxJ
      linarith
    have hsub : Set.Icc x (sSup J + δ / 2) ⊆ connectedComponentIn F x :=
      hpre.subset_connectedComponentIn ⟨le_rfl, hx_le⟩ hseg
    rw [← connectedComponentIn_eq hxJ] at hsub
    have hmem : sSup J + δ / 2 ∈ J := hsub ⟨by linarith, le_rfl⟩
    have := le_csSup hbddA hmem
    linarith


/-- If `K ⊆ ℂ` is closed, `0 ∈ K`, and the connected component of `0` in `K` is bounded, then
`Kᶜ` admits **no continuous argument** (no continuous real function `θ` with
`exp(θ z * I) = z / ‖z‖` for all `z ∈ Kᶜ`).  Equivalently, the inclusion `Kᶜ ↪ ℂ*` is not
null-homotopic. -/
theorem no_continuous_argument_of_bounded_component
    {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ¬ ∃ θ : C({z : ℂ // z ∈ Kᶜ}, ℝ),
        ∀ z, Complex.exp ((θ z : ℝ) * Complex.I) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) := by
  rintro hθ
  obtain ⟨γ, hγ, t₀, hγess⟩ := exists_essential_loop_of_bounded_component hK h0 hbdd
  exact hγess
    (Commons.Topology.Plane.nullhomotopic_loop_of_continuous_argument hK h0 hθ γ hγ t₀)

end Commons.Topology.Jordan
