import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.interior_unitBox
import Submission.Work.Drive.crossing_of_deriv_ne_zero

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Flows tangent to a locally-graph-like set: definitions

The manifold version of the mod-2 boundary parity (`Work.Drive.boxParity`) replaces the global
cutting function `F : ℝ^{m+1} → ℝ^m` by a *global tangential field* `V` whose flow lines lie in the
intersection set `K`.  This file sets up the abstract framework for that argument:

* `FlowChart W K p` — a local chart for `K` near `p`: `K` is the graph of `η` over the coordinate
  `i` in the region `{|x i - p i| < δ} ∩ {‖x - (x i) eᵢ - η (x i)‖ < ρ}`, and the `i`-th component
  of the field `W` is bounded below by `c > 0` there;
* `FlowSetup m` — a field `W`, its flow `Φ` (`Φ 0 = id`, `Φ (s + t) = Φ s ∘ Φ t`, integral curve
  equation), and a set `K` invariant under the flow;
* `FlowCover S` — a finite cover of `K ∩ [0,1]^{m+1}` by `FlowChart` regions;
* the reversed setup (`FlowSetup.reverse`), used to obtain the backward-time statements from the
  forward-time ones;
* `crossing_of_deriv_ne_zero_gen`: a curve with nonzero `i`-th derivative at a boundary point of the
  box crosses the box boundary transversally there.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- A local chart for the set `K` on which the field `W` has a non-vanishing tangential component
along `K`: `K` is the graph of `η` over the coordinate `i`, and `|W x i| ≥ c` on the region. -/
structure FlowChart {m : ℕ} (W : Amb m → Amb m) (K : Set (Amb m)) (p : Amb m) where
  /-- The index of the coordinate over which `K` is a graph. -/
  i : Fin (m + 1)
  /-- Radius of the chart in the `i`-th coordinate. -/
  δ : ℝ
  /-- Radius of the chart in the normal direction to the graph. -/
  ρ : ℝ
  /-- Lower bound for the `i`-th component of the field on the chart region. -/
  c : ℝ
  /-- The parametrisation of `K`: the graph of `u ↦ u • eᵢ + η u`. -/
  η : ℝ → Amb m
  hδ : 0 < δ
  hρ : 0 < ρ
  hc : 0 < c
  hηc : Continuous η
  hηi : ∀ u, η u i = 0
  hgraph : ∀ x, |x i - p i| < δ →
    ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ → x ∈ K →
    x = (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i)
  hvel : ∀ x, |x i - p i| < δ →
    ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ → c ≤ |W x i|

/-- The graph map `u ↦ u • eᵢ + η u` of a chart. -/
def FlowChart.graph {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) : ℝ → Amb m :=
  fun u => u • EuclideanSpace.single C.i (1 : ℝ) + C.η u

/-- The region of a chart: the tubular neighbourhood of the graph on which the chart is valid. -/
def FlowChart.region {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) : Set (Amb m) :=
  {x | |x C.i - p C.i| < C.δ ∧
    ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) - C.η (x C.i)‖ < C.ρ}

@[simp] theorem FlowChart.mem_region {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) (x : Amb m) :
    x ∈ C.region ↔ |x C.i - p C.i| < C.δ ∧
      ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) - C.η (x C.i)‖ < C.ρ := Iff.rfl

/-- The coordinate of the graph point at parameter `u` is `u`. -/
theorem FlowChart.graph_apply_i {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) (u : ℝ) : C.graph u C.i = u := by
  simp [FlowChart.graph, PiLp.add_apply, PiLp.smul_apply, C.hηi u]

/-- A point of the graph over the slab `|u - p i| < δ` lies in the region of the chart. -/
theorem FlowChart.graph_mem_region {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) {u : ℝ} (hu : |u - p C.i| < C.δ) : C.graph u ∈ C.region := by
  have hci : (u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i = u := by
    simp [PiLp.add_apply, PiLp.smul_apply, C.hηi u]
  rw [FlowChart.mem_region]
  refine ⟨?_, ?_⟩
  · show |(u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i - p.ofLp C.i| < C.δ
    rw [hci]
    exact hu
  · show ‖u • EuclideanSpace.single C.i (1 : ℝ) + C.η u -
      (u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i •
        EuclideanSpace.single C.i (1 : ℝ) - C.η ((u • EuclideanSpace.single C.i (1 : ℝ) +
          C.η u).ofLp C.i)‖ < C.ρ
    rw [hci]
    have h0 : u • EuclideanSpace.single C.i (1 : ℝ) + C.η u -
        u • EuclideanSpace.single C.i (1 : ℝ) - C.η u = 0 := by abel
    rw [h0, norm_zero]
    exact C.hρ

/-- The region of a chart is open. -/
theorem FlowChart.isOpen_region {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) : IsOpen C.region := by
  have h1 : Continuous fun x : Amb m => |x C.i - p C.i| := by fun_prop
  have h2 : Continuous fun x : Amb m => ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) -
      C.η (x C.i)‖ := by
    have : Continuous fun x : Amb m => C.η (x C.i) := C.hηc.comp (by fun_prop)
    fun_prop
  rw [FlowChart.region]
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

/-- A point of `K` in the region of a chart lies on the graph. -/
theorem FlowChart.eq_graph_of_mem_region {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)}
    {p : Amb m} (C : FlowChart W K p) {x : Amb m} (hx : x ∈ C.region) (hK : x ∈ K) :
    x = C.graph (x C.i) := by
  rw [FlowChart.mem_region] at hx
  exact C.hgraph x hx.1 hx.2 hK

/-- Continuity of the graph map of a chart. -/
theorem FlowChart.continuous_graph {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) : Continuous C.graph := by
  have h1 : Continuous fun u : ℝ => u • (EuclideanSpace.single C.i (1 : ℝ) : Amb m) :=
    continuous_id.smul continuous_const
  exact h1.add C.hηc

/-- The reversal of a chart under `W ↦ -W`: only the velocity bound changes. -/
def FlowChart.neg {m : ℕ} {W : Amb m → Amb m} {K : Set (Amb m)} {p : Amb m}
    (C : FlowChart W K p) : FlowChart (-W) K p where
  i := C.i
  δ := C.δ
  ρ := C.ρ
  c := C.c
  η := C.η
  hδ := C.hδ
  hρ := C.hρ
  hc := C.hc
  hηc := C.hηc
  hηi := C.hηi
  hgraph := C.hgraph
  hvel := by
    intro x h1 h2
    simpa using C.hvel x h1 h2

/-- Negation reflects the interval `Set.uIcc 0 t` into `Set.uIcc 0 (-t)`. -/
theorem mem_uIcc_zero_neg_iff (t v : ℝ) :
    v ∈ Set.uIcc (0 : ℝ) (-t) ↔ -v ∈ Set.uIcc (0 : ℝ) t := by
  rw [Set.mem_uIcc, Set.mem_uIcc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- **The abstract flow setup**: a smooth field `W`, its flow `Φ`, and a set `K` invariant under
the flow, with the flow lines inside `K` being integral curves of `W`. -/
structure FlowSetup (m : ℕ) where
  /-- The vector field. -/
  W : Amb m → Amb m
  /-- Its flow. -/
  Φ : ℝ → Amb m → Amb m
  /-- The invariant set. -/
  K : Set (Amb m)
  zero : ∀ x, Φ 0 x = x
  add : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)
  deriv : ∀ x t, HasDerivAt (fun s => Φ s x) (W (Φ t x)) t
  /-- Invariance of `K`: a flow line starting in `K` is again in `K` at time `t`, provided it stays
  in the closed box on the whole interval between the times `0` and `t`. -/
  mapsTo : ∀ x ∈ K, ∀ t : ℝ,
    (∀ u ∈ Set.uIcc (0 : ℝ) t, Φ u x ∈ Submission.Drive.unitBox m) → Φ t x ∈ K
  cont : Continuous W

namespace FlowSetup

variable {m : ℕ}

/-- The flow line of the setup through `x`. -/
def line (S : FlowSetup m) (x : Amb m) : ℝ → Amb m := fun t => S.Φ t x

theorem line_zero (S : FlowSetup m) (x : Amb m) : S.line x 0 = x := S.zero x

theorem line_deriv (S : FlowSetup m) (x : Amb m) (t : ℝ) :
    HasDerivAt (S.line x) (S.W (S.line x t)) t := S.deriv x t

theorem line_continuous (S : FlowSetup m) (x : Amb m) : Continuous (S.line x) :=
  continuous_iff_continuousAt.mpr fun t => (S.line_deriv x t).continuousAt

theorem line_mem (S : FlowSetup m) {x : Amb m} (hx : x ∈ S.K) {t : ℝ}
    (hbox : ∀ u ∈ Set.uIcc (0 : ℝ) t, S.line x u ∈ Submission.Drive.unitBox m) :
    S.line x t ∈ S.K :=
  S.mapsTo x hx t hbox

theorem line_add (S : FlowSetup m) (x : Amb m) (s t : ℝ) :
    S.line x (s + t) = S.line (S.line x t) s := S.add s t x

/-- A flow line which takes the same value at two times is periodic. -/
theorem line_periodic_of_eq (S : FlowSetup m) {x : Amb m} {s t : ℝ}
    (h : S.line x s = S.line x t) : Function.Periodic (S.line x) (s - t) := by
  have hs : S.Φ s x = S.Φ t x := h
  have hback : S.Φ (s - t) x = x := by
    have h1 : S.Φ (-t) (S.Φ s x) = S.Φ (-t) (S.Φ t x) := by rw [hs]
    rw [← S.add (-t) s x, ← S.add (-t) t x, neg_add_cancel, S.zero x] at h1
    rw [show -t + s = s - t by ring] at h1
    exact h1
  intro u
  show S.Φ (u + (s - t)) x = S.Φ u x
  rw [S.add u (s - t) x, hback]

/-- Shifting a flow line: the line through `S.line x t₀` is the line through `x` shifted by
`t₀`. -/
theorem line_shift (S : FlowSetup m) (x : Amb m) (t₀ : ℝ) :
    S.line (S.line x t₀) = fun t => S.line x (t + t₀) := by
  funext t
  show S.Φ t (S.Φ t₀ x) = S.line x (t + t₀)
  rw [← S.add t t₀ x]
  rfl

/-- **The reversed setup**: the flow of `-W` is the reverse of the flow of `W`, and the same set `K`
is invariant. -/
def reverse (S : FlowSetup m) : FlowSetup m where
  W := -S.W
  Φ := fun t x => S.Φ (-t) x
  K := S.K
  zero := by
    intro x
    simpa using S.zero x
  add := by
    intro s t x
    rw [show -(s + t) = -s + -t by ring, S.add (-s) (-t) x]
  deriv := by
    intro x t
    have hiff := hasDerivWithinAt_comp_mul_left_smul_iff (c := (-1 : ℝ))
      (f := fun u : ℝ => S.Φ u x) (f' := S.W (S.Φ (-t) x)) (s := Set.univ) (x := t)
    have hmain : HasDerivWithinAt (fun s : ℝ => S.Φ ((-1 : ℝ) * s) x)
        ((-1 : ℝ) • S.W (S.Φ (-t) x)) Set.univ t := by
      refine hiff.mpr ?_
      simpa using (S.deriv x (-t)).hasDerivWithinAt
    have := hasDerivWithinAt_univ.mp hmain
    simpa [Pi.neg_apply, neg_one_mul, neg_one_smul] using this
  mapsTo := by
    intro x hx t hbox
    have h : ∀ v ∈ Set.uIcc (0 : ℝ) (-t), S.Φ v x ∈ Submission.Drive.unitBox m := by
      intro v hv
      have hv' : -v ∈ Set.uIcc (0 : ℝ) t := (mem_uIcc_zero_neg_iff t v).mp hv
      simpa using hbox (-v) hv'
    exact S.mapsTo x hx (-t) h
  cont := S.cont.neg

@[simp] theorem reverse_W (S : FlowSetup m) : S.reverse.W = -S.W := rfl

theorem reverse_line (S : FlowSetup m) (x : Amb m) : S.reverse.line x = fun t => S.line x (-t) :=
  rfl

end FlowSetup

/-- A finite cover of `K ∩ [0,1]^{m+1}` by `FlowChart` regions. -/
@[ext]
structure FlowCover {m : ℕ} (S : FlowSetup m) where
  /-- The index type of the cover. -/
  ι : Type
  /-- The index type of the cover is finite. -/
  str : Fintype ι
  /-- The centres of the charts. -/
  p : ι → Amb m
  /-- The charts. -/
  C : ∀ j : ι, FlowChart S.W S.K (p j)
  cover : S.K ∩ Submission.Drive.unitBox m ⊆ ⋃ j, (C j).region

namespace FlowCover

attribute [instance] FlowCover.str

variable {m : ℕ} {S : FlowSetup m}

/-- A boundary point of `K` lies in some chart of the cover. -/
theorem exists_chart_mem (Cov : FlowCover S) {x : Amb m} (hx : x ∈ S.K)
    (hx' : x ∈ Submission.Drive.unitBox m) : ∃ j : Cov.ι, x ∈ (Cov.C j).region := by
  have h := Cov.cover ⟨hx, hx'⟩
  simpa using h

/-- The reversed cover: the same charts work for the reversed field, since the velocity bound is
stated with an absolute value. -/
def reverse (Cov : FlowCover S) : FlowCover S.reverse where
  ι := Cov.ι
  str := Cov.str
  p := Cov.p
  C := fun j => (Cov.C j).neg
  cover := by
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j, x ∈ (Cov.C j).region :=
      Cov.exists_chart_mem hx.1 hx.2
    exact Set.mem_iUnion.mpr ⟨j, hj⟩

end FlowCover

/-! ## Transversal crossing of the box boundary -/

/-- **A curve crosses the boundary of the unit box transversally.**  If `γ` is differentiable at
`0` with derivative `w`, `γ 0 = b` lies on exactly one face `i` of the box (`b i ∈ {0,1}`, all other
coordinates strictly inside `(0,1)`) and `w i ≠ 0`, then `γ` enters the interior of the box on one
side of `0` and lies outside the box on the other side. -/
theorem crossing_of_deriv_ne_zero_gen {m : ℕ} {γ : ℝ → Amb m} {b w : Amb m}
    (hγ : HasDerivAt γ w 0) (hγcont : Continuous γ) (hb0 : γ 0 = b) (i : Fin (m + 1))
    (hface : (b i = 0 ∨ b i = 1) ∧ (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1))
    (hne : w i ≠ 0) :
    ∃ ε > 0, ((∀ t ∈ Set.Ioo (0 : ℝ) ε, γ t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (-ε) 0, γ t ∉ Submission.Drive.unitBox m)) ∨
      ((∀ t ∈ Set.Ioo (-ε) 0, γ t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) ε, γ t ∉ Submission.Drive.unitBox m)) := by
  have hderiv : HasDerivAt (fun s => γ s i) (w i) 0 := hasDerivAt_apply hγ i
  have hf0 : γ 0 i = b i := by simp [hb0]
  -- All coordinates other than the `i`-th are strictly inside `(0,1)` near `t = 0`.
  have hgood : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j : Fin (m + 1), j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
    refine Filter.eventually_all.mpr (fun j => ?_)
    rcases eq_or_ne j i with rfl | hj
    · exact Filter.Eventually.of_forall (fun t h => absurd rfl h)
    · have hmem : {x : Amb m | x j ∈ Ioo (0:ℝ) 1} ∈ 𝓝 (γ 0) := by
        rw [hb0]
        exact (isOpen_Ioo.preimage (by fun_prop)).mem_nhds (hface.2 j hj)
      filter_upwards [hγcont.continuousAt.preimage_mem_nhds hmem] with t ht
      exact fun _ => ht
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hgood
  rcases lt_or_gt_of_ne hne with hc | hc
  · -- the `i`-th component of the field at `b` is negative
    obtain ⟨δ₁, hδ₁, hP1, hP2, hP3⟩ := scalar_neg hderiv hc
    have hoth : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → ∀ j, j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
      intro t ht j hj
      refine hδ₂ ?_ j hj
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂], by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have inside_of : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → γ t i ∈ Ioo (0:ℝ) 1 →
        γ t ∈ interior (Submission.Drive.unitBox m) := by
      intro t ht hti
      rw [interior_unitBox m]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · exact hti
      · exact hoth t ht j hj
    have outside_of : ∀ t, (γ t i < 0 ∨ 1 < γ t i) → γ t ∉ Submission.Drive.unitBox m := by
      intro t h hmem
      have hmem' : γ t i ∈ Set.Icc (0:ℝ) 1 := hmem i
      rcases h with h | h
      · linarith [hmem'.1]
      · linarith [hmem'.2]
    rcases hface.1 with hbi0 | hbi1
    · -- `b i = 0`: the curve enters on the negative side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inr ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨ht.1, by linarith [ht.2, lt_min hδ₁ hδ₂pos]⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
          simp only [hf0, hbi0] at h'
          exact h'
        · have h' := hP3 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], by linarith [ht.2, hδ₁]⟩
          simp only [hf0, hbi0, sub_zero] at h'
          exact (abs_lt.mp h').2
      · intro t ht
        refine outside_of t (Or.inl ?_)
        have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
        simp only [hf0, hbi0] at h'
        exact h'
    · -- `b i = 1`: the curve enters on the positive side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inl ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨by linarith [ht.1, lt_min hδ₁ hδ₂pos], ht.2⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP3 t ⟨by linarith [ht.1, hδ₁], by linarith [ht.2, min_le_left δ₁ δ₂]⟩
          simp only [hf0, hbi1] at h'
          have := (abs_lt.mp h').1
          linarith
        · have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
          simp only [hf0, hbi1] at h'
          exact h'
      · intro t ht
        refine outside_of t (Or.inr ?_)
        have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
        simp only [hf0, hbi1] at h'
        exact h'
  · -- the `i`-th component of the field at `b` is positive
    obtain ⟨δ₁, hδ₁, hP1, hP2, hP3⟩ := scalar_pos hderiv hc
    have hoth : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → ∀ j, j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
      intro t ht j hj
      refine hδ₂ ?_ j hj
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂], by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have inside_of : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → γ t i ∈ Ioo (0:ℝ) 1 →
        γ t ∈ interior (Submission.Drive.unitBox m) := by
      intro t ht hti
      rw [interior_unitBox m]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · exact hti
      · exact hoth t ht j hj
    have outside_of : ∀ t, (γ t i < 0 ∨ 1 < γ t i) → γ t ∉ Submission.Drive.unitBox m := by
      intro t h hmem
      have hmem' : γ t i ∈ Set.Icc (0:ℝ) 1 := hmem i
      rcases h with h | h
      · linarith [hmem'.1]
      · linarith [hmem'.2]
    rcases hface.1 with hbi0 | hbi1
    · -- `b i = 0`: the curve enters on the positive side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inl ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨by linarith [ht.1, lt_min hδ₁ hδ₂pos], ht.2⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
          simp only [hf0, hbi0] at h'
          exact h'
        · have h' := hP3 t ⟨by linarith [ht.1, hδ₁], by linarith [ht.2, min_le_left δ₁ δ₂]⟩
          simp only [hf0, hbi0, sub_zero] at h'
          exact (abs_lt.mp h').2
      · intro t ht
        refine outside_of t (Or.inl ?_)
        have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
        simp only [hf0, hbi0] at h'
        exact h'
    · -- `b i = 1`: the curve enters on the negative side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inr ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨ht.1, by linarith [ht.2, lt_min hδ₁ hδ₂pos]⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP3 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], by linarith [ht.2, hδ₁]⟩
          simp only [hf0, hbi1] at h'
          have := (abs_lt.mp h').1
          linarith
        · have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
          simp only [hf0, hbi1] at h'
          exact h'
      · intro t ht
        refine outside_of t (Or.inr ?_)
        have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
        simp only [hf0, hbi1] at h'
        exact h'

end

end Work.Drive
