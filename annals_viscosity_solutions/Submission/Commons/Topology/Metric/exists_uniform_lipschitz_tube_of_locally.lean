import Mathlib.Analysis.Normed.Module.Basic

open Set Metric Filter

namespace Commons.Topology.Metric

/-- **A uniform Lipschitz tube along a compact curve.**  If `f` is locally Lipschitz at every point
of the image of a continuous curve `u : ℝ → E` on the compact interval `Icc a b`, then there are a
radius `r > 0` and a constant `K` such that `f` is `K`-Lipschitz on the ball of radius `r` around
`u t`, uniformly in `t ∈ Icc a b`. -/
theorem exists_uniform_lipschitz_tube_of_locally
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {u : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hloc : ∀ x ∈ Set.image u (Set.Icc a b), ∃ K : NNReal, ∃ U ∈ nhds x, LipschitzOnWith K f U) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : NNReal, ∀ t ∈ Set.Icc a b, ∀ x y : E,
      dist x (u t) ≤ r → dist y (u t) ≤ r → dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
  classical
  set S : Set E := Set.image u (Set.Icc a b) with hSdef
  have hScomp : IsCompact S := by
    rw [hSdef]; exact isCompact_Icc.image_of_continuousOn hcont
  have hlocS : ∀ x ∈ S, ∃ K : NNReal, ∃ U ∈ nhds x, LipschitzOnWith K f U := by
    intro x hx; rw [hSdef] at hx; exact hloc x hx
  -- choose, for each `y : S`, a Lipschitz constant and a neighbourhood
  let Kf : S → NNReal := fun y => (hlocS y.1 y.2).choose
  let Uf : S → Set E := fun y => (hlocS y.1 y.2).choose_spec.choose
  have hUf_mem : ∀ y : S, Uf y ∈ nhds y.1 :=
    fun y => (hlocS y.1 y.2).choose_spec.choose_spec.1
  have hUf_lip : ∀ y : S, LipschitzOnWith (Kf y) f (Uf y) :=
    fun y => (hlocS y.1 y.2).choose_spec.choose_spec.2
  -- upgrade each neighbourhood to a ball
  have hδ : ∀ y : S, ∃ δ : ℝ, 0 < δ ∧ Metric.ball y.1 δ ⊆ Uf y :=
    fun y => Metric.mem_nhds_iff.mp (hUf_mem y)
  let δ : S → ℝ := fun y => (hδ y).choose
  have hδpos : ∀ y : S, 0 < δ y := fun y => (hδ y).choose_spec.1
  have hδsub : ∀ y : S, Metric.ball y.1 (δ y) ⊆ Uf y := fun y => (hδ y).choose_spec.2
  -- the halved balls cover `S`
  have hcover : S ⊆ ⋃ y : S, Metric.ball y.1 (δ y / 2) := by
    intro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    linarith [hδpos ⟨z, hz⟩]
  obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover (fun y : S => Metric.ball y.1 (δ y / 2))
    (fun _ => Metric.isOpen_ball) hcover
  have haS : u a ∈ S := by
    rw [hSdef]; exact ⟨a, ⟨le_refl a, hab⟩, rfl⟩
  have htne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (ht haS)
    exact ⟨i, hi⟩
  -- uniform radius and uniform constant
  let r : ℝ := t.inf' htne (fun y => δ y / 2)
  have hrle : ∀ y ∈ t, r ≤ δ y / 2 := fun y hy => Finset.inf'_le (fun y : S => δ y / 2) hy
  have hrpos : 0 < r := by
    obtain ⟨i, _, hieq⟩ := Finset.exists_mem_eq_inf' htne (fun y : S => δ y / 2)
    have : r = δ i / 2 := hieq
    rw [this]
    linarith [hδpos i]
  let K : NNReal := t.sup Kf
  have hKle : ∀ y ∈ t, Kf y ≤ K := fun y hy => Finset.le_sup hy
  refine ⟨r, hrpos, K, ?_⟩
  intro t' ht' x y hx hy
  have hutS : u t' ∈ S := by rw [hSdef]; exact ⟨t', ht', rfl⟩
  obtain ⟨i, hit, hui⟩ := mem_iUnion₂.mp (ht hutS)
  have hui' : dist (u t') i.1 < δ i / 2 := by
    rwa [Metric.mem_ball] at hui
  have hri : r ≤ δ i / 2 := hrle i hit
  have hxi : x ∈ Uf i := by
    apply hδsub i
    rw [Metric.mem_ball]
    have htri := dist_triangle x (u t') i.1
    linarith
  have hyi : y ∈ Uf i := by
    apply hδsub i
    rw [Metric.mem_ball]
    have htri := dist_triangle y (u t') i.1
    linarith
  calc dist (f x) (f y) ≤ (Kf i : ℝ) * dist x y := (hUf_lip i).dist_le_mul x hxi y hyi
    _ ≤ (K : ℝ) * dist x y := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        exact_mod_cast hKle i hit

end Commons.Topology.Metric