import Mathlib.Analysis.ODE.ExistUnique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set Metric Filter
open scoped Topology

/-- **One-sided local uniqueness** for `x' = f x`: if `f` is Lipschitz on a neighbourhood of
`u t` and `u t = v t`, then `u = v` on a small interval `Icc t (t + δ)` to the right of `t`.
This is the local ingredient of the global uniqueness statement. -/
private lemma local_unique_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {u v : ℝ → E} {a b : ℝ}
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ K : NNReal, ∃ U ∈ nhds (u t), LipschitzOnWith K f U)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (hut : u t = v t) (hlt : t < b) :
    ∃ δ > 0, δ ≤ b - t ∧ Set.EqOn u v (Set.Icc t (t + δ)) := by
  obtain ⟨K, U, hU, hLip⟩ := hloc t ht
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hcu : ContinuousAt u t := (hu t ht).continuousAt
  have hcv : ContinuousAt v t := (hv t ht).continuousAt
  have h1 : {s | u s ∈ ball (u t) r} ∈ 𝓝 t :=
    hcu.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  have h2 : {s | v s ∈ ball (v t) r} ∈ 𝓝 t :=
    hcv.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.mem_nhds_iff.mp h1
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.mem_nhds_iff.mp h2
  have hbt : 0 < b - t := sub_pos.mpr hlt
  set δ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) ((b - t) / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (half_pos hδ₁) (half_pos hδ₂)) (half_pos hbt)
  have hδlt₁ : δ < δ₁ := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((b - t) / 2) ≤ min (δ₁ / 2) (δ₂ / 2) := min_le_left _ _
      _ ≤ δ₁ / 2 := min_le_left _ _
      _ < δ₁ := half_lt_self hδ₁
  have hδlt₂ : δ < δ₂ := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((b - t) / 2) ≤ min (δ₁ / 2) (δ₂ / 2) := min_le_left _ _
      _ ≤ δ₂ / 2 := min_le_right _ _
      _ < δ₂ := half_lt_self hδ₂
  have hδb : δ ≤ b - t := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((b - t) / 2) ≤ (b - t) / 2 := min_le_right _ _
      _ ≤ b - t := half_le_self hbt.le
  have hrU' : ball (v t) r ⊆ U := by rw [← hut]; exact hrU
  refine ⟨δ, hδpos, hδb, ?_⟩
  have hsub : Set.Icc t (t + δ) ⊆ Set.Icc a b := fun x hx =>
    ⟨le_trans ht.1 hx.1, le_trans hx.2 (by linarith [hδb])⟩
  have huU : ∀ x ∈ Set.Icc t (t + δ), u x ∈ U := by
    intro x hx
    apply hrU
    apply hδ₁'
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    calc x - t ≤ δ := by linarith [hx.2]
      _ < δ₁ := hδlt₁
  have hvU : ∀ x ∈ Set.Icc t (t + δ), v x ∈ U := by
    intro x hx
    apply hrU'
    apply hδ₂'
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    calc x - t ≤ δ := by linarith [hx.2]
      _ < δ₂ := hδlt₂
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ x => f x) (s := fun _ => U)
    (K := K) (f := u) (g := v) (a := t) (b := t + δ)
    (fun x _ => hLip)
    (fun x hx => ((hu x (hsub hx)).continuousAt).continuousWithinAt)
    (fun x hx => (hu x (hsub (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x hx => huU x (Ico_subset_Icc_self hx))
    (fun x hx => ((hv x (hsub hx)).continuousAt).continuousWithinAt)
    (fun x hx => (hv x (hsub (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x hx => hvU x (Ico_subset_Icc_self hx))
    hut

/-- **Uniqueness of solutions of `x' = f x` for a locally Lipschitz field.**  Two solutions on
`Icc a b` with the same initial value at `a` agree on the whole interval, provided `f` is locally
Lipschitz at every point of one of the trajectories (for instance if that trajectory avoids the
singular set of `f`). -/
theorem eqOn_of_hasDerivAt_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {u v : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ K : NNReal, ∃ U ∈ nhds (u t), LipschitzOnWith K f U)
    (h0 : u a = v a) : Set.EqOn u v (Set.Icc a b) := by
  -- `A` is the set of right endpoints up to which `u` and `v` are known to agree on a prefix.
  let A : Set ℝ := {t | t ∈ Set.Icc a b ∧ Set.EqOn u v (Set.Icc a t)}
  have haA : a ∈ A := by
    refine ⟨⟨le_rfl, hab⟩, ?_⟩
    intro x hx
    have hx' : x = a := le_antisymm hx.2 hx.1
    rw [hx', h0]
  have hAne : A.Nonempty := ⟨a, haA⟩
  have hAbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  have hcsSup_le : sSup A ≤ b := csSup_le hAne (fun t ht => ht.1.2)
  have ha_le_c : a ≤ sSup A := le_csSup hAbdd haA
  -- `sSup A` itself belongs to `A`, by continuity at the endpoint.
  have hcA : sSup A ∈ A := by
    refine ⟨⟨ha_le_c, hcsSup_le⟩, ?_⟩
    rcases eq_or_lt_of_le ha_le_c with hca | hac
    · rw [← hca]
      intro x hx
      have hx' : x = a := le_antisymm hx.2 hx.1
      rw [hx', h0]
    · have hcont_u : ContinuousOn u (Set.Icc a (sSup A)) :=
        fun x hx => ((hu x ⟨hx.1, le_trans hx.2 hcsSup_le⟩).continuousAt).continuousWithinAt
      have hcont_v : ContinuousOn v (Set.Icc a (sSup A)) :=
        fun x hx => ((hv x ⟨hx.1, le_trans hx.2 hcsSup_le⟩).continuousAt).continuousWithinAt
      refine Set.EqOn.of_subset_closure ?_ hcont_u hcont_v Ico_subset_Icc_self
        (fun x hx => by rw [closure_Ico (ne_of_lt hac)]; exact hx)
      intro x hx
      obtain ⟨y, hyA, hxy⟩ := (lt_csSup_iff hAbdd hAne).mp hx.2
      exact hyA.2 ⟨hx.1, le_of_lt hxy⟩
  -- If `sSup A < b` one could extend the agreement to the right, contradicting the supremum.
  have hcb : sSup A = b := by
    by_contra hne
    have hlt : sSup A < b := lt_of_le_of_ne hcsSup_le hne
    have huc : u (sSup A) = v (sSup A) := hcA.2 ⟨ha_le_c, le_rfl⟩
    obtain ⟨δ, hδpos, hδle, heq⟩ := local_unique_right hu hv hloc hcA.1 huc hlt
    have hmem : sSup A + δ ∈ A := by
      refine ⟨⟨le_trans ha_le_c (le_add_of_nonneg_right hδpos.le), by linarith⟩, ?_⟩
      have h := Set.EqOn.union hcA.2 heq
      rwa [Icc_union_Icc_eq_Icc ha_le_c (le_add_of_nonneg_right hδpos.le)] at h
    have : sSup A + δ ≤ sSup A := le_csSup hAbdd hmem
    linarith
  rw [hcb] at hcA
  exact hcA.2

end Commons.Analysis.ODE