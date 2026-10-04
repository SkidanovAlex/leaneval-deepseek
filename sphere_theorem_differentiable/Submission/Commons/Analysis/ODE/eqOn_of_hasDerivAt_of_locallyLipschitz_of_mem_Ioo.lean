import Mathlib
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set Metric Filter
open scoped Topology

/-- **One-sided local uniqueness to the left** for `x' = f x`: if `f` is Lipschitz on a
neighbourhood of `u t` and `u t = v t`, then `u = v` on a small interval `Icc (t - δ) t` to the
left of `t`. This is the mirror image of `local_unique_right`. -/
private lemma local_unique_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {u v : ℝ → E} {a b : ℝ}
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ K : NNReal, ∃ U ∈ nhds (u t), LipschitzOnWith K f U)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (hut : u t = v t) (hlt : a < t) :
    ∃ δ > 0, δ ≤ t - a ∧ Set.EqOn u v (Set.Icc (t - δ) t) := by
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
  have hta : 0 < t - a := sub_pos.mpr hlt
  set δ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) ((t - a) / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (half_pos hδ₁) (half_pos hδ₂)) (half_pos hta)
  have hδlt₁ : δ < δ₁ := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((t - a) / 2) ≤ min (δ₁ / 2) (δ₂ / 2) := min_le_left _ _
      _ ≤ δ₁ / 2 := min_le_left _ _
      _ < δ₁ := half_lt_self hδ₁
  have hδlt₂ : δ < δ₂ := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((t - a) / 2) ≤ min (δ₁ / 2) (δ₂ / 2) := min_le_left _ _
      _ ≤ δ₂ / 2 := min_le_right _ _
      _ < δ₂ := half_lt_self hδ₂
  have hδa : δ ≤ t - a := by
    rw [hδdef]
    calc min (min (δ₁ / 2) (δ₂ / 2)) ((t - a) / 2) ≤ (t - a) / 2 := min_le_right _ _
      _ ≤ t - a := half_le_self hta.le
  have hrU' : ball (v t) r ⊆ U := by rw [← hut]; exact hrU
  refine ⟨δ, hδpos, hδa, ?_⟩
  have hsub : Set.Icc (t - δ) t ⊆ Set.Icc a b := fun x hx =>
    ⟨by linarith [hx.1, hδa], le_trans hx.2 ht.2⟩
  have huU : ∀ x ∈ Set.Icc (t - δ) t, u x ∈ U := by
    intro x hx
    apply hrU
    apply hδ₁'
    rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub]
    calc t - x ≤ δ := by linarith [hx.1]
      _ < δ₁ := hδlt₁
  have hvU : ∀ x ∈ Set.Icc (t - δ) t, v x ∈ U := by
    intro x hx
    apply hrU'
    apply hδ₂'
    rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub]
    calc t - x ≤ δ := by linarith [hx.1]
      _ < δ₂ := hδlt₂
  exact ODE_solution_unique_of_mem_Icc_left (v := fun _ x => f x) (s := fun _ => U)
    (K := K) (f := u) (g := v) (a := t - δ) (b := t)
    (fun x _ => hLip)
    (fun x hx => ((hu x (hsub hx)).continuousAt).continuousWithinAt)
    (fun x hx => (hu x (hsub (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x hx => huU x (Ioc_subset_Icc_self hx))
    (fun x hx => ((hv x (hsub hx)).continuousAt).continuousWithinAt)
    (fun x hx => (hv x (hsub (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x hx => hvU x (Ioc_subset_Icc_self hx))
    hut

/-- **Uniqueness of solutions of `x' = f x` for a locally Lipschitz field**, initial condition at
the *right* endpoint `b`.  This is the mirror image of
`eqOn_of_hasDerivAt_of_locallyLipschitz`. -/
theorem eqOn_of_hasDerivAt_of_locallyLipschitz_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {u v : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ K : NNReal, ∃ U ∈ nhds (u t), LipschitzOnWith K f U)
    (h0 : u b = v b) : Set.EqOn u v (Set.Icc a b) := by
  -- `B` is the set of left endpoints from which `u` and `v` are known to agree up to `b`.
  let B : Set ℝ := {t | t ∈ Set.Icc a b ∧ Set.EqOn u v (Set.Icc t b)}
  have hbB : b ∈ B := by
    refine ⟨⟨hab, le_rfl⟩, ?_⟩
    intro x hx
    have hx' : x = b := le_antisymm hx.2 hx.1
    rw [hx', h0]
  have hBne : B.Nonempty := ⟨b, hbB⟩
  have hBbdd : BddBelow B := ⟨a, fun t ht => ht.1.1⟩
  have hsinf_le : sInf B ≤ b := csInf_le hBbdd hbB
  have ha_le_sinf : a ≤ sInf B := le_csInf hBne (fun t ht => ht.1.1)
  -- `sInf B` itself belongs to `B`, by continuity at the endpoint.
  have hcB : sInf B ∈ B := by
    refine ⟨⟨ha_le_sinf, hsinf_le⟩, ?_⟩
    rcases eq_or_lt_of_le hsinf_le with hcb | hcb
    · rw [hcb]
      intro x hx
      have hx' : x = b := le_antisymm hx.2 hx.1
      rw [hx', h0]
    · have hcont_u : ContinuousOn u (Set.Icc (sInf B) b) :=
        fun x hx => ((hu x ⟨le_trans ha_le_sinf hx.1, hx.2⟩).continuousAt).continuousWithinAt
      have hcont_v : ContinuousOn v (Set.Icc (sInf B) b) :=
        fun x hx => ((hv x ⟨le_trans ha_le_sinf hx.1, hx.2⟩).continuousAt).continuousWithinAt
      refine Set.EqOn.of_subset_closure ?_ hcont_u hcont_v Ioc_subset_Icc_self
        (fun x hx => by rw [closure_Ioc (ne_of_lt hcb)]; exact hx)
      intro x hx
      obtain ⟨y, hyB, hyx⟩ := (csInf_lt_iff hBbdd hBne).mp hx.1
      exact hyB.2 ⟨le_of_lt hyx, hx.2⟩
  -- If `a < sInf B` one could extend the agreement to the left, contradicting the infimum.
  have hsinf : sInf B = a := by
    by_contra hne
    have hlt : a < sInf B := lt_of_le_of_ne ha_le_sinf (Ne.symm hne)
    have huc : u (sInf B) = v (sInf B) := hcB.2 ⟨le_rfl, hsinf_le⟩
    obtain ⟨δ, hδpos, hδle, heq⟩ := local_unique_left hu hv hloc hcB.1 huc hlt
    have hmem : sInf B - δ ∈ B := by
      refine ⟨⟨by linarith [hδle], by linarith [hδpos, hsinf_le]⟩, ?_⟩
      have h := Set.EqOn.union heq hcB.2
      rwa [Icc_union_Icc_eq_Icc (show sInf B - δ ≤ sInf B by linarith [hδpos]) hsinf_le] at h
    have : sInf B ≤ sInf B - δ := csInf_le hBbdd hmem
    linarith [hδpos]
  rw [hsinf] at hcB
  exact hcB.2

theorem eqOn_of_hasDerivAt_of_locallyLipschitz_of_mem_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {u v : ℝ → E} {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ K : NNReal, ∃ U ∈ nhds (u t), LipschitzOnWith K f U)
    (h0 : u t₀ = v t₀) : Set.EqOn u v (Set.Icc a b) := by
  have hta : a ≤ t₀ := le_of_lt ht₀.1
  have htb : t₀ ≤ b := le_of_lt ht₀.2
  -- Agreement to the right of `t₀`: the left-endpoint uniqueness theorem on `Icc t₀ b`.
  have hforward : Set.EqOn u v (Set.Icc t₀ b) :=
    eqOn_of_hasDerivAt_of_locallyLipschitz (le_of_lt ht₀.2)
      (fun t ht => hu t ⟨le_trans hta ht.1, ht.2⟩)
      (fun t ht => hv t ⟨le_trans hta ht.1, ht.2⟩)
      (fun t ht => hloc t ⟨le_trans hta ht.1, ht.2⟩)
      h0
  -- Agreement to the left of `t₀`: the right-endpoint uniqueness theorem on `Icc a t₀`.
  have hbackward : Set.EqOn u v (Set.Icc a t₀) :=
    eqOn_of_hasDerivAt_of_locallyLipschitz_right (le_of_lt ht₀.1)
      (fun t ht => hu t ⟨ht.1, le_trans ht.2 htb⟩)
      (fun t ht => hv t ⟨ht.1, le_trans ht.2 htb⟩)
      (fun t ht => hloc t ⟨ht.1, le_trans ht.2 htb⟩)
      h0
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hbackward ⟨ht.1, h⟩
  · exact hforward ⟨h, ht.2⟩

end Commons.Analysis.ODE
