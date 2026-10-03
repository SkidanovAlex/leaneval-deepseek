import Mathlib
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs

/-!
# `X ∖ K` is preconnected for a closed discrete `K`

A connected complex one-manifold minus a *closed discrete* set is preconnected.  This generalises
`Work.Modulus.isPreconnected_compl_singleton_of_isOpen_nhds` (the one-point case, which it uses
indirectly through `Work.Modulus.isPreconnected_ball_diff_center`) from one removed point to an
arbitrary closed discrete set; it is what a maximum-principle argument on `X` minus the zero set of
a holomorphic function needs.

## Proof

Let `A := Kᶜ ∩ u`, `B := Kᶜ ∩ v` be the two pieces of a hypothetical separation of `Kᶜ` into opens.
Then `A`, `B` are open, disjoint, nonempty and `A ∪ B = Kᶜ`.

* `closure A ⊆ A ∪ K` and `closure B ⊆ B ∪ K` (a closure point of `A` outside `A` cannot lie in
  the open set `B`, since `A ∩ B = ∅`).
* For `p ∈ K` there is an open `V ∋ p` with `V ∩ K = {p}` such that `V ∖ {p}` is preconnected
  (`p` isolated inside `K`, and a punctured chart disc is preconnected) and `p ∈ closure (V ∖ {p})`
  (the chart ball contains points different from `p`).  Since `V ∖ {p} ⊆ Kᶜ = A ∪ B` and is
  preconnected, it lies in `A` or in `B` (`IsPreconnected.subset_or_subset`); the side containing it
  contains `p` in its closure, while `p` lies in the closure of the other side only if `V` meets that
  side, which would force `A ∩ B ≠ ∅`.
* Hence `closure A ∩ closure B = ∅`, while `closure A ∪ closure B = univ`; the two complements are
  therefore a separation of `univ`.
-/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Local model.**  For `p` in a closed discrete `K` there is an open `V ∋ p` with `V ∩ K = {p}`
whose punctured version `V ∖ {p}` is preconnected and has `p` in its closure. -/
theorem exists_punctured_chart_nbhd {K : Set X}
    (hKd : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ K = {x}) {p : X} (hp : p ∈ K) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ∩ K = {p} ∧
      IsPreconnected (V \ {p}) ∧ p ∈ closure (V \ {p}) := by
  classical
  obtain ⟨U, hUo, hpU, hUK⟩ := hKd p hp
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc
  have hpsrc : p ∈ c.source := mem_chart_source ℂ p
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (c p) ρ ⊆ c.target :=
    Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hpsrc))
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (c p) ρ ⊆ c.symm ⁻¹'U := by
    refine Metric.mem_nhds_iff.mp ((c.continuousAt_symm (c.map_source hpsrc)).preimage_mem_nhds ?_)
    exact hUo.mem_nhds (by simpa [hc] using hpU)
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; have h := lt_min hρ₁ hρ₂; positivity
  have hρle₁ : ρ ≤ ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hρle₂ : ρ ≤ ρ₂ := by rw [hρdef]; linarith [min_le_right ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hballtgt : Metric.ball (c p) ρ ⊆ c.target := (Metric.ball_subset_ball hρle₁).trans hρ₁sub
  set V : Set X := c.symm '' Metric.ball (c p) ρ with hVdef
  have hVopen : IsOpen V := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtgt
  have hpV : p ∈ V := ⟨c p, Metric.mem_ball_self hρpos, c.left_inv hpsrc⟩
  have hVU : V ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact hρ₂sub (Metric.ball_subset_ball hρle₂ hz)
  have hVK : V ∩ K = {p} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxV, hxK⟩
      have hx : x ∈ U ∩ K := ⟨hVU hxV, hxK⟩
      rw [hUK] at hx
      simpa using hx
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨hpV, hp⟩
  have himg : V \ {p} = c.symm '' (Metric.ball (c p) ρ \ {c p}) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxp⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      intro hzc
      exact hxp (by rw [hzc, c.left_inv hpsrc]; exact mem_singleton p)
    · rintro ⟨z, hzc, rfl⟩
      refine ⟨⟨z, hzc.1, rfl⟩, ?_⟩
      intro h
      have h2 : c (c.symm z) = c p := by rw [h]
      rw [c.right_inv (hballtgt hzc.1)] at h2
      exact hzc.2 h2
  have hVpc : IsPreconnected (V \ {p}) := by
    rw [himg]
    exact (Work.Modulus.isPreconnected_ball_diff_center (c := c p) hρpos).image _
      (c.continuousOn_symm.mono fun z hz => hballtgt hz.1)
  have hpcl : p ∈ closure (V \ {p}) := by
    rw [himg, mem_closure_iff_nhds]
    intro t ht
    have ht2 : t ∈ 𝓝 (c.symm (c p)) := by rw [c.left_inv hpsrc]; exact ht
    have hpre : c.symm ⁻¹' t ∈ 𝓝 (c p) :=
      (c.continuousAt_symm (c.map_source hpsrc)).preimage_mem_nhds ht2
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
    set s : ℝ := min δ ρ / 2 with hsdef
    have hsmin : 0 < min δ ρ := lt_min hδ hρpos
    have hspos : 0 < s := by rw [hsdef]; positivity
    have hsδ : s < δ := by rw [hsdef]; linarith [min_le_left δ ρ, hsmin]
    have hsρ : s < ρ := by rw [hsdef]; linarith [min_le_right δ ρ, hsmin]
    have hballδ : c p + (s : ℂ) ∈ Metric.ball (c p) δ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hspos]
      exact hsδ
    have hballρ : c p + (s : ℂ) ∈ Metric.ball (c p) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hspos]
      exact hsρ
    refine ⟨c.symm (c p + (s : ℂ)), hδsub hballδ, ⟨c p + (s : ℂ), ⟨hballρ, ?_⟩, rfl⟩⟩
    intro hcon
    have h3 : ((s : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w : ℂ => w - c p) hcon
      simpa using this
    have h4 : s = 0 := Complex.ofReal_eq_zero.mp h3
    linarith
  exact ⟨V, hVopen, hpV, hVK, hVpc, hpcl⟩

/-- **`X ∖ K` is preconnected for a closed discrete `K`.**  See the file header for the proof. -/
theorem isPreconnected_compl_closedDiscrete {K : Set X} (hKc : IsClosed K)
    (hKd : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ K = {x}) :
    IsPreconnected (Kᶜ) := by
  classical
  intro u v hu hv huv hune hvne
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  set A : Set X := Kᶜ ∩ u with hAdef
  set B : Set X := Kᶜ ∩ v with hBdef
  have hAopen : IsOpen A := hKc.isOpen_compl.inter hu
  have hBopen : IsOpen B := hKc.isOpen_compl.inter hv
  have hAne : A.Nonempty := hune
  have hBne : B.Nonempty := hvne
  have hAB : A ∪ B = Kᶜ := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      rcases huv hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hdisj : A ∩ B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxB⟩
    have h1 : x ∈ Kᶜ := hxA.1
    have h2 : x ∈ u := hxA.2
    have h3 : x ∈ v := hxB.2
    have hmem : x ∈ Kᶜ ∩ (u ∩ v) := ⟨h1, h2, h3⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hemp) x hmem
  have hclA : closure A ⊆ A ∪ K := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · refine Or.inr ?_
      by_contra hxK
      have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hxK
      rcases hxAB with h | h
      · exact hxA h
      · obtain ⟨y, hyB, hyA⟩ := (mem_closure_iff_nhds.mp hx) B (hBopen.mem_nhds h)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyA, hyB⟩
  have hclB : closure B ⊆ B ∪ K := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · refine Or.inr ?_
      by_contra hxK
      have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hxK
      rcases hxAB with h | h
      · obtain ⟨y, hyA, hyB⟩ := (mem_closure_iff_nhds.mp hx) A (hAopen.mem_nhds h)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyA, hyB⟩
      · exact hxB h
  -- the punctured local model at a point of `K` separates the two sides
  have hloc : ∀ p ∈ K, ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ∩ K = {p} ∧
      IsPreconnected (V \ {p}) ∧ p ∈ closure (V \ {p}) ∧ V \ {p} ⊆ A ∪ B := by
    intro p hp
    obtain ⟨V, hVo, hpV, hVK, hVpc, hpcl⟩ := exists_punctured_chart_nbhd hKd hp
    refine ⟨V, hVo, hpV, hVK, hVpc, hpcl, ?_⟩
    rintro y ⟨hyV, hyx⟩
    have hyK : y ∉ K := by
      intro hyK
      have hmem : y ∈ V ∩ K := ⟨hyV, hyK⟩
      rw [hVK] at hmem
      exact hyx (by simpa using hmem)
    rw [hAB]
    exact hyK
  have hdisjCl : closure A ∩ closure B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxB⟩
    by_cases hxK : x ∈ K
    · obtain ⟨V, hVo, hxV, hVK, hVpc, hxcl, hsub⟩ := hloc x hxK
      rcases hVpc.subset_or_subset hAopen hBopen
          (Set.disjoint_iff_inter_eq_empty.mpr hdisj) hsub with hsubA | hsubB
      · obtain ⟨y, hyV, hyB⟩ := (mem_closure_iff_nhds.mp hxB) V (hVo.mem_nhds hxV)
        have hyKc : y ∈ Kᶜ := by
          have h := hyB
          rw [hBdef] at h
          exact h.1
        have hyx : y ≠ x := by
          intro hxy
          exact hyKc (by rw [hxy]; exact hxK)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hsubA ⟨hyV, hyx⟩, hyB⟩
      · obtain ⟨y, hyV, hyA⟩ := (mem_closure_iff_nhds.mp hxA) V (hVo.mem_nhds hxV)
        have hyKc : y ∈ Kᶜ := by
          have h := hyA
          rw [hAdef] at h
          exact h.1
        have hyx : y ≠ x := by
          intro hxy
          exact hyKc (by rw [hxy]; exact hxK)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyA, hsubB ⟨hyV, hyx⟩⟩
    · have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hxK
      rcases hxAB with h | h
      · obtain ⟨y, hyA, hyB⟩ := (mem_closure_iff_nhds.mp hxB) A (hAopen.mem_nhds h)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyA, hyB⟩
      · obtain ⟨y, hyB, hyA⟩ := (mem_closure_iff_nhds.mp hxA) B (hBopen.mem_nhds h)
        exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyA, hyB⟩
  -- the two closed sets cover `X` and are disjoint: a separation
  have hcov : ∀ x : X, x ∈ closure A ∪ closure B := by
    intro x
    by_cases hxK : x ∈ K
    · obtain ⟨V, hVo, hxV, hVK, hVpc, hxcl, hsub⟩ := hloc x hxK
      rcases hVpc.subset_or_subset hAopen hBopen
          (Set.disjoint_iff_inter_eq_empty.mpr hdisj) hsub with h | h
      · exact Or.inl (closure_mono h hxcl)
      · exact Or.inr (closure_mono h hxcl)
    · have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hxK
      rcases hxAB with h | h
      · exact Or.inl (subset_closure h)
      · exact Or.inr (subset_closure h)
  have hclopenA : IsClopen (closure A) := by
    have hcompl : (closure A) = (closure B)ᶜ := by
      ext x
      constructor
      · intro hx
        exact fun hxB => (Set.eq_empty_iff_forall_notMem.mp hdisjCl) x ⟨hx, hxB⟩
      · intro hx
        rcases hcov x with h | h
        · exact h
        · exact absurd h hx
    exact ⟨isClosed_closure, by rw [hcompl]; exact isClosed_closure.isOpen_compl⟩
  have hpcu : IsPreconnected (univ : Set X) :=
    (connectedSpace_iff_univ.mp inferInstance).isPreconnected
  have hsub : (univ : Set X) ⊆ closure A :=
    hpcu.subset_isClopen hclopenA ⟨hAne.some, mem_univ _, subset_closure hAne.some_mem⟩
  obtain ⟨y, hyB⟩ := hBne
  have hyA : y ∈ closure A := hsub (mem_univ y)
  have hyBcl : y ∈ closure B := subset_closure hyB
  exact (Set.eq_empty_iff_forall_notMem.mp hdisjCl) y ⟨hyA, hyBcl⟩

end Work.SimplyConnected.ABS
