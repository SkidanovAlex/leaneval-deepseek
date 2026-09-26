import Mathlib

/-!
# Every component of one of two covering sets meets the intersection

Let `S = {a ≤ ·.2 ≤ b}` be a closed horizontal strip, `T q = (q.1 + p, q.2)`.  Let `W₁, W₂ ⊆ S`
be `T`-invariant and *open in* `S` (i.e. `Wᵢ = Uᵢ ∩ S` with `Uᵢ` open in `ℝ²`), with
`W₁ ∪ W₂ = S`.  If the intersection `W₁ ∩ W₂` carries **no** translate crossing and `W₂` **does**
carry one, then **every connected component of `W₁` meets `W₁ ∩ W₂`**.

This settles (and strengthens: no periodicity is needed) the residual recorded in
`Work/Topology/Strip/NOTES_meridian.md` and in `Work/Topology/Strip/annulus_essential_intersection.lean`
("under `hno`, every `T`-periodic component of `VA` meets `W = VA ∩ VB`").

Proof sketch: let `E` be a component of `W₁` with `E ∩ W₂ = ∅`.  Since `E ⊆ S` and `W₂` is open in
the strip, `closure E ∩ W₂ = ∅`; and a point of `closure E ∩ W₁` lies in `E` (the component is
maximal).  As `closure E ⊆ S = W₁ ∪ W₂`, this gives `closure E ⊆ E`, so `E` is closed in `ℝ²`.
On the other hand `E` is the trace on `S` of an open set (for `q ∈ E`, a ball `B` with
`B ∩ S ⊆ W₁` is available, and `B ∩ S` is convex, hence connected, so `B ∩ S ⊆ E`).  Thus `E` is
clopen in the connected strip `S`; as `E ≠ ∅` we get `E = S`, so `W₁ = S` and `W = W₂`, which
contradicts `hno` by `hne₂`.
-/

open Set

namespace Commons.Topology.Strip

/-- **Every component of `W₁` meets `W₁ ∩ W₂`.** -/
theorem component_meets_inter_of_no_translate_path {p a b : ℝ} (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hno : ∀ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ → ¬ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2))
    (hne₂ : ∃ z : ℝ × ℝ, z ∈ W₂ ∧ JoinedIn W₂ z (z.1 + p, z.2))
    {z : ℝ × ℝ} (hz : z ∈ W₁) :
    (connectedComponentIn W₁ z ∩ (W₁ ∩ W₂)).Nonempty := by
  classical
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hSdef
  obtain ⟨U₁, hU₁, hW₁⟩ := hopen₁
  obtain ⟨U₂, hU₂, hW₂⟩ := hopen₂
  have hW₁S : W₁ ⊆ S := by rw [hW₁, hSdef]; exact Set.inter_subset_right
  have hW₂S : W₂ ⊆ S := by rw [hW₂, hSdef]; exact Set.inter_subset_right
  set E : Set (ℝ × ℝ) := connectedComponentIn W₁ z with hEdef
  have hzE : z ∈ E := mem_connectedComponentIn hz
  have hEpre : IsPreconnected E := hEdef ▸ isPreconnected_connectedComponentIn
  have hEW₁ : E ⊆ W₁ := fun q hq => connectedComponentIn_subset W₁ z (by rw [← hEdef]; exact hq)
  have hES : E ⊆ S := fun q hq => hW₁S (hEW₁ hq)
  have hEW₂ : E ∩ W₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqE, hqW₂⟩
    exact hcon q ⟨hqE, hEW₁ hqE, hqW₂⟩
  have hclW₂ : closure E ∩ W₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqcl, hqW₂⟩
    have hqU₂ : q ∈ U₂ := by rw [hW₂] at hqW₂; exact hqW₂.1
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU₂ q hqU₂
    obtain ⟨x, hxB, hxE⟩ :=
      mem_closure_iff.mp hqcl (Metric.ball q ε) Metric.isOpen_ball (Metric.mem_ball_self hεpos)
    have hxS : x ∈ S := hES hxE
    have hxW₂ : x ∈ W₂ := by rw [hW₂]; exact ⟨hε hxB, hxS⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hEW₂) x ⟨hxE, hxW₂⟩
  have hcomp : closure E ∩ W₁ ⊆ E := by
    rintro q ⟨hqcl, hqW₁⟩
    have hpre : IsPreconnected (E ∪ {q}) := by
      refine hEpre.subset_closure (fun x hx => Or.inl hx) ?_
      intro x hx
      rcases hx with h | rfl
      · exact subset_closure h
      · exact hqcl
    have hsub : E ∪ {q} ⊆ W₁ := by
      rintro x (hx | rfl)
      · exact hEW₁ hx
      · exact hqW₁
    exact hpre.subset_connectedComponentIn (Or.inl hzE) hsub (Or.inr rfl)
  have hSclosed : IsClosed S := by
    rw [hSdef]
    have h1 : {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} =
        {q : ℝ × ℝ | a ≤ q.2} ∩ {q : ℝ × ℝ | q.2 ≤ b} := by
      ext q; exact Iff.rfl
    rw [h1]
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)
  have hEclosed : IsClosed E := by
    refine closure_subset_iff_isClosed.mp ?_
    intro q hqcl
    have hclS : closure E ⊆ S := closure_minimal hES hSclosed
    have hmem : q ∈ W₁ ∪ W₂ := by rw [hcov]; exact hclS hqcl
    rcases hmem with h | h
    · exact hcomp ⟨hqcl, h⟩
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hclW₂) q ⟨hqcl, h⟩
  have hSconv : Convex ℝ S := by
    rw [hSdef]
    have h1 : {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} = Set.univ ×ˢ Set.Icc a b := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc]
    rw [h1]; exact convex_univ.prod (convex_Icc a b)
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hEopen_trace : ∃ E₀ : Set (ℝ × ℝ), IsOpen E₀ ∧ E = E₀ ∩ S := by
    have h : ∀ q : ℝ × ℝ, q ∈ E → ∃ ε : ℝ, 0 < ε ∧ Metric.ball q ε ∩ S ⊆ E := by
      intro q hqE
      have hqW₁ : q ∈ W₁ := hEW₁ hqE
      have hqU₁ : q ∈ U₁ := by rw [hW₁] at hqW₁; exact hqW₁.1
      obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU₁ q hqU₁
      refine ⟨ε, hεpos, ?_⟩
      have hconv : Convex ℝ (Metric.ball q ε ∩ S) := (convex_ball q ε).inter hSconv
      have hpre : IsPreconnected (Metric.ball q ε ∩ S) := hconv.isPreconnected
      have hsub : Metric.ball q ε ∩ S ⊆ W₁ := by
        rintro x ⟨hx, hxS⟩; rw [hW₁]; exact ⟨hε hx, hxS⟩
      have hmem : q ∈ Metric.ball q ε ∩ S := ⟨Metric.mem_ball_self hεpos, hES hqE⟩
      have hb : Metric.ball q ε ∩ S ⊆ connectedComponentIn W₁ q :=
        hpre.subset_connectedComponentIn hmem hsub
      have hEq : connectedComponentIn W₁ q = E := by
        rw [hEdef]
        exact (connectedComponentIn_eq (by rw [← hEdef]; exact hqE)).symm
      rwa [hEq] at hb
    have h2 : ∀ q : ℝ × ℝ, ∃ ε : ℝ, q ∈ E → 0 < ε ∧ Metric.ball q ε ∩ S ⊆ E := by
      intro q
      by_cases hq : q ∈ E
      · obtain ⟨ε, h1, h2⟩ := h q hq
        exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨1, fun hq' => absurd hq' hq⟩
    choose ε hε using h2
    refine ⟨{x : ℝ × ℝ | (∃ q : ℝ × ℝ, q ∈ E ∧ x ∈ Metric.ball q (ε q))} ∪ Sᶜ, ?_, ?_⟩
    · have hu : IsOpen {x : ℝ × ℝ | ∃ q : ℝ × ℝ, q ∈ E ∧ x ∈ Metric.ball q (ε q)} := by
        rw [isOpen_iff_mem_nhds]
        rintro x ⟨q, hqE, hxq⟩
        exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxq) (fun y hy => ⟨q, hqE, hy⟩)
      exact hu.union hSclosed.isOpen_compl
    · ext x
      constructor
      · intro hx
        exact ⟨Or.inl ⟨x, hx, Metric.mem_ball_self (hε x hx).1⟩, hES hx⟩
      · rintro ⟨hx | hx, hxS⟩
        · obtain ⟨q, hqE, hqx⟩ := hx
          exact (hε q hqE).2 ⟨hqx, hxS⟩
        · exact absurd hxS hx
  obtain ⟨E₀, hE₀open, hE₀eq⟩ := hEopen_trace
  have hES_eq : E = S := by
    have hcover : S ⊆ E₀ ∪ Eᶜ := by
      intro q hq
      by_cases h : q ∈ E₀
      · exact Or.inl h
      · refine Or.inr (fun hqE => h ?_)
        rw [hE₀eq] at hqE
        exact hqE.1
    have htri : S ∩ (E₀ ∩ Eᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨hqS, hqE₀, hqEc⟩
      have hqE : q ∈ E := by rw [hE₀eq]; exact ⟨hqE₀, hqS⟩
      exact hqEc hqE
    have hzE₀ : z ∈ E₀ := by
      have h : z ∈ E₀ ∩ S := hE₀eq.le hzE
      exact h.1
    have h1 : (S ∩ E₀).Nonempty := ⟨z, hES hzE, hzE₀⟩
    have hfin : S ∩ Eᶜ = ∅ := by
      by_contra hne
      have hne' : (S ∩ Eᶜ).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨q, hq⟩ := hSpre E₀ Eᶜ hE₀open hEclosed.isOpen_compl hcover h1 hne'
      exact (Set.eq_empty_iff_forall_notMem.mp htri) q hq
    refine Subset.antisymm hES ?_
    intro q hq
    by_contra hqE
    exact (Set.eq_empty_iff_forall_notMem.mp hfin) q ⟨hq, hqE⟩
  have hW₁S_eq : W₁ = S := Subset.antisymm hW₁S (by rw [← hES_eq]; exact hEW₁)
  obtain ⟨z₀, hz₀W₂, hJ⟩ := hne₂
  have hz₀W₁ : z₀ ∈ W₁ := by rw [hW₁S_eq]; exact hW₂S hz₀W₂
  have hJ' : JoinedIn (W₁ ∩ W₂) z₀ (z₀.1 + p, z₀.2) := by
    rw [hW₁S_eq, Set.inter_eq_right.mpr hW₂S]
    exact hJ
  exact hno z₀ ⟨hz₀W₁, hz₀W₂⟩ hJ'

end Commons.Topology.Strip
