import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLRelCross.exists_shrink_nhds

namespace Work.EKLRelCross.FlowerLocalAux

open Filter Topology

set_option linter.style.haveILetI false

/-- For a closed subgroup `U ≤ SL₃(ℝ)`, a real `R` and a compact set `F ⊆ X₃`, the set of pairs
`(u, u') ∈ Ucl U R × Ucl U R` which identify a *common* point of `F` is closed in
`SL₃(ℝ) × SL₃(ℝ)`.

This is the one-point analogue of `Work.EKLRelCross.isClosed_RetPair`: the set in question is the
image of the closed subset `{q : (SL₃ × SL₃) × X₃ | q.1.1 ∈ Ucl U R ∧ q.1.2 ∈ Ucl U R ∧ q.2 ∈ F ∧
q.1.1 • q.2 = q.1.2 • q.2}` of the compact set `(Ucl U R × Ucl U R) × F` under the continuous
projection to the first factor. -/
lemma isClosed_retSet {U : Subgroup Work.EKLContract.SL3}
    (hU : IsClosed (U : Set Work.EKLContract.SL3))
    (R : ℝ) {F : Set Work.EKLContract.X3} (hF : IsCompact F) :
    IsClosed (((Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R)) ∩
      {p : Work.EKLContract.SL3 × Work.EKLContract.SL3 |
        ∃ x ∈ F, p.1 • x = p.2 • x}) := by
  have hKc : IsCompact (Work.EKLRelCross.Ucl U R) :=
    Work.EKLRelCross.isCompact_Ucl hU R
  have hQclosed : IsClosed
      {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
        q.1.1 ∈ Work.EKLRelCross.Ucl U R ∧ q.1.2 ∈ Work.EKLRelCross.Ucl U R ∧ q.2 ∈ F ∧
          q.1.1 • q.2 = q.1.2 • q.2} := by
    have h1 : IsClosed
        {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
          q.1.1 ∈ Work.EKLRelCross.Ucl U R} :=
      (Work.EKLRelCross.isClosed_Ucl hU R).preimage (by fun_prop)
    have h2 : IsClosed
        {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
          q.1.2 ∈ Work.EKLRelCross.Ucl U R} :=
      (Work.EKLRelCross.isClosed_Ucl hU R).preimage (by fun_prop)
    have h3 : IsClosed
        {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
          q.2 ∈ F} := hF.isClosed.preimage (by fun_prop)
    have h5 : IsClosed
        {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
          q.1.1 • q.2 = q.1.2 • q.2} := isClosed_eq (by fun_prop) (by fun_prop)
    have heq : {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
        q.1.1 ∈ Work.EKLRelCross.Ucl U R ∧ q.1.2 ∈ Work.EKLRelCross.Ucl U R ∧ q.2 ∈ F ∧
          q.1.1 • q.2 = q.1.2 • q.2}
        = {q | q.1.1 ∈ Work.EKLRelCross.Ucl U R} ∩ {q | q.1.2 ∈ Work.EKLRelCross.Ucl U R} ∩
          {q | q.2 ∈ F} ∩ {q | q.1.1 • q.2 = q.1.2 • q.2} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [heq]
    exact ((h1.inter h2).inter h3).inter h5
  have hQcpt : IsCompact
      {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
        q.1.1 ∈ Work.EKLRelCross.Ucl U R ∧ q.1.2 ∈ Work.EKLRelCross.Ucl U R ∧ q.2 ∈ F ∧
          q.1.1 • q.2 = q.1.2 • q.2} :=
    ((hKc.prod hKc).prod hF).of_isClosed_subset hQclosed (by
      rintro q ⟨hq1, hq2, hq3, hq4⟩
      exact ⟨⟨hq1, hq2⟩, hq3⟩)
  have himg : Prod.fst ''
      {q : (Work.EKLContract.SL3 × Work.EKLContract.SL3) × Work.EKLContract.X3 |
        q.1.1 ∈ Work.EKLRelCross.Ucl U R ∧ q.1.2 ∈ Work.EKLRelCross.Ucl U R ∧ q.2 ∈ F ∧
          q.1.1 • q.2 = q.1.2 • q.2}
      = ((Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R)) ∩
        {p : Work.EKLContract.SL3 × Work.EKLContract.SL3 |
          ∃ x ∈ F, p.1 • x = p.2 • x} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Set.mem_prod.mpr ⟨hq.1, hq.2.1⟩, q.2, hq.2.2.1, hq.2.2.2⟩
    · rintro ⟨hp1, x, hx, hpx⟩
      exact ⟨(p, x), ⟨(Set.mem_prod.mp hp1).1, (Set.mem_prod.mp hp1).2, hx, hpx⟩, rfl⟩
  rw [← himg]
  exact (hQcpt.image continuous_fst).isClosed

/-- If a pair `p = (u, u')` identifies a common point of every compact neighbourhood of `x₀`, then
it identifies `x₀` itself.  Indeed, if `u • x₀ ≠ u' • x₀` then the closed set
`{x | u • x = u' • x}` misses `x₀`, so (local compactness) some compact neighbourhood `F` of `x₀`
misses it, contradicting the hypothesis. -/
lemma eq_at_of_forall_exists_mem {x₀ : Work.EKLContract.X3}
    {p : Work.EKLContract.SL3 × Work.EKLContract.SL3}
    (h : ∀ F : Set Work.EKLContract.X3, IsCompact F → x₀ ∈ interior F →
      ∃ x ∈ F, p.1 • x = p.2 • x) :
    p.1 • x₀ = p.2 • x₀ := by
  by_contra hne
  have hZcl : IsClosed {x : Work.EKLContract.X3 | p.1 • x = p.2 • x} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hopen : IsOpen {x : Work.EKLContract.X3 | p.1 • x = p.2 • x}ᶜ := hZcl.isOpen_compl
  have hx₀ : x₀ ∈ {x : Work.EKLContract.X3 | p.1 • x = p.2 • x}ᶜ := hne
  obtain ⟨F, hFc, hFint, hFsub⟩ := exists_compact_subset hopen hx₀
  obtain ⟨x, hx, hpx⟩ := h F hFc hFint
  exact hFsub hx hpx

/-- **Pisa (Einsiedler–Lindenstrauss, "Diagonal actions...") §6.8, first half**: near a point
`x₀` with free `U`-orbit, the orbit map is injective on the closed displacement ball
`Ucl U R` of any fixed radius `R`.

`Ucl U R = {g ∈ U | |g i j - 1 i j| ≤ R}` is defined in `Work.EKLRelCross.LeafBasic`;
`Work.EKLRelCross.isCompact_Ucl` (in `Submission/Work/EKLRelCross/exists_shrink_nhds.lean`) says
`Ucl U R` is compact for closed `U`, and `Work.EKLComp.locallyFree_compacta K hK` gives `η > 0`
such that no non-identity element of `V η` fixes a point of the compact set `K`.

Proof sketch.  If the claim failed for every compact neighbourhood of `x₀`, there would be
`x_n → x₀` and `u_n ≠ u'_n ∈ Ucl U R` with `u_n • x_n = u'_n • x_n`.  Compactness of `Ucl U R`
gives a subsequence with `u_n → u`, `u'_n → u'`; continuity and `u_n • x_n = u'_n • x_n` give
`u • x₀ = u' • x₀`, so `u = u'` by freeness.  Then `s_n := u_n⁻¹ * u'_n ≠ 1` fixes `x_n` and
`s_n → 1`; the set `K := {x₀} ∪ range x_n` is compact (a convergent sequence with its limit), so
`locallyFree_compacta K hK` applies with `s_n ∈ V η` for large `n` — contradiction.

The proof below is the compactness form of this argument, avoiding sequences: with `η` supplied by
local freeness on a compact neighbourhood `K₀` of `x₀`, put
`W = {p : SL₃ × SL₃ | p.1⁻¹ * p.2 ∈ V η}`, an open neighbourhood of the diagonal, and let
`Pf F = {(u, u') ∈ Ucl U R × Ucl U R | ∃ x ∈ F, u • x = u' • x}` for compact neighbourhoods `F` of
`x₀` inside `K₀`.  The `Pf F` are closed, form a decreasing directed family, and `Pf F ∩ Wᶜ` shrinks
to the diagonal (freeness at `x₀`); the intersection of the whole family with the compact set
`(Ucl U R × Ucl U R) ∩ Wᶜ` is empty, so by the finite intersection property some single `F` has
`(Ucl U R × Ucl U R) ∩ Wᶜ ∩ Pf F = ∅`.  For that `F`, `u • x = u' • x` with `x ∈ F` forces
`u⁻¹ * u' ∈ V η`, and `u⁻¹ * u'` fixes `x ∈ K₀`, so `u⁻¹ * u' = 1` by local freeness. -/
theorem inj_nhds_local {U : Subgroup Work.EKLContract.SL3}
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) (x₀ : Work.EKLContract.X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) {R : ℝ} :
    ∃ E : Set Work.EKLContract.X3, IsCompact E ∧ x₀ ∈ interior E ∧
      ∀ x ∈ E, ∀ u ∈ Work.EKLRelCross.Ucl U R, ∀ u' ∈ Work.EKLRelCross.Ucl U R,
        u • x = u' • x → u = u' := by
  classical
  -- a compact neighbourhood `K₀` of `x₀` and the local-freeness radius on it
  obtain ⟨K₀, hK₀c, hK₀nhds⟩ := exists_compact_mem_nhds x₀
  have hK₀int : x₀ ∈ interior K₀ := mem_interior_iff_mem_nhds.mpr hK₀nhds
  obtain ⟨η, hηpos, hlocfree⟩ := Work.EKLComp.locallyFree_compacta K₀ hK₀c
  have hKc : IsCompact (Work.EKLRelCross.Ucl U R) := Work.EKLRelCross.isCompact_Ucl hU R
  -- the open neighbourhood of the diagonal consisting of displacements in `V η`
  let W : Set (Work.EKLContract.SL3 × Work.EKLContract.SL3) :=
    {p | p.1⁻¹ * p.2 ∈ Work.EKLContract.V η}
  have hWopen : IsOpen W := by
    have hc : Continuous (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 =>
        p.1⁻¹ * p.2) := by fun_prop
    exact (Work.EKLContract.Lemmas.V_open_one η hηpos).1.preimage hc
  have h1V : (1 : Work.EKLContract.SL3) ∈ Work.EKLContract.V η :=
    (Work.EKLContract.Lemmas.V_open_one η hηpos).2
  -- the directed family of compact neighbourhoods of `x₀` inside `K₀`
  let ι := {F : Set Work.EKLContract.X3 // IsCompact F ∧ x₀ ∈ interior F ∧ F ⊆ K₀}
  haveI hneι : Nonempty ι := ⟨⟨K₀, hK₀c, hK₀int, subset_rfl⟩⟩
  let Pf : ι → Set (Work.EKLContract.SL3 × Work.EKLContract.SL3) :=
    fun F => ((Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R)) ∩
      {p | ∃ x ∈ F.1, p.1 • x = p.2 • x}
  have hPf_closed : ∀ F : ι, IsClosed (Pf F) := fun F => isClosed_retSet hU R F.2.1
  have hmono : ∀ F₁ F₂ : ι, F₁.1 ⊆ F₂.1 → Pf F₁ ⊆ Pf F₂ := by
    rintro F₁ F₂ hsub p ⟨hpK, x, hx, hpx⟩
    exact ⟨hpK, x, hsub hx, hpx⟩
  have hdir : Directed (· ⊇ ·) Pf := by
    intro F₁ F₂
    refine ⟨⟨F₁.1 ∩ F₂.1, F₁.2.1.inter F₂.2.1, ?_, ?_⟩, ?_, ?_⟩
    · rw [interior_inter]; exact ⟨F₁.2.2.1, F₂.2.2.1⟩
    · exact fun y hy => F₁.2.2.2 hy.1
    · exact hmono _ _ Set.inter_subset_left
    · exact hmono _ _ Set.inter_subset_right
  -- the compact set on which the finite intersection property is applied
  have hsc : IsCompact
      (((Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R)) ∩ Wᶜ) :=
    (hKc.prod hKc).of_isClosed_subset
      ((hKc.prod hKc).isClosed.inter hWopen.isClosed_compl) Set.inter_subset_left
  -- the family of return pairs meets `Wᶜ` only in the diagonal, which is free
  have hst : (((Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R)) ∩ Wᶜ) ∩
      ⋂ F : ι, Pf F = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hpKW, hpAll⟩
    simp only [Set.mem_iInter] at hpAll
    have hpK : p ∈ (Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R) := hpKW.1
    have hpW : p ∉ W := hpKW.2
    have hp1 : p.1 ∈ Work.EKLRelCross.Ucl U R := (Set.mem_prod.mp hpK).1
    have hp2 : p.2 ∈ Work.EKLRelCross.Ucl U R := (Set.mem_prod.mp hpK).2
    have hx₀ : p.1 • x₀ = p.2 • x₀ := by
      refine eq_at_of_forall_exists_mem fun F hFc hFint => ?_
      have hx₀F : x₀ ∈ interior (F ∩ K₀) := by
        rw [interior_inter]; exact ⟨hFint, hK₀int⟩
      obtain ⟨-, x, hx, hpx⟩ :=
        hpAll ⟨F ∩ K₀, hFc.inter hK₀c, hx₀F, Set.inter_subset_right⟩
      exact ⟨x, hx.1, hpx⟩
    have hpq : p.1 = p.2 := hfree p.1 hp1.1 p.2 hp2.1 hx₀
    refine hpW ?_
    show p.1⁻¹ * p.2 ∈ Work.EKLContract.V η
    rw [hpq, inv_mul_cancel]
    exact h1V
  obtain ⟨F, hF⟩ := IsCompact.elim_directed_family_closed hsc Pf hPf_closed (Set.disjoint_iff_inter_eq_empty.mpr hst) hdir
  refine ⟨F.1, F.2.1, F.2.2.1, ?_⟩
  intro x hx u hu u' hu' hux
  have hpK : (u, u') ∈ (Work.EKLRelCross.Ucl U R) ×ˢ (Work.EKLRelCross.Ucl U R) :=
    Set.mem_prod.mpr ⟨hu, hu'⟩
  have hpPf : (u, u') ∈ Pf F := ⟨hpK, x, hx, hux⟩
  have hpW : (u, u') ∈ W := by
    by_contra hcon
    exact (Set.eq_empty_iff_forall_notMem.mp (Set.disjoint_iff_inter_eq_empty.mp hF)) (u, u') ⟨⟨hpK, hcon⟩, hpPf⟩
  have hs : u⁻¹ * u' = 1 := by
    refine hlocfree x (F.2.2.2 hx) _ hpW ?_
    rw [mul_smul, ← hux, inv_smul_smul]
  have h1 : u * (u⁻¹ * u') = u' := by group
  rw [hs, mul_one] at h1
  exact h1

end Work.EKLRelCross.FlowerLocalAux
