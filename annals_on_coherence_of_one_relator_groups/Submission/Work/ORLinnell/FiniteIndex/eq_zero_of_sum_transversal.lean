import Mathlib
import Submission.Work.ORLinnell.Linnell

/-!
# Directness of the finite-index decomposition `D H = ⊕_{q} D H₀ x_q`

This file proves the *directness* half of the finite index crossed product decomposition of
`D H` over `D H₀` (node `S2` of `Submission/Work/ORLinnell/Probe.lean`): if a finitely
supported family of elements of `D H₀`, indexed by the cosets `H ⧸ H₀` and multiplied by the
corresponding coset representatives `Quotient.out q`, sums to zero in `U`, then it is zero.

This is an immediate consequence of Linnell independence `(I1)`
(`LinnellDatum.independence`): the group parts `Quotient.out q` of distinct cosets `q` lie in
distinct right `H₀`-cosets, and the quotient is taken by the *normal* subgroup
`H₀.subgroupOf H`, so that `x y⁻¹ ∈ H₀` is equivalent to `x⁻¹ y ∈ H₀` (this is where normality
is used).
-/

namespace Work.ORLinnell.FiniteIndex

open Work.ORLinnell

/-- Linnell independence `(I1)` for an arbitrary finite indexing type: if the group parts
`g i` lie in pairwise distinct right cosets of `H` and the coefficients `a i` all lie in the
division closure `L.D H`, then a vanishing sum `∑ i, a i * gen (g i)` forces every coefficient
to vanish.  The statement is reduced to the `Fin n` version in `LinnellDatum.independence` by
transporting along `Fintype.equivFin ι`. -/
theorem independence_fintype {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : LinnellDatum K G U) {H : Subgroup G} {ι : Type*}
    [Fintype ι] (g : ι → G) (hinj : ∀ i j, g i * (g j)⁻¹ ∈ H → i = j) (a : ι → U)
    (ha : ∀ i, a i ∈ L.D H) (hsum : ∑ i, a i * (L.gen (g i) : U) = 0) : ∀ i, a i = 0 := by
  classical
  let e := Fintype.equivFin ι
  have hid : ∀ i j : Fin (Fintype.card ι), g (e.symm i) * (g (e.symm j))⁻¹ ∈ H → i = j := by
    intro i j hij
    have h1 : e.symm i = e.symm j := hinj _ _ hij
    exact e.symm.injective h1
  have hsum' : ∑ k : Fin (Fintype.card ι), a (e.symm k) * (L.gen (g (e.symm k)) : U) = 0 := by
    rw [Equiv.sum_comp e.symm (fun i => a i * (L.gen (g i) : U))]
    exact hsum
  have h := L.independence H (Fintype.card ι) (fun k => g (e.symm k)) hid
    (fun k => a (e.symm k)) (fun k => ha _) hsum'
  intro i
  have := h (e i)
  simpa using this

/-- **Directness of the finite-index decomposition.**  Let `H₀ ≤ H` be a normal subgroup of
`H`.  If `c` is a finitely supported family in `D H₀` indexed by the cosets `H ⧸ H₀` whose
associated sum `∑_q c_q · gen (out q)` vanishes in `U`, then `c = 0`. -/
theorem eq_zero_of_sum_transversal {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    {H₀ H : Subgroup G} (hH₀ : H₀ ≤ H) (hN : (H₀.subgroupOf H).Normal)
    (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀))
    (hc : c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) = 0) : c = 0 := by
  classical
  -- `H₀ ≤ H` is recorded in the source statement; the quotient `H ⧸ H₀.subgroupOf H` already
  -- lives in `H`, so it is not needed below.
  have _hH₀ : H₀ ≤ H := hH₀
  -- The representatives of distinct cosets lie in distinct right `H₀`-cosets.  Normality of
  -- `H₀.subgroupOf H` in `H` is what lets us switch from `x⁻¹ y ∈ H₀` (the quotient relation)
  -- to `x y⁻¹ ∈ H₀` (the hypothesis expected by Linnell independence).
  have hinj : ∀ q q' : H ⧸ H₀.subgroupOf H,
      ((Quotient.out q : H) : G) * (((Quotient.out q' : H) : G))⁻¹ ∈ H₀ → q = q' := by
    intro q q' hmem
    have hmemH : (Quotient.out q) * (Quotient.out q')⁻¹ ∈ H₀.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hmem
    have hconj : (Quotient.out q')⁻¹ * (Quotient.out q) ∈ H₀.subgroupOf H := by
      have h := hN.conj_mem' ((Quotient.out q) * (Quotient.out q')⁻¹) hmemH (Quotient.out q')
      simpa [mul_assoc] using h
    have hinv : (Quotient.out q)⁻¹ * (Quotient.out q') ∈ H₀.subgroupOf H := by
      simpa using (H₀.subgroupOf H).inv_mem hconj
    have hmk : QuotientGroup.mk (Quotient.out q) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.mpr hinv
    exact (Quotient.out_eq q).symm.trans (hmk.trans (Quotient.out_eq q'))
  -- Rewrite the hypothesis `hc` as a sum over the finite type `↥c.support`.
  have hsum : ∑ i : ↑c.support,
      (c ↑i : U) * (L.gen ((Quotient.out (↑i : H ⧸ H₀.subgroupOf H) : H) : G) : U) = 0 := by
    rw [Finset.sum_coe_sort c.support
      (fun i : H ⧸ H₀.subgroupOf H => (c i : U) * (L.gen ((Quotient.out i : H) : G) : U))]
    rw [← Finsupp.sum_of_support_subset c (Finset.Subset.refl _)
      (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) (fun i hi => by simp)]
    exact hc
  have hind := independence_fintype L (H := H₀)
    (fun (i : ↑c.support) => ((Quotient.out (↑i : H ⧸ H₀.subgroupOf H) : H) : G))
    (fun i j hij => Subtype.ext (hinj ↑i ↑j hij))
    (fun i => (c ↑i : U))
    (fun i => (c ↑i).2)
    hsum
  ext q
  by_cases hq : q ∈ c.support
  · simpa using hind ⟨q, hq⟩
  · have h0 : c q = 0 := by
      by_contra h
      exact hq (Finsupp.mem_support_iff.mpr h)
    exact congrArg Subtype.val h0

end Work.ORLinnell.FiniteIndex
