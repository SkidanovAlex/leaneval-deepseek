import Mathlib
import Submission.Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

noncomputable section

/-- The finite-index transversal decomposition of `D H` over `D H₀` with the coefficients on the
*right*: if `H₀ ≤ H` is normal in `H` of finite index and every nonzero element of `D H₀` is a
unit, then every `y ∈ D H` is a finite `D H₀`-linear combination `∑_q gen (out q) · d_q` of the
coset representatives.

This is the mirror of `Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex` (coefficients on the
left), obtained by conjugating each coefficient: since `H₀` is normal in `H`, conjugation by
`gen (out q) ∈ D H` preserves `D H₀`, and `d · gen (out q) = gen (out q) · (gen (out q)⁻¹ · d ·
gen (out q))`. -/
theorem span_D_of_finiteIndex_right {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {H₀ H : Subgroup G}
    (hH₀ : H₀ ≤ H) (hN : (H₀.subgroupOf H).Normal) (hfin : (H₀.subgroupOf H).FiniteIndex)
    (hdiv : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) (y : U) (hy : y ∈ L.D H) :
    ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀),
      y = c.sum (fun q d => (L.gen ((Quotient.out q : H) : G) : U) * (d : U)) := by
  classical
  obtain ⟨c, hc⟩ :=
    Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex L hH₀ hN hfin hdiv y hy
  -- conjugation by an element of `H` preserves `D H₀`, in inverse order
  have hconj : ∀ (g : H) (d : U), d ∈ L.D H₀ →
      (↑((L.gen (g : G))⁻¹) : U) * d * (L.gen (g : G) : U) ∈ L.D H₀ := fun g d hd => by
    have h := L.conj_mem hH₀ hN g⁻¹ d hd
    simpa using h
  -- the conjugated coefficients
  let d' : (H ⧸ H₀.subgroupOf H) → ↥(L.D H₀) := fun q =>
    ⟨(↑((L.gen ((Quotient.out q : H) : G))⁻¹) : U) * (c q : U)
        * (L.gen ((Quotient.out q : H) : G) : U),
      hconj (Quotient.out q) (c q : U) (c q).2⟩
  have hd'zero : ∀ q ∉ c.support, d' q = 0 := by
    intro q hq
    have h0 : c q = 0 := Finsupp.notMem_support_iff.mp hq
    apply Subtype.ext
    simp [d', h0]
  have hf : ∀ q, d' q ≠ 0 → q ∈ c.support := fun q hq => by
    by_contra h
    exact hq (hd'zero q h)
  refine ⟨Finsupp.onFinset c.support d' hf, ?_⟩
  have hsub : (Finsupp.onFinset c.support d' hf).support ⊆ c.support := by
    intro q hq
    rw [Finsupp.mem_support_iff] at hq
    exact hf q (by rwa [Finsupp.onFinset_apply] at hq)
  rw [hc, Finsupp.sum, Finsupp.sum]
  rw [Finset.sum_subset hsub (fun q _ hq => by
    rw [Finsupp.notMem_support_iff.mp hq]; simp)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finsupp.onFinset_apply]
  show (c q : U) * (L.gen ((Quotient.out q : H) : G) : U)
      = (L.gen ((Quotient.out q : H) : G) : U)
        * ((↑((L.gen ((Quotient.out q : H) : G))⁻¹) : U) * (c q : U)
            * (L.gen ((Quotient.out q : H) : G) : U))
  rw [mul_assoc, ← mul_assoc (L.gen ((Quotient.out q : H) : G) : U)
    (↑((L.gen ((Quotient.out q : H) : G))⁻¹) : U), Units.mul_inv, one_mul]

end

end Work.ORFinal.TorsionData
