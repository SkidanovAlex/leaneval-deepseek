import Mathlib
import Submission.Work.ORVonNeumann.Envelope

namespace Work.ORBridgeLinnell

universe u

/-- Reindexing helper: if a function on a finite type vanishes off a predicate `P`, then its
total sum equals the sum of its restriction to the subtype `{x // P x}`. -/
theorem sum_eq_sum_subtype {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (f : ι → M) (hf : ∀ x, ¬ P x → f x = 0) :
    ∑ x : ι, f x = ∑ x : {x // P x}, f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (fun x => by simp) f]
  exact (Finset.sum_subset (Finset.filter_subset P Finset.univ)
    (fun x _ hx => hf x (by simpa using hx))).symm

/-- **Linnell independence, finite-index form.**

`Work.ORVonNeumann.LinnellIndependent` is stated for `Fin (n + 1)`-indexed families; here we
extend it to an arbitrary finite index type `I`.  The sum `∑ i, φ (d i) * ι (single (q i) 1)` can
only vanish if all the coefficients `d i` vanish: the terms with `d i = 0` contribute nothing
(`φ` is additive), so the sum is really a sum over the finite nonempty subtype `{i // d i ≠ 0}`,
after which `hlinnell` applies. -/
theorem linnellIndependent_fintype {G : Type u} [Group G] {V : Type u} [Ring V] {U : Type u} [Ring U]
    (H : Subgroup G) (φ : V →+* U) (ι : MonoidAlgebra ℂ G →+* U)
    (hlinnell : Work.ORVonNeumann.LinnellIndependent H V U φ ι)
    {I : Type*} [Fintype I] (q : I → G) (d : I → V)
    (hq : ∀ i j, q i * (q j)⁻¹ ∈ H → i = j)
    (hsum : ∑ i, φ (d i) * ι (MonoidAlgebra.single (q i) 1) = 0) : ∀ i, d i = 0 := by
  classical
  intro i0
  by_contra h0
  have hi0 : d i0 ≠ 0 := h0
  have hcard : 0 < Fintype.card {j : I // d j ≠ 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨i0, hi0⟩⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hcard)
  let e : {j : I // d j ≠ 0} ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn
  have hne : ∀ k : Fin (n + 1), d ↑(e.symm k) ≠ 0 := fun k => (e.symm k).2
  have hcos : ∀ k l : Fin (n + 1), q ↑(e.symm k) * (q ↑(e.symm l))⁻¹ ∈ H → k = l := by
    intro k l hkl
    exact e.symm.injective (Subtype.ext (hq _ _ hkl))
  have hnonzero := hlinnell n (fun k => q ↑(e.symm k)) (fun k => d ↑(e.symm k)) hne hcos
  have hstep : (∑ k : Fin (n + 1), φ (d ↑(e.symm k)) * ι (MonoidAlgebra.single (q ↑(e.symm k)) 1))
      = ∑ j : {j : I // d j ≠ 0}, φ (d ↑j) * ι (MonoidAlgebra.single (q ↑j) 1) :=
    Equiv.sum_comp e.symm
      (fun j : {j : I // d j ≠ 0} => φ (d ↑j) * ι (MonoidAlgebra.single (q ↑j) 1))
  have hsub : (∑ j : {j : I // d j ≠ 0}, φ (d ↑j) * ι (MonoidAlgebra.single (q ↑j) 1))
      = ∑ j : I, φ (d j) * ι (MonoidAlgebra.single (q j) 1) :=
    (sum_eq_sum_subtype (fun j : I => d j ≠ 0)
      (fun j => φ (d j) * ι (MonoidAlgebra.single (q j) 1))
      (fun j hj => by rw [show d j = 0 from not_not.mp hj, map_zero, zero_mul])).symm
  exact hnonzero (by rw [hstep, hsub]; exact hsum)

end Work.ORBridgeLinnell
