import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.PhiN_mapsTo

set_option linter.unusedVariables false

namespace Work.ORP311

/-- **B5b of `P311_DESIGN_LEAD.md`**: the matrix operator `matOp (B.map (PhiN N))` attached to the
entrywise image of a matrix `B` over `N(↥N)` under the diagonal inclusion `Φ_N : N(N) → N(G)` is
block diagonal over the right `N`-cosets of `G`.

The proof is coordinatewise.  By `mem_ell2Sub_iff` an element of `ell2Sub n (coset N t J)` has all
its `δ_g`-components with `g ∉ coset N t J = N * t ^ J` vanishing; by `hcoord_matOp_apply` the `i`-th
coordinate of `matOp (B.map (PhiN N)) x` is the finite sum `∑ j, Φ_N (B i j) (hcoord n j x)`, and
each summand preserves the `δ`-support condition `N * t ^ J` by the `Φ`-block lemma
(`PhiN_mapsTo`).  The twist data `h` is not needed. -/
theorem isBlockDiag_matOp_PhiN {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) {n : ℕ} (B : Matrix (Fin n) (Fin n) ↥(Work.ORVonNeumann.groupVonNeumann ↥N)) : Work.ORP311.IsBlockDiag N t n (Work.ORVonNeumann.Rep.matOp (G := G) (B.map (Work.ORP311.P311.PhiN N))) := by
  intro J x hx
  rw [Work.ORP311.mem_ell2Sub_iff] at hx ⊢
  intro g hg i
  rw [Work.ORVonNeumann.Rep.hcoord_matOp_apply]
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro j _
  have hg' : ¬ ∃ k ∈ N, g = k * t ^ J := by
    rintro ⟨k, hk, hk'⟩
    exact hg ⟨⟨k, hk⟩, hk'⟩
  have hf : ∀ g' : G, (¬∃ k ∈ N, g' = k * t ^ J) →
      inner ℂ (Work.ORVonNeumann.Rep.hcoord n j x) (Work.ORVonNeumann.Rep.deltaG g') = 0 := by
    intro g' hg''
    refine hx g' ?_ j
    rintro ⟨k, hk⟩
    exact hg'' ⟨(k : G), k.2, hk⟩
  simpa [Matrix.map_apply] using
    Work.ORP311.PhiN_mapsTo N (B i j) (t ^ J) (Work.ORVonNeumann.Rep.hcoord n j x) hf g hg'

end Work.ORP311
