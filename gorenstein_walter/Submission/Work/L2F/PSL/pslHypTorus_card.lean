import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.mem_hypTorus

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- For a nonsquare `d ≠ 0` (odd characteristic), `2 * Nat.card (pslHypTorus F d) = q + 1`, i.e.
`|pslHypTorus F d| = (q+1)/2`.  Proof: `hypTorus_card` gives `|hypTorus F d| = q + 1`; the kernel
of `pslMap` on it is `{±1}` (`pslMap_eq_one_iff`, and `-1 ∈ hypTorus F d` corresponds to
`(a,b) = (-1,0)`), so the image has `(q+1)/2` elements. -/
theorem pslHypTorus_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    (hns : ∀ a : F, a * a ≠ d) :
    2 * Nat.card (Work.L2F.pslHypTorus F d) = Nat.card F + 1 := by
  classical
  -- `-1` is the matrix `!![-1, 0; 0, -1]`, i.e. the pair `(a,b) = (-1,0)` lies on the conic.
  have hmemneg : Work.L2F.negOne F ∈ Work.L2F.hypTorus F d := by
    rw [Work.L2F.Conic.mem_hypTorus]
    refine ⟨-1, 0, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]
  let g : Work.L2F.hypTorus F d := ⟨Work.L2F.negOne F, hmemneg⟩
  -- The restriction of `pslMap` to `hypTorus F d`.
  let φ : Work.L2F.hypTorus F d →* PSL(2, F) :=
    (Work.PSL2.pslMap F).comp (Work.L2F.hypTorus F d).subtype
  have hφ : ∀ x : Work.L2F.hypTorus F d, φ x = Work.PSL2.pslMap F (x : SL(2, F)) := fun x => rfl
  -- Its kernel is the two-element subgroup `{1, -1}`, i.e. `⟨-1⟩`.
  have hker : φ.ker = Subgroup.zpowers g := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [hφ] at hx
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (x : SL(2, F))).mp hx with h | h
      · have hx1 : x = 1 := Subtype.ext h
        rw [hx1]
        exact Subgroup.one_mem _
      · have hxg : x = g := Subtype.ext h
        rw [hxg]
        exact Subgroup.mem_zpowers g
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      change Work.PSL2.pslMap F (((⟨Work.L2F.negOne F, hmemneg⟩ : Work.L2F.hypTorus F d) :
        SL(2, F))) = 1
      exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  -- hence the kernel has `2` elements (`g ^ 2 = 1`, `g ≠ 1`).
  have hcard : Nat.card φ.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      simp only [g, Subtype.coe_mk, Work.L2F.negOne]
      noncomm_ring
    · intro h
      have h1 : Work.L2F.negOne F = 1 := by
        simpa [g] using congrArg (fun x : Work.L2F.hypTorus F d => (x : SL(2, F))) h
      have h' : (-1 : F) = 1 := by
        have := congrArg (fun x : SL(2, F) => ((x : Matrix (Fin 2) (Fin 2) F) 0 0)) h1
        simpa [Work.L2F.negOne] using this
      have h2' : (1 : F) + 1 = 0 := neg_eq_iff_add_eq_zero.mp h'
      rw [one_add_one_eq_two] at h2'
      exact h2 h2'
  -- the range is `pslHypTorus F d` by definition.
  have hrange : φ.range = Work.L2F.pslHypTorus F d := by
    change ((Work.PSL2.pslMap F).comp (Work.L2F.hypTorus F d).subtype).range =
      Subgroup.map (Work.PSL2.pslMap F) (Work.L2F.hypTorus F d)
    rw [← MonoidHom.map_range (Work.PSL2.pslMap F) (Work.L2F.hypTorus F d).subtype,
      Subgroup.range_subtype]
  -- first isomorphism theorem: `|hypTorus| = |pslHypTorus| * |kernel|`.
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have heq : Nat.card (Work.L2F.hypTorus F d ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [heq, hcard, hrange] at hq
  rw [Work.L2F.Conic.hypTorus_card F h2 d hd hns] at hq
  rw [mul_comm]
  exact hq.symm

end Work.L2F.PSL
