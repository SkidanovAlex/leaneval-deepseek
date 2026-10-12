import Mathlib.Computability.Reduce
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.DvApriori.dk_gradeA_one_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.term_ij`

FS §6 (`lem:LocMatrices`): for the graded matrix `𝒜` and the norm profile `ψ` of a box
state `Φ` (`Work.BoseFixB2.gradeA`, `Work.BoseFixB2.gradePsi`), every matrix element
sandwiched between the profile components evaluates to the polarised box word:

    `star ψ_i · 𝒜_{ij} · ψ_j = ⟨1_{n₊=i}Φ, H_Λ 1_{n₊=j}Φ⟩ / ‖Φ‖²`

(`polB`'s definition is the polarisation of `wordB`, so the right-hand side is
`polB (vecZ i) (vecZ j) / normB Φ`).

The `ℕ`-indexed form of this identity — the pairs `(k, k+m)` with `k + m ≤ n`, in the
two orders in which they appear in `d₁`, `d₂` — is proved in
`Submission/Work/BoseFixB2/DvApriori/dk_gradeA_one_two.lean` as `term_fwd` (`k ≤ k+m`)
and `term_bwd` (the same pair read backwards, via `𝒜`'s symmetry `A_{ji} = A_{ij}`).
The present file removes those index restrictions: for *arbitrary* sector indices
`i, j ∈ [0,n]` the identity holds.  The two cases `i ≤ j` (use `term_fwd` with
`k = i.toNat`, `m = (j-i).toNat`) and `j < i` (use `term_bwd` with `k = j.toNat`,
`m = (i-j).toNat`, and the symmetry of `polB`) are pure index bookkeeping between the
integer indices of the grading and the natural-number indices of the sector sums.

The complement of the `term_fwd`/`term_bwd` hypotheses that *does* carry content —
FS's convention that `𝒜_{ij} = 0` when a sector norm vanishes, harmless because then
`polB` vanishes too — is already contained in those two lemmas
(`polB_eq_zero_of_normB_eq_zero` there).
-/

noncomputable section

open scoped Real Topology BigOperators
open Finset

namespace Work.BoseFixB2.Energy

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem term_ij {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < Work.BoseFixB2.fsSide v μ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {i j : ℤ} (hi : i ∈ Finset.Icc (0 : ℤ) (n : ℤ)) (hj : j ∈ Finset.Icc (0 : ℤ) (n : ℤ)) : star (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ i) * Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j * Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j = ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i) (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j) / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
  obtain ⟨hi0, hin⟩ := Finset.mem_Icc.mp hi
  obtain ⟨hj0, hjn⟩ := Finset.mem_Icc.mp hj
  rcases le_or_gt i j with hij | hji
  · -- Case `i ≤ j`: `term_fwd` applied to the pair `(i.toNat, i.toNat + (j-i).toNat)`.
    have hk : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
    have hm : (((j - i).toNat : ℕ) : ℤ) = j - i := Int.toNat_of_nonneg (by omega)
    have hidx : ((i.toNat : ℤ) + (((j - i).toNat : ℕ) : ℤ)) = j := by rw [hk, hm]; ring
    have hnat : j.toNat = i.toNat + (j - i).toNat := by
      have h : ((j.toNat : ℕ) : ℤ) = ((i.toNat + (j - i).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hj0]; push_cast; exact hidx.symm
      exact Nat.cast_injective h
    have hsum : ((i.toNat + (j - i).toNat : ℕ) : ℤ) = j := by push_cast; exact hidx
    have hkm : i.toNat + (j - i).toNat ≤ n := by
      have h : ((i.toNat + (j - i).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hsum]; exact hjn
      exact_mod_cast h
    have hf := Work.BoseFixB2.DvApriori.term_fwd (v := v) (h := h) (μ := μ) (n := n)
      (Φ := Φ) hℓ hℓ hpos hΦ (m := (j - i).toNat) (k := i.toNat) hkm
    have hZ1 : Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i
        = Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) i.toNat Φ :=
      Work.BoseFixB2.DvApriori.vecZ_apply (Work.BoseFixB2.fsSide v μ) hi0 hin
    have hZ2 : Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j
        = Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ)
            (i.toNat + (j - i).toNat) Φ := by
      rw [Work.BoseFixB2.DvApriori.vecZ_apply (Work.BoseFixB2.fsSide v μ) hj0 hjn, hnat]
    rw [hZ1, hZ2]
    conv_lhs => rw [← hk, ← hidx]
    exact hf
  · -- Case `j < i`: `term_bwd` applied to the pair `(j.toNat, j.toNat + (i-j).toNat)`.
    have hk : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hm : (((i - j).toNat : ℕ) : ℤ) = i - j := Int.toNat_of_nonneg (by omega)
    have hidx : ((j.toNat : ℤ) + (((i - j).toNat : ℕ) : ℤ)) = i := by rw [hk, hm]; ring
    have hnat : i.toNat = j.toNat + (i - j).toNat := by
      have h : ((i.toNat : ℕ) : ℤ) = ((j.toNat + (i - j).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hi0]; push_cast; exact hidx.symm
      exact Nat.cast_injective h
    have hsum : ((j.toNat + (i - j).toNat : ℕ) : ℤ) = i := by push_cast; exact hidx
    have hkm : j.toNat + (i - j).toNat ≤ n := by
      have h : ((j.toNat + (i - j).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hsum]; exact hin
      exact_mod_cast h
    have hb := Work.BoseFixB2.DvApriori.term_bwd (v := v) (h := h) (μ := μ) (n := n)
      (Φ := Φ) hℓ hℓ hpos hΦ (m := (i - j).toNat) (k := j.toNat) hkm
    have hZ1 : Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i
        = Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ)
            (j.toNat + (i - j).toNat) Φ := by
      rw [Work.BoseFixB2.DvApriori.vecZ_apply (Work.BoseFixB2.fsSide v μ) hi0 hin, hnat]
    have hZ2 : Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j
        = Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) j.toNat Φ :=
      Work.BoseFixB2.DvApriori.vecZ_apply (Work.BoseFixB2.fsSide v μ) hj0 hjn
    rw [hZ1, hZ2]
    rw [Work.BoseFixB2.Polar.polB_symm
      (hΦ := Work.BoseFixB2.DvApriori.secProj_contDiff' hℓ hΦ)
      (hΨ := Work.BoseFixB2.DvApriori.secProj_contDiff' hℓ hΦ)]
    conv_lhs => rw [← hk, ← hidx]
    exact hb

end Work.BoseFixB2.Energy
