import Mathlib
import Submission.Work.Whitney.WSumChars
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero
import Submission.Work.Whitney.cupChern_one_right
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Thom

noncomputable section

/-! ## Two transport lemmas on `Work.Thom.cohTransport`

The degree transport `Work.Thom.cohTransport h` is the canonical identification of the cohomology in
two equal degrees; it is an isomorphism (of `ℤ`-modules), and in this file we need

* `Work.Whitney.cohTransport_symm_comp` — the transport along `h` followed by the transport along
  `h.symm` is the identity (the reverse composition is `Work.Whitney.cohTransport_trans` itself);
* `Work.Whitney.cohTransport_chernClass_degree` — the Chern classes of a *fixed* bundle, viewed as a
  function of the degree, commute with the transport: `c_j(Z)` transported from degree `2j` to
  degree `2j'` is `c_{j'}(Z)`.  This is the "function evaluated at equal indices" fact (proved by
  `subst`), and it is what allows one to replace the degree `0 + m₂` of the target by `m₂`. -/

/-- **The degree transport composed with its inverse is the identity.** -/
theorem cohTransport_symm_comp {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n')
    (x : Work.Thom.Coh ℤ n B) :
    Work.Thom.cohTransport h.symm (Work.Thom.cohTransport h x) = x := by
  rw [Work.Whitney.cohTransport_trans,
    Work.LerayHirsch.cohTransport_congr_proof (h.trans h.symm) (rfl : n = n),
    Work.Thom.cohTransport_rfl]

/-- **The Chern classes commute with the degree transport.**  For a bundle `Z` of rank `m`, the
`j`-th Chern class transported from degree `2*j` to the equal degree `2*j'` is the `j'`-th Chern
class of `Z`. -/
theorem cohTransport_chernClass_degree {B : Type} [TopologicalSpace B] {m : ℕ} {ι : Type}
    [Fintype ι] {j j' : ℕ} (h : j = j') (h₂ : 2 * j = 2 * j')
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.Thom.cohTransport h₂ (Work.Thom.chernClass m j Z) = Work.Thom.chernClass m j' Z := by
  subst h
  exact (Work.LerayHirsch.cohTransport_congr_proof h₂ (rfl : 2 * j = 2 * j)).trans
    (Work.Thom.cohTransport_rfl _)

/-- **The top Chern class of a Whitney sum with a rank-`0` first summand.**

This is the boundary case `m1 = 0` of the headline `Work.Whitney.chernClass_whitneySum_top`
(= `Work.Whitney.TopClassMul`).  It is needed because the main route
(`Work.Whitney.thomClassRank_whitneySum_rel` + `Work.Whitney.chernClass_whitneySum_top_of_thomProduct`)
needs `1 ≤ m1` and `1 ≤ m2` (`Work.Thom.thomClassRank` is only defined for positive rank).

ROUTE.  `chernClass 0 0 Z1` is the unit class `Work.Cohomology.oneH` of `H^0(B;ℤ)`
(`Work.Thom.chernClass_zero_rank` + the definition of `Work.Thom.chernClassZero`; the `cohTransport`
there is along `rfl`), so the right-hand side is `Work.Whitney.cupChern 0 m2 oneH (chernClass m2 m2 Z2)`,
which is `Work.Thom.cohTransport (2*(0+m2) = 2*m2) (chernClass m2 m2 Z2)` by the left unit law
`Work.LerayHirsch.cohTransport_cupChern_one_left` (`Submission/Work/LerayHirsch/
whitneySumFormulaOfLerayHirsch.lean`; the right unit law `Work.Whitney.cupChern_one_right` is the
base case of the same computation).  On the left, `chernClass (0+m2) (0+m2) (whitneySum Z1 Z2)` is
`chernClass m2 m2 (whitneySum Z1 Z2)` up to the index rewrite `Nat.zero_add m2` (note: `0 + m2 = m2`
is *not* definitional in Lean 4, `Nat.zero_add` is proved by induction); commuting the sum
(`Work.Whitney.nonempty_bundleIso_whitneySum_comm`, with
`Work.Thom.chernClass_BundleIso_of_eq` for the index bookkeeping `0+m2` vs `m2+0`) reduces it to
`chernClass (m2+0) (m2+0) (whitneySum Z2 Z1)`, which is `chernClass m2 m2 Z2` by the rank-zero result
`Work.Whitney.chernClass_whitneySum_rank_zero` (`Submission/Work/Whitney/
chernClass_whitneySum_rank_zero.lean`) applied to `Z2` and `Z1`.  The two `cohTransport`-conventions
must be reconciled with `Work.Thom.cohTransport_trans` and
`Work.Thom.cohTransport_congr_proof` (`Submission/Work/LerayHirsch/
whitneySumFormula_one_one_of_topClassMul.lean`). -/
theorem chernClass_whitneySum_top_rank_zero_left {B : Type} [TopologicalSpace B] {m₂ : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (0 + m₂) (0 + m₂) (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.cupChern 0 m₂ (Work.Thom.chernClass 0 0 Z₁)
          (Work.Thom.chernClass m₂ m₂ Z₂) := by
  -- The degree `2 * (0 + m₂)` is `2 * m₂`; we compare the two sides after transporting to the
  -- degree `2 * m₂`, where the rank-`0` computation lives.
  have hdeg : 2 * (0 + m₂) = 2 * m₂ := by omega
  -- ## The left-hand side, in degree `2 * m₂`
  obtain ⟨ecomm⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm (Z₁ := Z₁) (Z₂ := Z₂)
  have hL : Work.Thom.cohTransport hdeg
        (Work.Thom.chernClass (0 + m₂) (0 + m₂) (Work.Whitney.whitneySum Z₁ Z₂))
      = Work.Thom.chernClass m₂ m₂ Z₂ := by
    -- interchange the two summands (`0 + m₂ = m₂ + 0`), then drop the rank-`0` summand
    rw [Work.Whitney.chernClass_BundleIso_of_eq (by omega : 0 + m₂ = m₂ + 0)
      (Work.Whitney.whitneySum Z₁ Z₂) (Work.Whitney.whitneySum Z₂ Z₁) ecomm (0 + m₂)]
    rw [Work.Whitney.chernClass_whitneySum_rank_zero Z₂ Z₁ (0 + m₂)]
    -- and undo the degree `0 + m₂` vs `m₂`
    exact cohTransport_chernClass_degree (show 0 + m₂ = m₂ by omega) hdeg Z₂
  -- ## The right-hand side, in degree `2 * m₂`
  have hR : Work.Thom.cohTransport hdeg
        (Work.Whitney.cupChern 0 m₂ (Work.Thom.chernClass 0 0 Z₁)
          (Work.Thom.chernClass m₂ m₂ Z₂))
      = Work.Thom.chernClass m₂ m₂ Z₂ := by
    -- `c_0` is the unit class, and the unit law of the graded product removes it
    rw [Work.Thom.chernClass_zero_eq_oneH Z₁]
    exact Work.LerayHirsch.cohTransport_cupChern_one_left m₂ (Work.Thom.chernClass m₂ m₂ Z₂)
  -- ## Assembly
  have hLeq : Work.Thom.chernClass (0 + m₂) (0 + m₂) (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Thom.cohTransport hdeg.symm (Work.Thom.chernClass m₂ m₂ Z₂) :=
    (cohTransport_symm_comp hdeg _).symm.trans (congrArg (Work.Thom.cohTransport hdeg.symm) hL)
  have hReq : Work.Whitney.cupChern 0 m₂ (Work.Thom.chernClass 0 0 Z₁)
        (Work.Thom.chernClass m₂ m₂ Z₂)
      = Work.Thom.cohTransport hdeg.symm (Work.Thom.chernClass m₂ m₂ Z₂) :=
    (cohTransport_symm_comp hdeg _).symm.trans (congrArg (Work.Thom.cohTransport hdeg.symm) hR)
  exact hLeq.trans hReq.symm

end

end Work.Whitney
