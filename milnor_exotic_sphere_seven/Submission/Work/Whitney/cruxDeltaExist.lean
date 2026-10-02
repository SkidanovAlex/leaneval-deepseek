import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Whitney.cruxAux
import Submission.Work.Whitney.cruxInputs
import Submission.Work.Gen.cruxComparison
import Submission.Work.Gen.chernRoot_split
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.Kunneth.kunnethCP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The `δ`-form of the crux exists.**

For every family `M` of `N ≥ 1` complex line bundles over a paracompact Hausdorff base `B`, the
top-minus-one Chern class `c_{N-1}(⊕_k M_k)` of the sum of the family is a `H⁰(B;ℤ)`-multiple of the
elementary symmetric class `eSym N M (N-1)`:

  `∃ δ : H⁰(B;ℤ), c_{N-1}(⊕_k M_k) = δ ⌣ eSym N M (N-1)`.

For `N = 1` both sides are the unit class and `δ = 1` works.  For `N ≥ 2` the proof is the
*coefficient comparison* of the crux (`Work.Gen.cruxComparison`): with `W = ⊕_k M_k` (rank `N`),
`P = P(W)`, and `ψ ∈ H^{2(N-2)}(P;ℤ)` the `ψ`-existence class of `Work.Whitney.cruxPsiExists`
(`c_{N-1}(Q) = π^*(c_{N-1}(W)) + ζ ⌣ ψ` for a complement `Q` of the tautological line), the
comparison of the `ζ¹`-coefficient of the top-class equation `ζ ⌣ c_{N-1}(Q) = π^*(c_N(W))`
(`Work.Whitney.cruxTopClassEq` together with `lineSumCore_top_chern`) against the Chern-root
expansion `ζ^N = Σ_i (-1)^{N+1+i} eSym N M (N-i) ζ^i` (`Work.Gen.chernRoot_split`) reads

  `c_{N-1}(W) = δ ⌣ eSym N M (N-1)`,  `δ = (-1)^{N+2} · (top Leray–Hirsch coefficient of ψ)`,

which is the statement with the explicit `δ` (a degree-`0` class, independent of the choice of `Q`,
`ψ`, and the splitting). -/
theorem cruxDeltaExist (N : ℕ) (hN : 1 ≤ N)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    ∃ δ : Work.Thom.Coh ℤ 0 B,
      Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
        = Work.Whitney.deltaCup N M δ := by
  rcases N with _ | n
  · omega
  · by_cases hn : n = 0
    · -- `N = 1`: both sides are the unit class, and `δ = 1` works.
      subst hn
      refine ⟨Work.Cohomology.oneH ℤ (Work.Whitney.ssB B), ?_⟩
      rw [Work.Thom.chernClass_zero_eq_oneH]
      rw [Work.Whitney.deltaCup_eq]
      have hz : Work.Gen.eSym 1 M 0
          = Work.Thom.cohTransport (by rfl : (2:ℕ)*0 = 0)
              (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) := by
        rw [Work.Gen.eSym_one_class]
      rw [hz]
      rw [Work.Whitney.cupChern_one_right]
      simp only [Work.Thom.cohTransport_rfl]
    · -- `N = n + 1` with `n ≥ 1`: the coefficient comparison of the crux.
      have hn1 : 1 ≤ n := by omega
      obtain ⟨Q, e, ψ, hψ⟩ := Work.Whitney.cruxPsiExists hn1 M
      have hLH : Work.LerayHirsch.LerayHirsch (Work.LerayHirsch.lineSumCore (n+1) M) :=
        Work.LerayHirsch.lerayHirsch_of_kunnethCP Work.Kunneth.kunnethCP _
      obtain ⟨ψf, hψf⟩ := (hLH (n-1)).2 ψ
      have hB : Work.Whitney.cupChern n 1 (Work.Thom.chernClass n n Q)
            (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore (n+1) M))
          = (Work.Thom.CohMap (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore (n+1) M))
                ℤ (2*(n+1))).hom
              (Work.Thom.chernClass (n+1) (n+1) (Work.LerayHirsch.lineSumCore (n+1) M)) := by
        have h := Work.Whitney.cruxTopClassEq hn1 M Q e
        rw [← Work.Gen.lineSumCore_top_chern (n+1) M] at h
        exact h
      let c : (i : {i : Fin (n+1) // (i:ℕ) ≤ n+1}) →
          Work.Thom.Coh ℤ (2*((n+1) - (i:ℕ))) B :=
        fun i => ((-1:ℤ)^((n+1)+1+(i:ℕ))) • Work.Gen.eSym (n+1) M ((n+1) - (i:ℕ))
      have hc : Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore (n+1) M) (n+1) c
          = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore (n+1) M) (n+1) :=
        Work.Gen.chernRoot_split (n := n+1) (by omega) M
      have hcmp := Work.Gen.cruxComparison hn1
        (W := Work.LerayHirsch.lineSumCore (n+1) M) hLH
        (Work.Thom.chernClass (n+1) n (Work.LerayHirsch.lineSumCore (n+1) M))
        (Work.Thom.chernClass (n+1) (n+1) (Work.LerayHirsch.lineSumCore (n+1) M))
        ψ (Work.Thom.chernClass n n Q) ψf hψf hψ hB c hc
      let y0 : Work.Thom.Coh ℤ 0 B :=
        Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
          (-(ψf Work.Gen.topCoeffIdx))
      have hc1 : c ⟨⟨1, by omega⟩, by omega⟩ = ((-1:ℤ)^(n+3)) • Work.Gen.eSym (n+1) M n := rfl
      refine ⟨((-1:ℤ)^(n+3)) • y0, ?_⟩
      rw [hc1] at hcmp
      rw [Work.Whitney.cupChern_negOnePow_right, Work.Thom.cohTransport_zsmul] at hcmp
      rw [Work.Whitney.deltaCup_eq_dcup]
      simp only [Work.Whitney.dcup]
      rw [Work.Whitney.cupChern_negOnePow_left, Work.Thom.cohTransport_zsmul]
      exact hcmp

end

end Work.Whitney
