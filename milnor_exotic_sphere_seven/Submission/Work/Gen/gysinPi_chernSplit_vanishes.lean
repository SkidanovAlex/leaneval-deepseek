import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.Thom.Gysin
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

/-- **The pullback of the crux class to the punctured total space of the tautological line bundle
vanishes.**  `Z` is a complex bundle of rank `n+1` over `B`, `Q` a complement in a splitting
`π^*Z ≅ ℓ ⊕ Q` (`h`), `π = projMap Z`, and `r : ℓ∖0 → P(Z)` the projection of the punctured total
space of the tautological line bundle `ℓ = tautLine Z`.  Claim: the class
`x = c_n(Q) - π^*(c_n Z) ∈ H^{2n}(P(Z))` has `r^*(x) = 0`.

`Work.Thom.gysinπ W (2*n)` (for `W = realification (tautLine Z)`) *is* the pullback `r^*` in degree
`2n`: it is `(bundleProj W ∘ subtypeMap (zeroComplement W))^*`.

Route: naturality (`Work.Thom.chernClass_comap`) gives `r^*c_n(Q) = c_n(r^*Q)` and
`r^*π^*c_n(Z) = c_n(r^*(π^*Z))`; `r^*(π^*Z) = r^*(ℓ ⊕ Q)` by `Work.Thom.BundleIso_comap_exists`
(plus `Work.Whitney.whitneySum_bundleComap`, and `Work.Thom.bundleComap_comp` /
`Work.Thom.CohMap_comp` for the composition of the two pullbacks) applied to `h`, with the
`1+n = n+1` fibre cast handled by `Work.Thom.chernClass_eq_of_cast_fibre_iso`; the peel
`Work.Whitney.chernClass_whitneySum_pullback_eq` (with `m₁ = 0`, `m₂ = n`, `k = n`) gives
`c_n(r^*(ℓ⊕Q)) = c_n(tautQuotient ℓ ⊕ r^*Q)`, and `tautQuotient ℓ` has rank `0`, so this is
`c_n(r^*Q)` (`Work.Whitney.nonempty_bundleIso_whitneySum_comm` +
`Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton`, or
`Work.Whitney.chernClass_whitneySum_rank_zero`).  Consequently
`r^*(x) = c_n(r^*Q) - c_n(r^*Q) = 0`. -/
theorem gysinPi_chernSplit_vanishes {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {n : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin n))
          (ι × Fin (n + 1)))
    (h : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) Q))) :
    Work.Thom.gysinπ (Work.Thom.realification (Work.LerayHirsch.tautLine Z)) (2 * n)
      (Work.Thom.chernClass n n Q
        - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * n)).hom
            (Work.Thom.chernClass (n + 1) n Z)) = 0 := by
  -- The projection of the punctured total space of the tautological line bundle: the composite of
  -- the bundle projection with the inclusion of the complement of the zero section.
  let pp :
      C(↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.tautLine Z))),
        Work.LerayHirsch.ProjSpace Z) :=
    (Work.Thom.bundleProj (Work.Thom.realification (Work.LerayHirsch.tautLine Z))).comp
      (Work.Thom.subtypeMap
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.tautLine Z))))
  -- **The crux computation**: over the punctured total space of `ℓ`, the pulled-back bundle
  -- `r^*(π^*Z) ≅ r^*(ℓ ⊕ Q)` has the same Chern classes as `r^*Q` (the line bundle `r^*ℓ` peels
  -- off, because the tautological section is nowhere zero).
  have key : Work.Thom.chernClass (n + 1) n
        (Work.Thom.bundleComap (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z)) pp)
      = Work.Thom.chernClass n n (Work.Thom.bundleComap Q pp) := by
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := Work.Thom.BundleIso_comap_exists
      (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))
      (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) Q) e pp
    refine (Work.Whitney.chernClass_eq_of_cast_fibre_iso (a := n + 1) (b := 1 + n) (by omega)
      (Work.Thom.bundleComap (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z)) pp)
      (Work.Thom.bundleComap (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) Q) pp)
      e' n).trans ?_
    rw [Work.Whitney.chernClass_whitneySum_pullback_eq (E := Work.LerayHirsch.tautLine Z) (F := Q)
      (m₁ := 0) (m₂ := n) (k := n)]
    obtain ⟨e''⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
      (Work.Thom.tautQuotient (m := 0) (Work.LerayHirsch.tautLine Z))
      (Work.Thom.bundleComap Q pp)
    rw [Work.Whitney.chernClass_eq_of_cast_fibre_iso (a := 0 + n) (b := n + 0) (by omega)
      (Work.Whitney.whitneySum (Work.Thom.tautQuotient (m := 0) (Work.LerayHirsch.tautLine Z))
        (Work.Thom.bundleComap Q pp))
      (Work.Whitney.whitneySum (Work.Thom.bundleComap Q pp)
        (Work.Thom.tautQuotient (m := 0) (Work.LerayHirsch.tautLine Z))) e'' n]
    rw [Work.Whitney.chernClass_whitneySum_rank_zero (Z := Work.Thom.bundleComap Q pp)
      (W := Work.Thom.tautQuotient (m := 0) (Work.LerayHirsch.tautLine Z)) n]
  -- `gysinπ W (2n)` is the pullback along `pp` (the two composing pullbacks are `CohMap_comp`).
  have hgys : Work.Thom.gysinπ (Work.Thom.realification (Work.LerayHirsch.tautLine Z)) (2 * n)
      (Work.Thom.chernClass n n Q
        - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * n)).hom
            (Work.Thom.chernClass (n + 1) n Z))
      = (Work.Thom.CohMap pp ℤ (2 * n)).hom
        (Work.Thom.chernClass n n Q
          - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * n)).hom
              (Work.Thom.chernClass (n + 1) n Z)) := by
    rw [Work.Thom.CohMap_comp]
    rfl
  rw [hgys]
  -- Naturality of `c_n(Q)` and of `c_n(Z)` under the pullback along `pp`.
  rw [map_sub]
  rw [← Work.Thom.chernClass_comap (j := n) Q pp]
  rw [Work.Thom.CohMap_comp_apply pp (Work.LerayHirsch.projMap Z) ℤ (2 * n)
    (Work.Thom.chernClass (n + 1) n Z)]
  rw [← Work.Thom.chernClass_comap (m := n + 1) (j := n) Z
    ((Work.LerayHirsch.projMap Z).comp pp)]
  rw [← Work.Thom.bundleComap_comp Z (Work.LerayHirsch.projMap Z) pp]
  rw [key, sub_self]

end Work.Gen
