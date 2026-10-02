import Submission.Work.Cohomology.pd_us_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The splitting of a killed class over a two-piece cover

See `Submission/Work/Cohomology/sphere_split_plan.md` for the plan.

This file proves `Work.Cohomology.pd_union_split`.

## The proof, in outline

Let `W = U ∪ V`, `X = TopCat.of W`, `K = K₁`, `L = K₂`, and suppose that
`x ∈ H^k(X, X∖(K∪L))` satisfies `goodD N c W (K∪L) x = 0`.  Writing `A₁ = pdRelSub W K`,
`A₂ = pdRelSub W L` (so that `A₁ ∩ A₂ = pdRelSub W (K∪L)`), the goal is to enlarge `K, L` so that
`enl x` lies in the image of the difference map of the `A+B` sequence, equivalently (by exactness)
that `δ(enl x) = 0`.

* `pd_split_setup` produces a cocycle `φ` representing `x` and a lift `φ = φA - φB` with
  `φA ∈ C^*(X,A₁)`, `φB ∈ C^*(X,A₂)`.  Then `ψ := dφA ∈ pdABCoh X A₁ A₂` represents `δ x`.
* `pd_hatcher_data` (in `M`) produces the four-piece decomposition of a cycle representing `c`;
  `pd_hatcher_Xdata` transports the three pieces to `C_*(X)` and produces the W-relative cycle
  `γX` representing `localFundClass N c W (K∪L)`, while `pd_hatcher_inter4` produces the
  corresponding data in `U ∩ V`.
* `goodD_homologyπ` + `relCapPairZ_iCycles_apply` + `pd_boundary_of_zero_class` turn
  `goodD x = 0` into the hypothesis `∃β, dβ = cap φ (mj+1) (α₁X+α₂X+α₃X)` of the crux.
* `pd_union_crux_zero_wk` (the crux chain identity with the weak boundary hypothesis
  `d(α₁+α₂+α₃) ∈ Kᶜ`) produces `γ` supported in `U ∩ V` with
  `dγ = (-1)^(k+1) • cap ψ mj α₂X`.
* `pd_inter_cap_boundary` descends this to `U ∩ V`, which identifies `goodD N c (U∩V) w = 0`
  for the restriction `w` of `ψ`; `Good.kill` for `hII` then kills `w` after enlarging inside
  `U ∩ V`.
* Excision (`pdCohExcision`) transports the vanishing back to `C^*(X, X∖L'')`, and the
  quasi-isomorphism `pdABCoh_quasiIso` together with `pdABInclRel_comp_pdABEnlarge` turns it into
  `enl(δ x) = 0` in the enlarged `A+B` slot.
* Finally `pdABdelta_natural` identifies `δ(enl x)` with `enl(δ x)`, exactness
  (`pdAB_exact₃`) exhibits `x₁, x₂` with `enl x = enl x₁ - enl x₂`, and
  `pdABEnlarge`/`pdRelComplexEnlarge` are the maps of the statement.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem pd_union_split {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m)
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k)
    (hx : Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm x = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
        = (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ := by
  exact pd_us_main hU hV hI hUU hVV hII k m hkm hm hK₁U hK₂V hK₁c hK₂c x hx

end

end Work.Cohomology
