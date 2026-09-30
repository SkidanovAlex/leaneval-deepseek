import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.exists_normalized_chartTensorMap
import Submission.Work.SpecLin.Alt.exists_isAffineOpen_containing_pts
import Submission.Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue
import Submission.Work.SpecLin.Setup.finite_compl_affineOpen
import Submission.Work.SpecLin.Setup.sectionEquationPull
import Submission.Work.SpecLin.Setup.localOrderPull
import Submission.Work.SpecLin.Setup.exists_representation_of_other_chart
import Submission.Work.SpecLin.Setup.globalStepPull
import Submission.Work.SpecLin.Setup.cruxChartPull

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Setup

universe u

/-- **Specialisation of linear equivalence over a valuation ring, affine-chart case.**

`R` is a `K`-valuation ring, `W ⊆ C` an affine open of the curve containing the images of the
`R`-points `s m`, `t m`, and `h ≠ 0` on `C_F` (`F = FractionRing R`) has
`div h = Σ_m [s_m^F] − Σ_m [t_m^F]` on `C_F`, where `[p] = Work.SpecLin.ptDiv p` and
`p^F = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R F) p` is the generic fibre of the
`R`-point `p`.  Then the divisors `Σ_m [s̄_m]` and `Σ_m [t̄_m]` of the special fibres on `C_κ`
(`κ = ResidueField R`) are linearly equivalent.

The proof is the assembly recorded in the docstring of the file's earlier version:

* content-normalise `h` to `h' = a_W/b_W` (`a_W, b_W ∉ P_W = chartFibrePrime R W`) with
  `div h' = div h` (`Work.SpecLin.Alt.exists_normalized_chartTensorMap`);
* pick a second affine chart `V` covering `C ∖ W` and the images of all the points
  (`Work.SpecLin.Setup.finite_compl_affineOpen` plus `Work.SpecLin.Alt.affineOpenContaining_sorryFree`),
  and transfer the presentation of `h'` to `V` (`Work.SpecLin.Setup.exists_representation_of_other_chart`);
* in each chart, at every maximal ideal `N ⊇ P` (a closed point `z` of the special fibre) with the
  order dictionary `hz`, read off the order of the reduction by
  `Work.SpecLin.Setup.localOrderPull` (whose inputs are
  `Work.SpecLin.Setup.sectionEquationPull` for the local equations of the section ideals and
  `Work.SpecLin.Setup.cruxChartPull` for the crux);
* convert the filter cardinalities produced by `localOrderPull` into the `ptDiv` form using
  `Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue` and `Work.SpecLin.ptDiv_apply`;
* globalise with `Work.SpecLin.Setup.globalStepPull`. -/
theorem chartCoreDivPull {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (t m))) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simpa using Work.SpecLin.linEquiv_refl C
      (0 : Work.SpecLin.Dv C (IsLocalRing.ResidueField R))
  -- `0 < n`: the given chart is nonempty because it contains the image of `s 0`
  haveI hWne : Nonempty W :=
    ⟨⟨(s ⟨0, hnpos⟩).left.base (IsLocalRing.closedPoint R),
      hs ⟨0, hnpos⟩ ⟨IsLocalRing.closedPoint R, rfl⟩⟩⟩
  haveI hWdom : IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    Work.SpecLin.Core.isDomain_chartTensor (K := K) (C := C) R W hW
  -- content normalisation of `h` in the chart `W`
  obtain ⟨h', aW, bW, hh', haW, hbW, hdiv', habW⟩ :=
    Work.SpecLin.Alt.exists_normalized_chartTensorMap (K := K) (C := C) R W hW h hh
  have hdivW : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))) := by
    rw [hdiv', hdiv]
  -- a second affine chart containing `C ∖ W` and the images of all the points
  have hpairS : ∀ m : Fin n, (Set.range (s m).left.base).Finite := fun m =>
    ((Set.finite_singleton ((s m).left.base (IsLocalRing.closedPoint R))).insert
      (genericPoint C.left)).subset (Work.SpecLin.Alt.range_base_subset_pair R (s m))
  have hpairT : ∀ m : Fin n, (Set.range (t m).left.base).Finite := fun m =>
    ((Set.finite_singleton ((t m).left.base (IsLocalRing.closedPoint R))).insert
      (genericPoint C.left)).subset (Work.SpecLin.Alt.range_base_subset_pair R (t m))
  have hSfin : (((W : Set C.left)ᶜ) ∪ (⋃ m : Fin n, Set.range (s m).left.base)
      ∪ (⋃ m : Fin n, Set.range (t m).left.base)).Finite :=
    ((Work.SpecLin.Setup.finite_compl_affineOpen C W hW).union
      (Set.finite_iUnion hpairS)).union (Set.finite_iUnion hpairT)
  obtain ⟨V, hV, hSV⟩ :=
    Work.SpecLin.Alt.affineOpenContaining_sorryFree C
      (((W : Set C.left)ᶜ) ∪ (⋃ m : Fin n, Set.range (s m).left.base)
        ∪ (⋃ m : Fin n, Set.range (t m).left.base)) hSfin
  have hcover : ∀ x : C.left, x ∉ W → x ∈ V := fun x hx => hSV (Or.inl (Or.inl hx))
  have hVs : ∀ m, Set.range (s m).left.base ⊆ (V : Set C.left) := fun m y hy =>
    hSV (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨m, hy⟩)))
  have hVt : ∀ m, Set.range (t m).left.base ⊆ (V : Set C.left) := fun m y hy =>
    hSV (Or.inr (Set.mem_iUnion.mpr ⟨m, hy⟩))
  haveI hVne : Nonempty V :=
    ⟨⟨(s ⟨0, hnpos⟩).left.base (IsLocalRing.closedPoint R), hVs ⟨0, hnpos⟩ ⟨_, rfl⟩⟩⟩
  haveI hVdom : IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R V) :=
    Work.SpecLin.Core.isDomain_chartTensor (K := K) (C := C) R V hV
  -- transfer the presentation of `h'` to the chart `V`
  obtain ⟨aV, bV, haV, hbV, habV⟩ :=
    Work.SpecLin.Setup.exists_representation_of_other_chart R W V hW hV aW bW haW hbW h' hh' habW
  -- the reading-off in a chart, with the filter cardinalities converted to `ptDiv`
  have hread : ∀ (U : C.left.Opens) (hU : IsAffineOpen U) (hUne : Nonempty U)
      (hUdom : IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U))
      (hUs : ∀ m, Set.range (s m).left.base ⊆ (U : Set C.left))
      (hUt : ∀ m, Set.range (t m).left.base ⊆ (U : Set C.left))
      (a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
      (ha : a ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U)
      (hb : b ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U)
      (hab : h' * Work.SpecLin.Alt.chartTensorMap R U hU b
        = Work.SpecLin.Alt.chartTensorMap R U hU a),
      ∀ (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)), N.IsMaximal →
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U ≤ N →
      ∀ (z : (C.baseChange (IsLocalRing.ResidueField R)).Place),
        (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
          (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R U, b ∉ N ∧
              x * Work.SpecLin.Alt.chartTensorRedMap R U hU b
                = Work.SpecLin.Alt.chartTensorRedMap R U hU a)
            ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) →
        (C.baseChange (IsLocalRing.ResidueField R)).ordAt
          (Work.SpecLin.Alt.chartTensorRedMap R U hU a
            * (Work.SpecLin.Alt.chartTensorRedMap R U hU b)⁻¹) z
          = ((Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (s m)))
              - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (t m)))) z := by
    intro U hU hUne hUdom hUs hUt a b ha hb hab N hN hPN z hz
    haveI : Nonempty U := hUne
    haveI : IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U) := hUdom
    haveI : N.IsMaximal := hN
    -- local equations of the section ideals at `N`
    have eqS : ∀ m : Fin n, ∃ f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R U,
        f ∈ Work.SpecLin.Core.sectionPrime R U
              (Work.SpecLin.Core.rgMap R U hU (s m) (hUs m)) ∧
        f ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U ∧
        (Work.SpecLin.Core.sectionPrime R U
            (Work.SpecLin.Core.rgMap R U hU (s m) (hUs m))).map
          (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
            (Localization.AtPrime N))
          = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
              (Localization.AtPrime N) f)) ∧
        (∀ p : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U),
          p.IsPrime → p ≤ N →
          (Work.SpecLin.Alt.IsUnitAt (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
              (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)) f) p
            ↔ ¬ (Work.SpecLin.Core.sectionPrime R U
                  (Work.SpecLin.Core.rgMap R U hU (s m) (hUs m)) ≤ p))) :=
      fun m => Work.SpecLin.Setup.sectionEquationPull R U hU (s m) (hUs m) N hN hPN
    have eqT : ∀ m : Fin n, ∃ f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R U,
        f ∈ Work.SpecLin.Core.sectionPrime R U
              (Work.SpecLin.Core.rgMap R U hU (t m) (hUt m)) ∧
        f ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U ∧
        (Work.SpecLin.Core.sectionPrime R U
            (Work.SpecLin.Core.rgMap R U hU (t m) (hUt m))).map
          (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
            (Localization.AtPrime N))
          = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
              (Localization.AtPrime N) f)) ∧
        (∀ p : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U),
          p.IsPrime → p ≤ N →
          (Work.SpecLin.Alt.IsUnitAt (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)
              (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R U)) f) p
            ↔ ¬ (Work.SpecLin.Core.sectionPrime R U
                  (Work.SpecLin.Core.rgMap R U hU (t m) (hUt m)) ≤ p))) :=
      fun m => Work.SpecLin.Setup.sectionEquationPull R U hU (t m) (hUt m) N hN hPN
    have hmain : (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (Work.SpecLin.Alt.chartTensorRedMap R U hU a
          * (Work.SpecLin.Alt.chartTensorRedMap R U hU b)⁻¹) z
        = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R U
                (Work.SpecLin.Core.rgMap R U hU (s m) (hUs m)) ⊔
                  Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U = N)).card : ℤ)
          - ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R U
                (Work.SpecLin.Core.rgMap R U hU (t m) (hUt m)) ⊔
                  Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U = N)).card : ℤ) :=
      Work.SpecLin.Setup.localOrderPull R U hU s t hUs hUt h' hh' hdivW a b ha hb hab
        N hN hPN eqS eqT
        (fun v hv hP hht => Work.SpecLin.Setup.cruxChartPull R U hU N hN hPN v hv hP hht) z hz
    rw [hmain]
    rw [Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
    congr 1
    · rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Work.SpecLin.ptDiv_apply]
      by_cases hm : Work.SpecLin.Core.sectionPrime R U
            (Work.SpecLin.Core.rgMap R U hU (s m) (hUs m)) ⊔
              Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U = N
      · rw [if_pos ((Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue R U hU
            (s m) (hUs m) N hPN z hz).mp hm), if_pos hm]
      · rw [if_neg (fun hc => hm ((Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue R U hU
            (s m) (hUs m) N hPN z hz).mpr hc)), if_neg hm]
    · rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Work.SpecLin.ptDiv_apply]
      by_cases hm : Work.SpecLin.Core.sectionPrime R U
            (Work.SpecLin.Core.rgMap R U hU (t m) (hUt m)) ⊔
              Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R U = N
      · rw [if_pos ((Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue R U hU
            (t m) (hUt m) N hPN z hz).mp hm), if_pos hm]
      · rw [if_neg (fun hc => hm ((Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue R U hU
            (t m) (hUt m) N hPN z hz).mpr hc)), if_neg hm]
  exact Work.SpecLin.Setup.globalStepPull R W V hW hV hcover s t hVs hVt h' hh' hdivW
    aW bW haW hbW habW aV bV haV hbV habV
    (fun N hN hPN => hread W hW hWne hWdom hs ht aW bW haW hbW habW N hN hPN)
    (fun N hN hPN => hread V hV hVne hVdom hVs hVt aV bV haV hbV habV N hN hPN)

end Work.SpecLin.Setup
