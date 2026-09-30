import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Alt.chartReading
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue
import Submission.Work.SpecLin.Core.chartSpecialisation
import Submission.Work.CurveBasics.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Setup

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option linter.style.haveILetI false

/-- **From a closed point of the special-fibre chart to the corresponding maximal ideal and the
order dictionary.**  Let `U ⊆ C` be a nonempty affine chart and `Q` a place of `C_κ` whose
underlying point lies in the chart `U_κ = C.bcOpens κ U` of the special fibre.  Then there is a
maximal ideal `N ⊇ P = 𝔪_R·(Γ(C,U) ⊗_K R)` of the relative chart ring such that the
"regularity dictionary"

`x = ρ_U a / ρ_U b` with `b ∉ N`  ⟺  `0 ≤ ord_Q x`

holds for every `x ∈ K(C_κ)`.  This is the converse direction of
`Work.SpecLin.Alt.exists_chartTensorFibrePoint`, and it is what allows the reading-off
`hReadW`/`hReadV` (stated for maximal ideals `N`) to be applied at an arbitrary place `Q` of
the chart. -/
theorem exists_maximalIdeal_of_place {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (U : C.left.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    (Q : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hQ : Q.point ∈ C.bcOpens (IsLocalRing.ResidueField R) U) :
    ∃ N : Ideal (Work.SpecLin.Core.chartTensor R U), N.IsMaximal ∧
      Work.SpecLin.Core.chartFibrePrime R U ≤ N ∧
      (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : Work.SpecLin.Core.chartTensor R U, b ∉ N ∧
            x * Work.SpecLin.Alt.chartTensorRedMap R U hU b
              = Work.SpecLin.Alt.chartTensorRedMap R U hU a)
          ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x Q) := by
  have hUaff : AlgebraicGeometry.IsAffineOpen
      (C.bcOpens (IsLocalRing.ResidueField R) U) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) U hU
  haveI : Nonempty (C.bcOpens (IsLocalRing.ResidueField R) U) := ⟨⟨Q.point, hQ⟩⟩
  let p : Ideal (Work.SpecLin.Alt.fibreSections R U) :=
    (hUaff.primeIdealOf ⟨Q.point, hQ⟩).asIdeal
  have hp : p.IsMaximal := hUaff.primeIdealOf_isMaximal_of_isClosed ⟨Q.point, hQ⟩ Q.isClosed
  let ψ : Work.SpecLin.Core.chartTensor R U →+* Work.SpecLin.Alt.fibreSections R U :=
    Work.SpecLin.Alt.chartTensorRedSectionsMap R U hU
  have hψsurj : Function.Surjective ψ :=
    Work.SpecLin.Alt.chartTensorRedSectionsMap_surjective R U hU
  let N : Ideal (Work.SpecLin.Core.chartTensor R U) := Ideal.comap ψ p
  have hNmax : N.IsMaximal := by
    haveI : p.IsMaximal := hp
    exact Ideal.comap_isMaximal_of_surjective ψ hψsurj
  have hPN : Work.SpecLin.Core.chartFibrePrime R U ≤ N := by
    rw [← Work.SpecLin.Alt.ker_chartTensorRedSectionsMap R U hU, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  refine ⟨N, hNmax, hPN, ?_⟩
  intro x
  rw [Work.SpecLin.Alt.image_fractionSet_map_of_surjective ψ hψsurj N ?_ _ _
    (fun a => rfl) x]
  · rw [show Ideal.map ψ N = p from Ideal.map_comap_of_surjective ψ hψsurj p]
    exact Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
      (C.bcOpens (IsLocalRing.ResidueField R) U) hUaff Q hQ x
  · exact (le_of_eq (Work.SpecLin.Alt.ker_chartTensorRedSectionsMap R U hU)).trans hPN

/-- **The two chart readings of `h` agree on the special fibre.**  Let `W`, `V` be two nonempty
affine charts of `C`, let `h ∈ K(C_F)` be the quotient `φ_W aW / φ_W bW = φ_V aV / φ_V bV`
witnessed by `habW`, `habV`, and let `bW`, `bV` be regular modulo the fibre primes.  Then the
reductions `ρ_W(aW)/ρ_W(bW)` and `ρ_V(aV)/ρ_V(bV)` are equal in `K(C_κ)`.

The proof restricts the identity `φ_W aW · φ_V bV = φ_W bW · φ_V aV` of `K(C_F)` to the smaller
affine open `W ∩ V` (`chartTensorMap_restrict`), uses that the chart dictionary is injective, and
applies the reduction map (`chartTensorRedMap_restrict`). -/
theorem chartTensorRedMap_div_eq_of_chartTensorMap_eq {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W V : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (hV : AlgebraicGeometry.IsAffineOpen V) [Nonempty W] [Nonempty V]
    (h : (C.baseChange (FractionRing R)).functionField)
    (aW bW : Work.SpecLin.Core.chartTensor R W)
    (aV bV : Work.SpecLin.Core.chartTensor R V)
    (hbW : bW ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (hbV : bV ∉ Work.SpecLin.Core.chartFibrePrime R V)
    (habW : h * Work.SpecLin.Alt.chartTensorMap R W hW bW
        = Work.SpecLin.Alt.chartTensorMap R W hW aW)
    (habV : h * Work.SpecLin.Alt.chartTensorMap R V hV bV
        = Work.SpecLin.Alt.chartTensorMap R V hV aV) :
    Work.SpecLin.Alt.chartTensorRedMap R W hW aW
        * (Work.SpecLin.Alt.chartTensorRedMap R W hW bW)⁻¹
      = Work.SpecLin.Alt.chartTensorRedMap R V hV aV
        * (Work.SpecLin.Alt.chartTensorRedMap R V hV bV)⁻¹ := by
  haveI : C.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from C.hom]
    infer_instance
  let Z : C.left.Opens := W ⊓ V
  have hZaff : AlgebraicGeometry.IsAffineOpen Z := hW.inf hV
  haveI : Nonempty Z := by
    have hWn : Nonempty W := inferInstance
    have hVn : Nonempty V := inferInstance
    obtain ⟨w, hw⟩ := hWn
    obtain ⟨v, hv⟩ := hVn
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter W.isOpen V.isOpen ⟨w, hw⟩ ⟨v, hv⟩
    exact ⟨⟨x, hx⟩⟩
  have hZW : Z ≤ W := inf_le_left
  have hZV : Z ≤ V := inf_le_right
  have hcross : Work.SpecLin.Alt.chartTensorMap R W hW aW
        * Work.SpecLin.Alt.chartTensorMap R V hV bV
      = Work.SpecLin.Alt.chartTensorMap R W hW bW
        * Work.SpecLin.Alt.chartTensorMap R V hV aV := by
    calc Work.SpecLin.Alt.chartTensorMap R W hW aW
            * Work.SpecLin.Alt.chartTensorMap R V hV bV
        = (h * Work.SpecLin.Alt.chartTensorMap R W hW bW)
            * Work.SpecLin.Alt.chartTensorMap R V hV bV := by rw [habW]
      _ = h * (Work.SpecLin.Alt.chartTensorMap R W hW bW
            * Work.SpecLin.Alt.chartTensorMap R V hV bV) := by ring
      _ = h * (Work.SpecLin.Alt.chartTensorMap R V hV bV
            * Work.SpecLin.Alt.chartTensorMap R W hW bW) := by ring
      _ = (h * Work.SpecLin.Alt.chartTensorMap R V hV bV)
            * Work.SpecLin.Alt.chartTensorMap R W hW bW := by ring
      _ = Work.SpecLin.Alt.chartTensorMap R V hV aV
            * Work.SpecLin.Alt.chartTensorMap R W hW bW := by rw [habV]
      _ = Work.SpecLin.Alt.chartTensorMap R W hW bW
            * Work.SpecLin.Alt.chartTensorMap R V hV aV := by ring
  have hcrossZ : Work.SpecLin.Alt.chartTensorMap R Z hZaff
        (Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZW aW
          * Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZV bV)
      = Work.SpecLin.Alt.chartTensorMap R Z hZaff
        (Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZW bW
          * Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZV aV) := by
    rw [map_mul, map_mul, Work.SpecLin.Core.chartTensorMap_restrict,
      Work.SpecLin.Core.chartTensorMap_restrict,
      Work.SpecLin.Core.chartTensorMap_restrict,
      Work.SpecLin.Core.chartTensorMap_restrict]
    exact hcross
  letI : Algebra (Work.SpecLin.Core.chartTensor R Z)
      (C.baseChange (FractionRing R)).functionField :=
    (Work.SpecLin.Alt.chartTensorMap R Z hZaff).toAlgebra
  haveI hfr : IsFractionRing (Work.SpecLin.Core.chartTensor R Z)
      (C.baseChange (FractionRing R)).functionField :=
    Work.SpecLin.Alt.chartTensorMap_isFractionRing R Z hZaff
  have hinj : Function.Injective (Work.SpecLin.Alt.chartTensorMap R Z hZaff) :=
    IsFractionRing.injective _ _
  have hZeq : Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZW aW
        * Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZV bV
      = Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZW bW
        * Work.SpecLin.Core.chartRestrict (K := K) (C := C) R hZV aV := hinj hcrossZ
  have hred : Work.SpecLin.Alt.chartTensorRedMap R W hW aW
        * Work.SpecLin.Alt.chartTensorRedMap R V hV bV
      = Work.SpecLin.Alt.chartTensorRedMap R W hW bW
        * Work.SpecLin.Alt.chartTensorRedMap R V hV aV := by
    have h2 := congrArg (Work.SpecLin.Alt.chartTensorRedMap R Z hZaff) hZeq
    rw [map_mul, map_mul, Work.SpecLin.Core.chartTensorRedMap_restrict,
      Work.SpecLin.Core.chartTensorRedMap_restrict,
      Work.SpecLin.Core.chartTensorRedMap_restrict,
      Work.SpecLin.Core.chartTensorRedMap_restrict] at h2
    exact h2
  have hbW0 : Work.SpecLin.Alt.chartTensorRedMap R W hW bW ≠ 0 :=
    Work.SpecLin.Alt.chartTensorRedMap_ne_zero_of_notMem R W hW hbW
  have hbV0 : Work.SpecLin.Alt.chartTensorRedMap R V hV bV ≠ 0 :=
    Work.SpecLin.Alt.chartTensorRedMap_ne_zero_of_notMem R V hV hbV
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hbW0 hbV0]
  exact hred.trans (mul_comm _ _)


/-- **Globalisation of the affine-chart reading-off to the whole special fibre.**

Two affine charts `W` (the given chart) and `V` of the curve `C` with `C = W ∪ V` cover the
special fibre (`C_κ = W_κ ∪ V_κ`), both containing the images of the sections.  Suppose that in
each of the two charts, at every closed point `z` of the chart (encoded by a maximal ideal
`N ⊇ P = 𝔪_R·B` and the order dictionary `hz`), the order of vanishing of the reduction of `h`
agrees with the difference `E = Σ_m ptDiv(s̄_m) − Σ_m ptDiv(t̄_m)` of the special fibres of the
sections (`hReadW`, `hReadV` — the conclusion of `Work.SpecLin.Setup.localOrderPull`, which
states it with cardinals `#{m : I_m ⊔ P = N}`; the two differ by
`Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue`, which the caller uses).

Then the divisors are linearly equivalent, i.e. `LinEquiv C (Σ_m ptDiv s̄_m) (Σ_m ptDiv t̄_m)`.

Route: the `V`-chart reading-off is applied to an element `h̄_V := ρ_V(aV)/ρ_V(bV)` of `K(C_κ)`;
to compare it with `h̄_W := ρ_W(aW)/ρ_W(bW)` use the two compatibilities of the chart dictionary
with restriction to the smaller affine open `W ∩ V`
(`Work.CurveBasics.Curve.chartTensorRedMap_restrict`, `…chartTensorMap_restrict` in
`SpecLin/Core/chartSpecialisation`): `h * φ_W bW = φ_W aW` and `h * φ_V bV = φ_V aV` become
`res aW · res bV = res bW · res aV` in `B_{W∩V}` after restricting, hence
`ρ_W(aW)·ρ_V(bV) = ρ_W(bW)·ρ_V(aV)` in `K(C_κ)`, i.e. `h̄_W = h̄_V`.  Then `h̄ := h̄_W` has the
prescribed divisor: on `W_κ` by `hReadW`, and on `V_κ` because there `h̄_W = h̄_V` and `hReadV`
applies.  To convert `hReadW`/`hReadV` (stated for maximal ideals `N` and the corresponding
`z`) into a statement about every closed point `Q` of the chart, one takes for `N` the preimage
in `B` of the prime `(hU).primeIdealOf Q` of the chart ring `B ⧸ P = Γ(W_κ)` and proves the
order dictionary via `exists_mul_eq_iff_ordAt_of_primeIdealOf`
(`SpecLin/Alt/exists_mul_eq_iff_ordAt_of_primeIdealOf`) together with
`image_fractionSet_map_of_surjective` and the surjectivity of `chartTensorRedSectionsMap` with
kernel `P`. -/
theorem globalStepPull {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W V : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (hV : AlgebraicGeometry.IsAffineOpen V) [Nonempty W] [Nonempty V]
    (hcover : ∀ x : C.left, x ∉ W → x ∈ V)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hVs : ∀ m, Set.range (s m).left.base ⊆ (V : Set C.left))
    (hVt : ∀ m, Set.range (t m).left.base ⊆ (V : Set C.left))
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))))
    (aW bW : Work.SpecLin.Core.chartTensor R W)
    (haW : aW ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (hbW : bW ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (habW : h * Work.SpecLin.Alt.chartTensorMap R W hW bW
        = Work.SpecLin.Alt.chartTensorMap R W hW aW)
    (aV bV : Work.SpecLin.Core.chartTensor R V)
    (haV : aV ∉ Work.SpecLin.Core.chartFibrePrime R V)
    (hbV : bV ∉ Work.SpecLin.Core.chartFibrePrime R V)
    (habV : h * Work.SpecLin.Alt.chartTensorMap R V hV bV
        = Work.SpecLin.Alt.chartTensorMap R V hV aV)
    (hReadW : ∀ (N : Ideal (Work.SpecLin.Core.chartTensor R W)), N.IsMaximal →
      Work.SpecLin.Core.chartFibrePrime R W ≤ N →
      ∀ (z : (C.baseChange (IsLocalRing.ResidueField R)).Place),
        (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
          (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ N ∧
              x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
                = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
            ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) →
        (C.baseChange (IsLocalRing.ResidueField R)).ordAt
          (Work.SpecLin.Alt.chartTensorRedMap R W hW aW
            * (Work.SpecLin.Alt.chartTensorRedMap R W hW bW)⁻¹) z
          = ((Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (s m)))
              - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (t m)))) z)
    (hReadV : ∀ (N : Ideal (Work.SpecLin.Core.chartTensor R V)), N.IsMaximal →
      Work.SpecLin.Core.chartFibrePrime R V ≤ N →
      ∀ (z : (C.baseChange (IsLocalRing.ResidueField R)).Place),
        (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
          (∃ a b : Work.SpecLin.Core.chartTensor R V, b ∉ N ∧
              x * Work.SpecLin.Alt.chartTensorRedMap R V hV b
                = Work.SpecLin.Alt.chartTensorRedMap R V hV a)
            ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) →
        (C.baseChange (IsLocalRing.ResidueField R)).ordAt
          (Work.SpecLin.Alt.chartTensorRedMap R V hV aV
            * (Work.SpecLin.Alt.chartTensorRedMap R V hV bV)⁻¹) z
          = ((Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (s m)))
              - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
                (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
                  (IsLocalRing.ResidueField R)) (t m)))) z) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
          (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
          (IsLocalRing.ResidueField R)) (t m))) := by
  classical
  let hbarW : (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    Work.SpecLin.Alt.chartTensorRedMap R W hW aW
      * (Work.SpecLin.Alt.chartTensorRedMap R W hW bW)⁻¹
  have hbarW0 : hbarW ≠ 0 := by
    apply mul_ne_zero
    · exact Work.SpecLin.Alt.chartTensorRedMap_ne_zero_of_notMem R W hW haW
    · exact inv_ne_zero (Work.SpecLin.Alt.chartTensorRedMap_ne_zero_of_notMem R W hW hbW)
  have hcompat : hbarW = Work.SpecLin.Alt.chartTensorRedMap R V hV aV
      * (Work.SpecLin.Alt.chartTensorRedMap R V hV bV)⁻¹ :=
    chartTensorRedMap_div_eq_of_chartTensorMap_eq R W V hW hV h aW bW aV bV hbW hbV habW habV
  refine ⟨hbarW, hbarW0, ?_⟩
  ext Q
  rw [Work.CurveBasics.Curve.div_apply, Finsupp.sub_apply]
  by_cases hmem : Q.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W
  · obtain ⟨N, hNmax, hPN, hz⟩ := exists_maximalIdeal_of_place R W hW Q hmem
    simpa only [Finsupp.sub_apply] using hReadW N hNmax hPN Q hz
  · have hmemV : Q.point ∈ C.bcOpens (IsLocalRing.ResidueField R) V :=
      hcover ((C.baseChangeFst (IsLocalRing.ResidueField R)) Q.point)
        (fun hw => hmem hw)
    obtain ⟨N, hNmax, hPN, hz⟩ := exists_maximalIdeal_of_place R V hV Q hmemV
    have hres := hReadV N hNmax hPN Q hz
    rw [hcompat]
    simpa only [Finsupp.sub_apply] using hres


end Work.SpecLin.Setup
