import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.alphaTwo_base_case
import Submission.Work.SSGRoute.PT.mapH2_zsmulHomEnd
import Submission.Work.SSGRoute.PT.resH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `(β)`: the corestriction on `H²` and the restriction–corestriction identity

The base case of the `α²`-dévissage (`PT.alphaTwo_coind_eq_cor`, file `alphaTwo_base_case.lean`)
reduces `α²(G, Coind^G_U M)` to `Hom(M^U, cor)` composed with `α²(U,M)`, where

  `cor = corH2 U hUo C : H²(U,C) →+ H²(G,C)`

is the corestriction.  The remaining input `(β)` is the non-degeneracy of `cor` for the local class
formation `(G_{k_v}, \bar k_v^×)` (Milne ADT (1.1b)), whose *provable* half — for coefficients of
exponent `p` and `p ∤ [G : U]` — is the classical restriction–corestriction argument

  `cor ∘ res = [G : U] · id`,   `p · (-) = 0`   ⟹   `cor` surjective, `res` injective.

This file proves exactly that.  The proof of the transfer identity reuses the `α²`-machinery
verbatim (`mapH2_comp`, `mapH2_congr_coeff`, `shapiroEquiv`, `trace`) and hinges on the
**orbit map** `coindOrbit U C : C →+ Coind^G_U C`, `c ↦ (x ↦ x⁻¹ • c`):

* it is `G`-equivariant (`isEquivariant_coindOrbit`),
* its value at `1` is `c`, whence `shapiroEquiv (mapH2 coindOrbit x) = resH2 x`
  (`shapiroEquiv_mapH2_coindOrbit`) — restriction is Shapiro of the orbit map,
* `trace ∘ coindOrbit = [G : U] · id` (`trace_coindOrbit`).

The *other* half of `(β)` (`cor` injective, equivalently `res ∘ cor = [G : U] · id`) needs a
computation with the explicit Shapiro lift `shapiroLift` (`PT/shapiro_H2_lift_defs.lean`); see the
docstring of `corH2_surjective_of_pTorsion_of_coprime` at the end of this file.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (U : Subgroup G)
  [U.FiniteIndex] [Fintype (G ⧸ U)]

/-! ## The orbit map `C →+ Coind^G_U C` -/

/-- **The orbit map** `c ↦ (x ↦ x⁻¹ • c)`, a `G`-equivariant map from a `G`-module into the
coinduced module.  Its value at `1` is `c`. -/
def coindOrbit (C : Type u) [AddCommGroup C] [DistribMulAction G C] : C →+ Coind G U C where
  toFun c := ⟨fun x => x⁻¹ • c, by
    intro g u
    show (g * (u : G))⁻¹ • c = u⁻¹ • (g⁻¹ • c)
    rw [mul_inv_rev, mul_smul, Subgroup.smul_def, Subgroup.coe_inv]⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    simp
  map_add' c c' := by
    apply Subtype.ext
    funext x
    simp only [Pi.add_apply, smul_add, AddSubgroup.coe_add]

@[simp] theorem coindOrbit_apply (C : Type u) [AddCommGroup C] [DistribMulAction G C]
    (c : C) (x : G) : (coindOrbit U C c : G → C) x = x⁻¹ • c := rfl

/-- The orbit map is `G`-equivariant. -/
theorem isEquivariant_coindOrbit (C : Type u) [AddCommGroup C] [DistribMulAction G C] :
    Work.GroupCohomology.IsEquivariant G (coindOrbit U C) := by
  intro g c
  apply Subtype.ext
  funext x
  show x⁻¹ • (g • c) = (g⁻¹ * x)⁻¹ • c
  rw [mul_inv_rev, mul_smul, inv_inv]

/-- **The trace of an orbit element is the index multiple**: `Σ_x x⁻¹ • c = [G : U] • c`. -/
theorem trace_coindOrbit (C : Type u) [AddCommGroup C] [DistribMulAction G C] (c : C) :
    trace U C (coindOrbit U C c) = (Nat.card (G ⧸ U)) • c := by
  rw [trace_apply]
  have h : ∀ q : G ⧸ U, secC U q • ((coindOrbit U C c : G → C) (secC U q)) = c := by
    intro q
    rw [coindOrbit_apply, ← mul_smul, mul_inv_cancel, one_smul]
  rw [Finset.sum_congr rfl (fun q _ => h q), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]

/-! ## Restriction is Shapiro of the orbit map -/

/-- **Restriction is Shapiro of the orbit map**: `shapiroEquiv (mapH2 coindOrbit x) = resH2 x`. -/
theorem shapiroEquiv_mapH2_coindOrbit (C : Type u) [AddCommGroup C] [DistribMulAction G C]
    (hUo : IsOpen (U : Set G)) (x : Work.AbsoluteKummer.H2 G C) :
    shapiroEquiv U hUo (M := C)
        (Work.AbsoluteKummer.mapH2 (coindOrbit U C) (isEquivariant_coindOrbit U C) x)
      = resH2 U x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G C).comap (Work.AbsoluteKummer.Z2 G C).subtype) x
  have hc' : Work.AbsoluteKummer.H2π G C c = x := hc
  rw [← hc', Work.AbsoluteKummer.mapH2_H2π, shapiroEquiv_H2π, resH2_H2π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨u, v⟩ := p
  show phiC U C ((Work.AbsoluteKummer.mapZ2 (coindOrbit U C)
      (isEquivariant_coindOrbit U C) c : Work.AbsoluteKummer.Z2 G (Coind G U C)) :
      G × G → Coind G U C) (u, v) = (c : G × G → C) ((u : G), (v : G))
  rw [phiC_apply, Work.AbsoluteKummer.mapZ2_apply, coindOrbit_apply, inv_one, one_smul]

/-! ## `mapH2` of a scalar multiple -/

/-- `mapH2` of the multiplication-by-`n` coefficient map is multiplication by `n` on `H²`. -/
theorem mapH2_nsmulHom_eq {G : Type u} [TopologicalSpace G] [Group G] {C : Type u}
    [AddCommGroup C] [DistribMulAction G C] (n : ℕ)
    (h : Work.GroupCohomology.IsEquivariant G (nsmulHom n C))
    (y : Work.AbsoluteKummer.H2 G C) :
    Work.AbsoluteKummer.mapH2 (nsmulHom n C) h y = n • y := by
  refine Work.AbsoluteKummer.SES.H2_induction_on y (C := fun z => _ = n • z) ?_
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π]
  have hmap : Work.AbsoluteKummer.mapZ2 (nsmulHom n C) h c = n • c := by
    refine Subtype.ext (funext (fun q => ?_))
    simp [Work.AbsoluteKummer.mapZ2_apply, nsmulHom_apply]
  rw [hmap, map_nsmul]

/-- `ℕ`-scalars commute with the action. -/
theorem nsmul_smul_comm {G : Type u} [Group G] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C] (n : ℕ) (g : G) (c : C) : n • (g • c) = g • (n • c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, smul_add]

/-- The multiplication-by-`n` coefficient map is equivariant. -/
theorem isEquivariant_nsmulHom {G : Type u} [Group G] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C] (n : ℕ) :
    Work.GroupCohomology.IsEquivariant G (nsmulHom n C) := by
  intro g c
  rw [nsmulHom_apply, nsmulHom_apply]
  exact nsmul_smul_comm n g c

/-! ## `(β)`: the restriction–corestriction identity and its consequences -/

/-- **The restriction–corestriction identity** `cor (res z) = [G : U] • z`. -/
theorem corH2_resH2 (hUo : IsOpen (U : Set G)) (C : Type u) [AddCommGroup C]
    [DistribMulAction G C] (z : Work.AbsoluteKummer.H2 G C) :
    corH2 U hUo C (resH2 U z) = (Nat.card (G ⧸ U)) • z := by
  have hs : (shapiroEquiv U hUo (M := C)).symm (resH2 U z)
      = Work.AbsoluteKummer.mapH2 (coindOrbit U C) (isEquivariant_coindOrbit U C) z := by
    rw [← shapiroEquiv_mapH2_coindOrbit U C hUo z]
    exact AddEquiv.symm_apply_apply _ _
  rw [corH2_apply, hs]
  have hcomp : (trace U C).comp (coindOrbit U C) = nsmulHom (Nat.card (G ⧸ U)) C := by
    apply AddMonoidHom.ext
    intro c
    rw [AddMonoidHom.comp_apply, trace_coindOrbit, nsmulHom_apply]
  rw [show Work.AbsoluteKummer.mapH2 (trace U C) (isEquivariant_trace U C)
        (Work.AbsoluteKummer.mapH2 (coindOrbit U C) (isEquivariant_coindOrbit U C) z)
      = Work.AbsoluteKummer.mapH2 ((trace U C).comp (coindOrbit U C))
          (Work.GroupCohomology.IsEquivariant.comp (isEquivariant_trace U C)
            (isEquivariant_coindOrbit U C)) z from
      (mapH2_comp (φ := coindOrbit U C) (ψ := trace U C) (isEquivariant_coindOrbit U C)
        (isEquivariant_trace U C) (Work.GroupCohomology.IsEquivariant.comp
          (isEquivariant_trace U C) (isEquivariant_coindOrbit U C)) z).symm]
  rw [show Work.AbsoluteKummer.mapH2 ((trace U C).comp (coindOrbit U C))
        (Work.GroupCohomology.IsEquivariant.comp (isEquivariant_trace U C)
          (isEquivariant_coindOrbit U C)) z
      = Work.AbsoluteKummer.mapH2 (nsmulHom (Nat.card (G ⧸ U)) C)
          (isEquivariant_nsmulHom (G := G) (C := C) (Nat.card (G ⧸ U))) z from
      congrArg (fun f => f z) (mapH2_congr_coeff
        (Work.GroupCohomology.IsEquivariant.comp (isEquivariant_trace U C)
          (isEquivariant_coindOrbit U C))
        (isEquivariant_nsmulHom (G := G) (C := C) (Nat.card (G ⧸ U))) hcomp)]
  exact mapH2_nsmulHom_eq (Nat.card (G ⧸ U)) _ z

/-- **Coefficients of exponent `p` make `H²` killed by `p`.** -/
theorem p_smul_H2_eq_zero {G : Type u} [TopologicalSpace G] [Group G] {C : Type u}
    [AddCommGroup C] [DistribMulAction G C] (p : ℕ) (hexp : ∀ c : C, p • c = 0)
    (y : Work.AbsoluteKummer.H2 G C) : p • y = 0 := by
  refine Work.AbsoluteKummer.SES.H2_induction_on y (C := fun z => p • z = 0) ?_
  intro c
  have hzero : (p • c : Work.AbsoluteKummer.Z2 G C) = 0 :=
    Subtype.ext (funext (fun q => hexp ((c : G × G → C) q)))
  rw [← map_nsmul, hzero, map_zero]

/-- **Bézout.** An element of an abelian group killed by `p` and by `n`, with `n` coprime to `p`,
is zero. -/
theorem eq_zero_of_pTorsion_of_coprime {A : Type u} [AddCommGroup A] {p : ℕ} {x : A}
    (hpx : p • x = 0) {n : ℕ} (hn : n.Coprime p) (hnx : n • x = 0) : x = 0 := by
  have hbez := Nat.gcd_eq_gcd_ab n p
  have hgcd : (Nat.gcd n p : ℤ) = 1 := by rw [hn.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA n p : ℤ) * (n : ℤ) + (Nat.gcdB n p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA n p) (n : ℤ), mul_comm (Nat.gcdB n p) (p : ℤ)]
    exact hbez.symm
  have hx : x = (Nat.gcdA n p * (n : ℤ) + Nat.gcdB n p * (p : ℤ)) • x := by
    rw [hbez', one_smul]
  rw [hx, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hnx, hpx, smul_zero,
    smul_zero, add_zero]

/-! ## `(β)` for coefficients of exponent `p` and index prime to `p`

`cor ∘ res = [G : U] · id` together with `p · (-) = 0` gives the *provable* half of `(β)`: the
corestriction is onto and the restriction is injective, whenever the coefficients have exponent `p`
and `p ∤ [G : U]`.

The dual identity `res ∘ cor = [G : U] · id` (equivalently the injectivity of `cor`, which is the
remaining half of `(β)`) is *not* proved here: it needs a cocycle computation with the explicit
Shapiro lift `shapiroLift` (`PT/shapiro_H2_lift_defs.lean`), whose restriction to `U × U` is the
cochain `(u,v) ↦ (x ↦ coord x • a (A u (xU), A v (u⁻¹ • xU)))`; the claim is that this is
cohomologous to `mapH2 coindOrbit` of `a`, whence `res (cor y) = [G : U] • y`. -/

/-- **(β), surjectivity half**: for coefficients of exponent `p` and `p ∤ [G : U]`, the
corestriction `H²(U,C) →+ H²(G,C)` is surjective. -/
theorem corH2_surjective_of_pTorsion_of_coprime (hUo : IsOpen (U : Set G))
    (C : Type u) [AddCommGroup C] [DistribMulAction G C] (p : ℕ) [Fact p.Prime]
    (hexp : ∀ c : C, p • c = 0) (hcop : (Nat.card (G ⧸ U)).Coprime p) :
    Function.Surjective (corH2 U hUo C) := by
  intro z
  have hz : (Nat.card (G ⧸ U)) • z = corH2 U hUo C (resH2 U z) :=
    (corH2_resH2 U hUo C z).symm
  have hpz : p • z = 0 := p_smul_H2_eq_zero p hexp z
  have hbez := Nat.gcd_eq_gcd_ab (Nat.card (G ⧸ U)) p
  have hgcd : (Nat.gcd (Nat.card (G ⧸ U)) p : ℤ) = 1 := by rw [hcop.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) * (Nat.card (G ⧸ U) : ℤ)
      + (Nat.gcdB (Nat.card (G ⧸ U)) p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA (Nat.card (G ⧸ U)) p) (Nat.card (G ⧸ U) : ℤ),
      mul_comm (Nat.gcdB (Nat.card (G ⧸ U)) p) (p : ℤ)]
    exact hbez.symm
  have hcomb : ((Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) * (Nat.card (G ⧸ U) : ℤ)
      + (Nat.gcdB (Nat.card (G ⧸ U)) p : ℤ) * (p : ℤ)) • z = z := by
    rw [hbez', one_smul]
  have hgoal : (Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) • corH2 U hUo C (resH2 U z) = z := by
    conv_rhs => rw [← hcomb]
    rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ← hz, hpz,
      smul_zero, add_zero]
  exact ⟨(Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) • resH2 U z, by rw [map_zsmul, hgoal]⟩

/-- **(β), the `res`-half**: for coefficients of exponent `p` and `p ∤ [G : U]`, the restriction
`H²(G,C) →+ H²(U,C)` is injective. -/
theorem resH2_injective_of_pTorsion_of_coprime (hUo : IsOpen (U : Set G))
    (C : Type u) [AddCommGroup C] [DistribMulAction G C] (p : ℕ) [Fact p.Prime]
    (hexp : ∀ c : C, p • c = 0) (hcop : (Nat.card (G ⧸ U)).Coprime p) :
    Function.Injective (resH2 (U := U) : Work.AbsoluteKummer.H2 G C →+
      Work.AbsoluteKummer.H2 ↥U C) := by
  intro z z' h
  have hz : resH2 U (z - z') = 0 := by rw [map_sub, h, sub_self]
  have h1 : (Nat.card (G ⧸ U)) • (z - z') = 0 := by
    rw [← corH2_resH2 U hUo C (z - z'), hz, map_zero]
  have h2 : p • (z - z') = 0 := p_smul_H2_eq_zero p hexp _
  exact sub_eq_zero.mp (eq_zero_of_pTorsion_of_coprime h2 hcop h1)

end

end Work.SSGRoute.PT
