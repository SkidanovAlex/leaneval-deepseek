import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs
import Submission.Work.Motivic.cInv_add_pt
import Submission.Work.Motivic.cInv_add_trans
import Submission.Work.Motivic.wgt_exDiv_trans_add
import Submission.Work.Motivic.wgt_exDiv_symm_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

/-
# cInv_add — additivity of the Lin–Shinder invariant (paper Lemma 2.2)

## The statement
`cInv 𝕜 w φ = excCount 𝕜 w φ.symm − excCount 𝕜 w φ` (an `ℤ`-valued coefficient of the
invariant `c(φ)`), where
`excCount 𝕜 w φ = (Set.ncard {x | x ∈ exDiv φ ∧ ResEquiv 𝕜 x w} : ℕ)` and
`exDiv φ = {x | coheight x = 1 ∧ ¬ IsIsoAt φ x}`; `IsIsoAt φ x` means that some partial
isomorphism `i : X.PartialIso Y` with `x ∈ i.source` represents `φ`. All definitions are in
`Submission/Work/Motivic/Defs.lean`.

This is the groupoid form of additivity for arbitrary `𝕜`-varieties. `Work.Motivic.cInv_mul`
(being proved elsewhere, in parallel, as the special case `X=Y=Z=𝔸ⁿ`) is strictly weaker, so do
not try to derive this from it: prove the general statement directly.

## Proof route (combinatorial; no resolution of singularities, no normality, no projectivity)
For a birational `φ : X ⇢ Y` over `𝕜` define `π_φ` on coheight-one points by evaluating any partial
iso representing `φ` at `x`: `x ↦ φ(x)`, defined when `IsIsoAt φ x`. It is well defined because two
partial isos representing the same rational map agree on the intersection of their sources (targets
are separated and reduced — `Variety` gives this; Mathlib: `RationalMap.toPartialMap`,
`RationalMap.domain`, `PartialMap.equiv`). It is a bijection
`P1(X) ∖ Ex1(φ) ≅ P1(Y) ∖ Ex1(φ⁻¹)`, preserves `coheight = 1` and gives `ResEquiv 𝕜 x (π_φ x)`
for `φ` over `𝕜` (isomorphism of stalks/residue fields, `Scheme.Hom.stalkMap`, `Scheme.residue`,
`ResidueField.lean`).

Pointwise facts for `x` of coheight one, all partial isos over `𝕜`, `π = π_φ`:
 (F1) `IsIsoAt φ x` and `IsIsoAt ψ (π x)` ⇒ `IsIsoAt (φ.trans ψ) x` (compose partial isos);
 (F2) `IsIsoAt φ x` and `IsIsoAt (φ.trans ψ) x` ⇒ `IsIsoAt ψ (π x)` (locally `ψ = (ψφ) ∘ φ⁻¹`);
 (F3) `¬ IsIsoAt φ x` and `IsIsoAt (φ.trans ψ) x`, `z = ψφ(x)` ⇒ `¬ IsIsoAt ψ⁻¹ z` (else
      `φ = ψ⁻¹ ∘ (ψφ)` would be an iso at `x`) and `ResEquiv 𝕜 x z`.
Hence `π_{ψφ}` agrees with `π_ψ ∘ π_φ` on the common domain, plus "extra" pairs `(x,z)` with
`x ∈ Ex1(φ)`, `z ∈ Ex1(ψ⁻¹)`, `ResEquiv 𝕜 x z`.

Counting with the weight `wgt A = #{a ∈ A : ResEquiv 𝕜 a w}`:
 `wgt (Ex1(ψφ)) = excCount 𝕜 w φ + wgt (Ex1(ψ) ∩ Ran π_φ) − E`,
 `wgt (Ex1((ψφ)⁻¹)) = excCount 𝕜 w ψ⁻¹ + wgt (Ex1(φ⁻¹) ∩ Dom π_ψ) − E`,
where `E` is the weight of the extra pairs. Subtracting and using
`Ex1(ψ) ∖ Ran π_φ = Ex1(ψ) ∩ Ex1(φ⁻¹) = Ex1(φ⁻¹) ∖ Dom π_ψ` gives the result.

## Suggested decomposition (delegate the independent pieces!)
 (P0) every `BirationalMap` has a partial-iso representative: from `hom_comp_inv_id` and
      `inv_comp_hom_id`, restrict both to a dense open on which the composites are the identities;
 (P1) agreement of two partial isos representing the same rational map on the intersection of their
      sources, and well-definedness/`π`-functoriality of the point map;
 (P2) partial isomorphisms over `𝕜` preserve `coheight = 1` and `ResEquiv 𝕜`;
 (P3) `Ex1(φ)` is finite: `Ex(φ)` is closed (complement = union of the sources of all representing
      partial isos), `X` is a Noetherian space (`LocallyOfFiniteType.isLocallyNoetherian`,
      `IsNoetherian`, `Variety` gives finite type + quasicompact over a field), so `Ex(φ)` has
      finitely many irreducible components and each coheight-one point of `Ex(φ)` is the generic
      point of one of them (`NoetherianSpace.finite_irreducibleComponents`);
 (P4) finite-set bookkeeping with `Set.ncard` (`Set.ncard_union`, `Set.ncard_sdiff`,
      `Set.ncard_congr`), including that the weights are finite.

## Lean hints (learned the hard way — save yourself the time)
 * `Variety 𝕜 X` is a `Prop`-class whose *data* fields are `[over]`, `[isIntegral]`, `[isSeparated]`,
   ... They are registered as instances by `attribute [instance] Variety.over Variety.isIntegral`, so
   `[Variety 𝕜 X]` supplies `X.Over (Spec 𝕜)` and `IrreducibleSpace X` for free.
 * Instance-implicit *fields* of a plain `structure` (e.g. `PseudoRegularization.variety`,
   `PseudoRegularization.isOver_α`) are NOT registered as instances. If you have such a structure
   value `P`, write `letI : Variety 𝕜 P.X' := P.variety` (use `letI`, not `haveI`: `letI` is
   zeta-reduced during unification, which avoids "type mismatch: expected `Variety.over hv`,
   got `Variety.over P.variety`" errors) and pass `P.isOver_α` etc. explicitly.
 * `BirationalMap.trans`/`symm` are plain defs, so instance search does **not** unfold them: the
   instances `(f.trans g).IsOver S` and `f.symm.IsOver S` do not fire. Prove them yourself, e.g.
   `isOver_trans : f.IsOver S → g.IsOver S → (f.trans g).IsOver S` by
   `change (f.hom.comp g.hom).IsOver S; infer_instance`, and for `f.symm` by
   `change f.inv.IsOver S; infer_instance`.
 * `PartialIso.toBirationalMap` is likewise not unfolded by instance search; if you need
   `γ.toBirationalMap.IsOver S` from `γ.IsOver (X ↘ S) (Y ↘ S)`, prove it via
   `RationalMap.isOver_iff`/`PartialMap.isOver_iff` (the identity on the dense source gives the
   equivalence of partial maps).
 * `Set.ncard` returns `0` on infinite sets, so the finiteness (P3) is essential for the statement
   to be true.
-/
theorem cInv_add (𝕜 : Type) [Field 𝕜] {X Y Z W : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    [Variety 𝕜 Z] [W.Over (Spec (.of 𝕜))] (w : W) (φ : X.BirationalMap Y)
    (ψ : Y.BirationalMap Z) [φ.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] :
    cInv 𝕜 w (φ.trans ψ) = cInv 𝕜 w φ + cInv 𝕜 w ψ := by
  haveI hφs : (φ.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
  haveI hψs : (ψ.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (ψ.inv.IsOver (Spec (.of 𝕜)))
  simp only [cInv, excCount_eq_wgt]
  set x1 : ℕ := wgt 𝕜 w (exDiv (φ.trans ψ) ∩ exDiv φ) with hx1
  set x2 : ℕ := wgt 𝕜 w (exDiv ψ ∩ exDiv φ.symm) with hx2
  set x3 : ℕ := wgt 𝕜 w (exDiv ψ.symm ∩ exDiv ((φ.trans ψ).symm)) with hx3
  set R : ℕ := wgt 𝕜 w (exDiv (φ.trans ψ)) with hR
  set S : ℕ := wgt 𝕜 w (exDiv ((φ.trans ψ).symm)) with hS
  set P : ℕ := wgt 𝕜 w (exDiv φ) with hP
  set Pp : ℕ := wgt 𝕜 w (exDiv φ.symm) with hPp
  set Q : ℕ := wgt 𝕜 w (exDiv ψ) with hQ
  set Qp : ℕ := wgt 𝕜 w (exDiv ψ.symm) with hQp
  have hI : R + x2 = x1 + Q := by
    have h := wgt_exDiv_trans_add (𝕜 := 𝕜) w φ ψ
    rw [← hR, ← hx2, ← hx1, ← hQ] at h
    exact h
  have hII : P + x3 = x1 + Qp := by
    have h := wgt_exDiv_symm_add (𝕜 := 𝕜) w φ ψ
    rw [← hP, ← hx3, ← hx1, ← hQp] at h
    exact h
  have hIII : S + x2 = x3 + Pp := by
    have hs1 : exDiv ((ψ.symm).symm) = exDiv ψ := rfl
    have hs2 : exDiv (ψ.symm.trans φ.symm) = exDiv ((φ.trans ψ).symm) := rfl
    have h := wgt_exDiv_trans_add (𝕜 := 𝕜) w ψ.symm φ.symm
    rw [hs1, hs2, Set.inter_comm (exDiv φ.symm) (exDiv ψ),
      Set.inter_comm (exDiv ((φ.trans ψ).symm)) (exDiv ψ.symm)] at h
    rw [← hS, ← hx2, ← hx3, ← hPp] at h
    exact h
  omega

end Work.Motivic
