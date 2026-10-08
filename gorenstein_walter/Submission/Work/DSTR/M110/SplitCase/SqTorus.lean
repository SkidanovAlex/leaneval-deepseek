/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Squares of elements of `C_{PΓL}(x ↦ -x)` have a diagonal `PGL`-part

For a field `F` of characteristic `≠ 2`:

* `centralizer_decomp`: an element `x ∈ PΓL(2,F)` commuting with `x ↦ -x` is `c · galHom σ`
  with `c ∈ PGL` diagonal or anti-diagonal;
* `mul_mem_torSub_of_coset`: the product of two `PGL`-parts of the same type is diagonal;
* `sq_decomp_torus`: `x²` has diagonal `PGL`-part `t ∈ torSub F` and Galois part `σ²`.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.PglCentralizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- Decomposition of an element of `C_{PΓL}(x ↦ -x)`: its `PGL`-part is diagonal or
anti-diagonal. -/
theorem centralizer_decomp (h2 : (2 : F) ≠ 0) (x : ↥(pgammaL F))
    (hx : (x : Equiv.Perm (P1 F)) * negPerm F = negPerm F * x) :
    ∃ (c : Equiv.Perm (P1 F)) (σ : F ≃+* F),
      c ∈ pglImage F ∧ (x : Equiv.Perm (P1 F)) = c * galHom F σ ∧
        (c ∈ torSub F ∨ weylEl F * c ∈ torSub F) := by
  obtain ⟨c, hc, hspec⟩ := galPart_spec F x
  refine ⟨c, galPart F x, hc, hspec, ?_⟩
  have hcg : galHom F (galPart F x) * negPerm F = negPerm F * galHom F (galPart F x) :=
    galHom_mul_negPerm F _
  have hccomm : c * negPerm F = negPerm F * c := by
    have h1 : c * negPerm F * galHom F (galPart F x) =
        negPerm F * c * galHom F (galPart F x) := by
      calc c * negPerm F * galHom F (galPart F x)
          = c * (negPerm F * galHom F (galPart F x)) := by group
        _ = c * (galHom F (galPart F x) * negPerm F) := by rw [← hcg]
        _ = c * galHom F (galPart F x) * negPerm F := by group
        _ = (x : Equiv.Perm (P1 F)) * negPerm F := by rw [← hspec]
        _ = negPerm F * x := hx
        _ = negPerm F * (c * galHom F (galPart F x)) := by rw [hspec]
        _ = negPerm F * c * galHom F (galPart F x) := by group
    exact mul_right_cancel h1
  exact pglImage_centralizer_negPerm F h2 c hc hccomm

/-- The product of the `PGL`-parts of the same type (both diagonal or both anti-diagonal) is
diagonal. -/
theorem mul_mem_torSub_of_coset (σ : F ≃+* F) {c : Equiv.Perm (P1 F)}
    (hc : c ∈ torSub F ∨ weylEl F * c ∈ torSub F) :
    c * (galHom F σ * c * (galHom F σ)⁻¹) ∈ torSub F := by
  rcases hc with hc | hc
  · exact Subgroup.mul_mem _ hc (galHom_conj_mem_torSub F σ hc)
  · obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hc
    have hd : weylEl F * (galHom F σ * c * (galHom F σ)⁻¹) ∈ torSub F :=
      galHom_conj_weyl_mem F σ hc
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hd
    have hc' : c = weylEl F * smulHom F s := by rw [hs, ← mul_assoc, weyl_self, one_mul]
    have hd' : galHom F σ * c * (galHom F σ)⁻¹ = weylEl F * smulHom F t := by
      rw [ht, ← mul_assoc, weyl_self, one_mul]
    rw [hd', hc']
    have hkey : weylEl F * smulHom F s * weylEl F ∈ torSub F := weylEl_conj_mem_torSub F s
    have heq : (weylEl F * smulHom F s) * (weylEl F * smulHom F t)
        = (weylEl F * smulHom F s * weylEl F) * smulHom F t := by group
    rw [heq]
    exact Subgroup.mul_mem _ hkey ⟨t, rfl⟩

/-- **The square of an element of `C_{PΓL}(x ↦ -x)` has diagonal `PGL`-part.** -/
theorem sq_decomp_torus (h2 : (2 : F) ≠ 0) (x : ↥(pgammaL F))
    (hx : (x : Equiv.Perm (P1 F)) * negPerm F = negPerm F * x) :
    ∃ (t : ↥(torSub F)) (σ : F ≃+* F),
      ((x * x : ↥(pgammaL F)) : Equiv.Perm (P1 F)) = (t : Equiv.Perm (P1 F)) * galHom F σ := by
  obtain ⟨c, σ, _hc, hspec, htype⟩ := centralizer_decomp F h2 x hx
  have ht : c * (galHom F σ * c * (galHom F σ)⁻¹) ∈ torSub F :=
    mul_mem_torSub_of_coset F σ htype
  refine ⟨⟨c * (galHom F σ * c * (galHom F σ)⁻¹), ht⟩, σ * σ, ?_⟩
  have h : ((x * x : ↥(pgammaL F)) : Equiv.Perm (P1 F))
      = (c * galHom F σ) * (c * galHom F σ) := by
    rw [Subgroup.coe_mul, hspec]
  rw [h, map_mul,
    show (c * (galHom F σ * c * (galHom F σ)⁻¹)) * (galHom F σ * galHom F σ)
      = (c * galHom F σ) * (c * galHom F σ) from by group]

end Work.DSTR.M110.SplitAux
