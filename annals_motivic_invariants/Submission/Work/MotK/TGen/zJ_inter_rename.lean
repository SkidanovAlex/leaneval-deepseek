import Mathlib
import Submission.Work.MotK.TGen.RadSatDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `zJ ∩ K[x₁,x₂] = (ZElim2)`

For the T-twisted Crauder–Katz link, `R = K[x₀,x₁,x₂]` carries the two relations

* `zF1 = α·x₀² + β·x₀ + γ`  (a quadratic equation for `x₀`, with `α = a²b⁴h` a unit), and
* `zB = zA·x₀ − zC`  (the graph relation `x₀ = zC/zA`),

where `zA, zC, zF1` involve only `x₁, x₂` (through `rename zEmb`).  The ideal
`J = (zF1, zB) ⊆ K[x₀,x₁,x₂]` cuts the graph of the map
`x₀ ↦ zC/zA` over the plane curve `zg = ZElim2 = 0`.

The content of `zJ_inter_rename` is that such a graph, *in the reduced plane coordinates*, meets
`K[x₁,x₂]` exactly in `(ZElim2)`:  a polynomial `H` of the two plane variables that lies in `J`
must be a multiple of the eliminant `ZElim2`.

The proof is the map `zPsi : K[x₀,x₁,x₂] →ₐ[K] Frac(ZD)` (`x₀ ↦ zC/zA`, `x₁ ↦ y₀`,
`x₂ ↦ y₁`).  Its kernel contains both generators of `J`
(`zF1 ∈ ZI ⊆ ker zPsi`, and `zPsi zB = 0`), and `zPsi (rename H) = algebraMap (mk H)`.  Since
`Frac(ZD)` is a fraction ring of the domain `ZD`, `algebraMap (mk H) = 0` forces `mk H = 0` in
`ZD`, i.e. `H ∈ (ZElim2)`.
-/

namespace Work.MotK.TGen

open MvPolynomial

/-- The ideal `J = (zF1, zB)` of `K[x₀,x₁,x₂]`.  It equals `(zF1, zB, zg)` (see `zg_mem_zJ` in
the assembly module `ZRingIsDomainAll`), and its intersection with `K[x₁,x₂]` is `(ZElim2)`
(`zJ_inter_rename` below). -/
noncomputable def zJ (K : Type) [Field K] (a b h : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K))

/-- **Intersection of `zJ = (zF1, zB)` with the plane polynomials.**

If `rename zEmb H` lies in `zJ = (zF1, zB)` for a polynomial `H` in the two plane variables
`x₁, x₂`, then `H` lies in the principal ideal `(ZElim2)`. -/
theorem zJ_inter_rename (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (Work.MotK.TGen.ZD K a b h)] (H : MvPolynomial (Fin 2) K) :
    MvPolynomial.rename Work.MotK.TGen.zEmb H ∈ Work.MotK.TGen.zJ K a b h →
      H ∈ Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)) := by
  intro hmem
  -- Both generators of `zJ` are killed by `zPsi`.
  have hle : zJ K a b h ≤ RingHom.ker (zPsi K a b h) := by
    rw [zJ, Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ZI_le_ker_zPsi K a b h ha hb hh (zF1_mem_ZI a b h ha hb)
    · exact RingHom.mem_ker.mpr (zPsi_zB K a b h ha hb hh)
  have hker : zPsi K a b h (MvPolynomial.rename zEmb H) = 0 := hle hmem
  rw [zPsi_rename K a b h H] at hker
  -- `Frac (ZD)` is a fraction ring of the domain `ZD`, so the structure map is injective.
  have hmk : Ideal.Quotient.mk (Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} :
      Set (MvPolynomial (Fin 2) K))) H = 0 :=
    IsFractionRing.injective (ZD K a b h) (ZF K a b h)
      (by rw [hker, map_zero])
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmk

end Work.MotK.TGen
