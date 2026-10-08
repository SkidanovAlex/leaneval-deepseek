import Mathlib
import Submission.Work.BG.orbitCardAux

/-!
# `Work.BG.ocm.inertia_eq_sup`

The inertia group `I = I_{H₀}(a)` of a class function `a` of the normal subgroup
`U = ↥(Uin C)` of `H₀ = ↥C.P.H0` satisfies

  `I = U ⊔ (I ⊓ S₀)`,

where `S₀ = S0in D C hDC` is the cyclic maximal subgroup of the Sylow `2`-subgroup
viewed inside `H₀`.

## Mathematical content

Two inputs are used:

* `U ≤ I`: `U` is normal in `H₀`, and a class function on `U` is invariant under
  conjugation by elements of `U`, so `U` lies in its own inertia group
  (`ClassFunction.subgroup_le_inertia`);
* `U ⊔ S₀ = ⊤` (`Work.BG.S0in_sup_Uin`).

Given these the identity is the Dedekind modular law, proved here by hand (the
ambient subgroup lattice is *not* registered as a modular lattice in Mathlib,
since the subgroup lattice of a general group need not be modular).  Since
`U.Normal`, every `x ∈ U ⊔ S₀` factors as `x = u * s` with `u ∈ U`, `s ∈ S₀`
(`Subgroup.mem_sup_of_normal_left`); for `x ∈ I` we get `s = u⁻¹ * x ∈ I`, so
`x ∈ U ⊔ (I ⊓ S₀)`, giving `I ≤ U ⊔ (I ⊓ S₀)`.  The reverse inclusion is
immediate from `U ≤ I`.
-/

namespace Work.BG.ocm

theorem inertia_eq_sup {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) :
    OddOrder.RepresentationTheory.ClassFunction.inertia (G := ↥C.P.H0)
        (H := Work.GW2.C16.Uin C) a
      = Work.GW2.C16.Uin C ⊔ (OddOrder.RepresentationTheory.ClassFunction.inertia
          (G := ↥C.P.H0) (H := Work.GW2.C16.Uin C) a ⊓ Work.BG.S0in D C hDC) := by
  -- `U` lies in its own inertia group (it is normal in `H₀`).
  have hU : Work.GW2.C16.Uin C ≤ OddOrder.RepresentationTheory.ClassFunction.inertia
      (G := ↥C.P.H0) (H := Work.GW2.C16.Uin C) a :=
    OddOrder.RepresentationTheory.ClassFunction.subgroup_le_inertia a
  -- `U ⊔ (I ⊓ S₀) ≤ I` is immediate; the content is the reverse inclusion,
  -- i.e. the Dedekind modular law using `U ⊔ S₀ = ⊤`.
  refine le_antisymm ?_ (sup_le hU inf_le_left)
  intro x hx
  have hxsup : x ∈ Work.GW2.C16.Uin C ⊔ Work.BG.S0in D C hDC := by
    rw [Work.BG.S0in_sup_Uin D C hDC]; trivial
  obtain ⟨u, hu, s, hs, hux⟩ := Subgroup.mem_sup_of_normal_left.mp hxsup
  refine Subgroup.mem_sup_of_normal_left.mpr ⟨u, hu, s, Subgroup.mem_inf.mpr ⟨?_, hs⟩, hux⟩
  -- `s = u⁻¹ * x` lies in `I` because `u⁻¹ ∈ U ≤ I` and `x ∈ I`.
  have h1 : u⁻¹ * (u * s) ∈ OddOrder.RepresentationTheory.ClassFunction.inertia
      (G := ↥C.P.H0) (H := Work.GW2.C16.Uin C) a :=
    (OddOrder.RepresentationTheory.ClassFunction.inertia (G := ↥C.P.H0)
        (H := Work.GW2.C16.Uin C) a).mul_mem
      ((OddOrder.RepresentationTheory.ClassFunction.inertia (G := ↥C.P.H0)
        (H := Work.GW2.C16.Uin C) a).inv_mem (hU hu))
      (hux.symm ▸ hx)
  simpa using h1

end Work.BG.ocm
