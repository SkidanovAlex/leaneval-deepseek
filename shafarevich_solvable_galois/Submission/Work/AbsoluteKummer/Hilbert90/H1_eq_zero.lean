/-
Copyright (c) 2025. All rights reserved.

# Hilbert 90 for the absolute Galois group, in the form `H¹(G_k, k̄ˣ) = 0`

`Submission/Work/AbsoluteKummer/Hilbert90/exists_div_of_isCrossedHom.lean` states Hilbert 90 in the
classical form: every locally constant crossed homomorphism `G_k → k̄ˣ` is of the shape
`σ ↦ σ b / b`.  Here that statement is transported to the cohomology group of this chapter:

* `Work.AbsoluteKummer.Hilbert90.H1_eq_zero` — **`H¹(G_k, k̄ˣ)` is the trivial group** (and
  `H1_eq_zero_absolute` for the `Field.absoluteGaloisGroup k` spelling).

This is the input (the Kummer sequence `1 → μ_n → k̄ˣ → k̄ˣ → 1` has vanishing `H¹(k̄ˣ)`) that
identifies the cokernel of `kˣ → kˣ`, `x ↦ xⁿ` with `H¹(G_k, μ_n)`.
-/
import Submission.Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Hilbert90

open scoped Classical

noncomputable section

variable {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)]

/-- **Hilbert 90, in the form `H¹(G_k, k̄ˣ) = 0`.**  Every class in `H¹(G_k, k̄ˣ)` is zero, i.e.
every continuous `1`-cocycle `G_k → k̄ˣ` is a coboundary. -/
theorem H1_eq_zero (x : H1 (G k) (Additive (AlgebraicClosure k)ˣ)) : x = 0 := by
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((B1 (G k) (Additive (AlgebraicClosure k)ˣ)).comap
      (Z1 (G k) (Additive (AlgebraicClosure k)ˣ)).subtype) x
  rw [show x = H1π (G k) (Additive (AlgebraicClosure k)ˣ) F from hF.symm, H1π_eq_zero_iff]
  obtain ⟨hcross, hloc⟩ := (mem_Z1_iff _).mp F.2
  have hcross' : ∀ σ τ : G k, Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) (σ * τ))
      = Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) σ)
        * algEquivUnitsMap k σ (Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) τ)) := by
    intro σ τ
    have h := congrArg Additive.toMul (hcross σ τ)
    simpa [addUnits_smul_toMul, mul_comm] using h
  have hloc' : IsLocallyConstant
      (fun σ : G k => Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) σ)) :=
    IsLocallyConstant.map Additive.toMul hloc
  obtain ⟨b, hb⟩ := exists_div_of_isCrossedHom (k := k)
    (fun σ : G k => Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) σ)) hcross' hloc'
  have hb' : ∀ σ : G k, (F : G k → Additive (AlgebraicClosure k)ˣ) σ =
      Additive.ofMul (algEquivUnitsMap k σ b / b) := by
    intro σ
    show Additive.ofMul (Additive.toMul ((F : G k → Additive (AlgebraicClosure k)ˣ) σ)) = _
    rw [hb σ]
  rw [mem_B1_iff]
  refine ⟨Additive.ofMul b, ?_⟩
  funext σ
  rw [Work.GroupCohomology.d0_apply, hb' σ]
  rfl

/-- **Hilbert 90, in the form `H¹(G_k, k̄ˣ) = 0`**, for the `Field.absoluteGaloisGroup k` spelling of
the absolute Galois group. -/
theorem H1_eq_zero_absolute
    (x : H1 (Field.absoluteGaloisGroup k) (Additive (AlgebraicClosure k)ˣ)) : x = 0 :=
  H1_eq_zero (k := k) x

end

end Work.AbsoluteKummer.Hilbert90
