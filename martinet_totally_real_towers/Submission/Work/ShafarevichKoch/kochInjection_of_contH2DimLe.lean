import Mathlib
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShaBound.exists_functionals_commonKernel_finrank_le_one

/-!
# `Work.ShafarevichKoch.kochInjection_of_contH2DimLe`

**The cohomological relation bound `dim_{𝔽₂} H²(G_∅, 𝔽₂) ≤ 6` produces the classical
Shafarevich--Koch injection `H²(G_∅, 𝔽₂) ↪ (V_∅/Kc^{×2})^∨`.**

This is the converse of `Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection`, and together with
it identifies the *arithmetic* input `KochInjection` of the Shafarevich--Koch chapter with the
numerical bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` -- i.e. with the classical relation bound
`r(G_∅) ≤ 6 = d₂(𝓞_{Kc}ˣ) + rank₂ Cl(Kc)` (Koch, *Galois theory of `p`-extensions*, Ch. 11
Thm. 11.3).

The content is purely a cardinality count, and that is the point: since
`#(V_∅/Kc^{×2})^∨ = 64 = 2^6` (`Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc`), the existence of
an *injection* of `H²` into that dual is equivalent to `#H² ≤ 64`.  Concretely:

* `H²(G_∅, 𝔽₂)` is cohomology with coefficients in `𝔽₂ = ℤ/2` carrying the trivial action, so
  every one of its elements is killed by `2` (`contH2_two_nsmul_eq_zero`): it is a module over
  `𝔽₂`, of cardinality `2 ^ k` with `k ≤ 6` by hypothesis, hence of `𝔽₂`-dimension `k ≤ 6`;
* the dual `Additive (V_∅/Kc^{×2} →* 𝔽₂)` is likewise an `𝔽₂`-vector space
  (`dual_two_nsmul_eq_zero`), of cardinality `64 = 2^6`, hence of dimension `6`;
* an injective `𝔽₂`-linear map from a space of dimension `k` into one of dimension `6` therefore
  exists (`Work.ShaBound.exists_injective_linearMap_pi` plus the isomorphism
  `(Fin 6 → 𝔽₂) ≃ₗ 𝔽₂` dual, from the equality of dimensions), and its underlying additive map is
  the required injection.

Nothing here uses arithmetic beyond the *count* `#(V_∅/Kc^{×2})^∨ = 2^6`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical
open Additive (ofMul toMul)

noncomputable section

namespace Work.ShafarevichKoch

/-- **Koch's Kummer quotient `V_∅/Kc^{×2}`** for `Kc = ℚ(√-30030)` (`V_∅ = VTwo Kc` is the group
of elements of `Kcˣ` generating a square fractional ideal). -/
abbrev kochKummerQuotient : Type :=
  ↥(VTwo Work.ClassFieldTower.Kc) ⧸
    (Work.QuadraticFields.squareSubgroup Work.ClassFieldTower.Kcˣ).subgroupOf
      (VTwo Work.ClassFieldTower.Kc)

/-- **The `𝔽₂`-dual of Koch's Kummer quotient**, as an additive group: the codomain of the
Shafarevich--Koch injection. -/
abbrev kochDual : Type := Additive (kochKummerQuotient →* Multiplicative (ZMod 2))

/-- In `𝔽₂ = Multiplicative (ZMod 2)` every element is its own inverse. -/
theorem mul_self_eq_one_multiplicative_zmodTwo (m : Multiplicative (ZMod 2)) : m * m = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]

/-- **`H²(Γ, 𝔽₂)` is killed by `2`**: the continuous cohomology of a topological group with
coefficients in the trivial `𝔽₂ = ℤ/2`-module is a module over `𝔽₂`. -/
theorem contH2_two_nsmul_eq_zero (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (x : Work.RelatorRank.contH2 Γ) : (2 : ℕ) • x = 0 := by
  letI := Work.RelatorRank.f2TrivialAction Γ
  letI : Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) := Work.RelatorRank.f2Discrete Γ
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (Work.ConCohomology.B2' Γ (ZMod 2)) x
  rw [← map_nsmul]
  rw [show (2 : ℕ) • z = 0 from by
        refine Subtype.ext ?_
        ext p
        show (2 : ℕ) • (z.1 p) = 0
        exact CharTwo.two_nsmul _,
    map_zero]

/-- **The dual of an abelian group of exponent `2` is killed by `2`**: for `Q` a group, the
additive group `Additive (Q →* 𝔽₂)` of homomorphisms into `𝔽₂ = Multiplicative (ZMod 2)` (with
pointwise multiplication) has exponent `2`. -/
theorem dual_two_nsmul_eq_zero {Q : Type*} [Group Q]
    (x : Additive (Q →* Multiplicative (ZMod 2))) : (2 : ℕ) • x = 0 := by
  have hf : toMul x * toMul x = 1 :=
    MonoidHom.ext fun q => mul_self_eq_one_multiplicative_zmodTwo (toMul x q)
  rw [two_nsmul, ← ofMul_toMul x, ← ofMul_mul, hf, ofMul_one]

/-- **The cohomological relation bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` gives the classical
Shafarevich--Koch injection** `H²(G_∅, 𝔽₂) ↪ (V_∅/Kc^{×2})^∨` for `Kc = ℚ(√-30030)`. -/
theorem kochInjection_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (h : Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6) :
    Work.ShafarevichKoch.KochInjection M := by
  obtain ⟨k, hk, hcard⟩ := h
  -- ## Step 1: both groups are `𝔽₂`-vector spaces.
  have hNtors : ∀ x : Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M),
      (2 : ℕ) • x = 0 := fun x => contH2_two_nsmul_eq_zero _ x
  have hDtors : ∀ x : kochDual, (2 : ℕ) • x = 0 := fun x => dual_two_nsmul_eq_zero x
  letI : Module (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    AddCommGroup.zmodModule (n := 2) hNtors
  letI : Module (ZMod 2) kochDual := AddCommGroup.zmodModule (n := 2) hDtors
  -- ## Step 2: finiteness and cardinality of the dual.
  have hDcard : Nat.card kochDual = 64 :=
    (Nat.card_congr (Additive.toMul :
      kochDual ≃ (kochKummerQuotient →* Multiplicative (ZMod 2)))).trans
      natCard_dual_VTwoQuot_Kc
  haveI : Finite kochDual := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
  haveI : Finite (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by norm_num))
  haveI : Module.Finite (ZMod 2) kochDual := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := Module.Finite.of_finite
  -- ## Step 3: the two dimensions are `6` and `k ≤ 6`.
  have hDfr : Module.finrank (ZMod 2) kochDual = 6 := by
    have h1 : Nat.card kochDual = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) kochDual :=
      Module.natCard_eq_pow_finrank
    rw [Nat.card_zmod, hDcard] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (by norm_num))
  have hNfr : Module.finrank (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) = k := by
    have h1 : Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) =
        Nat.card (ZMod 2) ^ Module.finrank (ZMod 2)
          (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
      Module.natCard_eq_pow_finrank
    rw [Nat.card_zmod, hcard] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (by norm_num))
  -- ## Step 4: an injective `𝔽₂`-linear map from `H²` into the dual.
  obtain ⟨L, hL⟩ := Work.ShaBound.exists_injective_linearMap_pi (K := ZMod 2)
    (X := Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) (ι := Fin 6)
    (by rw [hNfr, Fintype.card_fin]; exact hk)
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod 2)
    (M := (Fin 6 → ZMod 2)) (M' := kochDual)
    (by rw [Module.finrank_fintype_fun_eq_card (ZMod 2), Fintype.card_fin, hDfr])
  exact ⟨(e.toLinearMap.comp L).toAddMonoidHom, e.injective.comp hL⟩

end Work.ShafarevichKoch

