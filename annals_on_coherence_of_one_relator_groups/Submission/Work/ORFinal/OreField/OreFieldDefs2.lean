/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linnell's Ore field of fractions statement (I4′b) from the division-ring property (I4)

The Ore field of fractions statement `Work.ORFinal.OreFieldFrac K G φK` (field (I4′b) of the Linnell
datum of the M1 bridge) asks: for `N ≤ Γ ≤ G` with `Γ` torsion free and `Γ/N ≅ ℤ`, every element
of the division closure `D Γ` of `K[Γ]` in `U(G)` is a *right quotient* `a * t⁻¹` of two elements
of the subring `R = ⟨D N ∪ gen Γ⟩`.

This file proves it from `Work.ORFinal.DivOn` alone, i.e. from (I4): for every torsion free
subgroup `H`, `D H` is a division ring.  The mathematical content is Linnell's lemma: since
`Γ = N ⋊ ⟨s⟩`, the ring `R = D N[s^{±1}]` is a twisted Laurent polynomial ring over the division
ring `D N`; such a ring is an Ore domain, and the division closure of an Ore domain `R` inside a
division ring containing it is its classical ring of fractions `{a * t⁻¹}`.

The three ingredients are

* `Work.ORFinal.OreField.skewMonoidAlgebra_ore` — the Ore condition for the twisted Laurent
  polynomial ring `D[ℤ]` over a division ring `D`, proved from the degree/division algorithm;
* `Work.ORFinal.OreField.laurentSum_mem_genSubring` and
  `Work.ORFinal.OreField.exists_laurentSum_of_mem_genSubring` — `R` is exactly the image of the
  twisted Laurent polynomial ring under `single i d ↦ d * (gen s)^i`;
* `Work.ORFinal.OreField.independence_multiplicative_zpow` — injectivity of that map, i.e. Linnell
  independence (I1) for the powers of `s`.

The Ore condition on `R` (`ore_genSubring`) is then transported from the twisted Laurent
polynomial ring, and the quotient subring `Q = {a * t⁻¹ : a, t ∈ R, t ≠ 0}` of `U(G)` is shown to
be a division closed subring containing `K[Γ]`; minimality of the division closure gives
`D Γ ≤ Q`, which is the statement.
-/
import Mathlib
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORLinnell.Main
import Submission.Work.ORBridgeLinnell.Countable
import Submission.Work.ORFinal.OreField.OreFieldDefs
import Submission.Work.ORFinal.OreField.independence_multiplicative_zpow
import Submission.Work.ORFinal.OreField.skewMonoidAlgebra_ore

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.OreField

open Work.ORVonNeumann Work.ORBridgeLinnell

universe u v

variable {K : Type*} [Field K] {G : Type*} [Group G]

/-- **Linnell independence for the powers of `s`**, in the form of the injectivity of the twisted
Laurent sum. -/
theorem laurentSum_injective (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    {N Γ : Subgroup G} (hN : N ≤ Γ) (hφ : Work.ORLinnell.IsExtensionByZ N Γ) (s : Γ)
    (hs : ∀ h : Γ, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf Γ)
    (c : Multiplicative ℤ →₀ ↥(D E φK N)) (hc : laurentSum E φK s c = 0) : c = 0 :=
  independence_multiplicative_zpow E φK hφK hN hφ s hs c (by simpa [laurentSum, sPowU] using hc)

/-- **The Ore condition for the subring `R = ⟨D N ∪ gen Γ⟩`.**  This transports
`Work.ORFinal.OreField.skewMonoidAlgebra_ore` (the Ore condition for the twisted Laurent
polynomial ring over the division ring `D N`) across the bijection `D N[ℤ] → R`,
`single i d ↦ d * (gen s)^i`, whose injectivity is Linnell independence. -/
theorem ore_genSubring (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    {N Γ : Subgroup G} (hN : N ≤ Γ) (hNn : (N.subgroupOf Γ).Normal)
    (hdivN : ∀ x : ↥(D E φK N), x ≠ 0 → IsUnit x)
    (hφ : Work.ORLinnell.IsExtensionByZ N Γ) (s : Γ)
    (hs : ∀ h : Γ, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf Γ) :
    ∀ a ∈ genSubring E φK N Γ, a ≠ 0 → ∀ b ∈ genSubring E φK N Γ, b ≠ 0 →
      ∃ c ∈ genSubring E φK N Γ, c ≠ 0 ∧
        ∃ d ∈ genSubring E φK N Γ, d ≠ 0 ∧ a * c = b * d := by
  intro a ha ha0 b hb hb0
  letI : DivisionRing ↥(D E φK N) := DivisionRing.ofIsUnitOrEqZero (fun x => by
    rcases eq_or_ne x 0 with h | h
    · exact Or.inr h
    · exact Or.inl (hdivN x h))
  letI : MulSemiringAction (Multiplicative ℤ) E.U := conjAction E (s : G)
  haveI hInv : IsInvariantSubring (Multiplicative ℤ) (D E φK N) := by
    refine ⟨fun i y hy => ?_⟩
    rw [show i = Multiplicative.ofAdd (Multiplicative.toAdd i) from ofAdd_toAdd i,
      conjAction_smul_apply, sPowU_eq_gen E s (Multiplicative.toAdd i),
      sPowU_neg_eq_gen_inv E s (Multiplicative.toAdd i)]
    exact D_conj_mem_self E φK hN hNn (s ^ (Multiplicative.toAdd i)) hy
  let Φ : SkewMonoidAlgebra ↥(D E φK N) (Multiplicative ℤ) →+* E.U :=
    SkewMonoidAlgebra.liftNCRingHom (Subring.subtype (D E φK N))
      ((Units.coeHom E.U).comp (unitPow E (s : G))) (fun {x y} => by
        have hcoe : ((y • x : ↥(D E φK N)) : E.U)
            = sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U)
              * sPowU E (s : G) (-(Multiplicative.toAdd y)) := by
          have h₁ : ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • x : ↥(D E φK N))
              = (y • x : ↥(D E φK N)) := by rw [ofAdd_toAdd]
          rw [← h₁]
          change ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • (x : E.U)) = _
          rw [conjAction_smul_apply]
        show ((y • x : ↥(D E φK N)) : E.U) * sPowU E (s : G) (Multiplicative.toAdd y)
          = sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U)
        rw [hcoe, mul_assoc (sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U))
          (sPowU E (s : G) (-(Multiplicative.toAdd y)))
          (sPowU E (s : G) (Multiplicative.toAdd y)), sPowU_neg_mul, mul_one])
  have hΦof : ∀ c : Multiplicative ℤ →₀ ↥(D E φK N),
      Φ (SkewMonoidAlgebra.ofCoeff c) = laurentSum E φK s c := fun c => rfl
  have hΦC : ∀ C : SkewMonoidAlgebra ↥(D E φK N) (Multiplicative ℤ),
      Φ C = laurentSum E φK s C.coeff := fun C => rfl
  obtain ⟨ca, hca⟩ := exists_laurentSum_of_mem_genSubring E φK hN hNn s hs ha
  obtain ⟨cb, hcb⟩ := exists_laurentSum_of_mem_genSubring E φK hN hNn s hs hb
  have hfa : SkewMonoidAlgebra.ofCoeff ca ≠ 0 := by
    intro h
    refine ha0 ?_
    rw [← hca]
    have h1 : Φ (SkewMonoidAlgebra.ofCoeff ca) = 0 := by rw [h, map_zero]
    rwa [hΦof ca] at h1
  have hfb : SkewMonoidAlgebra.ofCoeff cb ≠ 0 := by
    intro h
    refine hb0 ?_
    rw [← hcb]
    have h1 : Φ (SkewMonoidAlgebra.ofCoeff cb) = 0 := by rw [h, map_zero]
    rwa [hΦof cb] at h1
  obtain ⟨C, Dk, hC, hD, hCD⟩ :=
    skewMonoidAlgebra_ore
      (x := (SkewMonoidAlgebra.ofCoeff ca : SkewMonoidAlgebra ↥(D E φK N) (Multiplicative ℤ)))
      (y := (SkewMonoidAlgebra.ofCoeff cb : SkewMonoidAlgebra ↥(D E φK N) (Multiplicative ℤ)))
      hfa hfb
  have heq : a * laurentSum E φK s C.coeff = b * laurentSum E φK s Dk.coeff := by
    have h1 := congrArg Φ hCD
    rw [map_mul, map_mul, hΦof ca, hΦof cb, hΦC C, hΦC Dk, hca, hcb] at h1
    exact h1
  refine ⟨laurentSum E φK s C.coeff, laurentSum_mem_genSubring E φK s C.coeff, ?_,
    laurentSum E φK s Dk.coeff, laurentSum_mem_genSubring E φK s Dk.coeff, ?_, heq⟩
  · intro h
    have h0 : C.coeff = 0 := laurentSum_injective E φK hφK hN hφ s hs C.coeff h
    exact hC (by rw [← SkewMonoidAlgebra.eta C, h0]; rfl)
  · intro h
    have h0 : Dk.coeff = 0 := laurentSum_injective E φK hφK hN hφ s hs Dk.coeff h
    exact hD (by rw [← SkewMonoidAlgebra.eta Dk, h0]; rfl)

end Work.ORFinal.OreField
