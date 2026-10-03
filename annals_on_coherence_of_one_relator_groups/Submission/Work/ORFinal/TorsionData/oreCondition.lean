/-
# The right Ore condition for the twisted Laurent ring `R = ⟨D N ∪ H⟩`

Let `L : LinnellDatum K G U`, `N ≤ H ≤ G` with `N` normal in `H`, `D N` a division ring, and let
`s : H` be an element whose powers represent all of `H/N ≅ ℤ` (`hs`, `hs0`).  In this file we
prove that the subring

`TorsionR L N H = Subring.closure (D N ∪ gen H) ⊆ U`

satisfies the right Ore condition: for nonzero `a b ∈ R` there are nonzero `c d ∈ R` with
`a * c = b * d`.

The proof identifies `R` with the twisted Laurent polynomial ring `D N[t^{±1}; σ]`
(`σ = conjugation by s`) via the ring homomorphism

`Φ : SkewMonoidAlgebra ↥(L.D N) (Multiplicative ℤ) →+* U`, `single i d ↦ d * (gen s)^i`,

whose restriction to coefficients is the twisted Laurent sum `laurentSumM`.  The twist is the
conjugation action of the powers of `s` on `D N`, which preserves `D N` because `N` is normal in
`H` (`conj_mem_DN`).  Injectivity of `laurentSumM` is Linnell independence (I1)
(`laurentSumM_eq_zero`), and its image is exactly `R` (`laurentSumM_mem_exists`, which uses the
Laurent decomposition `Work.ORLinnell.Laurent.laurentSum_exists`).  The Ore condition for the
skew monoid algebra over a division ring is `Work.ORFinal.OreField.skewMonoidAlgebra_ore`
(linear algebra over `D N`); transporting it along `Φ` gives the claim.
-/
import Mathlib
import Submission.Work.ORFinal.TorsionData.Defs
import Submission.Work.ORFinal.TorsionData.OreSetup
import Submission.Work.ORFinal.TorsionData.laurentSumM_eq_zero
import Submission.Work.ORFinal.TorsionData.laurentSumM_mem_exists
import Submission.Work.ORFinal.OreField.skewMonoidAlgebra_ore

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

theorem oreCondition {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {N H : Subgroup G}
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hdivN : ∀ x : ↥(L.D N), x ≠ 0 → IsUnit x) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ∀ a ∈ Work.ORFinal.TorsionData.TorsionR L N H, a ≠ 0 →
      ∀ b ∈ Work.ORFinal.TorsionData.TorsionR L N H, b ≠ 0 →
      ∃ c ∈ Work.ORFinal.TorsionData.TorsionR L N H, c ≠ 0 ∧
        ∃ d ∈ Work.ORFinal.TorsionData.TorsionR L N H, d ≠ 0 ∧ a * c = b * d := by
  intro a ha ha0 b hb hb0
  -- `D N` is a division ring by hypothesis.
  letI : DivisionRing ↥(L.D N) := DivisionRing.ofIsUnitOrEqZero (fun x => by
    rcases eq_or_ne x 0 with h | h
    · exact Or.inr h
    · exact Or.inl (hdivN x h))
  -- the conjugation action of the powers of `s` on `U`, restricted to `D N`
  letI : MulSemiringAction (Multiplicative ℤ) U := conjActionU L (s : G)
  haveI hInv : IsInvariantSubring (Multiplicative ℤ) (L.D N) := by
    refine ⟨fun i y hy => ?_⟩
    rw [show i = Multiplicative.ofAdd (Multiplicative.toAdd i) from ofAdd_toAdd i,
      conjActionU_smul_apply]
    exact conj_mem_DN L hNH hNn s (Multiplicative.toAdd i) hy
  -- the twisted Laurent presentation `Φ : D N[t^{±1}; σ] → U`
  let Φ : SkewMonoidAlgebra ↥(L.D N) (Multiplicative ℤ) →+* U :=
    SkewMonoidAlgebra.liftNCRingHom (Subring.subtype (L.D N))
      ((Units.coeHom U).comp (sUnitPow L (s : G))) (fun {x y} => by
        have hcoe : ((y • x : ↥(L.D N)) : U)
            = genZPow L (s : G) (Multiplicative.toAdd y) * (x : U)
              * genZPow L (s : G) (-(Multiplicative.toAdd y)) := by
          have h₁ : ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • x : ↥(L.D N))
              = (y • x : ↥(L.D N)) := by rw [ofAdd_toAdd]
          rw [← h₁]
          change ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • (x : U)) = _
          rw [conjActionU_smul_apply]
        show ((y • x : ↥(L.D N)) : U) * genZPow L (s : G) (Multiplicative.toAdd y)
          = genZPow L (s : G) (Multiplicative.toAdd y) * (x : U)
        rw [hcoe, mul_assoc (genZPow L (s : G) (Multiplicative.toAdd y) * (x : U))
          (genZPow L (s : G) (-(Multiplicative.toAdd y)))
          (genZPow L (s : G) (Multiplicative.toAdd y)), genZPow_neg_mul, mul_one])
  have hΦof : ∀ c : Multiplicative ℤ →₀ ↥(L.D N),
      Φ (SkewMonoidAlgebra.ofCoeff c) = laurentSumM L (s : G) c := fun c => rfl
  have hΦC : ∀ C : SkewMonoidAlgebra ↥(L.D N) (Multiplicative ℤ),
      Φ C = laurentSumM L (s : G) C.coeff := fun C => rfl
  -- preimages of `a` and `b` in the twisted Laurent polynomial ring
  obtain ⟨ca, hca⟩ := (laurentSumM_mem_exists L hNH hNn s hs).2 a ha
  obtain ⟨cb, hcb⟩ := (laurentSumM_mem_exists L hNH hNn s hs).2 b hb
  have hx0 : SkewMonoidAlgebra.ofCoeff ca ≠ 0 := by
    intro h
    refine ha0 ?_
    rw [← hca]
    have h1 : Φ (SkewMonoidAlgebra.ofCoeff ca) = 0 := by rw [h, map_zero]
    rwa [hΦof ca] at h1
  have hy0 : SkewMonoidAlgebra.ofCoeff cb ≠ 0 := by
    intro h
    refine hb0 ?_
    rw [← hcb]
    have h1 : Φ (SkewMonoidAlgebra.ofCoeff cb) = 0 := by rw [h, map_zero]
    rwa [hΦof cb] at h1
  -- the Ore condition in the twisted Laurent polynomial ring
  obtain ⟨C, Dk, hC, hD, hCD⟩ := Work.ORFinal.OreField.skewMonoidAlgebra_ore
    (x := (SkewMonoidAlgebra.ofCoeff ca : SkewMonoidAlgebra ↥(L.D N) (Multiplicative ℤ)))
    (y := (SkewMonoidAlgebra.ofCoeff cb : SkewMonoidAlgebra ↥(L.D N) (Multiplicative ℤ))) hx0 hy0
  -- transport along `Φ`
  have heq : a * laurentSumM L (s : G) C.coeff = b * laurentSumM L (s : G) Dk.coeff := by
    have h1 := congrArg Φ hCD
    rw [map_mul, map_mul, hΦof ca, hΦof cb, hΦC C, hΦC Dk, hca, hcb] at h1
    exact h1
  refine ⟨laurentSumM L (s : G) C.coeff, (laurentSumM_mem_exists L hNH hNn s hs).1 C.coeff, ?_,
    laurentSumM L (s : G) Dk.coeff, (laurentSumM_mem_exists L hNH hNn s hs).1 Dk.coeff, ?_, heq⟩
  · intro h
    have h0 : C.coeff = 0 := laurentSumM_eq_zero L s hs0 C.coeff h
    exact hC (by rw [← SkewMonoidAlgebra.eta C, h0]; rfl)
  · intro h
    have h0 : Dk.coeff = 0 := laurentSumM_eq_zero L s hs0 Dk.coeff h
    exact hD (by rw [← SkewMonoidAlgebra.eta Dk, h0]; rfl)

end Work.ORFinal.TorsionData
