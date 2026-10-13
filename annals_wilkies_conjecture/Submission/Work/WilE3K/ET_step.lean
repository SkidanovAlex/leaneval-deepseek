import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.newData_degree

namespace Work.WilE3K

theorem ET_step
    (hdeg : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re) (y : Fin N → ℝ) (δ : ℝ),
      (∑ i, WilkiesDesign.E.atomDeg ((E.newData y δ).G i)) + rt ≤
        (N + 8) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 8))
    (hsphere : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), (∀ z ∈ s, E.Nondegen z) →
      ∃ (E₁ : Work.WilE3K.ETData (N + 1) (rt + 1) (n + 1) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
        IsProperMap E₁.psiMap ∧ (∀ z ∈ t, E₁.Nondegen z) ∧
        (∑ i, WilkiesDesign.E.atomDeg (E₁.G i)) ≤ (∑ i, WilkiesDesign.E.atomDeg (E.G i)) + 3 ∧
        2 * s.card ≤ t.card)
    (hgood : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), (∀ z ∈ s, E.Nondegen z) → IsProperMap E.psiMap →
      ∃ (y : Fin N → ℝ) (ρ : ℝ), E.ETGood y ∧ 0 < ρ ∧ dist (E.psiLift y) 0 < ρ ∧
        ∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
          ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y')
    (hrolle : ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), (∀ z ∈ s, E.Nondegen z) → IsProperMap E.psiMap →
      ∀ (y : Fin N → ℝ) (ρ : ℝ), E.ETGood y → 0 < ρ → dist (E.psiLift y) 0 < ρ →
        (∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
          ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y') →
        ∃ (δ : ℝ) (t : Finset (Fin (N + 1) → ℝ)),
          (∀ z ∈ t, (E.newData y δ).Nondegen z) ∧ s.card ≤ t.card) :
    ∀ {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re) (s : Finset (Fin (N + 1) → ℝ)),
      (∀ z ∈ s, E.Nondegen z) →
      ∃ (E' : Work.WilE3K.ETData (N + 1) rt (n + 2) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
        (∀ z ∈ t, E'.Nondegen z) ∧ s.card ≤ t.card ∧
        (∑ i, WilkiesDesign.E.atomDeg (E'.G i)) + rt ≤
          (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11) := by
  intro N rt n re E s hs
  -- One sphere step: add a free coordinate and the sphere equation.
  obtain ⟨E₁, t₁, hproper, ht₁nd, ht₁deg, ht₁card⟩ := hsphere E s hs
  -- Choose a good level `y` of the remaining system of `E₁` and a radius `ρ`.
  obtain ⟨y, ρ, hgoody, hρ, hρdist, hsurj⟩ := hgood E₁ t₁ ht₁nd hproper
  -- One Rolle step at the level `y`: eliminate the last `tan` coordinate of `E₁`.
  obtain ⟨δ, t, htnd, htcard⟩ := hrolle E₁ t₁ ht₁nd hproper y ρ hgoody hρ hρdist hsurj
  refine ⟨E₁.newData y δ, t, htnd, ?_, ?_⟩
  · -- cardinality: `s.card ≤ 2 * s.card ≤ t₁.card ≤ t.card`
    omega
  · -- the degree bookkeeping
    have hd := hdeg E₁ y δ
    have hN : (N + 1) + 8 = N + 9 := by omega
    have hmul : (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E₁.G i)) + (rt + 1) + 8) ≤
        (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11) :=
      Nat.mul_le_mul_left _ (by omega)
    calc (∑ i, WilkiesDesign.E.atomDeg ((E₁.newData y δ).G i)) + rt
        ≤ ((N + 1) + 8) * ((∑ i, WilkiesDesign.E.atomDeg (E₁.G i)) + (rt + 1) + 8) := hd
      _ = (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E₁.G i)) + (rt + 1) + 8) := by rw [hN]
      _ ≤ (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11) := hmul

end Work.WilE3K
