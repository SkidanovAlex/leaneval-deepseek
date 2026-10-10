import Mathlib.RingTheory.MvPowerSeries.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Step
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniqueness of the solution of `D φ = 0` with prescribed linear part

The discrepancy `D φ = f ∘ φ - φ ∘ g` of Milne, *CFT*, Lemma I.2.11 is, at the level of the
lowest degree in which two candidates `φ`, `ψ` differ, affected by a nonzero factor `π - π^m`
(`LubinTate.coeff_Dsub_add`).  Since `π - π^m = π · (1 - π^{m-1})` is a nonzerodivisor (the
coefficient-ring conditions `IsLubinTateCoeff` give that `1 - π^{m-1}` is a unit and that `π` is a
nonzerodivisor), the two candidates must coincide.  This is the uniqueness half of
`existsUnique_lubinTate_solution`.

The higher-degree vanishing hypothesis on `φ₁` is not needed for this uniqueness statement, but the
statement is phrased with it because that is how the requester uses it; we keep the exact wording.
-/

namespace NK.LocalReciprocityLubinTate.Uniqueness

open MvPowerSeries

universe u

theorem eq_of_Dsub_eq_zero {A : Type u} [CommRing A] {π : A} {q n : ℕ}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    {f g : MvPowerSeries (Fin 1) A}
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    {φ₁ φ ψ : MvPowerSeries (Fin n) A}
    (hφ₁ : φ₁.constantCoeff = 0 ∧
      ∀ s : Fin n →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s φ₁ = 0)
    (hφlin : ∀ s : Fin n →₀ ℕ, s.degree ≤ 1 →
      MvPowerSeries.coeff s φ = MvPowerSeries.coeff s φ₁)
    (hψlin : ∀ s : Fin n →₀ ℕ, s.degree ≤ 1 →
      MvPowerSeries.coeff s ψ = MvPowerSeries.coeff s φ₁)
    (hφ : NK.LocalReciprocityLubinTate.LubinTate.Dsub n f g φ = 0)
    (hψ : NK.LocalReciprocityLubinTate.LubinTate.Dsub n f g ψ = 0) :
    φ = ψ := by
  classical
  obtain ⟨hφ₁c, _⟩ := hφ₁
  have hφc : φ.constantCoeff = 0 := by
    rw [show φ.constantCoeff = MvPowerSeries.coeff 0 φ from rfl, hφlin 0 (by simp)]
    exact hφ₁c
  have hψc : ψ.constantCoeff = 0 := by
    rw [show ψ.constantCoeff = MvPowerSeries.coeff 0 ψ from rfl, hψlin 0 (by simp)]
    exact hφ₁c
  have hψOrd : NK.LocalReciprocityLubinTate.LubinTate.OrderGe 1 ψ :=
    NK.LocalReciprocityLubinTate.LubinTate.OrderGe.of_constantCoeff hψc
  by_contra hne
  -- the smallest degree in which `φ` and `ψ` differ
  let p : ℕ → Prop := fun d => ∃ s : Fin n →₀ ℕ,
    s.degree = d ∧ MvPowerSeries.coeff s (φ - ψ) ≠ 0
  have hp : ∃ d, p d := by
    by_contra h
    refine hne (MvPowerSeries.ext fun s => ?_)
    have hz : MvPowerSeries.coeff s (φ - ψ) = 0 := by
      by_contra hc
      exact h ⟨s.degree, ⟨s, rfl, hc⟩⟩
    rwa [map_sub, sub_eq_zero] at hz
  obtain ⟨s₀, hs₀deg, hs₀coeff⟩ := Nat.find_spec hp
  have hδord : NK.LocalReciprocityLubinTate.LubinTate.OrderGe (Nat.find hp) (φ - ψ) := by
    intro t ht
    by_contra hc
    exact Nat.find_min hp ht ⟨t, rfl, hc⟩
  -- the two candidates agree in degrees `≤ 1`, so the first difference is in degree `≥ 2`
  have hm2 : 2 ≤ Nat.find hp := by
    by_contra h
    have hlt : Nat.find hp < 2 := Nat.lt_of_not_le h
    have hs : s₀.degree ≤ 1 := by omega
    have : MvPowerSeries.coeff s₀ (φ - ψ) = 0 := by
      rw [map_sub, hφlin s₀ hs, hψlin s₀ hs, sub_self]
    exact hs₀coeff this
  have hfO := NK.LocalReciprocityLubinTate.LubinTate.orderGe_two_sub_C_mul_X
    (g := f) hf.constantCoeff (by
      show MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) f = π
      simpa [NK.LocalReciprocityLubinTate.coeffX] using hf.coeff_one)
  have hg1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) g = π := by
    simpa [NK.LocalReciprocityLubinTate.coeffX] using hg.coeff_one
  -- the one-step formula: adding `φ - ψ` (of order `m`) changes the `≤ m`-coefficients of `D`
  -- by `coeff s (φ - ψ) * (π - π^m)`
  have hkey := NK.LocalReciprocityLubinTate.LubinTate.coeff_Dsub_add
    (n := n) (f := f) (g := g) (π := π) hfO hg.constantCoeff hg1
    (ψ := ψ) (δ := φ - ψ) (m := Nat.find hp) (by omega) hψOrd hδord s₀
    (le_of_eq hs₀deg)
  have hψδ : ψ + (φ - ψ) = φ := by abel
  have hzero : MvPowerSeries.coeff s₀ (φ - ψ) * (π - π ^ Nat.find hp) = 0 := by
    rw [hψδ, hφ, hψ, MvPowerSeries.coeff_zero, zero_add] at hkey
    exact hkey.symm
  -- `π - π^m = π * (1 - π^{m-1})` and `1 - π^{m-1}` is a unit
  have hu : IsUnit (1 - π ^ (Nat.find hp - 1)) := hπ.1 _ (by omega)
  have hfac : π - π ^ Nat.find hp = π * (1 - π ^ (Nat.find hp - 1)) := by
    have hpow : π ^ Nat.find hp = π * π ^ (Nat.find hp - 1) := by
      have h2 := pow_succ' π (Nat.find hp - 1)
      rw [show Nat.find hp - 1 + 1 = Nat.find hp by omega] at h2
      exact h2
    rw [hpow]; ring
  have hcp : MvPowerSeries.coeff s₀ (φ - ψ) * π = 0 := by
    have h : (MvPowerSeries.coeff s₀ (φ - ψ) * π) * (1 - π ^ (Nat.find hp - 1)) = 0 := by
      rw [mul_assoc, ← hfac]
      exact hzero
    rwa [IsUnit.mul_left_eq_zero hu] at h
  -- `π` is a nonzerodivisor, so the coefficient must vanish: contradiction
  have hc : MvPowerSeries.coeff s₀ (φ - ψ) = 0 := by
    rw [mul_comm] at hcp
    refine hπ.2.2 _ _ ?_
    rw [mul_zero]
    exact hcp
  exact hs₀coeff hc

end NK.LocalReciprocityLubinTate.Uniqueness
