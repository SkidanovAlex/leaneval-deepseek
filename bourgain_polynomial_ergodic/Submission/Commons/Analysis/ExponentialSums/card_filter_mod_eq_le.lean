import Mathlib

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

theorem card_filter_mod_eq_le (M q r : ℕ) (hq : 0 < q) :
    ((Finset.filter (fun h : ℕ => h % q = r) (Finset.Icc 1 M)).card : ℝ) ≤ (M:ℝ)/(q:ℝ) + 1 := by
  set S : Finset ℕ := Finset.filter (fun h : ℕ => h % q = r) (Finset.Icc 1 M) with hS
  -- every element of the filtered set is of the shape `q * k + r`
  have hkey : ∀ h ∈ S, h = q * (h / q) + r := by
    intro h hh
    rw [hS, Finset.mem_filter] at hh
    obtain ⟨-, hmod⟩ := hh
    calc h = q * (h / q) + h % q := (Nat.div_add_mod h q).symm
      _ = q * (h / q) + r := by rw [hmod]
  -- the map `h ↦ h / q` sends `S` into `{0, …, M / q}`
  have hsub : ∀ h ∈ S, h / q ∈ Finset.Icc 0 (M / q) := by
    intro h hh
    rw [hS, Finset.mem_filter] at hh
    obtain ⟨hIcc, -⟩ := hh
    have hM : h ≤ M := (Finset.mem_Icc.mp hIcc).2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hM⟩
  have hmaps : Set.MapsTo (fun h : ℕ => h / q) (S : Set ℕ)
      ((Finset.Icc 0 (M / q) : Finset ℕ) : Set ℕ) :=
    fun h hh => hsub h hh
  -- and it is injective on `S`
  have hinj : (S : Set ℕ).InjOn (fun h : ℕ => h / q) := by
    intro h₁ h₁S h₂ h₂S heq
    change h₁ / q = h₂ / q at heq
    have e₁ := hkey h₁ h₁S
    have e₂ := hkey h₂ h₂S
    rw [e₁, heq]
    exact e₂.symm
  have hcard : S.card ≤ (Finset.Icc 0 (M / q)).card :=
    Finset.card_le_card_of_injOn (fun h : ℕ => h / q) hmaps hinj
  have hcard' : (Finset.Icc 0 (M / q)).card = M / q + 1 := by simp
  have hnat : S.card ≤ M / q + 1 := by
    rw [hcard'] at hcard
    exact hcard
  calc (S.card : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((M / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (M:ℝ)/(q:ℝ) + 1 := by
        have h := Nat.cast_div_le (α := ℝ) (m := M) (n := q)
        linarith

end Commons.Analysis.ExponentialSums
