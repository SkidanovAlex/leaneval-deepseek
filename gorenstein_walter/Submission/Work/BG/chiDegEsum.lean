import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset

namespace Work.BG

/-- A `finsum` over a three-element `Set` (used to evaluate the collapsing sum in
`chiDegEsum`). -/
theorem finSumMemTriple {α M : Type} [AddCommMonoid M] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (F : α → M) :
    (∑ᶠ x ∈ ({a, b, c} : Set α), F x) = F a + (F b + F c) := by
  rw [finsum_mem_insert F (by simp [hab, hac]) (Set.toFinite _),
      finsum_mem_insert F (by simp [hbc]) (Set.toFinite _),
      finsum_mem_singleton]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chiDegEsum {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.bset C f χ)
    (hξ : ξ ∈ Work.GW2.C16.bset C f χ) (hνs : Work.BG.sconj C ν ≠ ν) (hξν : ξ ≠ ν)
    (hξνs : ξ ≠ Work.BG.sconj C ν)
    (hbset : Work.GW2.C16.bset C f χ = {ν, Work.BG.sconj C ν, ξ})
    {β α₁ α₂ : ClassFunction ↥(C.P.U) ℂ} (hνβ : Work.BG.restrictU C ν = β)
    (hsνβ : Work.BG.restrictU C (Work.BG.sconj C ν) = β)
    (hξα : Work.BG.restrictU C ξ = α₁ + α₂) (hα1eq : α₁ 1 = α₂ 1)
    (hβodd : ∃ m : ℤ, β 1 = (m : ℂ) ∧ Odd m) (hαodd : ∃ m : ℤ, α₁ 1 = (m : ℂ) ∧ Odd m) :
    ∃ k : ℤ, (∑ θ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) *
          ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = 4 * (k : ℂ) := by
  classical
  -- The degree of `ν`, of `ν^s` and of `ξ`, read off on `U`: `ν(1) = ν^s(1) = β(1)` and
  -- `ξ(1) = α₁(1) + α₂(1)`.
  have hν1 : ν 1 = β 1 := by
    have h := congrArg (fun φ : ClassFunction ↥(C.P.U) ℂ => φ (1 : ↥C.P.U)) hνβ
    rw [Work.BG.restrictU, ClassFunction.compHom_apply] at h
    rw [map_one] at h
    exact h
  have hsν1 : (Work.BG.sconj C ν) 1 = β 1 := by
    have h := congrArg (fun φ : ClassFunction ↥(C.P.U) ℂ => φ (1 : ↥C.P.U)) hsνβ
    rw [Work.BG.restrictU, ClassFunction.compHom_apply] at h
    rw [map_one] at h
    exact h
  have hξ1 : ξ 1 = α₁ 1 + α₂ 1 := by
    have h := congrArg (fun φ : ClassFunction ↥(C.P.U) ℂ => φ (1 : ↥C.P.U)) hξα
    rw [Work.BG.restrictU, ClassFunction.compHom_apply, ClassFunction.add_apply] at h
    rw [map_one] at h
    exact h
  -- The coherent coefficients of `ν`, `ν^s` (equal to that of `ν`) and `ξ` are `±1`,
  -- and `f` is constant on the `s`-pair `{ν, ν^s}`.
  obtain ⟨hstruct1, -⟩ := bset_orbit_struct C f hf χ hχ
  have hfνs : f (Work.BG.sconj C ν) = f ν := (hstruct1 ν hν).2.1
  have hνpm : ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1 :=
    (hstruct1 ν hν).2.2
  have hξpm : ClassFunction.inner χ (f ξ) = 1 ∨ ClassFunction.inner χ (f ξ) = -1 :=
    (hstruct1 ξ hξ).2.2
  -- Odd integer representatives of the degrees.
  obtain ⟨m, hm, hmodd⟩ := hβodd
  obtain ⟨n, hn, hnodd⟩ := hαodd
  have hα2 : α₂ 1 = (n : ℂ) := by rw [← hα1eq]; exact hn
  obtain ⟨az, haz, hazodd⟩ : ∃ az : ℤ, ClassFunction.inner χ (f ν) = (az : ℂ) ∧ Odd az := by
    rcases hνpm with h | h
    · exact ⟨1, by rw [h]; norm_num, ⟨0, by norm_num⟩⟩
    · exact ⟨-1, by rw [h]; norm_num, ⟨-1, by norm_num⟩⟩
  obtain ⟨bz, hbz, hbzodd⟩ : ∃ bz : ℤ, ClassFunction.inner χ (f ξ) = (bz : ℂ) ∧ Odd bz := by
    rcases hξpm with h | h
    · exact ⟨1, by rw [h]; norm_num, ⟨0, by norm_num⟩⟩
    · exact ⟨-1, by rw [h]; norm_num, ⟨-1, by norm_num⟩⟩
  have hev : Even (az * m + bz * n) := (hazodd.mul hmodd).add_odd (hbzodd.mul hnodd)
  rw [even_iff_two_dvd] at hev
  obtain ⟨k, hk⟩ := hev
  refine ⟨k, ?_⟩
  -- Off `𝒮(χ)` every coherent coefficient vanishes, so the sum lives on `𝒮(χ)`.
  have hF : ∀ μ : IrreducibleCharacter ↥C.P.H0,
      (μ : ClassFunction ↥C.P.H0 ℂ) ∉ bset C f χ →
      (fun ρ : ClassFunction ↥C.P.H0 ℂ => ClassFunction.inner χ (f ρ) * (ρ 1))
        (μ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    intro μ hμ
    have hz : ClassFunction.inner χ (f (μ : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
      by_contra hne
      exact hμ ⟨μ.2, hne⟩
    simp only [hz, zero_mul]
  rw [s02_sum_irr_eq_finsum_bset C f χ
      (fun ρ : ClassFunction ↥C.P.H0 ℂ => ClassFunction.inner χ (f ρ) * (ρ 1)) hF]
  -- `𝒮(χ) = {ν, ν^s, ξ}`, so only three characters contribute.
  rw [hbset]
  rw [finSumMemTriple
      (F := fun ρ : ClassFunction ↥C.P.H0 ℂ => ClassFunction.inner χ (f ρ) * (ρ 1))
      (a := ν) (b := Work.BG.sconj C ν) (c := ξ)
      (by intro h; exact hνs h.symm)
      (by intro h; exact hξν h.symm)
      (by intro h; exact hξνs h.symm)]
  -- Substitute all the values: the sum becomes `2 · (az·m + bz·n)`, and `az·m + bz·n`
  -- is even because `az, bz, m, n` are all odd.
  rw [hfνs, hν1, hsν1, hm, hξ1, hn, hα2, haz, hbz]
  have h1 : (az : ℂ) * (m : ℂ) + (bz : ℂ) * (n : ℂ) = (2 * (k : ℂ)) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hk
    push_cast at this
    exact this
  linear_combination 2 * h1

end Work.BG
