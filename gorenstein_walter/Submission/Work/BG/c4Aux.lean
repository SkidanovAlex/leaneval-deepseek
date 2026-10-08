import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.L41Aux
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.thmCSmallAux

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `t = t₁t₂` generates `S₀`, so `C.t` lies in `S₀`. -/
theorem ht_mem_S0 (D : Work.GW2.BGData G) (C : Sec2Ctx G) (hC : Compat D C) (hn : D.n = 2) :
    (C.t : G) ∈ D.S0 := by
  obtain ⟨ht_eq, -, -, -, -⟩ := thmCSmallAux D hn
  rw [hC.t_eq, ht_eq, D.gen]
  exact Subgroup.mem_zpowers _

/-- `κ ∈ S4Index C` for `κ` an admissible `κ₁`. -/
theorem kappa_mem_S4Index (D : Work.GW2.BGData G) (C : Sec2Ctx G) (hC : Compat D C)
    (hn : D.n = 2) {κ : ClassFunction ↥C.P.H0 ℂ} (hκ : IsKappa D C κ) :
    κ ∈ S4Index C := by
  obtain ⟨hirr, h1, hsconj, htriv, -⟩ := hκ
  refine ⟨hirr, hsconj, ?_⟩
  rw [h1]
  exact htriv C.t (ht_mem_S0 D C hC hn)

/-- `λ₂` is `1` at the identity. -/
theorem lamCF_apply_one' (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β (1 : ↥C.P.H0) = 1 := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- For `μ, ν ∈ S4Index C`, `λ₂μ ≠ ν`. -/
theorem lam_two_mul_ne_of_s4 (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ S4Index C) (hν : ν ∈ S4Index C) :
    lamCF C β₂ * μ ≠ ν := by
  obtain ⟨hirrμ, -, htμ⟩ := hμ
  obtain ⟨hirrν, -, htν⟩ := hν
  intro h
  have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
  rw [lam_two_mul_apply_t C h2 hβ μ, htμ, htν] at h1
  have h2' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ 1) h
  rw [ClassFunction.mul_apply, lamCF_apply_one' C β₂, one_mul] at h2'
  rw [h2'] at h1
  have hνeq : ν 1 = -ν 1 := h1.symm
  have h2m : (2 : ℂ) * ν 1 = 0 := by linear_combination hνeq
  exact irr_apply_one_ne_zero C hirrν ((mul_eq_zero.mp h2m).resolve_left (by norm_num))

/-- For `μ, ν ∈ S4Index C`, `μ ≠ λ₂ν`. -/
theorem s4_ne_lam_two_mul (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ S4Index C) (hν : ν ∈ S4Index C) :
    μ ≠ lamCF C β₂ * ν :=
  fun h => lam_two_mul_ne_of_s4 C (β₂ := β₂) h2 hβ hν hμ h.symm

/-- Distinct members of `S4Index C` have orthogonal `δ`'s (in the `|S| = 2` case). -/
theorem delta_orth (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2) {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν μ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) (hμ : μ ∈ S4Index C)
    (hne : μ ≠ ν) :
    ClassFunction.inner (delta C β₂ ν) (delta C β₂ μ) = 0 := by
  classical
  have hirrν : IsIrreducibleCharacter ν := hν.1
  have hsconjν : sconj C ν = ν := hν.2.1
  have hirrμ : IsIrreducibleCharacter μ := hμ.1
  have h2 : Nat.card (quotGroup C.P) = 2 := by
    rw [← Subgroup.index_eq_card (Uin C), rem31IndexUin D C hc, hn]
  have hlam2 : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hirrν
  have hlam2μ : IsIrreducibleCharacter (lamCF C β₂ * μ) := lam_two_mul_irr C hirrμ
  have hsq := lamCF_two_mul_self (C := C) (β₂ := β₂) h2
  have hgram := s02_gram C ν (lamCF C β₂ * ν) μ (lamCF C β₂ * μ)
    hirrν hlam2 hirrμ hlam2μ ⟨β₂, rfl⟩ ⟨β₂, rfl⟩
  have hfixlamν : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν :=
    (sconj_lam_two_mul_eq_iff C h2 hβ ν).mpr hsconjν
  have hA : cH C ν μ = 0 := by
    have hc : cH C ν μ
        = (if μ = ν then 1 else 0) + (if μ = sconj C ν then 1 else 0) := rfl
    rw [hc, if_neg hne, if_neg (by rw [hsconjν]; exact hne)]
    norm_num
  have hB : cH C ν (lamCF C β₂ * μ) = 0 := by
    have hc : cH C ν (lamCF C β₂ * μ)
        = (if (lamCF C β₂ * μ) = ν then 1 else 0)
          + (if (lamCF C β₂ * μ) = sconj C ν then 1 else 0) := rfl
    rw [hc, if_neg (lam_two_mul_ne_of_s4 C h2 hβ hμ hν),
      if_neg (by rw [hsconjν]; exact lam_two_mul_ne_of_s4 C h2 hβ hμ hν)]
    norm_num
  have hC : cH C (lamCF C β₂ * ν) μ = 0 := by
    have hc : cH C (lamCF C β₂ * ν) μ
        = (if μ = lamCF C β₂ * ν then 1 else 0)
          + (if μ = sconj C (lamCF C β₂ * ν) then 1 else 0) := rfl
    rw [hc, if_neg (s4_ne_lam_two_mul C h2 hβ hμ hν),
      if_neg (by rw [hfixlamν]; exact s4_ne_lam_two_mul C h2 hβ hμ hν)]
    norm_num
  have hD : cH C (lamCF C β₂ * ν) (lamCF C β₂ * μ) = 0 := by
    have hne2 : lamCF C β₂ * μ ≠ lamCF C β₂ * ν := by
      intro h
      have hμν : μ = ν := by
        calc μ = (linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) : ClassFunction ↥C.P.H0 ℂ) * μ := by
              rw [one_mul_cf]
          _ = (lamCF C β₂ * lamCF C β₂) * μ := by rw [hsq]
          _ = lamCF C β₂ * (lamCF C β₂ * μ) := by rw [mul_assoc_cf]
          _ = lamCF C β₂ * (lamCF C β₂ * ν) := by rw [h]
          _ = (lamCF C β₂ * lamCF C β₂) * ν := by rw [mul_assoc_cf]
          _ = (linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) : ClassFunction ↥C.P.H0 ℂ) * ν := by
              rw [hsq]
          _ = ν := by rw [one_mul_cf]
      exact hne hμν
    have hc : cH C (lamCF C β₂ * ν) (lamCF C β₂ * μ)
        = (if (lamCF C β₂ * μ) = lamCF C β₂ * ν then 1 else 0)
          + (if (lamCF C β₂ * μ) = sconj C (lamCF C β₂ * ν) then 1 else 0) := rfl
    rw [hc, if_neg hne2, if_neg (by rw [hfixlamν]; exact hne2)]
    norm_num
  simp only [delta]
  rw [hgram, hA, hB, hC, hD]
  norm_num

/-- `δ` is injective on `S4Index C` (both sides `s`-fixed). -/
theorem delta_injective (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2) {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {κ ν : ClassFunction ↥C.P.H0 ℂ} (hκ : κ ∈ S4Index C) (hν : ν ∈ S4Index C)
    (hnorm : ClassFunction.inner (delta C β₂ κ) (delta C β₂ κ) = 4)
    (heq : delta C β₂ ν = delta C β₂ κ) : ν = κ := by
  by_contra hne
  have horth := delta_orth D C hc hn hβ hκ hν hne
  rw [heq] at horth
  rw [hnorm] at horth
  norm_num at horth

/-- A signed irreducible that is not orthogonal to both `a` and `b` prevents `a`, `b` from
being disjoint. -/
theorem not_disjointCF_of_inner_ne_zero {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {a b χ : ClassFunction K ℂ}
    (hχ : IsPmIrr χ) (ha : ClassFunction.inner χ a ≠ 0)
    (hb : ClassFunction.inner χ b ≠ 0) : ¬ DisjointCF a b := by
  have ha' : ClassFunction.inner a χ ≠ 0 := by
    intro h0
    exact ha (by rw [ClassFunction.inner_star_comm, h0, star_zero])
  have hb' : ClassFunction.inner b χ ≠ 0 := by
    intro h0
    exact hb (by rw [ClassFunction.inner_star_comm, h0, star_zero])
  intro hd
  rcases hχ with hχ | hχ
  · rcases hd (⟨χ, hχ⟩ : IrreducibleCharacter K) with h | h
    · exact ha' h
    · exact hb' h
  · rcases hd (⟨-χ, hχ⟩ : IrreducibleCharacter K) with h | h
    · rw [ClassFunction.inner_neg_right] at h
      exact ha' (neg_eq_zero.mp h)
    · rw [ClassFunction.inner_neg_right] at h
      exact hb' (neg_eq_zero.mp h)

/-- The negative of a signed irreducible is a signed irreducible. -/
theorem isPmIrr_neg {K : Type} [Group K] {φ : ClassFunction K ℂ} (h : IsPmIrr φ) :
    IsPmIrr (-φ) := by
  rcases h with h | h
  · exact Or.inr (by rw [neg_neg]; exact h)
  · exact Or.inl h

/-- Two signed irreducibles with inner product `1` are equal. -/
theorem pmIrr_inner_one_eq {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ ψ : ClassFunction K ℂ} (hφ : IsPmIrr φ)
    (hψ : IsPmIrr ψ) (h : ClassFunction.inner φ ψ = 1) : φ = ψ := by
  rcases hφ with hφ | hφ <;> rcases hψ with hψ | hψ
  · rw [irr_cf_inner hφ hψ] at h
    by_contra hne
    rw [ite_eq_right hne] at h
    exact one_ne_zero h.symm
  · exfalso
    have h' := irr_cf_inner hφ hψ
    rw [ClassFunction.inner_neg_right, h] at h'
    by_cases hcase : φ = -ψ
    · rw [ite_eq_left hcase] at h'; norm_num at h'
    · rw [ite_eq_right hcase] at h'; norm_num at h'
  · exfalso
    have h' := irr_cf_inner hφ hψ
    rw [ClassFunction.inner_neg_left, h] at h'
    by_cases hcase : -φ = ψ
    · rw [ite_eq_left hcase] at h'; norm_num at h'
    · rw [ite_eq_right hcase] at h'; norm_num at h'
  · have h' := irr_cf_inner hφ hψ
    simp only [ClassFunction.inner_neg_right, ClassFunction.inner_neg_left, h, neg_neg] at h'
    by_contra hne
    have hcase : ¬ (-φ = -ψ) := fun hh => hne (neg_inj.mp hh)
    rw [ite_eq_right hcase] at h'
    norm_num at h'

/-- `‖φ + ψ‖² = 4` for signed irreducibles forces `φ = ψ`. -/
theorem pmIrr_add_eq_of_norm_four {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ ψ : ClassFunction K ℂ} (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ)
    (h : ClassFunction.inner (φ + ψ) (φ + ψ) = 4) : φ = ψ := by
  obtain ⟨m, hm, -⟩ :=
    inner_eq_int_and_sq_le (IsPmIrr.mem_ZIrr hφ) 1 (by rw [Nat.cast_one]; exact IsPmIrr.inner_self hφ) hψ
  have hstar : ClassFunction.inner ψ φ = (m : ℂ) := by
    have hs := ClassFunction.inner_star_comm ψ φ
    rw [hm, star_intCast] at hs
    exact hs
  have h2 : ClassFunction.inner (φ + ψ) (φ + ψ) = (m : ℂ) + (m : ℂ) + 2 := by
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, IsPmIrr.inner_self hφ, IsPmIrr.inner_self hψ, hstar, hm]
    ring
  rw [h2] at h
  have hm1 : m = 1 := by
    have hh : (m : ℂ) = 1 := by linear_combination (1 / 2 : ℂ) * h
    exact_mod_cast hh
  rw [hm1] at hm
  exact pmIrr_inner_one_eq hφ hψ (by simpa using hm)

end Work.BG
