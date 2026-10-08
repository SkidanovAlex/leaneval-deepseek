import Mathlib
import Submission.Work.BG.L41Aux
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_abstractCoherence
import Submission.OddOrder.Algebra.AlgInt

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2.C16

section Helpers

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 0. Elementary helpers for the derivation -/

/-- Coherence clause (iii) in the form used throughout: for `Λ`-equivalent irreducibles the
induced difference is the difference of the coherent extensions. -/
lemma l41_coherent_ind_sub (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ} (hf : IsCoherent C f)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ)
    (hν : IsIrreducibleCharacter ν) (h : LamEquiv C μ ν) :
    ind C (μ - ν) = f μ - f ν :=
  ((hf.1 μ hμ) μ (Or.inl (s02c_LamEquiv_refl C μ)) ν (Or.inl h) hμ hν).2.2.2.1 h

/-- `λ₂ * (λ₂ * μ) = μ`. -/
lemma l41_lam_lam (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (μ : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β₂ * (lamCF C β₂ * μ) = μ := by
  rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]

/-- `λ_β(1) = 1`. -/
lemma l41_lamCF_apply_one' (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β : quotGroup C.P →* ℂˣ) : lamCF C β (1 : ↥C.P.H0) = 1 := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- `(λ_β μ)(1) = μ(1)`. -/
lemma l41_lam_apply_one (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β : quotGroup C.P →* ℂˣ) (μ : ClassFunction ↥C.P.H0 ℂ) :
    (lamCF C β * μ) (1 : ↥C.P.H0) = μ 1 := by
  rw [ClassFunction.mul_apply, l41_lamCF_apply_one' C β, one_mul]

/-- `ind C (μ - ν) = -(ind C (ν - μ))`. -/
lemma l41_ind_neg_sub (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (μ ν : ClassFunction ↥C.P.H0 ℂ) :
    ind C (μ - ν) = -(ind C (ν - μ)) := by
  have h : ind C (μ - ν) + ind C (ν - μ) = 0 := by
    rw [← ClassFunction.induce_add]
    have h0 : (μ - ν : ClassFunction ↥C.P.H0 ℂ) + (ν - μ) = 0 := by
      ext g
      simp only [ClassFunction.add_apply, ClassFunction.sub_apply, ClassFunction.zero_apply]
      ring
    rw [h0, ClassFunction.induce_zero]
  exact eq_neg_of_add_eq_zero_left h

/-- `δ_{λ₂ν} = -δ_ν`. -/
lemma l41_delta_lam (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    delta C β₂ (lamCF C β₂ * ν) = -(delta C β₂ ν) := by
  show ind C (lamCF C β₂ * ν - lamCF C β₂ * (lamCF C β₂ * ν)) =
    -(ind C (ν - lamCF C β₂ * ν))
  rw [l41_lam_lam C h2 ν]
  exact l41_ind_neg_sub C (lamCF C β₂ * ν) ν

/-- Membership in `S4Index C`, unfolded and stripped of the parts already known. -/
lemma l41_s4Index_iff' (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) (hs : sconj C μ = μ) :
    μ ∈ S4Index C ↔ μ C.t = μ 1 := by
  simp only [S4Index, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨hμ, hs, h⟩⟩

/-- The same for `λ₂μ`, using `(λ₂μ)(t) = -μ(t)` and `(λ₂μ)(1) = μ(1)`. -/
lemma l41_lam_s4Index_iff (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) (hs : sconj C μ = μ) :
    lamCF C β₂ * μ ∈ S4Index C ↔ μ C.t = -μ 1 := by
  rw [l41_s4Index_iff' C (lam_two_mul_irr C hμ)
      ((sconj_lam_two_mul_eq_iff C h2 hβ μ).mpr hs),
    lam_two_mul_apply_t C h2 hβ μ, l41_lam_apply_one C β₂ μ]
  rw [neg_eq_iff_eq_neg]

/-- **Exactly one of `μ`, `λ₂μ` lies in `S4Index C`** (existence half). -/
lemma l41_s4_or (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) (hs : sconj C μ = μ) :
    μ ∈ S4Index C ∨ lamCF C β₂ * μ ∈ S4Index C := by
  rcases t_val_or C hμ with h | h
  · exact Or.inl ((l41_s4Index_iff' C hμ hs).mpr h)
  · exact Or.inr ((l41_lam_s4Index_iff C h2 hβ hμ hs).mpr h)

/-- **Exactly one of `μ`, `λ₂μ` lies in `S4Index C`** (exclusion half). -/
lemma l41_lam_not_s4 (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) (hs : sconj C μ = μ)
    (h : μ ∈ S4Index C) : lamCF C β₂ * μ ∉ S4Index C := by
  intro h'
  have h1 : μ C.t = μ 1 := (l41_s4Index_iff' C hμ hs).mp h
  have h2' : μ C.t = -μ 1 := (l41_lam_s4Index_iff C h2 hβ hμ hs).mp h'
  have hEq : μ 1 = -μ 1 := h1.symm.trans h2'
  have hz : μ 1 = 0 := by linear_combination (1 / 2 : ℂ) * hEq
  exact irr_apply_one_ne_zero C hμ hz

/-- At most one member of `Λμ = {μ, λ₂μ}` lies in `𝒮(χ)` when `μ` is `s`-fixed: the two
members of `Λμ` are `s`-conjugate, hence equal, whenever both lie in `𝒮(χ)`. -/
lemma l41_bset_lam_notMem (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ} (hf : IsCoherent C f)
    {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ bset C f χ) (hfixμ : sconj C μ = μ) :
    lamCF C β₂ * μ ∉ bset C f χ := by
  intro hmem
  have h1 := (bset_orbit_struct C f hf χ hχ).2 μ hμ (lamCF C β₂ * μ) hmem
      ⟨β₂, rfl⟩ (lam_two_mul_ne_self C h2 hβ hμ.1)
  rw [hfixμ] at h1
  exact lam_two_mul_ne_self C h2 hβ hμ.1 h1

/-- A sum of an odd number of odd integers is odd. -/
lemma l41_odd_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, Odd (f i)) (hc : Odd (s.card : ℤ)) : Odd (∑ i ∈ s, f i) := by
  have h1 : ∑ i ∈ s, f i = (s.card : ℤ) + ∑ i ∈ s, (f i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [h1]
  exact hc.add_even (Finset.even_sum _ fun i hi => (hf i hi).sub_odd odd_one)

/-- The degree of a signed irreducible character of `G` is an integer. -/
lemma l41_exists_int_degree {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ) :
    ∃ d : ℤ, χ 1 = (d : ℂ) := by
  rcases hχ with h | h
  · obtain ⟨n, -, hval, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    exact ⟨n, by rw [hval]; norm_num⟩
  · obtain ⟨n, -, hval, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    refine ⟨-(n : ℤ), ?_⟩
    have hval' : -(χ 1) = (n : ℂ) := by simpa [ClassFunction.neg_apply] using hval
    have hneg : χ 1 = -(n : ℂ) := by rw [← neg_neg (χ 1), hval']
    rw [hneg]; norm_num

/-- **Oddness of `χ(1)` (BG Lemma 4.1 (iv)).**  Lemma 2.4's mod-2 clause at `u = 1 ∈ U` gives
`χ(1) ≡ Σ_{ν ∈ 𝒮(χ)} ν(1) (mod 2)`; together with the equality of the two degree sums and the
fact that the `𝒮'(χ)`-degree sum is an odd integer, `χ(1)` is an odd integer. -/
lemma l41_odd_of_degCong (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ}
    {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ} (hf : IsCoherent C f)
    {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ)
    (hsum : (∑ᶠ ν ∈ bset C f χ, ν 1) = (∑ᶠ ν ∈ bset' C β₂ χ, ν 1))
    (hdeg : ∃ k : ℤ, (∑ᶠ ν ∈ bset' C β₂ χ, ν 1) = (k : ℂ) ∧ Odd k) :
    ∃ d : ℤ, Odd d ∧ χ 1 = (d : ℂ) := by
  obtain ⟨k, hk, hko⟩ := hdeg
  -- `χ(1) ≡ Σ_{𝒮(χ)} ν(1) (mod 2)`
  have hcong : AlgIntModTwo (χ 1) (∑ᶠ ν ∈ bset C f χ, ν 1) := by
    have h1 : ((1 : ↥C.P.H0) : G) ∈ C.P.U := by simpa using C.P.U.one_mem
    have hres := (lemma24 C f hf χ hχ).2.2 (1 : ↥C.P.H0) h1
    simpa using hres
  rw [hsum, hk] at hcong
  -- `χ(1) = (d : ℂ)`
  obtain ⟨d, hd⟩ := l41_exists_int_degree (G := G) hχ
  rw [hd] at hcong
  -- turn the congruence into a divisibility of integers
  have hcong2 : OddOrder.AlgInt.Cong 2 (d : ℂ) (k : ℂ) := by
    change IsIntegral ℤ (((d : ℂ) - (k : ℂ)) / ((2 : ℤ) : ℂ))
    obtain ⟨c, hcint, hc⟩ := hcong
    have hcq : ((d : ℂ) - (k : ℂ)) / ((2 : ℤ) : ℂ) = c := by
      rw [hc]
      push_cast
      field_simp
    rw [hcq]
    exact hcint
  have hdvd : (2 : ℤ) ∣ d - k :=
    OddOrder.RepresentationTheory.int_dvd_of_cong_intCast (by norm_num : (2 : ℤ) ≠ 0) hcong2
  obtain ⟨z, hz⟩ := hdvd
  obtain ⟨t, ht⟩ := hko
  exact ⟨d, ⟨z + t, by omega⟩, hd⟩

end Helpers

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **The derivation half of BG Lemma 4.1 (pp. 212).**  `hfix`, `hdict`, `hcard`, `hsh` are
clauses (2), (3), (4), (1) of `Work.BG.l41Shape`; the conclusions are the conjuncts of
`Work.GW2.C16.Lemma41Prop`.

Route.  `lemma24` (`hf`) at `g = C.t` (`C.t_not_mem_U`) gives
`χ(t) = Σᶠ_{μ ∈ bset C f χ} (χ, f μ) * μ(t)`.  By `hfix` every `μ ∈ bset` is `s`-fixed and
`|Λμ| = D.n = 2` (`L41Aux.lamOrbit_ncard_eq_two`), so `Λμ = {μ, λ₂μ}` (`λ₂ = lamCF C β₂`)
and exactly one of the two is in `S4Index C` (`L41Aux.t_val_or`); call it `ν_μ`, and
`ν_μ ∈ S4Index C` with `LamEquiv C ν_μ μ`.  By `hdict` and `hcard` the map `μ ↦ ν_μ` is a
bijection `bset C f χ ≃ bset' C β₂ χ` (`bset_orbit_struct` gives injectivity: two members of
`bset` in one `Λ`-orbit are `s`-conjugate, hence equal).  Termwise, using
`hf.1` (coherence (iii)) and `delta C β₂ ν = ind C (ν - λ₂ν)`:
* if `ν_μ = μ` then `μ(t) = μ(1) = ν_μ(1)` and `(χ, δ_{ν_μ}) = (χ, f μ) - (χ, f (λ₂μ)) = (χ, f μ)`
  because `λ₂μ ∉ bset` (at most one member per orbit);
* if `ν_μ = λ₂μ` then `μ(t) = -μ(1)`, `ν_μ(1) = μ(1)` and
  `(χ, δ_{ν_μ}) = -(χ, δ_μ) = (χ, f (λ₂μ)) - (χ, f μ) = -(χ, f μ)`.
Either way `(χ, δ_{ν_μ}) * ν_μ(1) = (χ, f μ) * μ(t)`, so the two finsums agree.
Conjunct (1) is `hcard` + `hsh`.  For conjunct (3): `χ(1) ∈ ℤ` (`IsPmIrr`), each `ν ∈ bset'`
has `ν(1)` an odd integer (`l41_s4Index_one_odd`), `|bset'| ∈ {1,3}`; `lemma24`'s mod-2 clause
at `u = 1 ∈ U` gives `χ(1) ≡ Σ_{ν ∈ bset'} ν(1) (mod 2)` (`AlgIntModTwo`), and
`OddOrder.AlgInt.Cong.int_dvd_of_cong_intCast` (in `Submission/OddOrder/Algebra/AlgInt.lean`)
turns that into `2 ∣` (difference of the two integers), whence `χ(1)` is odd. -/
theorem l41Deriv {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (β₂ : Work.BG.quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    (hfix : ∀ μ ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C μ = μ ∧
        (Work.BG.lamOrbit C μ).ncard = D.n)
    (hdict : ∀ ν ∈ Work.GW2.C16.S4Index C,
        ν ∈ Work.GW2.C16.bset' C β₂ χ ↔
          (Work.GW2.C16.bset C f χ ∩ Work.BG.lamOrbit C ν).Nonempty)
    (hcard : (Work.GW2.C16.bset' C β₂ χ).ncard = (Work.GW2.C16.bset C f χ).ncard)
    (hsh : (Work.GW2.C16.bset C f χ).ncard = 1 ∨ (Work.GW2.C16.bset C f χ).ncard = 3) :
    ((Work.GW2.C16.bset' C β₂ χ).ncard = 1 ∨ (Work.GW2.C16.bset' C β₂ χ).ncard = 3) ∧
    χ (C.t : G) = ∑ᶠ ν ∈ Work.GW2.C16.bset' C β₂ χ,
        ClassFunction.inner χ (Work.GW2.C16.delta C β₂ ν) * ν 1 ∧
    ∃ d : ℤ, Odd d ∧ χ 1 = d := by
  classical
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  -- ## Finiteness and the cardinality clause
  have hSfin : (bset C f χ).Finite := (lemma24 C f hf χ hχ).1
  have hcard' : (bset' C β₂ χ).ncard = 1 ∨ (bset' C β₂ χ).ncard = 3 := by
    rcases hsh with h | h
    · exact Or.inl (hcard.trans h)
    · exact Or.inr (hcard.trans h)
  have hTfin : (bset' C β₂ χ).Finite := by
    rcases hcard' with h | h
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
  -- ## The representative `ν_μ` of `Λμ ∩ S4Index C`
  let rep : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := fun μ =>
    if μ ∈ S4Index C then μ else lamCF C β₂ * μ
  have rep_eq : ∀ μ : ClassFunction ↥C.P.H0 ℂ,
      (μ ∈ S4Index C ∧ rep μ = μ) ∨ (μ ∉ S4Index C ∧ rep μ = lamCF C β₂ * μ) := by
    intro μ
    by_cases h : μ ∈ S4Index C
    · exact Or.inl ⟨h, by simp only [rep]; exact if_pos h⟩
    · exact Or.inr ⟨h, by simp only [rep]; exact if_neg h⟩
  have hLam_rep : ∀ μ : ClassFunction ↥C.P.H0 ℂ, LamEquiv C μ (rep μ) := by
    intro μ
    rcases rep_eq μ with ⟨-, hr⟩ | ⟨-, hr⟩
    · rw [hr]; exact s02c_LamEquiv_refl C μ
    · rw [hr]; exact ⟨β₂, rfl⟩
  have rep_deg : ∀ μ : ClassFunction ↥C.P.H0 ℂ, (rep μ) 1 = μ 1 := by
    intro μ
    rcases rep_eq μ with ⟨-, hr⟩ | ⟨-, hr⟩
    · rw [hr]
    · rw [hr]; exact l41_lam_apply_one C β₂ μ
  have rep_s4 : ∀ μ ∈ bset C f χ, rep μ ∈ S4Index C := by
    intro μ hμ
    rcases rep_eq μ with ⟨h, hr⟩ | ⟨h, hr⟩
    · rw [hr]; exact h
    · rw [hr]
      exact (l41_s4_or C h2 hβ hμ.1 (hfix μ hμ).1).resolve_left h
  have rep_mem : ∀ μ ∈ bset C f χ, rep μ ∈ bset' C β₂ χ := by
    intro μ hμ
    rw [hdict (rep μ) (rep_s4 μ hμ)]
    exact ⟨μ, hμ, s02c_LamEquiv_symm C (hLam_rep μ)⟩
  have rep_inj : ∀ μ₁ ∈ bset C f χ, ∀ μ₂ ∈ bset C f χ, rep μ₁ = rep μ₂ → μ₁ = μ₂ := by
    intro μ₁ h₁ μ₂ h₂ heq
    have hL : LamEquiv C μ₁ μ₂ := by
      have a := hLam_rep μ₁
      have b : LamEquiv C (rep μ₁) μ₂ := by
        rw [heq]; exact s02c_LamEquiv_symm C (hLam_rep μ₂)
      exact s02c_LamEquiv_trans C a b
    by_contra hne
    have hc := (bset_orbit_struct C f hf χ hχ).2 μ₁ h₁ μ₂ h₂ hL (fun h => hne h.symm)
    rw [(hfix μ₁ h₁).1] at hc
    exact hne hc.symm
  have rep_surj : ∀ ν ∈ bset' C β₂ χ, ∃ μ ∈ bset C f χ, rep μ = ν := by
    intro ν hν
    have hνS4 : ν ∈ S4Index C := hν.1
    obtain ⟨μ, hμmem, hμlam⟩ := (hdict ν hνS4).mp hν
    have hcases : μ = ν ∨ μ = lamCF C β₂ * ν := (LamEquiv_iff C h2 hβ ν μ).mp hμlam
    have hnu_choice : ν = μ ∨ ν = lamCF C β₂ * μ := by
      rcases hcases with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (l41_lam_lam C h2 ν).symm)
    have key : ∀ ν' : ClassFunction ↥C.P.H0 ℂ,
        ν' ∈ S4Index C → (ν' = μ ∨ ν' = lamCF C β₂ * μ) → ν' = rep μ := by
      intro ν' hν'S4 hν'c
      rcases rep_eq μ with ⟨hμS4, hr⟩ | ⟨hμnS4, hr⟩
      · rw [hr]
        rcases hν'c with h | h
        · exact h
        · exact absurd (h ▸ hν'S4)
            (l41_lam_not_s4 C h2 hβ hμmem.1 (hfix μ hμmem).1 hμS4)
      · rw [hr]
        rcases hν'c with h | h
        · exact absurd (h ▸ hν'S4) hμnS4
        · exact h
    exact ⟨μ, hμmem, (key ν hνS4 hnu_choice).symm⟩
  -- ## The termwise identity
  have rep_term : ∀ μ ∈ bset C f χ,
      ClassFunction.inner χ (f μ) * μ C.t =
        ClassFunction.inner χ (delta C β₂ (rep μ)) * (rep μ) 1 := by
    intro μ hμ
    have hμirr : IsIrreducibleCharacter μ := hμ.1
    have hfixμ : sconj C μ = μ := (hfix μ hμ).1
    have hνs4 : rep μ ∈ S4Index C := rep_s4 μ hμ
    have hνeq : rep μ = μ ∨ rep μ = lamCF C β₂ * μ := by
      rcases rep_eq μ with ⟨-, hr⟩ | ⟨-, hr⟩
      · exact Or.inl hr
      · exact Or.inr hr
    have hnotmem : lamCF C β₂ * μ ∉ bset C f χ :=
      l41_bset_lam_notMem C h2 hβ hf hχ hμ hfixμ
    have hzero : ClassFunction.inner χ (f (lamCF C β₂ * μ)) = 0 := by
      by_contra hc0
      exact hnotmem ⟨lam_two_mul_irr C hμirr, hc0⟩
    have hdel : delta C β₂ μ = f μ - f (lamCF C β₂ * μ) :=
      l41_coherent_ind_sub C hf hμirr (lam_two_mul_irr C hμirr) ⟨β₂, rfl⟩
    rcases hνeq with hνeq | hνeq
    · -- `ν_μ = μ`: `μ(t) = μ(1)` and `(χ, δ_μ) = (χ, f μ)`
      have hval : μ C.t = μ 1 := by
        have hmem : μ ∈ S4Index C := by rw [← hνeq]; exact hνs4
        exact (l41_s4Index_iff' C hμirr hfixμ).mp hmem
      rw [hνeq, hdel, ClassFunction.inner_sub_right, hzero, sub_zero, hval]
    · -- `ν_μ = λ₂μ`: `μ(t) = -μ(1)` and `(χ, δ_{λ₂μ}) = -(χ, f μ)`
      have hdel2 : delta C β₂ (lamCF C β₂ * μ) = -(f μ - f (lamCF C β₂ * μ)) := by
        rw [l41_delta_lam C h2 μ, hdel]
      have hval : μ C.t = -μ 1 := by
        have hmem : lamCF C β₂ * μ ∈ S4Index C := by rw [← hνeq]; exact hνs4
        have h1 := (l41_s4Index_iff' C (lam_two_mul_irr C hμirr)
          ((sconj_lam_two_mul_eq_iff C h2 hβ μ).mpr hfixμ)).mp hmem
        rw [lam_two_mul_apply_t C h2 hβ μ, l41_lam_apply_one C β₂ μ] at h1
        rwa [neg_eq_iff_eq_neg] at h1
      rw [hνeq, hdel2, ClassFunction.inner_neg_right, ClassFunction.inner_sub_right,
        hzero, sub_zero, l41_lam_apply_one C β₂ μ, hval]
      ring
  -- ## The two sums agree, term by term
  have hsum_eq : (∑ᶠ μ ∈ bset C f χ, ClassFunction.inner χ (f μ) * μ C.t) =
      (∑ᶠ ν ∈ bset' C β₂ χ, ClassFunction.inner χ (delta C β₂ ν) * ν 1) := by
    rw [finsum_mem_eq_finite_toFinset_sum
        (fun μ => ClassFunction.inner χ (f μ) * μ C.t) hSfin,
      finsum_mem_eq_finite_toFinset_sum
        (fun ν => ClassFunction.inner χ (delta C β₂ ν) * ν 1) hTfin]
    refine Finset.sum_bij (fun a _ => rep a) ?_ ?_ ?_ ?_
    · intro a ha
      exact (Set.Finite.mem_toFinset hTfin).mpr
        (rep_mem a ((Set.Finite.mem_toFinset hSfin).mp ha))
    · intro a₁ ha₁ a₂ ha₂ heq
      exact rep_inj a₁ ((Set.Finite.mem_toFinset hSfin).mp ha₁) a₂
        ((Set.Finite.mem_toFinset hSfin).mp ha₂) heq
    · intro b hb
      obtain ⟨a, ha, hrep⟩ := rep_surj b ((Set.Finite.mem_toFinset hTfin).mp hb)
      exact ⟨a, (Set.Finite.mem_toFinset hSfin).mpr ha, hrep⟩
    · intro a ha
      exact rep_term a ((Set.Finite.mem_toFinset hSfin).mp ha)
  have hsum_eq_deg : (∑ᶠ μ ∈ bset C f χ, μ 1) = (∑ᶠ ν ∈ bset' C β₂ χ, ν 1) := by
    rw [finsum_mem_eq_finite_toFinset_sum (fun μ => μ 1) hSfin,
      finsum_mem_eq_finite_toFinset_sum (fun ν => ν 1) hTfin]
    refine Finset.sum_bij (fun a _ => rep a) ?_ ?_ ?_ ?_
    · intro a ha
      exact (Set.Finite.mem_toFinset hTfin).mpr
        (rep_mem a ((Set.Finite.mem_toFinset hSfin).mp ha))
    · intro a₁ ha₁ a₂ ha₂ heq
      exact rep_inj a₁ ((Set.Finite.mem_toFinset hSfin).mp ha₁) a₂
        ((Set.Finite.mem_toFinset hSfin).mp ha₂) heq
    · intro b hb
      obtain ⟨a, ha, hrep⟩ := rep_surj b ((Set.Finite.mem_toFinset hTfin).mp hb)
      exact ⟨a, (Set.Finite.mem_toFinset hSfin).mpr ha, hrep⟩
    · intro a ha
      exact (rep_deg a).symm
  -- ## The degree sum over `𝒮'(χ)` is an odd integer
  have hdegOdd : ∃ k : ℤ, (∑ᶠ ν ∈ bset' C β₂ χ, ν 1) = (k : ℂ) ∧ Odd k := by
    have hdeg : ∀ ν ∈ bset' C β₂ χ, ∃ d : ℤ, Odd d ∧ ν 1 = (d : ℂ) :=
      fun ν hν => l41_s4Index_one_odd D C hc hn hν.1
    let dg : ClassFunction ↥C.P.H0 ℂ → ℤ := fun ν =>
      if h : ν ∈ bset' C β₂ χ then Classical.choose (hdeg ν h) else 0
    have hdgspec : ∀ ν (h : ν ∈ bset' C β₂ χ), ν 1 = (dg ν : ℂ) ∧ Odd (dg ν) := by
      intro ν h
      have h' : dg ν = Classical.choose (hdeg ν h) := by dsimp only [dg]; rw [dif_pos h]
      rw [h']
      exact ⟨(Classical.choose_spec (hdeg ν h)).2, (Classical.choose_spec (hdeg ν h)).1⟩
    refine ⟨∑ ν ∈ hTfin.toFinset, dg ν, ?_, ?_⟩
    · rw [finsum_mem_eq_finite_toFinset_sum (fun ν => ν 1) hTfin]
      push_cast
      exact Finset.sum_congr rfl fun ν hν =>
        (hdgspec ν ((Set.Finite.mem_toFinset hTfin).mp hν)).1
    · have hc1 : hTfin.toFinset.card = 1 ∨ hTfin.toFinset.card = 3 := by
        have h := hcard'
        rwa [Set.ncard_eq_toFinset_card (bset' C β₂ χ) hTfin] at h
      have hcard_odd : Odd (hTfin.toFinset.card : ℤ) := by
        rcases hc1 with h | h <;> rw [h] <;> norm_num
      exact l41_odd_finset_sum _ _ (fun ν hν =>
        (hdgspec ν ((Set.Finite.mem_toFinset hTfin).mp hν)).2) hcard_odd
  refine ⟨hcard', ?_, ?_⟩
  · rw [← hsum_eq]
    exact (lemma24 C f hf χ hχ).2.1 C.t C.t_not_mem_U
  · exact l41_odd_of_degCong C hf hχ hsum_eq_deg hdegOdd

end Work.BG
