import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Values of an irreducible character are algebraic integers: they are traces of
finite-order operators. -/
theorem isIntegral_apply_of_isIrreducibleCharacter' {K : Type*} [Group K] [Finite K]
    {φ : ClassFunction K ℂ} (h : IsIrreducibleCharacter φ) (g : K) :
    IsIntegral ℤ (φ g) := by
  obtain ⟨V, _, _, _, ρ, _, hchar⟩ := h
  rw [congrFun hchar g]
  exact character_isIntegral ρ g

/-- **Arithmetic heart of BG 1981 Lemma 3.3 (first case), abstract form.**

If `χ ∈ Irr(G)` has even degree (`χ(1) ≡ 0 mod 2`) and `|G : C_G(g)|` is odd, then
`χ(g) ≡ 0 (mod 2)`.  Indeed Gorenstein 4.2.10 makes `d · χ(g) / χ(1)` an algebraic integer
for `d = |G : C_G(g)|`; multiplying by the integral number `χ(1)/2` makes `d · χ(g) / 2`
integral, and `χ(g)/2 = d · χ(g)/2 - ((d-1)/2) · χ(g)` is then a difference of two algebraic
integers (`(d-1)/2` is an integer because `d` is odd). -/
theorem algIntModTwo_of_isIrreducibleCharacter_of_even_degree_of_odd_index
    {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) (heven : AlgIntModTwo (χ 1) 0)
    (g : G) (hodd : Odd (Subgroup.centralizer ({g} : Set G)).index) :
    AlgIntModTwo (χ g) 0 := by
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  -- the degree does not vanish
  have hdeg : χ 1 ≠ 0 := by
    obtain ⟨d, hd, h1⟩ := hχ.exists_apply_one_eq_pos_natCast
    rw [h1]
    exact_mod_cast hd.ne'
  -- Gorenstein 4.2.10
  have hci : IsIntegral ℤ
      (((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / χ 1) :=
    centralIntegral χ hχ g
  -- `χ 1 / 2` is an algebraic integer
  obtain ⟨c, hc, hceq⟩ := heven
  have hc1 : χ 1 = 2 * c := by simpa using hceq
  have hhalf : IsIntegral ℤ (χ 1 / 2) := by
    have hc2 : χ 1 / 2 = c := by
      rw [hc1]
      exact mul_div_cancel_left₀ c h2ne
    rw [hc2]
    exact hc
  -- hence `d * χ g / 2` is an algebraic integer
  have hd2 : IsIntegral ℤ (((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / 2) := by
    have heq : ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / 2 =
        (((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / χ 1) * (χ 1 / 2) :=
      (div_mul_div_cancel₀ hdeg).symm
    rw [heq]
    exact hci.mul hhalf
  -- `χ g` is an algebraic integer, and `d = 2k + 1`
  have hg : IsIntegral ℤ (χ g) := isIntegral_apply_of_isIrreducibleCharacter' hχ g
  obtain ⟨k, hk⟩ := hodd
  have hkey : χ g / 2 =
      ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / 2 - (k : ℂ) * χ g := by
    rw [hk]
    push_cast
    refine mul_right_cancel₀ h2ne ?_
    rw [sub_mul, div_mul_cancel₀ (χ g) h2ne,
      div_mul_cancel₀ (((2 : ℂ) * (k : ℂ) + 1) * χ g) h2ne]
    ring
  refine ⟨χ g / 2, ?_, ?_⟩
  · rw [hkey]
    exact hd2.sub ((isIntegral_natCast k).mul hg)
  · rw [sub_zero]
    exact (mul_div_cancel₀ (χ g) h2ne).symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- Parity step of BG 1981 Lemma 3.3, first case (p. 209, "Since `|G : C_G(g)|` is odd for each `g ∈ B`"): if `χ ∈ ±Irr(G)` has even value at `1`, and `h ∈ H₀` lies in `U` and is centralized by the Sylow 2-subgroup `S = D.S`, then `χ h` is even.  Since `S ≤ C_G(h)`, the index `d = |G : C_G(h)|` is odd; Gorenstein 4.2.10 (`Work.BG.centralIntegral`, X3) makes `d * χ h / χ 1` an algebraic integer, and multiplying by the integer `χ 1 / 2` makes `d * χ h / 2` an algebraic integer, whence `χ h / 2 = d * χ h / 2 - ((d-1)/2) * χ h` is an algebraic integer. -/
theorem lemma33Arith {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Work.GW2.C16.Compat D C)
    {χ : ClassFunction G ℂ} (hχ : Work.BG.IsPmIrr χ) (heven : AlgIntModTwo (χ 1) 0)
    {h : ↥C.P.H0} (hcU : (h : G) ∈ C.P.U)
    (hcomm : ∀ s ∈ (D.S : Subgroup G), s * (h : G) * s⁻¹ = (h : G)) :
    AlgIntModTwo (χ (h : G)) 0 := by
  -- `S` centralizes `h`, so `S ≤ C_G(h)`
  have hS_le_C : (D.S : Subgroup G) ≤ Subgroup.centralizer ({(h : G)} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h3 : s * (h : G) * s⁻¹ = (h : G) := hcomm s hs
    calc (h : G) * s = s * (h : G) * s⁻¹ * s := by rw [h3]
      _ = s * (h : G) := by group
  -- hence `|G : C_G(h)|` is odd
  have hoddC : Odd (Subgroup.centralizer ({(h : G)} : Set G)).index := by
    have hoddS : Odd (D.S : Subgroup G).index := by
      have h : ¬ 2 ∣ (D.S : Subgroup G).index := D.S.not_dvd_index
      exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact h)
    exact Odd.of_dvd_nat hoddS (Subgroup.index_dvd_of_le hS_le_C)
  rcases hχ with hχ | hχ
  · exact algIntModTwo_of_isIrreducibleCharacter_of_even_degree_of_odd_index hχ heven
      (h : G) hoddC
  · -- `-χ ∈ Irr(G)` has even degree as well
    have heven' : AlgIntModTwo ((-χ) 1) 0 := by
      obtain ⟨c, hc, hceq⟩ := heven
      refine ⟨-c, hc.neg, ?_⟩
      rw [ClassFunction.neg_apply]
      linear_combination -hceq
    have hres := algIntModTwo_of_isIrreducibleCharacter_of_even_degree_of_odd_index hχ heven'
      (h : G) hoddC
    have h2 : AlgIntModTwo (-(χ (h : G))) 0 := by simpa using hres
    simpa using AlgIntModTwo.neg h2

end Work.BG
