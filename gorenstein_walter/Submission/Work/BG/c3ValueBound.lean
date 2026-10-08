import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.centralValue
import Submission.Work.BG.c3vbCharBridge
import Submission.Work.BG.c3vbOrbit
import Submission.Work.BG.c3vbDegree
import Submission.Work.BG.degreeSqNonReal

/-!
# Area BG: the per-character value bound of Bender–Glauberman Theorem C

`Work.BG.c3ValueBound` is BG 1981, p. 211, facts (3) and (5): for `ν ∈ 𝒮(χ₁) = bset C f χ₁`
with `ν ≠ κ` (`κ = κ₁` an admissible linear character), the value `ν(t)` is an integer `m` with
`|m| ≤ |B|`, and `m² ≤ 2|B|`.

The proof uses the degree form of the same step, `Work.BG.c3vbDegree`: `ν(1)` is `β(1)` or
`2β(1)` for some irreducible `β` of `B = C_U(S)` (this is where BG's Lemma 3.3/3.4 input,
Remark 3.1 and the §3 hypothesis are consumed).  Then

* `β(1)² ≤ |B : ⊥| = |B|` (Isaacs Cor. 2.30 / Schur's bound with the trivial centre),
* if `β` is non-trivial and odd order, then `β ≠ β̄` (Peterfalvi (1.1)), so `2β(1)² ≤ |B|`,
* `ν(t) = ±ν(1)` because `t` is a central involution (`centralValue`), and `ν(1) ∈ ℕ`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3ValueBound {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Compat D C) (hThm : ThmCHyps D K1 K2) (hn : 4 ≤ D.n) (hSec3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : IsKappa D C κ)
    (χ₁ : ClassFunction G ℂ) (hχ : IsPmIrr χ₁) (hi : ClassFunction.inner χ₁ (f κ) = 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ bset C f χ₁) (hνκ : ν ≠ κ) :
    ∃ m : ℤ, ν C.t = (m : ℂ) ∧ |m| ≤ (Nat.card D.B : ℤ) ∧
      ((bset C f χ₁).ncard ≤ 2 → m ^ 2 ≤ 2 * (Nat.card D.B : ℤ)) := by
  classical
  -- the degree of `ν` is a natural number
  obtain ⟨n, hnpos, hn1, -⟩ := hν.1.exists_natDegree_charValue_one_dvd_card
  -- the `B`-character controlling the degree of `ν`
  obtain ⟨β, hβirr, hβdeg⟩ :=
    c3vbDegree D C K1 K2 hC hThm hn hSec3 f hf κ hκ χ₁ hχ hi ν hν hνκ
  obtain ⟨-, -, -, -, hB', -⟩ := hThm
  have hBne : D.B ≠ ⊥ := by
    intro hbot
    exact hB' (by rw [hbot]; simp)
  have hB2 : 2 ≤ Nat.card ↥D.B := by
    have h := (Subgroup.one_lt_card_iff_ne_bot (H := D.B)).mpr hBne
    omega
  have hBodd : Odd (Nat.card ↥D.B) := by
    refine Odd.of_dvd_nat (odd_card_U_of_compat hC) ?_
    refine Subgroup.card_dvd_of_le ?_
    rw [hC.U_eq]
    exact le_trans inf_le_left inf_le_left
  -- Schur's bound `β(1)² ≤ |B|` (with the trivial centre)
  obtain ⟨d, hd1, hd2⟩ := hβirr.exists_degree_sq_le_index (⊥ : Subgroup ↥D.B) bot_le
  rw [Subgroup.index_bot] at hd2
  obtain ⟨d₀, hd₀pos, hd₀1, -⟩ := hβirr.exists_natDegree_charValue_one_dvd_card
  have hdpos : 1 ≤ d := by
    have h : (d : ℂ) = (d₀ : ℂ) := by rw [← hd1, hd₀1]
    have h' : d = d₀ := by exact_mod_cast h
    rw [h']
    exact hd₀pos
  have hdle : d ≤ Nat.card ↥D.B := by
    calc d ≤ d ^ 2 := by nlinarith [hdpos]
      _ ≤ Nat.card ↥D.B := hd2
  -- the degree of `ν` is `β(1)` or `2β(1)`
  have hdeg2 : n = d ∨ n = 2 * d := by
    rcases hβdeg with h | h
    · left
      have hc : (n : ℂ) = (d : ℂ) := by rw [← hn1, h, hd1]
      exact_mod_cast hc
    · right
      have hc : (n : ℂ) = ((2 * d : ℕ) : ℂ) := by rw [← hn1, h, hd1]; push_cast; ring
      exact_mod_cast hc
  -- the numerical bound for `ν(1) = n`
  have hn_bound : n ^ 2 ≤ 2 * Nat.card ↥D.B ∧ n ≤ Nat.card ↥D.B := by
    rcases hdeg2 with h | h
    · subst h
      exact ⟨le_trans hd2 (Nat.le_mul_of_pos_left _ (by norm_num)), hdle⟩
    · subst h
      by_cases hβtriv : β = trivialClassFunction ↥D.B
      · have hd1' : d = 1 := by
          have hc : (d : ℂ) = 1 := by rw [← hd1, hβtriv]; rfl
          exact_mod_cast hc
        subst hd1'
        omega
      · have hnr : ¬ ClassFunction.IsReal β := by
          intro hreal
          have h1 := realIrreducibleCharacter_eq_trivial_of_odd_card' hBodd
            (⟨⟨β, hβirr⟩, hreal⟩ : RealIrreducibleCharacter ↥D.B)
          apply hβtriv
          have h2 : ((⟨⟨β, hβirr⟩, hreal⟩ : RealIrreducibleCharacter ↥D.B) :
              IrreducibleCharacter ↥D.B) = ⟨β, hβirr⟩ := rfl
          rw [h2] at h1
          have h3 : ((⟨β, hβirr⟩ : IrreducibleCharacter ↥D.B) : ClassFunction ↥D.B ℂ) = β := rfl
          have h4 := congrArg
            (fun χ : IrreducibleCharacter ↥D.B => (χ : ClassFunction ↥D.B ℂ)) h1
          rw [h3] at h4
          rw [h4]
          rfl
        obtain ⟨d', hd'1, hd'2⟩ := degreeSqNonReal hBodd hβirr hnr
        have hdd' : d = d' := by
          have hc : (d : ℂ) = (d' : ℂ) := by rw [← hd1, hd'1]
          exact_mod_cast hc
        subst hdd'
        refine ⟨?_, ?_⟩
        · nlinarith [hd'2]
        · nlinarith [hd'2, hdpos]
  -- the central value `ν(t) = ±ν(1)`
  have hcv := (centralValue C ν hν.1).1
  rcases hcv with hcv | hcv
  · refine ⟨(n : ℤ), ?_, ?_, ?_⟩
    · rw [hcv, hn1]; push_cast; ring
    · rw [abs_of_nonneg (Int.natCast_nonneg n)]; exact_mod_cast hn_bound.2
    · intro _; exact_mod_cast hn_bound.1
  · refine ⟨-(n : ℤ), ?_, ?_, ?_⟩
    · rw [hcv, hn1]; push_cast; ring
    · rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg n)]; exact_mod_cast hn_bound.2
    · intro _; rw [neg_sq]; exact_mod_cast hn_bound.1

end Work.BG
