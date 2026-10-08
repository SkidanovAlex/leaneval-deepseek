import Mathlib
import Submission.Work.BG.Assemblies
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.keyBigArith
import Submission.Work.BG.keyBigAsm
import Submission.Work.BG.arithC4
import Submission.Work.BG.arithC4b
import Submission.Work.BG.indexOdd
import Submission.Work.BG.kEqSmall
import Submission.Work.BG.L41Aux
import Submission.Work.BG.s4Decomp
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.decompBig
import Submission.Work.BG.s02_lemma21_aux

/-!
# Area BG: wave-5 assembly `thmCSmallAsm` (`|S| = 4`, Bender–Glauberman 1981)

Assembly of `Work.GW2.C16.ThmCSmallAsmProp` from the character-theoretic leaves of
`Work.GW2.C16` (BG 1981, pp. 214–215).

Route (BG p. 215):

* `δ_κ := (κ - λ₂κ)* = χ₁ + χ₂ + χ₃ + χ₄` (`C4-ID`) with the identity
  `2k²/|G:H| = Σ χᵢ(t)²/χᵢ(1)` (equation (2));
* `(1 - λ₂)* = 1_G + φ₁ + φ₂ + φ₃` (`S4-DEC`), and Lemma 2.2 at `κ = λ₁`, `ν = λ₂` gives
  the identity `2k²/|G:H| = 1 + Σ 1/φⱼ(1)` (equation (1));
* `C4-VAL`: either all `χᵢ(t) = 1`, or `2k² d = 8|G:H|`, in which case `AR-C4b` forces
  `|K| = 1`, contradicting `KNeOneProp`;
* in the remaining case `AR-C4` compares (1) with (2): both `|χᵢ(1)|` and `|φⱼ(1)|` are
  `≥ 5` by `C4-DEG`, and `1 + 1/a + 1/b + 1/c > 3/5 > Σ 1/dᵢ`.

The `C4-DEG` applications need an `s`-fixed member of `𝒮(χ)`.  For `χ = φⱼ` it is `λ₁` or
`λ₂` (because `f λ₁ - f λ₂ = 1_G + φ₁ + φ₂ + φ₃` has nonzero inner product with `φⱼ`), and for
`χ = χᵢ` it is `κ` or `λ₂κ` (because `f κ - f (λ₂κ) = χ₁+χ₂+χ₃+χ₄` has nonzero inner product
with `χᵢ`).  All four of `λ₁, λ₂, κ, λ₂κ` are `s`-fixed, `λ₁`/`κ` by hypothesis and `λ₂`/`λ₂κ`
because `β₂` and `κ` are `s`-fixed.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

set_option maxHeartbeats 1000000

/-! ## 1. Inner products of signed irreducible characters -/

section PmIrr

variable {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]

/-- A signed irreducible character has square norm `1`. -/
theorem pmIrr_inner_self {ν : ClassFunction K ℂ} (h : IsPmIrr ν) :
    ClassFunction.inner ν ν = 1 := by
  rcases h with h | h
  · rw [irreducibleCharacter_inner_eq_ite ⟨ν, h⟩ ⟨ν, h⟩, if_pos rfl]
  · have key : ClassFunction.inner (-ν) (-ν) = ClassFunction.inner ν ν := by
      rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg]
    rw [← key, irreducibleCharacter_inner_eq_ite ⟨-ν, h⟩ ⟨-ν, h⟩, if_pos rfl]

/-- Two signed irreducible characters have inner product `0` or `1`, unless one is the
negative of the other. -/
theorem pmIrr_inner_eq_zero_or_one {ν₁ ν₂ : ClassFunction K ℂ} (h₁ : IsPmIrr ν₁)
    (h₂ : IsPmIrr ν₂) (hne : ν₁ ≠ -ν₂) :
    ClassFunction.inner ν₁ ν₂ = 0 ∨ ClassFunction.inner ν₁ ν₂ = 1 := by
  classical
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · rw [irreducibleCharacter_inner_eq_ite ⟨ν₁, h₁⟩ ⟨ν₂, h₂⟩]
      by_cases h : (⟨ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨ν₂, h₂⟩
      · rw [if_pos h]; exact Or.inr rfl
      · rw [if_neg h]; exact Or.inl rfl
    · have key : ClassFunction.inner ν₁ (-ν₂)
          = (if (⟨ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨-ν₂, h₂⟩ then (1 : ℂ) else 0) :=
        irreducibleCharacter_inner_eq_ite ⟨ν₁, h₁⟩ ⟨-ν₂, h₂⟩
      by_cases h : (⟨ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨-ν₂, h₂⟩
      · exact absurd (Subtype.ext_iff.mp h) hne
      · left
        have hzero : ClassFunction.inner ν₁ (-ν₂) = 0 := by rw [key, if_neg h]
        have key2 : ClassFunction.inner ν₁ ν₂ = -ClassFunction.inner ν₁ (-ν₂) := by
          rw [ClassFunction.inner_neg_right]; ring
        rw [key2, hzero, neg_zero]
  · rcases h₂ with h₂ | h₂
    · have key : ClassFunction.inner (-ν₁) ν₂
          = (if (⟨-ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨ν₂, h₂⟩ then (1 : ℂ) else 0) :=
        irreducibleCharacter_inner_eq_ite ⟨-ν₁, h₁⟩ ⟨ν₂, h₂⟩
      by_cases h : (⟨-ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨ν₂, h₂⟩
      · exfalso
        have h' : -ν₁ = ν₂ := Subtype.ext_iff.mp h
        exact hne (by rw [show ν₁ = -(-ν₁) from (neg_neg ν₁).symm, h'])
      · left
        have hzero : ClassFunction.inner (-ν₁) ν₂ = 0 := by rw [key, if_neg h]
        have key2 : ClassFunction.inner ν₁ ν₂ = -ClassFunction.inner (-ν₁) ν₂ := by
          rw [ClassFunction.inner_neg_left]; ring
        rw [key2, hzero, neg_zero]
    · have key : ClassFunction.inner (-ν₁) (-ν₂) = ClassFunction.inner ν₁ ν₂ := by
        rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg]
      rw [← key, irreducibleCharacter_inner_eq_ite ⟨-ν₁, h₁⟩ ⟨-ν₂, h₂⟩]
      by_cases h : (⟨-ν₁, h₁⟩ : IrreducibleCharacter K) = ⟨-ν₂, h₂⟩
      · rw [if_pos h]; exact Or.inr rfl
      · rw [if_neg h]; exact Or.inl rfl

end PmIrr

/-! ## 2. `0/1`-valued sums -/

section ZeroOne

/-- A sum of `ℂ`-valued terms each `0` or `1` is the cardinality of the set of `1`'s. -/
theorem sum_eq_card_filter_of_forall_eq_zero_or_one {ι : Type*} [Fintype ι] (t : ι → ℂ)
    (h : ∀ i, t i = 0 ∨ t i = 1) :
    ∑ i, t i = ((Finset.univ.filter (fun i => t i = 1)).card : ℂ) := by
  classical
  rw [show (∑ i, t i) = ∑ i, (if t i = 1 then (1 : ℂ) else 0) from
    Finset.sum_congr rfl fun i _ => by rcases h i with h | h <;> simp [h]]
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Every term of a `0/1`-valued disjunction is a natural number cast. -/
private theorem exists_natCast_of_eq_zero_or_one {a : ℂ} (h : a = 0 ∨ a = 1) :
    ∃ m : ℕ, a = (m : ℂ) := by
  rcases h with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

/-- Four terms each `0` or `1` summing to `0` are all `0`. -/
theorem eq_zero_of_sum_four_eq_zero {a1 a2 a3 a4 : ℂ}
    (h1 : a1 = 0 ∨ a1 = 1) (h2 : a2 = 0 ∨ a2 = 1)
    (h3 : a3 = 0 ∨ a3 = 1) (h4 : a4 = 0 ∨ a4 = 1)
    (hsum : a1 + a2 + a3 + a4 = 0) : a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
  obtain ⟨m1, hm1⟩ := exists_natCast_of_eq_zero_or_one h1
  obtain ⟨m2, hm2⟩ := exists_natCast_of_eq_zero_or_one h2
  obtain ⟨m3, hm3⟩ := exists_natCast_of_eq_zero_or_one h3
  obtain ⟨m4, hm4⟩ := exists_natCast_of_eq_zero_or_one h4
  rw [hm1, hm2, hm3, hm4] at hsum
  have hsum' : ((m1 + m2 + m3 + m4 : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination hsum
  have h0 : m1 + m2 + m3 + m4 = 0 := Nat.cast_eq_zero.mp hsum'
  have hm1' : m1 = 0 := by omega
  have hm2' : m2 = 0 := by omega
  have hm3' : m3 = 0 := by omega
  have hm4' : m4 = 0 := by omega
  exact ⟨by simp [hm1, hm1'], by simp [hm2, hm2'], by simp [hm3, hm3'], by simp [hm4, hm4']⟩

/-- Three terms each `0` or `1` summing to `0` are all `0`. -/
theorem eq_zero_of_sum_three_eq_zero {a1 a2 a3 : ℂ}
    (h1 : a1 = 0 ∨ a1 = 1) (h2 : a2 = 0 ∨ a2 = 1) (h3 : a3 = 0 ∨ a3 = 1)
    (hsum : a1 + a2 + a3 = 0) : a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  obtain ⟨m1, hm1⟩ := exists_natCast_of_eq_zero_or_one h1
  obtain ⟨m2, hm2⟩ := exists_natCast_of_eq_zero_or_one h2
  obtain ⟨m3, hm3⟩ := exists_natCast_of_eq_zero_or_one h3
  rw [hm1, hm2, hm3] at hsum
  have hsum' : ((m1 + m2 + m3 : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination hsum
  have h0 : m1 + m2 + m3 = 0 := Nat.cast_eq_zero.mp hsum'
  have hm1' : m1 = 0 := by omega
  have hm2' : m2 = 0 := by omega
  have hm3' : m3 = 0 := by omega
  exact ⟨by simp [hm1, hm1'], by simp [hm2, hm2'], by simp [hm3, hm3']⟩

/-- Four terms each `0` or `1` never sum to `-1`. -/
theorem false_of_sum_four_eq_neg_one {a1 a2 a3 a4 : ℂ}
    (h1 : a1 = 0 ∨ a1 = 1) (h2 : a2 = 0 ∨ a2 = 1)
    (h3 : a3 = 0 ∨ a3 = 1) (h4 : a4 = 0 ∨ a4 = 1)
    (hsum : a1 + a2 + a3 + a4 = -1) : False := by
  obtain ⟨m1, hm1⟩ := exists_natCast_of_eq_zero_or_one h1
  obtain ⟨m2, hm2⟩ := exists_natCast_of_eq_zero_or_one h2
  obtain ⟨m3, hm3⟩ := exists_natCast_of_eq_zero_or_one h3
  obtain ⟨m4, hm4⟩ := exists_natCast_of_eq_zero_or_one h4
  rw [hm1, hm2, hm3, hm4] at hsum
  have hsum' : (m1 : ℂ) + (m2 : ℂ) + (m3 : ℂ) + (m4 : ℂ) = (-1 : ℂ) := hsum
  have h1' : ((m1 + m2 + m3 + m4 + 1 : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination hsum'
  have h0 : m1 + m2 + m3 + m4 + 1 = 0 := Nat.cast_eq_zero.mp h1'
  omega

/-- `1 + b + c + d ≠ 0` when `b, c, d` are each `0` or `1`. -/
theorem one_add_three_ne_zero {b c d : ℂ} (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) : (1 : ℂ) + b + c + d ≠ 0 := by
  obtain ⟨mb, hmb⟩ := exists_natCast_of_eq_zero_or_one hb
  obtain ⟨mc, hmc⟩ := exists_natCast_of_eq_zero_or_one hc
  obtain ⟨md, hmd⟩ := exists_natCast_of_eq_zero_or_one hd
  intro h
  rw [hmb, hmc, hmd] at h
  have h' : ((1 + mb + mc + md : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination h
  have h0 : 1 + mb + mc + md = 0 := Nat.cast_eq_zero.mp h'
  omega

end ZeroOne

/-! ## 3. The assembly -/

section Main

variable {G : Type} [Group G] [Finite G]

open Work.GW2.C16 in
theorem thmCSmallAsm : Work.GW2.C16.ThmCSmallAsmProp := by
  unfold Work.GW2.C16.ThmCSmallAsmProp
  intro hBridge hX hSec3 hShape hKNeOne hAr4 hAr4b hKEq hleaves
  intro G instG instFin D K1 K2 hn h1 h2 hdir hcop hB hfr hsimple
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  obtain ⟨C, hC⟩ := hBridge G D
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have hHyps : ThmCHyps D K1 K2 := ⟨h1, h2, hdir, hcop, hB, hfr⟩
  obtain ⟨hCoh, hIndDiff, hKappaEx, hL22, hC4ID, hC4VAL, hC4DEG, hS4⟩ :=
    hleaves G D C K1 K2 hC hHyps
  obtain ⟨hSec3h, hBU'⟩ := hSec3 G D K1 K2 h1 h2 hdir hB
  obtain ⟨hUeq, hkeq⟩ := hShape G D K1 K2 hn h1 h2 hdir
  have hKne : K1 ⊓ K2 ≠ ⊥ := hKNeOne G D K1 K2 h1 h2 hdir hB hfr hsimple
  obtain ⟨κ, hκ⟩ := hKappaEx hC hBU'
  obtain ⟨f, hf⟩ := (coherence23_iff C).mp hCoh
  have h2q : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hC hn
  -- the non-trivial `β₂`
  obtain ⟨β₂, hβ₂t⟩ := exists_negChar C
  have hβ₂ : β₂ ≠ 1 := by
    intro h
    rw [h, lamCF_one_eq_trivial] at hβ₂t
    simp only [trivialClassFunction_apply] at hβ₂t
    have hsum2 : (1 : ℂ) + 1 = 0 := by linear_combination hβ₂t
    have h2 : ((2 : ℕ) : ℂ) = 0 := by push_cast; simpa using hsum2
    have h3 : (2 : ℕ) = 0 := Nat.cast_eq_zero.mp h2
    omega
  have hβ₂irr : IsIrreducibleCharacter (lamCF C β₂) := isIrreducibleCharacter_lamCF C β₂
  -- `κ` facts
  have hκlin : IsIrreducibleCharacter κ := hκ.1
  have hκ1 : κ (1 : ↥C.P.H0) = 1 := hκ.2.1
  have hκs : sconj C κ = κ := hκ.2.2.1
  have hκ_ne : κ ≠ lamCF C 1 := hκ.2.2.2.2
  -- `λ₁` facts
  have hlam1irr : IsIrreducibleCharacter (lamCF C 1) := by
    rw [lamCF_one_eq_trivial]; exact trivialClassFunction_isIrreducible
  have hlam1_1 : lamCF C 1 (1 : ↥C.P.H0) = 1 := by
    rw [lamCF_one_eq_trivial]; rfl
  have hlam1_s : sconj C (lamCF C 1) = lamCF C 1 := sconj_lamCF_one C
  have hlam1_S0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → lamCF C 1 h = 1 := by
    intro h _
    rw [lamCF_one_eq_trivial]; rfl
  have hβmul : lamCF C β₂ * lamCF C 1 = lamCF C β₂ := s4d_lamCF_mul_one C β₂
  have hlam_one' : lamCF C β₂ (1 : ↥C.P.H0) = 1 := by
    simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  -- S4-DEC
  obtain ⟨φ1, φ2, φ3, hpm1, hpm2, hpm3, hδ1, hφ1t, hφ2t, hφ3t,
    a, b, c, ha_odd, hb_odd, hc_odd, hφ1d, hφ2d, hφ3d⟩ := hS4 hC hn β₂ hβ₂
  -- equation (1)
  have hdisj : sconj C (lamCF C β₂ * lamCF C 1) ≠ lamCF C β₂ * lamCF C 1 ∨
      (β₂ ≠ 1 ∧ sconj C (lamCF C β₂) = lamCF C β₂ ∧
        (centralizer ({D.t1} : Set G)).relIndex D.H =
          (centralizer ({D.t2} : Set G)).relIndex D.H) :=
    Or.inr ⟨hβ₂, s4d_sconj_two D C hC hn hβ₂, hKEq G D hn⟩
  have hkey := hL22 hC (lamCF C 1) β₂ hlam1irr hlam1_1 hlam1_s hlam1_S0 hdisj
  rw [hβmul] at hkey
  have hgood := hf.1 (lamCF C 1) hlam1irr
  have hlamEq : LamEquiv C (lamCF C 1) (lamCF C β₂) := ⟨β₂, hβmul.symm⟩
  have hμE : lamCF C 1 ∈ orbitKey C (lamCF C 1) := Or.inl (s02c_LamEquiv_refl C (lamCF C 1))
  have hνE : lamCF C β₂ ∈ orbitKey C (lamCF C 1) := Or.inl hlamEq
  have hind_eq : ind C (lamCF C 1 - lamCF C β₂) = f (lamCF C 1) - f (lamCF C β₂) :=
    (hgood (lamCF C 1) hμE (lamCF C β₂) hνE hlam1irr hβ₂irr).2.2.2.1 hlamEq
  have hind1 : ind C (lamCF C 1 - lamCF C β₂) = trivialClassFunction G + φ1 + φ2 + φ3 := by
    rw [← s4d_delta_eq C β₂]; exact hδ1
  have hF : f (lamCF C 1) - f (lamCF C β₂) = trivialClassFunction G + φ1 + φ2 + φ3 :=
    hind_eq.symm.trans hind1
  rw [hind1] at hkey
  -- X1
  let ε : Fin 4 → ClassFunction G ℂ := ![trivialClassFunction G, φ1, φ2, φ3]
  have hεsum : (∑ i : Fin 4, ε i) = trivialClassFunction G + φ1 + φ2 + φ3 := by
    simp [Fin.sum_univ_four, ε]
  have hεmem : ∀ i : Fin 4, IsPmIrr (ε i) := by
    intro i
    fin_cases i
    · exact Or.inl (by simpa [ε] using trivialClassFunction_isIrreducible)
    · simpa [ε] using hpm1
    · simpa [ε] using hpm2
    · simpa [ε] using hpm3
  have hXeq := hX ε hεmem (C.t : G)
  rw [hεsum] at hXeq
  have hεt : (∑ i : Fin 4, ε i (C.t : G) ^ 2 / ε i 1) =
      1 + 1 / (a : ℂ) + 1 / (b : ℂ) + 1 / (c : ℂ) := by
    rw [Fin.sum_univ_four]
    simp [ε, hφ1t, hφ2t, hφ3t, hφ1d, hφ2d, hφ3d]
  have hEq1 : (D.H.index : ℂ) * (1 + 1 / (a : ℂ) + 1 / (b : ℂ) + 1 / (c : ℂ)) =
      2 * (D.k : ℂ) ^ 2 := by
    rw [← hεt, ← hXeq]
    exact hkey
  -- C4-ID
  obtain ⟨χ1, χ2, χ3, χ4, hχ1pm, hχ2pm, hχ3pm, hχ4pm, hδκ, hEq2⟩ :=
    hC4ID hC hn β₂ hβ₂ κ hκ
  -- C4-VAL
  have hval := hC4VAL hC hn hHyps β₂ hβ₂ κ hκ χ1 χ2 χ3 χ4
    hχ1pm hχ2pm hχ3pm hχ4pm hδκ hEq2
  rcases hval with ⟨hχ1t, hχ2t, hχ3t, hχ4t⟩ | ⟨d, hd⟩
  · -- ## Case A: all `χᵢ(t) = 1`.
    have hδκ_eq : delta C β₂ κ = ind C (κ - lamCF C β₂ * κ) := rfl
    have hδκ_one : delta C β₂ κ (1 : G) = 0 := by
      rw [hδκ_eq, ClassFunction.induce_apply_one, ClassFunction.sub_apply,
        ClassFunction.mul_apply, hκ1, hlam_one', one_mul, sub_self, mul_zero]
    have hsum_deg : χ1 1 + χ2 1 + χ3 1 + χ4 1 = 0 := by
      have h := congrArg (fun ψ : ClassFunction G ℂ => ψ (1 : G)) hδκ
      rw [hδκ_one, ClassFunction.add_apply, ClassFunction.add_apply,
        ClassFunction.add_apply] at h
      exact h.symm
    obtain ⟨d1, hd1, -⟩ := keyBigAux_pmIrr_exists_int_value χ1 hχ1pm
    obtain ⟨d2, hd2, -⟩ := keyBigAux_pmIrr_exists_int_value χ2 hχ2pm
    obtain ⟨d3, hd3, -⟩ := keyBigAux_pmIrr_exists_int_value χ3 hχ3pm
    obtain ⟨d4, hd4, -⟩ := keyBigAux_pmIrr_exists_int_value χ4 hχ4pm
    have hdsum : d1 + d2 + d3 + d4 = 0 := by
      have h : ((d1 : ℤ) : ℂ) + ((d2 : ℤ) : ℂ) + ((d3 : ℤ) : ℂ) + ((d4 : ℤ) : ℂ) = 0 := by
        rw [← hd1, ← hd2, ← hd3, ← hd4]; exact hsum_deg
      exact_mod_cast h
    have hδ1_one : delta C β₂ (lamCF C 1) (1 : G) = 0 := by
      rw [s4d_delta_eq, ClassFunction.induce_apply_one, ClassFunction.sub_apply,
        hlam1_1, hlam_one', sub_self, mul_zero]
    have habc : 1 + a + b + c = 0 := by
      have h := congrArg (fun ψ : ClassFunction G ℂ => ψ (1 : G)) hδ1
      rw [hδ1_one, ClassFunction.add_apply, ClassFunction.add_apply,
        ClassFunction.add_apply, trivialClassFunction_apply, hφ1d, hφ2d, hφ3d] at h
      have h' : (1 : ℂ) + (a : ℂ) + (b : ℂ) + (c : ℂ) = 0 := h.symm
      exact_mod_cast h'
    -- sign facts at `t`
    have hφ1ne1 : φ1 ≠ -trivialClassFunction G := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ1t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
      norm_num at h2
    have hφ2ne1 : φ2 ≠ -trivialClassFunction G := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ2t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
      norm_num at h2
    have hφ3ne1 : φ3 ≠ -trivialClassFunction G := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ3t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
      norm_num at h2
    have hφ1ne2 : φ1 ≠ -φ2 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ1t, ClassFunction.neg_apply, hφ2t] at h2
      norm_num at h2
    have hφ2ne3 : φ2 ≠ -φ3 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ2t, ClassFunction.neg_apply, hφ3t] at h2
      norm_num at h2
    have hφ1ne3 : φ1 ≠ -φ3 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hφ1t, ClassFunction.neg_apply, hφ3t] at h2
      norm_num at h2
    have hφ2ne1' : φ2 ≠ -φ1 := fun h => hφ1ne2 (by rw [h]; abel)
    have hφ3ne1' : φ3 ≠ -φ1 := fun h => hφ1ne3 (by rw [h]; abel)
    have hφ3ne2' : φ3 ≠ -φ2 := fun h => hφ2ne3 (by rw [h]; abel)
    -- `(δ₁, 1_G) = 1`
    have hres : ClassFunction.restrict C.P.H0 (trivialClassFunction G) =
        trivialClassFunction ↥C.P.H0 := by
      ext h; simp [ClassFunction.restrict_apply, trivialClassFunction_apply]
    have hδ1in1 : ClassFunction.inner (delta C β₂ (lamCF C 1)) (trivialClassFunction G) = 1 := by
      rw [s4d_delta_eq,
        ClassFunction.inner_induce_eq_inner_restrict (C.P.H0) (lamCF C 1 - lamCF C β₂)
          (trivialClassFunction G), hres, ClassFunction.inner_sub_left]
      have h1v : ClassFunction.inner (lamCF C 1) (trivialClassFunction ↥C.P.H0) = 1 := by
        rw [lamCF_one_eq_trivial,
          irreducibleCharacter_inner_eq_ite
            ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩
            ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩,
          if_pos rfl]
      have h2v : ClassFunction.inner (lamCF C β₂) (trivialClassFunction ↥C.P.H0) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨lamCF C β₂, hβ₂irr⟩
            ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩, if_neg]
        intro hh
        have hh' : lamCF C β₂ = lamCF C 1 := by
          rw [lamCF_one_eq_trivial]
          exact Subtype.ext_iff.mp hh
        exact s4d_lamCF_two_ne_triv C hβ₂ hh'
      rw [h1v, h2v]; ring
    have hφsum : ClassFunction.inner φ1 (trivialClassFunction G) +
        ClassFunction.inner φ2 (trivialClassFunction G) +
          ClassFunction.inner φ3 (trivialClassFunction G) = 0 := by
      have hsplit : ClassFunction.inner (delta C β₂ (lamCF C 1)) (trivialClassFunction G) =
          ((1 + ClassFunction.inner φ1 (trivialClassFunction G)) +
            ClassFunction.inner φ2 (trivialClassFunction G)) +
              ClassFunction.inner φ3 (trivialClassFunction G) := by
        rw [hδ1]
        simp only [ClassFunction.inner_add_left]
        have h1v : ClassFunction.inner (trivialClassFunction G) (trivialClassFunction G) = 1 := by
          rw [irreducibleCharacter_inner_eq_ite
            ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
            ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩, if_pos rfl]
        rw [h1v]
      have htot : ((1 + ClassFunction.inner φ1 (trivialClassFunction G)) +
            ClassFunction.inner φ2 (trivialClassFunction G)) +
              ClassFunction.inner φ3 (trivialClassFunction G) = 1 :=
        hsplit.symm.trans hδ1in1
      linear_combination htot
    have hφinv : ClassFunction.inner φ1 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner φ1 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hpm1 (Or.inl trivialClassFunction_isIrreducible) hφ1ne1
    have hφ2inv : ClassFunction.inner φ2 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner φ2 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hpm2 (Or.inl trivialClassFunction_isIrreducible) hφ2ne1
    have hφ3inv : ClassFunction.inner φ3 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner φ3 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hpm3 (Or.inl trivialClassFunction_isIrreducible) hφ3ne1
    have hφall := eq_zero_of_sum_three_eq_zero hφinv hφ2inv hφ3inv hφsum
    have hinφ1_1 : ClassFunction.inner φ1 (trivialClassFunction G) = 0 := hφall.1
    have hinφ2_1 : ClassFunction.inner φ2 (trivialClassFunction G) = 0 := hφall.2.1
    have hinφ3_1 : ClassFunction.inner φ3 (trivialClassFunction G) = 0 := hφall.2.2
    -- `C4-DEG` for the `φⱼ`
    have hbsetφ1 : ∃ ν ∈ Work.GW2.C16.bset C f φ1, sconj C ν = ν := by
      have hinnerφ1 : ClassFunction.inner φ1 (trivialClassFunction G + φ1 + φ2 + φ3) ≠ 0 := by
        have hval : ClassFunction.inner φ1 (trivialClassFunction G + φ1 + φ2 + φ3) =
            (1 : ℂ) + ClassFunction.inner φ1 (trivialClassFunction G) +
              ClassFunction.inner φ1 φ2 + ClassFunction.inner φ1 φ3 := by
          simp only [ClassFunction.inner_add_right]
          rw [pmIrr_inner_self hpm1]
          ring
        rw [hval]
        exact one_add_three_ne_zero hφinv
          (pmIrr_inner_eq_zero_or_one hpm1 hpm2 hφ1ne2)
          (pmIrr_inner_eq_zero_or_one hpm1 hpm3 hφ1ne3)
      have hdiff : ClassFunction.inner φ1 (f (lamCF C 1)) -
          ClassFunction.inner φ1 (f (lamCF C β₂)) ≠ 0 := by
        have h0 : ClassFunction.inner φ1 (f (lamCF C 1) - f (lamCF C β₂)) ≠ 0 := by
          rw [hF]; exact hinnerφ1
        rwa [ClassFunction.inner_sub_right] at h0
      by_cases hcase : ClassFunction.inner φ1 (f (lamCF C 1)) = 0
      · refine ⟨lamCF C β₂, ⟨hβ₂irr, ?_⟩, s4d_sconj_two D C hC hn hβ₂⟩
        intro h0
        exact hdiff (by rw [hcase, h0, sub_zero])
      · exact ⟨lamCF C 1, ⟨hlam1irr, hcase⟩, hlam1_s⟩
    obtain ⟨dφ1, hdφ1, h5φ1⟩ := hC4DEG hC hHyps hsimple hn f hf φ1 hpm1 hinφ1_1 hbsetφ1
    have h5a : 5 ≤ |a| := by
      have hcast : ((dφ1 : ℤ) : ℂ) = ((a : ℤ) : ℂ) := by rw [← hdφ1, hφ1d]
      have hda : dφ1 = a := Int.cast_injective hcast
      rw [hda] at h5φ1; exact h5φ1
    have hbsetφ2 : ∃ ν ∈ Work.GW2.C16.bset C f φ2, sconj C ν = ν := by
      have hinnerφ2 : ClassFunction.inner φ2 (trivialClassFunction G + φ1 + φ2 + φ3) ≠ 0 := by
        have hval : ClassFunction.inner φ2 (trivialClassFunction G + φ1 + φ2 + φ3) =
            (1 : ℂ) + ClassFunction.inner φ2 (trivialClassFunction G) +
              ClassFunction.inner φ2 φ1 + ClassFunction.inner φ2 φ3 := by
          simp only [ClassFunction.inner_add_right]
          rw [pmIrr_inner_self hpm2]
          ring
        rw [hval]
        exact one_add_three_ne_zero hφ2inv
          (pmIrr_inner_eq_zero_or_one hpm2 hpm1 hφ2ne1')
          (pmIrr_inner_eq_zero_or_one hpm2 hpm3 hφ2ne3)
      have hdiff : ClassFunction.inner φ2 (f (lamCF C 1)) -
          ClassFunction.inner φ2 (f (lamCF C β₂)) ≠ 0 := by
        have h0 : ClassFunction.inner φ2 (f (lamCF C 1) - f (lamCF C β₂)) ≠ 0 := by
          rw [hF]; exact hinnerφ2
        rwa [ClassFunction.inner_sub_right] at h0
      by_cases hcase : ClassFunction.inner φ2 (f (lamCF C 1)) = 0
      · refine ⟨lamCF C β₂, ⟨hβ₂irr, ?_⟩, s4d_sconj_two D C hC hn hβ₂⟩
        intro h0
        exact hdiff (by rw [hcase, h0, sub_zero])
      · exact ⟨lamCF C 1, ⟨hlam1irr, hcase⟩, hlam1_s⟩
    obtain ⟨dφ2, hdφ2, h5φ2⟩ := hC4DEG hC hHyps hsimple hn f hf φ2 hpm2 hinφ2_1 hbsetφ2
    have h5b : 5 ≤ |b| := by
      have hcast : ((dφ2 : ℤ) : ℂ) = ((b : ℤ) : ℂ) := by rw [← hdφ2, hφ2d]
      have hda : dφ2 = b := Int.cast_injective hcast
      rw [hda] at h5φ2; exact h5φ2
    have hbsetφ3 : ∃ ν ∈ Work.GW2.C16.bset C f φ3, sconj C ν = ν := by
      have hinnerφ3 : ClassFunction.inner φ3 (trivialClassFunction G + φ1 + φ2 + φ3) ≠ 0 := by
        have hval : ClassFunction.inner φ3 (trivialClassFunction G + φ1 + φ2 + φ3) =
            (1 : ℂ) + ClassFunction.inner φ3 (trivialClassFunction G) +
              ClassFunction.inner φ3 φ1 + ClassFunction.inner φ3 φ2 := by
          simp only [ClassFunction.inner_add_right]
          rw [pmIrr_inner_self hpm3]
          ring
        rw [hval]
        exact one_add_three_ne_zero hφ3inv
          (pmIrr_inner_eq_zero_or_one hpm3 hpm1 hφ3ne1')
          (pmIrr_inner_eq_zero_or_one hpm3 hpm2 hφ3ne2')
      have hdiff : ClassFunction.inner φ3 (f (lamCF C 1)) -
          ClassFunction.inner φ3 (f (lamCF C β₂)) ≠ 0 := by
        have h0 : ClassFunction.inner φ3 (f (lamCF C 1) - f (lamCF C β₂)) ≠ 0 := by
          rw [hF]; exact hinnerφ3
        rwa [ClassFunction.inner_sub_right] at h0
      by_cases hcase : ClassFunction.inner φ3 (f (lamCF C 1)) = 0
      · refine ⟨lamCF C β₂, ⟨hβ₂irr, ?_⟩, s4d_sconj_two D C hC hn hβ₂⟩
        intro h0
        exact hdiff (by rw [hcase, h0, sub_zero])
      · exact ⟨lamCF C 1, ⟨hlam1irr, hcase⟩, hlam1_s⟩
    obtain ⟨dφ3, hdφ3, h5φ3⟩ := hC4DEG hC hHyps hsimple hn f hf φ3 hpm3 hinφ3_1 hbsetφ3
    have h5c : 5 ≤ |c| := by
      have hcast : ((dφ3 : ℤ) : ℂ) = ((c : ℤ) : ℂ) := by rw [← hdφ3, hφ3d]
      have hda : dφ3 = c := Int.cast_injective hcast
      rw [hda] at h5φ3; exact h5φ3
    -- `(δ_κ, 1_G) ∈ {0,-1}`
    have hκ_one : ClassFunction.inner κ (trivialClassFunction ↥C.P.H0) = 0 := by
      rw [irreducibleCharacter_inner_eq_ite ⟨κ, hκlin⟩
        ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩, if_neg]
      intro hh
      have hh' : κ = lamCF C 1 := by
        rw [lamCF_one_eq_trivial]
        exact Subtype.ext_iff.mp hh
      exact hκ_ne hh'
    have hδκin1 : ClassFunction.inner (delta C β₂ κ) (trivialClassFunction G) = 0 ∨
        ClassFunction.inner (delta C β₂ κ) (trivialClassFunction G) = -1 := by
      rw [hδκ_eq,
        ClassFunction.inner_induce_eq_inner_restrict (C.P.H0) (κ - lamCF C β₂ * κ)
          (trivialClassFunction G), hres, ClassFunction.inner_sub_left]
      rw [hκ_one,
        irreducibleCharacter_inner_eq_ite
          (⟨lamCF C β₂ * κ, lam_two_mul_irr C hκlin⟩ : IrreducibleCharacter ↥C.P.H0)
          (⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩ :
            IrreducibleCharacter ↥C.P.H0)]
      by_cases hh : (⟨lamCF C β₂ * κ, lam_two_mul_irr C hκlin⟩ :
            IrreducibleCharacter ↥C.P.H0) =
          (⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩ :
            IrreducibleCharacter ↥C.P.H0)
      · rw [if_pos hh]; right; ring
      · rw [if_neg hh]; left; ring
    have hsum1G : ClassFunction.inner χ1 (trivialClassFunction G) +
        ClassFunction.inner χ2 (trivialClassFunction G) +
          ClassFunction.inner χ3 (trivialClassFunction G) +
            ClassFunction.inner χ4 (trivialClassFunction G) =
              ClassFunction.inner (delta C β₂ κ) (trivialClassFunction G) := by
      rw [hδκ]
      simp only [ClassFunction.inner_add_left]
    have ht2 : ClassFunction.inner χ2 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner χ2 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hχ2pm (Or.inl trivialClassFunction_isIrreducible) (by
        intro h
        have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
        rw [hχ2t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
        norm_num at h2)
    have ht3 : ClassFunction.inner χ3 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner χ3 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hχ3pm (Or.inl trivialClassFunction_isIrreducible) (by
        intro h
        have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
        rw [hχ3t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
        norm_num at h2)
    have ht4 : ClassFunction.inner χ4 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner χ4 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hχ4pm (Or.inl trivialClassFunction_isIrreducible) (by
        intro h
        have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
        rw [hχ4t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
        norm_num at h2)
    have hχ1ne1 : χ1 ≠ -trivialClassFunction G := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ1t, ClassFunction.neg_apply, trivialClassFunction_apply] at h2
      norm_num at h2
    have ht1 : ClassFunction.inner χ1 (trivialClassFunction G) = 0 ∨
        ClassFunction.inner χ1 (trivialClassFunction G) = 1 :=
      pmIrr_inner_eq_zero_or_one hχ1pm (Or.inl trivialClassFunction_isIrreducible) hχ1ne1
    -- all four are zero
    have hδχ0 : ClassFunction.inner (delta C β₂ κ) (trivialClassFunction G) = 0 := by
      rcases hδκin1 with hδ0 | hδneg
      · exact hδ0
      · exfalso
        exact false_of_sum_four_eq_neg_one ht1 ht2 ht3 ht4 (hsum1G.trans hδneg)
    have hχall := eq_zero_of_sum_four_eq_zero ht1 ht2 ht3 ht4 (hsum1G.trans hδχ0)
    have hχ1_one : ClassFunction.inner χ1 (trivialClassFunction G) = 0 := hχall.1
    have hχ2_one : ClassFunction.inner χ2 (trivialClassFunction G) = 0 := hχall.2.1
    have hχ3_one : ClassFunction.inner χ3 (trivialClassFunction G) = 0 := hχall.2.2.1
    have hχ4_one : ClassFunction.inner χ4 (trivialClassFunction G) = 0 := hχall.2.2.2
    -- `𝒮(χⱼ)` contains an `s`-fixed member
    have hcohκ : ind C (κ - lamCF C β₂ * κ) = f κ - f (lamCF C β₂ * κ) := by
      have hg := hf.1 κ hκlin
      have hκE : κ ∈ orbitKey C κ := Or.inl (s02c_LamEquiv_refl C κ)
      have hκ2E : lamCF C β₂ * κ ∈ orbitKey C κ := Or.inl ⟨β₂, rfl⟩
      exact (hg κ hκE (lamCF C β₂ * κ) hκ2E hκlin (lam_two_mul_irr C hκlin)).2.2.2.1 ⟨β₂, rfl⟩
    have hκcoh : f κ - f (lamCF C β₂ * κ) = χ1 + χ2 + χ3 + χ4 := hcohκ.symm.trans hδκ
    have hbsetχ : ∀ (χ : ClassFunction G ℂ) (hχpm : IsPmIrr χ),
        ClassFunction.inner χ (χ1 + χ2 + χ3 + χ4) ≠ 0 →
        ∃ ν ∈ Work.GW2.C16.bset C f χ, sconj C ν = ν := by
      intro χ hχpm hinner
      have hdiff : ClassFunction.inner χ (f κ) - ClassFunction.inner χ (f (lamCF C β₂ * κ)) ≠ 0 := by
        have h0 : ClassFunction.inner χ (f κ - f (lamCF C β₂ * κ)) ≠ 0 := by
          rw [hκcoh]; exact hinner
        rwa [ClassFunction.inner_sub_right] at h0
      by_cases hcase : ClassFunction.inner χ (f κ) = 0
      · refine ⟨lamCF C β₂ * κ, ⟨lam_two_mul_irr C hκlin, ?_⟩,
          (sconj_lam_two_mul_eq_iff C h2q hβ₂ κ).mpr hκs⟩
        intro h0
        exact hdiff (by rw [hcase, h0, sub_zero])
      · exact ⟨κ, ⟨hκlin, hcase⟩, hκs⟩
    -- degree bounds for the `χⱼ`
    have hne12 : χ1 ≠ -χ2 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ1t, ClassFunction.neg_apply, hχ2t] at h2
      norm_num at h2
    have hne13 : χ1 ≠ -χ3 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ1t, ClassFunction.neg_apply, hχ3t] at h2
      norm_num at h2
    have hne14 : χ1 ≠ -χ4 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ1t, ClassFunction.neg_apply, hχ4t] at h2
      norm_num at h2
    have hne23 : χ2 ≠ -χ3 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ2t, ClassFunction.neg_apply, hχ3t] at h2
      norm_num at h2
    have hne24 : χ2 ≠ -χ4 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ2t, ClassFunction.neg_apply, hχ4t] at h2
      norm_num at h2
    have hne34 : χ3 ≠ -χ4 := by
      intro h
      have h2 := congrArg (fun ψ : ClassFunction G ℂ => ψ (C.t : G)) h
      rw [hχ3t, ClassFunction.neg_apply, hχ4t] at h2
      norm_num at h2
    have hne21 : χ2 ≠ -χ1 := fun h => hne12 (by rw [h]; abel)
    have hne31 : χ3 ≠ -χ1 := fun h => hne13 (by rw [h]; abel)
    have hne32 : χ3 ≠ -χ2 := fun h => hne23 (by rw [h]; abel)
    have hne41 : χ4 ≠ -χ1 := fun h => hne14 (by rw [h]; abel)
    have hne42 : χ4 ≠ -χ2 := fun h => hne24 (by rw [h]; abel)
    have hne43 : χ4 ≠ -χ3 := fun h => hne34 (by rw [h]; abel)
    have hin1 : ClassFunction.inner χ1 (χ1 + χ2 + χ3 + χ4) ≠ 0 := by
      have hval : ClassFunction.inner χ1 (χ1 + χ2 + χ3 + χ4) =
          (1 : ℂ) + ClassFunction.inner χ1 χ2 + ClassFunction.inner χ1 χ3 +
            ClassFunction.inner χ1 χ4 := by
        simp only [ClassFunction.inner_add_right]
        rw [pmIrr_inner_self hχ1pm] <;> ring
      rw [hval]
      exact one_add_three_ne_zero (pmIrr_inner_eq_zero_or_one hχ1pm hχ2pm hne12)
        (pmIrr_inner_eq_zero_or_one hχ1pm hχ3pm hne13)
        (pmIrr_inner_eq_zero_or_one hχ1pm hχ4pm hne14)
    have hin2 : ClassFunction.inner χ2 (χ1 + χ2 + χ3 + χ4) ≠ 0 := by
      have hval : ClassFunction.inner χ2 (χ1 + χ2 + χ3 + χ4) =
          (1 : ℂ) + ClassFunction.inner χ2 χ1 + ClassFunction.inner χ2 χ3 +
            ClassFunction.inner χ2 χ4 := by
        simp only [ClassFunction.inner_add_right]
        rw [pmIrr_inner_self hχ2pm] <;> ring
      rw [hval]
      exact one_add_three_ne_zero (pmIrr_inner_eq_zero_or_one hχ2pm hχ1pm hne21)
        (pmIrr_inner_eq_zero_or_one hχ2pm hχ3pm hne23)
        (pmIrr_inner_eq_zero_or_one hχ2pm hχ4pm hne24)
    have hin3 : ClassFunction.inner χ3 (χ1 + χ2 + χ3 + χ4) ≠ 0 := by
      have hval : ClassFunction.inner χ3 (χ1 + χ2 + χ3 + χ4) =
          (1 : ℂ) + ClassFunction.inner χ3 χ1 + ClassFunction.inner χ3 χ2 +
            ClassFunction.inner χ3 χ4 := by
        simp only [ClassFunction.inner_add_right]
        rw [pmIrr_inner_self hχ3pm] <;> ring
      rw [hval]
      exact one_add_three_ne_zero (pmIrr_inner_eq_zero_or_one hχ3pm hχ1pm hne31)
        (pmIrr_inner_eq_zero_or_one hχ3pm hχ2pm hne32)
        (pmIrr_inner_eq_zero_or_one hχ3pm hχ4pm hne34)
    have hin4 : ClassFunction.inner χ4 (χ1 + χ2 + χ3 + χ4) ≠ 0 := by
      have hval : ClassFunction.inner χ4 (χ1 + χ2 + χ3 + χ4) =
          (1 : ℂ) + ClassFunction.inner χ4 χ1 + ClassFunction.inner χ4 χ2 +
            ClassFunction.inner χ4 χ3 := by
        simp only [ClassFunction.inner_add_right]
        rw [pmIrr_inner_self hχ4pm] <;> ring
      rw [hval]
      exact one_add_three_ne_zero (pmIrr_inner_eq_zero_or_one hχ4pm hχ1pm hne41)
        (pmIrr_inner_eq_zero_or_one hχ4pm hχ2pm hne42)
        (pmIrr_inner_eq_zero_or_one hχ4pm hχ3pm hne43)
    have h5d1 : 5 ≤ |d1| := by
      obtain ⟨dχ1, hdχ1, h5χ1⟩ := hC4DEG hC hHyps hsimple hn f hf χ1 hχ1pm hχ1_one
        (hbsetχ χ1 hχ1pm hin1)
      have hcast : ((dχ1 : ℤ) : ℂ) = ((d1 : ℤ) : ℂ) := by rw [← hdχ1, hd1]
      have hda : dχ1 = d1 := Int.cast_injective hcast
      rw [hda] at h5χ1; exact h5χ1
    have h5d2 : 5 ≤ |d2| := by
      obtain ⟨dχ2, hdχ2, h5χ2⟩ := hC4DEG hC hHyps hsimple hn f hf χ2 hχ2pm hχ2_one
        (hbsetχ χ2 hχ2pm hin2)
      have hcast : ((dχ2 : ℤ) : ℂ) = ((d2 : ℤ) : ℂ) := by rw [← hdχ2, hd2]
      have hda : dχ2 = d2 := Int.cast_injective hcast
      rw [hda] at h5χ2; exact h5χ2
    have h5d3 : 5 ≤ |d3| := by
      obtain ⟨dχ3, hdχ3, h5χ3⟩ := hC4DEG hC hHyps hsimple hn f hf χ3 hχ3pm hχ3_one
        (hbsetχ χ3 hχ3pm hin3)
      have hcast : ((dχ3 : ℤ) : ℂ) = ((d3 : ℤ) : ℂ) := by rw [← hdχ3, hd3]
      have hda : dχ3 = d3 := Int.cast_injective hcast
      rw [hda] at h5χ3; exact h5χ3
    have h5d4 : 5 ≤ |d4| := by
      obtain ⟨dχ4, hdχ4, h5χ4⟩ := hC4DEG hC hHyps hsimple hn f hf χ4 hχ4pm hχ4_one
        (hbsetχ χ4 hχ4pm hin4)
      have hcast : ((dχ4 : ℤ) : ℂ) = ((d4 : ℤ) : ℂ) := by rw [← hdχ4, hd4]
      have hda : dχ4 = d4 := Int.cast_injective hcast
      rw [hda] at h5χ4; exact h5χ4
    -- ## The two identities and `AR-C4`.
    have hEq2' : (D.H.index : ℂ) *
        (1 / (d1 : ℂ) + 1 / (d2 : ℂ) + 1 / (d3 : ℂ) + 1 / (d4 : ℂ)) =
          2 * (D.k : ℂ) ^ 2 := by
      rw [← hEq2]
      congr 1
      rw [hχ1t, hχ2t, hχ3t, hχ4t, hd1, hd2, hd3, hd4]
      norm_num
    have hNne : (D.H.index : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Subgroup.index_ne_zero_of_finite
    have hdiv : (1 / (d1 : ℚ) + 1 / (d2 : ℚ) + 1 / (d3 : ℚ) + 1 / (d4 : ℚ) : ℚ) =
        1 + 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) := by
      have hC' : 1 / (d1 : ℂ) + 1 / (d2 : ℂ) + 1 / (d3 : ℂ) + 1 / (d4 : ℂ) =
          1 + 1 / (a : ℂ) + 1 / (b : ℂ) + 1 / (c : ℂ) :=
        mul_left_cancel₀ hNne (hEq2'.trans hEq1.symm)
      have hcast : (((1 / (d1 : ℚ) + 1 / (d2 : ℚ) + 1 / (d3 : ℚ) + 1 / (d4 : ℚ) : ℚ)) : ℂ) =
          (((1 + 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) : ℚ)) : ℂ) := by
        push_cast
        exact hC'
      exact Rat.cast_injective hcast
    exact hAr4 a b c d1 d2 d3 d4 h5a h5b h5c h5d1 h5d2 h5d3 h5d4 habc hdsum hdiv.symm

  · -- ## Case B
    have hNodd : Odd D.H.index := (indexOdd G D).1
    have hdk : (D.k : ℤ) = ((2 * Nat.card (K1 ⊓ K2 : Subgroup G) : ℕ) : ℤ) := by
      rw [hkeq]
    rw [hdk] at hd
    have hK1 : Nat.card (K1 ⊓ K2 : Subgroup G) = 1 :=
      hAr4b D.H.index (Nat.card (K1 ⊓ K2 : Subgroup G)) d hNodd hcop hd
    refine hKne ?_
    rw [Subgroup.eq_bot_iff_forall (K1 ⊓ K2)]
    intro x hx
    haveI : Fintype ↥(K1 ⊓ K2) := Fintype.ofFinite _
    have hc : Fintype.card ↥(K1 ⊓ K2) ≤ 1 := by
      rw [Nat.card_eq_fintype_card] at hK1; omega
    have hsub : Subsingleton ↥(K1 ⊓ K2) := Fintype.card_le_one_iff_subsingleton.mp hc
    exact Subtype.ext_iff.mp (Subsingleton.elim (⟨x, hx⟩ : ↥(K1 ⊓ K2)) 1)
end Main

end Work.BG
