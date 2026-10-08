import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.keyBigArith

/-!
# Area BG: **KEYBIG-ASM** (BG Lemma 2.5, `|S| ≥ 8`)

This module proves the assembly leaf `Work.GW2.C16.KeyBigAsmProp`, i.e. the passage from the
character-theoretic inputs (Coherence Theorem 2.3, `IndDiffProp` = Lemma 1.3 / I-1,
`DecompBigProp` = Lemma 2.5 front half, `Lemma22KappaProp` = Lemma 2.2 for the orbit of `λ₁`)
to KEY-BIG:

`|G : H| · (x - 1)² = 2 k² · x (x + 1)` for `x = φ(1)`, where `λ̃₁ = 1_G + φ` and
`λ̃₃` is the companion of `λ₃ = λ_β` with `λ₃(t) = -1`.

The proof is the one prescribed by the design (`NOTES_LEAD_gw_design16.md`, wave 3):

* Lemma 2.2 (p. 205) at `κ = λ₁ = 1_{H₀}`, `ν = λ₃` gives
  `|G:H| Σ_χ χ(t)²/χ(1) (λ̃₁ - λ̃₃, χ) = 2k²`;
* coherence (2.3 (iii)) identifies `(λ₁ - λ₃)* = f λ₁ - f λ₃`;
* `DecompBigProp` expands `f λ₁ = 1_G + φ`, and `IndDiffProp` (`(λ₁ - λ₃)*(1) = 0`) gives
  `λ̃₃(1) = λ̃₁(1) = x + 1`;
* X1 (`ConstituentSumProp`) with the signed decomposition `(1_G, φ, -λ̃₃)` of `λ̃₁ - λ̃₃`
  evaluates the sum as `1 + 1/x - 4/(x+1)` (using `φ(t) = 1`, `λ̃₃(t) = -2`);
* clearing denominators (`keyBigArith`) turns this into `|G:H| (x-1)² = 2k² x(x+1)`;
  `x ≠ 0` and `x ≠ -1` come from `φ` and `λ̃₃` being signed irreducible characters.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Subgroup

/-- A signed irreducible character (`IsPmIrr`) has a nonzero integral degree: its value at
`1` is `±d` for a positive natural `d`. -/
theorem keyBigAux_pmIrr_exists_int_value {K : Type} [Group K] [Finite K]
    (ψ : ClassFunction K ℂ) (h : IsPmIrr ψ) : ∃ x : ℤ, ψ 1 = (x : ℂ) ∧ x ≠ 0 := by
  rcases h with h | h
  · obtain ⟨n, hn0, hn, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    exact ⟨n, hn, by exact_mod_cast hn0.ne'⟩
  · obtain ⟨n, hn0, hn, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    have h1 : -(ψ 1) = (n : ℂ) := by
      rw [← ClassFunction.neg_apply]; exact hn
    refine ⟨-(n : ℤ), ?_, ?_⟩
    · push_cast
      linear_combination -h1
    · omega

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem keyBigAsm : Work.GW2.C16.KeyBigAsmProp := by
  unfold Work.GW2.C16.KeyBigAsmProp
  intro hBridge hX hBig
  intro G instG instFin D hn
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  obtain ⟨C, hCompat⟩ := hBridge G D
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hCoh, hIndDiff, hDecomp, hL22⟩ := hBig G D C
  obtain ⟨f, hf⟩ := (coherence23_iff C).mp hCoh
  obtain ⟨β, hβt, hβs, hβpm, hβtval, φ, hφpm, hφorth1, hφorth3, hlam1dec, hφt⟩ :=
    hDecomp hCompat hn f hf
  obtain ⟨x, hxval, hx0⟩ := keyBigAux_pmIrr_exists_int_value φ hφpm
  -- `λ₁ = lamCF C 1` is the trivial class function of `H₀`.
  have htriv : lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 := by
    rw [lamCF_one]
    ext h
    simp [linearClassFunction_apply, trivialClassFunction_apply]
  have hlam1irr : IsIrreducibleCharacter (lamCF C 1) := by
    rw [htriv]; exact trivialClassFunction_isIrreducible
  have hβmul : lamCF C β * lamCF C 1 = lamCF C β := by
    have h1 : β * (1 : quotGroup C.P →* ℂˣ) = β := mul_one β
    rw [← s02c_lamCF_mul, h1]
  have hlam3irr : IsIrreducibleCharacter (lamCF C β) := by
    have hmem : lamCF C β ∈ Lambda C.P := ⟨β, rfl⟩
    have h := lambda_mul_irreducible C.P hmem hlam1irr
    rwa [hβmul] at h
  -- Lemma 2.2 (BG p. 205) at `κ = λ₁`, `ν = λ₃ = λ_β`.
  have hκ1 : lamCF C 1 (1 : ↥C.P.H0) = 1 := by rw [htriv]; rfl
  have hκs : sconj C (lamCF C 1) = lamCF C 1 := by
    rw [htriv]
    ext h
    simp [sconj, conjByH_apply]
  have hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → lamCF C 1 h = 1 := by
    intro h _
    rw [htriv]; rfl
  have hdisj : sconj C (lamCF C β * lamCF C 1) ≠ lamCF C β * lamCF C 1 ∨
      (β ≠ 1 ∧ sconj C (lamCF C β) = lamCF C β ∧
        (centralizer ({D.t1} : Set G)).relIndex D.H =
          (centralizer ({D.t2} : Set G)).relIndex D.H) := by
    left
    rw [hβmul]
    exact hβs
  have hkey := hL22 hCompat (lamCF C 1) β hlam1irr hκ1 hκs hκS0 hdisj
  rw [hβmul] at hkey
  -- Coherence (2.3 (iii)): `(λ₁ - λ₃)* = f λ₁ - f λ₃`.
  have hgood := hf.1 (lamCF C 1) hlam1irr
  have hlamEq : LamEquiv C (lamCF C 1) (lamCF C β) := ⟨β, hβmul.symm⟩
  have hμE : lamCF C 1 ∈ orbitKey C (lamCF C 1) := Or.inl (s02c_LamEquiv_refl C (lamCF C 1))
  have hνE : lamCF C β ∈ orbitKey C (lamCF C 1) := Or.inl hlamEq
  have hind_eq : ind C (lamCF C 1 - lamCF C β) = f (lamCF C 1) - f (lamCF C β) :=
    (hgood (lamCF C 1) hμE (lamCF C β) hνE hlam1irr hlam3irr).2.2.2.1 hlamEq
  rw [hind_eq, hlam1dec] at hkey
  -- Degree bookkeeping: `IndDiffProp` gives `λ̃₃(1) = λ̃₁(1) = x + 1`.
  have hdeg : f (lamCF C 1) 1 = f (lamCF C β) 1 := by
    have h0 := (hIndDiff (lamCF C 1) (lamCF C β) hlam1irr hlam3irr hlamEq).2
    rw [hind_eq, ClassFunction.sub_apply] at h0
    linear_combination h0
  have hlam3one : f (lamCF C β) 1 = ((x : ℤ) : ℂ) + 1 := by
    rw [← hdeg, hlam1dec]
    simp only [ClassFunction.add_apply, trivialClassFunction_apply, hxval]
    ring
  have hx1 : x ≠ -1 := by
    intro hx
    have h0 : ((x : ℤ) : ℂ) + 1 = 0 := by rw [hx]; norm_num
    exact hβpm.apply_one_ne_zero (by rw [hlam3one]; exact h0)
  -- X1 with the signed decomposition `λ̃₁ - λ̃₃ = 1_G + φ - λ̃₃`.
  let ε : Fin 3 → ClassFunction G ℂ := ![trivialClassFunction G, φ, - f (lamCF C β)]
  have hsum : (∑ i : Fin 3, ε i) = trivialClassFunction G + φ - f (lamCF C β) := by
    simp [Fin.sum_univ_three, ε, sub_eq_add_neg]
  have hεmem : ∀ i : Fin 3, IsPmIrr (ε i) := by
    intro i
    fin_cases i
    · exact Or.inl (by simpa [ε] using trivialClassFunction_isIrreducible)
    · exact hφpm
    · rcases hβpm with h | h
      · exact Or.inr (by simpa [ε] using h)
      · exact Or.inl (by simpa [ε] using h)
  have hXeq := hX ε hεmem (C.t : G)
  rw [hsum] at hXeq
  have hε0t : ε 0 (C.t : G) = 1 := by simp [ε]
  have hε01 : ε 0 1 = 1 := by simp [ε]
  have hε1t : ε 1 (C.t : G) = 1 := by simp [ε, hφt]
  have hε11 : ε 1 1 = ((x : ℤ) : ℂ) := by simp [ε, hxval]
  have hε2t : ε 2 (C.t : G) = 2 := by simp [ε, hβtval]
  have hε21 : ε 2 1 = -(((x : ℤ) : ℂ) + 1) := by simp [ε, hlam3one]
  have hsumt : (∑ i : Fin 3, ε i (C.t : G) ^ 2 / ε i 1)
      = 1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1) := by
    rw [Fin.sum_univ_three, hε0t, hε01, hε1t, hε11, hε2t, hε21, div_neg]
    ring
  have hcomb : (D.H.index : ℂ) * (∑ i : Fin 3, ε i (C.t : G) ^ 2 / ε i 1)
      = 2 * (D.k : ℂ) ^ 2 := by
    rw [← hXeq]
    exact hkey
  have hfinal : (D.H.index : ℂ) * (1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1))
      = 2 * (D.k : ℂ) ^ 2 := by
    rw [← hsumt]
    exact hcomb
  exact ⟨x, hx0, hx1, keyBigArith D.H.index D.k x hx0 hx1 hfinal⟩

end Work.BG
