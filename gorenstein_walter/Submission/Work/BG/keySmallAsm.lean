import Mathlib
import Submission.Work.BG.Assemblies
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.keyBigArith
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.L41Aux
import Submission.Work.BG.lemma17_iii_lam2Conj
import Submission.Work.BG.indexOdd
import Submission.Work.BG.s02_lamSign
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.keySmallArith
import Submission.Work.BG.keySmallFinal

/-!
# Area BG: **KEYSMALL-ASM** (BG §4, `|S| = 4`)

This module proves the assembly leaf `Work.GW2.C16.KeySmallAsmProp` of
`Submission/Work/BG/Assemblies.lean`, i.e. the passage from the character-theoretic inputs
(`ConstituentSumProp` = X1, `S4DecompProp` = S4-DEC, `Lemma22KappaProp` = Lemma 2.2 for the
orbit of `λ₂`, `KEqSmallProp` = G5, `TDerivedProp` = G10, plus the coherence theorem and
`IndDiffProp` = I-1) to **KEY-SMALL**.

## Route

Let `D` be Bender–Glauberman data with `|S| = 2n = 4` (so `n = 2`), `C` a compatible §2
context and `β₂` a non-trivial linear character of `H₀/U` (`|H₀ : U| = 2`, so `λ₂ = lamCF C β₂`
is *`s`-fixed*, `Lemma17iii.lam2Conj`, and `λ₂(t) = -1`).

* Lemma 2.2 (BG p. 205) at `κ = λ₁ = 1_{H₀}`, `β = β₂`, i.e. `δ = (λ₁ - λ₂λ₁)*`, is applied
  in the *second* clause of its hypothesis: `λ₂` is `s`-fixed (`sconj_lamCF`, `λ₂⁻¹ = λ₂`
  because `|H₀/U| = 2`) and `|t₁^H| = |t₂^H|` is `KEqSmallProp` (G5).  This gives
  `|G : H| · Σ_χ χ(t)²/χ(1) (δ, χ) = 2 k²`.
* `S4DecompProp` expands `δ = 1_G + φ₁ + φ₂ + φ₃` with `φᵢ(t) = 1` and odd degrees
  `a, b, c`.
* X1 (`ConstituentSumProp`) evaluates the sum as `1 + 1/a + 1/b + 1/c`.
* `IndDiffProp` (I-1) gives `δ(1) = 0`, whence `1 + a + b + c = 0`.
* Clearing denominators (`keySmallArith`) gives the integral identity
  `|G:H| (abc + bc + ac + ab) = 2k²·abc`; with `k ≠ 0` (`indexOdd`) a value `-1` among
  `a, b, c` would force `k = 0` (`keySmallFinal`), so each of them is `1` or has
  absolute value `≥ 3`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Subgroup

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem keySmallAsm : Work.GW2.C16.KeySmallAsmProp := by
  intro hBridge hConst hBig hKEq _hTDer
  intro G instG instFin D hn
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  obtain ⟨C, hCompat⟩ := hBridge G D
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨_hCoh, _hIndDiff, hS4, hL22⟩ := hBig G D C
  -- a non-trivial linear character `β₂` of `H₀/U` (`|H₀ : U| = 2`), with `λ₂(t) = -1`.
  obtain ⟨β₂, hβ₂t⟩ := exists_negChar C
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hCompat hn
  have hβ₂ne : β₂ ≠ 1 := by
    intro h
    have h1 : lamCF C (1 : quotGroup C.P →* ℂˣ) C.t = -1 := by rw [← h]; exact hβ₂t
    rw [lamCF_one] at h1
    simp only [linearClassFunction_apply] at h1
    norm_num at h1
  -- `λ₂` is fixed by `s` (`|H₀/U| = 2`).
  have hβ₂fix : sconj C (lamCF C β₂) = lamCF C β₂ := by
    have := lemma17_iii_lam2Conj C.P h2 hβ₂ne C.s
    simpa [sconj, lamCF_eq_lambdaInf] using this
  -- S4-DEC:
  obtain ⟨φ₁, φ₂, φ₃, hφ₁pm, hφ₂pm, hφ₃pm, hδ, hφ₁t, hφ₂t, hφ₃t,
    a, b, c, ha, hb, hc, hφ₁1, hφ₂1, hφ₃1⟩ := hS4 hCompat hn β₂ hβ₂ne
  have htriv : lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 := by
    rw [lamCF_one]
    ext h
    simp [linearClassFunction_apply, trivialClassFunction_apply]
  have hlam1irr : IsIrreducibleCharacter (lamCF C (1 : quotGroup C.P →* ℂˣ)) := by
    rw [htriv]; exact trivialClassFunction_isIrreducible
  have hκ1 : lamCF C (1 : quotGroup C.P →* ℂˣ) (1 : ↥C.P.H0) = 1 := by rw [htriv]; rfl
  have hκs : sconj C (lamCF C (1 : quotGroup C.P →* ℂˣ)) =
      lamCF C (1 : quotGroup C.P →* ℂˣ) := by
    rw [htriv]
    ext h
    simp [sconj, conjByH_apply]
  have hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → lamCF C (1 : quotGroup C.P →* ℂˣ) h = 1 := by
    intro h _
    rw [htriv]; rfl
  have hdisj : (sconj C (lamCF C β₂ * lamCF C (1 : quotGroup C.P →* ℂˣ)) ≠
        lamCF C β₂ * lamCF C (1 : quotGroup C.P →* ℂˣ) ∨
      (β₂ ≠ 1 ∧ sconj C (lamCF C β₂) = lamCF C β₂ ∧
        (centralizer ({D.t1} : Set G)).relIndex D.H =
          (centralizer ({D.t2} : Set G)).relIndex D.H)) := by
    right
    exact ⟨hβ₂ne, hβ₂fix, hKEq G D hn⟩
  -- Lemma 2.2 at `κ = λ₁`, `β = β₂`.
  have hkey := hL22 hCompat (lamCF C (1 : quotGroup C.P →* ℂˣ)) β₂
    hlam1irr hκ1 hκs hκS0 hdisj
  -- S4-DEC in the `ind` form used by X1.
  have hδ' : ind C (lamCF C (1 : quotGroup C.P →* ℂˣ) -
        lamCF C β₂ * lamCF C (1 : quotGroup C.P →* ℂˣ))
      = trivialClassFunction G + φ₁ + φ₂ + φ₃ := by
    simpa only [delta] using hδ
  -- X1 (`ConstituentSumProp`) on `δ = 1_G + φ₁ + φ₂ + φ₃`.
  let ε : Fin 4 → ClassFunction G ℂ := ![trivialClassFunction G, φ₁, φ₂, φ₃]
  have hεmem : ∀ i : Fin 4, IsPmIrr (ε i) := by
    intro i
    fin_cases i
    · exact Or.inl (by simpa [ε] using trivialClassFunction_isIrreducible)
    · exact (by simpa [ε] using hφ₁pm)
    · exact (by simpa [ε] using hφ₂pm)
    · exact (by simpa [ε] using hφ₃pm)
  have hsumε : (∑ i : Fin 4, ε i) = ind C (lamCF C (1 : quotGroup C.P →* ℂˣ) -
      lamCF C β₂ * lamCF C (1 : quotGroup C.P →* ℂˣ)) := by
    rw [Fin.sum_univ_four]
    simp only [ε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    exact hδ'.symm
  have hv0t : ε 0 (C.t : G) = 1 := by simp [ε]
  have hv01 : ε 0 1 = 1 := by simp [ε]
  have hv1t : ε 1 (C.t : G) = 1 := by simp [ε, hφ₁t]
  have hv11 : ε 1 1 = ((a : ℤ) : ℂ) := by simp [ε, hφ₁1]
  have hv2t : ε 2 (C.t : G) = 1 := by simp [ε, hφ₂t]
  have hv21 : ε 2 1 = ((b : ℤ) : ℂ) := by simp [ε, hφ₂1]
  have hv3t : ε 3 (C.t : G) = 1 := by simp [ε, hφ₃t]
  have hv31 : ε 3 1 = ((c : ℤ) : ℂ) := by simp [ε, hφ₃1]
  have hrhs : (∑ i : Fin 4, ε i (C.t : G) ^ 2 / ε i 1)
      = 1 + 1 / ((a : ℤ) : ℂ) + 1 / ((b : ℤ) : ℂ) + 1 / ((c : ℤ) : ℂ) := by
    rw [Fin.sum_univ_four, hv0t, hv01, hv1t, hv11, hv2t, hv21, hv3t, hv31]
    norm_num
  have hXeq := hConst ε hεmem (C.t : G)
  rw [hsumε] at hXeq
  rw [hrhs] at hXeq
  have hfin : (D.H.index : ℂ) *
      (1 + 1 / ((a : ℤ) : ℂ) + 1 / ((b : ℤ) : ℂ) + 1 / ((c : ℤ) : ℂ))
      = 2 * (D.k : ℂ) ^ 2 := by
    rw [← hXeq]
    exact hkey
  have ha0 : a ≠ 0 := by obtain ⟨m, hm⟩ := ha; omega
  have hb0 : b ≠ 0 := by obtain ⟨m, hm⟩ := hb; omega
  have hc0 : c ≠ 0 := by obtain ⟨m, hm⟩ := hc; omega
  have heqzs := keySmallArith D.H.index D.k a b c ha0 hb0 hc0 hfin
  -- `δ(1) = 0` (I-1) gives `1 + a + b + c = 0`.
  have hδ1 : delta C β₂ (lamCF C (1 : quotGroup C.P →* ℂˣ)) 1 = 0 :=
    l41_delta_apply_one C hlam1irr
  have hsum : 1 + a + b + c = 0 := by
    have hev := congrArg (fun f : ClassFunction G ℂ => f 1) hδ
    rw [hδ1, ClassFunction.add_apply, ClassFunction.add_apply, ClassFunction.add_apply,
      trivialClassFunction_apply, hφ₁1, hφ₂1, hφ₃1] at hev
    have hcast : (((1 + a + b + c : ℤ)) : ℂ) = (((0 : ℤ)) : ℂ) := by
      push_cast
      rw [hev]
    exact_mod_cast hcast
  have hknz : D.k ≠ 0 := (indexOdd G D).2.ne'
  have hconcl := keySmallFinal D.H.index D.k a b c ha hb hc hsum heqzs hknz
  exact ⟨a, b, c, ha, hb, hc, hconcl.1, hconcl.2.1, hconcl.2.2, hsum, heqzs⟩

end Work.BG
