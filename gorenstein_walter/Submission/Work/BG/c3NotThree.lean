import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.thm32
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.indexOdd
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.c3Bounds
import Submission.Work.BG.c3Sfixed2
import Submission.Work.BG.c3DegEq2
import Submission.Work.BG.frobeniusCardDvd
import Submission.Work.BG.c3Kdiv
import Submission.Work.BG.c3IdentityTail
import Submission.Work.BG.c3KappaTValue
import Submission.Work.GLUE.Defs

/-!
# Area BG: `Work.BG.c3NotThree` — Bender–Glauberman, proof of Theorem C, the case `|𝒮(χ₁)| = 3`

BG 1981, p. 211.  With `𝒮(χ) := {ν ∈ Irr(H₀) | (χ, ν̃) ≠ 0}` and `κ₁` the character of §2
(linear, trivial on `S₀`, `s`-fixed), the argument is:

* `|𝒮(χ)| ≤ 3` for every `χ ∈ ±Irr(G)` (Theorem 3.2, `Work.BG.thm32`);
* if `|𝒮(χ₁)| = 3` with `(χ₁, κ̃₁) = 1` then `𝒮(χ₁) = {κ₁, ν₁, ν₂}` with `νᵢ` `s`-fixed and
  `|Λνᵢ| ≠ m` (Lemmas 3.3, 3.4 and `κ₁` linear);
* the two `δᵢ = νᵢ - μᵢ` (with `μᵢ` the other `s`-fixed member of `Λνᵢ`) satisfy
  `δ₁* = χ₁ - χ₂ + φ + σ`, `δ₂* = χ₁ - χ₂ - φ - σ`, so `χ₁(1) = χ₂(1)`; with
  `χ₃ = κ̃₃` (`κ₃ = λ₃κ₁` not `s`-fixed) one also has `χ₃(1) = 2χ₁(1)` (same `Λ`-orbit as
  `χ₁ + χ₂ = κ̃₁`), so (6) reads `k²·χ₁(1) = x²·|G : H|`;
* `2|K| ∣ k` and `(|K|, |G:H|) = 1` give `2|K| ∣ x`, and `|x| ≤ 2|B|` (equation (4) with
  `|𝒮(χ₁)| = 3`) gives `|K| ≤ |B|`, contradicting the Frobenius divisibility `|B| ∣ |K| - 1`
  of `BK`.

The steps above are the delegated sub-lemmas `Work.BG.c3Sfixed`, `Work.BG.c3DegEq`,
`Work.BG.c3Kdiv`, `Work.BG.frobeniusCardDvd`; the assembly and the final arithmetic
(`Work.BG.c3Arith`) are below.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## 1. Infrastructure -/

/-- The §3 standing hypothesis (`Sec3Hyp`) follows from the hypotheses of Theorem C:
`thmCSec3` (BG "G6") shows that every square `x²` with `x ∈ S₀` centralizes `U`. -/
theorem sec3Hyp_of_thmCHyps {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (K1 K2 : Subgroup G)
    (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) : Work.GW2.C16.Sec3Hyp D :=
  (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1

/-- `|𝒮(χ)| ≤ 3` (BG Theorem 3.2) under the hypotheses of Theorem C. -/
theorem bset_ncard_le_three {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ) :
    (Work.GW2.C16.bset C f χ).ncard ≤ 3 :=
  thm32 D C hComp (sec3Hyp_of_thmCHyps D K1 K2 hHyps) f hf χ hχ

/-- On a single `Λ`-orbit the coherent lifts have a common degree: `f μ 1 = f ν 1` for
`LamEquiv C μ ν`, because `f μ - f ν = (μ - ν)^{H₀→G}` and `(μ - ν)^{H₀→G}` has degree `0`
(`IndDiffProp`, `Work.BG.s02_indDiff`). -/
theorem orbit_degree_eq {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ)
    (hν : IsIrreducibleCharacter ν) (hlam : LamEquiv C μ ν) : f μ 1 = f ν 1 := by
  classical
  have hν' : ν ∈ orbitKey C μ := Or.inl hlam
  have hμ' : μ ∈ orbitKey C μ := Or.inl (s02c_LamEquiv_refl C μ)
  have hG := (hf.1 μ hμ) ν hν' μ hμ' hν hμ
  have hlam' : LamEquiv C ν μ := s02c_LamEquiv_symm C hlam
  have hind : ind C (ν - μ) = f ν - f μ := hG.2.2.2.1 hlam'
  have hdeg : ind C (ν - μ) 1 = 0 := (s02_indDiff C ν μ hν hμ hlam').2
  have hsub : (f ν - f μ) 1 = 0 := by rw [← hind]; exact hdeg
  rw [ClassFunction.sub_apply] at hsub
  exact (sub_eq_zero.mp hsub).symm

/-! ## 2. The final arithmetic (BG p. 211) -/

/-- **Final arithmetic of the `|𝒮(χ₁)| = 3` case.**  Suppose

* `k²·d = N·x²` (the identity (6) of p. 211 after `χ₁(1) = χ₂(1)`, `χ₃(1) = 2χ₁(1)`),
  with `k ≠ 0`, `d ≠ 0` and `N ≠ 0`;
* `2|K| ∣ k` (`c3Kdiv`) and `(K, N) = 1` (the coprimality of Theorem C), `K` odd;
* `|x| ≤ 2|B|` (equation (4) with `|𝒮(χ₁)| = 3`) and `|B| ∣ |K| - 1` (Frobenius, `BK`).

Then `2|K| ∣ x`, so `2|K| ≤ |x| ≤ 2|B|` gives `|K| ≤ |B|`, contradicting `|B| ∣ |K| - 1`
with `|K| > 1` (the Frobenius kernel is nontrivial). -/
theorem c3Arith {N k K B D X : ℕ} (hk : 0 < k) (hD : 0 < D) (hN : 0 < N) (hNodd : Odd N)
    (hKodd : Odd K) (hK2 : 2 ≤ K) (hcop : Nat.Coprime K N)
    (hkdvd : 2 * K ∣ k) (hid : k ^ 2 * D = N * X ^ 2)
    (hBdvd : B ∣ K - 1) (hX : X ≤ 2 * B) : False := by
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0] at hid
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hid
    have := hid
    rw [mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact absurd h (by positivity)
  have hcop' : Nat.Coprime (2 * K) N :=
    Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hNodd) hcop
  have h1 : (2 * K) ^ 2 ∣ k ^ 2 := by
    obtain ⟨j, hj⟩ := hkdvd
    exact ⟨j ^ 2, by rw [hj]; ring⟩
  have h2 : (2 * K) ^ 2 ∣ N * X ^ 2 :=
    h1.trans ⟨D, by rw [← hid]⟩
  have h3 : (2 * K) ^ 2 ∣ X ^ 2 :=
    (hcop'.pow_left 2).dvd_of_dvd_mul_left h2
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX0
  have h4 : (2 * K) ^ 2 ≤ X ^ 2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hX2) h3
  have h5 : 2 * K ≤ X := by nlinarith [h4, Nat.zero_le (2 * K), Nat.zero_le X]
  have hKB : K ≤ B := by omega
  have hpos : 0 < K - 1 := by omega
  have hBpos : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h] at hBdvd
      simp only [Nat.zero_dvd] at hBdvd
      omega
    · exact h
  have hle : B ≤ K - 1 := Nat.le_of_dvd hpos hBdvd
  omega

/-- Transport of an integral identity to natural absolute values: from
`k²·d = N·x²` over `ℤ` one gets `k²·|d| = N·|x|²` over `ℕ`. -/
theorem natAbs_identity {k N : ℕ} {d x : ℤ} (h : (k : ℤ) ^ 2 * d = (N : ℤ) * x ^ 2) :
    k ^ 2 * d.natAbs = N * x.natAbs ^ 2 := by
  have h' := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
    Int.natAbs_natCast, Int.natAbs_natCast] at h'
  exact h'

/-- The degree `φ 1` of a signed irreducible, as an integer. -/
theorem pmIrr_degree_int {K : Type} [Group K] [Finite K] {φ : ClassFunction K ℂ}
    (h : Work.BG.IsPmIrr φ) : ∃ d : ℤ, φ 1 = (d : ℂ) ∧ d ≠ 0 := by
  rcases h with h | h
  · obtain ⟨n, hnpos, hn, -⟩ :=
      IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card h
    exact ⟨n, hn, by exact_mod_cast hnpos.ne'⟩
  · obtain ⟨n, hnpos, hn, -⟩ :=
      IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card h
    refine ⟨-(n : ℤ), ?_, ?_⟩
    · have hn' : -(φ 1) = (n : ℂ) := by
        rw [← ClassFunction.neg_apply]
        exact hn
      have h1 : φ 1 = -(n : ℂ) := by
        rw [← neg_neg (φ 1), hn']
      rw [h1]
      push_cast
      ring
    · omega

/-- Clearing the denominator in the identity `|G:H|·(2x²/d) = 2k²` and passing to `ℤ`. -/
theorem key_of_div {N k : ℕ} {d x : ℤ} (hd : d ≠ 0)
    (h : (N : ℂ) * (2 * (x : ℂ) ^ 2 / (d : ℂ)) = 2 * (k : ℂ) ^ 2) :
    (k : ℤ) ^ 2 * d = (N : ℤ) * x ^ 2 := by
  have h1 : (N : ℂ) * (2 * (x : ℂ) ^ 2) = 2 * (k : ℂ) ^ 2 * (d : ℂ) := by
    have hc : (N : ℂ) * (2 * (x : ℂ) ^ 2 / (d : ℂ)) * (d : ℂ) = (N : ℂ) * (2 * (x : ℂ) ^ 2) := by
      field_simp
    rw [← hc, h]
  have h2 : ((N : ℤ) * x ^ 2 : ℤ) = ((k : ℤ) ^ 2 * d : ℤ) := by
    have hck : (((N : ℤ) * x ^ 2 : ℤ) : ℂ) = (((k : ℤ) ^ 2 * d : ℤ) : ℂ) := by
      push_cast
      linear_combination (1 / 2) * h1
    exact_mod_cast hck
  linarith [h2]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3NotThree {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.C3NotThreeProp D C K1 K2 := by
  intro hComp hHyps hSimp hn4 f hf κ hκ χ₁ hχ₁ hinner h3
  -- ## The §3 hypothesis and the bounds of C3-2
  have hS3 : Work.GW2.C16.Sec3Hyp D := sec3Hyp_of_thmCHyps D K1 K2 hHyps
  obtain ⟨x, hxt, hxb, -, htrig⟩ :=
    Work.BG.c3Bounds D C K1 K2 hComp hHyps hn4 hS3 f hf κ hκ χ₁ hχ₁ hinner
  -- ## C3-3: the structure of `𝒮(χ₁)`, the degree equality, and (6)
  have hsf := c3Sfixed2 D C K1 K2 hComp hHyps hSimp hn4 f hf κ hκ χ₁ hχ₁ hinner h3
  obtain ⟨χ₂, χ₃, β, hχ₂, horth, hfκ, hβt, hχ₃eq, hχ₃, hid6⟩ :=
    Work.BG.c3IdentityTail D C K1 K2 hComp hn4 hS3 f hf κ hκ χ₁ hχ₁ hinner
  have hκt2 : f κ (C.t : G) = 2 := Work.BG.c3KappaTValue D C hComp hn4 hS3 f hf κ hκ
  have hdeg12 : χ₁ 1 = χ₂ 1 :=
    c3DegEq2 D C K1 K2 hComp hHyps hSimp hn4 f hf κ hκ χ₁ χ₂ hχ₁ hχ₂ horth hfκ h3
      (fun ν hv hne => (hsf ν hv hne).1) (fun ν hv hne => (hsf ν hv hne).2)
  -- `χ₃ = f (λ_β κ)` has the degree of `f κ` (same `Λ`-orbit)
  have hlam3 : LamEquiv C κ (lamCF C β * κ) := ⟨β, rfl⟩
  have hχ₃1 : χ₃ 1 = f κ 1 := by
    rw [hχ₃eq]
    exact (orbit_degree_eq (C := C) (f := f) (μ := κ) (ν := lamCF C β * κ) hf hκ.1
      (lambda_mul_irreducible C.P ⟨β, rfl⟩ hκ.1) hlam3).symm
  have hd3 : χ₃ 1 = 2 * χ₁ 1 := by
    rw [hχ₃1, hfκ, ClassFunction.add_apply, hdeg12]
    ring
  have hsum2 : χ₁ (C.t : G) + χ₂ (C.t : G) = 2 := by
    have h := hκt2
    rw [hfκ] at h
    rwa [ClassFunction.add_apply] at h
  have hval2 : χ₂ (C.t : G) = 1 - x := by
    linear_combination hsum2 - hxt
  -- ## The identity (6) becomes `k²·d = |G:H|·x²`
  obtain ⟨d, hd, hd0⟩ := pmIrr_degree_int (K := G) hχ₁
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hbracket : χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 - 4 / χ₃ 1
      = 2 * (x : ℂ) ^ 2 / (d : ℂ) := by
    have e1 : χ₁ (C.t : G) = 1 + (x : ℂ) := hxt
    have e2 : χ₂ (C.t : G) = 1 - (x : ℂ) := hval2
    have e3 : χ₁ 1 = (d : ℂ) := hd
    have e4 : χ₂ 1 = (d : ℂ) := hdeg12.symm.trans hd
    have e5 : χ₃ 1 = 2 * (d : ℂ) := by rw [hd3, hd]
    rw [e1, e2, e3, e4, e5]
    field_simp
    ring
  have hkeyC : (D.H.index : ℂ) * (2 * (x : ℂ) ^ 2 / (d : ℂ)) = 2 * (D.k : ℂ) ^ 2 := by
    rw [← hbracket]
    exact hid6
  have hkeyZ : (D.k : ℤ) ^ 2 * d = (D.H.index : ℤ) * x ^ 2 :=
    key_of_div (N := D.H.index) (k := D.k) hd0 hkeyC
  have hmain := natAbs_identity (k := D.k) (N := D.H.index) (d := d) (x := x) hkeyZ
  -- ## The remaining numerical inputs
  have hidx := indexOdd G D
  -- `|x| ≤ 2|B|` (equation (4) with `|𝒮(χ₁)| = 3`)
  have hx2B : x.natAbs ≤ 2 * Nat.card D.B := by
    have h := hxb
    rw [h3] at h
    simp only [Nat.reduceSub, Nat.cast_ofNat] at h
    have := abs_le.mp h
    omega
  -- `K = |K₁ ⊓ K₂|` is odd, `≥ 2`, coprime to `|G:H|`; `2K ∣ k`
  have hKodd : Odd (Nat.card (K1 ⊓ K2 : Subgroup G)) :=
    Odd.of_dvd_nat hHyps.1.2.1 (Subgroup.card_dvd_of_le inf_le_left)
  have hcop : Nat.Coprime (Nat.card (K1 ⊓ K2 : Subgroup G)) D.H.index := hHyps.2.2.2.1
  have hkdvd : 2 * Nat.card (K1 ⊓ K2 : Subgroup G) ∣ D.k := Work.BG.c3Kdiv D K1 K2 hHyps
  -- `𝒮(χ₁) ≠ {κ}`, so `U ≠ BK` and `BK` is Frobenius
  have hne : Work.GW2.C16.bset C f χ₁ ≠ {κ} := by
    intro hcon
    rw [hcon] at h3
    simp at h3
  have hfr : Work.GW2.IsFrobeniusWith (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B :=
    hHyps.2.2.2.2.2 (htrig hne)
  have hK2 : 2 ≤ Nat.card (K1 ⊓ K2 : Subgroup G) := by
    have hbot : (K1 ⊓ K2 : Subgroup G) ≠ ⊥ := hfr.2.2.2.2.1
    have hcard : Nat.card (K1 ⊓ K2 : Subgroup G) ≠ 1 := fun h1 =>
      hbot (Subgroup.card_eq_one.mp h1)
    have hpos : 0 < Nat.card (K1 ⊓ K2 : Subgroup G) := Nat.card_pos
    omega
  have hBdvd : Nat.card D.B ∣ Nat.card (K1 ⊓ K2 : Subgroup G) - 1 :=
    Work.BG.frobeniusCardDvd (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B hfr
  -- ## Final arithmetic
  exact c3Arith (N := D.H.index) (k := D.k) (K := Nat.card (K1 ⊓ K2 : Subgroup G))
    (B := Nat.card D.B) (D := d.natAbs) (X := x.natAbs)
    hidx.2 (Int.natAbs_pos.mpr hd0) (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    hidx.1 hKodd hK2 hcop hkdvd hmain hBdvd hx2B

end Work.BG
