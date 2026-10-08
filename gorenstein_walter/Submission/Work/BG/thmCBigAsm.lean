import Mathlib
import Submission.Work.BG.Assemblies
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.keyBigArith
import Submission.Work.BG.arithC3
import Submission.Work.BG.indexOdd
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lemma17_ii_aux
import Submission.Work.BG.thmCBigKeyIneq
import Submission.Work.BG.thmCBigIneqArith

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- A signed irreducible character whose inner product with the trivial character is nonzero
is `±1_G`. -/
theorem pmIrr_eq_pm_triv_of_inner_triv_ne_zero {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ)
    (hne : ClassFunction.inner χ (trivialClassFunction G) ≠ 0) :
    χ = trivialClassFunction G ∨ χ = -trivialClassFunction G := by
  rcases hχ with h | h
  · left
    by_cases heq : (⟨χ, h⟩ : IrreducibleCharacter G) =
        ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
    · exact congrArg Subtype.val heq
    · exfalso
      have hite := irreducibleCharacter_inner_eq_ite (⟨χ, h⟩ : IrreducibleCharacter G)
        ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
      rw [if_neg heq] at hite
      exact hne (by simpa using hite)
  · right
    by_cases heq : (⟨-χ, h⟩ : IrreducibleCharacter G) =
        ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
    · have h1 : -χ = trivialClassFunction G := congrArg Subtype.val heq
      rw [show χ = -(-χ) by simp, h1]
    · exfalso
      have hite := irreducibleCharacter_inner_eq_ite (⟨-χ, h⟩ : IrreducibleCharacter G)
        ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
      rw [if_neg heq] at hite
      have h0 : ClassFunction.inner (-χ) (trivialClassFunction G) = 0 := by simpa using hite
      have h1 : ClassFunction.inner χ (trivialClassFunction G) = 0 := by
        have hh := ClassFunction.inner_neg_left χ (trivialClassFunction G)
        rw [hh] at h0
        exact neg_eq_zero.mp h0
      exact hne h1

/-- A constituent of `f κ` (with `κ` admissible) is not `±1_G`. -/
theorem inner_triv_eq_zero_of_constituent {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (φ : ClassFunction G ℂ) (hφ1 : ClassFunction.inner φ (trivialClassFunction G) = 0)
    (hφdec : f (lamCF C 1) = trivialClassFunction G + φ)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκirr : IsIrreducibleCharacter κ)
    (hκne : κ ≠ lamCF C 1) (hκt : κ C.t = 1)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hκin : ClassFunction.inner χ (f κ) = 1)
    (hcard : (bset C f χ).ncard ≤ 2) :
    ClassFunction.inner χ (trivialClassFunction G) = 0 := by
  classical
  have htriv : lamCF C 1 = trivialClassFunction ↥C.P.H0 := by
    rw [lamCF_one]
    ext h
    simp [linearClassFunction_apply, trivialClassFunction_apply]
  by_contra hne
  have hcases := pmIrr_eq_pm_triv_of_inner_triv_ne_zero hχ hne
  have hχν : χ (C.t : G) ≠ 0 := by
    rcases hcases with h | h
    · rw [h]; simp [trivialClassFunction_apply]
    · rw [h]; simp [ClassFunction.neg_apply, trivialClassFunction_apply]
  have hinnerl : ClassFunction.inner χ (f (lamCF C 1)) = χ (C.t : G) := by
    have h2 : ClassFunction.inner (trivialClassFunction G) φ = 0 := by
      rw [ClassFunction.inner_star_comm, hφ1, star_zero]
    rcases hcases with h | h
    · rw [h, hφdec, ClassFunction.inner_add_right,
        IsIrreducibleCharacter.inner_self_eq_one trivialClassFunction_isIrreducible, h2, add_zero]
      simp [trivialClassFunction_apply]
    · rw [h, hφdec, ClassFunction.inner_neg_left, ClassFunction.inner_add_right,
        IsIrreducibleCharacter.inner_self_eq_one trivialClassFunction_isIrreducible, h2, add_zero]
      simp [ClassFunction.neg_apply, trivialClassFunction_apply]
  have hlmem : lamCF C 1 ∈ bset C f χ := by
    refine ⟨?_, ?_⟩
    · rw [htriv]; exact trivialClassFunction_isIrreducible
    · rw [hinnerl]; exact hχν
  have hkmem : κ ∈ bset C f χ := ⟨hκirr, by rw [hκin]; norm_num⟩
  have hbset : bset C f χ = {lamCF C 1, κ} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (lemma24 C f hf χ hχ).1
    · intro x hx
      rcases hx with h | h
      · exact h ▸ hlmem
      · exact h ▸ hkmem
    · rw [Set.ncard_pair (fun h => hκne h.symm)]
      exact hcard
  obtain ⟨hbfin, hval, -⟩ := lemma24 C f hf χ hχ
  have hvalt := hval C.t C.t_not_mem_U
  rw [finsum_mem_eq_finite_toFinset_sum _ hbfin] at hvalt
  have h2fin : ({lamCF C 1, κ} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  have hto : hbfin.toFinset = h2fin.toFinset := Set.Finite.toFinset_inj.mpr hbset
  rw [hto, Set.Finite.toFinset_insert, Set.Finite.toFinset_singleton] at hvalt
  rw [Finset.sum_pair (fun h => hκne h.symm)] at hvalt
  have hl1t : (lamCF C 1 : ClassFunction ↥C.P.H0 ℂ) C.t = 1 := by rw [htriv]; rfl
  rw [hinnerl, hl1t, mul_one, hκin, one_mul, hκt] at hvalt
  have h0 : (1 : ℂ) = 0 := by
    have h := congrArg (fun z : ℂ => z - χ (C.t : G)) hvalt
    simpa using h
  exact one_ne_zero h0

/-! ## Backup proof of the orbit-disjunction (used only if the delegation stalls) -/

theorem ncard_four_of_ne {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Set α).ncard = 4 := by
  have h1 : ({a, b, c, d} : Set α) = insert a (insert b (insert c {d})) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [h1]
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_insert_of_notMem (by simp [hcd]), Set.ncard_singleton]

theorem thmCBigOrbitDisjAux {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hCompat : Compat D C) (hSec3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκirr : IsIrreducibleCharacter κ)
    (hκs : sconj C κ = κ) (β : quotGroup C.P →* ℂˣ)
    (hdirr : IsIrreducibleCharacter (lamCF C β * κ))
    (hpm : IsPmIrr (f (lamCF C β * κ))) :
    (∃ ν ∈ bset C f (f (lamCF C β * κ)), sconj C ν = ν) ∨
      (∀ ν ∈ bset C f (f (lamCF C β * κ)), sconj C ν ∈ lamOrbit C ν) := by
  classical
  have hbs := bset_orbit_struct C f hf (f (lamCF C β * κ)) hpm
  have hstab := hbs.1
  have h32 : (bset C f (f (lamCF C β * κ))).ncard ≤ 3 :=
    thm32 D C hCompat hSec3 f hf (f (lamCF C β * κ)) hpm
  have hfin : (bset C f (f (lamCF C β * κ))).Finite := s02_bset_finite C f _
  have hψmem : lamCF C β * κ ∈ bset C f (f (lamCF C β * κ)) := by
    refine ⟨hdirr, ?_⟩
    rw [IsPmIrr.inner_self hpm]; norm_num
  have hΛψ : LamEquiv C (lamCF C β * κ) (sconj C (lamCF C β * κ)) := by
    have hκeq : lamCF C β⁻¹ * (lamCF C β * κ) = κ := by
      have h2 : lamCF C β⁻¹ * lamCF C β = lamCF C 1 := lambdaInf_inv_mul C.P β
      rw [← mul_assoc_cf, h2, lamCF_one, one_mul_cf]
    refine ⟨β⁻¹ * β⁻¹, ?_⟩
    calc sconj C (lamCF C β * κ) = lamCF C β⁻¹ * κ := by rw [sconjLam C β κ, hκs]
      _ = lamCF C β⁻¹ * (lamCF C β⁻¹ * (lamCF C β * κ)) := by conv_lhs => rw [← hκeq]
      _ = (lamCF C β⁻¹ * lamCF C β⁻¹) * (lamCF C β * κ) := by rw [mul_assoc_cf]
      _ = lamCF C (β⁻¹ * β⁻¹) * (lamCF C β * κ) := by rw [← s02c_lamCF_mul]
  by_cases hfix : ∃ ν ∈ bset C f (f (lamCF C β * κ)), sconj C ν = ν
  · exact Or.inl hfix
  · right
    intro ν hν
    have hno : sconj C (lamCF C β * κ) ≠ lamCF C β * κ :=
      fun h => hfix ⟨_, hψmem, h⟩
    have hsub : bset C f (f (lamCF C β * κ)) ⊆
        {lamCF C β * κ, sconj C (lamCF C β * κ)} := by
      intro τ hτ
      by_contra hτnot
      have hτne1 : τ ≠ lamCF C β * κ :=
        fun h => hτnot (by rw [h]; exact Set.mem_insert _ _)
      have hτne2 : τ ≠ sconj C (lamCF C β * κ) :=
        fun h => hτnot (by rw [h]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hτc : sconj C τ ∈ bset C f (f (lamCF C β * κ)) := (hstab τ hτ).1
      have hτcne : sconj C τ ≠ τ := fun h => hfix ⟨τ, hτ, h⟩
      have hτcne1 : sconj C τ ≠ lamCF C β * κ := by
        intro h
        apply hτne2
        have h2 : sconj C (sconj C τ) = sconj C (lamCF C β * κ) := by rw [h]
        rwa [s02c_sconj_involutive] at h2
      have hτcne2 : sconj C τ ≠ sconj C (lamCF C β * κ) := by
        intro h
        apply hτne1
        have h2 : sconj C (sconj C τ) = sconj C (sconj C (lamCF C β * κ)) := by rw [h]
        rwa [s02c_sconj_involutive, s02c_sconj_involutive] at h2
      have h4 : ({lamCF C β * κ, sconj C (lamCF C β * κ), τ, sconj C τ} : Set _).ncard = 4 :=
        ncard_four_of_ne (fun h => hno h.symm) hτne1.symm hτcne1.symm hτne2.symm
          hτcne2.symm hτcne.symm
      have hsub4 : ({lamCF C β * κ, sconj C (lamCF C β * κ), τ, sconj C τ} : Set _) ⊆
          bset C f (f (lamCF C β * κ)) := by
        intro x hx
        rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
          rfl | rfl | rfl | rfl
        · exact hψmem
        · exact (hstab _ hψmem).1
        · exact hτ
        · exact hτc
      have := Set.ncard_le_ncard hsub4 hfin
      omega
    have hνeq : ν = lamCF C β * κ ∨ ν = sconj C (lamCF C β * κ) := by
      have h := hsub hν
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hνeq with h | h
    · rw [h]; exact hΛψ
    · rw [h, s02c_sconj_involutive]; exact s02c_LamEquiv_symm C hΛψ

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem thmCBigAsm : Work.GW2.C16.ThmCBigAsmProp := by
  unfold Work.GW2.C16.ThmCBigAsmProp
  intro hBridge hX hSec3 hKNeOne hArith hBundle
  intro G _ _ D K1 K2 hn hK1 hK2 hdir hcop hB' hfr hSimple
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  obtain ⟨C, hCompat⟩ := hBridge G D
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hSec3Hyp, hBU⟩ := hSec3 G D K1 K2 hK1 hK2 hdir hB'
  have hK : K1 ⊓ K2 ≠ ⊥ := hKNeOne G D K1 K2 hK1 hK2 hdir hB' hfr hSimple
  have hThm : ThmCHyps D K1 K2 := ⟨hK1, hK2, hdir, hcop, hB', hfr⟩
  obtain ⟨hCoh, hIndDiff, hDecompBig, hKappaEx, hL22, hC3Id, hC3Bounds, hC3NotThree,
    hC3Deg⟩ := hBundle G D C K1 K2 hCompat hThm
  obtain ⟨f, hf⟩ := (coherence23_iff C).mp hCoh
  obtain ⟨κ, hκ⟩ := hKappaEx hCompat hBU
  obtain ⟨hκirr, hκ1, hκs, hκS0, hκne⟩ := hκ
  have hκK : IsKappa D C κ := ⟨hκirr, hκ1, hκs, hκS0, hκne⟩
  obtain ⟨β, hβt, hβs, hlam3pm, hlam3t, φ, hφpm, hφ1, -, hφdec, hφt⟩ :=
    hDecompBig hCompat hn f hf
  obtain ⟨χ₁, χ₂, hχ₁pm, hχ₂pm, hχ₁χ₂, hfκ, hχ₃pm, hχ₃t2, hsumt, h6⟩ :=
    hC3Id hCompat hn hSec3Hyp f hf κ hκK β hβt
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hCompat.t_eq]; exact D.t_mem)
  have hi1 : ClassFunction.inner χ₁ (f κ) = 1 := by
    rw [hfκ, ClassFunction.inner_add_right, IsPmIrr.inner_self hχ₁pm, hχ₁χ₂, add_zero]
  have hχ₂χ₁ : ClassFunction.inner χ₂ χ₁ = 0 := by
    rw [ClassFunction.inner_star_comm, hχ₁χ₂, star_zero]
  have hi2 : ClassFunction.inner χ₂ (f κ) = 1 := by
    rw [hfκ, ClassFunction.inner_add_right, hχ₂χ₁, zero_add, IsPmIrr.inner_self hχ₂pm]
  -- cardinality bounds on the supports
  have h32₁ : (bset C f χ₁).ncard ≤ 3 := thm32 D C hCompat hSec3Hyp f hf χ₁ hχ₁pm
  have h3₁ : (bset C f χ₁).ncard ≠ 3 :=
    hC3NotThree hCompat hThm hSimple hn f hf κ hκK χ₁ hχ₁pm hi1
  have hcard₁ : (bset C f χ₁).ncard ≤ 2 := by omega
  have h32₂ : (bset C f χ₂).ncard ≤ 3 := thm32 D C hCompat hSec3Hyp f hf χ₂ hχ₂pm
  have h3₂ : (bset C f χ₂).ncard ≠ 3 :=
    hC3NotThree hCompat hThm hSimple hn f hf κ hκK χ₂ hχ₂pm hi2
  have hcard₂ : (bset C f χ₂).ncard ≤ 2 := by omega
  -- the values of χ₁, χ₂ at t
  obtain ⟨x, hχ₁t, hxbd, hx2bd, htrig⟩ :=
    hC3Bounds hCompat hThm hn hSec3Hyp f hf κ hκK χ₁ hχ₁pm hi1
  obtain ⟨y, hχ₂t, -, -, -⟩ :=
    hC3Bounds hCompat hThm hn hSec3Hyp f hf κ hκK χ₂ hχ₂pm hi2
  have hyx : y = -x := by
    have hsum := hsumt
    rw [hχ₁t, hχ₂t] at hsum
    have h0 : ((x + y : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hsum
    have h1 : x + y = 0 := by exact_mod_cast h0
    omega
  have hχ₂t' : χ₂ (C.t : G) = 1 - x := by
    rw [hχ₂t, hyx]
    push_cast
    ring
  -- orthogonality to the trivial character
  have ho1 : ClassFunction.inner χ₁ (trivialClassFunction G) = 0 :=
    inner_triv_eq_zero_of_constituent C f hf φ hφ1 hφdec κ hκirr hκne hκt χ₁ hχ₁pm hi1 hcard₁
  have ho2 : ClassFunction.inner χ₂ (trivialClassFunction G) = 0 :=
    inner_triv_eq_zero_of_constituent C f hf φ hφ1 hφdec κ hκirr hκne hκt χ₂ hχ₂pm hi2 hcard₂
  have ho3 : ClassFunction.inner (f (lamCF C β * κ)) (trivialClassFunction G) = 0 := by
    by_contra hne
    rcases pmIrr_eq_pm_triv_of_inner_triv_ne_zero hχ₃pm hne with h | h
    · rw [h] at hχ₃t2
      norm_num [trivialClassFunction_apply] at hχ₃t2
    · rw [h] at hχ₃t2
      norm_num [ClassFunction.neg_apply, trivialClassFunction_apply] at hχ₃t2
  -- the disjunctions
  have htrivLam : lamCF C 1 = trivialClassFunction ↥C.P.H0 := by
    rw [lamCF_one]
    ext h
    simp [linearClassFunction_apply, trivialClassFunction_apply]
  have hlamIrr : IsIrreducibleCharacter (lamCF C 1) := by
    rw [htrivLam]; exact trivialClassFunction_isIrreducible
  have hlamS : sconj C (lamCF C 1) = lamCF C 1 := by
    rw [htrivLam]
    ext h
    simp [sconj, conjByH_apply]
  have hκmem₁ : κ ∈ bset C f χ₁ := ⟨hκirr, by rw [hi1]; norm_num⟩
  have hκmem₂ : κ ∈ bset C f χ₂ := ⟨hκirr, by rw [hi2]; norm_num⟩
  have hlamMemPhi : lamCF C 1 ∈ bset C f φ := by
    refine ⟨hlamIrr, ?_⟩
    rw [hφdec, ClassFunction.inner_add_right, hφ1, IsPmIrr.inner_self hφpm]
    norm_num
  have hdis₁ : (∃ ν ∈ bset C f χ₁, sconj C ν = ν) ∨
      (∀ ν ∈ bset C f χ₁, sconj C ν ∈ lamOrbit C ν) := Or.inl ⟨κ, hκmem₁, hκs⟩
  have hdis₂ : (∃ ν ∈ bset C f χ₂, sconj C ν = ν) ∨
      (∀ ν ∈ bset C f χ₂, sconj C ν ∈ lamOrbit C ν) := Or.inl ⟨κ, hκmem₂, hκs⟩
  have hdisφ : (∃ ν ∈ bset C f φ, sconj C ν = ν) ∨
      (∀ ν ∈ bset C f φ, sconj C ν ∈ lamOrbit C ν) := Or.inl ⟨lamCF C 1, hlamMemPhi, hlamS⟩
  have hlam3mem : lamCF C β ∈ Lambda C.P := ⟨β, rfl⟩
  have hlam3κirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P hlam3mem hκirr
  have hlam3κmem : lamCF C β * κ ∈ bset C f (f (lamCF C β * κ)) :=
    ⟨hlam3κirr, by rw [IsPmIrr.inner_self hχ₃pm]; norm_num⟩
  have hdis₃ := thmCBigOrbitDisjAux D C hCompat hSec3Hyp f hf κ hκirr hκs β hlam3κirr hχ₃pm
  -- C3-4 for the four characters
  obtain ⟨A1, hA1, hA1B, d1, hd1eq, hd1bd⟩ :=
    hC3Deg hCompat hThm hSimple hn f hf χ₁ hχ₁pm ho1 hdis₁ ⟨κ, hκmem₁⟩
  obtain ⟨A2, hA2, hA2B, d2, hd2eq, hd2bd⟩ :=
    hC3Deg hCompat hThm hSimple hn f hf χ₂ hχ₂pm ho2 hdis₂ ⟨κ, hκmem₂⟩
  obtain ⟨A3, hA3, hA3B, d3, hd3eq, hd3bd⟩ :=
    hC3Deg hCompat hThm hSimple hn f hf (f (lamCF C β * κ)) hχ₃pm ho3 hdis₃
      ⟨lamCF C β * κ, hlam3κmem⟩
  obtain ⟨A4, hA4, hA4B, d4, hd4eq, hd4bd⟩ :=
    hC3Deg hCompat hThm hSimple hn f hf φ hφpm hφ1 hdisφ ⟨lamCF C 1, hlamMemPhi⟩
  -- Lemma 2.5's identity at φ
  obtain ⟨d0, hd0eq, hKey⟩ :=
    thmCBigKeyIneq D C hCompat hn f hf hX hIndDiff hL22 hDecompBig φ hφpm hφ1 hφdec hφt
  have hd04 : d0 = d4 := by
    have h : ((d0 : ℤ) : ℂ) = ((d4 : ℤ) : ℂ) := by rw [← hd0eq, hd4eq]
    exact_mod_cast h
  -- the common constant A
  let A : ℕ := min (min A1 A2) (min A3 A4)
  have hAge : 1 ≤ A := by
    have h := le_min (le_min hA1 hA2) (le_min hA3 hA4)
    simpa [A] using h
  have hAB : D.U ≠ D.B ⊔ (K1 ⊓ K2) → Nat.card D.B ≤ A := by
    intro hU
    have h := le_min (le_min (hA1B hU) (hA2B hU)) (le_min (hA3B hU) (hA4B hU))
    simpa [A] using h
  have hleA₁ : A ≤ A1 := by
    simp only [A]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hleA₂ : A ≤ A2 := by
    simp only [A]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hleA₃ : A ≤ A3 := by
    simp only [A]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hleA₄ : A ≤ A4 := by
    simp only [A]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hbd_of_le : ∀ {A' : ℕ}, A ≤ A' → 8 * (A : ℤ) + 1 ≤ 8 * (A' : ℤ) + 1 := by
    intro A' hle
    have : (A : ℤ) ≤ (A' : ℤ) := by exact_mod_cast hle
    linarith
  have hd1bd' : 8 * (A : ℤ) + 1 ≤ |d1| := le_trans (hbd_of_le hleA₁) hd1bd
  have hd2bd' : 8 * (A : ℤ) + 1 ≤ |d2| := le_trans (hbd_of_le hleA₂) hd2bd
  have hd3bd' : 8 * (A : ℤ) + 1 ≤ |d3| := le_trans (hbd_of_le hleA₃) hd3bd
  have hd4bd' : 8 * (A : ℤ) + 1 ≤ |d4| := le_trans (hbd_of_le hleA₄) hd4bd
  have hd0bd' : 8 * (A : ℤ) + 1 ≤ |d0| := by rw [hd04]; exact hd4bd'
  have h9 : 9 ≤ |d0| := by
    have h : 9 ≤ 8 * (A : ℤ) + 1 := by
      have : (1 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hAge
      linarith
    rw [hd04]
    linarith [hd4bd']
  -- Lemma 2.5's inequality
  have hineq : (D.H.index : ℚ) * (1 - 3 / |(d0 : ℚ)|) < 2 * (D.k : ℚ) ^ 2 :=
    thmCBigIneqArith D.H.index D.k d0
      (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) h9 hKey
  -- the identity (6) over ℚ
  have h6q : (D.H.index : ℚ) * ((1 + (x : ℚ)) ^ 2 / (d1 : ℚ) + (1 - (x : ℚ)) ^ 2 / (d2 : ℚ) -
      4 / (d3 : ℚ)) = 2 * (D.k : ℚ) ^ 2 := by
    have hcast : (((D.H.index : ℚ) * ((1 + (x : ℚ)) ^ 2 / (d1 : ℚ) + (1 - (x : ℚ)) ^ 2 / (d2 : ℚ) -
        4 / (d3 : ℚ)) : ℚ) : ℂ) = ((2 * (D.k : ℚ) ^ 2 : ℚ) : ℂ) := by
      push_cast
      rw [← hd1eq, ← hd2eq, ← hd3eq, ← hχ₁t, ← hχ₂t']
      simpa only [Nat.cast_add] using h6
    exact Rat.cast_injective hcast
  -- the bound `x ≠ 0 → x² ≤ 2|B| ∧ |B| ≤ A`
  have hb2 : 2 ≤ Nat.card D.B := by
    have hBne : D.B ≠ ⊥ := by
      intro hbot
      exact hB' (by rw [hbot, Subgroup.commutator_bot_left])
    have hne1 : Nat.card D.B ≠ 1 := fun h => hBne (Subgroup.card_eq_one.mp h)
    have hpos : 0 < Nat.card D.B := Nat.card_pos
    omega
  have hxb : x ≠ 0 → x ^ 2 ≤ 2 * (Nat.card D.B : ℤ) ∧ Nat.card D.B ≤ A := by
    intro hx0
    refine ⟨hx2bd hcard₁, ?_⟩
    have hUBK : D.U ≠ D.B ⊔ (K1 ⊓ K2) := by
      refine htrig ?_
      intro hbs
      obtain ⟨-, hval1, -⟩ := lemma24 C f hf χ₁ hχ₁pm
      have h := hval1 C.t C.t_not_mem_U
      rw [hbs, finsum_mem_eq_finite_toFinset_sum _ (Set.finite_singleton κ),
        Set.Finite.toFinset_singleton, Finset.sum_singleton, hi1, one_mul, hκt] at h
      have hx0' : x = 0 := by
        have h2 : ((x : ℤ) : ℂ) = 0 := by
          have h3 : (1 : ℂ) + ((x : ℤ) : ℂ) = 1 := by rw [← hχ₁t]; exact h
          linear_combination h3
        exact_mod_cast h2
      exact hx0 hx0'
    exact hAB hUBK
  exact hArith D.H.index D.k A (Nat.card D.B) x d1 d2 d3 d0
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) hAge hb2
    hd1bd' hd2bd' hd3bd' hd0bd' hineq h6q hxb

end Work.BG
