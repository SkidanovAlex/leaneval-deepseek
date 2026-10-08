import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.c3ExcFourB
import Submission.Work.BG.c3ExcNeFourC
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.sconjLam
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.nCases
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.CharBridge
import Submission.Work.BG.H0Conj
import Submission.Work.GLUE.Defs

/-!
# Area BG: the value `κ̃₁(t) = 2` of the coherent lift of the admissible `κ₁`

`Work.GW2.C16` records the §2/§3 vocabulary of Bender–Glauberman 1981; `Work.BG.c3Identity`
proves the identity (6) of the proof of Theorem C (p. 211) and, along the way, that the
coherent lift `κ̃₁ = f κ` of the admissible linear character `κ = κ₁` has value `2` at the
central involution `t`:

  `f κ (t) = χ₁(t) + χ₂(t) = 2`.

This file isolates that value.

## Route (BG pp. 204, 209, 210)

* Choose `β : H₀/U →* ℂˣ` with `λ_β(t) = -1` and `λ_β^s ≠ λ_β`
  (`Work.BG.exists_lamCF_t_neg_one_sconj_ne`), and put `ν := λ_β κ`.  Then `ν` is irreducible,
  `ν(t) = -1`, `ν^s ≠ ν` and `Λν = Λκ` has `n = |H₀ : U| = D.n` elements
  (the stabiliser of `κ` is trivial because `κ` is `1` on `S₀` and `H₀ = U·S₀`).
* `f ν ∈ ±Irr(G)`, and `f ν(t) = 2ν(t) = -2`:
  * if `|Λν| = D.n ≠ 4`, clause (vi) of `GoodOn` (coherence, Theorem 2.3) applies directly;
  * if `D.n = 4` we are in the exceptional configuration of BG Lemma 3.4
    (`|Λν| = 4` and `Λν` is `s`-stable, since `κ^s = κ`), where `𝒮(f ν) = {ν, ν^s}`:
    a third member which is not `s`-fixed contradicts `|𝒮| ≤ 3` (Theorem 3.2); an `s`-fixed
    third member is impossible by the two exceptional sub-lemmas
    (`Work.BG.c3ExcFourB`, `Work.BG.c3ExcNeFourC`).  Then Lemma 2.4 at `t` gives the value.
* Clause (v) of coherence at `t` for the `Λ`-equivalent pair `(ν, κ)` gives
  `f ν (t) - f κ (t) = 2(ν(t) - κ(t)) = -4`, i.e. `f κ(t) = f ν(t) + 4 = 2`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Helpers on `κ` -/

/-- **Cancellation of the `Λ`-action on `κ`.**  If `κ` is trivial on `S₀ = D.S0` then
`λ_γ κ = λ_{γ'} κ` forces `γ = γ'`: evaluating on the elements of `S₀` (where `κ = 1`) shows
`λ_γ = λ_{γ'}` there, and since `H₀ = U · S₀` while all `λ` are trivial on `U`, this gives
`γ = γ'`. -/
private theorem lamCF_mul_cancel (D : BGData G) (C : Sec2Ctx G) (hcompat : Compat D C)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {γ γ' : quotGroup C.P →* ℂˣ} (h : lamCF C γ * κ = lamCF C γ' * κ) : γ = γ' := by
  have hval' : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → γ (quotMk C.P s) = γ' (quotMk C.P s) := by
    intro s hs
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) h
    simp only [ClassFunction.mul_apply] at h'
    rw [hκS0 s hs] at h'
    rw [lamCF_apply, lamCF_apply] at h'
    exact Units.ext (by simpa using h')
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
  calc γ (quotMk C.P x) = γ (quotMk C.P s) := by rw [hπ]
    _ = γ' (quotMk C.P s) := hval' s hs
    _ = γ' (quotMk C.P x) := by rw [hπ]

/-- The stabiliser of `κ` in `Λ` is trivial when `κ` is `1` on `S₀`. -/
private theorem lamStab_kappa_eq_bot (D : BGData G) (C : Sec2Ctx G) (hcompat : Compat D C)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) :
    lamStab C κ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [mem_lamStab] at hγ
  have h1 : lamCF C γ * κ = lamCF C 1 * κ := by
    rw [hγ, lamCF_one, one_mul_cf]
  exact lamCF_mul_cancel D C hcompat κ hκS0 h1

/-- **The `Λ`-orbit of `κ` has `D.n` elements** when `κ` is `1` on `S₀`: the orbit–stabiliser
count `|Λ_κ| · |Λκ| = |H₀ : U|` together with `|Λ_κ| = 1` and `|H₀ : U| = D.n`. -/
private theorem orbit_lamCF_mul_kappa_card (D : BGData G) (C : Sec2Ctx G)
    (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) (β : quotGroup C.P →* ℂˣ) :
    (lamOrbit C (lamCF C β * κ)).ncard = D.n := by
  have hstab : lamStab C κ = ⊥ := lamStab_kappa_eq_bot D C hcompat κ hκS0
  have hcard1 : Nat.card ↥(lamStab C κ) = 1 := by rw [hstab]; exact Subgroup.card_bot
  have h2 := rem31StabCard C κ
  rw [hcard1, one_mul, rem31IndexUin D C hcompat] at h2
  rw [← s02c_lamOrbit_eq_of_lamEquiv C (show LamEquiv C κ (lamCF C β * κ) from ⟨β, rfl⟩)]
  exact h2

/-- `λ_β κ` is not `s`-fixed when `λ_β` is not (`κ` being `s`-fixed): otherwise
`λ_{β⁻¹} κ = λ_β κ` and cancellation forces `β⁻¹ = β`, i.e. `λ_β^s = λ_β`. -/
private theorem sconj_lamCF_mul_ne (D : BGData G) (C : Sec2Ctx G) (hcompat : Compat D C)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    (hκsconj : sconj C κ = κ)
    (β : quotGroup C.P →* ℂˣ) (hβ : sconj C (lamCF C β) ≠ lamCF C β) :
    sconj C (lamCF C β * κ) ≠ lamCF C β * κ := by
  intro hfix
  have hA : sconj C (lamCF C β * κ) = lamCF C β⁻¹ * κ := by
    rw [sconjLam C β κ, hκsconj]
  have h1 : lamCF C β⁻¹ * κ = lamCF C β * κ := by rw [← hA]; exact hfix
  have h2 : β⁻¹ = β := lamCF_mul_cancel D C hcompat κ hκS0 h1
  exact hβ (by rw [LamCFFixed.sconj_lamCF C β, h2])

/-- The orbit `Λ(λ_β κ)` is `s`-stable when `κ` is `s`-fixed (`λ_β κ` has its `s`-conjugate
`λ_{β⁻¹} κ` in the same orbit). -/
private theorem lamOrbit_sconj_image_eq (D : BGData G) (C : Sec2Ctx G) (_hcompat : Compat D C)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκsconj : sconj C κ = κ) (β : quotGroup C.P →* ℂˣ) :
    sconj C '' lamOrbit C (lamCF C β * κ) = lamOrbit C (lamCF C β * κ) := by
  have hLκ : LamEquiv C κ (sconj C (lamCF C β * κ)) := by
    refine ⟨β⁻¹, ?_⟩
    rw [sconjLam C β κ, hκsconj]
  rw [s02c_sconj_image_lamOrbit C (sconjLam C) (lamCF C β * κ)]
  exact (s02c_lamOrbit_eq_of_lamEquiv C hLκ).symm.trans
    (s02c_lamOrbit_eq_of_lamEquiv C ⟨β, rfl⟩)

/-! ## 2. `𝒮(χ)` is `s`-stable, and a non-fixed third member is impossible -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- Coherence keeps membership in `𝒮(χ)` under `s`-conjugation: `f (ξ^s) = f ξ`. -/
private theorem sconj_mem_bset {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : ξ ∈ bset C f χ) :
    sconj C ξ ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hξ.1, ?_⟩
  have hk : ξ ∈ orbitKey C ξ := Or.inl (s02c_LamEquiv_refl C ξ)
  have hfix : f (sconj C ξ) = f ξ := ((hf.1 ξ hξ.1) ξ hk ξ hk hξ.1 hξ.1).2.1
  rw [hfix]
  exact hξ.2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **A non-`s`-fixed third member of `𝒮(χ)` is impossible**: `ν, ν^s, ξ, ξ^s` would be four
distinct members, contradicting Theorem 3.2 (`|𝒮| ≤ 3`). -/
private theorem no_third_nonfixed {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (ξ : ClassFunction ↥C.P.H0 ℂ) (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν)
    (hξνs : ξ ≠ sconj C ν) (hξs : sconj C ξ ≠ ξ) : False := by
  have h2 : sconj C ν ∈ bset C f χ := sconj_mem_bset C f hf χ hν
  have h4 : sconj C ξ ∈ bset C f χ := sconj_mem_bset C f hf χ hξ
  have h12 : ν ≠ sconj C ν := fun h => hne h.symm
  have h13 : ν ≠ ξ := fun h => hξν h.symm
  have h14 : ν ≠ sconj C ξ := by
    intro h
    apply hξνs
    calc ξ = sconj C (sconj C ξ) := (s02c_sconj_involutive C ξ).symm
      _ = sconj C ν := by rw [← h]
  have h23 : sconj C ν ≠ ξ := by
    intro h
    apply h14
    calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
      _ = sconj C ξ := by rw [h]
  have h24 : sconj C ν ≠ sconj C ξ := by
    intro h
    apply h13
    calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
      _ = sconj C (sconj C ξ) := by rw [h]
      _ = ξ := s02c_sconj_involutive C ξ
  have h34 : ξ ≠ sconj C ξ := fun h => hξs h.symm
  have hsub : ({ν, sconj C ν, ξ, sconj C ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
    · exact h4
  have hncard : ({ν, sconj C ν, ξ, sconj C ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14]),
      Set.ncard_insert_of_notMem (by simp [h23, h24]),
      Set.ncard_insert_of_notMem (by simp [h34]), Set.ncard_singleton]
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hle4 : 4 ≤ (bset C f χ).ncard := by
    have := Set.ncard_le_ncard hsub hfin
    omega
  have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  omega

/-! ## 3. The value of `f (λ_β κ)` at `t` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **`f (λ_β κ)(t) = -2`.**  For `λ_β(t) = -1`, `λ_β` not `s`-fixed, and an admissible `κ`,
the coherent lift of `ν = λ_β κ` is a signed irreducible with `ν̃(t) = 2ν(t) = -2`. -/
private theorem value_lamCF_mul_kappa {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : IsKappa D C κ)
    (β : quotGroup C.P →* ℂˣ) (hβt : lamCF C β C.t = -1)
    (hβs : sconj C (lamCF C β) ≠ lamCF C β) :
    f (lamCF C β * κ) (C.t : G) = -2 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, -⟩ := hκ
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hComp.t_eq]; exact D.t_mem)
  have hνirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hνt : (lamCF C β * κ) C.t = -1 := by
    rw [ClassFunction.mul_apply, hκt, hβt, mul_one]
  have hsconj : sconj C (lamCF C β * κ) ≠ lamCF C β * κ :=
    sconj_lamCF_mul_ne D C hComp κ hκS0 hκsconj β hβs
  have horb : (lamOrbit C (lamCF C β * κ)).ncard = D.n :=
    orbit_lamCF_mul_kappa_card D C hComp κ hκS0 β
  -- coherence at the orbit of `ν = λ_β κ`
  have hkey : lamCF C β * κ ∈ orbitKey C (lamCF C β * κ) :=
    Or.inl (s02c_LamEquiv_refl C _)
  have hG := (hf.1 (lamCF C β * κ) hνirr) (lamCF C β * κ) hkey
    (lamCF C β * κ) hkey hνirr hνirr
  obtain ⟨hZI, hscf, hnorm, -, -, hvi⟩ := hG
  have hnorm1 : ClassFunction.inner (f (lamCF C β * κ)) (f (lamCF C β * κ)) = 1 := by
    rw [hnorm, if_neg hsconj]
  have hpmν : IsPmIrr (f (lamCF C β * κ)) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hZI hnorm1
  have hνmem : (lamCF C β * κ) ∈ bset C f (f (lamCF C β * κ)) :=
    ⟨hνirr, by rw [hnorm1]; norm_num⟩
  by_cases h4 : D.n = 4
  · -- exceptional configuration: `𝒮(f ν) = {ν, ν^s}`, then Lemma 2.4 at `t`
    have h4L : (lamOrbit C (lamCF C β * κ)).ncard = 4 := horb.trans h4
    have hinv : sconj C '' lamOrbit C (lamCF C β * κ) = lamOrbit C (lamCF C β * κ) :=
      lamOrbit_sconj_image_eq D C hComp κ hκsconj β
    have hνs_mem : sconj C (lamCF C β * κ) ∈ bset C f (f (lamCF C β * κ)) :=
      sconj_mem_bset C f hf (f (lamCF C β * κ)) hνmem
    have hbsetν : bset C f (f (lamCF C β * κ)) = {lamCF C β * κ, sconj C (lamCF C β * κ)} := by
      refine Set.Subset.antisymm ?_ ?_
      · intro ξ hξ
        by_contra hmem
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        push_neg at hmem
        obtain ⟨hξν, hξνs⟩ := hmem
        by_cases hfix : sconj C ξ = ξ
        · by_cases hξ4 : (lamOrbit C ξ).ncard = 4
          · exact c3ExcFourB D C hComp hS3 f hf (f (lamCF C β * κ)) hpmν
              (lamCF C β * κ) hνmem hsconj (Or.inr horb) h4L hinv ξ hξ hξν hξνs hfix hξ4
          · exact c3ExcNeFourC D C hComp hS3 f hf (f (lamCF C β * κ)) hpmν
              (lamCF C β * κ) hνmem hsconj (Or.inr horb) h4L hinv ξ hξ hξν hξνs hfix hξ4
        · exact no_third_nonfixed D C hComp hS3 f hf (f (lamCF C β * κ)) hpmν
            (lamCF C β * κ) hνmem hsconj ξ hξ hξν hξνs hfix
      · intro ξ hξ
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hξ
        rcases hξ with rfl | rfl
        · exact hνmem
        · exact hνs_mem
    have hT := (lemma24 C f hf (f (lamCF C β * κ)) hpmν).2.1 C.t C.t_not_mem_U
    have hnot1 : (lamCF C β * κ) ∉
        ({sconj C (lamCF C β * κ)} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact hsconj hmem.symm
    have hsum : (∑ᶠ η ∈ bset C f (f (lamCF C β * κ)),
          ClassFunction.inner (f (lamCF C β * κ)) (f η) * η C.t) = -2 := by
      rw [hbsetν,
        finsum_mem_insert (f := fun η => ClassFunction.inner (f (lamCF C β * κ)) (f η) * η C.t)
          (a := lamCF C β * κ)
          (s := ({sconj C (lamCF C β * κ)} : Set (ClassFunction ↥C.P.H0 ℂ)))
          hnot1 (Set.toFinite _),
        finsum_mem_singleton, hscf, hnorm1, sconj_apply_t, hνt]
      norm_num
    rw [hsum] at hT
    exact hT
  · -- generic case: clause (vi) of `GoodOn`
    have hnotex : ¬ ((lamOrbit C (lamCF C β * κ)).ncard = 4 ∧
        sconj C '' lamOrbit C (lamCF C β * κ) = lamOrbit C (lamCF C β * κ)) := by
      rintro ⟨h1, -⟩
      rw [horb] at h1
      exact h4 h1
    have hv := hvi hsconj hnotex
    rw [hνt] at hv
    simpa using hv

/-! ## 4. The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3KappaTValue {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hn4 : 4 ≤ D.n) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ) :
    f κ (C.t : G) = 2 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨β, hβt, hβs⟩ := exists_lamCF_t_neg_one_sconj_ne D C hComp hn4
  have hval : f (lamCF C β * κ) (C.t : G) = -2 :=
    value_lamCF_mul_kappa D C hComp hS3 f hf κ hκ β hβt hβs
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, -⟩ := hκ
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hComp.t_eq]; exact D.t_mem)
  have hνirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hνt : (lamCF C β * κ) C.t = -1 := by
    rw [ClassFunction.mul_apply, hκt, hβt, mul_one]
  have hLam : LamEquiv C κ (lamCF C β * κ) := ⟨β, rfl⟩
  -- clause (v) of coherence at `t` for the `Λ`-equivalent pair `(λ_β κ, κ)`
  have h := hf.2.2 (lamCF C β * κ) κ hνirr hκirr (s02c_LamEquiv_symm C hLam)
    C.t C.t_not_mem_U
  rw [conjMulEquiv_s_t C] at h
  simp only [ClassFunction.sub_apply] at h
  have h1 : f (lamCF C β * κ) (C.t : G) - f κ (C.t : G) =
      2 * ((lamCF C β * κ) C.t - κ C.t) := by
    rw [h]; ring
  rw [hνt, hκt] at h1
  linear_combination -h1 + hval

end Work.BG
