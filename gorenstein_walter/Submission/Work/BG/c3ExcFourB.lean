import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.l34TwoSfixedMaximal
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_abstractCoherence

/-!
# Area BG: BG 1981 Lemma 3.4, the exceptional case with an `s`-fixed third member (`|\Lambda\xi| = 4`)

This file proves `Work.BG.c3ExcFourB` (the same statement as `Work.BG.l34Exc_sfixed_four` and
`Work.BG.noThirdSfixedFour`).  The proof is the assembly recorded in
`Submission/Work/BG/l34Exc_sfixed_four.lean`, with its single deep input
`Work.BG.l34TwoSfixedMaximal` taken from the (fully proved) module
`Submission.Work.BG.l34TwoSfixedMaximal`.

Setting (Bender–Glauberman 1981, `Work.BG.Sec2Ctx`, `\mathcal{S}(\chi) = bset C f \chi`, `f`
the coherent map of Theorem 2.3): `\chi \in \pm\mathrm{Irr}(G)`, `\nu \in \mathcal{S}(\chi)`
with `\nu^s \neq \nu`, the standing Lemma 3.4 hypotheses
(`\nu^s \notin \Lambda\nu` or `|\Lambda\nu| = D.n`), `|\Lambda\nu| = 4`, `\Lambda\nu` is
`s`-stable; and `\xi \in \mathcal{S}(\chi)` is `s`-fixed with `|\Lambda\xi| = 4`.  Then
`False`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

section Helpers

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `(χ,χ) = 1` for a signed irreducible `χ`. -/
private theorem c3E4B_inner_self_pmIrr {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ) :
    ClassFunction.inner χ χ = 1 := by
  rcases hχ with h | h
  · exact (irreducibleCharacter_inner_eq_ite ⟨χ, h⟩ ⟨χ, h⟩).trans (if_pos rfl)
  · have h2 : ClassFunction.inner (-χ) (-χ) = 1 :=
      (irreducibleCharacter_inner_eq_ite ⟨-χ, h⟩ ⟨-χ, h⟩).trans (if_pos rfl)
    rwa [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg] at h2

/-- A norm-one element of `ℤ[Irr G]` that is not orthogonal to a signed irreducible `χ` equals
`(χ,φ) • φ`. -/
private theorem c3E4B_eq_smul_of_inner_ne_zero {φ χ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hn : ClassFunction.inner φ φ = 1) (hχ : IsPmIrr χ)
    (h : ClassFunction.inner χ φ ≠ 0) :
    χ = (ClassFunction.inner χ φ) • φ := by
  have hχχ := c3E4B_inner_self_pmIrr hχ
  have heval := inner_pmIrr_eq_pm_one hφ (Or.inl hn) hχ h
  have hself : ClassFunction.inner (χ - (ClassFunction.inner χ φ) • φ)
      (χ - (ClassFunction.inner χ φ) • φ) = 0 := by
    rcases heval with h1 | h1
    · rw [h1, one_smul]
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hn, hχχ, h1, ClassFunction.inner_star_comm φ χ, h1]
      norm_num
    · rw [h1, neg_one_smul, sub_neg_eq_add]
      rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_add_right, hn, hχχ, h1, ClassFunction.inner_star_comm φ χ, h1]
      norm_num
  have hzero := eq_zero_of_inner_self_re_eq_zero (φ := χ - _ • φ)
    (by rw [hself]; rfl)
  exact sub_eq_zero.mp hzero
end Helpers

section Main

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3ExcFourB {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard = 4 → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4ν hinv ξ hξ hξν hξνs hξs hξ4
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨hνirr, hνne0⟩ := hν
  obtain ⟨hξirr, hξne0⟩ := hξ
  have hνmem : ν ∈ bset C f χ := ⟨hνirr, hνne0⟩
  have hξmem : ξ ∈ bset C f χ := ⟨hξirr, hξne0⟩
  -- ## basic facts about the coherent map `f`
  have hkeyν : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  obtain ⟨hZIfν, hfνs, hnormfν, -, -, -⟩ := (hf.1 ν hνirr) ν hkeyν ν hkeyν hνirr hνirr
  have hnormfν1 : ClassFunction.inner (f ν) (f ν) = 1 := by
    rw [hnormfν]; simp [hne]
  have hkeyξ : ξ ∈ orbitKey C ξ := Or.inl (s02c_LamEquiv_refl C ξ)
  obtain ⟨hZIfξ, -, hnormfξ, -, -, -⟩ := (hf.1 ξ hξirr) ξ hkeyξ ξ hkeyξ hξirr hξirr
  have hnormfξ2 : ClassFunction.inner (f ξ) (f ξ) = 2 := by
    rw [hnormfξ]; simp [hξs]
  -- ## `χ = e_ν • f ν`; the coefficients
  set eν : ℂ := ClassFunction.inner χ (f ν) with heν
  set eξ : ℂ := ClassFunction.inner χ (f ξ) with heξ
  have hχeq : χ = eν • f ν := by
    rw [heν]; exact c3E4B_eq_smul_of_inner_ne_zero hZIfν hnormfν1 hχ hνne0
  have hξpm : ClassFunction.inner χ (f ξ) = 1 ∨ ClassFunction.inner χ (f ξ) = -1 :=
    inner_pmIrr_eq_pm_one hZIfξ (Or.inr hnormfξ2) hχ hξne0
  have hνpm : ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1 :=
    inner_pmIrr_eq_pm_one hZIfν (Or.inl hnormfν1) hχ hνne0
  have heξ1 : eξ = 1 ∨ eξ = -1 := by
    rcases hξpm with h1 | h1
    · exact Or.inl (heξ.trans h1)
    · exact Or.inr (heξ.trans h1)
  have heν1 : eν = 1 ∨ eν = -1 := by
    rcases hνpm with h1 | h1
    · exact Or.inl (heν.trans h1)
    · exact Or.inr (heν.trans h1)
  have heξ_ne : eξ ≠ 0 := by rcases heξ1 with h1 | h1 <;> rw [h1] <;> norm_num
  have heν_ne : eν ≠ 0 := by rcases heν1 with h1 | h1 <;> rw [h1] <;> norm_num
  -- ## `D.n = 4`
  have hmem : sconj C ν ∈ lamOrbit C ν := by
    have h : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, mem_lamOrbit_self C ν, rfl⟩
    rwa [hinv] at h
  have hn4 : D.n = 4 := by
    rcases hdisj with h | h
    · exact absurd hmem h
    · omega
  -- ## `ξ ∉ Λν`
  have hbset_orbit := (bset_orbit_struct C f hf χ hχ).2
  have hξnotlam : ¬ LamEquiv C ν ξ := fun hlam => hξνs (hbset_orbit ν hνmem ξ hξmem hlam hξν)
  have hnotlamsξ : ¬ LamEquiv C (sconj C ν) ξ :=
    fun h => hξnotlam (s02c_LamEquiv_trans C hmem h)
  -- ## two distinct `s`-fixed members of `Λν`
  have hfixν : ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard
      = 2 := ((s02_lemma21 C) ν hνirr).2 hinv
  have hfixν_fin : ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    (orbit_finite C ν).subset (fun _ hx => hx.1)
  obtain ⟨ν', hν'mem, hν'fix⟩ := (Set.ncard_pos hfixν_fin).mp (by omega)
  have hν'orbit : LamEquiv C ν ν' := hν'mem
  have hν'orbit_eq : lamOrbit C ν' = lamOrbit C ν :=
    (lamOrbit_eq_of_lamEquiv hν'orbit).symm
  have hν'irr : IsIrreducibleCharacter ν' := irreducible_of_mem_lamOrbit C hν'mem hνirr
  have hν'neν : ν' ≠ ν := fun h => hne (h ▸ hν'fix)
  have hν'neξ : ν' ≠ ξ := fun h => hξnotlam (h ▸ hν'orbit)
  have hν''_ne : ∃ ν'', ν'' ∈ ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) ∧ ν'' ≠ ν' := by
    by_contra hc
    push_neg at hc
    have hsub : ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
        Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ {ν'} := fun x hx => by
      simpa using hc x hx
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton ν')
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨ν'', hν''memS, hν''ne'⟩ := hν''_ne
  have hν''orbit : LamEquiv C ν ν'' := hν''memS.1
  have hν''fix : sconj C ν'' = ν'' := hν''memS.2
  have hν''irr : IsIrreducibleCharacter ν'' := irreducible_of_mem_lamOrbit C hν''memS.1 hνirr
  have hν''neν' : ν'' ≠ ν' := hν''ne'
  have hν''neν : ν'' ≠ ν := fun h => hne (h ▸ hν''fix)
  have hν''neξ : ν'' ≠ ξ := fun h => hξnotlam (h ▸ hν''orbit)
  have hν''orbit_eq : lamOrbit C ν'' = lamOrbit C ν :=
    (lamOrbit_eq_of_lamEquiv hν''orbit).symm
  -- ## a non-`s`-fixed member `μ` of `Λξ`
  have hξstab : sconj C '' lamOrbit C ξ = lamOrbit C ξ := by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) ξ, hξs]
  have hnotfixξ : ∃ μ ∈ lamOrbit C ξ, sconj C μ ≠ μ := by
    by_contra hc
    push_neg at hc
    have hset : ({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ))
        = lamOrbit C ξ :=
      Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, hc x hx⟩⟩
    have h2 := ((s02_lemma21 C) ξ hξirr).2 hξstab
    rw [hset, hξ4] at h2
    norm_num at h2
  obtain ⟨μ, hμorbit, hμnotfix⟩ := hnotfixξ
  have hμirr : IsIrreducibleCharacter μ := irreducible_of_mem_lamOrbit C hμorbit hξirr
  have hμ_ne_ξ : μ ≠ ξ := fun h => hμnotfix (h ▸ hξs)
  have hμ_not_bset : ClassFunction.inner χ (f μ) = 0 := by
    by_contra h0
    exact hμ_ne_ξ ((hbset_orbit ξ hξmem μ ⟨hμirr, h0⟩ hμorbit hμ_ne_ξ).trans hξs)
  have hχfν'_zero : ClassFunction.inner χ (f ν') = 0 := by
    by_contra h0
    have h := hbset_orbit ν hνmem ν' ⟨hν'irr, h0⟩ hν'orbit hν'neν
    exact hν'neν (by rw [← hν'fix, h, s02c_sconj_involutive C ν])
  have hχfν''_zero : ClassFunction.inner χ (f ν'') = 0 := by
    by_contra h0
    have h := hbset_orbit ν hνmem ν'' ⟨hν''irr, h0⟩ hν''orbit hν''neν
    exact hν''neν (by rw [← hν''fix, h, s02c_sconj_involutive C ν])
  -- ## the signed irreducible `ζ = f ξ - e_ξ • χ`
  obtain ⟨t, ht, htZI⟩ : ∃ t : ℤ, ((t : ℂ) = eξ) ∧ (f ξ - t • χ ∈ ZIrr G) := by
    rcases heξ1 with h1 | h1
    · refine ⟨1, ?_, ?_⟩
      · rw [h1]; norm_num
      · rw [one_smul]; exact Submodule.sub_mem _ hZIfξ (mem_ZIrr_of_isPmIrr hχ)
    · refine ⟨-1, ?_, ?_⟩
      · rw [h1]; norm_num
      · rw [neg_one_smul, sub_neg_eq_add]
        exact Submodule.add_mem _ hZIfξ (mem_ZIrr_of_isPmIrr hχ)
  have ht_smul : t • χ = (t : ℂ) • χ := (Int.cast_smul_eq_zsmul ℂ t χ).symm
  have hζ_norm : ClassFunction.inner (f ξ - t • χ) (f ξ - t • χ) = 1 := by
    rw [ht_smul, ht]
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, ClassFunction.inner_smul_right,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
      ClassFunction.inner_smul_left, hnormfξ2, c3E4B_inner_self_pmIrr hχ,
      ClassFunction.inner_star_comm (f ξ) χ, ← heξ]
    rcases heξ1 with h1 | h1 <;> rw [h1] <;> norm_num
  have hζpm : IsPmIrr (f ξ - t • χ) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one htZI hζ_norm
  have hξ_bset : ξ ∈ bset C f (f ξ - t • χ) := by
    refine ⟨hξirr, ?_⟩
    rw [ClassFunction.inner_sub_left, ht_smul, ht, ClassFunction.inner_smul_left, heξ,
      hnormfξ2]
    rcases hξpm with h1 | h1 <;> rw [h1] <;> norm_num
  -- ## `(f ν', f ξ) = 0` and `(f ν'', f ξ) = 0`
  have hfν'ξ : ClassFunction.inner (f ν') (f ξ) = 0 := by
    by_contra h0
    have hb : ν' ∈ bset C f (f ξ - t • χ) := by
      refine ⟨hν'irr, ?_⟩
      rw [ClassFunction.inner_sub_left, ht_smul, ht, ClassFunction.inner_smul_left,
        hχfν'_zero, mul_zero, sub_zero]
      intro h
      exact h0 (by rw [ClassFunction.inner_star_comm (f ν') (f ξ), h, star_zero])
    exact l34TwoSfixedMaximal D C hDC hS3 (by omega) f hf (f ξ - t • χ) hζpm
      ν' hb ξ hξ_bset hν'neξ hν'fix hξs
      (by rw [hν'orbit_eq, h4ν, hn4]) (by rw [hξ4, hn4])
  have hfν''ξ : ClassFunction.inner (f ν'') (f ξ) = 0 := by
    by_contra h0
    have hb : ν'' ∈ bset C f (f ξ - t • χ) := by
      refine ⟨hν''irr, ?_⟩
      rw [ClassFunction.inner_sub_left, ht_smul, ht, ClassFunction.inner_smul_left,
        hχfν''_zero, mul_zero, sub_zero]
      intro h
      exact h0 (by rw [ClassFunction.inner_star_comm (f ν'') (f ξ), h, star_zero])
    exact l34TwoSfixedMaximal D C hDC hS3 (by omega) f hf (f ξ - t • χ) hζpm
      ν'' hb ξ hξ_bset hν''neξ hν''fix hξs
      (by rw [hν''orbit_eq, h4ν, hn4]) (by rw [hξ4, hn4])
  -- ## the two coefficients coming from coherence clause (iv)
  have hfνξ : ClassFunction.inner (f ν) (f ξ) = eν * eξ := by
    have h := congrArg (fun z => ClassFunction.inner z (f ξ)) hχeq
    rw [ClassFunction.inner_smul_left, ← heξ] at h
    rcases heν1 with h1 | h1
    · rw [h1, one_mul] at h
      rw [h1, one_mul]
      exact h.symm
    · rw [h1, neg_one_mul] at h
      rw [h1, neg_one_mul]
      exact (neg_eq_iff_eq_neg.mpr h).symm
  have hfνμ : ClassFunction.inner (f ν) (f μ) = 0 := by
    have h := congrArg (fun z => ClassFunction.inner z (f μ)) hχeq
    rw [ClassFunction.inner_smul_left, hμ_not_bset] at h
    rcases zero_eq_mul.mp h with h2 | h2
    · exact absurd h2 heν_ne
    · exact h2
  have hclause : ∀ x : ClassFunction ↥C.P.H0 ℂ, LamEquiv C ν x → IsIrreducibleCharacter x →
      ClassFunction.inner (f ν - f x) (f ξ - f μ) = 0 := fun x hx hxirr =>
    hf.2.1 ν x ξ μ hνirr hxirr hξirr hμirr hx hμorbit hξnotlam hnotlamsξ
  have hfν'μ : ClassFunction.inner (f ν') (f μ) ≠ 0 := by
    have h := hclause ν' hν'orbit hν'irr
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hfνξ, hfνμ, hfν'ξ] at h
    intro h0
    rw [h0] at h
    simp only [sub_zero] at h
    exact (mul_ne_zero heν_ne heξ_ne) h
  have hfν''μ : ClassFunction.inner (f ν'') (f μ) ≠ 0 := by
    have h := hclause ν'' hν''orbit hν''irr
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hfνξ, hfνμ, hfν''ξ] at h
    intro h0
    rw [h0] at h
    simp only [sub_zero] at h
    exact (mul_ne_zero heν_ne heξ_ne) h
  -- ## conclusion: `ν', ν'' ∈ 𝒮(f μ)` are two `s`-fixed members of orbit size `m`
  have hμZI : f μ ∈ ZIrr G := ((hf.1 μ hμirr) μ (Or.inl (s02c_LamEquiv_refl C μ)) μ
    (Or.inl (s02c_LamEquiv_refl C μ)) hμirr hμirr).1
  have hnormfμ1 : ClassFunction.inner (f μ) (f μ) = 1 := by
    have h := ((hf.1 μ hμirr) μ (Or.inl (s02c_LamEquiv_refl C μ)) μ
      (Or.inl (s02c_LamEquiv_refl C μ)) hμirr hμirr).2.2.1
    rw [h]; simp [hμnotfix]
  have hψpm : IsPmIrr (f μ) := isPmIrr_of_mem_ZIrr_inner_self_eq_one hμZI hnormfμ1
  have hν'ψ : ν' ∈ bset C f (f μ) := ⟨hν'irr, fun h => hfν'μ (by
    rw [ClassFunction.inner_star_comm (f μ) (f ν')] at h
    exact star_eq_zero.mp h)⟩
  have hν''ψ : ν'' ∈ bset C f (f μ) := ⟨hν''irr, fun h => hfν''μ (by
    rw [ClassFunction.inner_star_comm (f μ) (f ν'')] at h
    exact star_eq_zero.mp h)⟩
  exact l34TwoSfixedMaximal D C hDC hS3 (by omega) f hf (f μ) hψpm
    ν' hν'ψ ν'' hν''ψ (Ne.symm hν''neν') hν'fix hν''fix
    (by rw [hν'orbit_eq, h4ν, hn4]) (by rw [hν''orbit_eq, h4ν, hn4])
end Main

end Work.BG
