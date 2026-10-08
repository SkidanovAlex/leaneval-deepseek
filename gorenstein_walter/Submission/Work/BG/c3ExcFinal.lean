import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma24
import Submission.Work.BG.rem31ShapeLeaf
import Submission.Work.BG.c3LamOrbitKappa
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.l34Exc_sfixed_four
import Submission.Work.BG.Core24
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.c3SsumReGTOne
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.cef_Ssum_eq
import Submission.Work.BG.cef_sconj_lamCF_mul_ne

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## The pairing identity `(f κ, f ν') = (f κ, f ν)` for `ν' ∈ Λν` -/

private theorem cef_fk_pairing (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Compat D C) (hS3 : Sec3Hyp D) (hn4 : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκirr : IsIrreducibleCharacter κ) (hκfix : sconj C κ = κ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {ν ν' : ClassFunction ↥C.P.H0 ℂ} (hνirr : IsIrreducibleCharacter ν)
    (hν'irr : IsIrreducibleCharacter ν') (hν'lam : LamEquiv C ν ν')
    (hκν : ¬ LamEquiv C κ ν) (hκν' : ¬ LamEquiv C κ ν') :
    ClassFunction.inner (f κ) (f ν') = ClassFunction.inner (f κ) (f ν) := by
  obtain ⟨β, hβt, -⟩ := exists_lamCF_t_neg_one_sconj_ne D C hComp hn4
  set κ₃ : ClassFunction ↥C.P.H0 ℂ := lamCF C β * κ with hκ₃def
  have hκ₃irr : IsIrreducibleCharacter κ₃ := lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hκ₃lam : LamEquiv C κ κ₃ := ⟨β, rfl⟩
  have hκ₃sconj : sconj C κ₃ ≠ κ₃ :=
    cef_sconj_lamCF_mul_ne D C hComp hn4 κ hκS0 hκfix β hβt
  have hκ₃orb : (lamOrbit C κ₃).ncard = D.n := by
    rw [← lamOrbit_eq_of_lamEquiv hκ₃lam]; exact c3LamOrbitKappa D C hComp κ hκS0
  obtain ⟨-, -, hbs⟩ :=
    Work.GW2.C24.bset_kappa3 D C (lemma34Leaf D C) hComp hS3 f hf κ₃ hκ₃irr hκ₃sconj hκ₃orb
  have horth : ∀ {η : ClassFunction ↥C.P.H0 ℂ}, IsIrreducibleCharacter η →
      (¬ LamEquiv C κ η) → ClassFunction.inner (f κ₃) (f η) = 0 := by
    intro η hη hκη
    by_contra hne
    have hmem : η ∈ bset C f (f κ₃) := ⟨hη, hne⟩
    rw [hbs, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hκη (by rw [h]; exact hκ₃lam)
    · exact hκη (by rw [h, sconjLam C β κ, hκfix]; exact ⟨β⁻¹, rfl⟩)
  have h3ν : ClassFunction.inner (f κ₃) (f ν) = 0 := horth hνirr hκν
  have h3ν' : ClassFunction.inner (f κ₃) (f ν') = 0 := horth hν'irr hκν'
  have hIV := hf.2.1 κ κ₃ ν' ν hκirr hκ₃irr hν'irr hνirr hκ₃lam
    (s02c_LamEquiv_symm C hν'lam) hκν' (by rw [hκfix]; exact hκν')
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, h3ν', h3ν] at hIV
  simp only [sub_zero] at hIV
  exact sub_eq_zero.mp hIV

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **The excluded case of BG p. 210 equation (2), stated with the hypotheses of Theorem C.**

`χ ∈ ±Irr(G)`; `κ = κ₁` is an admissible linear character (`IsKappa`) with `(χ, κ̃) = 1`;
`𝒮(χ) = bset C f χ` contains `ν ≠ κ` which is not `s`-fixed, whose `Λ`-orbit is `s`-stable
(`ν^s ∈ Λν`, the exception of coherence clause (vi)) of size `|Λν| = 4` with `|Λν| ≠ D.n`.
`hHyps` are the hypotheses of Theorem C, `G` is simple, `4 ≤ D.n`. Then `False`.

This is the single case of `Work.BG.c3Sfixed2` (BG p. 210, (2)) that
`Work.BG.lemma33Leaf` (needs *two* `s`-fixed members of `𝒮(χ)` of orbit size `D.n`, here only
`κ` is `s`-fixed), `Work.BG.lemma34Leaf` (its hypothesis `ν^s ∉ Λν ∨ |Λν| = D.n` is false here)
and coherence clause (vi) (whose exception `|Λν| = 4 ∧ (Λν)^s = Λν` holds, its conclusion being
in fact false here) do not cover; Remark 3.1 (`rem31ShapeLeaf`) forces `D.n = 8`.

This file must NOT import `Submission.Work.BG.c3Sfixed2` (the caller imports this one);
`Sec3Hyp D` should be obtained directly as `(Work.BG.thmCSec3 G D K1 K2 ...).1`.
Route: the Theorem C hypotheses must be used: the Frobenius/arithmetic chain
(`Work.BW.c3Bounds`, `Work.BW.c3Kdiv`, `Work.BW.frobeniusCardDvd`, `Work.BW.c3Arith`), and
Lemma 3.6 in the form `Work.GW2.C24.lemma36_thmC`.  Note `f κ = χ + ψ` with `ψ ∈ ±Irr`, and the
same analysis applied to `ψ` produces a second `s`-conjugate pair `η, η^s` — the substitute for
the `δ₁, δ₂` of BG p. 211.  Do NOT use `Work.BG.thmCHyps_absurd`/`c3Bbot`/`c3NotThree`: circular
(that route merely assumes Theorem C).

Proof actually formalised here (no arithmetic input of Theorem C beyond `thmCSec3`): with
`ψ := f κ - χ` the second signed irreducible constituent of `κ̃ = f κ`, coherence clause (iv)
applied to `(κ, κ₃)` with `κ₃ = λ_βκ` (`λ_β(t) = -1`, `Work.GW2.C24.bset_kappa3`) shows that
the two `s`-fixed members `ν', ν''` of `Λν` (Lemma 2.1, `Work.BG.s02_lemma21`; `|Λν| = 4`) lie
in `𝒮(ψ)`, so `𝒮(ψ) = {κ, ν', ν''}` (Theorem 3.2).  The correction term of Theorem 3.2's
counting identity is then `Ssum C f ψ = 1/D.n + 1/4 + 1/4 ≤ 3/4 < 1`, which contradicts
`Work.BG.c3SsumReGTOne` (`|𝒮| = 3` forces `1 < Ssum`). -/
theorem c3ExcFinal {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2)
    (hSimp : IsSimpleGroup G) (hn4 : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    (hinner : ClassFunction.inner χ (f κ) = 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ Work.GW2.C16.bset C f χ) (hνκ : ν ≠ κ)
    (hνne : Work.BG.sconj C ν ≠ ν)
    (hνorbit : Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (hν4 : (Work.BG.lamOrbit C ν).ncard = 4)
    (hνne4 : (Work.BG.lamOrbit C ν).ncard ≠ D.n) : False := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter (G := ↥C.P.H0)
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- ## 0. the §3 hypothesis, from the hypotheses of Theorem C
  have hS3 : Work.GW2.C16.Sec3Hyp D :=
    (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1
  -- ## 1. data on `κ`
  obtain ⟨hκirr, hκ1, hκfix, hκS0, hκne1⟩ := hκ
  have hκorb : (Work.BG.lamOrbit C κ).ncard = D.n := c3LamOrbitKappa D C hComp κ hκS0
  -- ## 2. the companion `ψ := f κ - χ` of `χ` in `κ̃ = f κ`
  have hZfκ : f κ ∈ ZIrr G := by
    have hkey : κ ∈ orbitKey C κ := Or.inl (s02c_LamEquiv_refl C κ)
    exact ((hf.1 κ hκirr) κ hkey κ hkey hκirr hκirr).1
  have hnormfκ : ClassFunction.inner (f κ) (f κ) = 2 := by
    have hkey : κ ∈ orbitKey C κ := Or.inl (s02c_LamEquiv_refl C κ)
    have h := ((hf.1 κ hκirr) κ hkey κ hkey hκirr hκirr).2.2.1
    rw [h]; simp [hκfix]
  have hχself : ClassFunction.inner χ χ = 1 := IsPmIrr.inner_self hχ
  have hψZI : f κ - χ ∈ ZIrr G := Submodule.sub_mem _ hZfκ (mem_ZIrr_of_isPmIrr hχ)
  have hfκχ : ClassFunction.inner (f κ) χ = 1 := by
    rw [ClassFunction.inner_star_comm, hinner, star_one]
  have hψnorm : ClassFunction.inner (f κ - χ) (f κ - χ) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hnormfκ, hfκχ, hinner, hχself]
    norm_num
  have hψpm : IsPmIrr (f κ - χ) := isPmIrr_of_mem_ZIrr_inner_self_eq_one hψZI hψnorm
  set ψ : ClassFunction G ℂ := f κ - χ with hψdef
  have hψpm' : IsPmIrr ψ := hψpm
  have hfκdec : f κ = χ + ψ := by rw [hψdef]; abel
  have hψχ : ClassFunction.inner ψ χ = 0 := by
    rw [hψdef, ClassFunction.inner_sub_left, hfκχ, hχself]
    ring
  have hψfκ : ClassFunction.inner ψ (f κ) = 1 := by
    rw [hfκdec, ClassFunction.inner_add_right, hψχ, hψnorm]
    norm_num
  -- ## 3. the two `s`-fixed members `ν', ν''` of `Λν`
  have hνirr : IsIrreducibleCharacter ν := hν.1
  have hνne' : ν ≠ Work.BG.sconj C ν := fun h => hνne h.symm
  have hstab : Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν := by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) ν]
    exact (lamOrbit_eq_of_lamEquiv hνorbit).symm
  have h2sf : ({χ' ∈ Work.BG.lamOrbit C ν | Work.BG.sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 := ((s02_lemma21 C) ν hνirr).2 hstab
  obtain ⟨ν', ν'', hν'neν'', hset⟩ := Set.ncard_eq_two.mp h2sf
  have hν'fix : Work.BG.sconj C ν' = ν' := by
    have h : ν' ∈ ({χ' ∈ Work.BG.lamOrbit C ν | Work.BG.sconj C χ' = χ'} :
        Set (ClassFunction ↥C.P.H0 ℂ)) := by rw [hset]; exact Set.mem_insert _ _
    exact h.2
  have hν''fix : Work.BG.sconj C ν'' = ν'' := by
    have h : ν'' ∈ ({χ' ∈ Work.BG.lamOrbit C ν | Work.BG.sconj C χ' = χ'} :
        Set (ClassFunction ↥C.P.H0 ℂ)) := by
      rw [hset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact h.2
  have hν'mem : ν' ∈ Work.BG.lamOrbit C ν := by
    have h : ν' ∈ ({χ' ∈ Work.BG.lamOrbit C ν | Work.BG.sconj C χ' = χ'} :
        Set (ClassFunction ↥C.P.H0 ℂ)) := by rw [hset]; exact Set.mem_insert _ _
    exact h.1
  have hν''mem : ν'' ∈ Work.BG.lamOrbit C ν := by
    have h : ν'' ∈ ({χ' ∈ Work.BG.lamOrbit C ν | Work.BG.sconj C χ' = χ'} :
        Set (ClassFunction ↥C.P.H0 ℂ)) := by
      rw [hset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact h.1
  have hν'irr : IsIrreducibleCharacter ν' := irreducible_of_mem_lamOrbit C hν'mem hνirr
  have hν''irr : IsIrreducibleCharacter ν'' := irreducible_of_mem_lamOrbit C hν''mem hνirr
  have hν'orbit : (Work.BG.lamOrbit C ν').ncard = 4 := by
    rw [← lamOrbit_eq_of_lamEquiv hν'mem]; exact hν4
  have hν''orbit : (Work.BG.lamOrbit C ν'').ncard = 4 := by
    rw [← lamOrbit_eq_of_lamEquiv hν''mem]; exact hν4
  have hν'neν : ν' ≠ ν := by
    intro h
    rw [h] at hν'fix
    exact hνne hν'fix
  have hν''neν : ν'' ≠ ν := by
    intro h
    rw [h] at hν''fix
    exact hνne hν''fix
  -- ## 4. `κ` is not `Λ`-equivalent to `ν`, `ν'`, `ν''`
  have h4neDn : (4 : ℕ) ≠ D.n := fun h => hνne4 (by rw [hν4]; exact h)
  have hκν : ¬ LamEquiv C κ ν := by
    intro hl
    have h1 : (Work.BG.lamOrbit C κ).ncard = (Work.BG.lamOrbit C ν).ncard := by
      rw [lamOrbit_eq_of_lamEquiv hl]
    rw [hκorb, hν4] at h1
    exact h4neDn h1.symm
  have hκν' : ¬ LamEquiv C κ ν' := by
    intro hl
    have h1 : (Work.BG.lamOrbit C κ).ncard = (Work.BG.lamOrbit C ν').ncard := by
      rw [lamOrbit_eq_of_lamEquiv hl]
    rw [hκorb, hν'orbit] at h1
    exact h4neDn h1.symm
  have hκν'' : ¬ LamEquiv C κ ν'' := by
    intro hl
    have h1 : (Work.BG.lamOrbit C κ).ncard = (Work.BG.lamOrbit C ν'').ncard := by
      rw [lamOrbit_eq_of_lamEquiv hl]
    rw [hκorb, hν''orbit] at h1
    exact h4neDn h1.symm
  -- ## 5. the pairing identity for the two `s`-fixed members of `Λν`
  have hEqν' : ClassFunction.inner (f κ) (f ν') = ClassFunction.inner (f κ) (f ν) :=
    cef_fk_pairing D C hComp hS3 hn4 f hf κ hκirr hκfix hκS0 hνirr hν'irr hν'mem hκν hκν'
  have hEqν'' : ClassFunction.inner (f κ) (f ν'') = ClassFunction.inner (f κ) (f ν) :=
    cef_fk_pairing D C hComp hS3 hn4 f hf κ hκirr hκfix hκS0 hνirr hν''irr hν''mem hκν hκν''
  -- ## 6. `f ν = ± χ`
  have hνkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  obtain ⟨hZfν, -, hnormfνraw, -, -, -⟩ :=
    (hf.1 ν hνirr) ν hνkey ν hνkey hνirr hνirr
  have hnormfν : ClassFunction.inner (f ν) (f ν) = 1 := by rw [hnormfνraw]; simp [hνne]
  have hfνeq : f ν = χ ∨ f ν = -χ := l34_eq_pm_of_inner_ne_zero hZfν hnormfν hχ hν.2
  -- ## 7. `ν'` and `ν''` lie in `𝒮(ψ)`
  have hψfν : ClassFunction.inner ψ (f ν) = 0 := by
    rcases hfνeq with h | h
    · rw [h]; exact hψχ
    · rw [h, ClassFunction.inner_neg_right, hψχ, neg_zero]
  have hχfν' : ClassFunction.inner χ (f ν') = 0 := by
    by_contra h
    have hmem : ν' ∈ Work.GW2.C16.bset C f χ := ⟨hν'irr, h⟩
    have h := (bset_orbit_struct C f hf χ hχ).2 ν hν ν' hmem hν'mem hν'neν
    rw [h, s02c_sconj_involutive] at hν'fix
    exact hνne hν'fix.symm
  have hχfν'' : ClassFunction.inner χ (f ν'') = 0 := by
    by_contra h
    have hmem : ν'' ∈ Work.GW2.C16.bset C f χ := ⟨hν''irr, h⟩
    have h := (bset_orbit_struct C f hf χ hχ).2 ν hν ν'' hmem hν''mem hν''neν
    rw [h, s02c_sconj_involutive] at hν''fix
    exact hνne hν''fix.symm
  have hψfν' : ClassFunction.inner ψ (f ν') ≠ 0 := by
    have h1 : ClassFunction.inner (f κ) (f ν') =
        ClassFunction.inner χ (f ν') + ClassFunction.inner ψ (f ν') := by
      rw [hfκdec, ClassFunction.inner_add_left]
    rw [hχfν', zero_add] at h1
    have h2 : ClassFunction.inner (f κ) (f ν) =
        ClassFunction.inner χ (f ν) + ClassFunction.inner ψ (f ν) := by
      rw [hfκdec, ClassFunction.inner_add_left]
    rw [hψfν, add_zero] at h2
    rw [← h1, hEqν', h2]
    exact hν.2
  have hψfν'' : ClassFunction.inner ψ (f ν'') ≠ 0 := by
    have h1 : ClassFunction.inner (f κ) (f ν'') =
        ClassFunction.inner χ (f ν'') + ClassFunction.inner ψ (f ν'') := by
      rw [hfκdec, ClassFunction.inner_add_left]
    rw [hχfν'', zero_add] at h1
    have h2 : ClassFunction.inner (f κ) (f ν) =
        ClassFunction.inner χ (f ν) + ClassFunction.inner ψ (f ν) := by
      rw [hfκdec, ClassFunction.inner_add_left]
    rw [hψfν, add_zero] at h2
    rw [← h1, hEqν'', h2]
    exact hν.2
  have hκmemψ : κ ∈ Work.GW2.C16.bset C f ψ := ⟨hκirr, by rw [hψfκ]; exact one_ne_zero⟩
  have hν'memψ : ν' ∈ Work.GW2.C16.bset C f ψ := ⟨hν'irr, hψfν'⟩
  have hν''memψ : ν'' ∈ Work.GW2.C16.bset C f ψ := ⟨hν''irr, hψfν''⟩
  have hκneν' : κ ≠ ν' := fun h => hκν' (by rw [← h]; exact s02c_LamEquiv_refl C κ)
  have hκneν'' : κ ≠ ν'' := fun h => hκν'' (by rw [← h]; exact s02c_LamEquiv_refl C κ)
  -- ## 8. `𝒮(ψ) = {κ, ν', ν''}`
  have hle3ψ : (Work.GW2.C16.bset C f ψ).ncard ≤ 3 := thm32 D C hComp hS3 f hf ψ hψpm'
  have hsubψ : ({κ, ν', ν''} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ Work.GW2.C16.bset C f ψ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl
    · exact hκmemψ
    · exact hν'memψ
    · exact hν''memψ
  have hcard3ψ : ({κ, ν', ν''} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hκneν', hκneν''⟩) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simpa using hν'neν'') (Set.toFinite _),
      Set.ncard_singleton]
  have h3ψ : (Work.GW2.C16.bset C f ψ).ncard = 3 := by
    have h := Set.ncard_le_ncard hsubψ (s02_bset_finite C f ψ)
    omega
  -- ## 9. the correction term for `ψ` is `< 1`, contradicting Theorem 3.2
  have hSsumψ : Work.BG.Ssum C f ψ = ((((1 : ℝ) / (D.n : ℝ) + 1 / 4 + 1 / 4) : ℝ) : ℂ) :=
    cef_Ssum_eq D C f hf ψ hψpm' ⟨κ, hκirr⟩ ⟨ν', hν'irr⟩ ⟨ν'', hν''irr⟩
      hκmemψ hν'memψ hν''memψ
      (fun h => hκneν' (Subtype.ext_iff.mp h)) (fun h => hκneν'' (Subtype.ext_iff.mp h))
      (fun h => hν'neν'' (Subtype.ext_iff.mp h))
      hκfix hν'fix hν''fix hκorb hν'orbit hν''orbit (by omega)
  have hgt := c3SsumReGTOne D C hComp hS3 f hf ψ hψpm' h3ψ
  rw [hSsumψ, Complex.ofReal_re] at hgt
  have hDn : (4 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn4
  have hle : (1 : ℝ) / (D.n : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hDn
  linarith

end Work.BG
