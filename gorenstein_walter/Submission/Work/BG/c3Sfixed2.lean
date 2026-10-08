import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.l34Exc_sfixed_four
import Submission.Work.BG.c3LamOrbitKappa
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma24
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.rem31ShapeLeaf
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.c3ExcFinal
import Submission.Work.GLUE.Defs

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The §3 hypothesis `Sec3Hyp D` from the hypotheses of Theorem C (`Work.BG.thmCSec3`). -/
theorem c3Sfixed2_sec3Hyp {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (K1 K2 : Subgroup G) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) :
    Work.GW2.C16.Sec3Hyp D :=
  (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- BG p. 210 equation (2) for `𝒮(χ₁)` of size three.  Route: Lemma 3.3 (`Work.BG.lemma33Leaf`)
and Lemma 3.4 (`Work.BG.lemma34Leaf`) with `κ ∈ bset` and `|Λκ| = D.n` (from `IsKappa`:
`κ` is linear with `S₀ ≤ ker κ`, so `|Λκ| = |Λ| = |H₀ : U| = D.n`, `rem31IndexUin`).
Do NOT use `Work.BG.c3Bbot` / `thmCHyps_absurd`: that route is circular (it *is* Theorem C). -/
theorem c3Sfixed2 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2)
    (hSimp : IsSimpleGroup G) (hn4 : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ)
    (χ₁ : ClassFunction G ℂ) (hχ₁ : Work.BG.IsPmIrr χ₁)
    (hinner : ClassFunction.inner χ₁ (f κ) = 1)
    (h3 : (Work.GW2.C16.bset C f χ₁).ncard = 3) :
    ∀ ν ∈ Work.GW2.C16.bset C f χ₁, ν ≠ κ →
      Work.BG.sconj C ν = ν ∧ (Work.BG.lamOrbit C ν).ncard ≠ D.n := by
  classical
  have hS3 : Work.GW2.C16.Sec3Hyp D := c3Sfixed2_sec3Hyp D K1 K2 hHyps
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter (G := ↥C.P.H0)
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- `κ` lies in `𝒮(χ₁)`, is `s`-fixed, and its orbit has size `D.n`
  have hκfix : Work.BG.sconj C κ = κ := hκ.2.2.1
  have hκt : κ C.t = 1 := hκ.2.2.2.1 C.t (by rw [hComp.t_eq]; exact D.t_mem)
  have hκorb : (Work.BG.lamOrbit C κ).ncard = D.n :=
    c3LamOrbitKappa D C hComp κ hκ.2.2.2.1
  have hκmem : κ ∈ Work.GW2.C16.bset C f χ₁ := ⟨hκ.1, by rw [hinner]; exact one_ne_zero⟩
  intro ν hν hne
  by_cases hfix : Work.BG.sconj C ν = ν
  · -- `s`-fixed `ν`: Lemma 3.3 rules out `|Λν| = D.n`
    refine ⟨hfix, fun horb => ?_⟩
    obtain ⟨h2, -, -⟩ := lemma33Leaf D C hComp hS3 f hf χ₁ hχ₁ ν hν κ hκmem hne
      hfix hκfix horb hκorb
    omega
  · -- `ν` is not `s`-fixed: derive a contradiction
    exfalso
    -- ## `𝒮(χ₁) = {κ, ν, ν^s}`
    have hνs_mem : Work.BG.sconj C ν ∈ Work.GW2.C16.bset C f χ₁ :=
      ((bset_orbit_struct C f hf χ₁ hχ₁).1 ν hν).1
    have hκneνs : κ ≠ Work.BG.sconj C ν := by
      intro h
      have h1 : Work.BG.sconj C κ = Work.BG.sconj C (Work.BG.sconj C ν) := by rw [← h]
      rw [s02c_sconj_involutive, hκfix] at h1
      exact hne h1.symm
    have hνneνs : ν ≠ Work.BG.sconj C ν := fun h => hfix h.symm
    have hsub3 : ({κ, ν, Work.BG.sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆
        Work.GW2.C16.bset C f χ₁ := by
      intro η hη
      rcases (by simpa using hη : η = κ ∨ η = ν ∨ η = Work.BG.sconj C ν) with rfl | rfl | rfl
      · exact hκmem
      · exact hν
      · exact hνs_mem
    have hcard3 : ({κ, ν, Work.BG.sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨Ne.symm hne, hκneνs⟩) (Set.toFinite _),
          Set.ncard_insert_of_notMem (by simpa using hνneνs) (Set.toFinite _),
          Set.ncard_singleton]
    have hset : Work.GW2.C16.bset C f χ₁ = {κ, ν, Work.BG.sconj C ν} :=
      (Set.eq_of_subset_of_ncard_le hsub3 (by rw [hcard3]; exact le_of_eq h3)
        (s02_bset_finite C f χ₁)).symm
    have hfin2 : ({ν, Work.BG.sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
      Set.toFinite _
    have hnot1 : κ ∉ ({ν, Work.BG.sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hne, hκneνs⟩
    have hnot2 : ν ∉ ({Work.BG.sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simpa using hνneνs
    have hG := (hf.1 ν hν.1) ν (Or.inl (s02c_LamEquiv_refl C ν)) ν
      (Or.inl (s02c_LamEquiv_refl C ν)) hν.1 hν.1
    have hfνfix : f (Work.BG.sconj C ν) = f ν := hG.2.1
    -- ## case split on the coherence clause (vi)
    by_cases hexc : (Work.BG.lamOrbit C ν).ncard = 4 ∧
        Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν
    · -- ## the exceptional configuration
      by_cases hdisj : Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨
          (Work.BG.lamOrbit C ν).ncard = D.n
      · -- `|Λν| = D.n = 4`: `l34Exc_sfixed_four` with `ξ = κ`
        have hνorbit : Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν := by
          rw [← hexc.2]
          exact ⟨ν, mem_lamOrbit_self C ν, rfl⟩
        have h4eq : (Work.BG.lamOrbit C ν).ncard = D.n :=
          hdisj.resolve_left (fun hA => hA hνorbit)
        have hD4 : D.n = 4 := by rw [← h4eq, hexc.1]
        have hκ4 : (Work.BG.lamOrbit C κ).ncard = 4 := by rw [hκorb, hD4]
        exact l34Exc_sfixed_four D C hComp hS3 f hf χ₁ hχ₁ ν hν hfix hdisj hexc.1 hexc.2
          κ hκmem (Ne.symm hne) hκneνs hκfix hκ4
      · -- `|Λν| ≠ D.n`: the configuration handled by `Work.BG.c3ExcLarge`
        have hνorbit : Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν := by
          by_contra h
          exact hdisj (Or.inl h)
        have hne4 : (Work.BG.lamOrbit C ν).ncard ≠ D.n := by
          intro h
          exact hdisj (Or.inr h)
        exact c3ExcFinal D C K1 K2 hComp hHyps hSimp hn4 f hf κ hκ χ₁ hχ₁ hinner
          ν hν hne hfix hνorbit hexc.1 hne4
    · -- ## clause (vi) applies: `f ν (t) = 2ν(t)`, against `f ν = ±χ₁` and Lemma 2.4
      have hvi : f ν (C.t : G) = 2 * ν C.t := hG.2.2.2.2.2 hfix hexc
      have hZI : f ν ∈ ZIrr G := hG.1
      have hnorm : ClassFunction.inner (f ν) (f ν) = 1 := by
        rw [hG.2.2.1]; simp [hfix]
      have hpm : f ν = χ₁ ∨ f ν = -χ₁ :=
        l34_eq_pm_of_inner_ne_zero hZI hnorm hχ₁ hν.2
      have hself : ClassFunction.inner χ₁ χ₁ = 1 := l34_inner_self_pmIrr hχ₁
      -- Lemma 2.4 at `t`, expanded over `𝒮(χ₁) = {κ, ν, ν^s}`
      have hL24 := (lemma24 C f hf χ₁ hχ₁).2.1 C.t C.t_not_mem_U
      have hval : χ₁ (C.t : G) = 1 + 2 * (ClassFunction.inner χ₁ (f ν)) * ν C.t := by
        rw [hL24, hset, finsum_mem_insert _ hnot1 hfin2,
          finsum_mem_insert _ hnot2 (Set.toFinite _), finsum_mem_singleton]
        rw [hinner, hκt, hfνfix, sconj_apply_t]
        ring
      rcases hpm with h | h
      · have he : ClassFunction.inner χ₁ (f ν) = 1 := by rw [h]; exact hself
        have h4 : (2 : ℂ) * ν C.t = 1 + 2 * ν C.t := by
          have h3' : f ν (C.t : G) = χ₁ (C.t : G) := by rw [h]
          rw [hvi, hval, he] at h3'
          linear_combination h3'
        have h5 : (1 : ℂ) + 2 * ν C.t = (0 : ℂ) + 2 * ν C.t := by
          rw [zero_add]
          exact h4.symm
        exact one_ne_zero (add_right_cancel h5)
      · have he : ClassFunction.inner χ₁ (f ν) = -1 := by
          rw [h, ClassFunction.inner_neg_right, hself]
        have h4 : (2 : ℂ) * ν C.t = -1 + 2 * ν C.t := by
          have h3' : f ν (C.t : G) = -(χ₁ (C.t : G)) := by
            rw [h]
            simp
          rw [hvi, hval, he] at h3'
          linear_combination h3'
        have h5 : (0 : ℂ) + 2 * ν C.t = (-1 : ℂ) + 2 * ν C.t := by
          rw [zero_add]
          exact h4
        have h6 : (1 : ℂ) = 0 := neg_eq_zero.mp (add_right_cancel h5).symm
        exact one_ne_zero h6

end Work.BG
