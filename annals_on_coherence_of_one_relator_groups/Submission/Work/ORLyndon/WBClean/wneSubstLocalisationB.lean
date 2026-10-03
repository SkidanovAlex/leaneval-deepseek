import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.magRew_block_subword_mmBeta
import Submission.Work.OROneRel.mrslDefs
import Submission.Work.OROneRel.mrslExp
import Submission.Work.ORLyndon.WBClean.mrslAux
import Submission.Work.OROneRel.mrsl_expAux_mk
import Submission.Work.OROneRel.mrsl_substList_mk
import Submission.Work.OROneRel.mrsl_rewrite_substList_isReduced
import Submission.Work.OROneRel.mrsl_expAux_isReduced
import Submission.Work.OROneRel.mrsl_expAux_cyclicReduction
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.relatorNorm_mmW_letterCountNot


/-!
# Import-hygiene copy of `Submission.Work.OROneRel.wneSubstLocalisationB`

**This file is a verbatim copy** of `Submission/Work/OROneRel/wneSubstLocalisationB.lean`, moved into the *nested*
namespace `Work.OROneRel.WBClean` (so that inside it every unqualified name still resolves through
the parent namespace to the untouched `Work.OROneRel` development).  The reason is *import hygiene*:
the original reaches `Submission.Work.OROneRel.mrslAux`, which redeclares the public theorem
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` already declared by
`Submission.Work.OROneRel.magnus_step_root` — a dependency of
`Submission.Work.ORLyndon.epsNeZeroDescent` — so no module can import both cones.  Here the
duplicated theorem is renamed `Work.OROneRel.WBClean.toWord_pow_of_isCyclicallyReduced_wbc` and the
imports inside the copied chain are redirected; nothing else is changed.

Consumer: `Submission/Work/ORLyndon/occTerm_distinct_clean.lean`.  Everything in
`Submission/Work/ORLyndon/WBClean/` (and that file) can be deleted as soon as the duplicate
declaration is removed on the `OROneRel` side.
-/
namespace Work.OROneRel

namespace WBClean

universe u

variable {β : Type u}

/-! ### Counting the letters different from `t` on the block word -/

/-- The letters of `runLetters t n` are all equal to `t`, so `nt` does not count them. -/
theorem wne_nt_runLetters (t : β) (n : ℤ) : Work.OROneRel.nt t (runLetters t n) = 0 := by
  classical
  rw [Work.OROneRel.nt_eq_zero_iff]
  intro b hb
  rw [runLetters] at hb
  rw [List.eq_of_mem_replicate hb]

/-- The blocks of `substList t x p q` contribute a letter different from `t` exactly for the letters
of the original word that are different from `t`. -/
theorem wne_nt_substList (t x : β) (p q : ℤ) (L : List (β × Bool)) :
    Work.OROneRel.nt t (substList t x p q L) = Work.OROneRel.nt t L := by
  classical
  induction L with
  | nil => rw [substList_nil]
  | cons c L ih =>
    have hcons : Work.OROneRel.nt t (c :: L) =
        Work.OROneRel.nt t [c] + Work.OROneRel.nt t L := by
      rw [show (c :: L) = [c] ++ L from rfl, Work.OROneRel.nt_append]
    rw [substList_cons, Work.OROneRel.nt_append, ih, hcons]
    by_cases h1 : c.1 = t
    · rw [blkLetter_of_eq h1, wne_nt_runLetters, Work.OROneRel.nt_singleton, if_pos h1]
    · rw [Work.OROneRel.nt_singleton, if_neg h1]
      by_cases h2 : c.1 = x
      · rw [blkLetter_of_ne_of_eq h1 h2]
        by_cases hc : c.2
        · rw [if_pos hc, Work.OROneRel.nt_append, wne_nt_runLetters,
            Work.OROneRel.nt_singleton, if_neg h1]
        · rw [if_neg hc, Work.OROneRel.nt_append, wne_nt_runLetters,
            Work.OROneRel.nt_singleton, if_neg h1]
      · rw [blkLetter_of_ne_of_ne h1 h2, Work.OROneRel.nt_singleton, if_neg h1]

/-- The expansion of a decorated word has one letter different from `t` for each of its letters. -/
theorem wne_nt_expAux (t : β) (a : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    Work.OROneRel.nt t (expAux t a D) = D.length := by
  classical
  induction D generalizing a with
  | nil => rw [expAux_nil, wne_nt_runLetters, List.length_nil]
  | cons p rest ih =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [expAux_cons, Work.OROneRel.nt_append, wne_nt_runLetters, Work.OROneRel.nt_cons, ih,
      if_neg c.2, List.length_cons]
    omega

/-- **Localisation of the Magnus rewriting of a substituted subword** (the decorated transport),
in the form consumed by the no-zero-exponent-sum case of Weinbaum's theorem.

This is `Work.OROneRel.magRew_subst_localisation` with two additional conclusions: the word `U` has
as many letters as the *arc* `w` has letters different from `t`, and the Magnus rewriting `mmW t v` of
the cyclically reduced conjugate `v` of `subst t x p q R` has `letterCountNot t R` letters.

Both follow from the internal data of the proof: the conjugator is a power of `t` (so the cyclic
reduction of `subst t x p q R` strips only `t`-letters), and free reduction of the substituted word
does not delete any letter different from `t` (this is the identity `rewrite t N = rewrite t
(toWord (subst t x p q w))` established in the proof, together with `nt (substList t x p q L) = nt
L`, i.e. the blocks of `substList` contribute a non-`t` letter exactly for the letters of `L` that are
not `t`). -/
theorem wneSubstLocalisationB {β : Type u} (R : FreeGroup β) {x t : β} (p q : ℤ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R) (hxt : x ≠ t) (hp : p ≠ 0) (hq : q ≠ 0)
    (hwt : Work.OROneRel.sigma t (Work.OROneRel.subst t x p q R) = 1)
    {w : FreeGroup β} {k : ℕ} (hsub : Work.OROneRel.IsSubwordOf w (R ^ k)) :
    ∃ (c v : FreeGroup β) (j : ℤ) (u : FreeGroup (Work.OROneRel.mmBeta t v)),
      v = c * Work.OROneRel.subst t x p q R * c⁻¹ ∧
      Work.OROneRel.IsCyclicallyReducedRelator v ∧
      Work.OROneRel.IsSubwordOf u ((Work.OROneRel.mmW t v) ^ (k + 1)) ∧
      FreeGroup.map (fun z : Work.OROneRel.mmBeta t v =>
          ((z.1.1, z.1.2) : ({y : β // y ≠ t} × ℤ))) u
        = magShiftAut t j (Work.OROneRel.magRewRel t (c * Work.OROneRel.subst t x p q w * c⁻¹)) ∧
      (FreeGroup.toWord u).length = Work.OROneRel.letterCountNot t w ∧
      Work.OROneRel.relatorNorm (Work.OROneRel.mmW t v) = Work.OROneRel.letterCountNot t R := by
  classical
  obtain ⟨L₁, L₂, hL12⟩ := hsub
  -- ### (0) the words of the relator and of the substituted relator
  set Rw : List (β × Bool) := FreeGroup.toWord R with hRw
  have hRred : FreeGroup.IsReduced Rw := FreeGroup.isReduced_toWord
  have hRcyc : FreeGroup.IsCyclicallyReduced Rw := hcyc
  set M : List (β × Bool) := substList t x p q Rw with hM
  have hmkM : FreeGroup.mk M = subst t x p q R := by
    rw [hM, mrsl_substList_mk, hRw, FreeGroup.mk_toWord]
  -- ### (1) the exponent sum in `t` of the substituted word vanishes
  have hM0 : sigmaList t M = 0 := by
    have h2 : sigma t (subst t x p q R) = Multiplicative.ofAdd (sigmaList t M) := by
      rw [← hmkM]; exact sigma_mk t M
    rw [h2] at hwt
    exact ofAdd_eq_one.mp hwt
  -- ### (2) the decoration of the substituted relator
  set D : List (MMAlpha t × Bool) := rewrite t M with hD
  have hDred : FreeGroup.IsReduced D := by
    rw [hD, hM]; exact mrsl_rewrite_substList_isReduced t x p q hp hq hRred
  have hDcyc : FreeGroup.IsCyclicallyReduced D := by
    have hMM : D ++ D = rewrite t (M ++ M) := by
      simp only [hD, rewrite, rewriteAux_append, hM0, add_zero]
    rw [isCyclicallyReduced_iff_isReduced_append_self, hMM]
    have h2 : M ++ M = substList t x p q (Rw ++ Rw) := by rw [substList_append, hM]
    rw [h2]
    exact mrsl_rewrite_substList_isReduced t x p q hp hq
      (isCyclicallyReduced_iff_isReduced_append_self.mp hRcyc)
  -- ### (3) the cyclic reduction of the substituted relator
  obtain ⟨m, V, hWV, hVcyc⟩ := mrsl_expAux_cyclicReduction t hDred hDcyc
  -- ### (4) the substituted word is the expansion of `D`
  have hWexp : expAux t 0 D = FreeGroup.toWord (FreeGroup.mk M) := by
    have hred1 : FreeGroup.IsReduced (expAux t 0 D) := mrsl_expAux_isReduced t 0 hDred
    have hred2 : FreeGroup.IsReduced (FreeGroup.toWord (FreeGroup.mk M)) :=
      FreeGroup.isReduced_toWord
    have hmk : FreeGroup.mk (expAux t 0 D) = FreeGroup.mk (FreeGroup.toWord (FreeGroup.mk M)) := by
      rw [FreeGroup.mk_toWord, mrsl_expAux_mk, prod_expandLetter_eq_magnusMap]
      have h : magnusMap t (FreeGroup.mk D) = FreeGroup.mk M := by
        rw [hD, ← magRew_zero_eq_rewrite]
        have h1 := rho_magRew t 0 M
        rw [rho_eq_magnusMap] at h1
        rw [h1, ← sigmaList_eq_wordEps, hM0]
        simp
      rw [h]
      simp
    have hsound := FreeGroup.reduce.sound hmk
    rwa [FreeGroup.IsReduced.reduce_eq hred1, FreeGroup.IsReduced.reduce_eq hred2] at hsound
  -- ### (5) the conjugate `v` and the conjugator `c`
  set v : FreeGroup β := FreeGroup.mk V with hv
  set c : FreeGroup β := (FreeGroup.of t) ^ (-m) with hc
  have hconj : subst t x p q R = (FreeGroup.of t) ^ m * v * (FreeGroup.of t) ^ (-m) := by
    rw [← hmkM, ← FreeGroup.mk_toWord (x := FreeGroup.mk M), ← hWexp, hWV, ← FreeGroup.mul_mk,
      ← FreeGroup.mul_mk, mk_runLetters, mk_runLetters, ← hv]
  have hv_eq : v = c * subst t x p q R * c⁻¹ := by
    rw [hc, hconj]; group
  have hvcyc : IsCyclicallyReducedRelator v := by
    change FreeGroup.IsCyclicallyReduced (FreeGroup.toWord (FreeGroup.mk V))
    rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hVcyc.isReduced]
    exact hVcyc
  have hσv : sigma t v = 1 := by
    rw [hv_eq, map_mul, map_mul, map_inv, hwt]; simp
  have heps : eps t v = 0 := (eps_eq_zero_iff_sigma_eq_one t v).mpr hσv
  -- ### (6) the Magnus rewriting of `v`
  have hV_toWord : FreeGroup.toWord v = V := by
    rw [hv, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hVcyc.isReduced]
  have hmmList : mmList t v = rewrite t V := by
    rw [mmList, hV_toWord, magRew_zero_eq_rewrite]
  have hD_shift : D = mmShiftList t m (rewrite t V) := by
    have h1 : rewrite t (expAux t 0 D) = D := by
      rw [rewrite]; exact rewriteAux_expAux t 0 D
    rw [← h1, hWV, rewrite, rewriteAux_append, rewriteAux_runLetters, List.append_nil,
      rewriteAux_append, rewriteAux_runLetters, List.nil_append, sigmaList_runLetters, zero_add,
      rewriteAux_zero_add]
    rfl
  -- ### (7) the subword structure of the substituted relator
  set A : List (β × Bool) := substList t x p q L₁ with hA
  set N : List (β × Bool) := substList t x p q (FreeGroup.toWord w) with hN
  set B : List (β × Bool) := substList t x p q L₂ with hB
  have hRk : (List.replicate k Rw).flatten = L₁ ++ FreeGroup.toWord w ++ L₂ := by
    rw [← toWord_pow_of_isCyclicallyReduced_wbc hRcyc k, hRw, FreeGroup.mk_toWord]
    exact hL12
  have hMN : (List.replicate k M).flatten = A ++ (N ++ B) := by
    rw [hM, ← substList_flatten_replicate, hRk]
    simp only [substList_append, List.append_assoc]
    rw [← hA, ← hN, ← hB]
  -- ### (8) the factor of the decorated periodic word
  have hfac : rewriteAux t (sigmaList t A) N <:+: (List.replicate k D).flatten := by
    have h1 : rewrite t ((List.replicate k M).flatten) = (List.replicate k D).flatten := by
      rw [hD, rewrite, rewrite, ← rewriteAux_flatten_replicate t M hM0 k]
    rw [← h1, hMN]
    refine ⟨rewriteAux t 0 A, rewriteAux t (sigmaList t A + sigmaList t N) B, ?_⟩
    rw [rewrite, rewriteAux_append, rewriteAux_append]
    simp only [zero_add]
    rw [List.append_assoc]
  -- ### (9) the rewriting of the substituted subword is the decorated word of `ψ w`
  have hNw : FreeGroup.mk (rewrite t N) = FreeGroup.mk (rewrite t (FreeGroup.toWord (subst t x p q w))) := by
    have h1 : FreeGroup.mk N = subst t x p q w := by
      rw [hN, mrsl_substList_mk, FreeGroup.mk_toWord]
    refine (magMagnusMap_injective t) ?_
    rw [magnusMap_rewrite, magnusMap_rewrite, h1, FreeGroup.mk_toWord]
    have hσ : sigmaList t N = sigmaList t (FreeGroup.toWord (subst t x p q w)) := by
      have hA := sigma_mk t N
      have hB := sigma_mk t (FreeGroup.toWord (subst t x p q w))
      rw [h1] at hA
      rw [FreeGroup.mk_toWord] at hB
      exact Multiplicative.ofAdd.injective (hA.symm.trans hB)
    rw [hσ]
  have hNψ : rewrite t N = rewrite t (FreeGroup.toWord (subst t x p q w)) := by
    have hred1 : FreeGroup.IsReduced (rewrite t N) :=
      mrsl_rewrite_substList_isReduced t x p q hp hq FreeGroup.isReduced_toWord
    have hred2 : FreeGroup.IsReduced (rewrite t (FreeGroup.toWord (subst t x p q w))) := by
      rw [rewrite]; exact rewriteAux_isReduced t _ FreeGroup.isReduced_toWord 0
    have hsound := FreeGroup.reduce.sound hNw
    rwa [FreeGroup.IsReduced.reduce_eq hred1, FreeGroup.IsReduced.reduce_eq hred2] at hsound
  -- ### (10) the factor of the periodic decorated word of `v`
  set j : ℤ := sigmaList t A with hj
  have hinf : mmShiftList t (j - m) (rewrite t (FreeGroup.toWord (subst t x p q w))) <:+:
      (List.replicate k (mmList t v)).flatten := by
    have h1 : mmShiftList t j (rewrite t (FreeGroup.toWord (subst t x p q w))) <:+:
        (List.replicate k D).flatten := by
      rw [hj, ← hNψ, ← rewriteAux_mmShiftList t (sigmaList t A) N]
      exact hfac
    rw [hD_shift, ← hmmList] at h1
    obtain ⟨s, t', hs⟩ := h1
    refine ⟨s.map (mmShift (-m)), t'.map (mmShift (-m)), ?_⟩
    rw [← mmShiftList_shift_neg t j m, ← List.map_append, ← List.map_append, hs,
      ← mmShiftList_flatten_replicate t m (mmList t v) k]
    exact mmShiftList_neg_self t m _
  -- ### (11) the lift to the decorated alphabet of `v`
  set F : List (MMAlpha t × Bool) :=
    mmShiftList t (j - m) (rewrite t (FreeGroup.toWord (subst t x p q w))) with hF
  set lf : MMAlpha t × Bool → mmBeta t v × Bool := fun z => (mmBetaOf t v z.1, z.2) with hlf
  set Fl : List (mmBeta t v × Bool) := F.map lf with hFl
  obtain ⟨sF, tF, hsF⟩ := hinf
  have hFmem : ∀ z ∈ F, z ∈ mmList t v := by
    intro z hz
    have hz' : z ∈ (List.replicate k (mmList t v)).flatten := by
      rw [← hsF]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz)))
    obtain ⟨l, hl, hzl⟩ := List.mem_flatten.mp hz'
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hl
    exact hzl
  have hFmemD : ∀ z ∈ F, z.1 ∈ mmDecSet t v := fun z hz => mmList_mem_decSet t v (hFmem z hz)
  have hFl_inf : Fl <:+: (List.replicate k (mmWL t v)).flatten := by
    have hmap : ((List.replicate k (mmList t v)).flatten).map lf =
        (List.replicate k (mmWL t v)).flatten := by
      rw [lift_flatten_replicate]
      congr 1
    refine ⟨sF.map lf, tF.map lf, ?_⟩
    rw [hFl]
    rw [← hmap]
    rw [← hsF]
    simp only [List.map_append, List.append_assoc]
  have hFl_val : Fl.map (fun z : mmBeta t v × Bool => ((z.1.1 : MMAlpha t), z.2)) = F := by
    rw [hFl, List.map_map]
    trans F.map id
    · refine List.map_congr_left (fun p hp => ?_)
      exact Prod.ext (mmBetaOf_val t v (hFmemD p hp)) rfl
    · exact List.map_id F
  have hFl_red : FreeGroup.IsReduced Fl :=
    ((mmWL_isCyclicallyReduced t v hvcyc heps).flatten_replicate k).isReduced.infix hFl_inf
  -- ### (12) the witness
  refine ⟨c, v, j, FreeGroup.mk Fl, hv_eq, hvcyc, ?_, ?_, ?_, ?_⟩
  · -- the subword relation
    have hutw : FreeGroup.toWord (FreeGroup.mk Fl) = Fl := by
      rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hFl_red]
    have hWkw : FreeGroup.toWord (mmW t v) = mmWL t v := by
      rw [mmW, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq (mmWL_isReduced t v hvcyc heps)]
    have hpow : FreeGroup.toWord ((mmW t v) ^ (k + 1)) =
        (List.replicate (k + 1) (mmWL t v)).flatten :=
      toWord_pow_of_isCyclicallyReduced_wbc (mmWL_isCyclicallyReduced t v hvcyc heps) (k + 1)
    have hpre : (List.replicate k (mmWL t v)).flatten <:+:
        (List.replicate (k + 1) (mmWL t v)).flatten := by
      refine ⟨mmWL t v, [], ?_⟩
      rw [List.append_nil, List.replicate_succ, List.flatten_cons]
    obtain ⟨s, t', hs⟩ := hFl_inf.trans hpre
    refine ⟨s, t', ?_⟩
    rw [hutw, hpow]
    exact hs.symm
  · -- the projection
    rw [FreeGroup.map.mk]
    show FreeGroup.mk (Fl.map (fun z : mmBeta t v × Bool => ((z.1.1 : MMAlpha t), z.2))) =
      magShiftAut t j (magRewRel t (c * subst t x p q w * c⁻¹))
    rw [hFl_val, hF]
    have hc' : c * subst t x p q w * c⁻¹
        = (FreeGroup.of t) ^ (-m) * subst t x p q w * (FreeGroup.of t) ^ m := by
      rw [hc, show ((FreeGroup.of t) ^ (-m))⁻¹ = (FreeGroup.of t) ^ m from by
        rw [← zpow_neg, neg_neg]]
    rw [hc', magRewRel_conj_zpow, magShiftAut_apply_add, magRewRel]
    have hmm : magShiftAut t (j + -m)
        (FreeGroup.mk (rewrite t (FreeGroup.toWord (subst t x p q w)))) =
        FreeGroup.mk (mmShiftList t (j + -m) (rewrite t (FreeGroup.toWord (subst t x p q w)))) :=
      rfl
    rw [hmm]
    congr 1
  · -- the number of letters different from `t` of `U` is that of the arc `w`
    have hutw : FreeGroup.toWord (FreeGroup.mk Fl) = Fl := by
      rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hFl_red]
    have hNnt : Work.OROneRel.nt t N = (N.filter (fun p => decide (p.1 ≠ t))).length := rfl
    have hwnt : Work.OROneRel.nt t (FreeGroup.toWord w) = Work.OROneRel.letterCountNot t w := by
      rw [Work.OROneRel.nt_eq_countP]
      rfl
    rw [hutw, hFl, List.length_map, hF, mmShiftList_length, ← hNψ, rewrite, rewriteAux_length,
      ← hNnt, hN, wne_nt_substList, hwnt]
  · -- the norm of the Magnus rewriting of `v`
    have hrun : ∀ n : ℤ, Work.OROneRel.nt t (runLetters t n) = 0 := wne_nt_runLetters t
    have htuple : FreeGroup.toWord (Work.OROneRel.subst t x p q R) =
        runLetters t m ++ V ++ runLetters t (-m) := by
      rw [← hmkM, ← hWexp, hWV]
    have hVnt : Work.OROneRel.nt t V =
        Work.OROneRel.nt t (FreeGroup.toWord (Work.OROneRel.subst t x p q R)) := by
      rw [htuple, Work.OROneRel.nt_append, Work.OROneRel.nt_append, hrun, hrun]
      simp
    have hExp : Work.OROneRel.nt t (FreeGroup.toWord (Work.OROneRel.subst t x p q R)) = D.length := by
      rw [← hmkM, ← hWexp]
      exact wne_nt_expAux t 0 D
    have hDlen : D.length = Work.OROneRel.nt t M := by
      rw [hD, rewrite, rewriteAux_length]
      rfl
    have hMnt : Work.OROneRel.nt t M = Work.OROneRel.nt t (FreeGroup.toWord R) := by
      rw [hM, wne_nt_substList]
    have hvnt : Work.OROneRel.letterCountNot t v = Work.OROneRel.nt t V := by
      rw [show Work.OROneRel.letterCountNot t v =
          (FreeGroup.toWord v).countP (fun p => decide (p.1 ≠ t)) from rfl, hV_toWord,
        Work.OROneRel.nt_eq_countP]
    have hRnt : Work.OROneRel.nt t (FreeGroup.toWord R) = Work.OROneRel.letterCountNot t R := by
      rw [Work.OROneRel.nt_eq_countP]
      rfl
    rw [Work.OROneRel.relatorNorm_mmW_letterCountNot t v hvcyc heps, hvnt, hVnt, hExp, hDlen, hMnt,
      hRnt]

end WBClean

end Work.OROneRel
