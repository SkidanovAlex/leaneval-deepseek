/-
  WilG1/Choice/PiecesB — the `Ω`-membership of the second disjunct of `selSet`
  (the symmetry / unique-centre case), via the symmetry sets `ctrT2`, `ctrE0`, `ctrE1`.

  All pieces are first brought to a uniform format `aK + aR + 6p + 90`, so that the format
  bookkeeping of the combinations reduces to `simp only [max_self]` plus linear arithmetic.
-/
import Mathlib
import Submission.Work.WilG1.Choice.PieceDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 6. `selB` -/

theorem selB_mem {S : SOMin} {p aK aR D : ℕ} {bK bR : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    (hK : K ∈ S.Ω aK (bK.eval D) (p + 1)) (_hR : R ∈ S.Ω aR (bR.eval D) p) :
    selB K ∈ S.Ω (aK + aR + 6 * p + 110) (16 * (bK.eval D + bR.eval D) + 33) (p + 1) := by
  -- The symmetry about the value of the last coordinate.
  have hB1 : {z : Fin (p + 1) → ℝ | ∀ t : ℝ,
        (Fin.snoc (Fin.init z) (z (Fin.last p) + t) ∈ K ↔
          Fin.snoc (Fin.init z) (z (Fin.last p) - t) ∈ K)} ∈
      S.Ω (aK + aR + 6 * p + 100) (4 * (bK.eval D + bR.eval D) + 8) (p + 1) := by
    have hctr := ctr_mem (S := S) (p := p) (k := 0) hK (Fin.last p)
    have he : {y : Fin (p + 1 + 0) → ℝ | ∀ t : ℝ,
          (Fin.snoc (basePart (k := 0) y) (y (Fin.last p) + t) ∈ K ↔
            Fin.snoc (basePart (k := 0) y) (y (Fin.last p) - t) ∈ K)} =
        {y : Fin (p + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc (Fin.init y) (y (Fin.last p) + t) ∈ K ↔
            Fin.snoc (Fin.init y) (y (Fin.last p) - t) ∈ K)} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      refine forall_congr' (fun t => ?_)
      rw [basePart_self y]
    rw [he] at hctr
    refine Omega.mono hctr
      (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  -- The centre is unique.
  have hB2 : selB K ∈ S.Ω (aK + aR + 6 * p + 100)
      (12 * (bK.eval D + bR.eval D) + 25) (p + 1) := by
    -- the symmetry sets, raised to the uniform format `aK + aR + 6p + 90`
    have hTT : ctrT2 K ∈ S.Ω (aK + aR + 6 * p + 90)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono (ctr_mem (S := S) (p := p) (k := 2) hK (idxT p 2))
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hTC : ctrE0 K ∈ S.Ω (aK + aR + 6 * p + 90)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono (ctr_mem (S := S) (p := p) (k := 2) hK (idxE p 2 (0 : Fin 2)))
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hTC' : ctrE1 K ∈ S.Ω (aK + aR + 6 * p + 90)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono (ctr_mem (S := S) (p := p) (k := 2) hK (idxE p 2 (1 : Fin 2)))
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have heq : eqE (p := p) ∈ S.Ω (aK + aR + 6 * p + 90) 1 (p + 1 + 2) :=
      Omega.mono (linEq_mem (S := S) (N := p + 1 + 2) (idxE p 2 (1 : Fin 2))
        (idxE p 2 (0 : Fin 2))) (by omega) le_rfl
    -- combine: `(ctrT2 ∩ ((ctrE1)ᶜ ∪ eqE)) ∩ ctrE0`
    have hcmpl : (ctrE1 K)ᶜ ∈ S.Ω (aK + aR + 6 * p + 92)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono (S.compl hTC') (by omega) le_rfl
    have heq' : eqE (p := p) ∈ S.Ω (aK + aR + 6 * p + 92) 1 (p + 1 + 2) :=
      Omega.mono heq (by omega) le_rfl
    have hU1 : ((ctrE1 K)ᶜ ∪ eqE (p := p)) ∈ S.Ω (aK + aR + 6 * p + 92)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D + 1) (p + 1 + 2) :=
      Omega.mono (union2_mem (S := S) hcmpl heq') (by simp only [max_self]; omega) (by omega)
    have hTT' : ctrT2 K ∈ S.Ω (aK + aR + 6 * p + 92)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono hTT (by omega) le_rfl
    have hI1 : (ctrT2 K ∩ ((ctrE1 K)ᶜ ∪ eqE (p := p))) ∈ S.Ω (aK + aR + 6 * p + 93)
        (2 * (Polynomial.C 4 * bK + Polynomial.C 8).eval D + 1) (p + 1 + 2) :=
      Omega.mono (inter2_mem (S := S) hTT' hU1) (by simp only [max_self]; omega) (by omega)
    have hTC'' : ctrE0 K ∈ S.Ω (aK + aR + 6 * p + 93)
        ((Polynomial.C 4 * bK + Polynomial.C 8).eval D) (p + 1 + 2) :=
      Omega.mono hTC (by omega) le_rfl
    have hΘ : ((ctrT2 K ∩ ((ctrE1 K)ᶜ ∪ eqE (p := p))) ∩ ctrE0 K) ∈
        S.Ω (aK + aR + 6 * p + 94)
          (3 * (Polynomial.C 4 * bK + Polynomial.C 8).eval D + 1) (p + 1 + 2) :=
      Omega.mono (inter2_mem (S := S) hI1 hTC'') (by simp only [max_self]; omega) (by omega)
    have hAll := forall_mem (S := S) hΘ
    have hAll2 : {y : Fin (p + 1 + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc y t : Fin (p + 1 + 2) → ℝ) ∈
          ((ctrT2 K ∩ ((ctrE1 K)ᶜ ∪ eqE (p := p))) ∩ ctrE0 K)} ∈
        S.Ω (aK + aR + 6 * p + 99) (12 * (bK.eval D + bR.eval D) + 25) (p + 1 + 1) := by
      refine Omega.mono hAll (by omega) ?_
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega
    have hEx : projLast {y : Fin (p + 1 + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc y t : Fin (p + 1 + 2) → ℝ) ∈
          ((ctrT2 K ∩ ((ctrE1 K)ᶜ ∪ eqE (p := p))) ∩ ctrE0 K)} ∈
        S.Ω (aK + aR + 6 * p + 100) (12 * (bK.eval D + bR.eval D) + 25) (p + 1) :=
      Omega.mono (S.proj hAll2) (by omega) le_rfl
    have he : projLast {y : Fin (p + 1 + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc y t : Fin (p + 1 + 2) → ℝ) ∈
          ((ctrT2 K ∩ ((ctrE1 K)ᶜ ∪ eqE (p := p))) ∩ ctrE0 K)} = selB K := by
      ext z
      constructor
      · rintro ⟨c, hc⟩
        have hct : ∀ u : ℝ, (Fin.snoc (Fin.init z) (z (Fin.last p) + u) ∈ K ↔
            Fin.snoc (Fin.init z) (z (Fin.last p) - u) ∈ K) := by
          intro u
          have h1 : ∀ u' : ℝ, (Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) 0))
                (((Fin.snoc (Fin.snoc z c) 0) : Fin (p + 1 + 2) → ℝ) (idxT p 2) + u') ∈ K ↔
              Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) 0))
                (((Fin.snoc (Fin.snoc z c) 0) : Fin (p + 1 + 2) → ℝ) (idxT p 2) - u') ∈ K) := by
            have hh := (hc 0).1.1
            simp only [ctrT2] at hh
            exact hh
          have h2 := h1 u
          rw [basePart_snoc_snoc z c 0, snoc_snoc_idxT z c 0] at h2
          exact h2
        have hcc : ∀ u : ℝ, (Fin.snoc (Fin.init z) (c + u) ∈ K ↔
            Fin.snoc (Fin.init z) (c - u) ∈ K) := by
          intro u
          have h1 : ∀ u' : ℝ, (Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) 0))
                (((Fin.snoc (Fin.snoc z c) 0) : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) + u') ∈ K ↔
              Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) 0))
                (((Fin.snoc (Fin.snoc z c) 0) : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) - u') ∈ K) := by
            have hh := (hc 0).2
            simp only [ctrE0] at hh
            exact hh
          have h2 := h1 u
          rw [basePart_snoc_snoc z c 0, snoc_snoc_idxE0 z c 0] at h2
          exact h2
        have huniq : ∀ c' : ℝ, (∀ u : ℝ, (Fin.snoc (Fin.init z) (c' + u) ∈ K ↔
            Fin.snoc (Fin.init z) (c' - u) ∈ K)) → c' = c := by
          intro c' hc'
          have h := (hc c').1.2
          rw [Set.mem_union] at h
          rcases h with h | h
          · simp only [Set.mem_compl_iff, ctrE1, Set.mem_ofPred_eq] at h
            simp only [basePart_snoc_snoc z c c', snoc_snoc_idxE1 z c c'] at h
            exact absurd hc' h
          · simp only [eqE, Set.mem_ofPred_eq] at h
            simp only [snoc_snoc_idxE1 z c c', snoc_snoc_idxE0 z c c'] at h
            exact h
        exact ⟨hct, ⟨c, hcc, huniq⟩⟩
      · rintro ⟨h1, c, hcc, huniq⟩
        refine ⟨c, fun t => ?_⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have h2 : ∀ u' : ℝ, (Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) t))
              (((Fin.snoc (Fin.snoc z c) t) : Fin (p + 1 + 2) → ℝ) (idxT p 2) + u') ∈ K ↔
            Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) t))
              (((Fin.snoc (Fin.snoc z c) t) : Fin (p + 1 + 2) → ℝ) (idxT p 2) - u') ∈ K) := by
            intro u'
            rw [basePart_snoc_snoc z c t, snoc_snoc_idxT z c t]
            exact h1 u'
          exact h2
        · rw [Set.mem_union]
          by_cases hc' : ∀ u : ℝ, (Fin.snoc (Fin.init z) (t + u) ∈ K ↔
              Fin.snoc (Fin.init z) (t - u) ∈ K)
          · refine Or.inr ?_
            have ht : t = c := huniq t hc'
            simp only [eqE, Set.mem_ofPred_eq]
            rw [snoc_snoc_idxE1 z c t, snoc_snoc_idxE0 z c t, ht]
          · refine Or.inl ?_
            rw [Set.mem_compl_iff]
            intro hcon
            simp only [ctrE1, Set.mem_ofPred_eq] at hcon
            exact hc' (by
              intro u
              have h := hcon u
              rw [basePart_snoc_snoc z c t, snoc_snoc_idxE1 z c t] at h
              exact h)
        · have h2 : ∀ u' : ℝ, (Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) t))
              (((Fin.snoc (Fin.snoc z c) t) : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) + u') ∈ K ↔
            Fin.snoc (basePart (k := 2) (Fin.snoc (Fin.snoc z c) t))
              (((Fin.snoc (Fin.snoc z c) t) : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) - u') ∈ K) := by
            intro u'
            rw [basePart_snoc_snoc z c t, snoc_snoc_idxE0 z c t]
            exact hcc u'
          exact h2
    rw [he] at hEx
    exact hEx
  exact Omega.mono hB2 (by omega) (by omega)

end Work.WilG1.Choice
