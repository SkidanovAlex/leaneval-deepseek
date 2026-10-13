/-
  WilG1/Choice/PiecesACD — the `Ω`-membership of the first, third and fourth disjuncts of
  `selSet` (the empty-fibre case and the two half-line cases).

  Each piece is first brought to a uniform clean format, so that the format bookkeeping of
  the combinations reduces to `simp only [max_self]` plus linear arithmetic.
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

/-! ## 3. `selA` -/

theorem selA_mem {S : SOMin} {p aK aR D : ℕ} {bK bR : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    (hK : K ∈ S.Ω aK (bK.eval D) (p + 1)) (_hR : R ∈ S.Ω aR (bR.eval D) p) :
    selA K ∈ S.Ω (aK + aR + 6 * p + 110) (bK.eval D + bR.eval D + 1) (p + 1) := by
  have h1 : {z : Fin (p + 1) → ℝ | ∀ s : ℝ, Fin.snoc (Fin.init z) s ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 90) (bK.eval D) (p + 1) := by
    have h := S.prod_right (isAll_mem (S := S) hK)
    have he : {z : Fin (p + 1) → ℝ |
          Fin.init z ∈ {l : Fin p → ℝ | ∀ s : ℝ, Fin.snoc l s ∈ K}} =
        {z : Fin (p + 1) → ℝ | ∀ s : ℝ, Fin.snoc (Fin.init z) s ∈ K} := rfl
    rw [he] at h
    exact Omega.mono h (by omega) le_rfl
  have h2 : {z : Fin (p + 1) → ℝ | z (Fin.last p) = 0} ∈
      S.Ω (aK + aR + 6 * p + 90) 1 (p + 1) :=
    Omega.mono (coordEq_mem (S := S) (Fin.last p) 0) (by omega) le_rfl
  have h3 : ({z : Fin (p + 1) → ℝ | ∀ s : ℝ, Fin.snoc (Fin.init z) s ∈ K} ∩
      {z : Fin (p + 1) → ℝ | z (Fin.last p) = 0}) ∈
      S.Ω (aK + aR + 6 * p + 91) (bK.eval D + 1) (p + 1) :=
    Omega.mono (inter2_mem (S := S) h1 h2) (by simp only [max_self]; omega) (by omega)
  exact Omega.mono h3 (by omega) (by omega)

/-! ## 4. `selC` -/

theorem selC_mem {S : SOMin} {p aK aR D : ℕ} {bK bR : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    (hK : K ∈ S.Ω aK (bK.eval D) (p + 1)) (_hR : R ∈ S.Ω aR (bR.eval D) p) :
    selC K ∈ S.Ω (aK + aR + 6 * p + 110) (4 * (bK.eval D + bR.eval D) + 18) (p + 1) := by
  have h1 : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D) (p + 1) := by
    have he : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} = K := by
      ext z
      simp
    rw [he]
    exact Omega.mono hK (by omega) le_rfl
  have h2 : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) - 1) ∉ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 2) (p + 1) := by
    have h := S.compl (affLast_last_sub (S := S) (p := p) hK 1)
    refine Omega.mono h
      (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  have h3 : {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 10) (p + 1) := by
    have hle : {w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + (0 + 1)) :=
      Omega.mono (leConst_mem (Fin.last (p + 1)) 0) (by omega) le_rfl
    have hge : {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + (0 + 1)) :=
      Omega.mono (geConst_mem (Fin.last (p + 1)) 1) (by omega) le_rfl
    have hAt : AtomPN (p := p) (k := 0) K (Fin.last p) (-1) ∈
        S.Ω (aK + aR + 6 * p + 90) ((bK + Polynomial.C 2).eval D) (p + 1 + (0 + 1)) :=
      Omega.mono (AtomPN_mem (S := S) (p := p) (k := 0) hK (Fin.last p) (-1))
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hG1 : ({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
        {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∈
        S.Ω (aK + aR + 6 * p + 90) (3 + 3) (p + 1 + (0 + 1)) :=
      Omega.mono (union2_mem (S := S) hle hge) (by simp only [max_self]; omega) (by omega)
    have hG : (({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
        {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∪
          AtomPN (p := p) (k := 0) K (Fin.last p) (-1)) ∈
        S.Ω (aK + aR + 6 * p + 90) ((3 + 3) + (bK + Polynomial.C 2).eval D)
          (p + 1 + (0 + 1)) :=
      Omega.mono (union2_mem (S := S) hG1 hAt) (by simp only [max_self]; omega) (by omega)
    have hW := forall_mem (S := S) hG
    have he : {z : Fin (p + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc z t : Fin (p + 1 + (0 + 1)) → ℝ) ∈
          (({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
            {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∪
              AtomPN (p := p) (k := 0) K (Fin.last p) (-1))} =
        {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
          Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      refine forall_congr' (fun t => ?_)
      simp only [Set.mem_union, AtomPN_snoc (K := K) (k := 0) (Fin.last p) (-1) z t,
        Set.mem_ofPred_eq, snoc_last (p := p) (k := 0) z t, basePart_self z]
      constructor
      · rintro ((h0 | h1) | h3) hgt hlt
        · linarith
        · linarith
        · rw [show z (Fin.last p) + t + (-1) = z (Fin.last p) - 1 + t from by ring] at h3
          exact h3
      · intro h
        by_cases h0 : t ≤ 0
        · exact Or.inl (Or.inl h0)
        · by_cases h1 : 1 ≤ t
          · exact Or.inl (Or.inr h1)
          · refine Or.inr ?_
            have h3 := h (not_le.mp h0) (not_le.mp h1)
            rw [show z (Fin.last p) - 1 + t = z (Fin.last p) + t + (-1) from by ring] at h3
            exact h3
    rw [he] at hW
    refine Omega.mono hW (by omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  have h4 : {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ M < s} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 5) (p + 1) := by
    have hAt : AtomLL (p := p) (k := 1) K 0 ∈
        S.Ω (aK + aR + 6 * p + 90) ((bK + Polynomial.C 2).eval D) (p + 1 + 2) :=
      Omega.mono (AtomLL_mem (S := S) (p := p) (k := 1) hK 0)
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hlt : {w : Fin (p + 1 + 2) → ℝ | w (idxE p 2 (0 : Fin 2)) < w (Fin.last (p + 2))} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + 2) :=
      Omega.mono (Calc.lt_mem (S := S) D (idxE p 2 (0 : Fin 2)) (Fin.last (p + 2)))
        (by omega) (by simp)
    have hW : (AtomLL (p := p) (k := 1) K 0 ∩
        {w : Fin (p + 1 + 2) → ℝ | w (idxE p 2 (0 : Fin 2)) < w (Fin.last (p + 2))}) ∈
        S.Ω (aK + aR + 6 * p + 91) (bK.eval D + 5) (p + 1 + 2) :=
      Omega.mono (inter2_mem (S := S) hAt hlt) (by simp only [max_self]; omega)
        (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega)
    have hU : {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
          Fin.snoc (basePart (k := 1) y) s ∈ K ∧ y (idxE p 1 (0 : Fin 1)) < s} ∈
        S.Ω (aK + aR + 6 * p + 92) (bK.eval D + 5) (p + 1 + 1) := by
      have h := S.proj hW
      have he : projLast (AtomLL (p := p) (k := 1) K 0 ∩
          {w : Fin (p + 1 + 2) → ℝ | w (idxE p 2 (0 : Fin 2)) < w (Fin.last (p + 2))}) =
          {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
            Fin.snoc (basePart (k := 1) y) s ∈ K ∧ y (idxE p 1 (0 : Fin 1)) < s} := by
        ext y
        constructor
        · rintro ⟨s, hs1, hs2⟩
          have hK1 : Fin.snoc (basePart (k := 1) y) (s + 0) ∈ K :=
            (AtomLL_snoc (p := p) (k := 1) (K := K) 0 y s).mp hs1
          have hK2 : Fin.snoc (basePart (k := 1) y) s ∈ K := by
            rw [show s + 0 = s from by ring] at hK1
            exact hK1
          have h2 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) =
              y (idxE p 1 0) := by
            rw [show idxE p 2 (0 : Fin 2) = Fin.castSucc (idxE p 1 (0 : Fin 1)) from
              Fin.ext rfl, Fin.snoc_castSucc]
          have h3 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (Fin.last (p + 2)) = s := by
            rw [Fin.snoc_last]
          simp only [Set.mem_ofPred_eq] at hs2
          rw [h2, h3] at hs2
          exact ⟨s, hK2, hs2⟩
        · rintro ⟨s, hs1, hs2⟩
          refine ⟨s, ?_, ?_⟩
          · rw [AtomLL_snoc (p := p) (k := 1) (K := K) 0 y s]
            rw [show s + 0 = s from by ring]
            exact hs1
          · simp only [Set.mem_ofPred_eq]
            have h2 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) =
                y (idxE p 1 0) := by
              rw [show idxE p 2 (0 : Fin 2) = Fin.castSucc (idxE p 1 (0 : Fin 1)) from
                Fin.ext rfl, Fin.snoc_castSucc]
            have h3 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (Fin.last (p + 2)) = s := by
              rw [Fin.snoc_last]
            rw [h2, h3]
            exact hs2
      rw [he] at h
      exact Omega.mono h (by omega) le_rfl
    have hAll := forall_mem (S := S) hU
    have he : {z : Fin (p + 1) → ℝ | ∀ t : ℝ, Fin.snoc z t ∈
          {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
            Fin.snoc (basePart (k := 1) y) s ∈ K ∧ y (idxE p 1 (0 : Fin 1)) < s}} =
        {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ M < s} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      refine forall_congr' (fun t => ?_)
      constructor
      · rintro ⟨s, hs1, hs2⟩
        have h1 : (Fin.snoc z t : Fin (p + 1 + 1) → ℝ) (idxE p 1 (0 : Fin 1)) = t :=
          snoc_idxE1_zero z t
        rw [basePart_snoc_zero z t] at hs1
        rw [h1] at hs2
        exact ⟨s, hs1, hs2⟩
      · rintro ⟨s, hs1, hs2⟩
        exact ⟨s, by
            rw [basePart_snoc_zero z t]
            exact hs1, by
            rw [snoc_idxE1_zero z t]
            exact hs2⟩
    rw [he] at hAll
    exact Omega.mono hAll (by omega) le_rfl
  have h12 := inter2_mem (S := S) h1 h2
  have h12' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) - 1) ∉ K}) ∈
      S.Ω (aK + aR + 6 * p + 101) (2 * bK.eval D + 2) (p + 1) :=
    Omega.mono h12 (by simp only [max_self]; omega) (by omega)
  have h3' : {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 101) (bK.eval D + 10) (p + 1) :=
    Omega.mono h3 (by omega) le_rfl
  have h123 := inter2_mem (S := S) h12' h3'
  have h123' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) - 1) ∉ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K}) ∈
      S.Ω (aK + aR + 6 * p + 102) (3 * bK.eval D + 12) (p + 1) :=
    Omega.mono h123 (by simp only [max_self]; omega) (by omega)
  have h4' : {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ M < s} ∈
      S.Ω (aK + aR + 6 * p + 102) (bK.eval D + 5) (p + 1) :=
    Omega.mono h4 (by omega) le_rfl
  have h1234 := inter2_mem (S := S) h123' h4'
  have h1234' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) - 1) ∉ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ M < s}) ∈
      S.Ω (aK + aR + 6 * p + 103) (4 * bK.eval D + 17) (p + 1) :=
    Omega.mono h1234 (by simp only [max_self]; omega) (by omega)
  exact Omega.mono h1234' (by omega) (by omega)

/-! ## 5. `selD` -/

theorem selD_mem {S : SOMin} {p aK aR D : ℕ} {bK bR : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    (hK : K ∈ S.Ω aK (bK.eval D) (p + 1)) (_hR : R ∈ S.Ω aR (bR.eval D) p) :
    selD K ∈ S.Ω (aK + aR + 6 * p + 110) (4 * (bK.eval D + bR.eval D) + 18) (p + 1) := by
  have h1 : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D) (p + 1) := by
    have he : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} = K := by
      ext z
      simp
    rw [he]
    exact Omega.mono hK (by omega) le_rfl
  have h2 : {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) + 1) ∉ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 2) (p + 1) := by
    have h := S.compl (affLast_last (S := S) (p := p) hK 1)
    refine Omega.mono h
      (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  have h3 : {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 10) (p + 1) := by
    have hle : {w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + (0 + 1)) :=
      Omega.mono (leConst_mem (Fin.last (p + 1)) 0) (by omega) le_rfl
    have hge : {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + (0 + 1)) :=
      Omega.mono (geConst_mem (Fin.last (p + 1)) 1) (by omega) le_rfl
    have hAt : AtomMN (p := p) (k := 0) K (Fin.last p) 1 ∈
        S.Ω (aK + aR + 6 * p + 90) ((bK + Polynomial.C 2).eval D) (p + 1 + (0 + 1)) :=
      Omega.mono (AtomMN_mem (S := S) (p := p) (k := 0) hK (Fin.last p) 1)
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hG1 : ({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
        {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∈
        S.Ω (aK + aR + 6 * p + 90) (3 + 3) (p + 1 + (0 + 1)) :=
      Omega.mono (union2_mem (S := S) hle hge) (by simp only [max_self]; omega) (by omega)
    have hG : (({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
        {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∪
          AtomMN (p := p) (k := 0) K (Fin.last p) 1) ∈
        S.Ω (aK + aR + 6 * p + 90) ((3 + 3) + (bK + Polynomial.C 2).eval D)
          (p + 1 + (0 + 1)) :=
      Omega.mono (union2_mem (S := S) hG1 hAt) (by simp only [max_self]; omega) (by omega)
    have hW := forall_mem (S := S) hG
    have he : {z : Fin (p + 1) → ℝ | ∀ t : ℝ,
          (Fin.snoc z t : Fin (p + 1 + (0 + 1)) → ℝ) ∈
          (({w : Fin (p + 1 + (0 + 1)) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∪
            {w : Fin (p + 1 + (0 + 1)) → ℝ | 1 ≤ w (Fin.last (p + 1))}) ∪
              AtomMN (p := p) (k := 0) K (Fin.last p) 1)} =
        {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
          Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      refine forall_congr' (fun t => ?_)
      simp only [Set.mem_union, AtomMN_snoc (K := K) (k := 0) (Fin.last p) 1 z t,
        Set.mem_ofPred_eq, snoc_last (p := p) (k := 0) z t, basePart_self z]
      constructor
      · rintro ((h0 | h1) | h3) hgt hlt
        · linarith
        · linarith
        · rw [show z (Fin.last p) - t + 1 = z (Fin.last p) + 1 - t from by ring] at h3
          exact h3
      · intro h
        by_cases h0 : t ≤ 0
        · exact Or.inl (Or.inl h0)
        · by_cases h1 : 1 ≤ t
          · exact Or.inl (Or.inr h1)
          · refine Or.inr ?_
            have h3 := h (not_le.mp h0) (not_le.mp h1)
            rw [show z (Fin.last p) + 1 - t = z (Fin.last p) - t + 1 from by ring] at h3
            exact h3
    rw [he] at hW
    refine Omega.mono hW (by omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  have h4 : {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ s < M} ∈
      S.Ω (aK + aR + 6 * p + 100) (bK.eval D + 5) (p + 1) := by
    have hAt : AtomLL (p := p) (k := 1) K 0 ∈
        S.Ω (aK + aR + 6 * p + 90) ((bK + Polynomial.C 2).eval D) (p + 1 + 2) :=
      Omega.mono (AtomLL_mem (S := S) (p := p) (k := 1) hK 0)
        (by simp only [Nat.add_assoc]; repeat (refine max_add_le ?_ ?_); all_goals omega) le_rfl
    have hlt : {w : Fin (p + 1 + 2) → ℝ | w (Fin.last (p + 2)) < w (idxE p 2 (0 : Fin 2))} ∈
        S.Ω (aK + aR + 6 * p + 90) 3 (p + 1 + 2) :=
      Omega.mono (Calc.lt_mem (S := S) D (Fin.last (p + 2)) (idxE p 2 (0 : Fin 2)))
        (by omega) (by simp)
    have hW : (AtomLL (p := p) (k := 1) K 0 ∩
        {w : Fin (p + 1 + 2) → ℝ | w (Fin.last (p + 2)) < w (idxE p 2 (0 : Fin 2))}) ∈
        S.Ω (aK + aR + 6 * p + 91) (bK.eval D + 5) (p + 1 + 2) :=
      Omega.mono (inter2_mem (S := S) hAt hlt) (by simp only [max_self]; omega)
        (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega)
    have hU : {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
          Fin.snoc (basePart (k := 1) y) s ∈ K ∧ s < y (idxE p 1 (0 : Fin 1))} ∈
        S.Ω (aK + aR + 6 * p + 92) (bK.eval D + 5) (p + 1 + 1) := by
      have h := S.proj hW
      have he : projLast (AtomLL (p := p) (k := 1) K 0 ∩
          {w : Fin (p + 1 + 2) → ℝ | w (Fin.last (p + 2)) < w (idxE p 2 (0 : Fin 2))}) =
          {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
            Fin.snoc (basePart (k := 1) y) s ∈ K ∧ s < y (idxE p 1 (0 : Fin 1))} := by
        ext y
        constructor
        · rintro ⟨s, hs1, hs2⟩
          have hK1 : Fin.snoc (basePart (k := 1) y) (s + 0) ∈ K :=
            (AtomLL_snoc (p := p) (k := 1) (K := K) 0 y s).mp hs1
          have hK2 : Fin.snoc (basePart (k := 1) y) s ∈ K := by
            rw [show s + 0 = s from by ring] at hK1
            exact hK1
          have h2 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) =
              y (idxE p 1 0) := by
            rw [show idxE p 2 (0 : Fin 2) = Fin.castSucc (idxE p 1 (0 : Fin 1)) from
              Fin.ext rfl, Fin.snoc_castSucc]
          have h3 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (Fin.last (p + 2)) = s := by
            rw [Fin.snoc_last]
          simp only [Set.mem_ofPred_eq] at hs2
          rw [h2, h3] at hs2
          exact ⟨s, hK2, hs2⟩
        · rintro ⟨s, hs1, hs2⟩
          refine ⟨s, ?_, ?_⟩
          · rw [AtomLL_snoc (p := p) (k := 1) (K := K) 0 y s]
            rw [show s + 0 = s from by ring]
            exact hs1
          · simp only [Set.mem_ofPred_eq]
            have h2 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) =
                y (idxE p 1 0) := by
              rw [show idxE p 2 (0 : Fin 2) = Fin.castSucc (idxE p 1 (0 : Fin 1)) from
                Fin.ext rfl, Fin.snoc_castSucc]
            have h3 : (Fin.snoc y s : Fin (p + 1 + 2) → ℝ) (Fin.last (p + 2)) = s := by
              rw [Fin.snoc_last]
            rw [h2, h3]
            exact hs2
      rw [he] at h
      exact Omega.mono h (by omega) le_rfl
    have hAll := forall_mem (S := S) hU
    have he : {z : Fin (p + 1) → ℝ | ∀ t : ℝ, Fin.snoc z t ∈
          {y : Fin (p + 1 + 1) → ℝ | ∃ s : ℝ,
            Fin.snoc (basePart (k := 1) y) s ∈ K ∧ s < y (idxE p 1 (0 : Fin 1))}} =
        {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ s < M} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      refine forall_congr' (fun t => ?_)
      constructor
      · rintro ⟨s, hs1, hs2⟩
        have h1 : (Fin.snoc z t : Fin (p + 1 + 1) → ℝ) (idxE p 1 (0 : Fin 1)) = t :=
          snoc_idxE1_zero z t
        rw [basePart_snoc_zero z t] at hs1
        rw [h1] at hs2
        exact ⟨s, hs1, hs2⟩
      · rintro ⟨s, hs1, hs2⟩
        exact ⟨s, by
            rw [basePart_snoc_zero z t]
            exact hs1, by
            rw [snoc_idxE1_zero z t]
            exact hs2⟩
    rw [he] at hAll
    exact Omega.mono hAll (by omega) le_rfl
  have h12 := inter2_mem (S := S) h1 h2
  have h12' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) + 1) ∉ K}) ∈
      S.Ω (aK + aR + 6 * p + 101) (2 * bK.eval D + 2) (p + 1) :=
    Omega.mono h12 (by simp only [max_self]; omega) (by omega)
  have h3' : {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K} ∈
      S.Ω (aK + aR + 6 * p + 101) (bK.eval D + 10) (p + 1) :=
    Omega.mono h3 (by omega) le_rfl
  have h123 := inter2_mem (S := S) h12' h3'
  have h123' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) + 1) ∉ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K}) ∈
      S.Ω (aK + aR + 6 * p + 102) (3 * bK.eval D + 12) (p + 1) :=
    Omega.mono h123 (by simp only [max_self]; omega) (by omega)
  have h4' : {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ s < M} ∈
      S.Ω (aK + aR + 6 * p + 102) (bK.eval D + 5) (p + 1) :=
    Omega.mono h4 (by omega) le_rfl
  have h1234 := inter2_mem (S := S) h123' h4'
  have h1234' : ({z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) + 1) ∉ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
        Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K} ∩
      {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ s < M}) ∈
      S.Ω (aK + aR + 6 * p + 103) (4 * bK.eval D + 17) (p + 1) :=
    Omega.mono h1234 (by simp only [max_self]; omega) (by omega)
  exact Omega.mono h1234' (by omega) (by omega)

end Work.WilG1.Choice
