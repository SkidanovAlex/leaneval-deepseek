/-
  Work.WilE9.Gen.gen_diff_gen — the atoms of the chain are `Gen`-sets.

  Their formats are constants (independent of the degree budget `D`), except for the two
  pullbacks along `G` (`dGB_gen`, `dGA_gen`), which cost `F + 2*(ambient + n + 1) + 1` in the
  format and `D + 2` in the degree, by `Work.WilE9.Glue.subst_mem`.
-/
import Submission.Work.WilE9.Gen.gen_diff_peel
import Submission.Work.WilE9.Glue.pos_poly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Gen

namespace DiffSet

open WilkiesDesign WilkiesDesign.E

lemma dA3_gen (n : ℕ) : Gen (dd3 n + 1) 1 (dd3 n) (dA3 n) := by
  have h := Gen.hyp (dd3 n) (MvPolynomial.X (dhI3 n) : MvPolynomial (Fin (dd3 n)) ℝ)
  have htd : (MvPolynomial.X (dhI3 n) : MvPolynomial (Fin (dd3 n)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have hset : {z : Fin (dd3 n) → ℝ |
      MvPolynomial.eval z (MvPolynomial.X (dhI3 n)) = 0} = {z : Fin (dd3 n) → ℝ |
        z (dhI3 n) = 0} := by
    ext z; simp
  have h1 : Gen (dd3 n) 1 (dd3 n) {z : Fin (dd3 n) → ℝ | z (dhI3 n) = 0} := by
    have h2 := Gen.monoD htd h
    rwa [hset] at h2
  have h3 := Gen.compl h1
  have hEq : ({z : Fin (dd3 n) → ℝ | z (dhI3 n) = 0})ᶜ = dA3 n := by
    ext z; simp [dA3, Set.mem_compl_iff]
  rwa [hEq] at h3

lemma dA4_gen (n : ℕ) : Gen (dd3 n + 4) 6 (dd3 n) (dA4 n) := by
  have h1 := Glue.pos_poly (P4a n)
  have h2 := Glue.pos_poly (P4b n)
  have h1' : Gen (dd3 n + 2) 3 (dd3 n)
      {z : Fin (dd3 n) → ℝ | 0 < MvPolynomial.eval z (P4a n)} :=
    Gen.monoD (by have := totalDegree_P4a_le n; omega) h1
  have h2' : Gen (dd3 n + 2) 3 (dd3 n)
      {z : Fin (dd3 n) → ℝ | 0 < MvPolynomial.eval z (P4b n)} :=
    Gen.monoD (by have := totalDegree_P4b_le n; omega) h2
  have h3 := Gen.inter₂ h1' h2'
  have hset : ({z : Fin (dd3 n) → ℝ | 0 < MvPolynomial.eval z (P4a n)} ∩
      {z : Fin (dd3 n) → ℝ | 0 < MvPolynomial.eval z (P4b n)}) = dA4 n := by
    ext z
    simp only [dA4, P4a, P4b, Set.mem_inter_iff, Set.mem_ofPred_eq, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_X]
  rw [hset] at h3
  refine Gen.mono ?_ (by omega) h3
  rw [max_eq_right (le_refl (dd3 n + 2))]
  simp only [dd3]; omega

lemma dA2_gen (n : ℕ) : Gen (dd4 n + 2) 3 (dd4 n) (dA2 n) := by
  have h := Glue.pos_poly (MvPolynomial.X (ddI4 n) : MvPolynomial (Fin (dd4 n)) ℝ)
  have hdeg : (MvPolynomial.X (ddI4 n) : MvPolynomial (Fin (dd4 n)) ℝ).totalDegree + 2 ≤ 3 := by
    rw [MvPolynomial.totalDegree_X]
  have hset : {z : Fin (dd4 n) → ℝ |
      0 < MvPolynomial.eval z (MvPolynomial.X (ddI4 n))} = dA2 n := by
    ext z; simp [dA2]
  rw [hset] at h
  exact Gen.monoD hdeg h

lemma dA1_gen (n : ℕ) : Gen (dd5 n + 2) 3 (dd5 n) (dA1 n) := by
  have h := Glue.pos_poly (MvPolynomial.X (deI5 n) : MvPolynomial (Fin (dd5 n)) ℝ)
  have hdeg : (MvPolynomial.X (deI5 n) : MvPolynomial (Fin (dd5 n)) ℝ).totalDegree + 2 ≤ 3 := by
    rw [MvPolynomial.totalDegree_X]
  have hset : {z : Fin (dd5 n) → ℝ |
      0 < MvPolynomial.eval z (MvPolynomial.X (deI5 n))} = dA1 n := by
    ext z; simp [dA1]
  rw [hset] at h
  exact Gen.monoD hdeg h

lemma dA5_gen (n : ℕ) (i : Fin n) : Gen (dd2 n + 1) n (dd2 n) (dA5 n i) := by
  have h : Gen (dd2 n + 1) (∑ _ : Fin n, 1) (dd2 n)
      (⋂ j : Fin n, {z : Fin (dd2 n) → ℝ | MvPolynomial.eval z (P5 n i j) = 0}) := by
    refine Gen.inter (fun _ : Fin n => 1) (fun j => {z : Fin (dd2 n) → ℝ |
      MvPolynomial.eval z (P5 n i j) = 0}) (fun j => ?_)
    exact Gen.monoD (totalDegree_P5_le n i j) (Gen.hyp (dd2 n) (P5 n i j))
  have hsum : (∑ _ : Fin n, 1) = n := by simp
  rw [hsum] at h
  have hset : (⋂ j : Fin n, {z : Fin (dd2 n) → ℝ | MvPolynomial.eval z (P5 n i j) = 0}) =
      dA5 n i := by
    ext z
    simp only [dA5, P5, Set.mem_iInter, Set.mem_ofPred_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    constructor
    · intro h j; linarith [h j]
    · intro h j; linarith [h j]
  rw [hset] at h
  exact h

lemma dGB_gen {F D n : ℕ} {G : Set (Fin (n + 1) → ℝ)} (hG : Gen F D (n + 1) G) :
    Gen (F + 2 * (dd0 n + (n + 1)) + 1) (D + 2) (dd0 n) (dGB n G) := by
  have h := Glue.subst_mem (ιGB n) hG
  have hset : {x : Fin (dd0 n) → ℝ | (fun j => x (ιGB n j)) ∈ G} = dGB n G := by
    ext x
    simp only [dGB, Set.mem_ofPred_eq, eq_snoc_ιGB]
  rwa [hset] at h

lemma dGA_gen {F D n : ℕ} {G : Set (Fin (n + 1) → ℝ)} (hG : Gen F D (n + 1) G) :
    Gen (F + 2 * (dd1 n + (n + 1)) + 1) (D + 2) (dd1 n) (dGA n G) := by
  have h := Glue.subst_mem (ιGA n) hG
  have hset : {x : Fin (dd1 n) → ℝ | (fun j => x (ιGA n j)) ∈ G} = dGA n G := by
    ext x
    simp only [dGA, Set.mem_ofPred_eq, eq_snoc_ιGA]
  rwa [hset] at h

lemma dA7_gen (n : ℕ) : Gen (dd0 n + 8) 15 (dd0 n) (dA7 n) := by
  have hε : Gen (dd0 n + 2) 3 (dd0 n) {z : Fin (dd0 n) → ℝ | 0 < z (deI0 n)} := by
    have h := Glue.pos_poly (P7a n)
    have hdeg : (P7a n).totalDegree + 2 ≤ 3 := by have := totalDegree_P7a_le n; omega
    have hset : {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7a n)} =
        {z : Fin (dd0 n) → ℝ | 0 < z (deI0 n)} := by
      ext z; simp [P7a]
    rw [hset] at h
    exact Gen.monoD hdeg h
  have hne : Gen (dd0 n + 1) 1 (dd0 n) {z : Fin (dd0 n) → ℝ | z (dhI0 n) ≠ 0} := by
    have h := Gen.hyp (dd0 n) (P7b n)
    have hset : {z : Fin (dd0 n) → ℝ | MvPolynomial.eval z (P7b n) = 0} =
        {z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} := by
      ext z; simp [P7b]
    rw [hset] at h
    exact Gen.compl (Gen.monoD (totalDegree_P7b_le n) h)
  have hz : Gen (dd0 n) 1 (dd0 n) {z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} := by
    have h := Gen.hyp (dd0 n) (P7b n)
    have hset : {z : Fin (dd0 n) → ℝ | MvPolynomial.eval z (P7b n) = 0} =
        {z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} := by
      ext z; simp [P7b]
    rw [hset] at h
    exact Gen.monoD (totalDegree_P7b_le n) h
  have hpos : Gen (dd0 n + 2) 6 (dd0 n)
      {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7c n)} := by
    have h := Glue.pos_poly (P7c n)
    have hdeg : (P7c n).totalDegree + 2 ≤ 6 := by have := totalDegree_P7c_le n; omega
    exact Gen.monoD hdeg h
  have hw2 : Gen (dd0 n + 2) 4 (dd0 n)
      {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7d n)} := by
    have h := Glue.pos_poly (P7d n)
    have hdeg : (P7d n).totalDegree + 2 ≤ 4 := by have := totalDegree_P7d_le n; omega
    exact Gen.monoD hdeg h
  have hdisj1 : Gen (dd0 n + 3) (1 + 6) (dd0 n)
      ({z : Fin (dd0 n) → ℝ | z (dhI0 n) ≠ 0} ∩
        {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7c n)}) := by
    have h := Gen.inter₂ hne hpos
    refine Gen.monoF ?_ h
    rw [max_eq_right (by simp only [dd0]; omega)]
  have hdisj2 : Gen (dd0 n + 3) (1 + 4) (dd0 n)
      ({z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} ∩
        {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7d n)}) := by
    have h := Gen.inter₂ hz hw2
    refine Gen.monoF ?_ h
    rw [max_eq_right (by simp only [dd0]; omega)]
  have hunion : Gen (dd0 n + 4) (7 + 5) (dd0 n)
      (({z : Fin (dd0 n) → ℝ | z (dhI0 n) ≠ 0} ∩
          {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7c n)}) ∪
        ({z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} ∩
          {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7d n)})) := by
    have h := Gen.union₂ hdisj1 hdisj2
    refine Gen.monoF ?_ h
    rw [max_eq_right (le_refl (dd0 n + 3))]
    exact Nat.le_succ _
  have htot : Gen (dd0 n + 5) (3 + 12) (dd0 n)
      ({z : Fin (dd0 n) → ℝ | 0 < z (deI0 n)} ∩
        (({z : Fin (dd0 n) → ℝ | z (dhI0 n) ≠ 0} ∩
            {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7c n)}) ∪
          ({z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} ∩
            {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7d n)}))) := by
    have h := Gen.inter₂ hε hunion
    refine Gen.monoF ?_ h
    rw [max_eq_right (by simp only [dd0]; omega)]
  have hset : ({z : Fin (dd0 n) → ℝ | 0 < z (deI0 n)} ∩
        (({z : Fin (dd0 n) → ℝ | z (dhI0 n) ≠ 0} ∩
            {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7c n)}) ∪
          ({z : Fin (dd0 n) → ℝ | z (dhI0 n) = 0} ∩
            {z : Fin (dd0 n) → ℝ | 0 < MvPolynomial.eval z (P7d n)}))) = dA7 n := by
    ext z
    simp only [dA7, P7c, P7d, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq,
      MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor
    · rintro ⟨h0, h | h⟩
      · exact ⟨h0, Or.inl h⟩
      · exact ⟨h0, Or.inr ⟨h.1, by linarith [h.2]⟩⟩
    · rintro ⟨h0, h | h⟩
      · exact ⟨h0, Or.inl h⟩
      · exact ⟨h0, Or.inr ⟨h.1, by linarith [h.2]⟩⟩
  rw [hset] at htot
  exact Gen.mono (by simp only [dd0]; omega) (by omega) htot

end DiffSet

end Work.WilE9.Gen
