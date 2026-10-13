import Mathlib
import Submission.Work.WilG4c.hbdd_defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.CG

namespace Work.WilG4c

/-- `ψ(u) = 1/2 + u/(2√(1+u²))`.  Its graph is the semialgebraic set
`{(u,v) | (2v-1)²(1+u²) = u² ∧ 0 ≤ u(2v-1)}`, hence `Ω`-definable with format and degree
independent of the degree parameter. -/
theorem hbdd_psi_graph_fb (S : WilkiesDesign.SOMin) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ D : ℕ,
      WilkiesDesign.graphOf (fun v : Fin 1 → ℝ => Work.WilkG4c.psi (v 0))
        ∈ S.Ω a (b.eval D) (1 + 1) := by
  set P : MvPolynomial (Fin 2) ℝ :=
    (2 * MvPolynomial.X 1 - 1) ^ 2 * (1 + MvPolynomial.X 0 ^ 2) - MvPolynomial.X 0 ^ 2 with hP
  set Q : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 * (2 * MvPolynomial.X 1 - 1) with hQ
  have hset : WilkiesDesign.graphOf (fun v : Fin 1 → ℝ => Work.WilkG4c.psi (v 0))
      = {z : Fin 2 → ℝ | MvPolynomial.eval z P = 0}
        ∩ {z : Fin 2 → ℝ | 0 ≤ MvPolynomial.eval z Q} := by
    ext x
    have hPx : MvPolynomial.eval x P
        = (2 * x 1 - 1) ^ 2 * (1 + x 0 ^ 2) - x 0 ^ 2 := by simp [hP]
    have hQx : MvPolynomial.eval x Q = x 0 * (2 * x 1 - 1) := by simp [hQ]
    simp only [WilkiesDesign.graphOf, Set.mem_setOf_eq, Set.mem_inter_iff]
    have h1 : x (Fin.last 1) = x 1 := by congr 1
    have h2 : (Fin.init x) 0 = x 0 := by congr 1
    rw [h1, h2]
    constructor
    · intro hx
      have hspos : 0 < Real.sqrt (1 + x 0 ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h2' : 2 * x 1 - 1 = x 0 / Real.sqrt (1 + x 0 ^ 2) := by
        rw [hx]
        show 2 * Work.WilkG4c.psi (x 0) - 1 = x 0 / Real.sqrt (1 + x 0 ^ 2)
        rw [Work.WilkG4c.psi]
        ring
      constructor
      · rw [hPx, h2']
        field_simp
        rw [Real.sq_sqrt (by positivity)]
        ring
      · rw [hQx, h2']
        have h3 : x 0 * (x 0 / Real.sqrt (1 + x 0 ^ 2))
            = x 0 ^ 2 / Real.sqrt (1 + x 0 ^ 2) := by ring
        rw [h3]
        positivity
    · rintro ⟨hP0, hQ0⟩
      rw [hPx] at hP0
      rw [hQx] at hQ0
      have hspos : 0 < Real.sqrt (1 + x 0 ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hsq : Real.sqrt (1 + x 0 ^ 2) ^ 2 = 1 + x 0 ^ 2 := Real.sq_sqrt (by positivity)
      set e : ℝ := 2 * x 1 - 1 with hedef
      have he1 : e ^ 2 * (1 + x 0 ^ 2) = x 0 ^ 2 := by
        rw [hedef]; linarith
      have he2 : (e * Real.sqrt (1 + x 0 ^ 2)) ^ 2 = x 0 ^ 2 := by
        rw [mul_pow, hsq]; nlinarith [he1]
      have heval : e = x 0 / Real.sqrt (1 + x 0 ^ 2) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp he2 with h | h
        · exact (eq_div_iff (ne_of_gt hspos)).mpr h
        · have hu0 : x 0 = 0 := by
            have hA : x 0 * (e * Real.sqrt (1 + x 0 ^ 2)) = -(x 0 ^ 2) := by rw [h]; ring
            have hB : 0 ≤ x 0 * (e * Real.sqrt (1 + x 0 ^ 2)) := by
              have hw : 0 ≤ x 0 * e := by rw [hedef]; linarith
              have := mul_nonneg hw (le_of_lt hspos)
              linarith
            have hC : x 0 ^ 2 ≤ 0 := by linarith
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hC (sq_nonneg _))
          rw [hu0] at h
          have hs1 : Real.sqrt (1 + (0 : ℝ) ^ 2) = 1 := by norm_num [Real.sqrt_one]
          rw [hs1, mul_one, neg_zero] at h
          rw [hu0, h, zero_div]
      rw [Work.WilkG4c.psi]
      rw [hedef] at heval
      have hkey : x 0 / (2 * Real.sqrt (1 + x 0 ^ 2))
          = (x 0 / Real.sqrt (1 + x 0 ^ 2)) / 2 := by ring
      rw [hkey, ← heval]
      ring
  rw [hset]
  have h1 : {z : Fin 2 → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω 2 P.totalDegree 2 := S.hyp 2 P
  have h2 : {z : Fin 2 → ℝ | 0 < MvPolynomial.eval z (-Q)} ∈
      S.Ω 4 ((-Q).totalDegree + 2) 2 := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := 2) 0 (-Q)
    simpa [Polynomial.eval_C] using h
  have h3 : ({z : Fin 2 → ℝ | 0 < MvPolynomial.eval z (-Q)})ᶜ ∈
      S.Ω 5 ((-Q).totalDegree + 2) 2 := S.compl h2
  have h1' : {z : Fin 2 → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω 5 P.totalDegree 2 :=
    Work.WilG1.Omega.mono h1 (by norm_num) le_rfl
  have h4 : {z : Fin 2 → ℝ | MvPolynomial.eval z P = 0} ∩
      ({z : Fin 2 → ℝ | 0 < MvPolynomial.eval z (-Q)})ᶜ ∈
      S.Ω 6 (P.totalDegree + ((-Q).totalDegree + 2)) 2 :=
    Work.WilG0.Omega_inter2 h1' h3
  have hcompl : {z : Fin 2 → ℝ | 0 ≤ MvPolynomial.eval z Q} =
      ({z : Fin 2 → ℝ | 0 < MvPolynomial.eval z (-Q)})ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, MvPolynomial.eval_neg, not_lt]
    constructor <;> intro h <;> linarith
  rw [hcompl]
  refine ⟨6, Polynomial.C (P.totalDegree + ((-Q).totalDegree + 2)), fun D => ?_⟩
  simpa [Polynomial.eval_C] using h4

end Work.WilG4c
