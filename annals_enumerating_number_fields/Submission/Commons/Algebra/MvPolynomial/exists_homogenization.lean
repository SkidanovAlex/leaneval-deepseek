import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

theorem exists_homogenization {k : Type} [Field k] {r : ℕ} (f : MvPolynomial (Fin r) k) :
    ∃ F : MvPolynomial (Fin (r+1)) k,
      (F.IsHomogeneous F.totalDegree) ∧ F.totalDegree ≤ f.totalDegree ∧
      (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) F = f) := by
  set ψ : Fin (r+1) → MvPolynomial (Fin r) k :=
    (fun i => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) with hψ
  let F : MvPolynomial (Fin (r+1)) k :=
    ∑ n ∈ Finset.range (f.totalDegree + 1),
      rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f) *
        X (0 : Fin (r+1)) ^ (f.totalDegree - n)
  have hhom : F.IsHomogeneous f.totalDegree := by
    dsimp only [F]
    apply IsHomogeneous.sum
    intro n hn
    have hnle : n ≤ f.totalDegree := by
      have := Finset.mem_range.mp hn; omega
    have h1 : (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f)).IsHomogeneous n :=
      (homogeneousComponent_isHomogeneous n f).rename_isHomogeneous
    have h2 : ((X (R := k) (0 : Fin (r+1))) ^ (f.totalDegree - n)).IsHomogeneous (f.totalDegree - n) := by
      simpa using (isHomogeneous_X (R := k) (0 : Fin (r+1))).pow (f.totalDegree - n)
    have h3 := h1.mul h2
    rwa [Nat.add_sub_cancel' hnle] at h3
  refine ⟨F, ?_, ?_, ?_⟩
  · rcases eq_or_ne F 0 with h | h
    · rw [h, MvPolynomial.totalDegree_zero]
      exact isHomogeneous_zero _ _ _
    · rw [hhom.totalDegree h]; exact hhom
  · exact hhom.totalDegree_le
  · have hcomp : ψ ∘ (Fin.succ : Fin r → Fin (r+1)) = (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k) := by
      funext j
      simp only [Function.comp_apply, hψ, Fin.cases_succ]
    have h0 : ψ (0 : Fin (r+1)) = 1 := by
      simp only [hψ, Fin.cases_zero]
    have h_eval : ∀ n, aeval ψ (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f) *
        X (0 : Fin (r+1)) ^ (f.totalDegree - n)) = homogeneousComponent n f := by
      intro n
      rw [map_mul, map_pow, aeval_rename, aeval_X, hcomp, aeval_X_left_apply, h0, one_pow, mul_one]
    dsimp only [F]
    rw [map_sum]
    have hsum : ∑ x ∈ Finset.range (f.totalDegree + 1),
        aeval ψ (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent x f) *
          X (0 : Fin (r+1)) ^ (f.totalDegree - x))
        = ∑ x ∈ Finset.range (f.totalDegree + 1), homogeneousComponent x f :=
      Finset.sum_congr rfl (fun n _ => h_eval n)
    rw [hsum, sum_homogeneousComponent f]

end Commons.Algebra.MvPolynomial