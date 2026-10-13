import Submission.Work.WilkiesD.Proj

namespace Work.WilkiesD.Omg

open WilkiesDesign WilkiesConjecture

/-- Auxiliary form of `projFst_mem_Omega`, with `F` and `D` universally quantified so that
the induction on the number of projected coordinates can step the format counter. -/
private theorem projFst_mem_Omega_aux {S : SOMin} {n : ℕ} (m : ℕ) :
    ∀ (F D : ℕ) (A : Set (Fin (n + m) → ℝ)),
      A ∈ S.Ω F D (n + m) → projFst m A ∈ S.Ω (F + m) D n := by
  induction m with
  | zero =>
      intro F D A hA
      simpa using hA
  | succ m ih =>
      intro F D A hA
      rw [projFst_succ]
      have hproj : projLast A ∈ S.Ω (F + 1) D (n + m) := S.proj hA
      have hih := ih (F + 1) D (projLast A) hproj
      have hEq : (F + 1) + m = F + (m + 1) := by ac_rfl
      rwa [hEq] at hih

/-- Pushing a set lying in `S.Ω F D (n+m)` through the projection `projFst m` onto the first `n`
coordinates (the `m`-fold iterate of `projLast`, defined in `Submission/Work/WilkiesD/Proj.lean`)
increases the format counter by `m` and leaves the degree counter unchanged. -/
theorem projFst_mem_Omega {S : SOMin} {n : ℕ} (m F D : ℕ) (A : Set (Fin (n + m) → ℝ))
    (hA : A ∈ S.Ω F D (n + m)) : projFst m A ∈ S.Ω (F + m) D n :=
  projFst_mem_Omega_aux m F D A hA

end Work.WilkiesD.Omg
