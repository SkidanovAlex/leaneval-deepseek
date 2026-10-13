import Mathlib
import Submission.Work.WilkiesH.Strat.omega_closure_defs

/-!
# The joint set of an `Ω`-set is `Ω`-definable

`jointSet W ⊆ ℝ^(n + (n+1))` is the set of triples `(y, x, t)` with `y ∈ W`, `t > 0` and
`(x i - y i)² < t²` for all `i`.  It is built from the `Ω`-sets

* `Work.WilG5.coordPre (yIdx n) W` — the witness condition `y ∈ W`
  (`Work.WilG5.coordPre_mem`, format `F + 64·((n+(n+1)) + n) + 64`,
  degree `D + 32·((n+(n+1)) + n) + 32`);
* the `n` box conditions `boxSet n i` — the strict polynomial inequality
  `(x i - y i)² - t² < 0` (`Work.WilkiesH.Omega.omega_poly_lt`, format `N + 3`, degree `4`);
* the positivity `posSet N (tIdx n)` of the radius (`Work.WilG5.ltSet_mem`,
  format `4N + 20`, degree `8`),

closed under binary intersections (`SOMin.inter`: one more format, degrees added).
The format `4N + 20` and the box format `N + 3` are dominated by the `coordPre` format,
which is at least `64·N + 64`; the resulting format is `F₀ + 2 ≤ F₀ + N + 16`, and the
degree `D₀ + 4n + 8` is exactly the stated one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-- Each box condition `(x i - y i)² - t² < 0` is `Ω`-definable, at format `n + (n+1) + 3`
and degree `4`: the polynomial `boxPoly n i` has total degree `≤ 2`, and a strict polynomial
inequality costs one projection and two degrees. -/
lemma boxSet_mem (S : WilkiesDesign.SOMin) (n : ℕ) (i : Fin n) :
    boxSet n i ∈ S.Ω (n + (n + 1) + 3) 4 (n + (n + 1)) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (n + (n + 1)) (boxPoly n i)
  have hdeg : (boxPoly n i).totalDegree + 2 ≤ 4 := by
    have h2 := boxPoly_totalDegree_le n i
    omega
  show {z : Fin (n + (n + 1)) → ℝ | (boxPoly n i).eval z < 0} ∈ _
  exact Work.WilG5.mem_mono h _ _ le_rfl hdeg

/-- Positivity of a single coordinate is `Ω`-definable, at format `4N + 20` and degree `8`. -/
lemma posSet_mem (S : WilkiesDesign.SOMin) (N : ℕ) (j : Fin N) :
    posSet N j ∈ S.Ω (4 * N + 20) 8 N :=
  Work.WilG5.ltSet_mem (S := S) j 0

/-- Positivity of the radius coordinate inside `jointSet`. -/
lemma posSet_tIdx_mem (S : WilkiesDesign.SOMin) (n : ℕ) :
    posSet (n + (n + 1)) (tIdx n) ∈ S.Ω (4 * (n + (n + 1)) + 20) 8 (n + (n + 1)) :=
  posSet_mem S (n + (n + 1)) (tIdx n)

theorem omega_closure_joint_mem {S : WilkiesDesign.SOMin} {n F D : ℕ} {W : Set (Fin n → ℝ)}
    (hW : W ∈ S.Ω F D n) :
    jointSet W ∈ S.Ω (F + 64 * ((n + (n + 1)) + n) + 64 + (n + (n + 1)) + 16)
      (D + 32 * ((n + (n + 1)) + n) + 32 + 4 * n + 8) (n + (n + 1)) := by
  -- the witness condition
  have hC : Work.WilG5.coordPre (yIdx n) W ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64)
        (D + 32 * ((n + (n + 1)) + n) + 32) (n + (n + 1)) :=
    Work.WilG5.coordPre_mem (S := S) (ι := yIdx n) (A := W) hW
  -- the box conditions
  have hbox : ∀ i : Fin n, boxSet n i ∈ S.Ω (n + (n + 1) + 3) 4 (n + (n + 1)) :=
    fun i => boxSet_mem S n i
  have hB : (⋂ i : Fin n, boxSet n i) ∈ S.Ω (n + (n + 1) + 4) (n * 4) (n + (n + 1)) := by
    have h := S.inter (fun _ : Fin n => 4) (fun i : Fin n => boxSet n i) hbox
    rw [show (∑ _ : Fin n, (4 : ℕ)) = n * 4 from by simp] at h
    exact h
  -- the radius positivity
  have hP : posSet (n + (n + 1)) (tIdx n) ∈
      S.Ω (4 * (n + (n + 1)) + 20) 8 (n + (n + 1)) :=
    posSet_tIdx_mem S n
  -- all three at the common format `F₀ = F + 64·((n+(n+1)) + n) + 64`
  have hB' : (⋂ i : Fin n, boxSet n i) ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64) (n * 4) (n + (n + 1)) :=
    Work.WilG5.mem_mono hB _ _ (by omega) le_rfl
  have hP' : posSet (n + (n + 1)) (tIdx n) ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64) 8 (n + (n + 1)) :=
    Work.WilG5.mem_mono hP _ _ (by omega) le_rfl
  have hP'' : posSet (n + (n + 1)) (tIdx n) ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64 + 1) 8 (n + (n + 1)) :=
    Work.WilG5.mem_mono hP' _ _ (by omega) le_rfl
  -- first intersection: witness ∩ boxes
  have hInt1 : Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i) ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64 + 1)
        (D + 32 * ((n + (n + 1)) + n) + 32 + n * 4) (n + (n + 1)) := by
    have h := S.inter (fun j : Fin 2 => if j = 0 then
          D + 32 * ((n + (n + 1)) + n) + 32 else n * 4)
      (fun j : Fin 2 => if j = 0 then Work.WilG5.coordPre (yIdx n) W
        else (⋂ i : Fin n, boxSet n i))
      (by
        intro j
        fin_cases j
        · simpa using hC
        · simpa using hB')
    rw [show (∑ j : Fin 2, (if j = 0 then
          D + 32 * ((n + (n + 1)) + n) + 32 else n * 4))
        = (D + 32 * ((n + (n + 1)) + n) + 32) + n * 4 from by
      simp [Fin.sum_univ_two]] at h
    have hset : (⋂ j : Fin 2, (if j = 0 then Work.WilG5.coordPre (yIdx n) W
        else (⋂ i : Fin n, boxSet n i)))
        = Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i) := by
      ext z; simp [Fin.forall_fin_two]
    rwa [hset] at h
  -- second intersection: (witness ∩ boxes) ∩ {t > 0}
  have hInt2 : (Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i)) ∩
      posSet (n + (n + 1)) (tIdx n) ∈
      S.Ω (F + 64 * ((n + (n + 1)) + n) + 64 + 2)
        (D + 32 * ((n + (n + 1)) + n) + 32 + n * 4 + 8) (n + (n + 1)) := by
    have h := S.inter (fun j : Fin 2 => if j = 0 then
          D + 32 * ((n + (n + 1)) + n) + 32 + n * 4 else 8)
      (fun j : Fin 2 => if j = 0 then
        Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i)
        else posSet (n + (n + 1)) (tIdx n))
      (by
        intro j
        fin_cases j
        · simpa using hInt1
        · simpa using hP'')
    rw [show (∑ j : Fin 2, (if j = 0 then
          D + 32 * ((n + (n + 1)) + n) + 32 + n * 4 else 8))
        = (D + 32 * ((n + (n + 1)) + n) + 32 + n * 4) + 8 from by
      simp [Fin.sum_univ_two]] at h
    have hset : (⋂ j : Fin 2, (if j = 0 then
        Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i)
        else posSet (n + (n + 1)) (tIdx n)))
        = (Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i)) ∩
            posSet (n + (n + 1)) (tIdx n) := by
      ext z; simp [Fin.forall_fin_two]
    rwa [hset] at h
  exact Work.WilG5.mem_mono hInt2 _ _ (by omega) (by omega)

end Work.WilkiesH.Strat
