/-
  Area G4b: helper lemmas for the final assembly `G4_bdd_dx_proved`.

  * `fin1_ext` : an element of `Fin 1 → ℝ` is determined by its coordinate;
  * `thrSet_mem_unif` : uniform `Ω`-definability of the threshold sets `thrSet G K`
    (the `∀ G` form of `Work.WilG4b.thrSet_mem`, whose witnesses only depend on the format and
    the degree budget);
  * `ivl_mem` : the interval `(c,d)` is an `Ω`-subset of `ℝ¹`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.thrSet_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical MeasureTheory Filter
open scoped Topology

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-- An element of `Fin 1 → ℝ` is determined by its coordinate. -/
theorem fin1_ext (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
  funext i
  rw [Subsingleton.elim i 0]

/-- **Uniform `Ω`-definability of the threshold sets.**  For a fixed format `F`, the threshold
set `thrSet G K` of a definable one-variable function is `Ω`-definable with format and degree
depending only on `F` and on the degree budget `D` of the graph — not on `G`, `K`.  This is the
`∀ G` form of `Work.WilG4b.thrSet_mem`, whose explicit witnesses only depend on `F` and `D`. -/
theorem thrSet_mem_unif (S : SOMin) (hder : S.SharpDeriv) (F : ℕ) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (G : ℝ → ℝ),
      graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2 →
      ∀ (t : ℝ), {x : Fin 1 → ℝ | x 0 ∈ thrSet G t} ∈ S.Ω (F + K) (p.eval D) 1 := by
  obtain ⟨a, b, hb⟩ := hder F 1
  refine ⟨max a (max 6 6) + 1 + 1,
    Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4), ?_⟩
  intro D G hG t
  have hDg : thrDeriGraph G ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) 2 :=
    hb D (thrDinG G) hG 1 (fun _ : Fin 1 => 0)
  have hDgp : thrDeriGraph G ∈ S.Ω a (Polynomial.eval D (Work.WilG1.psubst b 1)) 2 := by
    rw [Work.WilG1.eval_psubst]; exact hDg
  have hPosc : thrPosHalf t ∈ S.Ω 6 (Polynomial.eval D (Polynomial.C 4)) 2 := by
    rw [Polynomial.eval_C]; exact thrPosHalf_mem S t
  have hNegc : thrNegHalf t ∈ S.Ω 6 (Polynomial.eval D (Polynomial.C 4)) 2 := by
    rw [Polynomial.eval_C]; exact thrNegHalf_mem S t
  have hU : thrPosHalf t ∪ thrNegHalf t ∈
      S.Ω (max 6 6) (Polynomial.eval D (Polynomial.C 4 + Polynomial.C 4)) 2 :=
    Work.WilG1.Omega.union₂ hPosc hNegc
  have hInt : thrDeriGraph G ∩ (thrPosHalf t ∪ thrNegHalf t) ∈
      S.Ω (max a (max 6 6) + 1)
        (Polynomial.eval D (Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4))) 2 :=
    Work.WilG1.Omega.inter₂ hDgp hU
  have hproj := S.proj hInt
  have hset : projLast (thrDeriGraph G ∩ (thrPosHalf t ∪ thrNegHalf t))
      = {x : Fin 1 → ℝ | x 0 ∈ thrSet G t} := by
    ext x
    constructor
    · rintro ⟨M, hM⟩
      obtain ⟨hDgM, hUM⟩ :=
        (Set.mem_inter_iff (Fin.snoc x M) (thrDeriGraph G) (thrPosHalf t ∪ thrNegHalf t)).mp hM
      simp only [thrDeriGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hDgM
      obtain ⟨hint, hMval⟩ := hDgM
      have hc : ContDiffAt ℝ 1 G (x 0) := (thrMem_interior_c1 G x).1 hint
      have hit := thrIteratedFDeriv G x hc
      have hUM' : t < M ∨ M < -t := by
        rcases (Set.mem_union (Fin.snoc x M) (thrPosHalf t) (thrNegHalf t)).mp hUM with h | h
        · exact Or.inl (by simpa only [thrPosHalf, Set.mem_ofPred_eq, Fin.snoc_last] using h)
        · exact Or.inr (by simpa only [thrNegHalf, Set.mem_ofPred_eq, Fin.snoc_last] using h)
      simp only [thrSet, Set.mem_ofPred_eq]
      refine ⟨hc, ?_⟩
      rw [← hit, ← hMval, lt_abs]
      rcases hUM' with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · intro hx
      simp only [thrSet, Set.mem_ofPred_eq] at hx
      obtain ⟨hc, hlt⟩ := hx
      have hint : x ∈ interior {z : Fin 1 → ℝ | ContDiffAt ℝ 1 (thrDinG G) z} :=
        (thrMem_interior_c1 G x).2 hc
      let M : ℝ := iteratedFDeriv ℝ 1 (thrDinG G) x (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)
      have hit : M = deriv G (x 0) := thrIteratedFDeriv G x hc
      refine ⟨M, ?_⟩
      refine (Set.mem_inter_iff (Fin.snoc x M) (thrDeriGraph G)
        (thrPosHalf t ∪ thrNegHalf t)).mpr ⟨?_, ?_⟩
      · simp only [thrDeriGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hint, rfl⟩
      · refine (Set.mem_union (Fin.snoc x M) (thrPosHalf t) (thrNegHalf t)).mpr ?_
        rcases (lt_abs.mp hlt) with h | h
        · left
          simp only [thrPosHalf, Set.mem_ofPred_eq, Fin.snoc_last]
          rw [hit]; exact h
        · right
          simp only [thrNegHalf, Set.mem_ofPred_eq, Fin.snoc_last]
          rw [hit]; linarith
  rw [hset] at hproj
  exact Work.WilG5.mem_mono hproj (F + (max a (max 6 6) + 1 + 1))
    (Polynomial.eval D (Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4)))
    (by omega) le_rfl

/-- The interval `(c,d)` of `ℝ¹` is an `Ω`-set. -/
theorem ivl_mem (S : SOMin) (c d : ℝ) :
    ({x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d}) ∈ S.Ω 25 16 1 := by
  have h1 : ({x : Fin 1 → ℝ | c < x 0}) ∈ S.Ω 24 8 1 := by
    simpa using Work.WilG5.ltSet_mem (S := S) (n := 1) (0 : Fin 1) c
  have h2 : ({x : Fin 1 → ℝ | x 0 < d}) ∈ S.Ω 24 8 1 := by
    simpa using Work.WilG5.gtSet_mem (S := S) (n := 1) (0 : Fin 1) d
  have h3 := S.inter (F := 24) (n := 1) (k := 2) (fun _ : Fin 2 => 8)
    (fun i : Fin 2 => if i = 0 then {x : Fin 1 → ℝ | c < x 0} else {x : Fin 1 → ℝ | x 0 < d})
    (by intro i; fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [Work.WilG1.Omega.iInter_fin_two] at h3
  have hsum : (∑ _ : Fin 2, 8) = 16 := by simp
  rw [hsum] at h3
  convert h3 using 1
  ext x
  simp [Set.mem_Ioo]

end Work.WilG4b
