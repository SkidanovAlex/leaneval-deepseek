/-
  WilG4c — the comparison set `{|U| = |V|}` of two `Ω`-definable graphs.

  If `graphOf U` and `graphOf V` are `Ω`-sets of `ℝ^{N+1}` then the set of points `w` of `ℝ^N`
  with `|U w| = |V w|` is an `Ω`-set: lift the two graphs to the first `N` and the two value
  coordinates of `ℝ^{N+2}` (via `Work.WilG5.coordPre` and the two index maps `inc1`, `inc2`),
  intersect with the `Ω`-set `absSet N = {p | |p uIdx| = |p vIdx|}` (a union of the two
  hypersurfaces `p uIdx = p vIdx` and `p uIdx + p vIdx = 0`), and project the value block away
  with `Work.WilG5.projN 2`; `absEqCombine_set` identifies the result with `{|U| = |V|}`.

  This is the last compatibility set of the `StepLipHigh` refinement list (BNZ §5.5) after the
  `ε`-`δ` derivative relation (`EpsFDerivSetMem`) and the graph of the total `fderiv`
  (`FDerivDirGraphMem`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Plumb.SsetMem
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesConjecture

/-! The auxiliary vocabulary of the comparison-set construction, kept in its own namespace to
avoid clashing with the many other `uIdx`/`vIdx`-style names of the area. -/
namespace SgnEqAux

/-! ## 1. The two index maps and the value coordinates -/

/-- The coordinate of the left value `u` in `Iie^{N+2}`: the `N`-th one. -/
def uIdx (N : ℕ) : Fin (N + 2) := Fin.castSucc (Fin.last N)

/-- The coordinate of the right value `v` in `ℝ^{N+2}`: the last one. -/
def vIdx (N : ℕ) : Fin (N + 2) := Fin.last (N + 1)

/-- The first `N+1` coordinates of `ℝ^{N+2}` (the left graph `(w, u)`). -/
def inc1 (N : ℕ) : Fin (N + 1) → Fin (N + 2) := Fin.castAdd 1

/-- The first `N` coordinates together with the last one (the right graph `(w, v)`). -/
def inc2 (N : ℕ) : Fin (N + 1) → Fin (N + 2) := Fin.snoc (Fin.castAdd 2) (Fin.last (N + 1))

/-! ## 2. Reading the two reindexed graph pieces -/

theorem mem_coordPre_inc1 {N : ℕ} (U : (Fin N → ℝ) → ℝ) (p : Fin (N + 2) → ℝ) :
    p ∈ Work.WilG5.coordPre (inc1 N) (graphOf U) ↔
      p (uIdx N) = U (fun i : Fin N => p (Fin.castAdd 2 i)) := by
  have h1 : (p ∘ inc1 N) (Fin.last N) = p (uIdx N) := rfl
  have h2 : Fin.init (p ∘ inc1 N) = (fun i : Fin N => p (Fin.castAdd 2 i)) := by
    funext i; rfl
  simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf]
  rw [h1, h2]

theorem mem_coordPre_inc2 {N : ℕ} (V : (Fin N → ℝ) → ℝ) (p : Fin (N + 2) → ℝ) :
    p ∈ Work.WilG5.coordPre (inc2 N) (graphOf V) ↔
      p (vIdx N) = V (fun i : Fin N => p (Fin.castAdd 2 i)) := by
  have h1 : (p ∘ inc2 N) (Fin.last N) = p (vIdx N) := by
    simp only [Function.comp_apply, inc2, vIdx, Fin.snoc_last]
  have h2 : Fin.init (p ∘ inc2 N) = (fun i : Fin N => p (Fin.castAdd 2 i)) := by
    funext i; simp only [Fin.init, Function.comp_apply, inc2, Fin.snoc_castSucc]
  simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf]
  rw [h1, h2]

@[simp] theorem append_uIdx {N : ℕ} (w : Fin N → ℝ) (y : Fin 2 → ℝ) :
    Fin.append w y (uIdx N) = y 0 := by
  rw [show uIdx N = Fin.natAdd N (0 : Fin 2) from Fin.ext rfl, Fin.append_right]

@[simp] theorem append_vIdx {N : ℕ} (w : Fin N → ℝ) (y : Fin 2 → ℝ) :
    Fin.append w y (vIdx N) = y 1 := by
  rw [show vIdx N = Fin.natAdd N (1 : Fin 2) from Fin.ext rfl, Fin.append_right]

@[simp] theorem append_castAdd {N : ℕ} (w : Fin N → ℝ) (y : Fin 2 → ℝ) (i : Fin N) :
    Fin.append w y (Fin.castAdd 2 i) = w i := Fin.append_left _ _ i

/-! ## 3. The equality-of-absolute-values set on `ℝ^{N+2}` -/

/-- The set of points of `ℝ^{N+2}` whose `uIdx`- and `vIdx`-coordinates have equal absolute
value. -/
def absSet (N : ℕ) : Set (Fin (N + 2) → ℝ) := {p | |p (uIdx N)| = |p (vIdx N)|}

theorem mem_absSet_iff {N : ℕ} {p : Fin (N + 2) → ℝ} :
    p ∈ absSet N ↔ |p (uIdx N)| = |p (vIdx N)| := Iff.rfl

theorem absSet_eq (N : ℕ) :
    absSet N = {p : Fin (N + 2) → ℝ | p (uIdx N) = p (vIdx N)}
      ∪ {p : Fin (N + 2) → ℝ | p (uIdx N) + p (vIdx N) = 0} := by
  ext p
  simp only [absSet, Set.mem_ofPred_eq, Set.mem_union, abs_eq_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem absSet_mem (S : SOMin) (N : ℕ) : absSet N ∈ S.Ω (N + 2) 2 (N + 2) := by
  rw [absSet_eq]
  have h1 : {p : Fin (N + 2) → ℝ | p (uIdx N) = p (vIdx N)} ∈
      S.Ω (N + 2) 1 (N + 2) := by
    have h := Work.WilG1.Omega.coordEq_mem (S := S) (n := N + 2) 0 (uIdx N) (vIdx N)
    simpa using h
  have h2 : {p : Fin (N + 2) → ℝ | p (uIdx N) + p (vIdx N) = 0} ∈
      S.Ω (N + 2) 1 (N + 2) := by
    have h := S.hyp (N + 2) (MvPolynomial.X (uIdx N) + MvPolynomial.X (vIdx N) :
      MvPolynomial (Fin (N + 2)) ℝ)
    have hset : {p : Fin (N + 2) → ℝ | MvPolynomial.eval p
        (MvPolynomial.X (uIdx N) + MvPolynomial.X (vIdx N) : MvPolynomial (Fin (N + 2)) ℝ) = 0}
        = {p : Fin (N + 2) → ℝ | p (uIdx N) + p (vIdx N) = 0} := by
      ext p; simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_X]
    rw [hset] at h
    refine Work.WilG5.mem_mono h (N + 2) 1 le_rfl ?_
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [max_le_iff]
    exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩
  exact Work.WilG1.Plumb.union_same h1 h2

/-! ## 4. The set-theoretic identification -/

theorem absEqCombine_set (N : ℕ) (U V : (Fin N → ℝ) → ℝ) :
    {w : Fin N → ℝ | |U w| = |V w|} =
      Work.WilG5.projN 2 (Work.WilG5.coordPre (inc1 N) (graphOf U) ∩
        Work.WilG5.coordPre (inc2 N) (graphOf V) ∩ absSet N) := by
  ext w
  simp only [Work.WilG5.projN, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_coordPre_inc1,
    mem_coordPre_inc2, mem_absSet_iff, append_uIdx, append_vIdx, append_castAdd]
  constructor
  · intro h
    exact ⟨![U w, V w], ⟨⟨rfl, rfl⟩, h⟩⟩
  · rintro ⟨y, ⟨⟨hu, hv⟩, habs⟩⟩
    have h1 : |y 0| = |U (fun i => w i)| := congrArg abs hu
    have h2 : |y 1| = |V (fun i => w i)| := congrArg abs hv
    rw [h1, h2] at habs
    exact habs

end SgnEqAux

open SgnEqAux

/-! ## 5. The `Ω`-membership -/

/-- **The comparison set of two `Ω`-graphs is `Ω`.**  Bounds: the format grows by the constant
`64*((N+2)+(N+1)) + 64 + (N+2) + 8` (independent of the degrees), the degree by
`4*(b + b') + (2*(32*((N+2)+(N+1))+32) + 2)`. -/
theorem absEqCombine (S : SOMin) (N : ℕ) :
    ∃ (K m c : ℕ),
      ∀ (A A' : ℕ) (b b' : Polynomial ℕ) (D : ℕ) (U V : (Fin N → ℝ) → ℝ),
        graphOf U ∈ S.Ω A (b.eval D) (N + 1) →
        graphOf V ∈ S.Ω A' (b'.eval D) (N + 1) →
        {w : Fin N → ℝ | |U w| = |V w|} ∈
          S.Ω (A + A' + K) ((Polynomial.C m * (b + b') + Polynomial.C c).eval D) N := by
  refine ⟨64 * ((N + 2) + (N + 1)) + 64 + (N + 2) + 8, 4,
    2 * (32 * ((N + 2) + (N + 1)) + 32) + 2, ?_⟩
  intro A A' b b' D U V hU hV
  have hUc := Work.WilG5.coordPre_mem (S := S) (ι := inc1 N) hU
  have hVc := Work.WilG5.coordPre_mem (S := S) (ι := inc2 N) hV
  have ha := absSet_mem S N
  set Fm : ℕ := A + A' + (64 * ((N + 2) + (N + 1)) + 64) + (N + 2) with hFm
  have hU2 : Work.WilG5.coordPre (inc1 N) (graphOf U) ∈
      S.Ω Fm (b.eval D + (32 * ((N + 2) + (N + 1)) + 32)) (N + 2) :=
    Work.WilG5.mem_mono hUc Fm _ (by simp only [hFm]; omega) le_rfl
  have hV2 : Work.WilG5.coordPre (inc2 N) (graphOf V) ∈
      S.Ω Fm (b'.eval D + (32 * ((N + 2) + (N + 1)) + 32)) (N + 2) :=
    Work.WilG5.mem_mono hVc Fm _ (by simp only [hFm]; omega) le_rfl
  have hUV := Work.WilG1.Plumb.inter_same hU2 hV2
  have ha2 : absSet N ∈ S.Ω (Fm + 1) 2 (N + 2) :=
    Work.WilG5.mem_mono ha (Fm + 1) 2 (by simp only [hFm]; omega) le_rfl
  have hW := Work.WilG1.Plumb.inter_same hUV ha2
  have hproj := Work.WilG5.projN_mem (S := S) (n := N) 2 (Fm + 1 + 1) _ hW
  rw [absEqCombine_set N U V]
  refine Work.WilG5.mem_mono hproj
    (A + A' + (64 * ((N + 2) + (N + 1)) + 64 + (N + 2) + 8))
    ((Polynomial.C 4 * (b + b') + Polynomial.C (2 * (32 * ((N + 2) + (N + 1)) + 32) + 2)).eval D)
    ?_ ?_
  · simp only [hFm]; omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]; omega

end Work.WilG4c
