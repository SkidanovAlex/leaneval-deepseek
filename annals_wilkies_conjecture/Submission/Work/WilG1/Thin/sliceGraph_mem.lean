/-
  WilG1 / Thin — slicing the graph of a definable function at a parameter.

  Given `G : ℝ^{p+1} → ℝ` with `graphOf G ∈ S.Ω F D (p+2)` and a point `x : ℝ^p`, the set

      `graphOf (fun u : ℝ → ℝ => G (Fin.snoc x (u 0)))`

  is the slice of `graphOf G` over the first `p` coordinates fixed to `x`; it is again
  `Ω`-definable, at a format independent of `D` and a degree polynomial in `D`.

  The proof has three steps, all of them elementary:
  * `sliceAux_mem` intersects `graphOf G` with the `p` coordinate hyperplanes
    `z (Fin.castAdd 2 i) = x i` (each a hypersurface of a *linear* polynomial, so its
    `Ω`-degree is `≤ 1` uniformly in `x`);
  * `sliceCoordImage_eq` identifies the image of that set under the index map
    `sliceIdx p : Fin 2 → Fin (p+2)` (coordinates `p` and `p+1`) with the sliced graph;
  * `Work.WilG5.coordImage_mem` (from `WilG5.Reindex3`) supplies the `Ω`-membership of the
    coordinate image, with its explicit format/degree bounds.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.projLastIter_mem

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture

/-! ## 1. Reading and writing `Fin.snoc` -/

theorem snoc_castSucc_eq {n : ℕ} (y : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (Fin.snoc y c : Fin (n + 1) → ℝ) (Fin.castSucc i) = y i := Fin.snoc_castSucc _ _ _

theorem snoc_last_eq {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    (Fin.snoc y c : Fin (n + 1) → ℝ) (Fin.last n) = c := Fin.snoc_last _ _

theorem init_snoc_eq {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    Fin.init (Fin.snoc y c : Fin (n + 1) → ℝ) = y := Fin.init_snoc _ _

theorem snoc_castAdd_eq {n : ℕ} (y : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (Fin.snoc y c : Fin (n + 1) → ℝ) (Fin.castAdd 1 i) = y i := by
  rw [show (Fin.castAdd 1 i : Fin (n + 1)) = (Fin.castSucc i) from Fin.ext rfl]
  exact Fin.snoc_castSucc _ _ _

/-! ## 2. The index map selecting the last two coordinates -/

/-- `sliceIdx p : Fin 2 → Fin (p+2)` selects the coordinates `p` and `p+1`, i.e. the two
coordinates that survive when the first `p` coordinates are fixed. -/
def sliceIdx (p : ℕ) : Fin 2 → Fin (p + 2) := ![⟨p, by omega⟩, Fin.last (p + 1)]

theorem sliceIdx_zero (p : ℕ) : sliceIdx p 0 = (⟨p, by omega⟩ : Fin (p + 2)) := rfl
theorem sliceIdx_one (p : ℕ) : sliceIdx p 1 = (Fin.last (p + 1) : Fin (p + 2)) := rfl

/-! ## 3. The sliced graph as a coordinate image -/

theorem sliceCoordImage_eq {p : ℕ} (G : (Fin (p + 1) → ℝ) → ℝ) (x : Fin p → ℝ) :
    Work.WilG5.coordImage (sliceIdx p)
        (graphOf G ∩ ⋂ i : Fin p, {z : Fin (p + 2) → ℝ | z (Fin.castAdd 2 i) = x i})
      = graphOf (fun u : Fin 1 → ℝ => G (Fin.snoc x (u 0))) := by
  ext u
  constructor
  · rintro ⟨z, hz, hzu⟩
    rw [Set.mem_inter_iff, Set.mem_iInter] at hz
    obtain ⟨hzG, hzfix⟩ := hz
    have hzG' : z (Fin.last (p + 1)) = G (Fin.init z) := hzG
    have h0 : z (⟨p, by omega⟩ : Fin (p + 2)) = u 0 := by
      have h := congrFun hzu 0
      simp only [Function.comp_apply] at h
      rw [sliceIdx_zero] at h
      exact h
    have h1 : z (Fin.last (p + 1)) = u (Fin.last 1) := by
      have h := congrFun hzu 1
      simp only [Function.comp_apply] at h
      rw [sliceIdx_one] at h
      exact h
    have hinit : Fin.init z = (Fin.snoc x (u 0) : Fin (p + 1) → ℝ) := by
      funext j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · show z (Fin.castSucc j').castSucc =
          (Fin.snoc x (u 0) : Fin (p + 1) → ℝ) (Fin.castSucc j')
        rw [snoc_castSucc_eq,
          show (Fin.castSucc j').castSucc = (Fin.castAdd 2 j' : Fin (p + 2)) from Fin.ext rfl]
        exact hzfix j'
      · show z (Fin.last p).castSucc = (Fin.snoc x (u 0) : Fin (p + 1) → ℝ) (Fin.last p)
        rw [snoc_last_eq,
          show (Fin.last p).castSucc = (⟨p, by omega⟩ : Fin (p + 2)) from Fin.ext rfl]
        exact h0
    have hiu : (Fin.init u) 0 = u 0 := rfl
    show u (Fin.last 1) = G (Fin.snoc x ((Fin.init u) 0))
    rw [hiu, ← h1, ← hinit]
    exact hzG'
  · intro hu
    have hu' : u (Fin.last 1) = G (Fin.snoc x ((Fin.init u) 0)) := hu
    have hiu : (Fin.init u) 0 = u 0 := rfl
    rw [hiu] at hu'
    refine ⟨(Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ), ?_, ?_⟩
    · rw [Set.mem_inter_iff, Set.mem_iInter]
      refine ⟨?_, fun i => ?_⟩
      · show (Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ) (Fin.last (p + 1)) =
          G (Fin.init (Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ))
        rw [snoc_last_eq, init_snoc_eq]
        exact hu'
      · show (Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ) (Fin.castAdd 2 i) = x i
        rw [show (Fin.castAdd 2 i : Fin (p + 2)) = (Fin.castSucc (Fin.castAdd 1 i)) from Fin.ext rfl,
          snoc_castSucc_eq, snoc_castAdd_eq]
    · funext j
      fin_cases j
      · show (Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ) (sliceIdx p 0) = u 0
        rw [sliceIdx_zero,
          show (⟨p, by omega⟩ : Fin (p + 2)) = (Fin.last p).castSucc from Fin.ext rfl,
          snoc_castSucc_eq, snoc_last_eq]
      · show (Fin.snoc (Fin.snoc x (u 0)) (u (Fin.last 1)) : Fin (p + 2) → ℝ) (sliceIdx p 1) = u 1
        rw [sliceIdx_one, snoc_last_eq]
        rfl

/-! ## 4. The intermediate `Ω`-set: `graphOf G` with the first `p` coordinates fixed -/

/-- The coordinate hyperplane `{z | z i = c}` is `Ω`-definable at format `n` and degree `1`
(even for a nonzero constant `c`, since `X i - C c` is a linear polynomial). -/
theorem coordEqSet_mem {S : WilkiesDesign.SOMin} {n D : ℕ} (i : Fin n) (c : ℝ) :
    {z : Fin n → ℝ | z i = c} ∈ S.Ω n (D + 1) n := by
  have h := S.hyp n (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ)
  have hset : {z : Fin n → ℝ | MvPolynomial.eval z
        (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = 0}
      = {z : Fin n → ℝ | z i = c} := by
    ext z
    simp [MvPolynomial.eval_sub, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG5.mem_mono h n (D + 1) le_rfl ?_
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · simp
  · exact le_trans (Work.WilG5.td_C_le c) (Nat.zero_le _)

/-- `graphOf G` with the first `p` coordinates fixed to `x`, with explicit bounds:
format `max F (max F (p+2) + 1) + 1`, degree `D + p * (D + 1)`. -/
theorem sliceAux_mem {S : WilkiesDesign.SOMin} {p F D : ℕ}
    (G : (Fin (p + 1) → ℝ) → ℝ) (hG : WilkiesDesign.graphOf G ∈ S.Ω F D (p + 2))
    (x : Fin p → ℝ) :
    WilkiesDesign.graphOf G ∩ (⋂ i : Fin p,
        {z : Fin (p + 2) → ℝ | z (Fin.castAdd 2 i) = x i}) ∈
      S.Ω (max F (max F (p + 2) + 1) + 1)
        ((Polynomial.X + Polynomial.C p * (Polynomial.X + Polynomial.C 1)).eval D) (p + 2) := by
  have hH : ∀ i : Fin p, {z : Fin (p + 2) → ℝ | z (Fin.castAdd 2 i) = x i} ∈
      S.Ω (max F (p + 2)) (D + 1) (p + 2) := by
    intro i
    exact Work.WilG5.mem_mono (coordEqSet_mem (S := S) (n := p + 2) (D := D)
      (Fin.castAdd 2 i) (x i)) (max F (p + 2)) (D + 1) (le_max_right _ _) le_rfl
  have hInter := Work.WilG1.Omega.inter_mem (S := S) (n := p + 2) (k := p)
    (a := max F (p + 2)) (b := Polynomial.X + Polynomial.C 1) (D := D)
    (fun i : Fin p => {z : Fin (p + 2) → ℝ | z (Fin.castAdd 2 i) = x i})
    (by intro i; simpa using hH i)
  have hG' : WilkiesDesign.graphOf G ∈ S.Ω F (Polynomial.X.eval D) (p + 2) := by
    simpa using hG
  exact Work.WilG1.Omega.inter₂ (S := S) hG' hInter

/-! ## 5. The slice -/

theorem sliceGraph_mem {S : WilkiesDesign.SOMin} {p F D : ℕ}
    (G : (Fin (p + 1) → ℝ) → ℝ) (hG : WilkiesDesign.graphOf G ∈ S.Ω F D (p + 2))
    (x : Fin p → ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      WilkiesDesign.graphOf (fun u : Fin 1 → ℝ => G (Fin.snoc x (u 0))) ∈ S.Ω a (b.eval D) 2 := by
  have hB := sliceAux_mem (S := S) G hG x
  have hCI := Work.WilG5.coordImage_mem (S := S) (m := 2) (N := p + 2) (ι := sliceIdx p) hB
  rw [sliceCoordImage_eq G x] at hCI
  refine ⟨max F (max F (p + 2) + 1) + 1 + 64 * ((p + 2) + 2) + 64,
    Polynomial.X + Polynomial.C p * (Polynomial.X + Polynomial.C 1) +
      Polynomial.C (32 * ((p + 2) + 2)) + Polynomial.C 32, ?_⟩
  simpa [Polynomial.eval_add] using hCI

end Work.WilG1.Thin
