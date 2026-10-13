/-
  WilE8/Ocube — the open cube `(-1,1)^n` is a `Star`-set of format `n` and degree `2n+1`.

  The single basic semi-Pfaffian condition is the strict inequality
  `∏ i, (1 - x_i^2) > 0`; on the closed cube `[-1,1]^n` this says exactly
  that every coordinate is strictly between `-1` and `1`, i.e. it cuts out
  the open cube. Its atom degree is `2n + 1`.
-/
import Mathlib
import Submission.Work.WilE8.Basic

namespace Work.WilE8.Ocube

open WilkiesDesign WilkiesDesign.E

noncomputable section

/-- The polynomial `∏ i, (1 - x_i^2)`, in the variable set `Fin k ⊕ Fin 0` (only the `inl`
variables, i.e. the `x_i`, occur). -/
def cubePoly (k : ℕ) : MvPolynomial (Fin k ⊕ Fin 0) ℝ :=
  ∏ i : Fin k, (1 - (MvPolynomial.X (Sum.inl i)) ^ 2)

/-- The semi-Pfaffian set (one basic set, no exponential chain) cutting out the open cube. -/
def ocubeSemiPf (k : ℕ) : SemiPf k :=
  ⟨0, EAChain.nil k, [⟨[], [cubePoly k]⟩]⟩

/-- The `Star`-piece realising the open cube: the connected component of `ocubeSemiPf n` at the
origin is the open cube, and `ocubeSemiPf n` lives in dimension `n = n + 0`. -/
def ocubePiece (n : ℕ) : StarPiece n := ⟨0, ocubeSemiPf (n + 0), 0⟩

/-- Evaluation of `cubePoly`: it is the product of `1 - x_i^2`. -/
lemma eaEval_cubePoly (k : ℕ) (x : Fin k → ℝ) :
    eaEval (EAChain.nil k) (cubePoly k) x = ∏ i, (1 - x i ^ 2) := by
  rw [eaEval, cubePoly]
  simp only [map_prod, map_sub, map_one, map_pow, MvPolynomial.eval_X, Sum.elim_inl]

/-- The total degree of `cubePoly k` is at most `2 * k`. -/
lemma totalDegree_cubePoly_le (k : ℕ) : (cubePoly k).totalDegree ≤ 2 * k := by
  rw [cubePoly]
  have hfac : ∀ i : Fin k,
      (1 - (MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ).totalDegree ≤ 2 := by
    intro i
    calc (1 - (MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ).totalDegree
        ≤ max (1 : MvPolynomial (Fin k ⊕ Fin 0) ℝ).totalDegree
            ((MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ = 2 := by rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X_pow]; norm_num
  calc (∏ i : Fin k,
          (1 - (MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ)).totalDegree
      ≤ ∑ i : Fin k,
          (1 - (MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ).totalDegree := by
        simpa using MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin k))
          (fun i : Fin k => (1 - (MvPolynomial.X (Sum.inl i)) ^ 2 : MvPolynomial (Fin k ⊕ Fin 0) ℝ))
    _ ≤ ∑ _i : Fin k, 2 := Finset.sum_le_sum (fun i _ => hfac i)
    _ = 2 * k := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- The degree of the semi-Pfaffian set cutting out the open cube is `2k+1`. -/
lemma ocubeSemiPf_deg_le (k : ℕ) : (ocubeSemiPf k).deg ≤ 2 * k + 1 := by
  have h : (ocubeSemiPf k).deg = (cubePoly k).totalDegree + 1 := by
    simp only [SemiPf.deg, Basic.deg, ocubeSemiPf, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, atomDeg]
  rw [h]
  have := totalDegree_cubePoly_le k
  omega

/-- The single basic set holds exactly when `∏ i, (1 - x_i^2) > 0`. -/
lemma holds_cube (k : ℕ) (x : Fin k → ℝ) :
    (⟨[], [cubePoly k]⟩ : Basic k 0).holds (EAChain.nil k) x ↔ 0 < ∏ i, (1 - x i ^ 2) := by
  simp only [Basic.holds, List.not_mem_nil, List.mem_singleton, forall_eq]
  simp only [eaEval_cubePoly]
  simp

/-- On the closed cube, `∏ i, (1 - x_i^2) > 0` is equivalent to being in the open cube. -/
lemma cubeC_prod_pos_iff (k : ℕ) (x : Fin k → ℝ) :
    x ∈ cubeC k ∧ 0 < ∏ i, (1 - x i ^ 2) ↔ x ∈ ocube k := by
  rw [mem_ocube]
  constructor
  · rintro ⟨hx, hprod⟩ i
    have hfac : 1 - x i ^ 2 ≠ 0 := by
      intro h0
      have hz : (∏ j, (1 - x j ^ 2)) = 0 :=
        Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, h0⟩
      rw [hz] at hprod
      exact lt_irrefl 0 hprod
    have hle : |x i| ≤ 1 := hx i
    rw [abs_le] at hle
    rw [abs_lt]
    constructor
    · by_contra h
      have h' : x i ≤ -1 := not_lt.mp h
      exact hfac (by have h1 : x i = -1 := le_antisymm h' hle.1; rw [h1]; norm_num)
    · by_contra h
      have h' : 1 ≤ x i := not_lt.mp h
      exact hfac (by have h1 : x i = 1 := le_antisymm hle.2 h'; rw [h1]; norm_num)
  · rintro hx
    refine ⟨fun i => le_of_lt (hx i), ?_⟩
    apply Finset.prod_pos
    intro i _
    have h := hx i
    rw [abs_lt] at h
    nlinarith [h.1, h.2]

/-- The semi-Pfaffian set cuts out the open cube. -/
lemma ocubeSemiPf_set (k : ℕ) : (ocubeSemiPf k).set = ocube k := by
  ext x
  dsimp only [ocubeSemiPf]
  simp only [SemiPf.set, Set.mem_ofPred_eq]
  simp only [List.mem_singleton, exists_eq_left]
  rw [holds_cube]
  exact cubeC_prod_pos_iff k x

/-- The open cube as a product of open intervals. -/
lemma ocube_eq (k : ℕ) : ocube k = Set.univ.pi (fun _ : Fin k => Set.Ioo (-1 : ℝ) 1) := by
  ext x
  simp only [mem_ocube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, abs_lt]

lemma ocube_convex (k : ℕ) : Convex ℝ (ocube k) := by
  rw [ocube_eq]
  exact convex_pi fun _ _ => convex_Ioo (-1 : ℝ) 1

lemma ocube_preconnected (k : ℕ) : IsPreconnected (ocube k) := (ocube_convex k).isPreconnected

lemma zero_mem_ocube (k : ℕ) : (0 : Fin k → ℝ) ∈ ocube k := fun i => by simp

lemma connectedComponentIn_ocube (k : ℕ) :
    connectedComponentIn (ocube k) (0 : Fin k → ℝ) = ocube k := by
  refine Set.Subset.antisymm (connectedComponentIn_subset _ _) ?_
  exact IsPreconnected.subset_connectedComponentIn (ocube_preconnected k) (zero_mem_ocube k)
    (subset_refl _)

/-- Projection to the first `n` coordinates does not change the open cube. -/
lemma projFirst_image_ocube (n m : ℕ) : projFirst n m '' ocube (n + m) = ocube n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨z, hz, rfl⟩ i
    exact hz (Fin.castAdd m i)
  · intro x hx
    refine ⟨fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0, ?_, ?_⟩
    · intro i
      by_cases h : (i : ℕ) < n
      · simpa [h] using hx ⟨(i : ℕ), h⟩
      · simp [h]
    · funext i
      have h : ((Fin.castAdd m i : Fin (n + m)) : ℕ) < n := by
        rw [Fin.val_castAdd]; exact i.isLt
      show (if h' : ((Fin.castAdd m i : Fin (n + m)) : ℕ) < n then
          x ⟨((Fin.castAdd m i : Fin (n + m)) : ℕ), h'⟩ else 0) = x i
      rw [dite_eq_left h]
      exact congrArg x (Fin.ext (by rw [Fin.val_castAdd]))

/-- The `Star`-piece has `.set` equal to the open cube. -/
lemma ocubePiece_set (n : ℕ) : (ocubePiece n).set = ocube n := by
  show projFirst n 0 '' connectedComponentIn (ocubeSemiPf (n + 0)).set
      (0 : Fin (n + 0) → ℝ) = ocube n
  rw [ocubeSemiPf_set, connectedComponentIn_ocube, projFirst_image_ocube]

theorem ocube_star (n : ℕ) :
    WilkiesDesign.E.Star n (2 * n + 1) n (Work.WilE8.ocube n) := by
  refine ⟨[ocubePiece n], ?_, ?_, ?_⟩
  · rw [← ocubePiece_set n]
    ext x
    rw [mem_list_iUnion]
    constructor
    · intro hx
      exact ⟨ocubePiece n, by simp, hx⟩
    · rintro ⟨P, hP, hx⟩
      rw [List.mem_singleton] at hP
      subst hP
      exact hx
  · intro P hP
    rw [List.mem_singleton] at hP
    subst hP
    show (n + 0) + 0 ≤ n
    omega
  · simp only [ocubePiece, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := ocubeSemiPf_deg_le (n + 0)
    omega

end

end Work.WilE8.Ocube
