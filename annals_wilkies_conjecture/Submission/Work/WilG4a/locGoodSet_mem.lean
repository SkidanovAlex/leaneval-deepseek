/-
  WilG4a / `locGoodSet_mem`: the `Ω`-membership of the per-member "locally good" set.

  For a `p`-parameter family `f : ℝᵖ → ℝ → ℝ` whose graph is `Ω F0 D (p+2)`-definable in a
  sharply o-minimal structure with sharp derivatives, the set

    `locGoodSet f r ⊆ ℝ^{p+1}`

  (points at which the slice is locally `C^{r+2}` and each of its derivatives of order `≤ r+1`
  has locally constant sign) is `Ω a (b.eval ![D,r]) (p+1)` for a format `a` and a polynomial
  `b` depending only on `p` and `F0`.

  ## Proof

  `locGoodSet` is a finite intersection/union of four kinds of ingredients:

  * `CD.inflated p X` — the fibre-wise localisation of `X`, whose `Ω`-membership is
    `CD.inflated_mem` (format `+A`, degree `+C`, `A, C` depending only on `p`);
  * `CD.fibDerivGraph f j` — the graph of the `j`-th fibre derivative, whose `Ω`-membership is
    `CD.fibDerivGraph_mem` (format `a₁` independent of `j`, degree `b₁.eval ![D,j]`);
  * the two half-spaces `{0 ≤ v}` and `{v ≤ 0}` in the last coordinate, of format `p+5` and
    degree `3`;
  * the projection `projLast`.

  The only non-elementary point is that the order `j` ranges over `Fin (r+2)`: the polynomial
  bound `b₁.eval ![D,j]` must be replaced by a single polynomial in `(D,r)`.  This is done with
  monotonicity of `ℕ`-polynomial evaluation (`eval_mono_vars`: `j ≤ r+1` gives
  `b.eval ![D,j] ≤ b.eval ![D,r+1]`), the shift `r ↦ r+1` of the second variable
  (`exists_eval_shift_k`), and the fact that a finite intersection of `r+2` sets with the same
  degree has degree `(r+2) * degree` (`inter_uniform`).
-/
import Mathlib
import Submission.Work.WilG4a.locGoodDefs
import Submission.Work.WilG4a.CD.fibDerivGraph_mem
import Submission.Work.WilG4a.CD.inflated_mem
import Submission.Work.WilG4a.CD.sliceContDiffAt_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-! ## 1. Polynomial bookkeeping

`MvPolynomial (Fin 2) ℕ` evaluated at `![D, r]`.  The two lemmas below are the only polynomial
facts needed: monotonicity in the two variables, and the shift of the second variable. -/

/-- Evaluation of a two-variable polynomial with natural coefficients is monotone in both
variables. -/
theorem eval_mono_vars {b : MvPolynomial (Fin 2) ℕ} {D D' r r' : ℕ}
    (hD : D ≤ D') (hr : r ≤ r') : b.eval ![D, r] ≤ b.eval ![D', r'] := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [MvPolynomial.eval_add, MvPolynomial.eval_add]; exact add_le_add hp hq
  | mul_X p i hp =>
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul]
      refine Nat.mul_le_mul hp ?_
      fin_cases i
      · simpa using hD
      · simpa using hr

/-- **Shifting the order variable.**  A bound `b.eval ![D, r+k]` is again the evaluation at
`![D,r]` of a single two-variable polynomial. -/
theorem exists_eval_shift_k (b : MvPolynomial (Fin 2) ℕ) (k : ℕ) :
    ∃ d : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ, b.eval ![D, r + k] = d.eval ![D, r] := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 + MvPolynomial.C k) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 + MvPolynomial.C k) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 + MvPolynomial.C k))
      = ![D, r + k] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r + k] b
    = MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (MvPolynomial.bind₁ (fun i : Fin 2 =>
        if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 + MvPolynomial.C k) b)
  exact h.symm

/-! ## 2. The two sign half-spaces in the last coordinate -/

/-- `{v : ℝ^{p+2} | 0 ≤ v (last)}` is `Ω`-definable with format `p+5` and degree `3`. -/
theorem nonneg_last_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    {w : Fin (p + 2) → ℝ | 0 ≤ w (Fin.last (p + 1))} ∈ S.Ω (p + 5) 3 (p + 2) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 2) 0
    (-(MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ))
  have htd : (-(MvPolynomial.X (Fin.last (p + 1))) :
      MvPolynomial (Fin (p + 2)) ℝ).totalDegree + 2 = 3 := by
    rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]
  have hset : {v : Fin (p + 2) → ℝ | 0 < MvPolynomial.eval v
        (-(MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ))}
      = {v : Fin (p + 2) → ℝ | v (Fin.last (p + 1)) < 0} := by
    ext v
    simp only [Set.mem_setOf_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
    constructor <;> intro hv <;> linarith
  rw [hset] at h
  have hc := S.compl h
  have hset2 : ({v : Fin (p + 2) → ℝ | v (Fin.last (p + 1)) < 0})ᶜ
      = {v : Fin (p + 2) → ℝ | 0 ≤ v (Fin.last (p + 1))} := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [hset2] at hc
  simpa [htd] using hc

/-- `{v : ℝ^{p+2} | v (last) ≤ 0}` is `Ω`-definable with format `p+5` and degree `3`. -/
theorem nonpos_last_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    {w : Fin (p + 2) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∈ S.Ω (p + 5) 3 (p + 2) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 2) 0
    (MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ)
  have htd : (MvPolynomial.X (Fin.last (p + 1)) :
      MvPolynomial (Fin (p + 2)) ℝ).totalDegree + 2 = 3 := by
    rw [MvPolynomial.totalDegree_X]
  have hset : {v : Fin (p + 2) → ℝ | 0 < MvPolynomial.eval v
        (MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ)}
      = {v : Fin (p + 2) → ℝ | 0 < v (Fin.last (p + 1))} := by
    ext v
    simp only [Set.mem_setOf_eq, MvPolynomial.eval_X]
  rw [hset] at h
  have hc := S.compl h
  have hset2 : ({v : Fin (p + 2) → ℝ | 0 < v (Fin.last (p + 1))})ᶜ
      = {v : Fin (p + 2) → ℝ | v (Fin.last (p + 1)) ≤ 0} := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [hset2] at hc
  simpa [htd] using hc

/-! ## 3. Generic `Ω`-combinators with explicit natural-number degrees -/

/-- Binary intersection. -/
theorem inter2n {S : WilkiesDesign.SOMin} {n : ℕ} {a₁ a₂ D₁ D₂ : ℕ}
    {X Y : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a₁ D₁ n) (hY : Y ∈ S.Ω a₂ D₂ n) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) (D₁ + D₂) n := by
  have h1 : X ∈ S.Ω (max a₁ a₂) D₁ n := Work.WilG0.Omega_mono_FD (le_max_left _ _) le_rfl hX
  have h2 : Y ∈ S.Ω (max a₁ a₂) D₂ n := Work.WilG0.Omega_mono_FD (le_max_right _ _) le_rfl hY
  have h := S.inter (F := max a₁ a₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by rintro i; fin_cases i
        · simpa using h1
        · simpa using h2)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum] at h
  rw [Work.WilG0.iInter_fin_two] at h
  exact h

/-- Binary union. -/
theorem union2n {S : WilkiesDesign.SOMin} {n : ℕ} {a₁ a₂ D₁ D₂ : ℕ}
    {X Y : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a₁ D₁ n) (hY : Y ∈ S.Ω a₂ D₂ n) :
    X ∪ Y ∈ S.Ω (max a₁ a₂) (D₁ + D₂) n := by
  have h1 : X ∈ S.Ω (max a₁ a₂) D₁ n := Work.WilG0.Omega_mono_FD (le_max_left _ _) le_rfl hX
  have h2 : Y ∈ S.Ω (max a₁ a₂) D₂ n := Work.WilG0.Omega_mono_FD (le_max_right _ _) le_rfl hY
  have h := S.union (F := max a₁ a₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by rintro i; fin_cases i
        · simpa using h1
        · simpa using h2)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum] at h
  rw [Work.WilG0.iUnion_fin_two] at h
  exact h

/-- A finite intersection of `k` sets with a *common* degree bound `b.eval ![D,r]` has degree
`k * b.eval ![D,r]`, re-expressed as the evaluation of a polynomial when `k` itself is the
value of a polynomial (`hK`). -/
theorem inter_uniform {S : WilkiesDesign.SOMin} {n : ℕ} {a : ℕ} {k : ℕ}
    {bK b : MvPolynomial (Fin 2) ℕ} {D r : ℕ} (hK : bK.eval ![D, r] = k)
    (A : Fin k → Set (Fin n → ℝ)) (hA : ∀ i, A i ∈ S.Ω a (b.eval ![D, r]) n) :
    (⋂ i, A i) ∈ S.Ω (a + 1) ((bK * b).eval ![D, r]) n := by
  have h := S.inter (F := a) (n := n) (k := k) (fun _ : Fin k => b.eval ![D, r]) A hA
  have hk : k = bK.eval ![D, r] := hK.symm
  have hsum : (∑ _ : Fin k, b.eval ![D, r]) = (bK * b).eval ![D, r] := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hk,
      MvPolynomial.eval_mul]
    simp
  rwa [hsum] at h

/-! ## 4. The main theorem -/

theorem locGoodSet_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) → Work.WilG4a.locGoodSet f r ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) := by
  obtain ⟨A, C, hInfl⟩ := CD.inflated_mem (S := S) p
  obtain ⟨a₁, b₁, hG⟩ := CD.fibDerivGraph_mem S hcd hder p F0
  -- the sign bound `(b₁.eval ![D,j] + 3) + C`, twice, for the union of the two sign conditions
  set bU : MvPolynomial (Fin 2) ℕ :=
    (b₁ + MvPolynomial.C 3 + MvPolynomial.C C) + (b₁ + MvPolynomial.C 3 + MvPolynomial.C C)
    with hbU
  -- `e` evaluates at `![D,r]` the uniform bound `bU.eval ![D,r+1]`
  obtain ⟨e, he⟩ := exists_eval_shift_k bU 1
  -- `d₂` evaluates at `![D,r]` the graph bound `b₁.eval ![D,r+2]`
  obtain ⟨d₂, hd₂⟩ := exists_eval_shift_k b₁ 2
  refine ⟨max ((a₁ + 1) + A) ((max a₁ (p + 5) + 1 + 1 + A) + 1) + 1,
    (d₂ + MvPolynomial.C C) + (MvPolynomial.X 1 + MvPolynomial.C 2) * e, ?_⟩
  intro D r f hf
  have hGe : {w : Fin (p + 2) → ℝ | 0 ≤ w (Fin.last (p + 1))} ∈ S.Ω (p + 5) 3 (p + 2) :=
    nonneg_last_mem S p
  have hLe : {w : Fin (p + 2) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∈ S.Ω (p + 5) 3 (p + 2) :=
    nonpos_last_mem S p
  have hbUeval : ∀ D j : ℕ, bU.eval ![D, j]
      = (b₁.eval ![D, j] + 3 + C) + (b₁.eval ![D, j] + 3 + C) := by
    intro D j
    simp only [hbU, MvPolynomial.eval_add, MvPolynomial.eval_C]
  -- one sign condition, at order `j`
  have hge : ∀ j : ℕ, CD.inflated p (sliceGeq f j) ∈
      S.Ω (max a₁ (p + 5) + 1 + 1 + A) (b₁.eval ![D, j] + 3 + C) (p + 1) := by
    intro j
    have hInt : CD.fibDerivGraph f j ∩
        {w : Fin (p + 2) → ℝ | 0 ≤ w (Fin.last (p + 1))} ∈
        S.Ω (max a₁ (p + 5) + 1) (b₁.eval ![D, j] + 3) (p + 2) :=
      inter2n (S := S) (hG D j hf) hGe
    exact hInfl (max a₁ (p + 5) + 1 + 1) (b₁.eval ![D, j] + 3) (sliceGeq f j)
      (by simpa [sliceGeq] using S.proj hInt)
  have hle : ∀ j : ℕ, CD.inflated p (sliceLeq f j) ∈
      S.Ω (max a₁ (p + 5) + 1 + 1 + A) (b₁.eval ![D, j] + 3 + C) (p + 1) := by
    intro j
    have hInt : CD.fibDerivGraph f j ∩
        {w : Fin (p + 2) → ℝ | w (Fin.last (p + 1)) ≤ 0} ∈
        S.Ω (max a₁ (p + 5) + 1) (b₁.eval ![D, j] + 3) (p + 2) :=
      inter2n (S := S) (hG D j hf) hLe
    exact hInfl (max a₁ (p + 5) + 1 + 1) (b₁.eval ![D, j] + 3) (sliceLeq f j)
      (by simpa [sliceLeq] using S.proj hInt)
  -- the sign condition (either sign) with the doubled bound
  have hsign : ∀ j : ℕ,
      (CD.inflated p (sliceGeq f j) ∪ CD.inflated p (sliceLeq f j)) ∈
        S.Ω (max a₁ (p + 5) + 1 + 1 + A) (bU.eval ![D, j]) (p + 1) := by
    intro j
    have h := union2n (S := S) (hge j) (hle j)
    refine Work.WilG0.Omega_mono_FD (F' := max a₁ (p + 5) + 1 + 1 + A)
      (D' := bU.eval ![D, j]) (by omega) ?_ h
    rw [hbUeval D j]
  -- uniformly in `j < r+2`: replace `j` by `r+1`
  have hUnif : ∀ j : Fin (r + 2),
      (CD.inflated p (sliceGeq f j.val) ∪ CD.inflated p (sliceLeq f j.val)) ∈
        S.Ω (max a₁ (p + 5) + 1 + 1 + A) (bU.eval ![D, r + 1]) (p + 1) := by
    intro j
    refine Work.WilG0.Omega_mono_FD (F' := max a₁ (p + 5) + 1 + 1 + A)
      (D' := bU.eval ![D, r + 1]) le_rfl ?_ (hsign j.val)
    exact eval_mono_vars (b := bU) le_rfl (by omega : j.val ≤ r + 1)
  have hK : (MvPolynomial.X 1 + MvPolynomial.C 2 : MvPolynomial (Fin 2) ℕ).eval ![D, r]
      = r + 2 := by simp
  have hYmem : ∀ j : Fin (r + 2),
      (CD.inflated p (sliceGeq f j.val) ∪ CD.inflated p (sliceLeq f j.val)) ∈
        S.Ω (max a₁ (p + 5) + 1 + 1 + A) (e.eval ![D, r]) (p + 1) := by
    intro j
    have h := hUnif j
    rwa [he D r] at h
  -- the intersection over the `r+2` orders
  have hInter := inter_uniform (S := S) (n := p + 1)
    (a := max a₁ (p + 5) + 1 + 1 + A) (k := r + 2)
    (bK := MvPolynomial.X 1 + MvPolynomial.C 2) (b := e) hK
    (fun j : Fin (r + 2) =>
      (CD.inflated p (sliceGeq f j.val) ∪ CD.inflated p (sliceLeq f j.val))) hYmem
  -- the `C^{r+2}` component
  have hGg : CD.inflated p (WilkiesDesign.projLast (CD.fibDerivGraph f (r + 2))) ∈
      S.Ω ((a₁ + 1) + A) ((d₂ + MvPolynomial.C C).eval ![D, r]) (p + 1) := by
    have h := S.proj (hG D (r + 2) hf)
    have h₂ : CD.inflated p (WilkiesDesign.projLast (CD.fibDerivGraph f (r + 2))) ∈
        S.Ω ((a₁ + 1) + A) (b₁.eval ![D, r + 2] + C) (p + 1) :=
      hInfl (a₁ + 1) (b₁.eval ![D, r + 2]) _ h
    refine Work.WilG0.Omega_mono_FD (F' := (a₁ + 1) + A)
      (D' := (d₂ + MvPolynomial.C C).eval ![D, r]) le_rfl ?_ h₂
    rw [MvPolynomial.eval_add, MvPolynomial.eval_C, hd₂ D r]
  have hfin := inter2n (S := S) hGg hInter
  rw [locGoodSet]
  rw [MvPolynomial.eval_add]
  exact hfin

end Work.WilG4a
