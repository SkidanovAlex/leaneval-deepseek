import Mathlib
import Submission.Work.WilkiesH.Count.Interface
import Submission.Work.WilkiesH.Omega.omega_poly_ne
import Submission.Work.WilkiesH.Omega.dimLE_of_forall_proj_subset_zeroLocus
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilG5.Count.dominate
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.PolyEval.poly_abs_bound
import Submission.Work.WilkiesI.Basic

namespace Work.WilkiesH.Count

open WilkiesDesign WilkiesConjecture

/-! ## Local helpers (self-contained copies of the shape needed below) -/

/-- A finite intersection of `Ω`-sets indexed by an arbitrary `Fintype` is in `Ω`, with the
format index raised by one and the degree index summed. -/
theorem omega_iInter_local {S : WilkiesDesign.SOMin} {ι : Type*} [Fintype ι] {n F : ℕ}
    (D : ι → ℕ) (A : ι → Set (Fin n → ℝ))
    (h : ∀ i, A i ∈ S.Ω F (D i) n) : (⋂ i, A i) ∈ S.Ω (F + 1) (∑ i, D i) n := by
  classical
  have heq : (⋂ i, A i) = ⋂ j : Fin (Fintype.card ι), A ((Fintype.equivFin ι).symm j) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx j; exact hx _
    · intro hx i; have := hx (Fintype.equivFin ι i); simpa using this
  rw [heq]
  have h2 := S.inter (fun j : Fin (Fintype.card ι) => D ((Fintype.equivFin ι).symm j))
    (fun j => A ((Fintype.equivFin ι).symm j)) (fun j => h _)
  rw [Equiv.sum_comp (Fintype.equivFin ι).symm D] at h2
  exact h2

/-- The common zero locus of a finite family of coordinate pull-backs of polynomials is in
`Ω`, with format index `n + 1` and degree index the sum of the total degrees. -/
theorem omega_family_coord_zeroLocus_local {S : WilkiesDesign.SOMin} {n μ : ℕ}
    (Q : (Fin (μ + 1) ↪ Fin n) → MvPolynomial (Fin (μ + 1)) ℝ) :
    {x : Fin n → ℝ | ∀ e, MvPolynomial.eval (fun i => x (e i)) (Q e) = 0} ∈
      S.Ω (n + 1) (∑ e, (Q e).totalDegree) n := by
  classical
  have h : ∀ e : (Fin (μ + 1) ↪ Fin n),
      {x : Fin n → ℝ | MvPolynomial.eval (fun i => x (e i)) (Q e) = 0} ∈
        S.Ω n ((Q e).totalDegree) n := by
    intro e
    have heq : {x : Fin n → ℝ | MvPolynomial.eval (fun i => x (e i)) (Q e) = 0} =
        {x : Fin n → ℝ | MvPolynomial.eval x (MvPolynomial.rename (⇑e) (Q e)) = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_rename]
      exact Iff.rfl
    rw [heq]
    exact Work.WilG5.mem_mono (S.hyp n (MvPolynomial.rename (⇑e) (Q e))) n
      ((Q e).totalDegree) (le_refl n) (MvPolynomial.totalDegree_rename_le _ _)
  have h2 := omega_iInter_local (S := S) (F := n) (fun e => (Q e).totalDegree)
    (fun e => {x : Fin n → ℝ | MvPolynomial.eval (fun i => x (e i)) (Q e) = 0}) h
  convert h2 using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]

/-- The same common zero locus is semialgebraic. -/
theorem isSemialgebraic_family_coord_zeroLocus_local {n μ : ℕ}
    (Q : (Fin (μ + 1) ↪ Fin n) → MvPolynomial (Fin (μ + 1)) ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ e, MvPolynomial.eval (fun i => x (e i)) (Q e) = 0} := by
  have h := Work.WilkiesI.isSemialgebraic_zeroLocus (n := n)
    (fun e : (Fin (μ + 1) ↪ Fin n) => MvPolynomial.rename (⇑e) (Q e))
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, MvPolynomial.eval_rename]
  exact Iff.rfl

/-- Scaling a polynomial by a natural constant is dominated by another polynomial, evaluwise. -/
theorem poly_const_mul_le_local (q : MvPolynomial (Fin 3) ℝ) (K : ℕ) :
    ∃ q' : MvPolynomial (Fin 3) ℝ,
      ∀ (D g : ℕ) (L : ℝ), 0 ≤ L →
        (K : ℝ) * MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q ≤
          MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q' :=
  ⟨MvPolynomial.C (K : ℝ) * q,
    fun D g L _ => le_of_eq (by rw [MvPolynomial.eval_mul, MvPolynomial.eval_C])⟩

/-- A polynomial `c` evaluated at `(D, r, u)` with `D : ℕ` and both `r` and `u` bounded by
`q(D,g,L)` is dominated by a polynomial in `(D, g, L)`. -/
theorem poly_le_comp_log_local (c q : MvPolynomial (Fin 3) ℝ) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      ∀ (D g : ℕ) (L r u : ℝ), 0 ≤ L → 0 ≤ r → 0 ≤ u →
        r ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q →
        u ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q →
        MvPolynomial.eval ![(D : ℝ), r, u] c ≤
          MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] p := by
  obtain ⟨C, N, hC, hbound⟩ := Work.WilG5.PolyEval.poly_abs_bound c
  refine ⟨MvPolynomial.C C *
    (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.C 2 * q) ^ N, ?_⟩
  intro D g L r u hL hr hu hrq huq
  have hsum : (∑ i : Fin 3, |(![(D : ℝ), r, u] : Fin 3 → ℝ) i|) = (D : ℝ) + r + u := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [abs_of_nonneg (Nat.cast_nonneg D), abs_of_nonneg hr, abs_of_nonneg hu]
  have hb := hbound (![(D : ℝ), r, u] : Fin 3 → ℝ)
  rw [hsum] at hb
  have htarget : MvPolynomial.eval ![(D : ℝ), (g : ℝ), L]
      (MvPolynomial.C C *
        (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.C 2 * q) ^ N)
      = C * (1 + ((D : ℝ) + 2 * MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q)) ^ N := by
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  rw [htarget]
  have h1 : (1 : ℝ) + ((D : ℝ) + r + u)
      ≤ 1 + ((D : ℝ) + 2 * MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q) := by
    linarith [hrq, huq]
  have hpow := pow_le_pow_left₀ (by positivity) h1 N
  calc MvPolynomial.eval ![(D : ℝ), r, u] c
      ≤ |MvPolynomial.eval ![(D : ℝ), r, u] c| := le_abs_self _
    _ ≤ C * (1 + ((D : ℝ) + r + u)) ^ N := hb
    _ ≤ C * (1 + ((D : ℝ) + 2 * MvPolynomial.eval ![(D : ℝ), (g : ℝ), L] q)) ^ N :=
        mul_le_mul_of_nonneg_left hpow hC

theorem chartCover_of_interp {S : WilkiesDesign.SOMin} {F n : ℕ}
    (hG : WilkiesDesign.AlgLemma S F n) (hint : Work.WilkiesH.InterpPerChart S F n) :
    Work.WilkiesH.ChartCover S F n := by
  classical
  obtain ⟨pG, hpG⟩ := hG
  obtain ⟨pq, hq⟩ := hint
  obtain ⟨plc, hplc⟩ := poly_le_comp_log_local pG pq
  refine ⟨n + 1, plc, MvPolynomial.C ((((n + 1) ^ (n + 1) : ℕ) : ℝ)) * pq, ?_⟩
  intro D X μ hμn hX hXcube hdim g H T hT hTdeg
  obtain ⟨d0, r0, ε, hε0, hε1, hd0, hr0, hεinv, hinterp⟩ := hq D μ X hμn hX hXcube hdim g H
  obtain ⟨Φ, hΦcard, hΦprop, hΦcover⟩ := hpG D r0 ε hε0 hε1 μ X hμn hXcube hX hdim
  have hex : ∀ (φ : {φ : (Fin μ → ℝ) → (Fin n → ℝ) // φ ∈ Φ}) (e : Fin (μ + 1) ↪ Fin n),
      ∃ P : MvPolynomial (Fin (μ + 1)) ℝ, P ≠ 0 ∧ P.totalDegree ≤ d0 ∧
        ∀ x : Fin n → ℝ, x ∈ degreeHeightLE X g H →
          (∃ t ∈ openCube μ, dist (φ.1 t) x < ε) →
          MvPolynomial.eval (fun i => x (e i)) P = 0 :=
    fun φ e => hinterp φ.1 (hΦprop φ.1 φ.2).1 (hΦprop φ.1 φ.2).2.1 (hΦprop φ.1 φ.2).2.2 e
  choose Pfun hPne hPdeg hPeval using hex
  let W : {φ : (Fin μ → ℝ) → (Fin n → ℝ) // φ ∈ Φ} → Set (Fin n → ℝ) :=
    fun φ => {x : Fin n → ℝ | ∀ e, MvPolynomial.eval (fun i => x (e i)) (Pfun φ e) = 0}
  have hWΩ : ∀ φ, W φ ∈ S.Ω (n + 1) (∑ e, (Pfun φ e).totalDegree) n := fun φ =>
    omega_family_coord_zeroLocus_local (S := S) (Q := fun e => Pfun φ e)
  have hWdim : ∀ φ, DimLE (W φ) μ := fun φ =>
    Work.WilkiesH.Omega.dimLE_of_forall_proj_subset_zeroLocus
      (fun e => ⟨Pfun φ e, hPne φ e, fun x hx => hx e⟩)
  have hWsem : ∀ φ, IsSemialgebraic (W φ) := fun φ =>
    isSemialgebraic_family_coord_zeroLocus_local (Q := fun e => Pfun φ e)
  have hKbound : Fintype.card (Fin (μ + 1) ↪ Fin n) ≤ (n + 1) ^ (n + 1) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    exact le_trans (Nat.descFactorial_le_pow n (μ + 1))
      (le_trans (Nat.pow_le_pow_left (Nat.le_succ n) (μ + 1))
        (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.succ_le_succ hμn)))
  have hsum : ∀ φ, ∑ e, (Pfun φ e).totalDegree ≤ (n + 1) ^ (n + 1) * d0 := by
    intro φ
    calc ∑ e, (Pfun φ e).totalDegree
        ≤ ∑ _e : Fin (μ + 1) ↪ Fin n, d0 := Finset.sum_le_sum (fun e _ => hPdeg φ e)
      _ = Fintype.card (Fin (μ + 1) ↪ Fin n) * d0 := by simp [Finset.sum_const]
      _ ≤ (n + 1) ^ (n + 1) * d0 := Nat.mul_le_mul_right d0 hKbound
  have hWcover : (↑T : Set (Fin n → ℝ)) ⊆
      ⋃ φ : {φ : (Fin μ → ℝ) → (Fin n → ℝ) // φ ∈ Φ}, W φ := by
    intro x hx
    obtain ⟨φ, hφmem, t, ht, hdist⟩ := hΦcover x (hT hx)
    refine Set.mem_iUnion.mpr ⟨⟨φ, hφmem⟩, ?_⟩
    intro e
    exact hPeval ⟨φ, hφmem⟩ e x (hTdeg hx) ⟨t, ht, hdist⟩
  let eΦ := Finset.equivFin Φ
  refine ⟨Φ.card, fun j => W (eΦ.symm j), (n + 1) ^ (n + 1) * d0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hΦcard.trans (hplc D g (Real.log H) (r0 : ℝ) (- Real.log ε) ?_ ?_ ?_ ?_ ?_)
    · exact Real.log_natCast_nonneg H
    · exact Nat.cast_nonneg r0
    · have hlogneg := Real.log_neg hε0 hε1
      linarith
    · exact hr0
    · rw [one_div, Real.log_inv] at hεinv
      exact hεinv
  · rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    have hcast : ((((n + 1) ^ (n + 1) * d0 : ℕ)) : ℝ)
        = ((((n + 1) ^ (n + 1) : ℕ)) : ℝ) * (d0 : ℝ) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hd0 (Nat.cast_nonneg _)
  · intro j
    exact Work.WilG5.mem_mono (hWΩ (eΦ.symm j)) (n + 1) ((n + 1) ^ (n + 1) * d0)
      (le_refl _) (hsum (eΦ.symm j))
  · intro j; exact hWdim (eΦ.symm j)
  · intro j; exact hWsem (eΦ.symm j)
  · have hi : (⋃ j : Fin Φ.card, W (eΦ.symm j)) =
        ⋃ φ : {φ : (Fin μ → ℝ) → (Fin n → ℝ) // φ ∈ Φ}, W φ :=
      eΦ.symm.surjective.iUnion_comp W
    rw [hi]
    exact hWcover

end Work.WilkiesH.Count
