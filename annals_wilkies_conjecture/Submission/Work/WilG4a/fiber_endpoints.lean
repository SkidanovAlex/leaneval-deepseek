/-
  WilG4a : `Work.WilG4a.fiber_endpoints`.

  For a set `Z ⊆ ℝ^{p+1}` whose last coordinate is constrained to the open unit interval, the
  pointwise infimum and supremum of the fibre `Z_l = {x | (l,x) ∈ Z}` are graphs of functions
  whose graphs are `Ω`-definable with a format independent of the degree `D` and a degree
  polynomial in `D`.  This is BNZ's "gr a(z), gr b(z) ∈ Ω_{O_F(1),poly_F(D)} since they can be
  defined using first-order formulas as the infimum and supremum of the fibre C_z"
  (arXiv 2202.05305, Prop. "Definable choice").

  The construction is in `fiber_defs`: `A_lo p Z` is the set of pairs `(l,y)` such that
  `y = inf Z_l` (and `y = 0` when `Z_l = ∅`), assembled from the first-order conditions
  `∃t, (l,t) ∈ Z`, `∀t, (l,t) ∈ Z → y ≤ t`, `∀u > y, ∃t, (l,t) ∈ Z ∧ t < u` and `y = 0`.
  This file proves the two halves of the theorem:
  * `A_lo p Z` is the graph of `l ↦ inf Z_l` (the semantic half, using the order-theoretic
    characterisation of `inf`);
  * `A_lo p Z ∈ S.Ω a (b.eval D) (p+1)` with `a`, `b` independent of `D` (the Ω-bookkeeping
    half, from the sibling modules `NE1_mem`, `LB1_mem`, `GLB1_mem`, `LUB1_mem`, `UB1_mem`
    and `WilG1.Calc.lt_mem`).
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG4a.NE1_mem
import Submission.Work.WilG4a.LB1_mem
import Submission.Work.WilG4a.UB1_mem
import Submission.Work.WilG4a.GLB1_mem
import Submission.Work.WilG4a.LUB1_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign WilkiesConjecture

/-! ## 1. Reading the four fibre conditions in coordinates -/

theorem snoc_mem_pullZ2 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (x : Fin (p + 1) → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ pullZ2 p Z ↔ Fin.snoc (Fin.init x) t ∈ Z := by
  simp only [pullZ2, Set.mem_ofPred_eq, comp_iota1]
  simp

theorem snoc_snoc_mem_pullZ3 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (x : Fin (p + 1) → ℝ)
    (u t : ℝ) :
    Fin.snoc (Fin.snoc x u) t ∈ pullZ3 p Z ↔ Fin.snoc (Fin.init x) t ∈ Z := by
  simp only [pullZ3, Set.mem_ofPred_eq, comp_iota2]
  simp

theorem snoc_mem_tLtY (p : ℕ) (x : Fin (p + 1) → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ tLtY p ↔ t < x (Fin.last p) := by
  simp only [tLtY, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]

theorem snoc_mem_yLtT (p : ℕ) (x : Fin (p + 1) → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ yLtT p ↔ x (Fin.last p) < t := by
  simp only [yLtT, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]

theorem snoc_snoc_mem_tLtU (p : ℕ) (x : Fin (p + 1) → ℝ) (u t : ℝ) :
    Fin.snoc (Fin.snoc x u) t ∈ tLtU p ↔ t < u := by
  simp only [tLtU, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]

theorem snoc_snoc_mem_uLtT (p : ℕ) (x : Fin (p + 1) → ℝ) (u t : ℝ) :
    Fin.snoc (Fin.snoc x u) t ∈ uLtT p ↔ u < t := by
  simp only [uLtT, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]

/-! ## 2. The meaning of the five sets -/

theorem mem_NE1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ NE1 p Z ↔ ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z := by
  rw [NE1, projLast, Set.mem_ofPred_eq]
  exact exists_congr fun x => snoc_mem_pullZ2 p Z z x

theorem mem_LB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ LB1 p Z ↔ ∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → z (Fin.last p) ≤ x := by
  rw [LB1, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists]
  constructor
  · intro h x hx
    have h' := h x
    rw [Set.mem_inter_iff, snoc_mem_pullZ2, snoc_mem_tLtY] at h'
    by_contra hcon
    exact h' ⟨hx, not_le.mp hcon⟩
  · intro h t
    rw [Set.mem_inter_iff, snoc_mem_pullZ2, snoc_mem_tLtY]
    rintro ⟨ht, hlt⟩
    exact absurd (h t ht) (not_le.mpr hlt)

theorem mem_UB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ UB1 p Z ↔ ∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → x ≤ z (Fin.last p) := by
  rw [UB1, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists]
  constructor
  · intro h x hx
    have h' := h x
    rw [Set.mem_inter_iff, snoc_mem_pullZ2, snoc_mem_yLtT] at h'
    by_contra hcon
    exact h' ⟨hx, not_le.mp hcon⟩
  · intro h t
    rw [Set.mem_inter_iff, snoc_mem_pullZ2, snoc_mem_yLtT]
    rintro ⟨ht, hlt⟩
    exact absurd (h t ht) (not_le.mpr hlt)

theorem mem_GLB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ GLB1 p Z ↔ ∀ u : ℝ, z (Fin.last p) < u →
      ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ x < u := by
  rw [GLB1, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq]
  constructor
  · intro h u hu
    by_contra hcon
    have hcon' : ∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → u ≤ x := by
      intro x hx
      by_contra hle
      exact hcon ⟨x, hx, not_le.mp hle⟩
    apply h
    refine ⟨u, ?_, ?_⟩
    · rw [NIn2lo, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq]
      rintro ⟨t, ht⟩
      rw [In3lo, Set.mem_inter_iff, snoc_snoc_mem_pullZ3, snoc_snoc_mem_tLtU] at ht
      exact absurd (hcon' t ht.1) (not_le.mpr ht.2)
    · rw [yLtT, Set.mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last]; exact hu
  · intro h
    rintro ⟨u, hu, hu'⟩
    rw [yLtT, Set.mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last] at hu'
    rw [NIn2lo, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists] at hu
    obtain ⟨x, hx, hxu⟩ := h u hu'
    exact hu x ⟨(snoc_snoc_mem_pullZ3 p Z z u x).mpr hx,
      (snoc_snoc_mem_tLtU p z u x).mpr hxu⟩

theorem mem_LUB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ LUB1 p Z ↔ ∀ u : ℝ, u < z (Fin.last p) →
      ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ u < x := by
  rw [LUB1, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq]
  constructor
  · intro h u hu
    by_contra hcon
    have hcon' : ∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → x ≤ u := by
      intro x hx
      by_contra hle
      exact hcon ⟨x, hx, not_le.mp hle⟩
    apply h
    refine ⟨u, ?_, ?_⟩
    · rw [NIn2hi, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq]
      rintro ⟨t, ht⟩
      rw [In3hi, Set.mem_inter_iff, snoc_snoc_mem_pullZ3, snoc_snoc_mem_uLtT] at ht
      exact absurd (hcon' t ht.1) (not_le.mpr ht.2)
    · rw [tLtY, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]; exact hu
  · intro h
    rintro ⟨u, hu, hu'⟩
    rw [tLtY, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc] at hu'
    rw [NIn2hi, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists] at hu
    obtain ⟨x, hx, hxu⟩ := h u hu'
    exact hu x ⟨(snoc_snoc_mem_pullZ3 p Z z u x).mpr hx,
      (snoc_snoc_mem_uLtT p z u x).mpr hxu⟩

theorem mem_yZero1 (p : ℕ) (z : Fin (p + 1) → ℝ) :
    z ∈ yZero1 p ↔ z (Fin.last p) = 0 := Iff.rfl

/-! ## 3. The two graphs -/

theorem mem_A_lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ A_lo p Z ↔
      (((∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∧
          (∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → z (Fin.last p) ≤ x)) ∧
          (∀ u : ℝ, z (Fin.last p) < u →
            ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ x < u)) ∨
        (¬ (∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∧ z (Fin.last p) = 0) := by
  rw [A_lo, Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
    Set.mem_compl_iff, mem_NE1, mem_LB1, mem_GLB1, mem_yZero1]

theorem mem_A_hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ A_hi p Z ↔
      (((∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∧
          (∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → x ≤ z (Fin.last p))) ∧
          (∀ u : ℝ, u < z (Fin.last p) →
            ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ u < x)) ∨
        (¬ (∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∧ z (Fin.last p) = 0) := by
  rw [A_hi, Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
    Set.mem_compl_iff, mem_NE1, mem_UB1, mem_LUB1, mem_yZero1]

/-! ## 4. The order-theoretic characterisation of `inf` and `sup` -/

theorem eq_sInf_iff (f : Set ℝ) (hne : f.Nonempty) (hbdd : BddBelow f) (y : ℝ) :
    ((∀ t ∈ f, y ≤ t) ∧ (∀ u : ℝ, y < u → ∃ t ∈ f, t < u)) ↔ y = sInf f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine le_antisymm (le_csInf hne h1) ?_
    by_contra hcon
    obtain ⟨t, ht, htu⟩ := h2 (sInf f) (not_le.mp hcon)
    exact absurd (csInf_le hbdd ht) (not_le.mpr htu)
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h]; exact fun t ht => csInf_le hbdd ht
    · rw [h]
      intro u hu
      exact (csInf_lt_iff hbdd hne).mp hu

theorem eq_sSup_iff (f : Set ℝ) (hne : f.Nonempty) (hbdd : BddAbove f) (y : ℝ) :
    ((∀ t ∈ f, t ≤ y) ∧ (∀ u : ℝ, u < y → ∃ t ∈ f, u < t)) ↔ y = sSup f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ (csSup_le hne h1)
    by_contra hcon
    obtain ⟨t, ht, htu⟩ := h2 (sSup f) (not_le.mp hcon)
    exact absurd (le_csSup hbdd ht) (not_le.mpr htu)
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h]; exact fun t ht => le_csSup hbdd ht
    · rw [h]
      intro u hu
      exact (lt_csSup_iff hbdd hne).mp hu

/-! ## 5. Membership of the fibre-zero set -/

theorem yZero1_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    yZero1 p ∈ S.Ω (p + 1) 1 (p + 1) := by
  have hdeg : ((MvPolynomial.X (Fin.last p) - MvPolynomial.C (0 : ℝ) :
      MvPolynomial (Fin (p + 1)) ℝ)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; omega
  have h := S.hyp (p + 1) (MvPolynomial.X (Fin.last p) - MvPolynomial.C (0 : ℝ) :
    MvPolynomial (Fin (p + 1)) ℝ)
  have hset : {x : Fin (p + 1) → ℝ | MvPolynomial.eval x
      (MvPolynomial.X (Fin.last p) - MvPolynomial.C (0 : ℝ) :
        MvPolynomial (Fin (p + 1)) ℝ) = 0} = yZero1 p := by
    ext z
    simp only [Set.mem_ofPred_eq, yZero1, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_eq_zero]
  rw [hset] at h
  exact Work.WilG5.mem_mono h (p + 1) 1 le_rfl hdeg

/-! ## 6. Bookkeeping helpers -/

/-- Monotonicity of the degree expression `c * D + c'`. -/
theorem deg_mono {c c' C C' D : ℕ} (h1 : c ≤ C) (h2 : c' ≤ C') :
    c * D + c' ≤ C * D + C' := by
  have h := Nat.mul_le_mul_right D h1
  omega

/-- The final degree polynomial, as an `MvPolynomial (Fin 2) ℕ`. -/
theorem exists_eval_mv (c c' : ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ,
      ∀ D r : ℕ, MvPolynomial.eval ![D, r] b = c * D + c' := by
  refine ⟨MvPolynomial.C c' + MvPolynomial.C c * MvPolynomial.X 0, ?_⟩
  intro D r
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero]
  ring

/-! ## 7. The theorem -/

theorem fiber_endpoints (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) → (∀ z ∈ Z, z (Fin.last p) ∈ Work.WilG4a.I) → ∃ (lo hi : (Fin p → ℝ) → ℝ), WilkiesDesign.graphOf lo ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ WilkiesDesign.graphOf hi ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ ∀ l : Fin p → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) → (∀ x : ℝ, Fin.snoc l x ∈ Z → lo l ≤ x ∧ x ≤ hi l) ∧ (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u) ∧ (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x) := by
  -- the uniform constants supplied by the sibling membership lemmas
  obtain ⟨A₁, c₁, d₁, hNE⟩ := NE1_mem S p F
  obtain ⟨A₂, c₂, d₂, hLB⟩ := LB1_mem S p F
  obtain ⟨A₃, c₃, d₃, hUB⟩ := UB1_mem S p F
  obtain ⟨A₄, c₄, d₄, hGLB⟩ := GLB1_mem S p F
  obtain ⟨A₅, c₅, d₅, hLUB⟩ := LUB1_mem S p F
  -- a common (crude) format and degree bound
  set A : ℕ := A₁ + A₂ + A₃ + A₄ + A₅ + F + p + 10 with hA
  set cmax : ℕ := c₁ + c₂ + c₃ + c₄ + c₅ + 1 with hcmax
  set dmax : ℕ := d₁ + d₂ + d₃ + d₄ + d₅ + 2 with hdmax
  obtain ⟨b, hb⟩ := exists_eval_mv (5 * cmax) (5 * dmax)
  refine ⟨A + 6, b, ?_⟩
  intro D r Z hZ hI
  -- the two candidate functions
  let lo : (Fin p → ℝ) → ℝ := fun l =>
    if _ : ∃ x : ℝ, Fin.snoc l x ∈ Z then sInf {x : ℝ | Fin.snoc l x ∈ Z} else 0
  let hi : (Fin p → ℝ) → ℝ := fun l =>
    if _ : ∃ x : ℝ, Fin.snoc l x ∈ Z then sSup {x : ℝ | Fin.snoc l x ∈ Z} else 0
  -- the six elementary pieces, all in `Ω A (cmax*D+dmax) (p+1)`
  have hNE1 : NE1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hNE D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLB1 : LB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hUB1 : UB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hGLB1 : GLB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hGLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLUB1 : LUB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hyZero : yZero1 p ∈ S.Ω A (cmax * D + dmax) (p + 1) := by
    refine Work.WilG5.mem_mono (yZero1_mem S p) A (cmax * D + dmax) (by omega) ?_
    have h2 : dmax ≤ cmax * D + dmax := Nat.le_add_left dmax (cmax * D)
    omega
  -- assembling the two graphs
  have hX2 : (NE1 p Z ∩ LB1 p Z) ∩ GLB1 p Z ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_inter2 (S := S) hNE1 hLB1)
      (Work.WilG5.mem_mono hGLB1 (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hX4 : (NE1 p Z)ᶜ ∩ yZero1 p ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) (S.compl hNE1)
      (Work.WilG5.mem_mono hyZero (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hA_lo : A_lo p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax))) (p + 1) := by
    unfold A_lo
    exact Work.WilG0.Omega_union2 (S := S) hX2 hX4
  have hY2 : (NE1 p Z ∩ UB1 p Z) ∩ LUB1 p Z ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_inter2 (S := S) hNE1 hUB1)
      (Work.WilG5.mem_mono hLUB1 (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hA_hi : A_hi p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax))) (p + 1) := by
    unfold A_hi
    exact Work.WilG0.Omega_union2 (S := S) hY2 hX4
  -- the degree is dominated by `(5*cmax)*D + 5*dmax`
  have hdeg : ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
      ((cmax * D + dmax) + (cmax * D + dmax)) ≤ 5 * cmax * D + 5 * dmax := by
    have e1 : ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax)) = 5 * (cmax * D + dmax) := by ring
    rw [e1]
    have e2 : 5 * (cmax * D + dmax) = 5 * cmax * D + 5 * dmax := by ring
    rw [e2]
  have hAlo' : A_lo p Z ∈ S.Ω (A + 6) (5 * cmax * D + 5 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_lo (A + 6) (5 * cmax * D + 5 * dmax) (by omega) hdeg
  have hAhi' : A_hi p Z ∈ S.Ω (A + 6) (5 * cmax * D + 5 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_hi (A + 6) (5 * cmax * D + 5 * dmax) (by omega) hdeg
  -- `A_lo` (resp. `A_hi`) is the graph of `lo` (resp. `hi`)
  have hbddOf : ∀ u : Fin p → ℝ,
      BddBelow {x : ℝ | Fin.snoc u x ∈ Z} := by
    intro u
    refine ⟨0, fun x hx => le_of_lt ?_⟩
    have h := hI (Fin.snoc u x) hx
    simp only [Fin.snoc_last] at h
    exact h.1
  have hbddOf' : ∀ u : Fin p → ℝ,
      BddAbove {x : ℝ | Fin.snoc u x ∈ Z} := by
    intro u
    refine ⟨1, fun x hx => le_of_lt ?_⟩
    have h := hI (Fin.snoc u x) hx
    simp only [Fin.snoc_last] at h
    exact h.2
  have hlo_eq : graphOf lo = A_lo p Z := by
    ext z
    rw [graphOf, Set.mem_ofPred_eq, mem_A_lo]
    by_cases hne : ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z
    · have hlo : lo (Fin.init z) = sInf {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} := dif_pos hne
      have hf : ({x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} : Set ℝ).Nonempty := hne
      have hbd := hbddOf (Fin.init z)
      constructor
      · intro hz
        left
        have hz' : z (Fin.last p) = sInf {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} := by
          rw [hz, hlo]
        refine ⟨⟨hne, ?_⟩, ?_⟩
        · intro x hx; rw [hz']; exact csInf_le hbd hx
        · intro u hu; rw [hz'] at hu; exact (csInf_lt_iff hbd hf).mp hu
      · rintro (⟨⟨_, h1⟩, h2⟩ | ⟨hempty, _⟩)
        · rw [hlo]
          exact (eq_sInf_iff _ hf hbd _).mp ⟨h1, h2⟩
        · exact absurd hne hempty
    · have hlo : lo (Fin.init z) = 0 := dif_neg hne
      constructor
      · intro hz
        right
        exact ⟨hne, by rw [hlo] at hz; exact hz⟩
      · rintro (⟨⟨hne', _⟩, _⟩ | ⟨_, h0⟩)
        · exact absurd hne' hne
        · rw [hlo]; exact h0
  have hhi_eq : graphOf hi = A_hi p Z := by
    ext z
    rw [graphOf, Set.mem_ofPred_eq, mem_A_hi]
    by_cases hne : ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z
    · have hhi : hi (Fin.init z) = sSup {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} := dif_pos hne
      have hf : ({x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} : Set ℝ).Nonempty := hne
      have hbd := hbddOf' (Fin.init z)
      constructor
      · intro hz
        left
        have hz' : z (Fin.last p) = sSup {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} := by
          rw [hz, hhi]
        refine ⟨⟨hne, ?_⟩, ?_⟩
        · intro x hx; rw [hz']; exact le_csSup hbd hx
        · intro u hu; rw [hz'] at hu; exact (lt_csSup_iff hbd hf).mp hu
      · rintro (⟨⟨_, h1⟩, h2⟩ | ⟨hempty, _⟩)
        · rw [hhi]
          exact (eq_sSup_iff _ hf hbd _).mp ⟨h1, h2⟩
        · exact absurd hne hempty
    · have hhi : hi (Fin.init z) = 0 := dif_neg hne
      constructor
      · intro hz
        right
        exact ⟨hne, by rw [hhi] at hz; exact hz⟩
      · rintro (⟨⟨hne', _⟩, _⟩ | ⟨_, h0⟩)
        · exact absurd hne' hne
        · rw [hhi]; exact h0
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · rw [hlo_eq, hb D r]; exact hAlo'
  · rw [hhi_eq, hb D r]; exact hAhi'
  · intro l hfib
    have hf : ({x : ℝ | Fin.snoc l x ∈ Z} : Set ℝ).Nonempty := hfib
    have hbd := hbddOf l
    have hbd' := hbddOf' l
    have hlo : lo l = sInf {x : ℝ | Fin.snoc l x ∈ Z} := dif_pos hfib
    have hhi : hi l = sSup {x : ℝ | Fin.snoc l x ∈ Z} := dif_pos hfib
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hlo, hhi]
      exact ⟨csInf_le hbd hx, le_csSup hbd' hx⟩
    · intro u hu
      rw [hlo] at hu
      exact (csInf_lt_iff hbd hf).mp hu
    · intro u hu
      rw [hhi] at hu
      exact (lt_csSup_iff hbd' hf).mp hu

end Work.WilG4a
