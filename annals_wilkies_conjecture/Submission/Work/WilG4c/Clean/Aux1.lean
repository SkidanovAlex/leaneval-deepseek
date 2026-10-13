import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.GraphOfComp

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ### Helper lemmas for `clean_StepCellGraph` (part 1: `Ω`-bookkeeping) -/

/-! ## 1. `Fin` index bookkeeping -/

theorem init_append_cl {p N : ℕ} (l : Fin p → ℝ) (y : Fin (N + 1) → ℝ) :
    Fin.init (Fin.append (n := N + 1) l y) = Fin.append l (Fin.init y) := by
  have h : (Fin.snoc (Fin.append l (Fin.init y)) (y (Fin.last N)) : Fin (p + N + 1) → ℝ)
      = Fin.append (n := N + 1) l y := by
    rw [← Fin.append_snoc l (Fin.init y) (y (Fin.last N)), Fin.snoc_init_self]
  rw [← h, Fin.init_snoc]

theorem clean_castSucc_castAdd {p N : ℕ} (i : Fin p) :
    (Fin.castSucc (Fin.castAdd N i) : Fin (p + N + 1)) = Fin.castAdd (N + 1) i := by
  apply Fin.ext
  simp

theorem clean_natAdd_last {p N : ℕ} :
    (Fin.natAdd p (Fin.last N) : Fin (p + N + 1)) = Fin.last (p + N) := by
  apply Fin.ext
  simp

def clean_snocM {n : ℕ} (q : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ := Fin.snoc q x

theorem clean_snocM_eq {n : ℕ} (q : Fin n → ℝ) (x : ℝ) : clean_snocM q x = Fin.snoc q x := rfl

theorem clean_snoc_last' {n : ℕ} (q : Fin n → ℝ) (x : ℝ) :
    (Fin.snoc q x : Fin (n + 1) → ℝ) (Fin.last n) = x := by simp

theorem clean_snoc_init' {n : ℕ} (q : Fin (n + 1) → ℝ) :
    (Fin.snoc (Fin.init q) (q (Fin.last n)) : Fin (n + 1) → ℝ) = q := by simp

theorem clean_image_init_eq_projLast {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    Fin.init '' A = projLast A := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩
  · rintro ⟨t, ht⟩
    refine ⟨Fin.snoc x t, ht, ?_⟩
    simp

/-! ## 2. Polynomial evaluation bookkeeping -/

theorem clean_eval_le_add_right (D : ℕ) (b₁ b₂ : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval ![D, 1] b₁ ≤ MvPolynomial.eval ![D, 1] (b₁ + b₂) := by
  rw [MvPolynomial.eval_add]
  exact Nat.le_add_right _ _

theorem clean_eval_le_add_left (D : ℕ) (b₁ b₂ : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval ![D, 1] b₂ ≤ MvPolynomial.eval ![D, 1] (b₁ + b₂) := by
  rw [MvPolynomial.eval_add]
  exact Nat.le_add_left _ _

/-! ## 2b. Membership in the cube -/

theorem clean_mem_inCubeSet_iff {p N : ℕ} (z : Fin (p + N) → ℝ) :
    z ∈ inCubeSet p N ↔ ∀ j : Fin N, z (Fin.natAdd p j) ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · intro h
    have h' := h
    rw [inCubeSet, Set.mem_ofPred_eq, openCube, Set.mem_ofPred_eq] at h'
    exact fun j => h' j
  · intro h
    rw [inCubeSet, Set.mem_ofPred_eq, openCube, Set.mem_ofPred_eq]
    exact fun j => h j

/-! ## 3. Padding a graph by a dummy trailing coordinate -/

theorem clean_graphOf_pad (S : SOMin) (m : ℕ) : ∃ a : ℕ, ∀ (F D : ℕ) (b : MvPolynomial (Fin 2) ℕ)
    (g : (Fin m → ℝ) → ℝ),
    graphOf g ∈ S.Ω F (MvPolynomial.eval ![D, 1] b) (m + 1) →
    graphOf (fun w : Fin (m + 1) → ℝ => g (Fin.init w)) ∈
      S.Ω (F + a) (MvPolynomial.eval ![D, 1] (b + MvPolynomial.C 2)) (m + 1 + 1) := by
  refine ⟨2 * ((m + 2) + (m + 1)) + 1, ?_⟩
  intro F D b g hg
  set σ : Fin (m + 1) → Fin (m + 2) :=
    Fin.snoc (fun j : Fin m => Fin.castSucc (Fin.castSucc j)) (Fin.last (m + 1)) with hσ
  have hset : {x : Fin (m + 2) → ℝ | x ∘ σ ∈ graphOf g} =
      graphOf (fun w : Fin (m + 1) → ℝ => g (Fin.init w)) := by
    ext x
    have h1 : (x ∘ σ) (Fin.last m) = x (Fin.last (m + 1)) := by
      simp only [Function.comp_apply, hσ, Fin.snoc_last]
    have h2 : Fin.init (x ∘ σ) = Fin.init (Fin.init x) := by
      funext j
      simp only [Function.comp_apply, Fin.init, hσ, Fin.snoc_castSucc]
    simp only [Set.mem_ofPred_eq, graphOf, Fin.init, h1, h2]
  have h := GraphComp.subst_mem (S := S) (n := m + 1) (N := m + 2) σ hg
  rw [hset] at h
  have hdeg : MvPolynomial.eval ![D, 1] b + 2 ≤
      MvPolynomial.eval ![D, 1] (b + MvPolynomial.C 2) := by
    rw [MvPolynomial.eval_add]
    simp
  exact Work.WilG1.Omega.mono h (by omega) hdeg

/-! ## 4. The graph of a coordinate -/

theorem clean_graphOf_coord (S : SOMin) (m : ℕ) (j : Fin (m + 1)) :
    graphOf (fun w : Fin (m + 1) → ℝ => w j) ∈ S.Ω (m + 2) 1 (m + 2) := by
  have hset : {x : Fin (m + 2) → ℝ | x (Fin.last (m + 1)) = x (Fin.castSucc j)} =
      graphOf (fun w : Fin (m + 1) → ℝ => w j) := by
    ext x
    simp only [Set.mem_ofPred_eq, graphOf, Fin.init]
  rw [← hset]
  have h := Work.WilG1.Omega.coordEq_mem (S := S) 0 (Fin.last (m + 1)) (Fin.castSucc j)
  simp only [Polynomial.eval_C] at h
  exact h

/-! ## 5. The fibre of a cell over a point -/

theorem clean_slice_graph {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (q : Fin n → ℝ) :
    (∃ a b : EReal, {x : ℝ | Fin.snoc q x ∈
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}} =
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∨
      (∃ c : ℝ, {x : ℝ | Fin.snoc q x ∈
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}} = {c}) := by
  by_cases hq : q ∈ C
  · refine Or.inr ⟨f q, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.init_snoc, Fin.snoc_last]
    exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  · refine Or.inl ⟨0, 0, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨fun h => absurd h.1 hq, fun h => absurd (h.1.trans h.2) (lt_irrefl _)⟩

theorem clean_slice_band {n : ℕ} (C : Set (Fin n → ℝ)) (α β : (Fin n → ℝ) → EReal)
    (q : Fin n → ℝ) :
    (∃ a b : EReal, {x : ℝ | Fin.snoc q x ∈
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
          α (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
          ((z (Fin.last n) : ℝ) : EReal) < β (Fin.init z)}} =
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∨
      (∃ c : ℝ, {x : ℝ | Fin.snoc q x ∈
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
          α (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
          ((z (Fin.last n) : ℝ) : EReal) < β (Fin.init z)}} = {c}) := by
  by_cases hq : q ∈ C
  · refine Or.inl ⟨α q, β q, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hq, h.1, h.2⟩⟩
  · refine Or.inl ⟨0, 0, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨fun h => absurd h.1 hq, fun h => absurd (h.1.trans h.2) (lt_irrefl _)⟩

theorem clean_cell_slice {n : ℕ} {κ : Set (Fin (n + 1) → ℝ)} (h : IsCell (n + 1) κ)
    (q : Fin n → ℝ) :
    (∃ a b : EReal, {x : ℝ | Fin.snoc q x ∈ κ} = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∨
      (∃ c : ℝ, {x : ℝ | Fin.snoc q x ∈ κ} = {c}) := by
  cases h with
  | graph hC f hf => exact clean_slice_graph _ _ q
  | band hC a b ha hb hab => exact clean_slice_band _ _ _ q

/-! ## 6. `EReal` intervals -/

theorem clean_ereal_Ioo_convex {a b : EReal} {x z y : ℝ}
    (hx : a < (x : EReal) ∧ (x : EReal) < b) (hy : a < (y : EReal) ∧ (y : EReal) < b)
    (hxz : x < z) (hzy : z < y) : a < (z : EReal) ∧ (z : EReal) < b :=
  ⟨lt_trans hx.1 (EReal.coe_lt_coe_iff.mpr hxz), lt_trans (EReal.coe_lt_coe_iff.mpr hzy) hy.2⟩

theorem clean_ereal_Ioo_exists_lt {a b : EReal} {x : ℝ} (hx : a < (x : EReal) ∧ (x : EReal) < b) :
    ∃ x' : ℝ, a < (x' : EReal) ∧ (x' : EReal) < b ∧ x' < x := by
  obtain ⟨y, hay, hyx⟩ := EReal.lt_iff_exists_real_btwn.mp hx.1
  exact ⟨y, hay, lt_trans hyx hx.2, EReal.coe_lt_coe_iff.mp hyx⟩

theorem clean_ereal_Ioo_exists_gt {a b : EReal} {x : ℝ} (hx : a < (x : EReal) ∧ (x : EReal) < b) :
    ∃ x' : ℝ, a < (x' : EReal) ∧ (x' : EReal) < b ∧ x < x' := by
  obtain ⟨y, hxy, hyb⟩ := EReal.lt_iff_exists_real_btwn.mp hx.2
  exact ⟨y, lt_trans hx.1 hxy, hyb, EReal.coe_lt_coe_iff.mp hxy⟩

/-! ## 7. Composition with uniform constants -/

theorem clean_GraphOfComp_uniform (S : SOMin) (m : ℕ) :
    ∃ C₁ C₂ : ℕ, ∀ {F₁ F₂ D₁ D₂ : ℕ} (g : (Fin m → ℝ) → ℝ)
      (φ : (Fin m → ℝ) → (Fin m → ℝ)),
      graphOf g ∈ S.Ω F₁ D₁ (m + 1) →
      (∀ j : Fin m, graphOf (fun x : Fin m → ℝ => φ x j) ∈ S.Ω F₂ D₂ (m + 1)) →
      graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + m * D₂ + C₂) (m + 1) := by
  refine ⟨2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1), 2 + 2 * m, ?_⟩
  intro F₁ F₂ D₁ D₂ g φ hg hφ
  have hG : GraphComp.setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (D₁ + 2) ((m + 1) + m) :=
    Work.WilG1.Omega.mono (GraphComp.subst_mem S (GraphComp.sigG m) hg) (by omega) le_rfl
  have hH : ∀ j : Fin m, GraphComp.setH m φ j ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₂ + 2) ((m + 1) + m) :=
    fun j =>
      Work.WilG1.Omega.mono (GraphComp.subst_mem S (GraphComp.sigPhi m j) (hφ j)) (by omega) le_rfl
  have hA2 : (⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
        (m * (D₂ + 2)) ((m + 1) + m) := by
    have h := S.inter (F := F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (n := (m + 1) + m) (D := fun _ : Fin m => D₂ + 2)
      (A := fun j : Fin m => GraphComp.setH m φ j) hH
    have hsum : (∑ _ : Fin m, (D₂ + 2)) = m * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum] at h
    exact h
  have hG' : GraphComp.setG m g ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1) (D₁ + 2) ((m + 1) + m) :=
    Work.WilG1.Omega.mono hG (by omega) le_rfl
  have hInt : (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
        ((D₁ + 2) + m * (D₂ + 2)) ((m + 1) + m) := Work.WilG0.Omega_inter2 hG' hA2
  have hProj : Work.WilG0.projLastIter (m + 1) m
      (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1))
        ((D₁ + 2) + m * (D₂ + 2)) (m + 1) :=
    Work.WilG0.projLastIter_mem S (m + 1) m _ _ _ hInt
  have hset : Work.WilG0.projLastIter (m + 1) m
      (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) = graphOf (g ∘ φ) := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [Set.mem_inter_iff] at hw
      obtain ⟨hGm, hHm⟩ := hw
      rw [Set.mem_iInter] at hHm
      have hlast : x (Fin.last m) = g w := (GraphComp.mem_setG g x w).mp hGm
      have hwx : w = φ (Fin.init x) := by
        funext j
        exact (GraphComp.mem_setH φ j x w).mp (hHm j)
      rw [hwx] at hlast
      simpa [graphOf] using hlast
    · intro hx
      have hx' : x (Fin.last m) = g (φ (Fin.init x)) := by simpa [graphOf] using hx
      refine ⟨φ (Fin.init x), ?_⟩
      rw [Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨(GraphComp.mem_setG g x (φ (Fin.init x))).mpr hx',
        fun j => (GraphComp.mem_setH φ j x (φ (Fin.init x))).mpr rfl⟩
  rw [← hset]
  have hF : ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1)) ≤
      F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1)) := le_of_eq (by ring)
  have hD : (D₁ + 2) + m * (D₂ + 2) ≤ D₁ + m * D₂ + (2 + 2 * m) := le_of_eq (by ring)
  exact Work.WilG1.Omega.mono hProj hF hD


end Work.WilG4c
