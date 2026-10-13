/-
  WilG4c / `SliceC1FD` — the `Ω`-encoding of the *pointwise* `ε`-`δ` Fréchet-differentiability
  condition of a family (the "FD set"), and of the fibre `C¹`-locus `C1Pred`.

  The construction is carried out with the shape calculus `TSh` of `Submission.Work.WilG4c.TSh`:
  every atom is a `PKS`, every quantifier a `PKS.exi` (one real variable), `PKS.exb` (a block of
  `M` real variables) or `PKS.allb`/`allOne` (universal), and the format/degree of the result are
  the shape's `Fmt`/`Deg`, so no arithmetic has to be done by hand.

  Everything is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.TSh

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Reading the assembled points -/

/-- Lifting a position by one coordinate (used for the single-variable quantifiers). -/
def lift1 {K : ℕ} (i : Fin K) : Fin (K + 1) := i.castSucc

/-- Lifting a position by `M` coordinates (used for the block quantifiers). -/
def liftM {M K : ℕ} (i : Fin K) : Fin (K + M) := Fin.castAdd M i

@[simp] theorem lift1_apply {K : ℕ} (i : Fin K) : (lift1 i).val = i.val := rfl

@[simp] theorem liftM_apply {M K : ℕ} (i : Fin K) : (liftM (M := M) i).val = i.val := rfl

@[simp] theorem castAdd_one_eq_castSucc {n : ℕ} (i : Fin n) :
    Fin.castAdd 1 i = i.castSucc := Fin.ext rfl

@[simp] theorem snoc_castSucc' {n : ℕ} (z : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) z t i.castSucc = z i :=
  Fin.snoc_castSucc (α := fun _ => ℝ) t z i

@[simp] theorem snoc_last' {n : ℕ} (z : Fin n → ℝ) (t : ℝ) :
    Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) z t (Fin.last n) = t :=
  Fin.snoc_last (α := fun _ : Fin (n + 1) => ℝ) t z

@[simp] theorem append_left' {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin m) :
    Fin.append a b (Fin.castAdd n i) = a i := Fin.append_left a b i

@[simp] theorem append_right' {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    Fin.append a b (Fin.natAdd m i) = b i := Fin.append_right a b i

theorem append_comp {P M K : ℕ} (iw : Fin P → Fin K) (iy : Fin M → Fin K) (z : Fin K → ℝ) :
    z ∘ Fin.append iw iy = Fin.append (z ∘ iw) (z ∘ iy) := by
  funext a
  induction a using Fin.addCases with
  | left i => simp
  | right j => simp

/-! ## 2. The graph index map -/

/-- The index map picking `(params, point, value)` — i.e. the graph point of the family. -/
def memIdx {P M K : ℕ} (iw : Fin P → Fin K) (iy : Fin M → Fin K) (it : Fin K) :
    Fin (P + M + 1) → Fin K :=
  Fin.snoc (Fin.append iw iy) it

theorem memIdx_comp {P M K : ℕ} (iw : Fin P → Fin K) (iy : Fin M → Fin K) (it : Fin K)
    (z : Fin K → ℝ) :
    z ∘ memIdx iw iy it = Fin.snoc (Fin.append (z ∘ iw) (z ∘ iy)) (z it) := by
  rw [memIdx, Fin.comp_snoc, append_comp]

theorem memIdx_graph {P M K : ℕ} {G : (Fin (P + M) → ℝ) → ℝ}
    (iw : Fin P → Fin K) (iy : Fin M → Fin K) (it : Fin K) (z : Fin K → ℝ) :
    (z ∘ memIdx iw iy it ∈ graphOf G) ↔ z it = G (Fin.append (z ∘ iw) (z ∘ iy)) := by
  have hlast : (z ∘ memIdx iw iy it) (Fin.last (P + M)) = z it := by
    rw [memIdx_comp, snoc_last']
  have hinit : Fin.init (z ∘ memIdx iw iy it) = z ∘ Fin.append iw iy := by
    rw [memIdx_comp, Fin.init_snoc, append_comp]
  rw [graphOf, Set.mem_setOf_eq, hlast, hinit, append_comp]

/-! ## 3. The universal quantification of a single variable -/

/-- `∀ t : ℝ` applied to a shape in the next dimension. -/
def PKS.allOne {S : SOMin} {F D n : ℕ} (s : PKS S F D (n + 1)) : PKS S F D n :=
  PKS.neg (PKS.exi (PKS.neg s))

theorem PKS.Real_allOne {S : SOMin} {F D n : ℕ} (s : PKS S F D (n + 1)) :
    (PKS.allOne s).Real = {x : Fin n → ℝ | ∀ t : ℝ, Fin.snoc x t ∈ s.Real} := by
  ext x
  simp only [PKS.allOne, PKS.Real_neg, PKS.Real_exi, projLast, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  constructor
  · intro h t
    by_contra ht
    exact h ⟨t, ht⟩
  · rintro h ⟨t, ht⟩
    exact ht (h t)

/-! ## 4. The Fréchet-differentiability set -/

theorem td_lin {K : ℕ} (a b : Fin K) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin K) ℝ).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  omega

theorem td_prod {K : ℕ} (c d e : Fin K) :
    (MvPolynomial.X c * (MvPolynomial.X d - MvPolynomial.X e) :
      MvPolynomial (Fin K) ℝ).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h : (MvPolynomial.X d - MvPolynomial.X e : MvPolynomial (Fin K) ℝ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have hc : (MvPolynomial.X c : MvPolynomial (Fin K) ℝ).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_X]
  omega

theorem td_affine {M K : ℕ} (a b : Fin K) (ic id ie : Fin M → Fin K) :
    (MvPolynomial.X a - MvPolynomial.X b - ∑ j : Fin M,
      MvPolynomial.X (ic j) * (MvPolynomial.X (id j) - MvPolynomial.X (ie j)) :
      MvPolynomial (Fin K) ℝ).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (td_lin a b) ?_)
  exact MvPolynomial.totalDegree_finsetSum_le fun j _ => td_prod (ic j) (id j) (ie j)

theorem td_sq_of_two {K : ℕ} {P : MvPolynomial (Fin K) ℝ} (h : P.totalDegree ≤ 2) :
    (P ^ 2).totalDegree ≤ 4 := by
  refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
  omega

theorem td_X_sq2 {K : ℕ} (i : Fin K) :
    ((MvPolynomial.X i) ^ 2 : MvPolynomial (Fin K) ℝ).totalDegree ≤ 2 := by
  rw [MvPolynomial.totalDegree_X_pow]

theorem td_mul_sq {K : ℕ} {P Q : MvPolynomial (Fin K) ℝ} (hP : P.totalDegree ≤ 2)
    (hQ : Q.totalDegree ≤ 2) : (P * Q).totalDegree ≤ 4 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  omega

theorem read_iw {P M K : ℕ} (iw : Fin P → Fin K) (z : Fin K → ℝ) (y : Fin M → ℝ)
    (t t₁ t₂ : ℝ) :
    (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂) ∘
      (fun i : Fin P => (Fin.castAdd M ((iw i).castSucc.castSucc)).castSucc) = z ∘ iw := by
  funext i
  simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']

theorem read_iy {P M K : ℕ} (iy : Fin M → Fin K) (z : Fin K → ℝ) (y : Fin M → ℝ)
    (t t₁ t₂ : ℝ) :
    (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂) ∘
      (fun j : Fin M => (Fin.castAdd M ((iy j).castSucc.castSucc)).castSucc) = z ∘ iy := by
  funext i
  simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']

theorem read_it {M K : ℕ} (it : Fin K) (z : Fin K → ℝ) (y : Fin M → ℝ)
    (t t₁ t₂ : ℝ) :
    ((Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂ : Fin (K+1+1+M+1) → ℝ)
      (lift1 (liftM (lift1 (lift1 it))))) = z it := by
  simp only [lift1, liftM, castAdd_one_eq_castSucc, snoc_castSucc', append_left']

theorem read_y2 {P M K : ℕ} (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ t₂ : ℝ) :
    (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂) ∘
      (fun j : Fin M => (Fin.natAdd (K + 1 + 1) j).castSucc) = y := by
  funext i
  simp only [Function.comp_apply, snoc_castSucc', append_right']

theorem read_t2 {M K : ℕ} (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ t₂ : ℝ) :
    ((Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂ : Fin (K+1+1+M+1) → ℝ)
      (Fin.last (K + 1 + 1 + M))) = t₂ := by
  simp only [snoc_last']

theorem read_eps {M K : ℕ} (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ t₂ : ℝ) :
    ((Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) t₂ : Fin (K+1+1+M+1) → ℝ)
      (lift1 (liftM (lift1 (Fin.last K))))) = t := by
  simp only [lift1, liftM, castAdd_one_eq_castSucc, snoc_castSucc', snoc_last', append_left']

theorem read_iwB {P M K : ℕ} (iw : Fin P → Fin K) (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ : ℝ) :
    (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) ∘
      (fun i : Fin P => Fin.castAdd M ((iw i).castSucc.castSucc)) = z ∘ iw := by
  funext i
  simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']

theorem read_iyB {P M K : ℕ} (iy : Fin M → Fin K) (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ : ℝ) :
    (Fin.append (Fin.snoc (Fin.snoc z t) t₁) y) ∘
      (fun j : Fin M => Fin.castAdd M ((iy j).castSucc.castSucc)) = z ∘ iy := by
  funext i
  simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']

theorem read_delB {M K : ℕ} (z : Fin K → ℝ) (y : Fin M → ℝ) (t t₁ : ℝ) :
    ((Fin.append (Fin.snoc (Fin.snoc z t) t₁) y : Fin (K+1+1+M) → ℝ)
      (Fin.castAdd M (Fin.last (K+1)))) = t₁ := by
  simp only [lift1, liftM, castAdd_one_eq_castSucc, snoc_castSucc', snoc_last', append_left']

/-- **The Fréchet-differentiability condition**, with the value `z it` of the family member at
the base point supplied as a coordinate.  Realises
`∀ ε > 0, ∃ δ > 0, ∀ y', ℓ²(y' - y) < δ² → ∃ t', (graph point at (y',t') ∈ G) ∧ (ineq)`. -/
def fdP (S : SOMin) (F D : ℕ) {P M : ℕ} (G : Set (Fin (P + M + 1) → ℝ))
    (hG : G ∈ S.Ω F D (P + M + 1))
    {K : ℕ} (iw : Fin P → Fin K) (iy ic : Fin M → Fin K) (it : Fin K) : PKS S F D K :=
  PKS.allOne
    (PKS.imp (posS S F D (Fin.last K))
      (PKS.exi
        (PKS.conj (posS S F D (Fin.last (K + 1)))
          (PKS.allb (k := M)
            (PKS.imp
              (ballS S F D (fun j : Fin M => Fin.natAdd (K + 1 + 1) j)
                (fun j : Fin M => liftM (lift1 (lift1 (iy j))))
                (liftM (Fin.last (K + 1))))
              (PKS.exi
                (PKS.conj
                  (PKS.mem G hG
                    (memIdx (fun i : Fin P => lift1 (liftM (lift1 (lift1 (iw i)))))
                      (fun j : Fin M => lift1 (Fin.natAdd (K + 1 + 1) j))
                      (Fin.last (K + 1 + 1 + M))))
                  (leS S F D
                    ((MvPolynomial.X (Fin.last (K + 1 + 1 + M)) -
                        MvPolynomial.X (lift1 (liftM (lift1 (lift1 it)))) -
                        ∑ j : Fin M,
                          MvPolynomial.X (lift1 (liftM (lift1 (lift1 (ic j))))) *
                            (MvPolynomial.X (lift1 (Fin.natAdd (K + 1 + 1) j)) -
                              MvPolynomial.X (lift1 (liftM (lift1 (lift1 (iy j))))))) ^ 2)
                    ((MvPolynomial.X (lift1 (liftM (lift1 (Fin.last K))))) ^ 2 *
                      sqSum (fun j : Fin M => lift1 (Fin.natAdd (K + 1 + 1) j))
                        (fun j : Fin M => lift1 (liftM (lift1 (lift1 (iy j))))))
                    (td_sq_of_two (td_affine _ _ _ _ _))
                    (td_mul_sq (td_X_sq2 _) (sqSum_td _ _))))))))))

theorem fdP_Real {S : SOMin} {F D P M : ℕ} {G : Set (Fin (P + M + 1) → ℝ)}
    (hG : G ∈ S.Ω F D (P + M + 1)) {K : ℕ} (iw : Fin P → Fin K) (iy ic : Fin M → Fin K)
    (it : Fin K) :
    (fdP S F D G hG iw iy ic it).Real = {z : Fin K → ℝ |
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' : Fin M → ℝ,
        (∑ j : Fin M, (y' j - z (iy j)) ^ 2) < δ ^ 2 →
          ∃ t' : ℝ, (Fin.snoc (Fin.append (z ∘ iw) y') t' ∈ G) ∧
            (t' - z it - ∑ j : Fin M, z (ic j) * (y' j - z (iy j))) ^ 2 ≤
              ε ^ 2 * ∑ j : Fin M, (y' j - z (iy j)) ^ 2} := by
  ext z
  simp only [fdP, PKS.Real_allOne, PKS.Real_imp, PKS.Real_neg, PKS.Real_exi, PKS.Real_conj,
    PKS.Real_mem, PKS.Real_poly, PKS.Real_allb, PKS.Real_exb, posS_Real, ballS_Real, leS_Real,
    projLast, Work.WilG5.projN, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_union, not_exists, not_not, Function.comp_apply, memIdx_comp, lift1, liftM,
    castAdd_one_eq_castSucc, snoc_castSucc', snoc_last', append_left', append_right',
    MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_sum, MvPolynomial.eval_X,
    MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_C, sqSum]
  constructor
  · intro h ε hε
    rcases h ε with hbad | hgood
    · exact absurd hε hbad
    obtain ⟨δ, hδ, hy⟩ := hgood
    refine ⟨δ, hδ, fun y' hy' => ?_⟩
    rcases hy y' with hbad | hgood
    · exact absurd hy' hbad
    obtain ⟨t', hmem, hineq⟩ := hgood
    refine ⟨t', ?_, hineq⟩
    have h1 : (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z ε) δ) y') t') ∘
        (fun i : Fin P => (Fin.castAdd M ((iw i).castSucc.castSucc)).castSucc) = z ∘ iw := by
      funext i
      simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']
    have h2 : (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z ε) δ) y') t') ∘
        (fun j : Fin M => (Fin.natAdd (K + 1 + 1) j).castSucc) = y' := by
      funext j
      simp only [Function.comp_apply, snoc_castSucc', append_right']
    rw [h1, h2] at hmem
    exact hmem
  · intro h ε
    by_cases hε : 0 < ε
    · obtain ⟨δ, hδ, hy⟩ := h ε hε
      refine Or.inr ⟨δ, hδ, fun y' => ?_⟩
      by_cases hy' : (∑ j : Fin M, (y' j - z (iy j)) ^ 2) < δ ^ 2
      · obtain ⟨t', hmem, hineq⟩ := hy y' hy'
        refine Or.inr ⟨t', ?_, hineq⟩
        have h1 : (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z ε) δ) y') t') ∘
            (fun i : Fin P => (Fin.castAdd M ((iw i).castSucc.castSucc)).castSucc) = z ∘ iw := by
          funext i
          simp only [Function.comp_apply, castAdd_one_eq_castSucc, snoc_castSucc', append_left']
        have h2 : (Fin.snoc (Fin.append (Fin.snoc (Fin.snoc z ε) δ) y') t') ∘
            (fun j : Fin M => (Fin.natAdd (K + 1 + 1) j).castSucc) = y' := by
          funext j
          simp only [Function.comp_apply, snoc_castSucc', append_right']
        rw [h1, h2]
        exact hmem
      · exact Or.inl hy'
    · exact Or.inl hε

/-! ## 5. General reading lemmas for the peel layers -/

@[simp] theorem comp_snoc_lift {n : ℕ} (w : Fin n → ℝ) (b : ℝ) {ι : Type*} (f : ι → Fin n) :
    (Fin.snoc w b) ∘ (fun i => (f i).castSucc) = w ∘ f := by
  funext i
  simp only [Function.comp_apply, snoc_castSucc']

@[simp] theorem comp_append_liftM {n M : ℕ} (w : Fin n → ℝ) (y : Fin M → ℝ)
    {ι : Type*} (f : ι → Fin n) :
    (Fin.append w y) ∘ (fun i => Fin.castAdd M (f i)) = w ∘ f := by
  funext i
  simp only [Function.comp_apply, append_left']

@[simp] theorem comp_append_liftN {n M : ℕ} (w : Fin n → ℝ) (y : Fin M → ℝ)
    {ι : Type*} (f : ι → Fin M) :
    (Fin.append w y) ∘ (fun i => Fin.natAdd n (f i)) = y ∘ f := by
  funext i
  simp only [Function.comp_apply, append_right']

@[simp] theorem comp_snoc_lift_pt {n : ℕ} (w : Fin n → ℝ) (b : ℝ) :
    (Fin.snoc w b) ∘ (Fin.castSucc) = w := by
  funext i
  simp only [Function.comp_apply, snoc_castSucc']

@[simp] theorem comp_append_liftM_pt {n M : ℕ} (w : Fin n → ℝ) (y : Fin M → ℝ) :
    (Fin.append w y) ∘ (Fin.castAdd M) = w := by
  funext i
  simp only [Function.comp_apply, append_left']

@[simp] theorem comp_append_liftN_pt {n M : ℕ} (w : Fin n → ℝ) (y : Fin M → ℝ) :
    (Fin.append w y) ∘ (Fin.natAdd n) = y := by
  funext i
  simp only [Function.comp_apply, append_right']

end Work.WilG4c
