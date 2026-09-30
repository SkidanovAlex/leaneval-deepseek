import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ### B1a `transl_basic`: pull-back by the translation action of `G` on the cone

Node `transl_basic` of the block-B split of `zero_estimate_stepwise` (see DESIGN_B.md; the design
table lists it under **B1**, the first wave, with no dependencies and size 0.6-1k).

All the work is bookkeeping about `MvPolynomial.aeval`.  The substitution `transl g` is, by
definition, `MvPolynomial.aeval (uTrans g)` where `uTrans g` is the map on variables

* `X_{i0} ↦ X_{i0}` (the `i = 0` factor included),
* `X_{01} ↦ X_{01} + g₀X_{00}`,
* `X_{i1} ↦ gᵢ X_{i1}` for `i = j.succ`.

Each of the five assertions is then read off from the corresponding property of `aeval`:
`MvPolynomial.comp_aeval_apply` for the pull-back and functoriality statements, a general gradedness
statement `isWeightedHomogeneous_aeval` for the multidegree preservation, and
`MvPolynomial.aeval_X_left` for `transl (gone N) = id`.  The helpers below are `private` on purpose:
the sibling nodes of block B are all imported together, and none of them should have to worry about
names here. -/

namespace Work.BW

/-- The variable substitution defining `transl g`: `aeval (uTrans g) = transl g` by definition. -/
private noncomputable def uTrans {N : ℕ} (g : Fin (N + 1) → ℂ) : Fin (N + 1) × Fin 2 → MR N :=
  fun v => if v.2 = 0 then MvPolynomial.X v
    else if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (g 0) * MvPolynomial.X (0, 0)
    else MvPolynomial.C (g v.1) * MvPolynomial.X v

private lemma transl_eq_aeval {N : ℕ} (g : Fin (N + 1) → ℂ) :
    transl g = MvPolynomial.aeval (uTrans g) := rfl

/-- An algebra map sending every variable to a weighted homogeneous polynomial of the corresponding
weighted degree is graded: it preserves every weighted homogeneous submodule. -/
private lemma isWeightedHomogeneous_aeval {M : Type*} [AddCommMonoid M] {σ τ : Type*}
    {w : τ → M} {w' : σ → M} (u : σ → MvPolynomial τ ℂ)
    (hu : ∀ i, (u i).IsWeightedHomogeneous w (w' i))
    {F : MvPolynomial σ ℂ} {m : M} (hF : F.IsWeightedHomogeneous w' m) :
    (MvPolynomial.aeval u F).IsWeightedHomogeneous w m := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum F.support
    (fun d => MvPolynomial.aeval u (MvPolynomial.monomial d (F.coeff d))) m ?_
  intro d hd
  rw [MvPolynomial.aeval_monomial, Finsupp.prod]
  have hdeg : (∑ i ∈ d.support, (d i) • w' i) = m := by
    rw [← hF (Finsupp.mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
  have hmem := MvPolynomial.IsWeightedHomogeneous.prod d.support
    (fun i => u i ^ (d i)) (fun i => (d i) • w' i) (fun i _ => (hu i).pow (d i))
  rw [hdeg] at hmem
  exact hmem.C_mul _

/-- Every variable image under `uTrans g` is homogeneous of its own multidegree. -/
private lemma uTrans_isWeightedHomogeneous {N : ℕ} (g : Fin (N + 1) → ℂ)
    (v : Fin (N + 1) × Fin 2) :
    (uTrans g v).IsWeightedHomogeneous (mdeg N) (mdeg N v) := by
  obtain ⟨i, b⟩ := v
  fin_cases b
  · simpa [uTrans] using MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 0)
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simpa [uTrans] using (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (0, 1)).add
        ((MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (0, 0)).C_mul (g 0))
    · simpa [uTrans] using
        (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (j.succ, 1)).C_mul (g j.succ)

/-- `τ_g` preserves every multidegree piece of the homogeneous coordinate ring. -/
private lemma homPiece_transl {N : ℕ} (g : Fin (N + 1) → ℂ) (d : Fin (N + 1) →₀ ℕ) (F : MR N)
    (hF : F ∈ homPiece N d) : transl g F ∈ homPiece N d := by
  rw [homPiece] at hF ⊢
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hF ⊢
  exact isWeightedHomogeneous_aeval (uTrans g) (uTrans_isWeightedHomogeneous g) hF

/-- Composition of the substitutions: `aeval (uTrans g) ∘ aeval (uTrans h) = aeval (uTrans (g·h))`. -/
private lemma uTrans_comp {N : ℕ} (g h : Fin (N + 1) → ℂ) :
    (fun v => MvPolynomial.aeval (uTrans g) (uTrans h v)) = uTrans (gmul g h) := by
  funext v
  obtain ⟨i, b⟩ := v
  fin_cases b
  · simp [uTrans]
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp [uTrans, gmul, Fin.cons]; ring
    · simp [uTrans, gmul, Fin.cons]; ring

/-- `τ` is a (right) action: `τ_g ∘ τ_h = τ_{g·h}`. -/
private lemma transl_transl {N : ℕ} (g h : Fin (N + 1) → ℂ) (F : MR N) :
    transl g (transl h F) = transl (gmul g h) F := by
  rw [show transl g (transl h F) =
      MvPolynomial.aeval (uTrans g) (MvPolynomial.aeval (uTrans h) F) from rfl,
    MvPolynomial.comp_aeval_apply (uTrans h) (MvPolynomial.aeval (uTrans g)) F, uTrans_comp]
  rfl

/-- The substitution attached to the neutral element is the identity on variables. -/
private lemma uTrans_gone {N : ℕ} : uTrans (gone N) = fun v => MvPolynomial.X v := by
  funext v
  obtain ⟨i, b⟩ := v
  fin_cases b
  · simp [uTrans]
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp [uTrans, gone, Fin.cons]
    · simp [uTrans, gone, Fin.cons]

/-- `τ` at the neutral element of `G` is the identity. -/
private lemma transl_gone {N : ℕ} (F : MR N) : transl (gone N) F = F := by
  rw [show transl (gone N) F = MvPolynomial.aeval (uTrans (gone N)) F from rfl, uTrans_gone]
  exact MvPolynomial.aeval_X_left_apply F

/-- `g⁻¹ · g = 1` in `G` for `g ∈ G`. -/
private lemma gmul_ginv {N : ℕ} {g : Fin (N + 1) → ℂ} (hg : InG g) : gmul (ginv g) g = gone N := by
  funext i
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp [gmul, ginv, gone, Fin.cons]
  · simp [gmul, ginv, gone, Fin.cons, hg j]

/-- `τ_g` is the pull-back of the action `g ⋆ ·` on cone points. -/
private lemma eval_transl {N : ℕ} (g : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ) (F : MR N) :
    MvPolynomial.eval x (transl g F) = MvPolynomial.eval (coneAct g x) F := by
  have key : (fun v => MvPolynomial.eval x (uTrans g v)) = coneAct g x := by
    funext v
    obtain ⟨i, b⟩ := v
    fin_cases b
    · simp [uTrans, coneAct]
    · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simp [uTrans, coneAct]
      · simp [uTrans, coneAct]
  calc MvPolynomial.eval x (transl g F)
      = MvPolynomial.eval x (MvPolynomial.aeval (uTrans g) F) := rfl
    _ = MvPolynomial.aeval (fun v => MvPolynomial.eval x (uTrans g v)) F :=
        MvPolynomial.comp_aeval_apply (uTrans g) (MvPolynomial.aeval x) F
    _ = MvPolynomial.aeval (coneAct g x) F := by rw [key]
    _ = MvPolynomial.eval (coneAct g x) F := rfl

/-- `coneAct` on the cone point over `y` is the cone point over `g · y`. -/
private lemma coneAct_conePt {N : ℕ} (g : Fin (N + 1) → ℂ) (y : Fin (N + 1) → ℂ) :
    coneAct g (conePt N y) = conePt N (gmul g y) := by
  ext ⟨i, b⟩
  fin_cases b
  · simp [coneAct, conePt]
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp [coneAct, conePt, gmul, Fin.cons]; ring
    · simp [coneAct, conePt, gmul, Fin.cons]

/-- B1a (Philippon 4.1, `c_i = 1`). `τ_g` is the pull-back by `g ⋆ ·`: it maps cone points over
`y` to cone points over `g y`, composes as the group law, preserves every multidegree piece, and
is inverted by `τ_{g⁻¹}` for `g ∈ G`. Proof: `MvPolynomial.aeval` bookkeeping on the variables;
each substitution is linear in its `P¹` factor. Size 0.6–1k. -/
theorem transl_basic {N : ℕ} (g h : Fin (N + 1) → ℂ) :
    (∀ (x : Fin (N + 1) × Fin 2 → ℂ) (F : MR N),
      MvPolynomial.eval x (transl g F) = MvPolynomial.eval (coneAct g x) F) ∧
    (∀ y : Fin (N + 1) → ℂ, coneAct g (conePt N y) = conePt N (gmul g y)) ∧
    (∀ F : MR N, transl g (transl h F) = transl (gmul g h) F) ∧
    (∀ (d : Fin (N + 1) →₀ ℕ) (F : MR N), F ∈ homPiece N d → transl g F ∈ homPiece N d) ∧
    (InG g → ∀ F : MR N, transl (ginv g) (transl g F) = F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x F; exact eval_transl g x F
  · intro y; exact coneAct_conePt g y
  · intro F; exact transl_transl g h F
  · intro d F hF; exact homPiece_transl g d F hF
  · intro hg F
    rw [transl_transl, gmul_ginv hg, transl_gone]

end Work.BW
