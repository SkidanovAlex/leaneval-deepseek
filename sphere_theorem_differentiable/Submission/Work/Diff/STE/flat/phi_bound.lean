/-
# The DeTurck nonlinearity is bounded on the elliptic ball

`Work.Diff.STE.flat.phi_bound`: for a nonlinearity `Φ` of DeTurck shape
(`IsDeTurckNonlin Φ`, i.e. `Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L))` on the
non-degenerate locus) the *norm* `‖Φ (x, (A, L, B))‖` is bounded by a constant `C` depending
only on the dimension, on the ellipticity constant `lam`, and on the size of the matrices
`A`, `L`, `B` — uniformly in `x ∈ [0,1]ⁿ`, in the entry bounds and in the (uniformly elliptic)
matrix `A`.

This is the "the nonlinearity is a bounded function of its arguments on the elliptic ball"
input of the Galerkin scheme (`energy_apriori`, `galerkin_ode_existence`).

## Proof

By compactness, and *without any analysis of `secOpFlat`*:

* the hypotheses `x ∈ [0,1]ⁿ`, `‖A i j‖ ≤ BA`, `‖L i‖ ≤ BL`, `‖B i j‖ ≤ BB` describe compact
  sets of `x`, `A`, `L`, `B`;
* the remaining hypotheses (symmetry of `reMat A` and the quadratic-form ellipticity bound
  with constant `lam > 0`) are *closed* conditions, so the set `S` of all admissible data is
  compact;
* on `S` the determinant of `reMat A` does not vanish: the symmetry makes `reMat A` Hermitian
  and the ellipticity inequality makes it positive definite (`lam > 0`), so its determinant is
  positive (`Matrix.PosDef.det_pos`);
* hence `S` is contained in the *open* set `Set.univ ×ˢ {w | (reMat w.1).det ≠ 0}` on which
  `Φ` is continuous (`ContDiffOn.continuousOn`), and a continuous function on a compact set is
  bounded (`IsCompact.exists_bound_of_continuousOn`).

That is the whole content.  Note that the bound is *not* closed under `A ↦ A + ε • I`-type
arguments: the constant `C` genuinely depends on `BA`, `BL`, `BB` and `lam`, as it must (the
term `secOpFlat A B` is quadratic in the size of `A` and `B`).
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- Each entry of the real part of a matrix is a continuous function of the matrix. -/
@[fun_prop]
lemma continuous_reMat_apply {n : ℕ} (i j : Fin n) :
    Continuous (fun A : Work.Diff.STE.Flat.MatC n => Work.Diff.STE.Flat.reMat A i j) := by
  simp only [Work.Diff.STE.Flat.reMat_apply]
  exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))

/-- A symmetric matrix whose quadratic form is bounded below by `lam * ‖v‖²` with `lam > 0` is
positive definite, so its determinant does not vanish.  (No continuity is needed here: this is
the pointwise reason why the admissible set avoids the singular locus of `reMat`.) -/
lemma reMat_det_ne_zero_of_elliptic {n : ℕ} (A : Work.Diff.STE.Flat.MatC n) {lam : ℝ}
    (hlam : 0 < lam)
    (hsym : ∀ i j, Work.Diff.STE.Flat.reMat A i j = Work.Diff.STE.Flat.reMat A j i)
    (hpos : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * v i * v j) :
    (Work.Diff.STE.Flat.reMat A).det ≠ 0 := by
  have hHerm : (Work.Diff.STE.Flat.reMat A).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext (fun i j => hsym j i)
  have hpd : (Work.Diff.STE.Flat.reMat A).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hHerm, ?_⟩
    intro v hv
    -- `∑ i, v i ^ 2 > 0` for `v ≠ 0`
    have hsum : 0 < ∑ i : Fin n, (v i) ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    -- the two quadratic forms agree
    have hquad : star v ⬝ᵥ (Work.Diff.STE.Flat.reMat A).mulVec v
        = ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * v i * v j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hquad]
    exact lt_of_lt_of_le (mul_pos hlam hsum) (hpos v)
  exact ne_of_gt (Matrix.PosDef.det_pos hpd)

theorem phi_bound (n : ℕ)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (BA BL BB : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ)
      (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
      (A : Work.Diff.STE.Flat.MatC n) (L : Fin n → Work.Diff.STE.Flat.MatC n)
      (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j, Work.Diff.STE.Flat.reMat A i j = Work.Diff.STE.Flat.reMat A j i) →
      (∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * v i * v j) →
      (∀ i j, ‖A i j‖ ≤ BA) → (∀ i, ‖L i‖ ≤ BL) → (∀ i j, ‖B i j‖ ≤ BB) →
      ‖Φ (x, (A, L, B))‖ ≤ C := by
  classical
  -- `Φ` is continuous on the (open) non-degeneracy locus
  obtain ⟨hcont, -⟩ := hshape
  -- the compact box of admissible data
  set cube : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)
    with hcube
  set KA : Set (Work.Diff.STE.Flat.MatC n) :=
    Set.univ.pi (fun _ : Fin n =>
      Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) (max BA 0))) with hKA
  set KL : Set (Fin n → Work.Diff.STE.Flat.MatC n) :=
    Set.univ.pi (fun _ : Fin n =>
      Metric.closedBall (0 : Work.Diff.STE.Flat.MatC n) (max BL 0)) with hKL
  set KB : Set (Fin n → Fin n → Work.Diff.STE.Flat.MatC n) :=
    Set.univ.pi (fun _ : Fin n =>
      Set.univ.pi (fun _ : Fin n =>
        Metric.closedBall (0 : Work.Diff.STE.Flat.MatC n) (max BB 0))) with hKB
  set T : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) := cube ×ˢ (KA ×ˢ (KL ×ˢ KB))
    with hT
  -- the two closed conditions (symmetry of `reMat A`, ellipticity)
  set Csym : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) :=
    ⋂ (i : Fin n), ⋂ (j : Fin n),
      {p | Work.Diff.STE.Flat.reMat (p.2.1) i j = Work.Diff.STE.Flat.reMat (p.2.1) j i}
    with hCsym
  set Cpos : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) :=
    ⋂ (v : Fin n → ℝ), {p | lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (p.2.1) i j * v i * v j} with hCpos
  set S : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) := T ∩ Csym ∩ Cpos with hS
  have hTcomp : IsCompact T := by
    rw [hT, hcube, hKA, hKL, hKB]
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_Icc) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hsymC : IsClosed Csym := by
    rw [hCsym]
    refine isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq ?_ ?_ <;> fun_prop
  have hposC : IsClosed Cpos := by
    rw [hCpos]
    refine isClosed_iInter fun _ => isClosed_le continuous_const ?_
    fun_prop
  have hScomp : IsCompact S := by
    rw [hS]
    exact (hTcomp.inter_right hsymC).inter_right hposC
  -- on `S` the determinant of `reMat` does not vanish
  have hSsub : S ⊆ Set.univ ×ˢ
      {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := by
    intro p hp
    rw [hS] at hp
    obtain ⟨⟨_, hsymp⟩, hposp⟩ := hp
    rw [hCsym] at hsymp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hsymp
    rw [hCpos] at hposp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hposp
    exact ⟨trivial, reMat_det_ne_zero_of_elliptic p.2.1 hlam hsymp hposp⟩
  obtain ⟨C, hC⟩ :=
    hScomp.exists_bound_of_continuousOn ((ContDiffOn.continuousOn hcont).mono hSsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx A L B hsym hpos hA hL hB
  have hmem : (x, (A, L, B)) ∈ S := by
    rw [hS]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hT]
      refine ⟨hx, ?_, ?_, ?_⟩
      · rw [hKA]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (hA i j) (le_max_left _ _)
      · rw [hKL]
        intro i _
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (hL i) (le_max_left _ _)
      · rw [hKB]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (hB i j) (le_max_left _ _)
    · rw [hCsym]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hsym
    · rw [hCpos]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hpos
  exact le_trans (hC _ hmem) (le_max_left C 0)

end Work.Diff.STE.flat
