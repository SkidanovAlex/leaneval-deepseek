/-
# The DeTurck nonlinearity is bounded on the elliptic ball, *without* symmetry of `A`

`Work.Diff.STE.flat.phi_bound_nosym` is the same statement as `Work.Diff.STE.flat.phi_bound`, but
with the hypothesis

> `∀ i j, reMat A i j = reMat A j i`  (symmetry of the real part of the value matrix)

**removed**.  This is what the Galerkin scheme actually needs: the projected ODE
(`galerkin_ode_existence`) is run on *matrix-valued* coefficients without an a priori symmetry
constraint, and the only structural hypothesis available at a solution is the *quadratic-form*
ellipticity bound

> `lam * ‖v‖² ≤ ∑ᵢ ∑ⱼ reMat A i j vᵢ vⱼ`  for all `v`, with `lam > 0`.

## Proof

Exactly the compactness argument of `phi_bound.lean`: the admissible data (`x ∈ [0,1]ⁿ`, entries of
`A`, `L`, `B` bounded by `BA`, `BL`, `BB`, and the quadratic-form ellipticity bound) form a compact
set `S`, on which `Φ` is continuous because `IsDeTurckNonlin` makes `Φ` smooth on the open set
`Set.univ ×ˢ {w | (reMat w.1).det ≠ 0}`.

The only change is *why* `S` avoids the singular locus `{det (reMat ·) = 0}`.  With the symmetry
hypothesis this came from positive definiteness (`Matrix.PosDef.det_pos`).  Without it, it comes
from the observation that a matrix whose quadratic form dominates `lam * ‖v‖²` with `lam > 0`
cannot kill a nonzero vector: if `M v = 0` then `v ⬝ᵥ M v = 0`, while the hypothesis gives
`v ⬝ᵥ M v = ∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ ≥ lam * ∑ᵢ vᵢ² > 0`.  This is precisely the lemma
`Work.Diff.STE.flat.det_ne_zero_of_quadForm_le` (already proved, and `det ∘ reMat`-composed below);
no symmetry of `M` is involved anywhere.

That is the whole content.  As in `phi_bound.lean` the bound genuinely depends on `BA`, `BL`, `BB`
and `lam` (the term `secOpFlat A B` is quadratic in the sizes of `A` and `B`).
-/
import Mathlib
import Submission.Work.Diff.STE.flat.phi_bound
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- A (not necessarily symmetric) complex matrix whose real quadratic form dominates
`lam * ‖v‖²` with `lam > 0` has nonvanishing real determinant.

This is `Work.Diff.STE.flat.det_ne_zero_of_quadForm_le` transported to complex matrices along
`reMat`.  It replaces the positive-definiteness argument of
`Work.Diff.STE.flat.reMat_det_ne_zero_of_elliptic`, which needed the symmetry of `reMat A`. -/
lemma reMat_det_ne_zero_of_quadForm {n : ℕ} (A : Work.Diff.STE.Flat.MatC n) {lam : ℝ}
    (hlam : 0 < lam)
    (hpos : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * v i * v j) :
    (Work.Diff.STE.Flat.reMat A).det ≠ 0 :=
  det_ne_zero_of_quadForm_le (Work.Diff.STE.Flat.reMat A) hlam hpos

theorem phi_bound_nosym (n : ℕ)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (BA BL BB : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ)
      (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
      (A : Work.Diff.STE.Flat.MatC n) (L : Fin n → Work.Diff.STE.Flat.MatC n)
      (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
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
  -- the closed ellipticity condition
  set Cpos : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) :=
    ⋂ (v : Fin n → ℝ), {p | lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (p.2.1) i j * v i * v j} with hCpos
  set S : Set ((Fin n → ℝ) × Work.Diff.STE.Flat.Jet n) := T ∩ Cpos with hS
  have hTcomp : IsCompact T := by
    rw [hT, hcube, hKA, hKL, hKB]
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_Icc) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hposC : IsClosed Cpos := by
    rw [hCpos]
    refine isClosed_iInter fun _ => isClosed_le continuous_const ?_
    fun_prop
  have hScomp : IsCompact S := by
    rw [hS]
    exact hTcomp.inter_right hposC
  -- on `S` the determinant of `reMat` does not vanish
  have hSsub : S ⊆ Set.univ ×ˢ
      {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := by
    intro p hp
    rw [hS] at hp
    obtain ⟨_, hposp⟩ := hp
    rw [hCpos] at hposp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hposp
    exact ⟨trivial, reMat_det_ne_zero_of_quadForm p.2.1 hlam hposp⟩
  obtain ⟨C, hC⟩ :=
    hScomp.exists_bound_of_continuousOn ((ContDiffOn.continuousOn hcont).mono hSsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx A L B hpos hA hL hB
  have hmem : (x, (A, L, B)) ∈ S := by
    rw [hS]
    refine ⟨?_, ?_⟩
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
    · rw [hCpos]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hpos
  exact le_trans (hC _ hmem) (le_max_left C 0)

end Work.Diff.STE.flat
