import Mathlib
import Submission.Work.L2F.Props.OddSubDefs

/-!
# Eigenline vocabulary for `isCyclic_of_no_unipotent`

The proof that an odd-order subgroup `K ≤ PGL(2,F)` with no unipotent lift is cyclic goes
through the action of the preimage in `SL(2,F)` on the projective line over the algebraic
closure `F̄` of `F`:  a non-scalar, non-unipotent element of `SL(2,F)` has two distinct
eigenvalues in `F̄`, hence acts on `ℙ¹(F̄)` with exactly two fixed points.  A counting
argument then shows that the whole group fixes two distinct points, and a group in
`SL(2,F)` fixing two distinct points of `ℙ¹(F̄)` is isomorphic to a finite subgroup of `F̄ˣ`,
hence cyclic.

This file only collects the vocabulary (the projective line over `F̄`, the base change
`SL(2,F) → SL(2,F̄)` and the set of eigenpoints of a `2 × 2` matrix) together with the
easy bridge between eigenpoints and fixed points of the action; the substantive lemmas are
stated elsewhere.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

noncomputable section

/-- The projective line `ℙ¹` over the algebraic closure of `F` (points of `F̄²` up to scalars). -/
abbrev PLineFbar (F : Type*) [Field F] :=
  Projectivization (AlgebraicClosure F) (Fin 2 → AlgebraicClosure F)

/-- Base change of `SL(2,F)` to `SL(2,F̄)` along `F → F̄`. -/
def baseChangeSL (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F) :=
  Matrix.SpecialLinearGroup.map (algebraMap F (AlgebraicClosure F))

/-- The set of *eigenpoints* of a `2 × 2` matrix `m` over a field `E`: the lines of `E²` which
are spanned by an eigenvector of `m`.  Using the chosen representative `p.rep` of a point `p`
of the projective line, this is the set of `p` with `m *ᵥ p.rep ∈ E ∙ p.rep`. -/
def eigenPointSet {E : Type*} [Field E] (m : Matrix (Fin 2) (Fin 2) E) :
    Set (Projectivization E (Fin 2 → E)) :=
  {p | ∃ c : E, m *ᵥ p.rep = c • p.rep}

/-- **The fixed points of `m ∈ SL(2,E)` acting on `ℙ¹(E)` are exactly the eigenpoints of `m`.** -/
theorem mem_fixedBy_iff_mem_eigenPointSet {E : Type*} [Field E]
    (m : Matrix.SpecialLinearGroup (Fin 2) E) (p : Projectivization E (Fin 2 → E)) :
    p ∈ MulAction.fixedBy (Projectivization E (Fin 2 → E)) m ↔
      p ∈ eigenPointSet (m : Matrix (Fin 2) (Fin 2) E) := by
  have hmv : ∀ v : Fin 2 → E, m • v = ((m : Matrix (Fin 2) (Fin 2) E)) *ᵥ v := fun v => by
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  have hsm : m • p = Projectivization.mk E (m • p.rep)
      ((smul_ne_zero_iff_ne m).mpr (Projectivization.rep_nonzero p)) := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    rw [Projectivization.smul_mk]
  rw [MulAction.mem_fixedBy, hsm]
  have hrep := Projectivization.mk_rep p
  constructor
  · intro h
    have h2 : Projectivization.mk E (m • p.rep)
        ((smul_ne_zero_iff_ne m).mpr (Projectivization.rep_nonzero p))
        = Projectivization.mk E p.rep (Projectivization.rep_nonzero p) := h.trans hrep.symm
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨a, ha⟩ := h2
    refine ⟨(a : E), ?_⟩
    rw [← hmv, ← ha, Units.smul_def]
  · rintro ⟨c, hc⟩
    have hcm : c ≠ 0 := by
      intro h0
      have hz : m • p.rep = 0 := by rw [hmv, hc, h0, zero_smul]
      have hcontra : p.rep = 0 := by
        calc p.rep = (m⁻¹ * m) • p.rep := by rw [inv_mul_cancel, one_smul]
          _ = m⁻¹ • (m • p.rep) := by rw [mul_smul]
          _ = 0 := by rw [hz, smul_zero]
      exact Projectivization.rep_nonzero p hcontra
    have h2 : Projectivization.mk E (m • p.rep)
        ((smul_ne_zero_iff_ne m).mpr (Projectivization.rep_nonzero p))
        = Projectivization.mk E p.rep (Projectivization.rep_nonzero p) := by
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 c hcm, ?_⟩
      rw [Units.smul_def, Units.val_mk0, ← hc, ← hmv]
    rw [h2, hrep]

end

end Work.L2F.Props.oddsub
