import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesH.Norm.JointDefs
import Submission.Work.WilkiesH.Norm.normPiece_mem
import Submission.Work.WilkiesH.Norm.normJointGraph_mem
import Submission.Work.WilG0.API

/-!
# Area H (counting) — the normalised image is `Ω`-definable

For a sharply o-minimal structure `S`, a set `A ∈ S.Ω F D n` and a shape vector
`σ : Fin n → NormShape`, the normalised image `normSet σ A = normMap σ '' (A ∩ normPiece σ)`
belongs to `S.Ω (F + a) (D + b) n` for constants `a`, `b` depending only on `n` (and `σ`).
This is what lets the counting induction replace `A` by `normSet σ A ⊆ cube01 n` without
leaving the class `Ω` at a bounded cost.

The proof projects the joint set `normJoint σ A ⊆ ℝⁿ × ℝⁿ` of `JointDefs` (its first block is
the image, its last block the source, the two tied by the shape relations):

* `liftLast n A ∈ S.Ω (F + n) D (n + n)` and
  `liftLast n (normPiece σ) ∈ S.Ω (Fa + n) Da (n + n)` (`liftLast_mem`, `normPiece_mem`);
* `normJointGraph σ ∈ S.Ω Fb Db (n + n)` (`normJointGraph_mem`);
* intersecting the three (`Omega_inter2`) and projecting the source block away (`projN_mem`)
  gives a member of `S.Ω (((F + K) + 1) + 1 + n) ((D + Da) + Db) n` with
  `K = max n (max (Fa + n) Fb)`, which by `projN_normJoint_eq` is exactly `normSet σ A`.

The stated constants are the resulting arithmetic cost; only their existence is asserted.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture
open Work.WilG5

theorem normSet_mem {n : ℕ} {S : WilkiesDesign.SOMin} (σ : Fin n → NormShape) : ∃ a b : ℕ, ∀ {F D : ℕ} {A : Set (Fin n → ℝ)}, A ∈ S.Ω F D n → normSet σ A ∈ S.Ω (F + a) (D + b) n := by
  obtain ⟨Fa, Da, hPiece⟩ := normPiece_mem σ
  obtain ⟨Fb, Db, hGraph⟩ := normJointGraph_mem σ
  refine ⟨max n (max (Fa + n) Fb) + 1 + 1 + n, Da + Db, ?_⟩
  intro F D A hA
  have h1 : liftLast n A ∈ S.Ω (F + max n (max (Fa + n) Fb)) D (n + n) :=
    mem_mono (liftLast_mem (S := S) n F D hA) _ _ (by omega) le_rfl
  have h2 : liftLast n (normPiece σ) ∈ S.Ω (F + max n (max (Fa + n) Fb)) Da (n + n) :=
    mem_mono (liftLast_mem (S := S) n Fa Da (hPiece S)) _ _ (by omega) le_rfl
  have h3 : normJointGraph σ ∈ S.Ω (F + max n (max (Fa + n) Fb)) Db (n + n) :=
    mem_mono (hGraph S) _ _ (by omega) le_rfl
  have h12 := Work.WilG0.Omega_inter2 (S := S) h1 h2
  have h3' : normJointGraph σ ∈ S.Ω (F + max n (max (Fa + n) Fb) + 1) Db (n + n) :=
    mem_mono h3 _ _ (by omega) le_rfl
  have h123 := Work.WilG0.Omega_inter2 (S := S) h12 h3'
  have hproj := projN_mem (S := S) n _ _ h123
  rw [show projN n (liftLast n A ∩ liftLast n (normPiece σ) ∩ normJointGraph σ)
      = normSet σ A from projN_normJoint_eq σ A] at hproj
  exact mem_mono hproj _ _ (by omega) (by omega)

end Work.WilkiesH.Norm
