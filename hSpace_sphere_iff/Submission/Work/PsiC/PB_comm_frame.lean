import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.PB_comm_frame`

`PB p` is the six-fold tensor power `p^{⊗6}` of the idempotent matrix `p.2`, written in the
bracketing `((1,2),(3,4)),(5,6)` of the index type `IB n = (I2 n × I2 n) × I2 n`,
`I2 n = Fin n × Fin n`.

Every entry of `PB p` is an ordered product of six entries of `p.2`.  Over a *commutative*
ring `A` (hypothesis `hA`) the value of such a product is invariant under permeating the six
tensor coordinates; consequently `PB p` commutes with the permutation matrices of all the
coordinate permutations which preserve the pairing `{{1,2},{3,4},{5,6}}`:

* the individual pair swaps `sg0`, `sg1`, `sg2`, and their product `sB`;
* the cycle `cB` of the three pairs;
* the permutation `invB` exchanging the first and third pairs;
* hence also with `Edel d0 d1 d2 = h_{d0}(σ₀) h_{d1}(σ₁) h_{d2}(σ₂)`, the joint spectral
  projector of the three pair swaps.

The proof is pointwise: `PB p * σ.permMatrix A = σ.permMatrix A * PB p` is equivalent to
`PB p (σ a) (σ b) = PB p a b` for all `a b`, and the latter is a rearrangement of a product
of six commuting entries closed by `ring`.
-/

namespace Work.PsiC

open Matrix

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Frame

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The entries of `PB p` are products of the six entries of `p.2` in tensor order. -/
theorem PB_apply (p : Work.KT.Mat A) (a b : Work.KT.PsiC.IB p.1) :
    Work.KT.PsiC.PB p a b =
      ((p.2 a.1.1.1 b.1.1.1 * p.2 a.1.1.2 b.1.1.2) *
        (p.2 a.1.2.1 b.1.2.1 * p.2 a.1.2.2 b.1.2.2)) *
      (p.2 a.2.1 b.2.1 * p.2 a.2.2 b.2.2) := rfl

theorem sg0_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.sg0 n (((a, b), (c, d)), (e, f)) = (((b, a), (c, d)), (e, f)) := rfl

theorem sg1_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.sg1 n (((a, b), (c, d)), (e, f)) = (((a, b), (d, c)), (e, f)) := rfl

theorem sg2_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.sg2 n (((a, b), (c, d)), (e, f)) = (((a, b), (c, d)), (f, e)) := rfl

theorem invB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.invB n (((a, b), (c, d)), (e, f)) = (((e, f), (c, d)), (a, b)) := rfl

/-- If `PB p` is invariant under the coordinate permutation `σ`, then it commutes with the
permutation matrix of `σ`. -/
theorem PB_comm_of_reindex (p : Work.KT.Mat A) (σ : Equiv.Perm (Work.KT.PsiC.IB p.1))
    (h : ∀ a b, Work.KT.PsiC.PB p (σ a) (σ b) = Work.KT.PsiC.PB p a b) :
    Work.KT.PsiC.PB p * σ.permMatrix A = σ.permMatrix A * Work.KT.PsiC.PB p := by
  ext a b
  rw [Work.KT.PsiC.mul_permMatrix, Work.KT.PsiC.permMatrix_mul]
  simpa using (h a (σ.symm b)).symm

theorem PB_comm_sg0 (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.sg0 p.1).permMatrix A =
      (Work.KT.PsiC.sg0 p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.sg0 p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, sg0_apply]
  ring

theorem PB_comm_sg1 (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.sg1 p.1).permMatrix A =
      (Work.KT.PsiC.sg1 p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.sg1 p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, sg1_apply]
  ring

theorem PB_comm_sg2 (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.sg2 p.1).permMatrix A =
      (Work.KT.PsiC.sg2 p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.sg2 p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, sg2_apply]
  ring

theorem PB_comm_sB (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.sB p.1).permMatrix A =
      (Work.KT.PsiC.sB p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.sB p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, Work.KT.PsiC.sB_apply]
  ring

theorem PB_comm_cB (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.cB p.1).permMatrix A =
      (Work.KT.PsiC.cB p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.cB p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, Work.KT.PsiC.cB_apply]
  ring

theorem PB_comm_invB (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.invB p.1).permMatrix A =
      (Work.KT.PsiC.invB p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.invB p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, invB_apply]
  ring

/-- Commutation is multiplicative. -/
theorem comm_mul_of_comm {ι : Type} [Fintype ι] [DecidableEq ι]
    (Z X Y : Matrix ι ι A) (hX : Z * X = X * Z) (hY : Z * Y = Y * Z) :
    Z * (X * Y) = (X * Y) * Z := by
  rw [← mul_assoc, hX, mul_assoc, hY, ← mul_assoc]

theorem PB_comm_Edel (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A)
    (d0 d1 d2 : ℂ) :
    Work.KT.PsiC.PB p * Work.KT.PsiC.Edel d0 d1 d2 p.1 =
      Work.KT.PsiC.Edel d0 d1 d2 p.1 * Work.KT.PsiC.PB p := by
  have h0 := Work.KT.PsiC.halfProj_comm_of (A := A) hA (Work.KT.PsiC.sg0 p.1) d0
    (Work.KT.PsiC.PB p) (PB_comm_sg0 hA p)
  have h1 := Work.KT.PsiC.halfProj_comm_of (A := A) hA (Work.KT.PsiC.sg1 p.1) d1
    (Work.KT.PsiC.PB p) (PB_comm_sg1 hA p)
  have h2 := Work.KT.PsiC.halfProj_comm_of (A := A) hA (Work.KT.PsiC.sg2 p.1) d2
    (Work.KT.PsiC.PB p) (PB_comm_sg2 hA p)
  simp only [Work.KT.PsiC.Edel]
  have h01 := comm_mul_of_comm (Work.KT.PsiC.PB p)
    (Work.KT.PsiC.halfProj d0 (Work.KT.PsiC.sg0 p.1))
    (Work.KT.PsiC.halfProj d1 (Work.KT.PsiC.sg1 p.1)) h0 h1
  exact comm_mul_of_comm (Work.KT.PsiC.PB p) _ _ h01 h2

end Frame

theorem PB_comm_frame (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) :
    (Work.KT.PsiC.PB p * (Work.KT.PsiC.sB p.1).permMatrix A = (Work.KT.PsiC.sB p.1).permMatrix A * Work.KT.PsiC.PB p) ∧
    (Work.KT.PsiC.PB p * (Work.KT.PsiC.cB p.1).permMatrix A = (Work.KT.PsiC.cB p.1).permMatrix A * Work.KT.PsiC.PB p) ∧
    (Work.KT.PsiC.PB p * (Work.KT.PsiC.invB p.1).permMatrix A = (Work.KT.PsiC.invB p.1).permMatrix A * Work.KT.PsiC.PB p) ∧
    (∀ d0 d1 d2 : ℂ, Work.KT.PsiC.PB p * Work.KT.PsiC.Edel d0 d1 d2 p.1 = Work.KT.PsiC.Edel d0 d1 d2 p.1 * Work.KT.PsiC.PB p) := by
  exact ⟨PB_comm_sB hA p, PB_comm_cB hA p, PB_comm_invB hA p,
    fun d0 d1 d2 => PB_comm_Edel hA p d0 d1 d2⟩

end Work.PsiC
