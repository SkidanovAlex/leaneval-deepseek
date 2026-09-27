import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.kronAux

/-!
# `Work.KT.PsiC.Setup` — the two tensor frames for `ψ²ψ³ = ψ³ψ²`

Both `ψ²ψ³[p]` and `ψ³ψ²[p]` are computed on the six-fold tensor power `p^{⊗6}`, but in two
different bracketings:

* **frame A** = `(E^{⊗3})^{⊗2}`, index type `IA n = I3 n × I3 n`, `I3 n = (Fin n × Fin n) × Fin n`;
* **frame B** = `(E^{⊗2})^{⊗3}`, index type `IB n = (I2 n × I2 n) × I2 n`, `I2 n = Fin n × Fin n`.

The bridge between them is the "transpose" equivalence `Phi : IA n ≃ IB n`,
`(((i,j),k),((i',j'),k')) ↦ (((i,i'),(j,j')),(k,k'))`, which conjugates the frame-A pair
`(block swap, cyclic`) into the frame-B pair `(product of the three pair swaps, pair cycle)`.
-/

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The unreindexed double tensor power index type. -/
abbrev I2 (n : ℕ) : Type := Fin n × Fin n

/-- The unreindexed triple tensor power index type. -/
abbrev I3 (n : ℕ) : Type := (Fin n × Fin n) × Fin n

/-- Frame A index type `(E^{⊗3})^{⊗2}`. -/
abbrev IA (n : ℕ) : Type := I3 n × I3 n

/-- Frame B index type `(E^{⊗2})^{⊗3}`. -/
abbrev IB (n : ℕ) : Type := (I2 n × I2 n) × I2 n

/-! ## Projectors -/

/-- The `λ`-spectral projector `(1 + λ⁻¹σ + λ⁻²σ²)/3` of a permutation matrix. -/
def cycProj {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (lam : ℂ) :
    Matrix ι ι A :=
  algebraMap ℂ A ((1:ℂ)/3) •
    (1 + algebraMap ℂ A lam⁻¹ • σ.permMatrix A +
      algebraMap ℂ A (lam⁻¹ ^ 2) • (σ.permMatrix A * σ.permMatrix A))

/-- The projector `(1 + εσ)/2` of an involutive permutation matrix. -/
def halfProj {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℂ) (σ : Equiv.Perm ι) :
    Matrix ι ι A :=
  algebraMap ℂ A ((1:ℂ)/2) • (1 + algebraMap ℂ A ε • σ.permMatrix A)

/-! ## The two frames -/

/-- Frame A: `p^{⊗6}` in the bracketing `(E^{⊗3})^{⊗2}`. -/
def PA (p : Mat A) : Matrix (IA p.1) (IA p.1) A :=
  kroneckerMap (· * ·)
    (kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2)
    (kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2)

/-- Frame B: `p^{⊗6}` in the bracketing `(E^{⊗2})^{⊗3}`. -/
def PB (p : Mat A) : Matrix (IB p.1) (IB p.1) A :=
  kroneckerMap (· * ·)
    (kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) (kroneckerMap (· * ·) p.2 p.2))
    (kroneckerMap (· * ·) p.2 p.2)

/-- The block swap `s` of frame A. -/
def sA (n : ℕ) : Equiv.Perm (IA n) := Equiv.prodComm (I3 n) (I3 n)

/-- The cyclic permutation `c₁` on the first block of frame A. -/
def c1A (n : ℕ) : Equiv.Perm (IA n) :=
  Equiv.prodCongr (cycPermP n) (Equiv.refl (I3 n))

/-- The cyclic permutation `c₂` on the second block of frame A. -/
def c2A (n : ℕ) : Equiv.Perm (IA n) :=
  Equiv.prodCongr (Equiv.refl (I3 n)) (cycPermP n)

/-- The element `t = c₁c₂` of frame A. -/
def tA (n : ℕ) : Equiv.Perm (IA n) :=
  Equiv.prodCongr (cycPermP n) (cycPermP n)

/-- Flip of the first two tensor factors of `I3 n`, `(i,j,k) ↦ (j,i,k)`. -/
def flipI3 (n : ℕ) : Equiv.Perm (I3 n) where
  toFun x := ((x.1.2, x.1.1), x.2)
  invFun x := ((x.1.2, x.1.1), x.2)
  left_inv x := by rcases x with ⟨⟨i,j⟩,k⟩; rfl
  right_inv x := by rcases x with ⟨⟨i,j⟩,k⟩; rfl

/-- The reflection `R` of frame A: flip the first two factors in both blocks. -/
def RA (n : ℕ) : Equiv.Perm (IA n) :=
  Equiv.prodCongr (flipI3 n) (flipI3 n)

/-- The swap of the first pair in frame B. -/
def sg0 (n : ℕ) : Equiv.Perm (IB n) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.prodComm (Fin n) (Fin n)) (Equiv.refl (I2 n)))
    (Equiv.refl (I2 n))

/-- The swap of the second pair in frame B. -/
def sg1 (n : ℕ) : Equiv.Perm (IB n) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (I2 n)) (Equiv.prodComm (Fin n) (Fin n)))
    (Equiv.refl (I2 n))

/-- The swap of the third pair in frame B. -/
def sg2 (n : ℕ) : Equiv.Perm (IB n) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (I2 n)) (Equiv.refl (I2 n)))
    (Equiv.prodComm (Fin n) (Fin n))

/-- The product of the three pair swaps of frame B. -/
def sB (n : ℕ) : Equiv.Perm (IB n) := sg0 n * sg1 n * sg2 n

/-- The reindexing of frame B onto the standard unreindexed triple tensor power. -/
def cBIdx (n : ℕ) : IB n ≃ (Fin (n * n) × Fin (n * n)) × Fin (n * n) :=
  Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv finProdFinEquiv) finProdFinEquiv

/-- The cyclic permutation of the three pairs in frame B (the reindexed `cycPermP (n*n)`). -/
def cB (n : ℕ) : Equiv.Perm (IB n) :=
  (cBIdx n).trans ((cycPermP (n * n)).trans (cBIdx n).symm)

/-- The transpose equivalence `IA n ≃ IB n` bridging the two frames. -/
def Phi (n : ℕ) : IA n ≃ IB n where
  toFun x := (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2))
  invFun y := (((y.1.1.1, y.1.2.1), y.2.1), ((y.1.1.2, y.1.2.2), y.2.2))
  left_inv x := by rcases x with ⟨⟨⟨i,j⟩,k⟩,⟨i',j'⟩,k'⟩; rfl
  right_inv y := by rcases y with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨e,f⟩⟩; rfl

@[simp] theorem Phi_apply (n : ℕ) (x : IA n) :
    Phi n x = (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2)) := rfl

@[simp] theorem Phi_symm_apply (n : ℕ) (y : IB n) :
    (Phi n).symm y = (((y.1.1.1, y.1.2.1), y.2.1), ((y.1.1.2, y.1.2.2), y.2.2)) := rfl

/-! ## The classes `X(ε,r)` (frame A) and `Y(ε,r)` (frame B) -/

/-- `X(ε,r) = [P₆ · T_r · (1+εs)/2]` in frame A. -/
def XA (p : Mat A) (ε : ℂ) (r : ℕ) : K0 A :=
  clsM (IA p.1) (PA (A := A) p * cycProj (tA p.1) (omega ^ r) * halfProj ε (sA p.1))

/-- `Y(ε,r) = [P₆' · (1+εs')/2 · E'_r]` in frame B. -/
def YB (p : Mat A) (ε : ℂ) (r : ℕ) : K0 A :=
  clsM (IB p.1) (PB (A := A) p * halfProj ε (sB p.1) * cycProj (cB p.1) (omega ^ r))

end

end Work.KT.PsiC
