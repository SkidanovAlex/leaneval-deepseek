import Mathlib
import Submission.Work.PTCert.Interfaces

/-!
# `Xtr`: the Nielsen transvections indexed by `(i, j, kind)`

A common vocabulary for the letter theory of the certificate pipeline.  The eight Nielsen
transvections attached to an *ordered* pair `(i,j)` of distinct generators are

  `kind = 0`: `ρᵢⱼ` (`aᵢ ↦ aᵢ aⱼ`),   `kind = 1`: `ρᵢⱼ⁻¹` (`aᵢ ↦ aᵢ aⱼ⁻¹`),
  `kind = 2`: `λᵢⱼ` (`aᵢ ↦ aⱼ aᵢ`),   `kind = 3`: `λᵢⱼ⁻¹` (`aᵢ ↦ aⱼ⁻¹ aᵢ`).

The letter `b1 r k` of `Interfaces.lean`, for `1 ≤ k < NB1 r`, is `Xtr i j hij ((k-1) % 4)`
where `(i,j) = pairOf r ((k-1)/4)` decoded to `Fin r`.
-/

set_option autoImplicit false

namespace Submission.PTCert

open Submission.FreeGroupAut

/-- The Nielsen transvection of code `kind ∈ {0,1,2,3}` on the ordered pair `(i,j)`. -/
noncomputable def Xtr {r : ℕ} (i j : Fin r) (hij : i ≠ j) (kind : ℕ) :
    MulAut (FreeGroup (Fin r)) :=
  if kind = 0 then rho i j hij else if kind = 1 then rhoNeg i j hij
    else if kind = 2 then lam i j hij else lamNeg i j hij

@[simp] theorem Xtr_zero {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Xtr i j hij 0 = rho i j hij := rfl

@[simp] theorem Xtr_one {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Xtr i j hij 1 = rhoNeg i j hij := rfl

@[simp] theorem Xtr_two {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Xtr i j hij 2 = lam i j hij := rfl

@[simp] theorem Xtr_three {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Xtr i j hij 3 = lamNeg i j hij := rfl

/-- The letter `k` decoded: `Xtr` of the pair `pairOf r ((k-1)/4)` and the kind `(k-1)%4`.
For `1 ≤ k < NB1 r` this is `b1 r k`; the definition is total and is `1` when the decoded
pair is out of range. -/
noncomputable def ltr (r k : ℕ) : MulAut (FreeGroup (Fin r)) :=
  if h : (pairOf r ((k - 1) / 4)).1 < r ∧ (pairOf r ((k - 1) / 4)).2 < r ∧
      (pairOf r ((k - 1) / 4)).1 ≠ (pairOf r ((k - 1) / 4)).2 then
    Xtr ⟨(pairOf r ((k - 1) / 4)).1, h.1⟩ ⟨(pairOf r ((k - 1) / 4)).2, h.2.1⟩
      (fun e => h.2.2 (congrArg Fin.val e)) ((k - 1) % 4)
  else 1

/-- The two vertices of an edge, as the pair of natural numbers used by `cEdge`/`edgeL`. -/
def edgePair {r : ℕ} (p : Submission.RouteB.Edge r) : ℕ × ℕ := (p.1.1.val, p.1.2.val)

@[simp] theorem edgePair_val {r : ℕ} (p : Submission.RouteB.Edge r) :
    (edgePair p).1 = p.1.1.val ∧ (edgePair p).2 = p.1.2.val := ⟨rfl, rfl⟩

end Submission.PTCert
