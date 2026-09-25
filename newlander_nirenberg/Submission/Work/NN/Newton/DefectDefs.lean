import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

/-!
# Shared definitions for the quadratic flat `∂̄`-defect of the coordinate datum

This module collects the objects used by the proof of
`Work.NN.Newton.coordDatum_defect_quadratic`:

* `lamC l` — the `l`-th coordinate functional `w ↦ w l` on `ℂⁿ`;
* `evec j`, `ievec j` — the vectors `e_j` and `i·e_j`;
* `LDv A z X Y = (DA_z X)(Y)`, `LD A z l X Y = λ((DA_z X)(Y))` — the entries of the
  first derivative of `A` at `z`;
* `coordDatum A l` — the coordinate datum `F^{(l)}_m = Lcoef A (·l) m`;
* `TA A z l j k` — the "quadratic" remainder `Q` of the integrability identity
  `0 = proj02 J (dOne (∂̄_J z_l)) z e_j e_k`, expressed through `LD`, `LDv`;
* `defectExpr A z l j k` — the corresponding defect expression of the flat `∂̄`-defect.

The identity proved downstream is
`ddbar Jstd (coordDatum A l) j k z = -(I/8) * TA A z l j k`.
-/

namespace Work.NN.Newton

open scoped ContDiff
open Set

noncomputable section

variable {n : ℕ}

/-- The `l`-th coordinate functional on `ℂⁿ`. -/
def lamC (l : Fin n) : Work.NN.Core.Cn n →L[ℝ] ℂ := ContinuousLinearMap.proj l

@[simp] lemma lamC_apply (l : Fin n) (w : Work.NN.Core.Cn n) : lamC l w = w l := rfl

lemma fderiv_lamC (l : Fin n) (z : Work.NN.Core.Cn n) :
    fderiv ℝ (fun y : Work.NN.Core.Cn n => y l) z = lamC l := by
  have h : (fun y : Work.NN.Core.Cn n => y l) = ⇑(lamC l) := rfl
  rw [h]
  exact (lamC l).hasFDerivAt.fderiv

/-- The unit vector `e_j ∈ ℂⁿ`. -/
def evec (j : Fin n) : Work.NN.Core.Cn n := Pi.single j (1 : ℂ)

/-- The vector `i·e_j ∈ ℂⁿ`. -/
def ievec (j : Fin n) : Work.NN.Core.Cn n := Pi.single j (Complex.I : ℂ)

lemma ievec_eq_smul (j : Fin n) : ievec j = Complex.I • evec j := by
  rw [ievec, evec, Work.NN.Core.smul_single_I]

/-- `(DA_z X)(Y)`, the first derivative of `A` at `z` in direction `X` applied to `Y`. -/
def LDv (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (X Y : Work.NN.Core.Cn n) : Work.NN.Core.Cn n :=
  (fderiv ℝ A z X) Y

/-- `λ((DA_z X)(Y))`, the `l`-th coordinate of `(DA_z X)(Y)`. -/
def LD (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y : Work.NN.Core.Cn n) : ℂ :=
  lamC l (LDv A z X Y)

/-- The coordinate datum of `z_l`: `F^{(l)}_m = Lcoef A (·l) m = (i/2)(A z e_m)_l`. -/
def coordDatum (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n) :
    Fin n → Work.NN.Core.Cn n → ℂ :=
  fun m z => Work.NN.Core.Lcoef A (fun y => y l) m z

@[simp] lemma coordDatum_apply (A) (l : Fin n) (m : Fin n) (z : Work.NN.Core.Cn n) :
    coordDatum A l m z = Work.NN.Core.Lcoef A (fun y => y l) m z := rfl

lemma coordDatum_eq (A) (l : Fin n) (m : Fin n) (z : Work.NN.Core.Cn n) :
    coordDatum A l m z = (Complex.I / 2) * lamC l (A z (evec m)) := by
  simp only [coordDatum, Work.NN.Core.Lcoef, evec, lamC, fderiv_lamC]

/-- **The quadratic remainder of the integrability identity.**

`TA A z l j k` is the sum of the ten terms of `E = 2·X + TA` (in the notation of the proof of
`coordDatum_defect_quadratic`) that contain at least one factor `A`; each is a product of an entry
of `A` with an entry of `DA`, hence of size `a²` in the `C^{1,α}`-small regime. -/
def TA (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  Complex.I * LD A z l (A z (evec j)) (evec k)
  + Complex.I * lamC l (A z (LDv A z (evec k) (evec j)))
  - Complex.I * lamC l (A z (LDv A z (evec j) (evec k)))
  - Complex.I * LD A z l (A z (evec k)) (evec j)
  + lamC l (A z (LDv A z (ievec j) (evec k)))
  - LD A z l (A z (evec j)) (ievec k)
  - LD A z l (A z (evec j)) (A z (evec k))
  - lamC l (A z (LDv A z (ievec k) (evec j)))
  + LD A z l (A z (evec k)) (ievec j)
  + LD A z l (A z (evec k)) (A z (evec j))

/-- The "linear" defect expression `X = λ(DA[e_j]e_k) - λ(DA[e_k]e_j)
+ i λ(DA[ie_j]e_k) - i λ(DA[ie_k]e_j)`: four times the flat `∂̄`-defect of the coordinate
datum divided by `i`. -/
def defectExpr (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  LD A z l (evec j) (evec k) - LD A z l (evec k) (evec j)
  + Complex.I * LD A z l (ievec j) (evec k) - Complex.I * LD A z l (ievec k) (evec j)

/-- The expression `E` of the integrability identity: `proj02 J (dOne (∂̄_J z_l)) z e_j e_k`
equals `(I/8)·E`. -/
def Eexpr (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  LD A z l (evec j) (evec k) - LD A z l (evec k) (evec j)
  + Complex.I * LD A z l ((Work.NN.Core.JstdCn n + A) z (evec j)) (evec k)
  - Complex.I * LD A z l (evec k) ((Work.NN.Core.JstdCn n + A) z (evec j))
  + Complex.I * LD A z l (evec j) ((Work.NN.Core.JstdCn n + A) z (evec k))
  - Complex.I * LD A z l ((Work.NN.Core.JstdCn n + A) z (evec k)) (evec j)
  - LD A z l ((Work.NN.Core.JstdCn n + A) z (evec j)) ((Work.NN.Core.JstdCn n + A) z (evec k))
  + LD A z l ((Work.NN.Core.JstdCn n + A) z (evec k)) ((Work.NN.Core.JstdCn n + A) z (evec j))

/-- The hypothesis on `A`: the `C^{1,α}`-norm on `P_r` of every coefficient `z ↦ A z w j`
(`‖w‖ ≤ 1`) is at most `a`. -/
def CVBound (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (α a : ℝ) (P : Set (Work.NN.Core.Cn n)) : Prop :=
  ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
    Work.CR.Flat.holderNorm 1 α (fun z => A z w j) P ≤ ENNReal.ofReal a

/-- The polydisc of multi-radius `r`. -/
def polydiscR (n : ℕ) (r : ℝ) : Set (Work.NN.Core.Cn n) :=
  Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)

lemma isOpen_polydiscR (n : ℕ) (r : ℝ) : IsOpen (polydiscR n r) :=
  Work.CR.Flat.isOpen_polydisc 0 _

end

end Work.NN.Newton
