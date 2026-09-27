import Mathlib
import Submission.Work.KT.hkWDefs
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.hk_k0cls
import Submission.Work.KT.Wblk_mul_self
import Submission.Work.KT.cls_conj_involution

open Matrix

namespace Work.KT

noncomputable section

/-!
# `Work.KT.hkW_class` — the class identity of the `W`-construction

Route.  Write `W = Wblk p C`, `D = Dblk p X C`.

* `W` is an involution (`Work.KT.Wblk_mul_self`), so conjugating the idempotent `D` by `W` does not
  change its `K₀`-class: `[W D W] = [D]` (`Work.KT.cls_conj_involution`, witnesses `D * W` and `W`).
* `D` is the block sum `⟨p,X⟩ ⊕ ⟨p,1-C⟩` (`Mat.sum`), so `[D] = [X] + [1-C]` (`cls_sum`).
* `⟨p,C⟩ ⊕ ⟨p,1-C⟩` is Murray–von Neumann equivalent to `1_p` (`Work.KT.mvN_sum_compl_mat`), and
  `diagMat R p (p+p)` is Murray–von Neumann equivalent to `1_p` (`Work.KT.hk_diagMat_mvN_one`);
  hence `[C] + [1-C] = [diag(1_p,0)]` (`cls_add_compl_diagMat`).
* Substituting `[C] = [Y]` gives the claim.
-/

/-- `diag(1_p, 0)`, of size `p+p`, has the class of the identity of size `p`. -/
lemma cls_matOne_eq_diagMat {R : Type} [Ring R] (p : ℕ) :
    cls (Mat.one R p) = cls (diagMat R p (p + p)) :=
  cls_eq_of_mvN (Mat.one_isIdem (R := R) p) (diagMat_isIdem R p (p + p))
    (Mat.mvN_symm (hk_diagMat_mvN_one R p (p + p) (Nat.le_add_right p p)))

/-- For an idempotent `C`: `[C] + [1 - C] = [diag(1_p, 0)]` (both sides of size `p + p`). -/
lemma cls_add_compl_diagMat {R : Type} [Ring R] {p : ℕ} {C : Matrix (Fin p) (Fin p) R}
    (hC : C * C = C) :
    cls (⟨p, C⟩ : Mat R) + cls (⟨p, 1 - C⟩ : Mat R) = cls (diagMat R p (p + p)) := by
  have hCc : Mat.IsIdem (⟨p, C⟩ : Mat R) := hC
  have h1 : cls (⟨p, C⟩ : Mat R) + cls (⟨p, 1 - C⟩ : Mat R)
      = cls (Mat.sum (⟨p, C⟩ : Mat R) (⟨p, 1 - C⟩ : Mat R)) :=
    (cls_sum hCc (Mat.isIdem_one_sub hCc)).symm
  rw [h1]
  rw [← cls_matOne_eq_diagMat (R := R) p]
  exact cls_eq_of_mvN (Mat.sum_idem hCc (Mat.isIdem_one_sub hCc))
    (Mat.one_isIdem (R := R) p) (mvN_sum_compl_mat R p C hC)

/-- **The `W`-construction class identity.**  For matrices `X`, `C` of size `p` and a matrix `Y`
of size `p` with `[C] = [Y]` in `K₀`, the conjugate `Wblk p C * Dblk p X C * Wblk p C` of the block
diagonal matrix `Dblk p X C` by the involution `Wblk p C` has class `[X] - [Y] + [diag(1_p,0)]`,
where `diag(1_p,0)` is the diagonal matrix `diagMat R p (p+p)` of size `p+p`. -/
theorem hkW_class {R : Type} [Ring R] (hcomm : ∀ x y : R, x * y = y * x) {p : ℕ}
    (X Y C : Matrix (Fin p) (Fin p) R) (hX : X * X = X) (hC : C * C = C)
    (hCY : cls (⟨p, C⟩ : Mat R) = cls (⟨p, Y⟩ : Mat R)) :
    cls (⟨p + p, Wblk p C * Dblk p X C * Wblk p C⟩ : Mat R)
      = cls (⟨p, X⟩ : Mat R) - cls (⟨p, Y⟩ : Mat R) + cls (diagMat R p (p + p)) := by
  have hCc : Mat.IsIdem (⟨p, C⟩ : Mat R) := hC
  have hXc : Mat.IsIdem (⟨p, X⟩ : Mat R) := hX
  -- `Wblk p C` is an involution, `Dblk p X C` is idempotent, so the class is unchanged
  have hWW : Wblk p C * Wblk p C = 1 := Wblk_mul_self hC
  have hDD : Dblk p X C * Dblk p X C = Dblk p X C :=
    Mat.sum_idem hXc (Mat.isIdem_one_sub hCc)
  have hconj : cls (⟨p + p, Wblk p C * Dblk p X C * Wblk p C⟩ : Mat R)
      = cls (⟨p + p, Dblk p X C⟩ : Mat R) :=
    cls_conj_involution hWW hDD
  -- `Dblk p X C = ⟨p,X⟩ ⊕ ⟨p,1-C⟩`
  have hsum : cls (⟨p + p, Dblk p X C⟩ : Mat R)
      = cls (⟨p, X⟩ : Mat R) + cls (⟨p, 1 - C⟩ : Mat R) := by
    have hD : (⟨p + p, Dblk p X C⟩ : Mat R)
        = Mat.sum (⟨p, X⟩ : Mat R) (⟨p, 1 - C⟩ : Mat R) := rfl
    rw [hD]
    exact cls_sum hXc (Mat.isIdem_one_sub hCc)
  -- `[1 - C] = [diag(1_p,0)] - [C]`
  have hcompl : cls (⟨p, 1 - C⟩ : Mat R) = cls (diagMat R p (p + p)) - cls (⟨p, C⟩ : Mat R) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact cls_add_compl_diagMat hC
  rw [hconj, hsum, hcompl, ← hCY]
  abel

end

end Work.KT
