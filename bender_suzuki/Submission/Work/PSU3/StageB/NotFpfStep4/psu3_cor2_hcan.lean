/-
# `psu3_cor2_hcan`: Peterfalvi's Cor. (Ch. VII §1) for the model `PSU(3,2ⁿ)`

Peterfalvi II, Ch. VII §1 (Cor. 2), in the model: given `ζ ∈ Eˣ` with `ζ·σζ = 1` (so `ζ` is
an element of order dividing `q+1` outside `F`), there is `p = (x,y) ∈ Q = SZ(E)` with
`p.x ≠ 0`, `p.y = ζ⁻¹`, `f(p) = ζ·p⁻¹` **and** whose `D`-coordinate `h(p) ∈ D = B ⊓ Bʷ` (the
canonical `h` of Peterfalvi's `t x t = g(x) h(x) t f(x)`) is exactly the torus element
`suTg ζ⁻¹ ∈ T̄ ≤ PSU(3,2ⁿ)`.

The last conjunct is the content of `hcan`: the element `h(Ā(p))` of `twoPoint B̄ w̄` is the
image of `suTg ζ⁻¹` under `psu3Hom`.  It is proved by exhibiting the canonical decomposition
of `w̄ · Ā(p) · w̄` explicitly: the Weyl relation `psu3_weylConj_pglHom` writes it with
`weylFactorM = suTg(σp.y)⁻¹ · u(σp.y·p.x/p.y, σp.y)`, the torus normalises the unipotent
radical, so this is `(unipotent)·(torus)` in the Borel, and `σp.y = ζ` for our `p`, so the
torus part is `suTg ζ⁻¹` — and `twoPoint B̄ w̄ = T̄` (`twoPoint_psu3B_psu3Weyl`) identifies
which elements of the Borel are eligible as the `D`-coordinate.  The decomposition is
computed in `weylFactorM_decomp`; `canon_unique''` then identifies its `D`-part with `hcan`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.Model.psu3_cor2
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.NotFpfStep4.weylFactorM_decomp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs

theorem psu3_cor2_hcan {n : ℕ} (hn : 2 ≤ n) (ζ : (Work.PSU3.E n)ˣ) (hζ1 : ζ ≠ 1)
    (hζ : (ζ : Work.PSU3.E n) * Work.PSU3.σE (ζ : Work.PSU3.E n) = 1) :
    ∃ p : Work.PSU3.SZ (Work.PSU3.E n), p.x ≠ 0 ∧ p.y = (ζ : Work.PSU3.E n)⁻¹ ∧
      Work.PSU3.fMapTot p = Work.PSU3.SZ.torusAct ζ p⁻¹ ∧
      ((Work.PSU3.StageB.hcan (Work.PSU3.Model.psu3_isSplitRankOne n hn)
          (Work.PSU3.Model.psu3UEquiv n hn p) :
          ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
            (Submission.PSU3.psu3Weyl n))) : LeanEval.GroupTheory.Defs.PSU3Model n)
        = Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suTg n ζ⁻¹,
            Submission.PSU3.suTg_isSU3 n ζ⁻¹⟩ := by
  -- The model element `p` of `psu3_cor2`: `p.y = ζ⁻¹`, `p.x ≠ 0`, `f(p) = ζ·p⁻¹`.
  obtain ⟨p, hxne, hpy, hf⟩ := Work.PSU3.Model.psu3_cor2 n ζ hζ1 hζ
  -- `p ≠ 1`, and `σ(p.y) = ζ`.
  have hp : p ≠ 1 := by
    intro h
    exact inv_ne_zero (Units.ne_zero ζ) (by rw [← hpy, h, Work.PSU3.SZ.one_y])
  have hσζ : Work.PSU3.σE (ζ : Work.PSU3.E n) = (ζ : Work.PSU3.E n)⁻¹ :=
    eq_inv_of_mul_eq_one_right hζ
  have hσy : Work.PSU3.σE p.y = (ζ : Work.PSU3.E n) := by
    rw [hpy, Work.PSU3.σE_inv, hσζ, inv_inv]
  -- The canonical decomposition of `w̄·Ā(p)·w̄`: unipotent part `g`, `D`-part `hh = suTg ζ⁻¹`.
  obtain ⟨g, hh, hhh, hdec⟩ := weylFactorM_decomp ζ p hp hσy
  -- `Ā(p) ≠ 1`, so its canonical data is the non-junk one.
  have hxne1 : ((Work.PSU3.Model.psu3UEquiv n hn p :
      ↥(Submission.PSU3.psu3U n)) : PSU3Model n) ≠ 1 := by
    intro h
    have h2 : Work.PSU3.Model.psu3UEquiv n hn p = 1 := by
      apply Subtype.ext
      simpa using h
    have h3 : Work.PSU3.Model.psu3UEquiv n hn p =
        Work.PSU3.Model.psu3UEquiv n hn 1 := by
      rw [map_one]; exact h2
    exact hp ((Work.PSU3.Model.psu3UEquiv n hn).injective h3)
  -- The Weyl relation, rewritten as the canonical form `g · hh · w̄ · f(p)`.
  have heq : Submission.PSU3.psu3Weyl n *
        ((Work.PSU3.Model.psu3UEquiv n hn p :
            ↥(Submission.PSU3.psu3U n)) : PSU3Model n) *
        Submission.PSU3.psu3Weyl n =
      (g : PSU3Model n) * (hh : PSU3Model n) * Submission.PSU3.psu3Weyl n *
        ((Work.PSU3.Model.psu3UEquiv n hn (Work.PSU3.SZ.fMap p hp) :
            ↥(Submission.PSU3.psu3U n)) : PSU3Model n) := by
    rw [Work.PSU3.Model.psu3UEquiv_apply, Work.PSU3.Model.psu3UEquiv_apply, ← hdec]
    exact Work.PSU3.Model.psu3_weylConj_pglHom n p hp
  -- Uniqueness of the canonical data identifies the `D`-part with `hcan`.
  obtain ⟨-, hcan_eq, -⟩ := Work.PSU3.StageB.canon_unique'' (H := Submission.PSU3.psu3B n)
    (Q := Submission.PSU3.psu3U n) (t := Submission.PSU3.psu3Weyl n)
    (Work.PSU3.Model.psu3_isSplitRankOne n hn) hxne1 heq
  refine ⟨p, hxne, hpy, hf, ?_⟩
  show ((Work.PSU3.StageB.hcan (H := Submission.PSU3.psu3B n)
      (Q := Submission.PSU3.psu3U n) (t := Submission.PSU3.psu3Weyl n)
      (Work.PSU3.Model.psu3_isSplitRankOne n hn)
      (Work.PSU3.Model.psu3UEquiv n hn p)) : PSU3Model n)
      = Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suTg n ζ⁻¹,
            Submission.PSU3.suTg_isSU3 n ζ⁻¹⟩
  rw [← hcan_eq]
  exact hhh

end Work.PSU3.StageB.NotFpfStep4
