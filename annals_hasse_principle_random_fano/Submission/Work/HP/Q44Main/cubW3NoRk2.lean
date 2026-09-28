import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.HP.MDEstimates.vanishRatSpanCub
import Submission.Work.HP.MDEstimates.cubicHyperplaneFactor

namespace Work.HP.Q44Main

set_option autoImplicit false
noncomputable section

open MvPolynomial

/-
GOAL.  Here `latW B = invSub B ∩ ℤ⁵` is the invariance lattice (`Work.Q44Geom.latW`,
`mem_latW_iff`) and `ratSpan L` is the `ℚ`-span of `L`; the tools `ratSpan_finrank_general`,
`sat_span`, `ratSpan_mono`, `ratSpan_latW_le`, `ratSpan_injective_of_isPrimLat`,
`isPrimLat_inf` are all in the complete Submission/Work/Q44Geom/BadDefs.lean and Setup.lean.

Math: let `B` be a nonzero homogeneous cubic in 5 variables with no linear factor, with
`dim (invSub B) = 3`, and let `L ⊆ ℤ⁵` be a primitive rank-3 lattice on whose lattice points
`B` vanishes (equivalently `B` vanishes on `P = ratSpan L`, see
`Work.HP.MDEstimates.vanishRatSpanCub`).  Then `rk (L ⊓ latW B) ≠ 2`.
Proof: put `Q = invSub B`; `B` vanishes on `Q` (it is translation invariant there, so
`B w = B 0 = 0`, see `Work.Q44Geom.mem_invSub_point`) and on `P`.  If `dim (P ⊓ Q) = 2`, then
`H = P ⊔ Q` is a hyperplane of `ℚ⁵` on which `B` vanishes (for `x ∈ P`, `w ∈ Q` we have
`B (x + w) = B x = 0`), so `B` has a linear factor by `Work.HP.Q44Main.cubHyperplaneFactor`
(Submission/Work/HP/Q44Main/cubHyperplaneFactor.lean, the cubic analogue of the proved
`Work.HP.MDEstimates.hyperplaneFactor`), contradicting `hnolin`.  Note that
`dim (P ⊓ Q) ∈ {2,3}`: it is `≥ 2` because `ratSpan (L ⊓ latW B) ≤ P ⊓ Q` and
`rk (L ⊓ latW B) = 2`, while `dim (P ⊓ Q) = 3` would force `P = Q`, hence `L = latW B` (two
saturated lattices with the same `ℚ`-span), i.e. `rk (L ⊓ latW B) = 3`, not `2`.
The file Submission/Work/HP/MDEstimates/cubW3Empty.lean contains the same argument with the
extra successive-minima hypotheses; those successive-minima hypotheses are NOT needed.

The proof below is exactly this argument; the linear-factor input is the proved
`Work.HP.MDEstimates.cubicHyperplaneFactor`.
-/

theorem cubW3NoRk2 (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0)
    (hnolin : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False)
    (h3 : Module.finrank ℚ (Work.Q44Geom.invSub B) = 3)
    (L : Submodule ℤ (Fin 5 → ℤ)) (hprim : Work.HP.IsPrimLat L) (hrk : Work.HP.rk L = 3)
    (hv : ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) :
    Work.HP.rk (L ⊓ Work.Q44Geom.latW B) ≠ 2 := by
  intro hrkN
  set Q : Submodule ℚ (Fin 5 → ℚ) := Work.Q44Geom.invSub B with hQdef
  set P : Submodule ℚ (Fin 5 → ℚ) := Work.Q44Geom.ratSpan L with hPdef
  have hPfin : Module.finrank ℚ P = 3 := by
    rw [hPdef, Work.Q44Geom.ratSpan_finrank_general, hrk]
  have hQfin : Module.finrank ℚ Q = 3 := by
    rw [hQdef]; exact h3
  have hvanP : ∀ x ∈ P, MvPolynomial.eval x B = 0 := by
    rw [hPdef]; exact Work.HP.MDEstimates.vanishRatSpanCub hB hv
  have hNle : Work.Q44Geom.ratSpan (L ⊓ Work.Q44Geom.latW B) ≤ P ⊓ Q := by
    refine le_inf ?_ ?_
    · rw [hPdef]; exact Work.Q44Geom.ratSpan_mono inf_le_left
    · rw [hQdef]
      exact le_trans (Work.Q44Geom.ratSpan_mono inf_le_right) (Work.Q44Geom.ratSpan_latW_le B)
  have hNfin : Module.finrank ℚ (Work.Q44Geom.ratSpan (L ⊓ Work.Q44Geom.latW B)) = 2 := by
    rw [Work.Q44Geom.ratSpan_finrank_general, hrkN]
  have hge : 2 ≤ Module.finrank ℚ ↥(P ⊓ Q) := by
    have h := Submodule.finrank_mono hNle
    rw [hNfin] at h
    exact h
  have hle : Module.finrank ℚ ↥(P ⊓ Q) ≤ 3 := by
    have h := Submodule.finrank_mono (inf_le_right : P ⊓ Q ≤ Q)
    rw [hQfin] at h
    exact h
  have hne : Module.finrank ℚ ↥(P ⊓ Q) ≠ 3 := by
    intro hcon
    have hEq : P ⊓ Q = Q := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hcon, hQfin])
    have hQP : Q ≤ P := hEq ▸ inf_le_left
    have hPQ : Q = P := Submodule.eq_of_le_of_finrank_eq hQP (by rw [hQfin, hPfin])
    have hL : L = Work.Q44Geom.latW B := by
      ext v
      rw [Work.Q44Geom.sat_span L hprim v, ← hPdef, ← hPQ, hQdef]
      exact Iff.symm Work.Q44Geom.mem_latW_iff
    have hLL : L ⊓ L = L := by simp
    have h3rk : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) = 3 := by
      rw [← hL, hLL, hrk]
    omega
  have hinf : Module.finrank ℚ ↥(P ⊓ Q) = 2 := by omega
  have hsup : Module.finrank ℚ ↥(P ⊔ Q) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hinf, hPfin, hQfin] at h
    omega
  have hvanH : ∀ v ∈ P ⊔ Q, MvPolynomial.eval v B = 0 := by
    intro v hv
    obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp hv
    rw [← hpq]
    rw [hQdef] at hqQ
    exact (Work.Q44Geom.mem_invSub_point hqQ p).trans (hvanP p hpP)
  obtain ⟨ℓ, hℓ1, hℓdvd⟩ := Work.HP.MDEstimates.cubicHyperplaneFactor B hB (P ⊔ Q) hsup hvanH
  exact hnolin ℓ hℓ1 hℓdvd

end

end Work.HP.Q44Main
