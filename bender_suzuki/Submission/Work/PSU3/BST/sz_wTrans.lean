/-
# `Work.PSU3.BST.sz_wTrans` — the Weyl transitivity of `Sz(2^(2n+1))`

In a finite group with a split rank-one datum `(H, Q, t)` of characteristic two in which the
involution `t` inverts the two-point stabiliser `D = H ∩ Hᵗ`, the subgroup `H` is transitive on
the involutions of `G` outside `H` (`Work.PSU3.BenderST.transitive_involutions_outside`).

Applying this to the standard datum of the Suzuki group `Sz(2^(2n+1))` — `H = B` the Borel
subgroup, `Q = U` the Suzuki `2`-group, `t = w` the Weyl element — we obtain the statement that
every involution `w' ∉ B` is conjugate by an element of `B` to the Weyl element:

`∃ b ∈ B, b * w' * b⁻¹ = w`.

The two model inputs are `B = U ⋊ T` with `T = B ⊓ Bʷ` the torus (`Work.Models.Abstract.inf_conj_w`)
and the fact that the Weyl element inverts the torus
(`Submission.Sz.szWgM_conj_szTgM`).
-/
import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.Defs
import Submission.Work.PSU3.BenderST.transitive_involutions_outside

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.BST

theorem sz_wTrans (n : ℕ) (hn : 1 ≤ n) :
    ∀ w : LeanEval.GroupTheory.Defs.SzModel n,
      orderOf w = 2 → w ∉ (Submission.Sz.szBenderPair n hn).B →
      ∃ b ∈ (Submission.Sz.szBenderPair n hn).B,
        b * w * b⁻¹ = (Submission.Sz.szBenderPair n hn).w := by
  intro w hw hwB
  set P := Submission.Sz.szBenderPair n hn with hP
  -- The Weyl element is an involution.
  have hww : P.w * P.w = 1 := by
    rw [hP]
    exact Subtype.ext (Submission.Sz.szWg_mul_self n)
  -- The standard datum `(B, U, w)` of the Suzuki group is a split rank-one datum.
  have hsplit : Submission.Blueprint.IsSplitRankOne P.B P.U P.w :=
    Work.PSU3.BenderST.benderPair_isSplitRankOne P hww
  -- The Weyl element inverts the two-point stabiliser `D = B ⊓ Bʷ = T`.
  have hinv : ∀ d ∈ Submission.Blueprint.twoPoint P.B P.w, P.w * d * P.w = d⁻¹ := by
    intro d hd
    have hdT : d ∈ P.T := by
      rwa [show Submission.Blueprint.twoPoint P.B P.w = P.T from
        Work.Models.Abstract.inf_conj_w P] at hd
    rw [hP] at hdT
    obtain ⟨y, hy⟩ :=
      MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hdT)
    have hy' : Submission.Sz.szTgM n y = d := Subtype.ext hy
    rw [← hy', hP]
    have hwinv : (Submission.Sz.szWgM n)⁻¹ = Submission.Sz.szWgM n :=
      inv_eq_of_mul_eq_one_right (Subtype.ext (Submission.Sz.szWg_mul_self n))
    have hinvy : (Submission.Sz.szTgM n y)⁻¹ = Submission.Sz.szTgM n y⁻¹ := by
      apply Subtype.ext
      show (Submission.Sz.szTg n y)⁻¹ = Submission.Sz.szTg n y⁻¹
      rw [show Submission.Sz.szTg n y⁻¹ = (Submission.Sz.szTg n y)⁻¹ from
        map_inv (Submission.Sz.szTgHom n) y]
    calc (Submission.Sz.szBenderPair n hn).w * Submission.Sz.szTgM n y *
            (Submission.Sz.szBenderPair n hn).w
        = Submission.Sz.szWgM n * Submission.Sz.szTgM n y * Submission.Sz.szWgM n := rfl
      _ = Submission.Sz.szWgM n * Submission.Sz.szTgM n y * (Submission.Sz.szWgM n)⁻¹ := by
            rw [hwinv]
      _ = (Submission.Sz.szTgM n y)⁻¹ := by
            rw [hinvy]
            exact Submission.Sz.szWgM_conj_szTgM n y
  obtain ⟨h, hh, hconj⟩ :=
    Work.PSU3.BenderST.transitive_involutions_outside hsplit hinv hw hwB
  exact ⟨h⁻¹, P.B.inv_mem hh, by rw [hconj]; group⟩

end Work.PSU3.BST
