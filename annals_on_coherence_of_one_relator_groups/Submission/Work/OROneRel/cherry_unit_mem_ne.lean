/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The non-degenerate cherry is a *trivial* unit

The vocabulary (`Work.OROneRel.tlWinCherryDefs`) attaches the "cherry" element
`cherryConn p q m pα pβ s · [x,y] · cherryConn p q m pα pβ (s + lsig [x,y])⁻¹` to a pair of letters
`x y` whose first letter `x` is one of the two new letters `a = (0,true)`, `b⁻¹ = (1,false)` of the
window `[0,m+1]` read at an *outer* level `s`, and whose second letter `y` is one of the two letters
that bring the running level back to an outer level.

The point of this file is that -- unlike the "degenerate" case `p = q`, where the level computation
fails and the two connection elements coincide -- the unit attached to such a pair is **not** a
genuine unit of the cherry: spelling out the four cases `(x, y)` shows that the unit is either `1` or
one of the two elements `±(pα · a · b · pβ⁻¹)` of the new generator of the window.  Consequently:

* the unit always lies in `tlWin p q m ⊔ ⟨pα·a·b·pβ⁻¹⟩`, and
* the level `s + lsig (tlW p q) [x,y]` is again an outer level.

Nothing here needs any hypothesis on `m` beyond `p ≠ q` (which is exactly what `hne` says, since
`m + 1 - p = m + 1 - q ↔ p = q`): the four computations are the identities
`a·a⁻¹ = 1`, `b⁻¹·b = 1`, `a·b`, `b⁻¹·a⁻¹`.
-/
import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

/-- The class of a two-letter word is the product of the classes of its letters. -/
private theorem cum_mk_pair (x y : Fin 2 × Bool) :
    FreeGroup.mk [x, y] = FreeGroup.mk [x] * FreeGroup.mk [y] := by
  rw [FreeGroup.mul_mk]; rfl

/-- A positive letter spells the corresponding generator. -/
private theorem cum_mk_true (a : Fin 2) : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl

/-- A negative letter spells the inverse of the corresponding generator. -/
private theorem cum_mk_false (a : Fin 2) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := rfl

/-- The trivial units `lsig` of the four relevant two-letter words of the weight `tlW p q`
(`a = 0 ↦ q`, `b = 1 ↦ -p`). -/
private theorem lsig_tlW_aaInv (p q : ℕ) :
    lsig (tlW p q) [((0 : Fin 2), true), ((0 : Fin 2), false)] = 0 := by
  simp [lsig, tlW]

private theorem lsig_tlW_bbInv (p q : ℕ) :
    lsig (tlW p q) [((1 : Fin 2), false), ((1 : Fin 2), true)] = 0 := by
  simp [lsig, tlW]

private theorem lsig_tlW_ab (p q : ℕ) :
    lsig (tlW p q) [((0 : Fin 2), true), ((1 : Fin 2), true)] = (q : ℤ) - p := by
  simp [lsig, tlW]; ring

private theorem lsig_tlW_bInvaInv (p q : ℕ) :
    lsig (tlW p q) [((1 : Fin 2), false), ((0 : Fin 2), false)] = (p : ℤ) - q := by
  simp [lsig, tlW]; ring

theorem cherry_unit_mem_ne (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℤ)
    (hne : m + 1 - (p : ℤ) ≠ m + 1 - (q : ℤ))
    {pα pβ : FreeGroup (Fin 2)} {s : ℤ} (x y : Fin 2 × Bool)
    (hx : (s = m + 1 - (q : ℤ) ∧ x = ((0 : Fin 2), true)) ∨
      (s = m + 1 - (p : ℤ) ∧ x = ((1 : Fin 2), false)))
    (hy : y = ((0 : Fin 2), false) ∨ y = ((1 : Fin 2), true)) :
    cherryConn p q m pα pβ s * FreeGroup.mk [x, y] *
        (cherryConn p q m pα pβ (s + lsig (tlW p q) [x, y]))⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) ∧
    cherryOuter p q m (s + lsig (tlW p q) [x, y]) := by
  have hG : pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹ ∈
      Subgroup.closure ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
        Set (FreeGroup (Fin 2))) := Subgroup.subset_closure (by simp)
  rcases hx with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · -- `x = a`, read at the level `m + 1 - q`, with `s = m + 1 - q`
    rcases hy with rfl | rfl
    · -- `x = a`, `y = a⁻¹`: the unit is `1`
      have hlvl : s + lsig (tlW p q) [((0 : Fin 2), true), ((0 : Fin 2), false)] =
          m + 1 - (q : ℤ) := by
        rw [hs, lsig_tlW_aaInv, add_zero]
      have hc : cherryConn p q m pα pβ s = pα := by rw [hs, cherryConn_self_q]
      have hc' : cherryConn p q m pα pβ
          (s + lsig (tlW p q) [((0 : Fin 2), true), ((0 : Fin 2), false)]) = pα := by
        rw [hlvl, cherryConn_self_q]
      refine ⟨?_, ?_⟩
      · rw [hc, hc', cum_mk_pair, cum_mk_true, cum_mk_false]
        simp
      · rw [hlvl]; unfold cherryOuter; exact Or.inr (Or.inl rfl)
    · -- `x = a`, `y = b`: the unit is the new generator `pα · a · b · pβ⁻¹` itself
      have hlvl : s + lsig (tlW p q) [((0 : Fin 2), true), ((1 : Fin 2), true)] =
          m + 1 - (p : ℤ) := by
        rw [hs, lsig_tlW_ab]; ring
      have hc : cherryConn p q m pα pβ s = pα := by rw [hs, cherryConn_self_q]
      have hc' : cherryConn p q m pα pβ
          (s + lsig (tlW p q) [((0 : Fin 2), true), ((1 : Fin 2), true)]) = pβ := by
        rw [hlvl, cherryConn_of_ne p q m pα pβ hne, if_pos rfl]
      refine ⟨?_, ?_⟩
      · rw [hc, hc', cum_mk_pair, cum_mk_true, cum_mk_true, ← mul_assoc]
        exact Subgroup.mem_sup_right hG
      · rw [hlvl]; unfold cherryOuter; exact Or.inr (Or.inr rfl)
  · -- `x = b⁻¹`, read at the level `m + 1 - p`, with `s = m + 1 - p`
    rcases hy with rfl | rfl
    · -- `x = b⁻¹`, `y = a⁻¹`: the unit is the inverse of the new generator
      have hlvl : s + lsig (tlW p q) [((1 : Fin 2), false), ((0 : Fin 2), false)] =
          m + 1 - (q : ℤ) := by
        rw [hs, lsig_tlW_bInvaInv]; ring
      have hc : cherryConn p q m pα pβ s = pβ := by
        rw [hs, cherryConn_of_ne p q m pα pβ hne, if_pos rfl]
      have hc' : cherryConn p q m pα pβ
          (s + lsig (tlW p q) [((1 : Fin 2), false), ((0 : Fin 2), false)]) = pα := by
        rw [hlvl, cherryConn_self_q]
      refine ⟨?_, ?_⟩
      · rw [hc, hc', cum_mk_pair, cum_mk_false, cum_mk_false]
        have hkey : pβ * ((FreeGroup.of (1 : Fin 2))⁻¹ * (FreeGroup.of (0 : Fin 2))⁻¹) *
              pα⁻¹ = (pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹)⁻¹ := by
          group
        rw [hkey]
        exact Subgroup.mem_sup_right (Subgroup.inv_mem _ hG)
      · rw [hlvl]; unfold cherryOuter; exact Or.inr (Or.inl rfl)
    · -- `x = b⁻¹`, `y = b`: the unit is `1`
      have hlvl : s + lsig (tlW p q) [((1 : Fin 2), false), ((1 : Fin 2), true)] =
          m + 1 - (p : ℤ) := by
        rw [hs, lsig_tlW_bbInv, add_zero]
      have hc : cherryConn p q m pα pβ s = pβ := by
        rw [hs, cherryConn_of_ne p q m pα pβ hne, if_pos rfl]
      have hc' : cherryConn p q m pα pβ
          (s + lsig (tlW p q) [((1 : Fin 2), false), ((1 : Fin 2), true)]) = pβ := by
        rw [hlvl, cherryConn_of_ne p q m pα pβ hne, if_pos rfl]
      refine ⟨?_, ?_⟩
      · rw [hc, hc', cum_mk_pair, cum_mk_false, cum_mk_true]
        simp
      · rw [hlvl]; unfold cherryOuter; exact Or.inr (Or.inr rfl)

end Work.OROneRel
