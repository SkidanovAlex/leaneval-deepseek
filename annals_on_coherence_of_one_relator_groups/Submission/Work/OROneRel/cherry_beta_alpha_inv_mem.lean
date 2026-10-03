import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

theorem cherry_beta_alpha_inv_mem (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {Lα Lβ : List (Fin 2 × Bool)} {pα pβ : FreeGroup (Fin 2)}
    (hmkα : FreeGroup.mk Lα = pα) (hmkβ : FreeGroup.mk Lβ = pβ)
    (hlsigα : lsig (tlW p q) Lα = m + 1 - (q : ℤ))
    (hlsigβ : lsig (tlW p q) Lβ = m + 1 - (p : ℤ))
    (hwalkα : ∀ e ∈ decor (tlW p q) 0 Lα, coverEdge e ∈ winE (tlW p q) 0 m)
    (hwalkβ : ∀ e ∈ decor (tlW p q) 0 Lβ, coverEdge e ∈ winE (tlW p q) 0 m)
    (heq : m + 1 - (p : ℤ) = m + 1 - (q : ℤ)) :
    pβ * pα⁻¹ ∈ tlWin p q m := by
  -- `tlWin p q m` is the closure of the classes representable by words of weight `0` whose walk
  -- stays in the window `[0,m]`.  The hypothesis `heq` forces the two attachment levels to
  -- coincide (`m+1-p = m+1-q`), so the word `Lβ ++ invRev Lα` is a closed walk: it follows the
  -- connection path `Lβ` from level `0` up to the attachment level and then retraces `Lα`
  -- backwards down to level `0`.
  rw [tlWin]
  refine Subgroup.subset_closure ⟨Lβ ++ FreeGroup.invRev Lα, ?_, ?_, ?_⟩
  · -- the class of the concatenation is `pβ * pα⁻¹`
    rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, hmkβ, hmkα]
  · -- its total weight is `(m+1-q) - (m+1-p) = 0`
    rw [decor_lsig_append, CoedgeBase.lsig_invRev, hlsigβ, hlsigα, heq]
    ring
  · -- the walk stays in the window: `Lβ` by `hwalkβ`, and the reversed `Lα` traverses exactly the
    -- (reversed) edges of `Lα`, which are in the window by `hwalkα`
    intro e he
    have hlev : (0 : ℤ) + lsig (tlW p q) Lβ = (0 : ℤ) + lsig (tlW p q) Lα := by
      rw [hlsigβ, hlsigα, heq]
    have hdec : decor (tlW p q) 0 (Lβ ++ FreeGroup.invRev Lα)
        = decor (tlW p q) 0 Lβ ++
          (decor (tlW p q) 0 Lα).reverse.map (fun x => (x.1, !x.2)) := by
      rw [decor_append, hlev, decor_invRev]
    rw [hdec] at he
    rcases List.mem_append.mp he with he | he
    · exact hwalkβ e he
    · obtain ⟨r, hr, hre⟩ := List.mem_map.mp he
      have hr' : r ∈ decor (tlW p q) 0 Lα := List.mem_reverse.mp hr
      have hce : coverEdge e = coverEdge r := by rw [← hre]; rfl
      rw [hce]
      exact hwalkα r hr'

end Work.OROneRel
