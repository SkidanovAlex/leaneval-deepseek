import Mathlib
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_state_flipSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **Transport of a Voronoi piece along a group element whose translate is a sign index.**

If the "state" `(toG (foldKr i ·), foldCr i ·)` of `r'` is the `γ`-translate of that of `r`, then
`actX γ` carries the Voronoi piece `Dvor i r` onto `Dvor i r'`.  This is the Voronoi analogue of
`actX_image_Dlift`: the copies agree by `hc`, the walls are permuted by `sidePerm γ.1` by `hk`
(`sidePerm γ.1 (foldWalls i r' t) = foldWalls i r t`), and the strict inequalities of
`VoronoiOpen` transport along `sideSlack_act`, `truncSlack_act` and the induced permutations of the
`24` sides and the `24` truncations. -/
theorem actX_image_Dvor_of_state (i : Fin 98) (γ : Gg) (r r' : Fin (foldCodim i) → Bool)
    (hk : toG (foldKr i r') = γ.1 + toG (foldKr i r))
    (hc : foldCr i r' = γ.2 + foldCr i r) :
    actX γ '' Dvor i r = Dvor i r' := by
  -- The walls of `r'` are the `γ`-images of the walls of `r`, and conversely.
  have hwall : ∀ t : Fin (foldCodim i), sidePerm γ.1 (foldWalls i r' t) = foldWalls i r t := by
    intro t
    have harg : γ.1 + toG (foldKr i r') = toG (foldKr i r) := by
      have hgg : γ.1 + γ.1 = 0 := by ext j; exact ZMod2_add_self (γ.1 j)
      calc γ.1 + toG (foldKr i r') = γ.1 + (γ.1 + toG (foldKr i r)) := by rw [hk]
        _ = (γ.1 + γ.1) + toG (foldKr i r) := by rw [add_assoc]
        _ = toG (foldKr i r) := by rw [hgg, zero_add]
    simp only [foldWalls]
    rw [← sidePerm_add, harg]
  have hwall' : ∀ t : Fin (foldCodim i), foldWalls i r' t = sidePerm γ.1 (foldWalls i r t) := by
    intro t
    have h2 := congrArg (sidePerm γ.1) (hwall t)
    rwa [sidePerm_invol] at h2
  ext x
  constructor
  · -- `actX γ` maps `Dvor i r` into `Dvor i r'`.
    rintro ⟨z, hz, rfl⟩
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, ?_⟩
    · show z.1 + γ.2 = foldCr i r'
      rw [hc, hz1]; abel
    · rw [mem_VoronoiOpen] at hz2 ⊢
      obtain ⟨hz2a, hz2b⟩ := hz2
      refine ⟨?_, ?_⟩
      · intro S hS
        have hS' : ∀ t : Fin (foldCodim i), foldWalls i r t ≠ sidePerm γ.1 S := by
          intro t ht
          exact hS t (by rw [hwall' t, ht, sidePerm_invol])
        obtain ⟨h0, hlt⟩ := hz2a (sidePerm γ.1 S) hS'
        refine ⟨?_, ?_⟩
        · rw [actX_snd, sideSlack_act]; exact h0
        · intro t
          rw [actX_snd, sideSlack_act, sideSlack_act, hwall t]
          exact hlt t
      · intro w
        obtain ⟨h0, hlt⟩ := hz2b (truncPerm γ.1 w)
        refine ⟨?_, ?_⟩
        · rw [actX_snd, truncSlack_act]; exact h0
        · intro t
          rw [actX_snd, sideSlack_act, truncSlack_act, hwall t]
          exact hlt t
  · -- `actX γ` maps `Dvor i r'` into `Dvor i r`; the action is an involution.
    rintro hz'
    obtain ⟨hz'1, hz'2⟩ := hz'
    refine ⟨actX γ x, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show x.1 + γ.2 = foldCr i r
        calc x.1 + γ.2 = (γ.2 + foldCr i r) + γ.2 := by rw [hz'1, hc]
          _ = (γ.2 + γ.2) + foldCr i r := by abel
          _ = foldCr i r := by rw [ZMod2_add_self γ.2, zero_add]
      · rw [mem_VoronoiOpen] at hz'2 ⊢
        obtain ⟨hz'2a, hz'2b⟩ := hz'2
        refine ⟨?_, ?_⟩
        · intro S hS
          have hS' : ∀ t : Fin (foldCodim i), foldWalls i r' t ≠ sidePerm γ.1 S := by
            intro t ht
            exact hS t (by rw [← hwall t, ht, sidePerm_invol])
          obtain ⟨h0, hlt⟩ := hz'2a (sidePerm γ.1 S) hS'
          refine ⟨?_, ?_⟩
          · rw [actX_snd, sideSlack_act]; exact h0
          · intro t
            rw [actX_snd, sideSlack_act, ← hwall' t, sideSlack_act]
            exact hlt t
        · intro w
          obtain ⟨h0, hlt⟩ := hz'2b (truncPerm γ.1 w)
          refine ⟨?_, ?_⟩
          · rw [actX_snd, truncSlack_act]; exact h0
          · intro t
            rw [actX_snd, sideSlack_act, ← hwall' t, truncSlack_act]
            exact hlt t
    · rw [actX_add, Gg_add_self, actX_zero]

/-- **The identification `actX (wallSum i Δ)` carries the Voronoi piece `Dvor i r` onto the piece
`Dvor i (flipSet r Δ)`.**  The flip step `fold_state_flipSet` identifies the state of `flipSet r Δ`
with the `wallSum i Δ`-translate of the state of `r`, and `actX_image_Dvor_of_state` transports the
piece along that group element. -/
theorem actX_image_Dvor (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    actX (wallSum i Δ) '' Dvor i r = Dvor i (flipSet r Δ) := by
  have hk : toG (foldKr i (flipSet r Δ)) = (wallSum i Δ).1 + toG (foldKr i r) := by
    have h := congrArg Prod.fst (fold_state_flipSet i r Δ)
    simpa using h
  have hc : foldCr i (flipSet r Δ) = (wallSum i Δ).2 + foldCr i r := by
    have h := congrArg Prod.snd (fold_state_flipSet i r Δ)
    simpa using h
  exact actX_image_Dvor_of_state i (wallSum i Δ) r (flipSet r Δ) hk hc

end Work.FoldInst
