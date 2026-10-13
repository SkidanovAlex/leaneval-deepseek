import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE7.AboveAux

/-- Reassembling a point of `ℝ^{p+q}` from its first `p` and last `q` coordinates. -/
private theorem append_projFirst_projSnd {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (WilkiesDesign.E.projFirst p q z) (WilkiesDesign.E.projSnd p q z) = z := by
  funext i
  exact Fin.addCases (motive := fun i => Fin.append (WilkiesDesign.E.projFirst p q z)
      (WilkiesDesign.E.projSnd p q z) i = z i)
    (fun i => by rw [Fin.append_left]; rfl)
    (fun i => by rw [Fin.append_right]; rfl) i

/-- **The fibre over `x` has exactly as many points as any strictly increasing `k`-chain of
points of `S.X.set` above `x`.**  The `k` given sheets are pairwise distinct points of
`fiber S.X.set x`; since that fibre has `ncard = k` they exhaust it, and each lies below
level `t`, so the whole fibre does. -/
theorem level_lt_of_fibre_chain {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (C : Set (Fin p → ℝ)) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k)
    {x : Fin p → ℝ} (hx : x ∈ C) {t : ℝ}
    (ht : ∃ z : Fin k → (Fin (p + (m + 1)) → ℝ),
        (∀ l, z l ∈ S.X.set) ∧
        (∀ l, WilkiesDesign.E.projFirst p (m + 1) (z l) = x) ∧
        (∀ l l', l < l' → (z l) (Fin.natAdd p (Fin.last m)) <
          (z l') (Fin.natAdd p (Fin.last m))) ∧
        (∀ l, (z l) (Fin.natAdd p (Fin.last m)) < t)) :
    ∀ v ∈ WilkiesDesign.E.fiber S.X.set x, v (Fin.last m) < t := by
  obtain ⟨Z, hZmem, hZproj, hZmono, hZlt⟩ := ht
  set y : Fin k → (Fin (m + 1) → ℝ) := fun l => WilkiesDesign.E.projSnd p (m + 1) (Z l) with hy
  have hyl : ∀ l, y l = WilkiesDesign.E.projSnd p (m + 1) (Z l) := fun l => by rw [hy]
  have hlast : ∀ l, (y l) (Fin.last m) = (Z l) (Fin.natAdd p (Fin.last m)) := fun l => by
    rw [hyl l]; rfl
  -- the `k` sheets are pairwise distinct points of the fibre
  have hinj : Function.Injective y := by
    intro l l' hll
    rcases lt_trichotomy l l' with h | h | h
    · have h1 : (y l) (Fin.last m) < (y l') (Fin.last m) := by
        rw [hlast l, hlast l']; exact hZmono l l' h
      rw [hll] at h1
      exact absurd h1 (lt_irrefl _)
    · exact h
    · have h1 : (y l') (Fin.last m) < (y l) (Fin.last m) := by
        rw [hlast l, hlast l']; exact hZmono l' l h
      rw [hll] at h1
      exact absurd h1 (lt_irrefl _)
  have hsub : Set.range y ⊆ WilkiesDesign.E.fiber S.X.set x := by
    rintro v ⟨l, rfl⟩
    show Fin.append x (y l) ∈ S.X.set
    rw [hyl l, ← hZproj l, append_projFirst_projSnd (Z l)]
    exact hZmem l
  have hrange : (Set.range y).ncard = k := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- the fibre is finite because it has positive `ncard`
  have hfin : (WilkiesDesign.E.fiber S.X.set x).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard x hx]; exact hk)
  have hfac : WilkiesDesign.E.fiber S.X.set x = Set.range y :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard x hx, hrange]) hfin).symm
  intro v hv
  rw [hfac] at hv
  obtain ⟨l, rfl⟩ := hv
  rw [hlast l]
  exact hZlt l

end Work.WilE7.AboveAux
