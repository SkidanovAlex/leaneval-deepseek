import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

/-!
# The "old walk" bookkeeping of the cherry lemma

`cherryConn p q m pα pβ v` is the connection element attached to an outer level `v`, spelled by
`cherryConnList p q m Lα Lβ v` (the witness word `Lα` of `pα` at level `m+1-q`, the witness word
`Lβ` of `pβ` at level `m+1-p`, or the empty word at level `0`).

`cherryOld_mem` states that a loop of the *old* window `[0,m]` run from the outer level `s` to the
outer level `t`, transported by the two connection elements, is an element of the window subgroup
`tlWin p q m`.  Concretely the word

  `cherryConnList p q m Lα Lβ s ++ A ++ (cherryConnList p q m Lα Lβ t)⁻¹`

has weight `s + (t - s) - t = 0` and its decorated walk stays in the window `[0,m]`: the `s`-th
outer level is the endpoint of the connection word at level `s`, the word `A` has weight `t - s` and
its walk (given from level `s`) lies in the window, and the reversed connection word at level `t`
mirrors the connection walk back down to level `0`.

The two elementary facts about the connection words (`cherryConnList_lsig`,
`cherryConnList_walk`) and the mirroring of a window walk under `FreeGroup.invRev`
(`decor_invRev_winE`) are the pieces of the assembly.
-/

/-- **The weight of a connection word is the level it connects.**  For an outer level `v`, the
connection word `cherryConnList p q m Lα Lβ v` has weight `v`: branch `v = m+1-q` uses
`lsig Lα = m+1-q`, branch `v = m+1-p` uses `lsig Lβ = m+1-p` (this needs a case split on `p = q`,
when the first branch wins), and the last branch `v = 0` is the empty word. -/
theorem cherryConnList_lsig (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {Lα Lβ : List (Fin 2 × Bool)}
    (hlsigα : lsig (tlW p q) Lα = m + 1 - (q : ℤ))
    (hlsigβ : lsig (tlW p q) Lβ = m + 1 - (p : ℤ))
    {v : ℤ} (hv : cherryOuter p q m v) :
    lsig (tlW p q) (cherryConnList p q m Lα Lβ v) = v := by
  rcases hv with rfl | rfl | rfl
  · rw [cherryConnList_zero p q hp hq hm1 Lα Lβ, lsig_nil]
  · rw [cherryConnList_self_q, hlsigα]
  · by_cases hpq : m + 1 - (p : ℤ) = m + 1 - (q : ℤ)
    · rw [cherryConnList, if_pos hpq, hlsigα]; omega
    · rw [cherryConnList, if_neg hpq, if_pos rfl, hlsigβ]

/-- **The walk of a connection word lies in the old window `[0,m]`.**  The branch `v = m+1-q`
uses the witness walk `hwalkα`, the branch `v = m+1-p` uses `hwalkβ` (again splitting on `p = q`),
and the branch `v = 0` is empty. -/
theorem cherryConnList_walk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {Lα Lβ : List (Fin 2 × Bool)}
    (hwalkα : ∀ e ∈ decor (tlW p q) 0 Lα, coverEdge e ∈ winE (tlW p q) 0 m)
    (hwalkβ : ∀ e ∈ decor (tlW p q) 0 Lβ, coverEdge e ∈ winE (tlW p q) 0 m)
    {v : ℤ} (hv : cherryOuter p q m v) :
    ∀ e ∈ decor (tlW p q) 0 (cherryConnList p q m Lα Lβ v),
      coverEdge e ∈ winE (tlW p q) 0 m := by
  rcases hv with rfl | rfl | rfl
  · rw [cherryConnList_zero p q hp hq hm1 Lα Lβ]
    intro e he
    exact (List.not_mem_nil he).elim
  · rw [cherryConnList_self_q]
    exact hwalkα
  · by_cases hpq : m + 1 - (p : ℤ) = m + 1 - (q : ℤ)
    · rw [cherryConnList, if_pos hpq]; exact hwalkα
    · rw [cherryConnList, if_neg hpq, if_pos rfl]; exact hwalkβ

/-- **A window walk reversed.**  If the decorated walk of `L` started at level `0` lies in the
window `[0,hi]` and `lsig c L = t`, then the decorated walk of the reversed word `FreeGroup.invRev L`
started at level `t` (i.e. read back down to level `0`) also lies in the window `[0,hi]`:
`decor_invRev` identifies it with the reverse of `decor c 0 L` with the booleans flipped, and the
edge `coverEdge` sees only the letter, not the boolean. -/
theorem decor_invRev_winE {α : Type*} (c : α → ℤ) {hi t : ℤ} (L : List (α × Bool))
    (hlsig : lsig c L = t)
    (hwalk : ∀ e ∈ decor c 0 L, coverEdge e ∈ winE c 0 hi) :
    ∀ e ∈ decor c t (FreeGroup.invRev L), coverEdge e ∈ winE c 0 hi := by
  intro e he
  have h : decor c t (FreeGroup.invRev L) =
      (decor c 0 L).reverse.map (fun p => (p.1, !p.2)) := by
    rw [← hlsig, ← decor_invRev c 0 L]
    simp
  rw [h] at he
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp he
  rw [← hpe]
  exact hwalk p (List.mem_reverse.mp hp)

theorem cherryOld_mem (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    {Lα Lβ : List (Fin 2 × Bool)} {pα pβ : FreeGroup (Fin 2)}
    (hmkα : FreeGroup.mk Lα = pα) (hmkβ : FreeGroup.mk Lβ = pβ)
    (hlsigα : lsig (tlW p q) Lα = m + 1 - (q : ℤ))
    (hlsigβ : lsig (tlW p q) Lβ = m + 1 - (p : ℤ))
    (hwalkα : ∀ e ∈ decor (tlW p q) 0 Lα, coverEdge e ∈ winE (tlW p q) 0 m)
    (hwalkβ : ∀ e ∈ decor (tlW p q) 0 Lβ, coverEdge e ∈ winE (tlW p q) 0 m)
    {s t : ℤ} (hs : cherryOuter p q m s) (ht : cherryOuter p q m t)
    {A : List (Fin 2 × Bool)}
    (hA : ∀ e ∈ decor (tlW p q) s A, coverEdge e ∈ winE (tlW p q) 0 m)
    (hls : lsig (tlW p q) A = t - s) :
    cherryConn p q m pα pβ s * FreeGroup.mk A * (cherryConn p q m pα pβ t)⁻¹ ∈
      tlWin p q m := by
  classical
  have hCs_lsig := cherryConnList_lsig p q hp hq hm1 hlsigα hlsigβ hs
  have hCt_lsig := cherryConnList_lsig p q hp hq hm1 hlsigα hlsigβ ht
  have hCs_walk := cherryConnList_walk p q hp hq hm1 hwalkα hwalkβ hs
  have hCt_walk := cherryConnList_walk p q hp hq hm1 hwalkα hwalkβ ht
  have hRev_walk := decor_invRev_winE (tlW p q) (cherryConnList p q m Lα Lβ t) hCt_lsig hCt_walk
  -- The product is spelled by the concatenated word `Cs ++ A ++ (Ct)⁻¹`.
  have hL : cherryConn p q m pα pβ s * FreeGroup.mk A * (cherryConn p q m pα pβ t)⁻¹
      = FreeGroup.mk (cherryConnList p q m Lα Lβ s ++ A ++
          FreeGroup.invRev (cherryConnList p q m Lα Lβ t)) := by
    rw [← cherryConn_mk p q m hmkα hmkβ s, ← cherryConn_mk p q m hmkα hmkβ t,
        FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk]
  rw [hL]
  refine Subgroup.subset_closure ⟨_, rfl, ?_, ?_⟩
  · -- the weight of the concatenation is `0`
    simp only [decor_lsig_append, CoedgeBase.lsig_invRev, hCs_lsig, hls, hCt_lsig]
    ring
  · -- each edge of the walk lies in the window `[0,m]`
    intro e he
    rw [decor_append, decor_append] at he
    rcases List.mem_append.mp he with h | h
    · rcases List.mem_append.mp h with h1 | h2
      · exact hCs_walk e h1
      · rw [zero_add, hCs_lsig] at h2
        exact hA e h2
    · have hmid : 0 + lsig (tlW p q) (cherryConnList p q m Lα Lβ s ++ A) = t := by
        rw [decor_lsig_append, hCs_lsig, hls]; ring
      rw [hmid] at h
      exact hRev_walk e h

end Work.OROneRel
