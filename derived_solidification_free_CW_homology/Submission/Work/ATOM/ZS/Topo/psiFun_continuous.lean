import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs

/-!
# Continuity of `ψ : (ℕ∪{∞}) × S ⟶ ℕ∪{∞}`

We prove that the function `Work.ATOM.psiFun S` is continuous, by means of the criterion
`Work.ATOM.continuous_onePoint_iff_isClopen`: it suffices to show that all its fibres over finite
indices `j : ℕ` are clopen.

The fibre of `ψ` over `j` is

`ψ ⁻¹' {j} = {n(j)} × {x | e_{n(j)} x = a_j}`

where `n(j) = lvl S j` (`Work.ATOM.ZS.Topo.psiFun_eq_some_iff`).  This is clopen because

* `{n(j)}` is a clopen point of `ℕ∪{∞}` (`Work.ATOM.isClopen_singleton_some`);
* `{x | e_{n(j)} x = a_j} = π_{n(j)} ⁻¹' {π_{n(j)} a_j}` (`isClopen_e_eq_a`), and `π_{n(j)}` takes
  values in the finite (hence discrete) component `S.component (n(j))`, so the fibre over a point
  is clopen.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint

namespace Work.ATOM.ZS.Topo

/-- **The fibre of `ψ` over a finite index.**  For `p : (ℕ∪{∞}) × S` and `j : ℕ` we have
`ψ p = j` if and only if `p = (n(j), x)` with `e_{n(j)} x = a_j` (where `n(j) = lvl S j`). -/
lemma psiFun_eq_some_iff (S : LightProfinite.{0}) [Infinite S] (j : ℕ) (p : ↥(NS S)) :
    psiFun S p = ((j : ℕ) : ℕ∪{∞}) ↔
      p.1 = ((lvl S j : ℕ) : ℕ∪{∞}) ∧ e S (lvl S j) p.2 = (levelData S).a j := by
  obtain ⟨k, x⟩ := p
  constructor
  · intro h
    by_cases hk : k = ∞
    · subst hk
      simp only at h
      exact absurd h.symm (OnePoint.coe_ne_infty j)
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp hk
      subst hm
      by_cases hc : e S m x ∈ Set.range (levelData S).a ∧ (levelData S).lv (e S m x) = m
      · have hmi : (levelData S).idx (e S m x) = j := by
          have h2 := psiFun_some_of (S := S) m hc
          rw [h2] at h
          exact OnePoint.coe_eq_coe.mp h
        have hax : (levelData S).a j = e S m x := by
          have hy : e S m x ∈ levelSet' S := levelData_range (S := S) ▸ hc.1
          rw [← hmi, levelData_a_idx (S := S) (e S m x) hy]
        have hlv : lvl S j = m := by
          rw [lvl, hax]; exact hc.2
        exact ⟨by rw [hlv], by rw [hlv]; exact hax.symm⟩
      · exfalso
        have h2 := psiFun_some_eq_infty (S := S) m hc
        rw [h2] at h
        exact (OnePoint.coe_ne_infty j) h.symm
  · rintro ⟨h1, h2⟩
    have hk : k = ((lvl S j : ℕ) : ℕ∪{∞}) := h1
    rw [hk]
    exact psiFun_some_eq (S := S) (lvl S j) h2 rfl

/-- The fibre of `ψ` over `j` is the set `{n(j)} × {x | e_{n(j)} x = a_j}`. -/
lemma psiFun_preimage_singleton (S : LightProfinite.{0}) [Infinite S] (j : ℕ) :
    psiFun S ⁻¹' {((j : ℕ) : ℕ∪{∞})} =
      (fun p : ↥(NS S) => p.1) ⁻¹' {((lvl S j : ℕ) : ℕ∪{∞})} ∩
        (fun p : ↥(NS S) => p.2) ⁻¹' {x : ↥S | e S (lvl S j) x = (levelData S).a j} := by
  ext p
  rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, psiFun_eq_some_iff]
  tauto

/-- The set `{x : S | e_{n(j)} x = a_j}` is clopen: `e_{n(j)}` factors through the finite component
`S.component (n(j))`, on which points are clopen. -/
lemma isClopen_e_eq_a (S : LightProfinite.{0}) [Infinite S] (j : ℕ) :
    IsClopen {x : ↥S | e S (lvl S j) x = (levelData S).a j} := by
  have hset : {x : ↥S | e S (lvl S j) x = (levelData S).a j} =
      S.proj (lvl S j) ⁻¹' {S.proj (lvl S j) ((levelData S).a j)} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have h2 := congrArg (S.proj (lvl S j)) h
      rwa [e_apply, sig_proj_apply] at h2
    · intro h
      have h' : e S (lvl S j) x = e S (lvl S j) ((levelData S).a j) := by
        rw [e_apply, e_apply, h]
      rwa [levelData_e_lvl_a j] at h'
  rw [hset]
  exact (isClopen_discrete _).preimage (by fun_prop)

theorem psiFun_continuous (S : LightProfinite.{0}) [Infinite S] :
    Continuous (Work.ATOM.psiFun S) := by
  rw [continuous_onePoint_iff_isClopen]
  intro j
  rw [psiFun_preimage_singleton]
  refine IsClopen.inter ?_ ?_
  · exact (isClopen_singleton_some (lvl S j)).preimage continuous_fst
  · exact (isClopen_e_eq_a S j).preimage continuous_snd

end Work.ATOM.ZS.Topo
