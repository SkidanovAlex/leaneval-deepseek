import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps

/-!
# AREA ATOM / `ℤ[S]`: the fibre of `ψ` over a finite value

`Work.ATOM.psiN : (ℕ∪{∞}) ⊗ S ⟶ ℕ∪{∞}` is the map `ψ` of `Submission/Work/ATOM/ZS/Topo/Defs.lean`:
`ψ(k,x) = idx (e_k x)` if `e_k x` is a point of level exactly `k` different from `s₀`, and `∞`
otherwise.

This file records the structure of a point `p` at which `ψ` takes a *finite* value `j`: then the
first coordinate of `p` is finite, say `k`, the point is `(k,x)`, the idempotent `e_k` fixes `x` up
to the enumerated point `a_j`, and `k` is exactly the level `n(j)` of `a_j`.  This is the pointwise
input identifying the two sides of the identity `ℤ[ψ] ∘ ĝ` of REFS/03 §1 at a generator of `P`
(the other case, `ψ(p) = ∞`, is `Submission/Work/ATOM/ZS/psiN_gBig_infty.lean`).
-/

open OnePoint

namespace Work.ATOM.ZS

theorem psiN_gBig_finite (S : LightProfinite.{0}) [Infinite S] (p : ↥(Work.ATOM.NS S)) (j : ℕ)
    (h : Work.ATOM.psiN S p = ((j : ℕ) : LightProfinite.NatUnionInfty)) :
    ∃ k : ℕ, ∃ x : ↥S, p = Work.ATOM.mkNS S ((k : ℕ) : LightProfinite.NatUnionInfty) x ∧
      Work.ATOM.e S k x = (Work.ATOM.levelData S).a j ∧ Work.ATOM.lvl S j = k := by
  classical
  -- `ψ` is the underlying function `psiFun`
  rw [Work.ATOM.psiN_apply] at h
  -- `ψ` takes the value `∞` at every point of `(ℕ∪{∞}) ⊗ S` whose first coordinate is `∞`
  have hne : p.1 ≠ ∞ := by
    intro hinf
    have h2 : Work.ATOM.psiFun S p = ∞ := by
      simp only [Work.ATOM.psiFun, hinf, OnePoint.elim_infty]
    rw [h2] at h
    exact absurd h.symm (OnePoint.coe_ne_infty j)
  -- hence the first coordinate is a natural number `k`
  obtain ⟨k, hk⟩ := OnePoint.ne_infty_iff_exists.mp hne
  -- and we may replace `p` by `(k, p.2)`
  have hp : Work.ATOM.mkNS S ((k : ℕ) : LightProfinite.NatUnionInfty) p.2 = p := by
    simp only [Work.ATOM.mkNS]
    rw [hk]
    exact Prod.ext rfl rfl
  rw [← hp] at h
  by_cases hc : Work.ATOM.e S k p.2 ∈ Set.range (Work.ATOM.levelData S).a ∧
      (Work.ATOM.levelData S).lv (Work.ATOM.e S k p.2) = k
  · -- `ψ(k,x)` is the index of `e_k x`: so `e_k x = a_j`
    have hidx : (Work.ATOM.levelData S).idx (Work.ATOM.e S k p.2) = j :=
      OnePoint.coe_eq_coe.mp ((Work.ATOM.psiFun_some_of k hc).symm.trans h)
    obtain ⟨i, hi⟩ := hc.1
    have hia : i = j := by rw [← hidx, ← hi, (Work.ATOM.levelData S).idx_a i]
    refine ⟨k, p.2, hp.symm, ?_, ?_⟩
    · rw [← hia, hi]
    · -- and `k` is the level of `e_k x = a_j`
      rw [Work.ATOM.lvl, ← hia, hi]
      exact hc.2
  · -- `ψ` takes the value `∞` off the locus of points of level `k`
    have hinf' : Work.ATOM.psiFun S
        (Work.ATOM.mkNS S ((k : ℕ) : LightProfinite.NatUnionInfty) p.2) = ∞ :=
      Work.ATOM.psiFun_some_eq_infty k hc
    rw [hinf'] at h
    exact absurd h.symm (OnePoint.coe_ne_infty j)

end Work.ATOM.ZS
