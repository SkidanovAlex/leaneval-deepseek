import Mathlib
import Submission.Work.Pi6.EMODD.Defs
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.Models
import Submission.Work.Serre.piMapN_monoidHom
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

open Work.Serre

/-- **One more degree of the Postnikov tower.**  If `Y` is a model of `K(A,k)` in degrees `≤ m`
(with `k ≤ m`) then attaching `(m+2)`-cells along every map `S^{m+1} → Y` kills `π_{m+1}` and does
not change `π_i` for `i ≤ m`, so the result is a model of `K(A,k)` in degrees `≤ m+1`. -/
theorem killEnlarge (A : Type) [AddCommGroup A] (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (hY : Work.Serre.IsEMSpaceUpTo A k (by omega) m Y y₀) :
    Work.Serre.IsEMSpaceUpTo A k (by omega) (m + 1) (Work.Serre.KillCells m Y)
      (Work.Serre.killIncl m Y y₀) := by
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨eY, hYvan⟩ := hY
  have hstep := Work.Serre.killCells_step m Y
  refine ⟨?_, ?_⟩
  · -- the isomorphism on `π_k`: the inclusion `Y → KillCells m Y` is a `π_k`-isomorphism
    obtain ⟨F, hF⟩ := Work.Serre.piMapN_monoidHom (Work.Serre.killIncl m Y) k y₀
    have hFeq : ⇑F = Work.Serre.piMapN (Work.Serre.killIncl m Y) k y₀ := funext hF
    have hbij : Function.Bijective F := hFeq ▸ hstep.1 k hkm y₀
    exact ⟨(MulEquiv.ofBijective F hbij).symm.trans eY.some⟩
  · -- vanishing in all other degrees
    intro i hi hlt
    have him : i ≤ m + 1 := by rcases hlt with h | h <;> omega
    rcases Nat.lt_or_ge i (m + 1) with hlt' | hge
    · -- `i ≤ m`: transport triviality of `π_i Y` across the `π_i`-isomorphism
      have him' : i ≤ m := by omega
      haveI := hYvan i hi (Or.inr him')
      exact (hstep.1 i him' y₀).2.subsingleton
    · -- `i = m + 1`: the cells just attached kill `π_{m+1}`
      have hieq : i = m + 1 := by omega
      subst hieq
      exact hstep.2.1 (Work.Serre.killIncl m Y y₀)

end Work.Pi6.EMODD
