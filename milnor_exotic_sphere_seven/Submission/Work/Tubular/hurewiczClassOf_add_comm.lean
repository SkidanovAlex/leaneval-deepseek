import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz class under a reindexing of the cube

`Work.ThomBordism.PontryaginThom.hurewiczClassOf n hn t₀ α` is the Hurewicz class of a homotopy
class `α ∈ πₙ(T,t₀)`.  The Pontryagin–Thom assembly of the project produces loops at degree
`8 + k` (`Work.Tubular.alphaV`, `Work.Tubular.tubeGenLoopOnePoint`) while the interface
`Work.Tubular.TubeThomRep` is stated at degree `k + 8`; the two degrees are related by the
canonical reindexing `Fin (8+k) ≃ Fin (k+8)` of the cube.  This module records that the Hurewicz
class is compatible with that reindexing.

* `Work.Tubular.hurewiczClassOf_proof_irrel` — the Hurewicz class does not depend on the *proof*
  of `1 ≤ n` (all the choices inside it depend on `n` only through propositions);
* `Work.Tubular.hurewiczClassOf_finCongr` — the general form, for any `h : n = m`;
* `Work.Tubular.hurewiczClassOf_add_comm` — the case `h = Nat.add_comm 8 k` used by the assembly.
-/

set_option autoImplicit false

namespace Work.Tubular

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- The Hurewicz class does not depend on the proof of `1 ≤ n`.  Every `Classical.choose` inside
`Work.Stems.hurewiczChain` is applied to a proposition in which `hn` occurs only as a *proof*, so
two proofs give the same value. -/
theorem hurewiczClassOf_proof_irrel {n : ℕ} (h h' : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (x₀ : X) (α : HomotopyGroup (Fin n) X x₀) :
    hurewiczClassOf n h x₀ α = hurewiczClassOf n h' x₀ α := by
  rw [Subsingleton.elim h h']

/-- **The Hurewicz class under a reindexing of the cube.**  For an equality of degrees `h : n = m`,
the Hurewicz class of the reindexed cube is the transport of the Hurewicz class. -/
theorem hurewiczClassOf_finCongr {n m : ℕ} (h : n = m) (hn : 1 ≤ n) (hm : 1 ≤ m)
    {X : Type} [TopologicalSpace X] (x₀ : X) (c : GenLoop (Fin n) X x₀) :
    hurewiczClassOf m hm x₀ (Quotient.mk _ ((GenLoop.congr x₀ (finCongr h)) c))
      = h ▸ (hurewiczClassOf n hn x₀ (Quotient.mk _ c)) := by
  cases h
  have hc : GenLoop.congr x₀ (finCongr (rfl : n = n)) c = c := by
    ext t
    rfl
  rw [hc]

/-- **The `8 + k ↔ k + 8` bookkeeping for the Hurewicz class.**  This is the identity the
Pontryagin–Thom assembly needs in order to move the collapse loop from the degree `8 + k` of
`Work.Tubular.alphaV` to the degree `k + 8` of `Work.Tubular.TubeThomRep`. -/
theorem hurewiczClassOf_add_comm {k : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (c : GenLoop (Fin (8 + k)) X x₀) :
    hurewiczClassOf (k + 8) (by omega) x₀
        (Quotient.mk _ ((GenLoop.congr x₀ (finCongr (Nat.add_comm 8 k))) c))
      = (Nat.add_comm 8 k) ▸
        (hurewiczClassOf (8 + k) (by omega) x₀ (Quotient.mk _ c)) :=
  hurewiczClassOf_finCongr (Nat.add_comm 8 k) (by omega) (by omega) x₀ c

end

end Work.Tubular
