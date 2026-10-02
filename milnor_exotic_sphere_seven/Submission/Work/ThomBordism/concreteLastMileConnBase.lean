import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.GenuineTransversality
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the last mile in the CONNECTED-FAMILY form — the `SourceWiring`-free part

`Submission/Work/ThomBordism/NOTE_SESSION64.md` sections 8-14.  The boundary coordination of the last
mile needs *connectedness* of the pieces (the branch of `pulledThom_gauss` is pinned only through
`Work.ThomBordism.localDegree_universalThomClass`, whose statement carries `[ConnectedSpace V.pt]`),
so the producer interface of the source construction is restated in the connected-family form.

This module contains the part of the connected-family last-mile chain that does **not** mention the
orientation producer, so that it can be imported by
`Submission/Work/PTGeometric/SourceWiring.lean` itself (which must *produce* the producer and
therefore cannot be imported here — that would be an import cycle).  The producer-facing half lives in
`Submission/Work/ThomBordism/concreteLastMileConn.lean`.

## Why `ConcreteLastMileFixed`

`Work.PTGeometric.ConcreteLastMile k D` binds its own `ι` and `Fam`, so a hypothesis on the family
cannot reach it; `ConcreteLastMileFixed` is the same statement with the family *instantiated*, which
is the shape a connectedness hypothesis can be attached to.

## Main results

* `Work.ThomBordism.ConcreteLastMileFixed`, `Work.ThomBordism.ConcreteLastMileConn`;
* `Work.ThomBordism.ConcreteLastMileFixed.of_lastMile`,
  `Work.ThomBordism.concreteLastMileConn_of_lastMile`;
* `Work.ThomBordism.transversalityCoreFamilyConn_of_concreteLastMileConn`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism

open Work.PTGeometric

noncomputable section

/-- **`Work.PTGeometric.ConcreteLastMile k D` with the family fixed.**  This is the shape in which the
connectedness hypothesis `(∀ i, ConnectedSpace (Fam i).pt)` can be attached to the last mile. -/
def ConcreteLastMileFixed (k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) (ι : Type)
    [Fintype ι] (Fam : ι → Man8) : Prop :=
  ∀ (G : GenuineTubeGeometry k D ι Fam) (m : ℕ), 0 < m →
    (∏ i, tubeAlpha (G.rep i)) ^ m = 1 →
    ∃ N' : ℕ, 0 < N' ∧ Nonempty (NullBordismFamily (Fin N' × ι) (fun x => Fam x.2))

/-- The fixed-family statement follows from the unrestricted one (its `ι`, `Fam` binders are simply
instantiated). -/
theorem ConcreteLastMileFixed.of_lastMile {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (h : Work.PTGeometric.ConcreteLastMile k D) : ConcreteLastMileFixed k D ι Fam :=
  h ι Fam

/-- **The last mile restricted to connected families** — the form in which the endgame consumes it. -/
def ConcreteLastMileConn (k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8), (∀ i, ConnectedSpace (Fam i).pt) →
    ConcreteLastMileFixed k D ι Fam

/-- The unrestricted last mile implies the connected-family one. -/
theorem concreteLastMileConn_of_lastMile {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    (h : Work.PTGeometric.ConcreteLastMile k D) : ConcreteLastMileConn k D :=
  fun ι _ Fam _ => ConcreteLastMileFixed.of_lastMile (D := D) (Fam := Fam) h

/-- **The connected-family deliverable from the connected-family last mile.**

A copy of `Work.PTGeometric.transversalityCoreFamilyConn_of_concreteDataConn` with
`ConcreteLastMileConn` in place of `ConcreteLastMile`. -/
theorem transversalityCoreFamilyConn_of_concreteLastMileConn
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : Work.ThomBordism.PontryaginThom.ThomTarget k,
        Nonempty (GenuineTubeGeometry k D ι F) ∧ ConcreteLastMileConn k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn := by
  intro ι _ F hconn h1 h2
  obtain ⟨k, hk, D, ⟨G⟩, hG⟩ := hdata ι F hconn
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (G.rep i))
  obtain ⟨m, hm, hpow⟩ := ρ.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  have hρ : ρ.α = ∏ i, tubeAlpha (G.rep i) := by rw [hρα]; rfl
  have hpow' : (∏ i, tubeAlpha (G.rep i)) ^ m = 1 := by rw [← hρ]; exact hpow
  exact hG ι F hconn G m hm hpow'

end

end Work.ThomBordism
