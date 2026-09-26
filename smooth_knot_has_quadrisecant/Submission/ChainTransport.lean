import Mathlib
import Submission.OChartTwoStep

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — finite-chain gluing: iterated
transport along a chain of aligned monotone patches (third subgoal of the
interval-chain exhaustion)

`OChartTwoStep.lean` (S110) proved the atomic two-step composite
(`MonotoneDirectionOn` + injectivity).  This module proves the *iterated*
composite over a whole chain in a purely combinatorial form — lists of
bundled monotone interval patches with explicit alignment membership
conditions — so the statement has no dependency on paths or chart
geometry: exactly the shape the S106 scoping note endorses (alignment is
explicit data, never transported along arbitrary paths).

Content (namespace LeanEval.KnotTheory.Quadrisecant):

1. **`MonoPiece`** — a bundled open-interval piece with a monotone-in-one-
   direction coordinate map (`lo hi : ℝ`, `τ : ChartInterval lo hi → ℝ`,
   `hmono : MonotoneOnPiece τ`);
2. generic composition engine for `MonotoneDirectionOn`:
   **`MonotoneDirectionOn.comp_of_coord`** — if the transport `f : D → E`
   is monotone in one direction as a coordinate map (`cE ∘ f` monotone in
   `cD`) and `g` is monotone in one direction with respect to `cE`, then
   `g ∘ f` is monotone in one direction with respect to `cD` (the four
   direction combinations), and **`MonotoneDirectionOn.coord_eq`** — a
   pointwise coordinate change transfers the property;
3. **`transports`** — the alignment predicate: a parameter `x₁` of piece
   `q` transports through the rest of the chain iff each step's value
   lands in the next piece's interval (recursive, existential over the
   membership proofs);
4. **`ChainDomain`** — the type of chain-start parameters (elements of
   the first piece whose transport through the whole chain exists);
5. **`chainCoord`** (the real value of the start parameter, injective on
   the chain domain by two `Subtype.ext`s: `chainCoord_injective`) and
   **`chainValue`** (the transported coordinate after all patches are
   applied, by recursion on the chain);
6. **`chain_transport_monotone_direction`** — the iterated transport is
   monotone in one direction with respect to the starting coordinate
   (induction on the chain: the one-piece case is the patch's own
   monotonicity on its subtype domain, the cons case applies the S110
   two-step composite through the generic composition engine and the
   recursion equation `chainValue (p :: q :: rest) x =
   chainValue (q :: rest) ⟨⟨p.τ x.1, …⟩, …⟩`), and
   **`chain_transport_injective`** — monotone-in-one-direction with
   injective coordinate gives injectivity
   (`MonotoneDirectionOn.injective`).

This is the pure engine of the finite-chain iterated transport; the
instantiation with the S99/S105 chart-chain junction data (per-junction
monotone neighbourhoods, S106 shrinking to make patches aligned, backward
induction choosing the shrunk pieces) is recorded as the next slice.
Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option synthInstance.maxHeartbeats 800000

structure MonoPiece where
  lo : ℝ
  hi : ℝ
  τ : ChartInterval lo hi → ℝ
  hmono : MonotoneOnPiece τ

lemma MonotoneDirectionOn.comp_of_coord {D E : Type*} (cD : D → ℝ) (cE : E → ℝ)
    (f : D → E) (g : E → ℝ)
    (hf : MonotoneDirectionOn cD (fun x => cE (f x)))
    (hg : MonotoneDirectionOn cE g) :
    MonotoneDirectionOn cD (fun x => g (f x)) := by
  rcases hg with hgi | hgd
  · rcases hf with hfi | hfd
    · left
      intro a b hab
      exact hgi (f a) (f b) (hfi a b hab)
    · right
      intro a b hab
      exact hgi (f b) (f a) (hfd a b hab)
  · rcases hf with hfi | hfd
    · right
      intro a b hab
      exact hgd (f a) (f b) (hfi a b hab)
    · left
      intro a b hab
      exact hgd (f b) (f a) (hfd a b hab)

lemma MonotoneDirectionOn.coord_eq {D : Type*} {c c' : D → ℝ} {f : D → ℝ}
    (hc : ∀ x : D, c' x = c x) (h : MonotoneDirectionOn c f) :
    MonotoneDirectionOn c' f := by
  rcases h with hfi | hfd
  · left
    intro a b hab
    rw [hc a, hc b] at hab
    exact hfi a b hab
  · right
    intro a b hab
    rw [hc a, hc b] at hab
    exact hfd a b hab

def transports (q : MonoPiece) : List MonoPiece → ChartInterval q.lo q.hi → Prop
  | [], _ => True
  | r :: rest, x => ∃ h : q.τ x ∈ Set.Ioo r.lo r.hi, transports r rest ⟨q.τ x, h⟩

def ChainDomain : List MonoPiece → Type
  | [] => PUnit
  | p :: rest => {x : ChartInterval p.lo p.hi // transports p rest x}

def chainCoord : (ps : List MonoPiece) → ChainDomain ps → ℝ
  | [], _ => 0
  | _ :: _, x => (x.1 : ℝ)

def chainValue : (ps : List MonoPiece) → ChainDomain ps → ℝ
  | [], _ => 0
  | [p], x => p.τ x.1
  | p :: q :: rest, x =>
      chainValue (q :: rest) ⟨⟨p.τ x.1, x.2.choose⟩, x.2.choose_spec⟩

lemma chainCoord_injective (ps : List MonoPiece) : Function.Injective (chainCoord ps) := by
  intro x y h
  cases ps with
  | nil =>
      cases x
      cases y
      rfl
  | cons p rest =>
      apply Subtype.ext
      apply Subtype.ext
      exact h

lemma mono_direction_subtype {lo hi : ℝ} (τ : ChartInterval lo hi → ℝ)
    (hτ : MonotoneOnPiece τ) (Q : ChartInterval lo hi → Prop) :
    MonotoneDirectionOn (fun x : {a : ChartInterval lo hi // Q a} => (x.1 : ℝ))
      (fun x : {a : ChartInterval lo hi // Q a} => τ x.1) := by
  rcases hτ with hτi | hτd
  · left
    intro x y hxy
    exact hτi x.1 y.1 hxy
  · right
    intro x y hxy
    exact hτd x.1 y.1 hxy

theorem chain_transport_monotone_direction (ps : List MonoPiece) :
    MonotoneDirectionOn (chainCoord ps) (chainValue ps) := by
  induction ps with
  | nil =>
      left
      intro a b hab
      exfalso
      simp [chainCoord] at hab
  | cons p rest ih =>
      cases rest with
      | nil =>
          change MonotoneDirectionOn
            (fun x : {a : ChartInterval p.lo p.hi // transports p [] a} => (x.1 : ℝ))
            (fun x : {a : ChartInterval p.lo p.hi // transports p [] a} => p.τ x.1)
          exact mono_direction_subtype p.τ p.hmono (transports p [])
      | cons q rest' =>
          have hf : MonotoneDirectionOn (chainCoord (p :: q :: rest'))
              (fun x : ChainDomain (p :: q :: rest') =>
                chainCoord (q :: rest') ⟨⟨p.τ x.1, x.2.choose⟩, x.2.choose_spec⟩) := by
            change MonotoneDirectionOn
              (fun x : {a : ChartInterval p.lo p.hi // transports p (q :: rest') a} =>
                (x.1 : ℝ))
              (fun x : {a : ChartInterval p.lo p.hi // transports p (q :: rest') a} =>
                p.τ x.1)
            exact mono_direction_subtype p.τ p.hmono (transports p (q :: rest'))
          have hcomp := MonotoneDirectionOn.comp_of_coord
            (chainCoord (p :: q :: rest')) (chainCoord (q :: rest'))
            (fun x : ChainDomain (p :: q :: rest') =>
              ⟨⟨p.τ x.1, x.2.choose⟩, x.2.choose_spec⟩)
            (chainValue (q :: rest')) hf ih
          have hpeq : chainValue (p :: q :: rest') =
              fun x : ChainDomain (p :: q :: rest') =>
                chainValue (q :: rest') ⟨⟨p.τ x.1, x.2.choose⟩, x.2.choose_spec⟩ := by
            funext x
            rfl
          rw [hpeq]
          exact hcomp

theorem chain_transport_injective (ps : List MonoPiece) :
    Function.Injective (chainValue ps) := by
  exact MonotoneDirectionOn.injective
    (chain_transport_monotone_direction ps) (chainCoord_injective ps)

end LeanEval.KnotTheory.Quadrisecant
