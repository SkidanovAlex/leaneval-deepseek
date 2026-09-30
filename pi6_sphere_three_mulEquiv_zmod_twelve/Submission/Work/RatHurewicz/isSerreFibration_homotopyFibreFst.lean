import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.hasHLP_pullback
import Submission.Work.StemsB.isSerreFibration_evalOne

/-!
# The projection of the homotopy fibre of `i : C(A,X)` is a Serre fibration

The homotopy fibre of `i : C(A,X)` over `a₀` (`Work.RatHurewicz.homotopyFibre`) is the pullback of
the path–loop fibration `evalOne X (i a₀) : PathSpace X (i a₀) → X` along `i`, so its first
projection `homotopyFibreFst i a₀` is the base change of a fibration.  Base change preserves the
homotopy lifting property (`Work.StemsB.hasHLP_pullback`) and the path–loop fibration has it
(`Work.StemsB.hasHLP_evalOne`); all that is missing is the bookkeeping that identifies the
workspace's two models of the same pullback:

* `bundlePullback X x₀ D s` (`Submission/Work/StemsB/BundlePullback.lean`), the pairs `(d, γ)` with
  `evalOne X x₀ γ = s d`, whose *first* projection is `bundlePullbackFst`; and
* `Pullback (evalOne X x₀) s` (`Submission/Work/StemsB/Fibrations.lean`), the pairs `(γ, d)` with
  `evalOne X x₀ γ = s d`, whose *second* projection `pullbackSnd` is the base change of
  `evalOne X x₀` along `s`.

The two spaces differ only in the order of the coordinates, so they are related by the two mutually
inverse continuous maps `bundlePullbackToPullback` and `pullbackToBundlePullback` of this file, and
`pullbackSnd` composed with the first of them *is* `bundlePullbackFst`.  The second ingredient,
`hasHLP_comp_of_inverse`, records that the homotopy lifting property of a map depends on its total
space only up to a pair of mutually inverse maps: this is the "invariance of `HasHLP` under a
homeomorphism of the total space" whose absence is noted in `Submission/Work/StemsB/STATUS.md`,
proved here in the slightly more general form in which the two inverse identities are hypotheses.

With these two lemmas the theorem is immediate: `homotopyFibreFst i a₀` is (up to the coordinate
swap) the base change of the path–loop fibration, so it inherits the HLP with respect to every cube,
i.e. it is a Serre fibration.

## Main declarations

* `Work.RatHurewicz.hasHLP_comp_of_inverse` — `HasHLP` is invariant under an inverse pair of
  continuous maps on the total space.
* `Work.RatHurewicz.bundlePullbackToPullback`, `pullbackToBundlePullback`, with
  `pullbackSnd_comp_bundlePullbackToPullback`.
* `Work.RatHurewicz.isSerreFibration_homotopyFibreFst` — the target.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.StemsB

/-! ## The homotopy lifting property depends on the total space only up to an inverse pair -/

/-- **The homotopy lifting property is invariant under a change of the total space along mutually
inverse maps.**  If `φ : E' → E` and `ψ : E → E'` are inverse to each other (`ψ ∘ φ = id` and
`φ ∘ ψ = id`) and `p : E → B` has the HLP with respect to `Z`, then so does `p ∘ φ : E' → B`.

Given `f : Z → E'`, `b : Z → B` and a homotopy `H` from `(p ∘ φ) ∘ f` to `b`, apply the HLP of `p`
to `φ ∘ f`, obtaining `G : Z → E` together with a homotopy `HG` from `φ ∘ f` to `G` over `H`; then
`ψ ∘ G` and `ψ ∘ HG` are the required lift and lifted homotopy, the two inverse identities being
used exactly at the two ends. -/
theorem hasHLP_comp_of_inverse {E B E' Z : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace Z] (p : C(E, B)) (φ : C(E', E)) (ψ : C(E, E'))
    (hφψ : ∀ x, ψ (φ x) = x) (hψφ : ∀ y, φ (ψ y) = y) (h : HasHLP p Z) :
    HasHLP (p.comp φ) Z := by
  intro f b H
  obtain ⟨G, HG, hHG⟩ := h (φ.comp f) b H
  -- the lifted homotopy `ψ ∘ HG` starts at `f` (here the identity `ψ ∘ φ = id` is used)
  have hg0 : ∀ z, ψ (HG.toContinuousMap (0, z)) = f z := by
    intro z
    rw [show HG.toContinuousMap (0, z) = φ (f z) from HG.map_zero_left z]
    exact hφψ (f z)
  have hg1 : ∀ z, ψ (HG.toContinuousMap (1, z)) = ψ (G z) := by
    intro z
    rw [show HG.toContinuousMap (1, z) = G z from HG.map_one_left z]
  let H' : f.Homotopy (ψ.comp G) :=
    ContinuousMap.Homotopy.mk (ψ.comp HG.toContinuousMap) hg0 hg1
  refine ⟨ψ.comp G, H', ?_⟩
  ext w
  show p (φ (ψ (HG.toContinuousMap w))) = H.toContinuousMap w
  rw [hψφ] -- here the identity `φ ∘ ψ = id` is used
  exact congrFun (congrArg DFunLike.coe hHG) w

/-! ## The two coordinate orders of the pullback of the path–loop fibration -/

/-- The coordinate swap `(d, γ) ↦ (γ, d)` from the model `bundlePullback` of the pullback of the
path–loop fibration (parameter coordinate first) to the model `Pullback` (parameter coordinate
second).  Its underlying map is just the swap of the two factors of the product. -/
def bundlePullbackToPullback {X : Type} [TopologicalSpace X] (x₀ : X) (D : Type)
    [TopologicalSpace D] (s : C(D, X)) :
    C(bundlePullback X x₀ D s, Pullback (evalOne X x₀) s) where
  toFun p := ⟨(p.1.2, p.1.1), p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)

/-- The inverse coordinate swap `(γ, d) ↦ (d, γ)`. -/
def pullbackToBundlePullback {X : Type} [TopologicalSpace X] (x₀ : X) (D : Type)
    [TopologicalSpace D] (s : C(D, X)) :
    C(Pullback (evalOne X x₀) s, bundlePullback X x₀ D s) where
  toFun q := ⟨(q.1.2, q.1.1), q.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)

/-- The two coordinate swaps are inverse to each other (in the direction
`Pullback → bundlePullback → Pullback`). -/
@[simp]
theorem pullbackToBundlePullback_to {X : Type} [TopologicalSpace X] (x₀ : X) (D : Type)
    [TopologicalSpace D] (s : C(D, X)) (p : bundlePullback X x₀ D s) :
    pullbackToBundlePullback x₀ D s (bundlePullbackToPullback x₀ D s p) = p := rfl

/-- The two coordinate swaps are inverse to each other (in the direction
`bundlePullback → Pullback → bundlePullback`). -/
@[simp]
theorem bundlePullbackToPullback_to {X : Type} [TopologicalSpace X] (x₀ : X) (D : Type)
    [TopologicalSpace D] (s : C(D, X)) (q : Pullback (evalOne X x₀) s) :
    bundlePullbackToPullback x₀ D s (pullbackToBundlePullback x₀ D s q) = q := rfl

/-- Composing the base change `pullbackSnd (evalOne X x₀) s` of the path–loop fibration with the
coordinate swap gives the first projection `bundlePullbackFst` of the homotopy fibre. -/
theorem pullbackSnd_comp_bundlePullbackToPullback {X : Type} [TopologicalSpace X] (x₀ : X)
    (D : Type) [TopologicalSpace D] (s : C(D, X)) :
    (pullbackSnd (evalOne X x₀) s).comp (bundlePullbackToPullback x₀ D s)
      = bundlePullbackFst (x₀ := x₀) D s := by
  ext p
  rfl

/-! ## The theorem -/

/-- The projection `(a, γ) ↦ a` of the homotopy fibre of `i : C(A,X)` (the pullback of the
path–loop fibration `evalOne X x₀ : PathSpace X x₀ → X` along `i`) is a Serre fibration: the
homotopy lifting property is stable under base change. -/
theorem isSerreFibration_homotopyFibreFst {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) :
    Work.StemsB.IsSerreFibration (Work.RatHurewicz.homotopyFibreFst i a₀) := by
  intro n
  -- the base change of the path–loop fibration along `i` has the HLP with respect to `I^n`
  have hHLP : HasHLP (pullbackSnd (evalOne X (i a₀)) i) (Fin n → I) :=
    hasHLP_pullback (evalOne X (i a₀)) i (hasHLP_evalOne X (i a₀) (Fin n → I))
  -- and the coordinate swap carries it to the HLP of the first projection of the homotopy fibre
  have htr : HasHLP (bundlePullbackFst (x₀ := i a₀) A i) (Fin n → I) := by
    have h := hasHLP_comp_of_inverse (p := pullbackSnd (evalOne X (i a₀)) i)
      (φ := bundlePullbackToPullback (i a₀) A i) (ψ := pullbackToBundlePullback (i a₀) A i)
      (fun p => pullbackToBundlePullback_to (i a₀) A i p)
      (fun q => bundlePullbackToPullback_to (i a₀) A i q) hHLP
    rwa [pullbackSnd_comp_bundlePullbackToPullback] at h
  exact htr

end

end Work.RatHurewicz
