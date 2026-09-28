import Mathlib
import Submission.Work.StemsB.Fibrations

/-!
# The homotopy lifting property is inherited by retracts of the test space

The homotopy lifting property `Work.StemsB.HasHLP q Z` is *contravariant in the test space* in the
following sense: if `Z` is a retract of `W` — that is, if `i : Z → W` has a left inverse
`r : W → Z`, `r ∘ i = id` — then a map having the HLP with respect to `W` has it with respect to
`Z` as well.

The proof is the classical one: given a lifting problem `(f, b, H)` in `Z`, push all the data
forward along the retraction `r : W → Z` (`f ↦ f ∘ r`, `b ↦ b ∘ r`, `H ↦ H ∘ (id × r)`), solve it
by the HLP with respect to `W`, and pull the solution back along the section `i : Z → W`
(`G ↦ G ∘ i`, `HG ↦ HG ∘ (id × i)`).  The identity `r ∘ i = id` is exactly what makes the
pullback solve the original problem: it is used once to see that the pulled-back lifted homotopy
starts at `f`, and once to see that it covers `H`.

## Main declaration

* `Work.RatHurewicz.hasHLP_of_retract` — `HasHLP q W → HasHLP q Z` for `Z` a retract of `W`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **The homotopy lifting property passes to retracts of the test space.**  If `q : E → B` has the
HLP with respect to `W`, and `i : Z → W` is a section of `r : W → Z` (so that `Z` is a retract of
`W`), then `q` has the HLP with respect to `Z` as well.

Given `f : Z → E`, `b : Z → B` and a homotopy `H` from `q ∘ f` to `b`, the same data composed with
`r` form a lifting problem in `W`; the HLP of `q` with respect to `W` supplies a lift `G : W → E`
and a lifted homotopy `HG` of `f ∘ r` over `H ∘ (id × r)`.  The required lift and lifted homotopy
for the original problem are `G ∘ i` and `HG ∘ (id × i)`: the identity `r ∘ i = id` shows that
`HG ∘ (id × i)` starts at `f` and that `q ∘ HG ∘ (id × i) = H`. -/
theorem hasHLP_of_retract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    (q : C(E, B)) (i : C(Z, W)) (r : C(W, Z)) (hri : r.comp i = ContinuousMap.id Z)
    (hW : Work.StemsB.HasHLP q W) : Work.StemsB.HasHLP q Z := by
  intro f b H
  -- the identity `r ∘ i = id` in pointwise form
  have hri' : ∀ z : Z, r (i z) = z := fun z => congrFun (congrArg DFunLike.coe hri) z
  -- the homotopy pushed forward along the retraction `r : W → Z`
  have hHr0 : ∀ w : W,
      (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap r)) (0, w)
        = (q.comp (f.comp r)) w := by
    intro w
    show H (0, r w) = q (f (r w))
    rw [H.apply_zero]
    rfl
  have hHr1 : ∀ w : W,
      (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap r)) (1, w)
        = (b.comp r) w := by
    intro w
    show H (1, r w) = b (r w)
    rw [H.apply_one]
  let Hr : (q.comp (f.comp r)).Homotopy (b.comp r) :=
    ContinuousMap.Homotopy.mk
      (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap r)) hHr0 hHr1
  -- the pointwise description of the pushed-forward homotopy
  have hHr_apply : ∀ (t : I) (w : W), Hr.toContinuousMap (t, w) = H (t, r w) :=
    fun t w => rfl
  -- solve the pushed-forward problem using the HLP with respect to `W`
  obtain ⟨G, HG, hHG⟩ := hW (f.comp r) (b.comp r) Hr
  -- the covering relation, pointwise
  have hHG' : ∀ (t : I) (w : W), q (HG.toContinuousMap (t, w)) = H (t, r w) := by
    intro t w
    have h := congrFun (congrArg DFunLike.coe hHG) (t, w)
    simp only [ContinuousMap.comp_apply] at h
    rw [h]
    exact hHr_apply t w
  -- the solution pulled back along the section `i : Z → W`
  have h0 : ∀ z : Z,
      (HG.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) (0, z) = f z := by
    intro z
    show HG (0, i z) = f z
    rw [HG.apply_zero]
    show f (r (i z)) = f z
    rw [hri' z]
  have h1 : ∀ z : Z,
      (HG.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) (1, z) = (G.comp i) z := by
    intro z
    show HG (1, i z) = G (i z)
    rw [HG.apply_one]
  refine ⟨G.comp i,
    ContinuousMap.Homotopy.mk
      (HG.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) h0 h1, ?_⟩
  ext w
  show q (HG.toContinuousMap (w.1, i w.2)) = H w
  rw [hHG' w.1 (i w.2), hri' w.2]

end

end Work.RatHurewicz
