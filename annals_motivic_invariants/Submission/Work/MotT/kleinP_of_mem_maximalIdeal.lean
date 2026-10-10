import Mathlib
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **`kleinP` is natural in the coefficient ring.**

The five Klein quadrics are polynomials with integer coefficients in the coordinates, so any
ring homomorphism `f : R →+* S` commutes with them: applying `f` to `kleinP a b x k` gives the
same quadric evaluated at `f a`, `f b` and the image coordinates `f ∘ x`. -/
theorem map_kleinP_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R)
    (x : Fin 5 → R) (k : Fin 5) :
    f (Work.MotK.kleinP a b x k) = Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, map_add, map_sub, map_mul, map_pow,
      map_neg]

/-- The canonical injection of the local ring at infinity into `L(E)` sends the image of a
constant of `L` to that constant. -/
lemma val_algebraMap {L : Type} [Field L] (E : WeierstrassCurve L) (c : L) :
    (Subalgebra.val (Work.MotC2.infPlace E)).toRingHom
      (algebraMap L ↥(Work.MotC2.infPlace E) c) = algebraMap L (Work.MotC2.Func E) c := rfl

/-- **Reduction of the Klein quadrics at the rational place at infinity.**

Let `E/L` be a Weierstrass curve over a field, and let `a b : L`.  Suppose `X i ∈ ↥(infPlace E)`
(for `i : Fin 5`) are elements of the local ring at infinity that agree modulo its maximal ideal
with the constants `y i : L`, i.e. `X i - algebraMap L ↥(infPlace E) (y i) ∈ 𝔪`; and suppose the
images of the `X i` in `L(E)` satisfy the five Klein quadrics with coefficients `a, b` (this is the
content of `KleinData.Good.klein_eq`).  Then `y` is a zero of the five Klein quadrics over `L`:
`kleinP a b y k = 0` for `k = 0,…,4`.

Route: apply `kleinP`-compatibility of ring homomorphisms (proved as a local helper by `fin_cases k`
on the five explicit forms `kleinP0 … kleinP4`, using the primed component lemmas `kleinP_zero'` …
`kleinP_four'`) to the quotient map `Ideal.Quotient.mk 𝔪` and to the composite
`φ = mk ∘ algebraMap L ↥(infPlace E)`, and use `hX` to identify `mk (X i)` with `φ (y i)`; the
injectivity half of `Work.MotC2.InfPlaceCore.residue_field`, together with
`IsLocalRing.mem_maximalIdeal` (units are not in the maximal ideal), converts
`φ (kleinP a b y k) = 0` into `kleinP a b y k = 0`.  Note that `h0` is stated in `Func E`,
so first transfer it to `↥(infPlace E)` by injectivity of the coercion and ring-hom compatibility. -/
theorem kleinP_of_mem_maximalIdeal {L : Type} [Field L] (E : WeierstrassCurve L) (a b : L)
    (y : Fin 5 → L) (X : Fin 5 → ↥(Work.MotC2.infPlace E))
    (hX : ∀ i, X i - algebraMap L ↥(Work.MotC2.infPlace E) (y i) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E))
    (h0 : ∀ k, Work.MotK.kleinP (algebraMap L (Work.MotC2.Func E) a)
      (algebraMap L (Work.MotC2.Func E) b) (fun i => (X i : Work.MotC2.Func E)) k = 0) :
    ∀ k, Work.MotK.kleinP a b y k = 0 := by
  intro k
  -- Step 1: transfer `h0` from `Func E = L(E)` to the local ring at infinity, using that the
  -- coercion `↥(infPlace E) → L(E)` is an injective ring homomorphism.
  have hR : Work.MotK.kleinP (algebraMap L ↥(Work.MotC2.infPlace E) a)
      (algebraMap L ↥(Work.MotC2.infPlace E) b) X k = 0 := by
    apply Subtype.ext
    rw [show ((0 : ↥(Work.MotC2.infPlace E)) : Work.MotC2.Func E) = 0 from rfl]
    change (Subalgebra.val (Work.MotC2.infPlace E)).toRingHom
      (Work.MotK.kleinP (algebraMap L ↥(Work.MotC2.infPlace E) a)
        (algebraMap L ↥(Work.MotC2.infPlace E) b) X k) = 0
    rw [map_kleinP_apply (Subalgebra.val (Work.MotC2.infPlace E)).toRingHom
        (algebraMap L ↥(Work.MotC2.infPlace E) a) (algebraMap L ↥(Work.MotC2.infPlace E) b) X k]
    rw [val_algebraMap, val_algebraMap]
    exact h0 k
  -- Step 2: reduce the Klein identity modulo the maximal ideal of the local ring at infinity.
  have hq : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E)))
      (Work.MotK.kleinP (algebraMap L ↥(Work.MotC2.infPlace E) a)
        (algebraMap L ↥(Work.MotC2.infPlace E) b) X k) = 0 := by
    rw [hR, map_zero]
  rw [map_kleinP_apply (Ideal.Quotient.mk _)
      (algebraMap L ↥(Work.MotC2.infPlace E) a) (algebraMap L ↥(Work.MotC2.infPlace E) b) X k] at hq
  -- Step 3: the residue class of `X i` is the residue class of the constant `y i`, by `hX`.
  have hXi : ∀ i, (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E))) (X i) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E)))
        (algebraMap L ↥(Work.MotC2.infPlace E) (y i)) := by
    intro i
    exact Ideal.Quotient.eq.mpr (hX i)
  simp only [hXi] at hq
  -- Step 4: transport the resulting identity of `L`-constants along `algebraMap L ↥(infPlace E)`
  -- and `Ideal.Quotient.mk 𝔪`, and use `kleinP`-compatibility once more.
  have h1 : (algebraMap L ↥(Work.MotC2.infPlace E)) (Work.MotK.kleinP a b y k)
      = Work.MotK.kleinP ((algebraMap L ↥(Work.MotC2.infPlace E)) a)
          ((algebraMap L ↥(Work.MotC2.infPlace E)) b)
          (fun i => (algebraMap L ↥(Work.MotC2.infPlace E)) (y i)) k :=
    map_kleinP_apply _ a b y k
  have h2 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E)))
      (Work.MotK.kleinP (algebraMap L ↥(Work.MotC2.infPlace E) a)
        (algebraMap L ↥(Work.MotC2.infPlace E) b)
        (fun i => (algebraMap L ↥(Work.MotC2.infPlace E)) (y i)) k) = 0 := by
    rw [map_kleinP_apply (Ideal.Quotient.mk _) (algebraMap L ↥(Work.MotC2.infPlace E) a)
      (algebraMap L ↥(Work.MotC2.infPlace E) b) (fun i => (algebraMap L ↥(Work.MotC2.infPlace E)) (y i)) k]
    exact hq
  have hz : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E)))
      ((algebraMap L ↥(Work.MotC2.infPlace E)) (Work.MotK.kleinP a b y k)) = 0 :=
    (congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E))) h1).trans h2
  -- Step 5: the residue field of the local ring at infinity is `L`, via `c ↦ mk (algebraMap c)`.
  exact (Work.MotC2.InfPlaceCore.residue_field E).1 (by
    simp only [hz, map_zero])

end Work.MotT
