import Mathlib
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotV.twCoord_eq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted Klein equations for the T-twist over an arbitrary base field

`Work.MotV.twCoord_eq_univ0` proves, for the base field `K = RatFunc 𝕜` (the `𝔸¹_t` route `S45`),
that the twisted Klein coordinates `twCoord D h` satisfy the twisted Klein quadrics `kleinTw`.
This file proves the same statement for the **generic** T-twist data of
`Submission/Work/MotK/LinkCertGen.lean`: an arbitrary base field `K` and an arbitrary Kummer class
`h ∈ Kˣ` (`h : K`, `h ≠ 0`), with `KbG K = AlgebraicClosure K`, `OmG K D = K̄(E)` and
`twCoordG K D h i = w^{-i}·κ_i/κ_0`, `w = algebraMap (KbG K) (OmG K D) (root5G K h)`, `w^5 = h`.

Route (verbatim the proof of `Work.MotV.twCoord_eq_of_klein`, with `Kb 𝕜` replaced by `KbG K` and
`KbG`-analogues of the three auxiliary facts):

* `D.Good.klein_eq` at `L = KbG K` says `kleinP a b (kleinCoord D (KbG K)) k = 0`;
* `kleinP` is homogeneous of degree two in the coordinates, so writing
  `kleinCoord D (KbG K) = κ_0 • (κ_i/κ_0)` gives `kleinP a b (κ_i/κ_0) k = 0` as well;
* `pow_mul_twCoordG` identifies `(κ_i/κ_0)` with `(fun i => w^i · twCoordG K D h i)`, and the
  substitution identity `Work.MotV.kleinTw_subst` turns the vanishing of `kleinP` into
  `w^{4k} · kleinTw a b (w^5) (twCoordG K D h) k = 0`;
* `w ≠ 0` (because `w^5 = algebraMap K (OmG K D) h ≠ 0`) finishes.

The statement is at `{K : Type}` (universe `0`), like `Work.MotV.twCoord_eq_univ0`: it is exactly
the universe in which `KleinData.Good`'s fields (`∀ (L : Type)`) can be applied to `KbG K`.  See
the discussion in `Submission/Work/MotV/twCoord_eq.lean`.
-/

namespace Work.MotK.TGen

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type} [Field K]

/-! ## Auxiliary facts about the generic T-twist data -/

/-- The defining property of the chosen fifth root `root5G h` of `h` in `KbG K = AlgebraicClosure K`. -/
theorem root5G_spec (h : K) : Work.MotK.root5G K h ^ 5 = algebraMap K (Work.MotK.KbG K) h :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap K (Work.MotK.KbG K) h)
    (by norm_num : 0 < 5))

/-- `w = algebraMap (KbG K) (OmG K D) (root5G K h)` is a fifth root of the Kummer class `h`. -/
theorem wG_pow_five (D : Work.MotV.KleinData K) (h : K) :
    (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ 5
      = algebraMap K (Work.MotK.OmG K D) h := by
  rw [← map_pow, root5G_spec,
    IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)]

/-- `w ≠ 0` for `h ≠ 0` (an `algebraMap` out of a field is injective). -/
theorem wG_ne_zero (D : Work.MotV.KleinData K) {h : K} (hh : h ≠ 0) :
    algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) ≠ 0 := by
  intro h0
  have h5 := wG_pow_five D h
  rw [h0, zero_pow (by norm_num : 5 ≠ 0)] at h5
  exact hh ((algebraMap K (Work.MotK.OmG K D)).injective (by simpa using h5.symm))

/-- The defining identity of the twisted coordinates: `w^i · y_i = κ_i/κ_0`. -/
theorem pow_mul_twCoordG (D : Work.MotV.KleinData K) (h : K) (hh : h ≠ 0) (i : Fin 5) :
    (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ (i : ℕ) *
      Work.MotK.twCoordG K D h i =
      Work.MotV.kleinCoord D (Work.MotK.KbG K) i / Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 := by
  rw [Work.MotK.twCoordG, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (wG_ne_zero D hh), one_pow,
    one_mul]

/-! ## The twisted Klein equations -/

/-- **The twisted Klein quadrics vanish on the twisted Klein coordinates**, over an arbitrary base
field `K` and Kummer class `h ∈ Kˣ`. -/
theorem TwCoordGKleinTw {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) (k : Fin 5) :
    Work.MotV.kleinTw (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
      (Work.MotK.twCoordG K D h) k = 0 := by
  -- The Klein (Pfaffian) equations for the model, evaluated at `L = KbG K`.
  have hkleinK : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b) (Work.MotV.kleinCoord D (Work.MotK.KbG K)) k = 0 :=
    fun k => hD.klein_eq (Work.MotK.KbG K) k
  have hκ0 : Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 ≠ 0 :=
    hD.coord0_ne (Work.MotK.KbG K)
  -- `w = algebraMap (KbG K) (OmG K D) (root5G K h)` is a fifth root of `h`, hence nonzero.
  let w : Work.MotK.OmG K D :=
    algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)
  have hw5 : w ^ 5 = algebraMap K (Work.MotK.OmG K D) h := wG_pow_five D h
  have hwnz : w ≠ 0 := wG_ne_zero D hh
  -- The defining identity of the twisted coordinates: `w^i * y_i = κ_i / κ_0`.
  have hpoint : ∀ i : Fin 5, w ^ (i : ℕ) * Work.MotK.twCoordG K D h i
      = Work.MotV.kleinCoord D (Work.MotK.KbG K) i /
        Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 :=
    fun i => pow_mul_twCoordG D h hh i
  -- `κ = κ 0 • (κ_i / κ_0)`, so homogeneity of degree two in the coordinates shows that the
  -- Klein Pfaffians vanish on the `κ_i / κ_0` as well.
  have hsplit : Work.MotV.kleinCoord D (Work.MotK.KbG K) =
      fun i => Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 *
        (Work.MotV.kleinCoord D (Work.MotK.KbG K) i /
          Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) := by
    funext i
    exact (mul_div_cancel₀ (Work.MotV.kleinCoord D (Work.MotK.KbG K) i) hκ0).symm
  have hhom : ∀ (c : Work.MotK.OmG K D) (z : Fin 5 → Work.MotK.OmG K D),
      Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
        (algebraMap K (Work.MotK.OmG K D) D.b) (fun i => c * z i) k
        = c ^ 2 * Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
          (algebraMap K (Work.MotK.OmG K D) D.b) z k :=
    fun c z => Work.MotV.kleinP_smul _ _ c z k
  have hz : Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b)
      (fun i => Work.MotV.kleinCoord D (Work.MotK.KbG K) i /
        Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) k = 0 := by
    have hkleinK' := hkleinK k
    rw [hsplit, hhom] at hkleinK'
    exact (mul_eq_zero.mp hkleinK').resolve_left (pow_ne_zero 2 hκ0)
  -- `kleinTw_subst` turns this into the twisted Klein equation.
  have hfun : (fun i : Fin 5 => w ^ (i : ℕ) * Work.MotK.twCoordG K D h i)
      = (fun i => Work.MotV.kleinCoord D (Work.MotK.KbG K) i /
          Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) :=
    funext hpoint
  have hsub := Work.MotV.kleinTw_subst (algebraMap K (Work.MotK.OmG K D) D.a)
    (algebraMap K (Work.MotK.OmG K D) D.b) w (Work.MotK.twCoordG K D h) k
  rw [hfun, hz] at hsub
  have hfin : Work.MotV.kleinTw (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b) (w ^ 5) (Work.MotK.twCoordG K D h) k = 0 :=
    (mul_eq_zero.mp hsub.symm).resolve_left (pow_ne_zero _ hwnz)
  rw [hw5] at hfin
  exact hfin

end Work.MotK.TGen
