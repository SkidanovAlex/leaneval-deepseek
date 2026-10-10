import Mathlib
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

set_option linter.style.haveILetI false

/-
The twist field `Work.MotK.twistFieldTG K D h` depends only on the *Kummer class* of `h ∈ Kˣ/Kˣ⁵`:
multiplying `h` by a fifth power gives a `K`-isomorphic field.  This is the sub-piece of node K6
(`Work.MotK.TwCensus.ZTwist`) that handles the case where `h²` is itself a fifth power (e.g.
`h = t⁵`, or `h = 32` in `ℚ`), where the twist is *trivial* and one must know that
`twistFieldTG K D (h²)` is still `K`-isomorphic to the untwisted field `twistFieldTG K D 1`.  It
also shows that no extra hypothesis (`∀ s, s⁵ ≠ h²`) is needed in K6.

Route (two reviewers checked the mathematics; note the direction, the maps go *onto* the `h`-field):
* `w  := algebraMap (KbG K) (OmG K D) (root5G K h)`, `w' := ⋯ (root5G K (h * s ^ 5))`, `s̄ := ⋯ s`;
  both `w⁵ = algebraMap h` and `w'⁵ = algebraMap (h * s ^ 5)` (`Work.MotK.TGen.wG_pow_five`), so
  `u := w' / (w * s̄)` satisfies `u ^ 5 = 1` (`div_pow`, `mul_pow`, `map_pow`, `mul_assoc`,
  `div_eq_mul_inv`).
* If `u = 1`, then `twCoordG K D (h*s^5) i = (s̄^{-i}) * twCoordG K D h i` with `s̄^{-i} ∈ K`, so the
  two intermediate fields are *equal*.
* Otherwise `u` is a primitive fifth root of unity (5 is prime: `orderOf_eq_prime`), and
  `Work.MotV.KleinData.Good.T_diag` with `L = KbG K` and `ζ = u⁻¹` gives a `KbG K`-algebra
  automorphism `σ` of `OmG K D` with `σ (κ_i/κ_0) = u^{-i} (κ_i/κ_0)`.  Then
  `σ (twCoordG K D h i) = u^i * twCoordG K D (h * s ^ 5) i` (up to the constant `s⁻ⁱ`), i.e.
  `IntermediateField.map σ (twistFieldTG K D h) = twistFieldTG K D (h * s ^ 5)`; `σ` is
  `KbG K`-linear hence `K`-linear, giving the `K`-algebra isomorphism (use
  `IntermediateField.map`/`AlgEquiv.restrictScalars`, cf. `Work.MotV.nonempty_algEquiv_restrictScalars`).
  (Equivalently work with `σ⁻¹`, which maps the `(h s⁵)`-coordinates to `K`-multiples of the
  `h`-coordinates; the conclusion is symmetric.)

It is *not* claimed that the fields are equal as subfields of `OmG K D` (they are not in general:
their coordinate systems differ by the `K̄`-linear automorphism `σ`).  No hypothesis
`ringChar K ≠ 5` is needed.
-/
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## The Kummer cocycle `u = w'/(w·s̄)` and the twisted coordinates

All the bookkeeping of the proof lives in this section.  With `w = wG h`, `w' = wG (h * s^5)` the
chosen fifth roots and `u = algebraMap (KbG K) (OmG K D) (root5G (h*s^5) / (root5G h * s))`:

* `u ^ 5 = 1` (`kummerCocycle_pow`, `UOm_pow`);
* `twCoordG K D (h*s^5) i = u^{-i} * (s̄^{-i}) * twCoordG K D h i`, the scalar `s̄^{-i} = kummerScalar`
  lying in the image of `K` (`twCoordG_mul_pow`);
* the diagonal automorphism of `T_diag` at `ζ = u^{-1}` acts on the `h`-coordinates by `u^{-i}`
  (`tau_twCoordG`).
-/

/-- The Kummer cocycle `u = root5G(h·s⁵)/(root5G(h)·s) ∈ KbG K`: a fifth root of unity. -/
noncomputable def kummerCocycle (K : Type) [Field K] (h s : K) : Work.MotK.KbG K :=
  Work.MotK.root5G K (h * s ^ 5) / (Work.MotK.root5G K h * algebraMap K (Work.MotK.KbG K) s)

/-- The image of the Kummer cocycle in `OmG K D`; `T_diag` fixes it (it is a `KbG K`-constant). -/
noncomputable def UOm (K : Type) [Field K] (D : Work.MotV.KleinData K) (h s : K) :
    Work.MotK.OmG K D :=
  algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (kummerCocycle K h s)

/-- The `K`-scalar `(algebraMap K (OmG K D) s)⁻¹ ^ n` by which the `n`-th twisted coordinate of
`h * s⁵` differs from the `n`-th twisted coordinate of `h`. -/
noncomputable def kummerScalar (K : Type) [Field K] (D : Work.MotV.KleinData K) (s : K) (n : ℕ) :
    Work.MotK.OmG K D :=
  (algebraMap K (Work.MotK.OmG K D) s)⁻¹ ^ n

theorem kummerCocycle_pow {K : Type} [Field K] {h s : K} (hh : h ≠ 0) (hs : s ≠ 0) :
    kummerCocycle K h s ^ 5 = 1 := by
  have h1 : algebraMap K (Work.MotK.KbG K) h ≠ 0 := fun h0 =>
    hh ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  have h2 : algebraMap K (Work.MotK.KbG K) s ≠ 0 := fun h0 =>
    hs ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  have hnum : Work.MotK.root5G K (h * s ^ 5) ^ 5 =
      algebraMap K (Work.MotK.KbG K) h * algebraMap K (Work.MotK.KbG K) s ^ 5 := by
    rw [Work.MotK.TGen.root5G_spec, map_mul, map_pow]
  have hden : (Work.MotK.root5G K h * algebraMap K (Work.MotK.KbG K) s) ^ 5 =
      algebraMap K (Work.MotK.KbG K) h * algebraMap K (Work.MotK.KbG K) s ^ 5 := by
    rw [mul_pow, Work.MotK.TGen.root5G_spec]
  rw [kummerCocycle, div_pow, hden, hnum, div_self (mul_ne_zero h1 (pow_ne_zero 5 h2))]

theorem UOm_pow {K : Type} [Field K] (D : Work.MotV.KleinData K) {h s : K} (hh : h ≠ 0)
    (hs : s ≠ 0) : UOm K D h s ^ 5 = 1 := by
  rw [UOm, ← map_pow, kummerCocycle_pow hh hs, map_one]

/-- `UOm K D h s = w' * (w * s̄)⁻¹`: the fifth root of `h * s⁵` is `w·s̄` up to the cocycle. -/
theorem UOm_eq {K : Type} [Field K] (D : Work.MotV.KleinData K) (h s : K) :
    UOm K D h s =
      algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K (h * s ^ 5)) *
        (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) *
          algebraMap K (Work.MotK.OmG K D) s)⁻¹ := by
  rw [UOm, kummerCocycle, map_div₀, map_mul,
    ← IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D), div_eq_mul_inv]

/-- **The two coordinate systems differ by the cocycle and a `K`-scalar.** -/
theorem twCoordG_mul_pow {K : Type} [Field K] (D : Work.MotV.KleinData K) (h s : K)
    (hh : h ≠ 0) (hs : s ≠ 0) (i : Fin 5) :
    Work.MotK.twCoordG K D (h * s ^ 5) i =
      (UOm K D h s)⁻¹ ^ (i : ℕ) * kummerScalar K D s (i : ℕ) * Work.MotK.twCoordG K D h i := by
  have hS : algebraMap K (Work.MotK.OmG K D) s ≠ 0 := fun h0 =>
    hs ((algebraMap K (Work.MotK.OmG K D)).injective (by rw [h0, map_zero]))
  have hWh : algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) ≠ 0 :=
    Work.MotK.TGen.wG_ne_zero D hh
  have hW' : algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K (h * s ^ 5)) =
      UOm K D h s *
        (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) *
          algebraMap K (Work.MotK.OmG K D) s) := by
    rw [UOm_eq, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hWh hS), mul_one]
  simp only [Work.MotK.twCoordG]
  rw [hW']
  have hcoef : (UOm K D h s *
        (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) *
          algebraMap K (Work.MotK.OmG K D) s))⁻¹ ^ (i : ℕ) =
      (UOm K D h s)⁻¹ ^ (i:ℕ) * (algebraMap K (Work.MotK.OmG K D) s)⁻¹ ^ (i:ℕ) *
        (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h))⁻¹ ^ (i:ℕ) := by
    rw [mul_inv, mul_pow, mul_inv_rev, mul_pow]; ring
  rw [hcoef, kummerScalar]
  first | refl_ring1 | ring

/-! ## The diagonal automorphism of `T_diag` -/

/-- **The Klein scaling automorphism** (`T_diag` with the identity for `c = 1`): for every fifth
root of unity `c` of `L` there is an `L`-algebra automorphism of `L(E)` multiplying the Klein
ratios `κ_i/κ_0` by `c^i`. -/
theorem exists_kleinScaling {K L : Type} [Field K] [Field L] [Algebra K L]
    (D : Work.MotV.KleinData K) (hD : D.Good) (c : L) (hc : c ^ 5 = 1) :
    ∃ τ : Affine.FunctionField (D.E.baseChange L) ≃ₐ[L] Affine.FunctionField (D.E.baseChange L),
      ∀ i : Fin 5, τ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) =
        (algebraMap L (Affine.FunctionField (D.E.baseChange L)) c) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) := by
  rcases eq_or_ne c 1 with rfl | hc1
  · exact ⟨1, fun i => by simp⟩
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hprim : IsPrimitiveRoot c 5 := by
      rw [IsPrimitiveRoot.iff_orderOf]
      exact orderOf_eq_prime hc hc1
    exact hD.T_diag L c hprim

/-- **The diagonal automorphism at `ζ = u⁻¹`**, acting on the `h`-twisted coordinates by `u^{-i}`. -/
theorem tau_twCoordG {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h s : K)
    (hh : h ≠ 0) (hs : s ≠ 0) :
    ∃ τ : Work.MotK.OmG K D ≃ₐ[K] Work.MotK.OmG K D,
      ∀ i : Fin 5, τ (Work.MotK.twCoordG K D h i) =
        (UOm K D h s)⁻¹ ^ (i:ℕ) * Work.MotK.twCoordG K D h i := by
  have hc5 : (kummerCocycle K h s)⁻¹ ^ 5 = 1 := by
    rw [inv_pow, kummerCocycle_pow hh hs, inv_one]
  obtain ⟨τL, hτL⟩ := exists_kleinScaling D hD (kummerCocycle K h s)⁻¹ hc5
  refine ⟨AlgEquiv.restrictScalars K τL, fun i => ?_⟩
  have hW : τL (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) =
      algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) :=
    τL.commutes (Work.MotK.root5G K h)
  have hU : (UOm K D h s)⁻¹ = algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D)
      ((kummerCocycle K h s)⁻¹) := by rw [UOm, map_inv₀]
  show τL (Work.MotK.twCoordG K D h i) = (UOm K D h s)⁻¹ ^ (i:ℕ) * Work.MotK.twCoordG K D h i
  simp only [Work.MotK.twCoordG]
  rw [map_mul, map_pow, map_inv₀, hW, hτL i, hU]
  first | refl_ring1 | ring

/-! ## Membership and invariance of the `K`-scalar -/

theorem kummerScalar_mem {K : Type} [Field K] (D : Work.MotV.KleinData K) (s : K)
    (S : IntermediateField K (Work.MotK.OmG K D)) (n : ℕ) : kummerScalar K D s n ∈ S := by
  have hpow : (algebraMap K (Work.MotK.OmG K D) s)⁻¹ ^ n ∈ S := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact S.mul_mem ih (S.inv_mem (S.algebraMap_mem s))
  exact hpow

theorem pow_mem_nat {K : Type} [Field K] (D : Work.MotV.KleinData K) (s : K)
    (S : IntermediateField K (Work.MotK.OmG K D)) (n : ℕ) :
    algebraMap K (Work.MotK.OmG K D) s ^ n ∈ S := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact S.mul_mem ih (S.algebraMap_mem s)

theorem tau_kummerScalar {K : Type} [Field K] (D : Work.MotV.KleinData K) (s : K)
    (τ : Work.MotK.OmG K D ≃ₐ[K] Work.MotK.OmG K D) (n : ℕ) :
    τ (kummerScalar K D s n) = kummerScalar K D s n := by
  rw [kummerScalar, map_pow, map_inv₀, τ.commutes]

/-- `s̄^n * (a * s̄^{-n} * x) = a * x`: the `K`-scalar in `twCoordG_mul_pow` cancels against its
inverse, so `T_diag`'s automorphism sends the `(h*s⁵)`-coordinates onto `K`-multiples of the
`h`-coordinates. -/
theorem kummerScalar_mul_cancel {K : Type} [Field K] (D : Work.MotV.KleinData K) {s : K}
    (hs : s ≠ 0) (n : ℕ) (a x : Work.MotK.OmG K D) :
    algebraMap K (Work.MotK.OmG K D) s ^ n * (a * kummerScalar K D s n * x) = a * x := by
  have hSb_ne : algebraMap K (Work.MotK.OmG K D) s ≠ 0 := fun h0 =>
    hs ((algebraMap K (Work.MotK.OmG K D)).injective (by rw [h0, map_zero]))
  rw [kummerScalar]
  calc algebraMap K (Work.MotK.OmG K D) s ^ n *
        (a * (algebraMap K (Work.MotK.OmG K D) s)⁻¹ ^ n * x)
      = (algebraMap K (Work.MotK.OmG K D) s ^ n * (algebraMap K (Work.MotK.OmG K D) s)⁻¹ ^ n) *
          (a * x) := by ring
    _ = 1 * (a * x) := by rw [← mul_pow, mul_inv_cancel₀ hSb_ne, one_pow]
    _ = a * x := one_mul _

/-! ## The identification of the two twist fields -/

/-- **`T_diag` identifies the two twist fields.**  If `τ` acts on the `h`-coordinates by the
cocycle `u^{-i}` and the `(h s⁵)`-coordinates differ from the `h`-coordinates by `u^{-i}·s̄^{-i}`,
then `τ` maps the `h`-twist field *onto* the `(h s⁵)`-twist field. -/
theorem map_twistFieldTG_eq {K : Type} [Field K] (D : Work.MotV.KleinData K) (h s : K) (hs : s ≠ 0)
    (τ : Work.MotK.OmG K D ≃ₐ[K] Work.MotK.OmG K D)
    (hτ : ∀ i : Fin 5, τ (Work.MotK.twCoordG K D h i) =
      (UOm K D h s)⁻¹ ^ (i:ℕ) * Work.MotK.twCoordG K D h i)
    (hy' : ∀ i : Fin 5, Work.MotK.twCoordG K D (h * s ^ 5) i =
      (UOm K D h s)⁻¹ ^ (i:ℕ) * kummerScalar K D s (i:ℕ) * Work.MotK.twCoordG K D h i) :
    (Work.MotK.twistFieldTG K D h).map τ.toAlgHom = Work.MotK.twistFieldTG K D (h * s ^ 5) := by
  apply le_antisymm
  · rw [IntermediateField.map_le_iff_le_comap, Work.MotK.twistFieldTG,
      IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    change τ.toAlgHom (Work.MotK.twCoordG K D h i) ∈ Work.MotK.twistFieldTG K D (h * s ^ 5)
    have hkey : τ.toAlgHom (Work.MotK.twCoordG K D h i) =
        algebraMap K (Work.MotK.OmG K D) s ^ (i:ℕ) * Work.MotK.twCoordG K D (h * s^5) i := by
      rw [AlgEquiv.toAlgHom_apply, hτ i, hy' i,
        kummerScalar_mul_cancel D hs (i:ℕ) ((UOm K D h s)⁻¹ ^ (i:ℕ)) (Work.MotK.twCoordG K D h i)]
    rw [hkey]
    exact IntermediateField.mul_mem _ (pow_mem_nat D s _ (i:ℕ))
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · rw [Work.MotK.twistFieldTG, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    rw [IntermediateField.coe_map, Set.mem_image]
    refine ⟨kummerScalar K D s (i:ℕ) * Work.MotK.twCoordG K D h i, ?_, ?_⟩
    · exact IntermediateField.mul_mem _ (kummerScalar_mem D s _ (i:ℕ))
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · rw [map_mul, AlgEquiv.toAlgHom_apply, tau_kummerScalar, AlgEquiv.toAlgHom_apply, hτ i, hy' i]
      first | refl_ring1 | ring

/-! ## The Kummer invariance -/

/-- **The twist field depends only on the Kummer class**: replacing `h` by `h * s⁵` gives a
`K`-isomorphic twist field. -/
theorem KummerInvariance (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h s : K) (hh : h ≠ 0) (hs : s ≠ 0) :
    Nonempty (↥(Work.MotK.twistFieldTG K D (h * s ^ 5)) ≃ₐ[K]
      ↥(Work.MotK.twistFieldTG K D h)) := by
  obtain ⟨τ, hτ⟩ := tau_twCoordG D hD h s hh hs
  have hmap := map_twistFieldTG_eq D h s hs τ hτ (twCoordG_mul_pow D h s hh hs)
  exact ⟨(IntermediateField.equivMap (Work.MotK.twistFieldTG K D h) τ.toAlgHom).trans
    (IntermediateField.equivOfEq hmap) |>.symm⟩

end Work.MotK.TwCensus
