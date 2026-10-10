import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.PointlessTwist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessTwist.GaloisFixed

/-! ## The two halves of the descent argument

Both directions of `galMap_eq_self_iff` need the `L`-points of the base change `E_L = E ⁄ L`
rewritten through `WeierstrassCurve.Affine.Point.map_some`; the ingredients are the Galois
fixed-field dictionary for the coordinates and the base-change dictionary for the Weierstrass
equation. -/

/-- **Galois descent for coordinates.**  An element of `L` fixed by the generator `σ` of the
cyclic Galois group of `L/𝕜` is the image of an element of `𝕜`.

`σ` generates `Gal(L/𝕜)` (`CyclicExtension.gen_generator`), so `σ z = z` implies that *every*
Galois automorphism fixes `z`; the Galois fixed field of `L/𝕜` is `𝕜`
(`IsGalois.mem_range_algebraMap_iff_fixed`). -/
lemma exists_algebraMap_eq_of_gen_fixed {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {z : D.ext.L} (hz : D.ext.gen z = z) :
    ∃ a : 𝕜, algebraMap 𝕜 D.ext.L a = z := by
  have hpow : ∀ k : ℕ, (D.ext.gen ^ k) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hz, ih]
  have hfix : ∀ f : D.ext.L ≃ₐ[𝕜] D.ext.L, f z = z := by
    intro f
    obtain ⟨k, hk⟩ := D.ext.gen_generator f
    rw [hk]
    exact hpow k
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := 𝕜) (E := D.ext.L) z).mpr hfix
  exact ⟨a, ha⟩

/-- **Galois descent for the Weierstrass equation.**  An affine point of `E_L` whose coordinates
are both base changes of elements of `𝕜` comes from an affine point of `E`.

This is `WeierstrassCurve.Affine.baseChange_nonsingular`, read in the descending direction: the
`𝕜`-algebra map `𝕜 → L` is injective, so the Weierstrass equation (and the nonvanishing of a
partial derivative) can be pulled back along it. -/
lemma nonsingular_baseChange_of_algebraMap {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {a b : 𝕜}
    (h : WeierstrassCurve.Affine.Nonsingular (D.E.baseChange D.ext.L)
      (algebraMap 𝕜 D.ext.L a) (algebraMap 𝕜 D.ext.L b)) :
    WeierstrassCurve.Affine.Nonsingular (D.E.baseChange 𝕜) a b := by
  have h2 : WeierstrassCurve.Affine.Nonsingular (D.E.baseChange D.ext.L)
      ((Algebra.ofId 𝕜 D.ext.L) a) ((Algebra.ofId 𝕜 D.ext.L) b) := by
    simpa only [Algebra.ofId_apply] using h
  have hinj : Function.Injective ⇑(Algebra.ofId 𝕜 D.ext.L) := by
    intro p q hpq
    exact (algebraMap 𝕜 D.ext.L).injective (by simpa only [Algebra.ofId_apply] using hpq)
  exact (WeierstrassCurve.Affine.baseChange_nonsingular D.E
    (f := Algebra.ofId 𝕜 D.ext.L) hinj a b).mp h2

/-- **Galois descent in degree `0` for `E(L)`.**  A point `R` of the twist group `E(L)` is fixed by
the generator `σ` of `Gal(L/𝕜)` if and only if it is the base change of a `𝕜`-rational point of
`E`.  This is the `H⁰` part of the descent dictionary of the twist: `E(L)^σ = E(𝕜)`.

Route: `⇐` is `WeierstrassCurve.Affine.Point.map_baseChange`.  `⇒`: `σ R = R` forces the two
coordinates of `R` to be `σ`-fixed (`Point.map_some` and `Point.some.injEq`); since
`D.ext.gen` generates `Gal(L/𝕜)` (`Work.TorsorExistence.CyclicExtension.zpowers_gen`), a
`σ`-fixed element lies in `IntermediateField.fixedField (Subgroup.zpowers D.ext.gen)`, i.e. in
`IntermediateField.fixedField ⊤`, which is `⊥` by `IsGalois.fixedField_top` (`[FiniteDimensional 𝕜 L]`
and `[IsGalois 𝕜 L]` are instances of `CyclicExtension`); `x ∈ (⊥ : IntermediateField 𝕜 L)` means
`x` is in the range of `algebraMap 𝕜 L` (`IntermediateField.mem_bot`), and the Weierstrass equation
descends by injectivity of `algebraMap` (cf. `WeierstrassCurve.Affine.baseChange_equation`).
The `zero` case is `baseChange 0 = 0` (take `Q = 0`). -/
theorem galMap_eq_self_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (R : D.LPoints) :
    D.galMap R = R ↔ ∃ Q : WeierstrassCurve.Affine.Point D.E,
      WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L Q = R := by
  constructor
  · intro h
    rcases R with _ | ⟨x, y, hns⟩
    · exact ⟨0, WeierstrassCurve.Affine.Point.map_zero (W' := D.E)
        (f := Algebra.ofId 𝕜 D.ext.L)⟩
    · -- `σ` fixes an affine point only if it fixes both coordinates
      have key := h
      change (WeierstrassCurve.Affine.Point.map (W' := D.E)
          (f := (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L)))
          (WeierstrassCurve.Affine.Point.some x y hns)
        = WeierstrassCurve.Affine.Point.some x y hns at key
      rw [WeierstrassCurve.Affine.Point.map_some] at key
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at key
      obtain ⟨hx, hy⟩ := key
      -- the coordinates are `σ`-fixed, hence rational over `𝕜`
      obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_gen_fixed D hx
      obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_gen_fixed D hy
      have hq : WeierstrassCurve.Affine.Nonsingular (D.E.baseChange 𝕜) a b :=
        nonsingular_baseChange_of_algebraMap D (by rw [ha, hb]; exact hns)
      refine ⟨WeierstrassCurve.Affine.Point.some a b hq, ?_⟩
      refine (WeierstrassCurve.Affine.Point.map_some (W' := D.E) (f := Algebra.ofId 𝕜 D.ext.L)
        (x := a) (y := b) hq).trans ?_
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨by rw [Algebra.ofId_apply, ha], by rw [Algebra.ofId_apply, hb]⟩
  · rintro ⟨Q, rfl⟩
    exact WeierstrassCurve.Affine.Point.map_baseChange (W' := D.E)
      (f := (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L)) Q

end Work.PointlessTwist.GaloisFixed
