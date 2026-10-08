import Mathlib
import Submission.Work.ZASS.Leaf9

/-! # ZASS2: the field map `S` induced by the involution `s`

Given field coordinates `C : ZassCoords G X inf zero U` (`Θ : X ≃ Option C.E`, `Θ inf = none`,
`Θ zero = some 0`) and a group element `s` with `s • zero = inf` and `s * s = 1`, we define
the map `S = zassS C s` on `C.E` by

`zassS C s y := (C.Θ (s • (C.Θ.symm (some y)))).getD 0`,

i.e. `S y` is the coordinate of `s • x` where `x = Θ.symm (some y)`; the default `0` is only
used at `y = 0` (where `s • zero = inf` has coordinate `none`).

The basic API proved here:

* `zassS_spec : y ≠ 0 → Θ (s • Θ.symm (some y)) = some (S y)`;
* `zassS_ne_zero : y ≠ 0 → S y ≠ 0`;
* `zassS_involutive : y ≠ 0 → S (S y) = y`.
-/

namespace Work.ZASS2

open Work.GW2

/-- The map `S` on the field coordinates induced by the involution `s`. -/
noncomputable def zassS {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) (s : G) (y : C.E) : C.E :=
  (C.Θ (s • (C.Θ.symm (some y)))).getD 0

/-- `Option.getD` of a non-`none` option. -/
theorem option_eq_some_getD {α : Type*} [Zero α] {o : Option α} (h : o ≠ none) :
    o = some (o.getD 0) := by
  cases o with
  | none => exact absurd rfl h
  | some a => rfl

/-- `S y` is the coordinate of `s • x`, where `x` is the point of coordinate `y` (for `y ≠ 0`). -/
theorem zassS_spec {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) {s : G} (hsz : s • zero = inf) (hs2 : s * s = 1)
    {y : C.E} (hy : y ≠ 0) :
    C.Θ (s • (C.Θ.symm (some y))) = some (zassS C s y) := by
  have hne : C.Θ (s • (C.Θ.symm (some y))) ≠ none := by
    intro h
    -- then `s • x = inf`, hence `x = zero`, contradicting `Θ x = some y`
    -- `s • inf = zero`, and `s • (s • x) = x`
    have hsinf : s • inf = zero := by
      rw [← hsz, ← mul_smul, hs2, one_smul]
    have h1 : s • (C.Θ.symm (some y)) = inf := C.Θ.injective (by rw [h, C.Θ_inf])
    have h2 : C.Θ.symm (some y) = zero := by
      have h3 : s • (s • (C.Θ.symm (some y))) = s • inf := congrArg (fun z => s • z) h1
      rw [← mul_smul, hs2, one_smul] at h3
      rw [h3, hsinf]
    have h4 : (some y : Option C.E) = some 0 := by
      calc (some y : Option C.E) = C.Θ (C.Θ.symm (some y)) :=
            (Equiv.apply_symm_apply C.Θ (some y)).symm
        _ = C.Θ zero := by rw [h2]
        _ = some 0 := C.Θ_zero
    exact hy (Option.some.inj h4)
  have := option_eq_some_getD (α := C.E) hne
  simpa only [zassS] using this

/-- `S y ≠ 0` for `y ≠ 0`: if `S y = 0` then `s • x = zero`, so `x = inf`. -/
theorem zassS_ne_zero {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) {s : G} (hsz : s • zero = inf) (hs2 : s * s = 1)
    {y : C.E} (hy : y ≠ 0) : zassS C s y ≠ 0 := by
  intro h0
  have hspec := zassS_spec C hsz hs2 hy
  rw [h0, ← C.Θ_zero] at hspec
  have h1 : s • (C.Θ.symm (some y)) = zero := C.Θ.injective hspec
  have h2 : C.Θ.symm (some y) = inf := by
    have h3 : s • (s • (C.Θ.symm (some y))) = s • zero := congrArg (fun z => s • z) h1
    rw [← mul_smul, hs2, one_smul] at h3
    rw [h3, hsz]
  have h4 : (some y : Option C.E) = none := by
    rw [← Equiv.apply_symm_apply C.Θ (some y), h2, C.Θ_inf]
  exact absurd h4 (Option.some_ne_none y)

/-- `S (S y) = y` for `y ≠ 0`, because `s * s = 1`. -/
theorem zassS_involutive {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) {s : G} (hsz : s • zero = inf) (hs2 : s * s = 1)
    {y : C.E} (hy : y ≠ 0) : zassS C s (zassS C s y) = y := by
  have hy' : zassS C s y ≠ 0 := zassS_ne_zero C hsz hs2 hy
  have h2 : C.Θ.symm (some (zassS C s y)) = s • (C.Θ.symm (some y)) := by
    rw [← zassS_spec C hsz hs2 hy]
    exact Equiv.symm_apply_apply C.Θ _
  have hA : C.Θ (s • (s • (C.Θ.symm (some y)))) = some (zassS C s (zassS C s y)) := by
    rw [← h2]
    exact zassS_spec C hsz hs2 hy'
  have hB : C.Θ (s • (s • (C.Θ.symm (some y)))) = C.Θ (C.Θ.symm (some y)) := by
    rw [← mul_smul, hs2, one_smul]
  have h5 : (some (zassS C s (zassS C s y)) : Option C.E) = some y := by
    rw [← hA, hB, Equiv.apply_symm_apply]
  exact Option.some.inj h5

end Work.ZASS2
