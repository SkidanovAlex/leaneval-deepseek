/-
# `Work.FIArea7.card_charMod4d_eq_card_units`

The characters of `(ℤ[i]/4d)∗` extended by zero are exactly the multiplicative characters of the
multiplicative monoid `(ℤ[i]/4d)` (Mathlib's `MulChar`), and there are as many of them as there are
units of that monoid -- i.e. as there are pairs `(z₁,z₂) ∈ (ZMod 4d)²` with `z₁² + z₂²` a unit.
This file proves that count:

  `#{χ : ℤ[i] → ℂ // IsCharMod4d d χ ∧ χ vanishes off the units mod 4d}
     = #{z : ZMod (4d) × ZMod (4d) // IsUnit (z₁² + z₂²)}`.

Ingredients:

* `GaussMod N`, the ring `(ℤ[i]/Nℤ[i])` realised as the quadratic algebra `(ZMod N)[i]/(i²+1)`
  (Mathlib's `QuadraticAlgebra (ZMod N) (-1) 0`), whose multiplication is the Gaussian one and
  whose norm is `re² + im²`; `QuadraticAlgebra.isUnit_iff_norm_isUnit` then decides the units.
* `gaussModUnitsEquiv`: the units of `GaussMod N` are the pairs with `IsUnit (r² + s²)`.
* `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity`: a finite monoid has as many
  multiplicative characters over `ℂ` as it has units (duality of finite abelian groups).
* `charEquivMulChar`: a character of the unit group of `ℤ[i]/4d`, extended by zero, is the same
  thing as a `IsCharMod4d`-character vanishing off the units -- the bookkeeping that
  `IsCharMod4d` is stated on `ℤ[i]` (periodicity mod `4d`, vanishing on multiples of `4d`) rather
  than on the quotient ring.

The remaining glue is elementary: `z ↦ (re z, im z)` sends `4d ∣ z - w` to the equality of the
classes mod `4d` and back, and a Gaussian integer `z` is a unit mod `N` exactly when `N` is
coprime to its norm `gnorm z = re z ^ 2 + im z ^ 2` (the arithmetic input of the FI §16 character
machinery).
-/
import Mathlib
import Submission.Work.FITop3.Defs3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open scoped BigOperators

noncomputable section

/-! ## 1. The Gaussian integers modulo `N`

`GaussMod N` is `(ℤ[i]/Nℤ[i])`, presented as the quadratic algebra `(ZMod N)[i]/(i²+1)`: its
elements are pairs `⟨r, s⟩` standing for `r + s·i`, multiplied as Gaussian integers, with norm
`r² + s²`. -/

/-- The ring `(ℤ[i]/Nℤ[i])` as a quadratic algebra over `ZMod N` (`i² = -1`). -/
abbrev GaussMod (N : ℕ) : Type := QuadraticAlgebra (ZMod N) (-1) 0

instance instFiniteGaussMod (N : ℕ) [NeZero N] : Finite (GaussMod N) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (R := ZMod N) (-1) 0).symm

/-- The norm of `⟨r, s⟩ : (ℤ[i]/N)` is `r² + s²`. -/
lemma gaussMod_norm (N : ℕ) (r s : ZMod N) : (⟨r, s⟩ : GaussMod N).norm = r ^ 2 + s ^ 2 := by
  rw [QuadraticAlgebra.norm_def, pow_two, pow_two]; ring

/-- An element of `(ℤ[i]/N)` is a unit iff its norm (i.e. `r² + s²`) is a unit of `ZMod N`. -/
lemma isUnit_gaussMod_iff (N : ℕ) (r s : ZMod N) :
    IsUnit (⟨r, s⟩ : GaussMod N) ↔ IsUnit (r ^ 2 + s ^ 2) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, gaussMod_norm]

/-- Reduction `ℤ[i] → (ℤ[i]/N)`, coordinatewise. -/
def toGaussMod (N : ℕ) : GaussianInt →* GaussMod N where
  toFun z := ⟨(z.re : ZMod N), (z.im : ZMod N)⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Zsqrtd.re_mul,
        Zsqrtd.im_mul, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one]
    all_goals ring

lemma toGaussMod_apply (N : ℕ) (z : GaussianInt) :
    toGaussMod N z = ⟨(z.re : ZMod N), (z.im : ZMod N)⟩ := rfl

/-- `N ∣ z - w` in `ℤ[i]` gives equality of the classes mod `N`, coordinatewise. -/
lemma casts_eq_of_dvd {N : ℕ} {z w : GaussianInt}
    (h : (((N : ℕ) : ℤ) : GaussianInt) ∣ z - w) :
    (z.re : ZMod N) = (w.re : ZMod N) ∧ (z.im : ZMod N) = (w.im : ZMod N) := by
  obtain ⟨c, hc⟩ := h
  have hre : z.re - w.re = ((N : ℕ) : ℤ) * c.re := by
    have := congr_arg Zsqrtd.re hc
    simpa [Zsqrtd.re_mul, Zsqrtd.re_sub] using this
  have him : z.im - w.im = ((N : ℕ) : ℤ) * c.im := by
    have := congr_arg Zsqrtd.im hc
    simpa [Zsqrtd.im_mul, Zsqrtd.im_sub] using this
  constructor
  · have h0 : ((z.re - w.re : ℤ) : ZMod N) = 0 := by
      rw [hre, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rwa [Int.cast_sub, sub_eq_zero] at h0
  · have h0 : ((z.im - w.im : ℤ) : ZMod N) = 0 := by
      rw [him, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rwa [Int.cast_sub, sub_eq_zero] at h0

/-- Conversely, equality of the classes mod `N` gives the Gaussian divisibility `N ∣ z - w`. -/
lemma dvd_of_casts_eq {N : ℕ} {z w : GaussianInt}
    (hre : (z.re : ZMod N) = (w.re : ZMod N)) (him : (z.im : ZMod N) = (w.im : ZMod N)) :
    (((N : ℕ) : ℤ) : GaussianInt) ∣ z - w := by
  have h1 : (N : ℤ) ∣ z.re - w.re := by
    have h := (Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff z.re w.re N).mp hre))
    rw [show z.re - w.re = -(w.re - z.re) by ring]
    exact dvd_neg.mpr h
  have h2 : (N : ℤ) ∣ z.im - w.im := by
    have h := (Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff z.im w.im N).mp him))
    rw [show z.im - w.im = -(w.im - z.im) by ring]
    exact dvd_neg.mpr h
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨⟨a, b⟩, ?_⟩
  ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, ha, hb]

/-- The Gaussian norm `gnorm z = re z ^ 2 + im z ^ 2` of `ℤ[i]`, read in `ZMod N`. -/
lemma gnorm_cast (N : ℕ) (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ZMod N) = (z.re : ZMod N) ^ 2 + (z.im : ZMod N) ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def, pow_two, pow_two]; ring
  have h1 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Work.FIPlan.gnorm, hnorm, Int.natAbs_of_nonneg (by positivity)]
  calc ((Work.FIPlan.gnorm z : ℕ) : ZMod N)
      = ((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod N) := by rw [← Int.cast_natCast, h1]
    _ = (z.re : ZMod N) ^ 2 + (z.im : ZMod N) ^ 2 := by push_cast; ring

/-- A Gaussian integer is a unit mod `N` iff its norm is coprime to `N`.  This is the arithmetic
heart of the character machinery of *FI* §16: units mod `4d` are exactly the `z` with
`(gnorm z, 4d) = 1`, so the characters extended by zero live on the unit group. -/
lemma isUnit_toGaussMod_iff (N : ℕ) (z : GaussianInt) :
    IsUnit (toGaussMod N z) ↔ Nat.Coprime (Work.FIPlan.gnorm z) N := by
  rw [toGaussMod_apply, isUnit_gaussMod_iff, ← gnorm_cast N z, ZMod.isUnit_iff_coprime]

/-- The units of `(ℤ[i]/N)` are the pairs `(r, s)` with `r² + s²` a unit of `ZMod N`. -/
noncomputable def gaussModUnitsEquiv (N : ℕ) :
    (GaussMod N)ˣ ≃ {p : ZMod N × ZMod N // IsUnit (p.1 ^ 2 + p.2 ^ 2)} where
  toFun u := ⟨((u : GaussMod N).re, (u : GaussMod N).im),
    (isUnit_gaussMod_iff N _ _).mp u.isUnit⟩
  invFun p := ((isUnit_gaussMod_iff N p.1.1 p.1.2).mpr p.2).unit
  left_inv u := Units.ext (by rw [IsUnit.unit_spec])
  right_inv p := Subtype.ext (by simp [IsUnit.unit_spec])

/-! ## 2. The characters of `(ℤ[i]/4d)∗` extended by zero -/

/-- `IsCharMod4d d` (a character of modulus `4d` on `ℤ[i]`) **together with** the vanishing
condition off the units mod `4d`.  The second conjunct is what turns a `MulChar` of the quotient
ring into a function on `ℤ[i]` and back; without it `IsCharMod4d` only encodes monoid
semicharacters of `ℤ[i]/4d` (see the notes of `FIArea7`). -/
def IsCharExt (d : ℕ) (chi : GaussianInt → ℂ) : Prop :=
  Work.FITop3.IsCharMod4d d chi ∧
    (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0)

lemma IsCharExt.one {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) : chi 1 = 1 := h.1.1
lemma IsCharExt.mul {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) :
    ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := h.1.2.1
lemma IsCharExt.norm_le {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) :
    ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := h.1.2.2.1
lemma IsCharExt.periodic {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) :
    ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) → chi z = chi w :=
  h.1.2.2.2.1
lemma IsCharExt.eq_zero_of_not_coprime {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) :
    ∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0 := h.2

/-- Periodicity in the coordinate form in which the quotient ring speaks it. -/
lemma IsCharExt.congr {d : ℕ} {chi : GaussianInt → ℂ} (h : IsCharExt d chi) {z w : GaussianInt}
    (hre : (z.re : ZMod (4 * d)) = (w.re : ZMod (4 * d)))
    (him : (z.im : ZMod (4 * d)) = (w.im : ZMod (4 * d))) : chi z = chi w :=
  h.periodic z w (dvd_of_casts_eq hre him)

/-- **Values of a multiplicative character of a finite monoid are bounded by `1`**: on the finite
group of units they are roots of unity. -/
lemma MulChar.norm_apply_le_one {M : Type} [CommMonoid M] [Finite M] (f : MulChar M ℂ) (a : M) :
    ‖f a‖ ≤ 1 := by
  classical
  by_cases h : IsUnit a
  · obtain ⟨n, hnpos, hn⟩ := (isOfFinOrder_of_finite h.unit).exists_pow_eq_one
    have hpow : f (h.unit : M) ^ n = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val h.unit n, hn, Units.val_one, map_one]
    have hspec : (h.unit : M) = a := IsUnit.unit_spec h
    rw [← hspec, Complex.norm_eq_one_of_pow_eq_one hpow hnpos.ne']
  · rw [MulChar.map_nonunit f h]
    simp

/-- A multiplicative character of `(ℤ[i]/4d)` read on `ℤ[i]`. -/
noncomputable def mulCharToFun (d : ℕ) (f : MulChar (GaussMod (4 * d)) ℂ) (z : GaussianInt) : ℂ :=
  f (toGaussMod (4 * d) z)

/-- **One direction of the bijection**: a multiplicative character of `(ℤ[i]/4d)` is an
`IsCharMod4d d`-character of `ℤ[i]` vanishing off the units. -/
lemma isCharExt_mulCharToFun (d : ℕ) (hd : 0 < d) (f : MulChar (GaussMod (4 * d)) ℂ) :
    IsCharExt d (mulCharToFun d f) := by
  have : NeZero (4 * d) := ⟨by omega⟩
  have : Fact (1 < 4 * d) := ⟨by omega⟩
  have hle : ∀ a : GaussMod (4 * d), ‖f a‖ ≤ 1 := MulChar.norm_apply_le_one f
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [mulCharToFun]
  · intro z w
    simp only [mulCharToFun, map_mul]
  · intro z
    exact hle _
  · intro z w hzw
    rw [mulCharToFun, mulCharToFun]
    obtain ⟨hre, him⟩ := casts_eq_of_dvd (N := 4 * d) hzw
    rw [toGaussMod_apply, toGaussMod_apply, hre, him]
  · intro z hz
    rw [mulCharToFun]
    have h0 : toGaussMod (4 * d) z = 0 := by
      rw [toGaussMod_apply]
      obtain ⟨hre, him⟩ := casts_eq_of_dvd (N := 4 * d) (z := z) (w := 0) (by simpa using hz)
      rw [hre, him]
      ext <;> simp
    rw [h0]
    exact MulChar.map_nonunit f not_isUnit_zero
  · intro z hz
    rw [mulCharToFun]
    exact MulChar.map_nonunit f (fun hc => hz ((isUnit_toGaussMod_iff (4 * d) z).mp hc))

/-! ## 3. The other direction, by the canonical representative lift -/

/-- The canonical representative lift `(ℤ[i]/N) → ℤ[i]`, using `ZMod.val`. -/
def liftToInt (N : ℕ) (a : GaussMod N) : GaussianInt := ⟨(a.re.val : ℤ), (a.im.val : ℤ)⟩

lemma liftToInt_re {N : ℕ} [NeZero N] (a : GaussMod N) : ((liftToInt N a).re : ZMod N) = a.re := by
  simp [liftToInt]

lemma liftToInt_im {N : ℕ} [NeZero N] (a : GaussMod N) : ((liftToInt N a).im : ZMod N) = a.im := by
  simp [liftToInt]

/-- **The other direction**: an `IsCharMod4d d`-character vanishing off the units is a
multiplicative character of `(ℤ[i]/4d)`.  The well-definedness on the quotient is exactly the
periodicity axiom, applied to the components of the chosen representatives. -/
noncomputable def funToMulChar (d : ℕ) (hd : 0 < d) (χ : GaussianInt → ℂ) (hχ : IsCharExt d χ) :
    MulChar (GaussMod (4 * d)) ℂ where
  toFun a := χ (liftToInt (4 * d) a)
  map_one' := by
    have : NeZero (4 * d) := ⟨by omega⟩
    rw [← hχ.one]
    refine hχ.congr ?_ ?_ <;>
      simp [liftToInt_re, liftToInt_im, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' a b := by
    have : NeZero (4 * d) := ⟨by omega⟩
    rw [← hχ.mul (liftToInt (4 * d) a) (liftToInt (4 * d) b)]
    refine hχ.congr ?_ ?_ <;>
      simp [liftToInt_re, liftToInt_im, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_nonunit' a ha := by
    have : NeZero (4 * d) := ⟨by omega⟩
    refine hχ.eq_zero_of_not_coprime _ fun hc => ha ?_
    have hcast : ((Work.FIPlan.gnorm (liftToInt (4 * d) a) : ℕ) : ZMod (4 * d)) =
        a.re ^ 2 + a.im ^ 2 := by
      rw [gnorm_cast]
      simp [liftToInt_re, liftToInt_im]
    rw [isUnit_gaussMod_iff, ← hcast, ZMod.isUnit_iff_coprime]
    exact hc

lemma mulCharToFun_funToMulChar (d : ℕ) (hd : 0 < d) (χ : GaussianInt → ℂ) (hχ : IsCharExt d χ) :
    mulCharToFun d (funToMulChar d hd χ hχ) = χ := by
  have : NeZero (4 * d) := ⟨by omega⟩
  funext z
  refine hχ.congr ?_ ?_
  · rw [liftToInt_re, toGaussMod_apply]
  · rw [liftToInt_im, toGaussMod_apply]

lemma funToMulChar_mulCharToFun (d : ℕ) (hd : 0 < d) (f : MulChar (GaussMod (4 * d)) ℂ) :
    funToMulChar d hd (mulCharToFun d f) (isCharExt_mulCharToFun d hd f) = f := by
  have : NeZero (4 * d) := ⟨by omega⟩
  ext a
  change (mulCharToFun d f) (liftToInt (4 * d) (a : GaussMod (4 * d))) =
    f (a : GaussMod (4 * d))
  rw [mulCharToFun]
  have h : toGaussMod (4 * d) (liftToInt (4 * d) (a : GaussMod (4 * d))) =
      (a : GaussMod (4 * d)) := by
    rw [toGaussMod_apply]
    ext <;> simp [liftToInt_re, liftToInt_im]
  rw [h]

/-- **The characters of the unit group of `ℤ[i]/4d`, extended by zero, are the multiplicative
characters of the monoid `ℤ[i]/4d`.** -/
noncomputable def charEquivMulChar (d : ℕ) (hd : 0 < d) :
    {chi : GaussianInt → ℂ // IsCharExt d chi} ≃ MulChar (GaussMod (4 * d)) ℂ where
  toFun p := funToMulChar d hd p.1 p.2
  invFun f := ⟨mulCharToFun d f, isCharExt_mulCharToFun d hd f⟩
  left_inv p := Subtype.ext (mulCharToFun_funToMulChar d hd p.1 p.2)
  right_inv f := funToMulChar_mulCharToFun d hd f

/-- **The count of the characters of `(ℤ[i]/4d)∗`, extended by zero, is the number of units of
`(ℤ[i]/4d)`** -- i.e. the number of pairs `(z₁,z₂) ∈ (ZMod 4d)²` with `z₁² + z₂²` a unit. -/
theorem card_charMod4d_eq_card_units (d : ℕ) (hd : 0 < d) :
    Nat.card {chi : GaussianInt → ℂ // Work.FITop3.IsCharMod4d d chi ∧
        (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0)}
      = Nat.card {z : ZMod (4 * d) × ZMod (4 * d) // IsUnit (z.1 ^ 2 + z.2 ^ 2)} := by
  have : NeZero (4 * d) := ⟨by omega⟩
  calc Nat.card {chi : GaussianInt → ℂ // Work.FITop3.IsCharMod4d d chi ∧
          (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0)}
      = Nat.card (MulChar (GaussMod (4 * d)) ℂ) := Nat.card_congr (charEquivMulChar d hd)
    _ = Nat.card (GaussMod (4 * d))ˣ :=
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity _ _
    _ = Nat.card {z : ZMod (4 * d) × ZMod (4 * d) // IsUnit (z.1 ^ 2 + z.2 ^ 2)} :=
        Nat.card_congr (gaussModUnitsEquiv (4 * d))

end

end Work.FIArea7
