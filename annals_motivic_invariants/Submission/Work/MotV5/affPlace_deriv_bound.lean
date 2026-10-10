import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotV.PlaceDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The invariant derivation is regular at the affine places of an elliptic curve

Two facts about the invariant derivation `D` of an elliptic Weierstrass curve (the derivation with
`D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`, i.e. the derivation attached to the
invariant differential) are proved here for the local ring `affPlaceAt E a b` of a nonsingular
affine point:

* `Work.MotV5.deriv_mem_affPlaceAt`: `D` maps the local ring into itself;
* `Work.MotV5.affPlace_deriv_bound`: for a function with a pole at `(a,b)` the order at that place
  drops by at most one under `D`.

The second statement is `ordOfPlace f - 1 ≤ ordOfPlace (D f)` for `f ∉ affPlaceAt E a b`.  Since
`D f = - f² · D(f⁻¹)` and `f⁻¹` is regular at the place, the whole content is the inequality
`ord (D g) ≥ ord g - 1` for `g` in the local ring: if `π` is a uniformizer and `g = u πⁿ`, then
`D g = πⁿ⁻¹ · (u n Dπ + π Du)`, and every factor of the second factor is regular.

## Tags

elliptic curve, function field, invariant derivation, place, order of vanishing
-/

set_option maxHeartbeats 1000000

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine

/-- `WithTop.untopD 0` of a natural number cast to `ℕ∞` is that number.  (Stated separately
because rewriting with `WithTop.untopD_coe` in a goal where the value was produced by
`IsDiscreteValuationRing.addVal` runs into a definitional-unfolding mismatch between `ℕ∞` and
`WithTop ℕ`.) -/
private lemma untopD_enat (n : ℕ) :
    (WithTop.untopD (0 : ℕ) ((n : ℕ∞)) : ℕ) = n :=
  WithTop.untopD_coe 0 n

/-! ## The invariant derivation preserves the local ring of an affine point -/

/-- The derivation `D` acting on the coordinates as the invariant derivation does
(`D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`) maps the local ring `affPlaceAt E a b` of
any affine point into itself.

No hypothesis on the characteristic, on the point, or on the curve is needed: `D` is determined by
its values on `x` and `y`, both of which lie in the coordinate ring, and `2y + a₁x + a₃`,
`3x² + 2a₂x + a₄ - a₁y` are themselves elements of the coordinate ring. -/
theorem deriv_mem_affPlaceAt {N : Type*} [Field N] (E : WeierstrassCurve N) (a b : N)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    ∀ f : Work.MotC2.Func E, f ∈ Work.MotC2.affPlaceAt E a b →
      D f ∈ Work.MotC2.affPlaceAt E a b := by
  let S : Subalgebra N (Work.MotC2.Func E) := Work.MotC2.affPlaceAt E a b
  have hxS : Work.MotC2.genX E ∈ S :=
    Work.MotC2.algebraMap_mem_affPlaceAt E a b (Work.MotC2.coordX E)
  have hyS : Work.MotC2.genY E ∈ S :=
    Work.MotC2.algebraMap_mem_affPlaceAt E a b (Work.MotC2.coordY E)
  have h2S : (2 : Work.MotC2.Func E) ∈ S := by
    simpa using S.algebraMap_mem (2 : N)
  have h3S : (3 : Work.MotC2.Func E) ∈ S := by
    simpa using S.algebraMap_mem (3 : N)
  have hDx : D (Work.MotC2.genX E) ∈ S := by
    rw [hx]
    exact S.add_mem (S.add_mem (S.mul_mem h2S hyS)
      (S.mul_mem (S.algebraMap_mem E.a₁) hxS)) (S.algebraMap_mem E.a₃)
  have hDy : D (Work.MotC2.genY E) ∈ S := by
    rw [hy]
    exact S.sub_mem (S.add_mem (S.add_mem (S.mul_mem h3S (S.pow_mem hxS 2))
      (S.mul_mem (S.mul_mem h2S (S.algebraMap_mem E.a₂)) hxS))
      (S.algebraMap_mem E.a₄)) (S.mul_mem (S.algebraMap_mem E.a₁) hyS)
  -- `U` is the subalgebra of elements `f` with `f ∈ S` and `D f ∈ S`.
  let U : Subalgebra N (Work.MotC2.Func E) :=
    { carrier := {f : Work.MotC2.Func E | f ∈ S ∧ D f ∈ S}
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨S.mul_mem hx1 hy1, ?_⟩
        rw [Derivation.leibniz]
        rw [smul_eq_mul, smul_eq_mul]
        exact S.add_mem (S.mul_mem hx1 hy2) (S.mul_mem hy1 hx2)
      one_mem' := ⟨S.one_mem, by rw [Derivation.map_one_eq_zero]; exact S.zero_mem⟩
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨S.add_mem hx1 hy1, ?_⟩
        rw [map_add]
        exact S.add_mem hx2 hy2
      zero_mem' := ⟨S.zero_mem, by rw [map_zero]; exact S.zero_mem⟩
      algebraMap_mem' := by
        intro c
        refine ⟨S.algebraMap_mem c, ?_⟩
        rw [Derivation.map_algebraMap]
        exact S.zero_mem }
  have hgen : Algebra.adjoin N ({Work.MotC2.genX E, Work.MotC2.genY E} :
      Set (Work.MotC2.Func E)) ≤ U := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨hxS, hDx⟩
    · exact ⟨hyS, hDy⟩
  -- Every element of the coordinate ring lies in `U`.
  have hR : ∀ c : Work.MotC2.Coord E,
      algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) c ∈ U := by
    intro c
    apply hgen
    rw [← Work.MotC2.affRing_eq_adjoin]
    exact Algebra.subset_adjoin (Set.mem_range_self c)
  -- The generators of `S` lie in `U`.
  have hSle : S ≤ U := by
    rw [show S = Algebra.adjoin N (Work.MotC2.affPlaceGens E a b) from rfl]
    rw [Algebra.adjoin_le_iff]
    rintro x (hx | hx)
    · obtain ⟨c, rfl⟩ := hx
      exact hR c
    · obtain ⟨r, hr, rfl⟩ := hx
      refine ⟨Work.MotC2.inv_algebraMap_mem_affPlaceAt E a b hr, ?_⟩
      rw [Derivation.leibniz_inv]
      rw [smul_eq_mul]
      exact S.mul_mem (S.neg_mem (S.pow_mem
        (Work.MotC2.inv_algebraMap_mem_affPlaceAt E a b hr) 2)) (hR r).2
  intro f hf
  exact (hSle hf).2

/-! ## Elementary properties of the order at a rational place -/

/-- The order of a function which is regular at the place is nonnegative. -/
theorem ordOfPlace_nonneg_of_mem {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    {x : Work.MotC2.Func E} (hx : x ∈ S) : 0 ≤ Work.MotV.ordOfPlace E S hS x := by
  unfold Work.MotV.ordOfPlace
  rw [dif_pos hx]
  exact Int.natCast_nonneg _

/-- **The order of a unit times a power of a uniformizer.**  If `π` is a uniformizer of the
discrete valuation ring `↥S` (i.e. `π` is irreducible) and `u` is a unit of `↥S`, then the order
of `u πᵏ` at the place is `k`. -/
theorem ordOfPlace_unit_mul_zpow {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (π : ↥S) (hπ : Irreducible π) (u : Sˣ) (k : ℤ) :
    Work.MotV.ordOfPlace E S hS (((u : ↥S) : Work.MotC2.Func E) *
      ((π : ↥S) : Work.MotC2.Func E) ^ k) = k := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  have hπne : ((π : ↥S) : Work.MotC2.Func E) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.coe_injective (by simpa using h))
  by_cases hk : 0 ≤ k
  · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    have hzpow : ((π : ↥S) : Work.MotC2.Func E) ^ k
        = ((π : ↥S) : Work.MotC2.Func E) ^ k.toNat := by
      conv_lhs => rw [← hk']
      rw [zpow_natCast]
    have hx : (((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ k)
        = ((↑u * π ^ k.toNat : ↥S) : Work.MotC2.Func E) := by
      rw [hzpow, Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [hx]
    unfold Work.MotV.ordOfPlace
    rw [dif_pos (↑u * π ^ k.toNat).2]
    have hcoe : (⟨((↑u * π ^ k.toNat : ↥S) : Work.MotC2.Func E),
        (↑u * π ^ k.toNat).2⟩ : ↥S) = ↑u * π ^ k.toNat := rfl
    rw [hcoe, IsDiscreteValuationRing.addVal_def' u hπ k.toNat,
      untopD_enat, hk']
  · push_neg at hk
    set j : ℕ := (-k).toNat with hjdef
    have hkj : (j : ℤ) = -k := by rw [hjdef]; exact Int.toNat_of_nonneg (by omega)
    have hjpos : 0 < j := by
      rw [← Int.ofNat_lt, hkj]; omega
    have hxne : (((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ k) ≠ 0 := by
      apply mul_ne_zero
      · intro h
        exact u.ne_zero (Subtype.coe_injective (by simpa using h))
      · exact zpow_ne_zero _ hπne
    have hxnot : (((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ k) ∉ S := by
      intro hxmem
      have hz : (⟨_, hxmem⟩ : ↥S) * π ^ j = (↑u : ↥S) := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
        rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hπne]
        have hzero : k + (j : ℤ) = 0 := by rw [hkj]; ring
        rw [hzero, zpow_zero, mul_one]
      have h := congrArg (fun z : ↥S => IsDiscreteValuationRing.addVal ↥S z) hz
      rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hπ,
        IsDiscreteValuationRing.addVal_eq_zero_of_unit u] at h
      simp only [nsmul_eq_mul, mul_one] at h
      exact absurd (add_eq_zero.mp h).2 (by simpa using hjpos.ne')
    have huu : (((↑u : ↥S)) : Work.MotC2.Func E)⁻¹ = (((↑u⁻¹ : ↥S)) : Work.MotC2.Func E) :=
      (map_units_inv (algebraMap ↥S (Work.MotC2.Func E)) u).symm
    have hinv : (((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ k)⁻¹
        = ((↑(u⁻¹) * π ^ j : ↥S) : Work.MotC2.Func E) := by
      rw [mul_inv, huu, ← zpow_neg, Subalgebra.coe_mul, Subalgebra.coe_pow]
      rw [show -k = (j : ℤ) from hkj.symm, zpow_natCast]
    have hsub : (⟨(((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ k)⁻¹,
        (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS _).resolve_left hxnot⟩ : ↥S)
        = (↑(u⁻¹) * π ^ j : ↥S) := by
      apply Subtype.ext
      exact hinv
    unfold Work.MotV.ordOfPlace
    rw [dif_neg hxnot, hsub, IsDiscreteValuationRing.addVal_def' u⁻¹ hπ j, untopD_enat]
    rw [hkj]
    first | refl_ring1 | ring

/-- **The order of a regular element times a power of a uniformizer.**  For `w ∈ ↥S` and any
`k : ℤ`, the order of `w πᵏ` is `ord w + k`. -/
theorem ordOfPlace_mul_zpow {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (π : ↥S) (hπ : Irreducible π) (w : ↥S) (hw : w ≠ 0) (k : ℤ) :
    Work.MotV.ordOfPlace E S hS (((w : ↥S) : Work.MotC2.Func E) *
        ((π : ↥S) : Work.MotC2.Func E) ^ k)
      = Work.MotV.ordOfPlace E S hS ((w : ↥S) : Work.MotC2.Func E) + k := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  have hπne : ((π : ↥S) : Work.MotC2.Func E) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.coe_injective (by simpa using h))
  obtain ⟨a, u, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hπ
  have hwcoe : ((w : ↥S) : Work.MotC2.Func E)
      = ((u : ↥S) : Work.MotC2.Func E) * ((π : ↥S) : Work.MotC2.Func E) ^ a := by
    rw [hwu, Subalgebra.coe_mul, Subalgebra.coe_pow]
  have h1 : Work.MotV.ordOfPlace E S hS ((w : ↥S) : Work.MotC2.Func E) = (a : ℤ) := by
    rw [hwcoe, ← zpow_natCast]
    exact ordOfPlace_unit_mul_zpow E S hS π hπ u (a : ℤ)
  have h2 : Work.MotV.ordOfPlace E S hS (((w : ↥S) : Work.MotC2.Func E) *
      ((π : ↥S) : Work.MotC2.Func E) ^ k) = (a : ℤ) + k := by
    rw [hwcoe, ← zpow_natCast, mul_assoc, ← zpow_add₀ hπne]
    exact ordOfPlace_unit_mul_zpow E S hS π hπ u ((a : ℤ) + k)
  rw [h1, h2]

/-- The order of `0` at a place is `0` (the convention of `ordOfPlace`). -/
theorem ordOfPlace_zero {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    Work.MotV.ordOfPlace E S hS (0 : Work.MotC2.Func E) = 0 := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  unfold Work.MotV.ordOfPlace
  rw [dif_pos S.zero_mem]
  have h0 : (⟨(0 : Work.MotC2.Func E), S.zero_mem⟩ : ↥S) = 0 := rfl
  rw [h0, IsDiscreteValuationRing.addVal_zero]
  rfl

/-! ## A field-theoretic identity -/

/-- In a field, with `P ≠ 0` and `1 ≤ n`:
`((UPⁿ)⁻¹)² · Pⁿ⁻¹S = (U⁻¹)²S · (Pⁿ⁺¹)⁻¹`. -/
private lemma inv_mul_pow_identity {K : Type*} [Field K] (P U S : K) (n : ℕ) (hn : 1 ≤ n)
    (hP : P ≠ 0) :
    ((U * P ^ n)⁻¹) ^ 2 * (P ^ (n - 1) * S) = ((U⁻¹) ^ 2 * S) * (P ^ (n + 1))⁻¹ := by
  have hb : ((P ^ n)⁻¹) ^ 2 = (P ^ (2 * n))⁻¹ := by
    rw [inv_pow, ← pow_mul, show n * 2 = 2 * n from by ring]
  have hkey : ((P ^ (2 * n))⁻¹) * P ^ (n - 1) = (P ^ (n + 1))⁻¹ := by
    rw [show 2 * n = (n - 1) + (n + 1) from by omega, pow_add, mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hP), mul_one]
  rw [mul_inv, mul_pow, hb]
  rw [show (U⁻¹) ^ 2 * (P ^ (2 * n))⁻¹ * (P ^ (n - 1) * S)
      = (U⁻¹) ^ 2 * ((P ^ (2 * n))⁻¹ * P ^ (n - 1)) * S from by ring, hkey]
  first | refl_ring1 | ring

theorem affPlace_deriv_bound {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N)
    [E.IsElliptic] (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    (∀ f : Work.MotC2.Func E, f ∈ Work.MotC2.affPlaceAt E a b →
      D f ∈ Work.MotC2.affPlaceAt E a b) ∧
    (∀ f : Work.MotC2.Func E, f ∉ Work.MotC2.affPlaceAt E a b →
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b) (Work.MotC2.AffPlace N E a b h).1 f - 1 ≤
        Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b) (Work.MotC2.AffPlace N E a b h).1
          (D f)) := by
  have hpart1 : ∀ f : Work.MotC2.Func E, f ∈ Work.MotC2.affPlaceAt E a b →
      D f ∈ Work.MotC2.affPlaceAt E a b := deriv_mem_affPlaceAt E a b D hx hy
  refine ⟨hpart1, ?_⟩
  intro f hf
  let S : Subalgebra N (Work.MotC2.Func E) := Work.MotC2.affPlaceAt E a b
  let hS : Work.MotC2.IsRatPlace E S := (Work.MotC2.AffPlace N E a b h).1
  change Work.MotV.ordOfPlace E S hS f - 1 ≤ Work.MotV.ordOfPlace E S hS (D f)
  have hfS : f ∉ S := hf
  have hf0 : f ≠ 0 := fun h0 => hfS (h0 ▸ S.zero_mem)
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  obtain ⟨π, hπ⟩ : ∃ π : ↥S, Irreducible π := IsDiscreteValuationRing.exists_irreducible ↥S
  have hπne : ((π : ↥S) : Work.MotC2.Func E) ≠ 0 := by
    intro hh
    exact hπ.ne_zero (Subtype.coe_injective (by simpa using hh))
  -- `g := f⁻¹` is regular at the place
  have hgmem : f⁻¹ ∈ S := (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hfS
  let g : ↥S := ⟨f⁻¹, hgmem⟩
  have hgval : (g : Work.MotC2.Func E) = f⁻¹ := rfl
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : f⁻¹ = 0 := by rw [← hgval, h0]; rfl
    exact hf0 (inv_eq_zero.mp h1)
  -- write `g = u πⁿ`
  obtain ⟨n, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hπ
  have hvalg : IsDiscreteValuationRing.addVal ↥S g = (n : ℕ∞) := by
    rw [hgu, IsDiscreteValuationRing.addVal_def' u hπ n]
  have hgc : (g : Work.MotC2.Func E) = ((u : ↥S) : Work.MotC2.Func E) *
      ((π : ↥S) : Work.MotC2.Func E) ^ n := by
    rw [hgu, Subalgebra.coe_mul, Subalgebra.coe_pow]
  -- the exponent `n` is positive, else `f = g⁻¹` would be regular
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have hunit : IsUnit g := by
        rw [hgu, h0]
        simpa using u.isUnit
      obtain ⟨w, hw⟩ := hunit
      have h1 : f = ((↑w⁻¹ : ↥S) : Work.MotC2.Func E) := by
        have h2 : (g : Work.MotC2.Func E) = ((w : ↥S) : Work.MotC2.Func E) := by rw [← hw]
        rw [show f = (g : Work.MotC2.Func E)⁻¹ from by rw [hgval, inv_inv], h2]
        exact (map_units_inv (algebraMap ↥S (Work.MotC2.Func E)) w).symm
      rw [h1] at hfS
      exact hfS (↑w⁻¹ : ↥S).2
    · exact hpos
  -- the orders of `g` and of `f`
  have hordg : Work.MotV.ordOfPlace E S hS (g : Work.MotC2.Func E) = (n : ℤ) := by
    unfold Work.MotV.ordOfPlace
    rw [dif_pos g.2]
    have hcoe : (⟨(g : Work.MotC2.Func E), g.2⟩ : ↥S) = g := rfl
    rw [hcoe, hvalg, untopD_enat]
  have hordf : Work.MotV.ordOfPlace E S hS f = -(n : ℤ) := by
    unfold Work.MotV.ordOfPlace
    rw [dif_neg hfS]
    have hsub : (⟨f⁻¹,
        (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hfS⟩ : ↥S) = g := rfl
    rw [hsub, hvalg, untopD_enat]
  -- the "regular correction" `s`
  have hDgmem : D (g : Work.MotC2.Func E) ∈ S := hpart1 _ g.2
  have hDumem : D ((u : ↥S) : Work.MotC2.Func E) ∈ S := hpart1 _ (u : ↥S).2
  have hDπmem : D ((π : ↥S) : Work.MotC2.Func E) ∈ S := hpart1 _ π.2
  let e : Work.MotC2.Func E := ((u : ↥S) : Work.MotC2.Func E) * (n : Work.MotC2.Func E) *
      D ((π : ↥S) : Work.MotC2.Func E) + ((π : ↥S) : Work.MotC2.Func E) *
      D ((u : ↥S) : Work.MotC2.Func E)
  have he_mem : e ∈ S := by
    dsimp only [e]
    refine S.add_mem (S.mul_mem (S.mul_mem (u : ↥S).2 ?_) hDπmem) (S.mul_mem π.2 hDumem)
    simpa using S.algebraMap_mem (n : N)
  let sm : ↥S := ⟨e, he_mem⟩
  have hsm_val : (sm : Work.MotC2.Func E) = e := rfl
  -- `D g = πⁿ⁻¹ · s`
  have hDg_eq : D (g : Work.MotC2.Func E) =
      ((π : ↥S) : Work.MotC2.Func E) ^ (n - 1) * (sm : Work.MotC2.Func E) := by
    rw [hgc, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, hsm_val]
    have hpown : ((π : ↥S) : Work.MotC2.Func E) ^ n
        = ((π : ↥S) : Work.MotC2.Func E) ^ (n - 1) * ((π : ↥S) : Work.MotC2.Func E) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ]
    rw [hpown]
    dsimp only [e]
    first | refl_ring1 | ring
  -- `D f = W · π^{-(n+1)}` with `W ∈ S`
  let W0 : ↥S := (↑(u⁻¹) : ↥S) ^ 2 * sm
  let W : ↥S := -W0
  have hDf_eq : D f = (W : Work.MotC2.Func E) *
      ((π : ↥S) : Work.MotC2.Func E) ^ (-((n + 1 : ℕ) : ℤ)) := by
    have hfg : f = (g : Work.MotC2.Func E)⁻¹ := by rw [hgval, inv_inv]
    rw [hfg, Derivation.leibniz_inv, smul_eq_mul, neg_mul, hDg_eq, hgc]
    rw [inv_mul_pow_identity ((π : ↥S) : Work.MotC2.Func E) ((u : ↥S) : Work.MotC2.Func E)
      (sm : Work.MotC2.Func E) n hn hπne]
    have hW : (W : Work.MotC2.Func E)
        = -(((↑(u⁻¹) : ↥S) : Work.MotC2.Func E) ^ 2 * (sm : Work.MotC2.Func E)) := by
      simp only [W, W0, Subalgebra.coe_neg, Subalgebra.coe_mul, Subalgebra.coe_pow]
    have huu : (((u : ↥S) : Work.MotC2.Func E))⁻¹
        = (((↑u⁻¹ : ↥S)) : Work.MotC2.Func E) :=
      (map_units_inv (algebraMap ↥S (Work.MotC2.Func E)) u).symm
    have hzpow : ((π : ↥S) : Work.MotC2.Func E) ^ (-((n + 1 : ℕ) : ℤ))
        = (((π : ↥S) : Work.MotC2.Func E) ^ (n + 1))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hW, huu, hzpow]
    first | refl_ring1 | ring
  -- conclude
  rw [hordf, hDf_eq]
  by_cases hW0 : W = 0
  · rw [hW0, Subalgebra.coe_zero, zero_mul, ordOfPlace_zero]
    omega
  · rw [ordOfPlace_mul_zpow E S hS π hπ W hW0 (-((n + 1 : ℕ) : ℤ))]
    have hnonneg : 0 ≤ Work.MotV.ordOfPlace E S hS ((W : ↥S) : Work.MotC2.Func E) :=
      ordOfPlace_nonneg_of_mem E S hS W.2
    have hcast : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
    linarith

end Work.MotV5
