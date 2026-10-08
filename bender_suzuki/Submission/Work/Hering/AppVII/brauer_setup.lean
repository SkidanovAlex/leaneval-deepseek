import Mathlib
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

open scoped BigOperators

namespace Work.Hering.AppVII

/-- A central idempotent of a monoid with zero. -/
def IsCentralIdempotent {R : Type*} [MonoidWithZero R] (e : R) : Prop :=
  IsIdempotentElem e ∧ ∀ x : R, x * e = e * x

/-- A primitive central idempotent: a non-zero central idempotent that is not the orthogonal
sum of two non-zero central idempotents. -/
def IsPrimitiveCentralIdempotent {R : Type*} [MonoidWithZero R] (e : R) : Prop :=
  IsCentralIdempotent e ∧ e ≠ 0 ∧
    ∀ f : R, IsCentralIdempotent f → f * e = f → f = 0 ∨ f = e

/-- The field `k = F̄_r`. -/
abbrev BrauerField (r : ℕ) [Fact r.Prime] : Type := AlgebraicClosure (ZMod r)

/-- The `ℤ`-algebra `ℤ[ζ_n]`, presented as `ℤ[X]/(Φ_n)`. -/
abbrev CycloRing (n : ℕ) : Type := AdjoinRoot (Polynomial.cyclotomic n ℤ)

theorem cycloRing_prime {n : ℕ} (hn : n ≠ 0) : Prime (Polynomial.cyclotomic n ℤ) :=
  (UniqueFactorizationMonoid.irreducible_iff_prime).mp
    (Polynomial.cyclotomic.irreducible (Nat.pos_of_ne_zero hn))

instance {n : ℕ} [NeZero n] : IsDomain (CycloRing n) :=
  AdjoinRoot.isDomain_of_prime (cycloRing_prime (NeZero.ne n))

/-- `eval₂` of the integral cyclotomic polynomial at a primitive root vanishes. -/
theorem eval₂_cyclotomic_eq_zero {S : Type*} [Field S] {n : ℕ} (x : S) (hxn : (n : S) ≠ 0)
    (hx : IsPrimitiveRoot x n) :
    Polynomial.eval₂ (Int.castRingHom S) x (Polynomial.cyclotomic n ℤ) = 0 := by
  haveI : NeZero (n : S) := ⟨hxn⟩
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact Polynomial.IsRoot.def.mp ((Polynomial.isRoot_cyclotomic_iff).mpr hx)

/-- The canonical `ℤ`-algebra map `ℤ[ζ_n] → ℂ`. -/
def iota (n : ℕ) [NeZero n] : CycloRing n →+* ℂ :=
  AdjoinRoot.lift (Int.castRingHom ℂ) (Complex.exp (2 * Real.pi * Complex.I / n))
    (eval₂_cyclotomic_eq_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n))
      (Complex.isPrimitiveRoot_exp n (NeZero.ne n)))

/-- A chosen primitive `n`-th root of unity in `k = F̄_r` (exists since `r ∤ n`). -/
def fieldRoot (r n : ℕ) [Fact r.Prime] (hrn : ¬ r ∣ n) : BrauerField r :=
  haveI : NeZero ((n : ℕ) : ZMod r) :=
    ⟨fun hh => hrn ((CharP.cast_eq_zero_iff (ZMod r) r n).mp hh)⟩
  Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot (BrauerField r) n)

theorem fieldRoot_spec (r n : ℕ) [Fact r.Prime] (hrn : ¬ r ∣ n) :
    IsPrimitiveRoot (fieldRoot r n hrn) n :=
  haveI : NeZero ((n : ℕ) : ZMod r) :=
    ⟨fun hh => hrn ((CharP.cast_eq_zero_iff (ZMod r) r n).mp hh)⟩
  Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot (BrauerField r) n)

/-- The canonical `ℤ`-algebra map `ℤ[ζ_n] → k` sending `ζ` to a fixed primitive `n`-th root. -/
def jred (r n : ℕ) [Fact r.Prime] (hrn : ¬ r ∣ n) :
    CycloRing n →+* BrauerField r :=
  AdjoinRoot.lift (Int.castRingHom (BrauerField r)) (fieldRoot r n hrn)
    (eval₂_cyclotomic_eq_zero _ (fun h => hrn ((CharP.cast_eq_zero_iff (BrauerField r) r n).mp h))
      (fieldRoot_spec r n hrn))

end Work.Hering.AppVII
