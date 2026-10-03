/-
Shared definitions for the construction of the `∗`-regular envelope of the natural extension
[JZLA20, §3.2].
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.skewToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul
import Submission.Work.ORHughesFree.Epic

set_option autoImplicit false
universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The twist `τ` of `U[t^{±1};τ]` is compatible with the involution of `U`: this is the
hypothesis `hstar` of the main theorem. -/
class StarAction (U : Type u) [Ring U] [StarRing U]
    [MulSemiringAction (Multiplicative ℤ) U] : Prop where
  /-- `τ` commutes with `star`. -/
  map_smul : ∀ (n : Multiplicative ℤ) (x : U), star (n • x) = n • star x

/-- The involution on `U[t^{±1};τ]` with `t^* = t^{-1}`, i.e. `(star p)_m = m • star (p_{m⁻¹})`,
expressed on the underlying `Finsupp`: `star p = ∑_m single m⁻¹ (m⁻¹ • star (p m))`. -/
noncomputable def starSkewL {U : Type u} [AddCommMonoid U] [Star U] [SMul (Multiplicative ℤ) U]
    (p : SkewMonoidAlgebra U (Multiplicative ℤ)) : SkewMonoidAlgebra U (Multiplicative ℤ) :=
  p.sum fun m a => SkewMonoidAlgebra.single m⁻¹ (m⁻¹ • star a)

/-- The product of matrix rings `∏_{n ≥ 1} M_n(U)`. -/
abbrev W (U : Type u) : Type u := (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) U

/-- The `n`-th Toeplitz matrix of `p`, as an element of `W U`. -/
noncomputable def toeplitzFamily {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (p : SkewL U) : W U := fun n => toeplitz (n+1) p

/-- Pointwise block flattening of a matrix over `W U`. -/
noncomputable def flatW {U : Type u} (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)) :
    (n : ℕ) → Matrix (Fin (k * (n+1))) (Fin (m * (n+1))) U :=
  fun n => flattenBlocks (fun i j => A i j n)

/-- The ultralimit rank on `W U`: the ultralimit of the ranks of the flattened matrices
normalized by `n+1`. -/
noncomputable def blimRank {U : Type u} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)) : ℝ :=
  blim ω (fun n => rk.rk (k * (n+1)) (m * (n+1)) (flatW k m A n) / ((n+1 : ℕ) : ℝ))

/-- The family of Toeplitz matrices of the entries of a matrix over `U[t^{±1};τ]`. -/
noncomputable def toeplitzMatrix {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {k m : ℕ} (A : Matrix (Fin k) (Fin m) (SkewL U)) : Matrix (Fin k) (Fin m) (W U) :=
  fun i j => toeplitzFamily (A i j)

/-- The block flattening of the Toeplitz family of `A` is the truncation `trunc n A`. -/
theorem flatW_toeplitzMatrix {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {k m : ℕ} (A : Matrix (Fin k) (Fin m) (SkewL U)) (n : ℕ) :
    flatW k m (toeplitzMatrix A) n = trunc (n+1) A := by
  ext x y
  rw [trunc_apply]
  simp only [flatW, toeplitzMatrix, toeplitzFamily, flattenBlocks, toeplitz,
    finProdFinEquiv_symm_apply]
  rfl

/-- The involution on the underlying subtype of a `∗`-subring, presented through its
underlying `Subring`.  This is definitionally the instance `StarRing ↥V` of a `StarSubring`, but
instance search does not unfold the coercion `↑V` to `V.toSubring`, so it is registered
separately. -/
instance instStarRingSubringCoe {U : Type u} [Ring U] [StarRing U] (V : StarSubring U) :
    StarRing ↥(V.toSubring) :=
  inferInstanceAs (StarRing ↥V)

/-- The composition of a ring homomorphism into a `∗`-ring with the inclusion of the `∗`-regular
closure of its image. -/
noncomputable def closureCorestrict {S P : Type u} [Ring S] [StarRing S] [Ring P] [StarRing P]
    (φ : S →+* P) :
    S →+* ↥(starRegularClosure (starSubringClosure (Set.range φ))) :=
  φ.codRestrict ((starRegularClosure (starSubringClosure (Set.range φ))).toSubring)
    (fun s => Work.ORHughesFree.subset_starRegularClosure _
      (Work.ORHughesFree.subset_starSubringClosure _ (Set.mem_range_self s)))


/-! ## The involution on a quotient by a `∗`-closed ideal -/

/-- The involution on `R ⧸ I` induced by the involution of `R`, defined on representatives using
`Quotient.out`. -/
noncomputable def starQuot {R : Type u} [Ring R] [StarRing R] (I : Ideal R) [I.IsTwoSided]
    (x : R ⧸ I) : R ⧸ I :=
  Ideal.Quotient.mk I (star (Quotient.out x))

/-- The induced involution of the quotient is computed on representatives. -/
theorem starQuot_mk {R : Type u} [Ring R] [StarRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, star x ∈ I) [I.IsTwoSided] (a : R) :
    starQuot I (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) := by
  unfold starQuot
  rw [Ideal.Quotient.eq]
  have h1 : Quotient.out (Ideal.Quotient.mk I a) - a ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have h2 : star (Quotient.out (Ideal.Quotient.mk I a)) - star a =
      star (Quotient.out (Ideal.Quotient.mk I a) - a) :=
    (star_sub _ _).symm
  rw [h2]
  exact hI _ h1

/-- The involution of a `∗`-ring descends to the quotient by any `∗`-closed two-sided ideal. -/
@[reducible] noncomputable def starRingQuotient {R : Type u} [Ring R] [StarRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, star x ∈ I) [I.IsTwoSided] : StarRing (R ⧸ I) where
  star := starQuot I
  star_involutive x := by
    rw [← Ideal.Quotient.mk_out (I := I) x]
    rw [starQuot_mk I hI, starQuot_mk I hI]
    simp
  star_mul a b := by
    rw [← Ideal.Quotient.mk_out (I := I) a, ← Ideal.Quotient.mk_out (I := I) b]
    rw [← map_mul]
    rw [starQuot_mk I hI (Quotient.out a * Quotient.out b)]
    rw [star_mul]
    rw [map_mul, starQuot_mk I hI, starQuot_mk I hI]
  star_add a b := by
    rw [← Ideal.Quotient.mk_out (I := I) a, ← Ideal.Quotient.mk_out (I := I) b]
    rw [← map_add]
    rw [starQuot_mk I hI (Quotient.out a + Quotient.out b)]
    rw [star_add]
    rw [map_add, starQuot_mk I hI, starQuot_mk I hI]

end Work.ORHughesFree.NaturalExtension
