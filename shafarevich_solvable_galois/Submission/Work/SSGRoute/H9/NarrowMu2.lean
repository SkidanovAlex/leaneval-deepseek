import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
import Submission.Work.SSGRoute.ZDataTwo.SignAdjustment
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *narrow* modulus of the `p = 2` escape correction

The `p = 2` escape step of Schmidt--Wingberg §4 requires, besides the local data at `T` and the
unramifiedness away from the escape class, that the corrected class `b` **kills the involutions of
`G_K`** (the paper's "the modulus contains the real places").  With the wide subgroup
`gesU K p T' = im(Kˣ · E_{T,unr})` this clause is *not* implied by the escape construction: the
read-off element `γ` of the escape is determined only up to a unit which is a local `p`-th power at
the primes of `T'`, and the signs of those units are not free.

The fix is the *narrow* modulus: strengthen `E_{T,unr}` by the requirement that the **archimedean
components of the idèles be positive**.  Then

* every character of `C_K` killing the narrow `U` is trivial at every real place of `↥K`, so the
  archimedean summands of the two product formulas of the orthogonality argument vanish (this is
  what the wide odd-`p` proof gets from `isTotallyComplex_of_primitiveRoot`), and
* the **narrow read-off** produces `γ` *totally positive*: the archimedean component of
  `fracIdele 𝔵` is `1`, so `γ` is the inverse of the (positive) archimedean component of the
  `E`-factor of the decomposition — whence `b = a γ⁻¹` is totally positive as soon as the input
  `a` is, and its Kummer cochain kills the involutions.

This file sets up the vocabulary (`IsPosInf`, `narrowPowTIdeles`, `narrowGesU`) with its elementary
API, and proves the key positivity mechanism `pos_of_decomposition` (the missing input of the narrow
read-off); the arithmetic lemmas themselves (the narrow read-off, the narrow orthogonality, the
narrow escape prime) are stated in the companion files.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.H9

/-- The local field of `K` at an infinite place is the completion at that place. -/
theorem localField_ofInfinite {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) :
    Place.localField K (Place.ofInfinite w) = w.Completion := rfl

/-- **Positivity of a local unit at an infinite place.**  At a complex place the predicate is
vacuous; at a real place it says that the image of the unit under the real embedding is positive. -/
def IsPosInf (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K)
    (x : w.Completionˣ) : Prop :=
  ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion)

theorem isPosInf_one (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    IsPosInf K w (1 : w.Completionˣ) := by
  intro hw
  rw [show ((1 : w.Completionˣ) : w.Completion) = 1 by simp, map_one]
  norm_num

theorem IsPosInf.mul {K : Type*} [Field K] [NumberField K] {w : InfinitePlace K}
    {x y : w.Completionˣ} (hx : IsPosInf K w x) (hy : IsPosInf K w y) :
    IsPosInf K w (x * y) := by
  intro hw
  rw [Units.val_mul, map_mul]
  exact mul_pos (hx hw) (hy hw)

theorem IsPosInf.inv {K : Type*} [Field K] [NumberField K] {w : InfinitePlace K}
    {x : w.Completionˣ} (hx : IsPosInf K w x) : IsPosInf K w x⁻¹ := by
  intro hw
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact inv_pos.mpr (hx hw)

/-- **The narrow `E_{T,unr}`.**  The idèles of `powTIdeles K p T` whose archimedean components are
positive: the "the modulus contains the real places" strengthening of the escape modulus. -/
noncomputable def narrowPowTIdeles (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) : Subgroup (Idele K) where
  carrier := {x | x ∈ Work.SSGRoute.powTIdeles K p T ∧
    ∀ w : InfinitePlace K, IsPosInf K w (x (Place.ofInfinite w))}
  one_mem' := ⟨Subgroup.one_mem _, fun w => by
    rw [Idele.one_apply]
    exact isPosInf_one K w⟩
  mul_mem' := by
    rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun w => ?_⟩
    rw [Idele.mul_apply]
    exact (hpx w).mul (hpy w)
  inv_mem' := by
    rintro x ⟨hx, hpx⟩
    refine ⟨Subgroup.inv_mem _ hx, fun w => ?_⟩
    rw [Idele.inv_apply]
    exact (hpx w).inv

@[simp] theorem mem_narrowPowTIdeles {K : Type} [Field K] [NumberField K] {p : ℕ}
    {T : Finset (NK.Chebotarev.PrimeIdeal K)} {x : Idele K} :
    x ∈ narrowPowTIdeles K p T ↔
      x ∈ Work.SSGRoute.powTIdeles K p T ∧
        ∀ w : InfinitePlace K, IsPosInf K w (x (Place.ofInfinite w)) := Iff.rfl

/-- The narrow idèles lie in the wide `E_{T,unr}`. -/
theorem narrowPowTIdeles_le_powTIdeles {K : Type} [Field K] [NumberField K] (p : ℕ)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    narrowPowTIdeles K p T ≤ Work.SSGRoute.powTIdeles K p T :=
  fun _ hx => hx.1

/-- **The narrow `U`**: the image in `C_K` of `Kˣ · E^{narrow}_{T,unr}`, i.e. the class field of the
narrow escape modulus. -/
noncomputable def narrowGesU (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) : Subgroup (IdeleClassGroup K) :=
  (Idele.principalSubgroup K ⊔ narrowPowTIdeles K p T').map (IdeleClassGroup.mk K)

/-- Membership in the narrow `U` in idèle form. -/
theorem mem_narrowGesU_iff {K : Type} [Field K] [NumberField K] {p : ℕ}
    {T' : Finset (NK.Chebotarev.PrimeIdeal K)} {y : Idele K} :
    IdeleClassGroup.mk K y ∈ narrowGesU K p T' ↔
      ∃ c : Idele K, c ∈ Idele.principalSubgroup K ⊔ narrowPowTIdeles K p T' ∧
        IdeleClassGroup.mk K c = IdeleClassGroup.mk K y :=
  ⟨fun h => Subgroup.mem_map.mp h, fun ⟨c, hc, hcy⟩ => Subgroup.mem_map.mpr ⟨c, hc, hcy⟩⟩

/-- The narrow `U` is contained in the wide `gesU`. -/
theorem narrowGesU_le_gesU {K : Type} [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    narrowGesU K p T' ≤ GrunwaldEscapeCore.gesU K p T' := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
  have hc' : c ∈ (Idele.principalSubgroup K : Subgroup (Idele K)) ⊔ narrowPowTIdeles K p T' := hc
  have hc'' := (Subgroup.mem_sup (s := Idele.principalSubgroup K)
    (t := narrowPowTIdeles K p T')).mp hc'
  obtain ⟨u, hu, v, hv, huv⟩ := hc''
  refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
  refine Subgroup.mem_sup.mpr ⟨u, hu, v, ?_, huv⟩
  exact narrowPowTIdeles_le_powTIdeles p T' hv

/-- The archimedean component of the idèle of a fractional ideal is `1`. -/
theorem fracIdele_ofInfinite {K : Type} [Field K] [NumberField K]
    (𝔵 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (w : InfinitePlace K) :
    NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 (Place.ofInfinite w) = 1 := rfl

/-- The archimedean component of the principal idèle of `γ` is the image of `γ`. -/
theorem principalIdele_ofInfinite_coe {K : Type} [Field K] [NumberField K]
    (γ : Kˣ) (w : InfinitePlace K) :
    ((Idele.principalIdele K γ (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion)
      = algebraMap K w.Completion (γ : K) := by
  rw [Idele.principalIdele_apply]
  rfl

/-- **The positivity mechanism of the narrow read-off.**  If `a = (γ) · e` as idèles with `e` in
the narrow `E_{T,unr}`, and if the archimedean components of `a` are all `1` (which holds in
particular for `a = fracIdele 𝔵`), then `γ` is positive at every real place of `K`.

This is the missing input of the wide read-off `Work.SSGRoute.EscapeCoreLib.readOffSupPow`: with the
narrow modulus, the read-off element of the correction `b = a γ⁻¹` is totally positive, so `b` is
totally positive whenever the input `a` is, and its Kummer cochain kills the involutions of `G_K`. -/
theorem pos_of_decomposition {K : Type} [Field K] [NumberField K] {γ : Kˣ} {e a : Idele K}
    (hae : Idele.principalIdele K γ * e = a)
    (he : ∀ w : InfinitePlace K, IsPosInf K w (e (Place.ofInfinite w)))
    (ha : ∀ w : InfinitePlace K, a (Place.ofInfinite w) = 1)
    (w : InfinitePlace K) (hw : w.IsReal) :
    0 < InfinitePlace.embedding_of_isReal hw (γ : K) := by
  set ρ := InfinitePlace.Completion.ringEquivRealOfIsReal hw with hρ
  -- the identity at the infinite place `w`
  have hcomp : Idele.principalIdele K γ (Place.ofInfinite w) * e (Place.ofInfinite w)
      = (1 : (Place.localField K (Place.ofInfinite w))ˣ) := by
    rw [← Idele.mul_apply, hae, ha w]
  -- the value of `ρ` on the two factors
  have hγ : ρ (((Idele.principalIdele K γ (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion))
      = InfinitePlace.embedding_of_isReal hw (γ : K) := by
    rw [show (((Idele.principalIdele K γ (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion))
        = algebraMap K w.Completion (γ : K) from principalIdele_ofInfinite_coe γ w]
    exact ZDataTwo.ringEquivRealOfIsReal_algebraMap_eq w hw (γ : K)
  have hepos : 0 < ρ (((e (Place.ofInfinite w) :
      (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion)) := he w hw
  -- multiply and conclude
  have hprod : InfinitePlace.embedding_of_isReal hw (γ : K)
      * ρ (((e (Place.ofInfinite w) :
          (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion)) = 1 := by
    have h := congrArg (fun u : (Place.localField K (Place.ofInfinite w))ˣ =>
      ρ (u : w.Completion)) hcomp
    rw [Units.val_mul, map_mul, Units.val_one, map_one, hγ] at h
    exact h
  nlinarith [hprod, hepos]

end Work.SSGRoute.H9
