import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Idele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle norm (content) and the norm-one idèles

For a number field `K` and an idèle `x` we define its **content** `|x|` as the product over all
places of the normalized local absolute values `‖x_v‖_v`.  By the product formula
(`NumberField.prod_abs_eq_one`) the content of a principal idèle is `1`, so `Kˣ` is contained in
the subgroup `𝕀¹ K` of idèles of norm `1`.

## Main definitions

* `NK.GlobalCFT.Idele.localAbs`: the normalized local absolute value `K_vˣ →* ℝˣ`.
* `NK.GlobalCFT.Idele.abs`: the content `𝕀 K →* ℝˣ`.
* `NK.GlobalCFT.Idele.normOne`: the subgroup `𝕀¹ K = ker (abs)` of idèles of norm one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K : Type*} [Field K] [NumberField K]

/-- The normalized local absolute value at a place: the norm `‖·‖` at a finite place, and
`‖·‖ ^ w.mult` at an infinite place (so that the product over all places satisfies the product
formula).  Values are taken in the multiplicative group `ℝˣ` of nonzero reals. -/
def localAbs (K : Type*) [Field K] [NumberField K] :
    (v : Place K) → (Place.localField K v)ˣ →* ℝˣ
  | Sum.inl w =>
      { toFun := fun x =>
          (Units.mk0 ‖(x : w.Completion)‖ (norm_ne_zero_iff.mpr (Units.ne_zero x))) ^ w.mult
        map_one' := by
          ext
          simp
        map_mul' := by
          intro a b
          ext
          simp [mul_pow, norm_mul, Units.val_mul] }
  | Sum.inr q =>
      { toFun := fun x =>
          Units.mk0 ‖(x : q.adicCompletion K)‖ (norm_ne_zero_iff.mpr (Units.ne_zero x))
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [norm_mul, Units.val_mul] }

@[simp] theorem localAbs_ofFinite (q : HeightOneSpectrum (𝓞 K))
    (x : (q.adicCompletion K)ˣ) :
    localAbs K (Place.ofFinite q) x =
      Units.mk0 ‖(x : q.adicCompletion K)‖ (norm_ne_zero_iff.mpr (Units.ne_zero x)) := rfl

@[simp] theorem localAbs_ofInfinite (w : InfinitePlace K) (x : w.Completionˣ) :
    localAbs K (Place.ofInfinite w) x =
      (Units.mk0 ‖(x : w.Completion)‖ (norm_ne_zero_iff.mpr (Units.ne_zero x))) ^ w.mult := rfl

/-- At a finite place, the local absolute value of a local unit is `1`. -/
theorem localAbs_ofFinite_eq_one {q : HeightOneSpectrum (𝓞 K)}
    {y : (q.adicCompletion K)ˣ} (hy : y ∈ Place.localUnits K (Place.ofFinite q)) :
    localAbs K (Place.ofFinite q) y = 1 := by
  obtain ⟨hy1, hy2⟩ := (Place.mem_localUnits_ofFinite (q := q) (x := y)).mp hy
  have h1 : ‖(y : q.adicCompletion K)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hy1
  have h2 : ‖((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hy2
  have hmul : ‖(y : q.adicCompletion K)‖ *
      ‖((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)‖ = 1 := by
    have h1 : (y : q.adicCompletion K) *
        ((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K) = 1 := by simp
    rw [← norm_mul, h1, norm_one]
  have hle : ‖(y : q.adicCompletion K)‖ *
      ‖((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)‖ ≤ ‖(y : q.adicCompletion K)‖ * 1 :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  rw [mul_one] at hle
  have hy1' : ‖(y : q.adicCompletion K)‖ = 1 := by linarith
  rw [localAbs_ofFinite]
  ext
  simp [hy1']

/-- An idèle is a local unit at all but finitely many places, and at a finite place the local
absolute value of a local unit is `1`; hence the local absolute values of an idèle are `1`
at all but finitely many places. -/
theorem localAbs_eq_one_eventually (x : Idele K) :
    ∀ᶠ v in Filter.cofinite, localAbs K v (x v) = 1 := by
  rw [Filter.eventually_cofinite]
  have hInf : {v : Place K | Place.IsInfinite v}.Finite := by
    have h : {v : Place K | Place.IsInfinite v} = Set.range (Place.ofInfinite (K := K)) := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_range, Place.isInfinite_iff]
      exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩
    rw [h]
    exact Set.finite_range (Place.ofInfinite (K := K))
  have hBad : {v : Place K | x v ∉ Place.localUnits K v}.Finite :=
    Filter.eventually_cofinite.mp x.2
  refine Set.Finite.subset (hInf.union hBad) ?_
  intro v hv
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  rcases v with w | q
  · exact hcon.1 (Place.isInfinite_ofInfinite w)
  · exact hv (localAbs_ofFinite_eq_one (not_not.mp hcon.2))

/-- The **content** (or norm) of an idèle: the product of the normalized local absolute
values over all places; it is a finite product because an idèle is a local unit at all but
finitely many places. -/
def abs (K : Type*) [Field K] [NumberField K] : Idele K →* ℝˣ where
  toFun x := ∏ᶠ v, localAbs K v (x v)
  map_one' := by
    rw [show (fun v => localAbs K v ((1 : Idele K) v)) = fun _ => (1 : ℝˣ) from by
      funext v; simp]
    exact finprod_one
  map_mul' x y := by
    rw [show (fun v => localAbs K v ((x * y) v)) =
        fun v => localAbs K v (x v) * localAbs K v (y v) from by funext v; simp]
    exact finprod_mul_distrib (localAbs_eq_one_eventually x) (localAbs_eq_one_eventually y)

theorem abs_apply (x : Idele K) : abs K x = ∏ᶠ v, localAbs K v (x v) := rfl

/-- The subgroup `𝕀¹ K` of idèles of content `1`. -/
def normOne (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) := (abs K).ker

theorem mem_normOne {x : Idele K} : x ∈ normOne K ↔ abs K x = 1 := Iff.rfl

end Idele

end NK.GlobalCFT
