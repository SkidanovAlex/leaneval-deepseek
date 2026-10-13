import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs

/-!
# DSM5b — concrete coordinates for the degree-`0` part of the chart Čech complexes

This file provides the *honest* (unperfected) counterparts of the concrete objects
`Work.DSM5b.PCX` / `Work.DSM5b.PCd` of `Submission/Work/DSM5b/PerfComplexDefs.lean`:

* `HCX t m = ∀ τ : Fin (m+1) → ι, chartRing t (tupRng τ)` — the terms of the honest chart Čech
  complex in coordinates;
* `rhoH t h : chartRing t S →ₐ[R] chartRing t T` for `h : S ⊆ T` — the restriction map;
* `HCd t m` — the alternating coface differential, `(HCd z) τ = Σ i, (-1)^i • rhoH (z (tupDel i τ))`.

The point is that the coordinate-equivalence statements
`Work.DSM5b.perfCechCoordEquiv` (perfected) and `Work.DSM5b.honestCechCoordEquiv` (honest),
both expressed against these concrete objects, let the analysis of the chart Čech complexes be
carried out with explicit formulas on tuples rather than by unfolding `cechComplexFunctor`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Hon

variable {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R]

/-- The localisation map between honest chart rings, restricted to the subalgebras. -/
noncomputable def rhoH (t : ι → R) {S T : Finset ι} (h : S ⊆ T) :
    chartRing t S →ₐ[R] chartRing t T where
  toFun x := ⟨locRes t h x.1, chartRing_map_le t h ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (locRes t h))
  map_mul' x y := Subtype.ext (map_mul (locRes t h) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (locRes t h))
  map_add' x y := Subtype.ext (map_add (locRes t h) x.1 y.1)
  commutes' r := Subtype.ext ((locRes t h).commutes r)

@[simp] lemma rhoH_coe (t : ι → R) {S T : Finset ι} (h : S ⊆ T) (x : chartRing t S) :
    (rhoH t h x : Localization.Away (tS t T)) = locRes t h x.1 := rfl

/-- Terms of the honest concrete chart Čech complex. -/
noncomputable abbrev HCX (t : ι → R) (m : ℕ) : Type a :=
  ∀ τ : Fin (m + 1) → ι, chartRing t (tupRng τ)

/-- The alternating coface differential of the honest concrete complex, in coordinates. -/
noncomputable def HCd (t : ι → R) (m : ℕ) : HCX t m →ₗ[R] HCX t (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) • rhoH t (tupRng_del_subset i τ) (z (tupDel i τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

@[simp] lemma HCd_apply (t : ι → R) (m : ℕ) (z : HCX t m) (τ : Fin (m + 2) → ι) :
    HCd t m z τ = ∑ i : Fin (m + 2),
      ((-1 : R) ^ ((i : ℕ))) • rhoH t (tupRng_del_subset i τ) (z (tupDel i τ)) := rfl

/-- The concrete coaugmentation `R → HCX t 0` of the honest tuple complex: the constant family
through the algebra map. -/
noncomputable def HCcoaug (t : ι → R) (w : R) : HCX t 0 :=
  fun τ => ⟨algebraMap R (Localization.Away (tS t (tupRng τ))) w,
    (chartRing t (tupRng τ)).algebraMap_mem w⟩

end Hon

section Perf

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type a} [DecidableEq ι]

/-- The concrete coaugmentation `R → PCX p t 0` of the perfected tuple complex. -/
noncomputable def PCcoaug (t : ι → R) (w : R) : PCX p t 0 :=
  fun τ => ⟨algebraMap R (Localization.Away (tS t (tupRng τ))) w,
    (perfChartRing p t (tupRng τ)).algebraMap_mem w⟩

end Perf

end Work.DSM5b
