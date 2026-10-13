import Submission.Work.DSM5b.HCF.Basic

/-!
# The "sorted" (increasing tuple) complex of a coefficient system and the comparison map

For a coefficient system `𝒜` on the subsets of a linearly ordered index type `ι`, the *sorted*
complex has the same terms as the honest tuple complex, but its cochains are only required on
*increasing* tuples:

  `Stc 𝒜 m = ∏_{τ : Fin (m+1) → ι increasing} 𝒜.M (tupRng τ)`,

and the differential is the same formula as `CoeffSys.htcD` (deleting a coordinate of an increasing
tuple leaves it increasing, so the formula makes sense).  The *comparison map* `toStc : Htc 𝒜 → Stc 𝒜`
is the restriction map `z ↦ (fun τ => z τ.1)`, and it is a chain map.

This is the intermediate object between the honest (tuple-indexed) complex, whose cohomology is the
one of the target `Work.DSM5b.honestCohomologyFinite`, and the *subset-indexed* alternating chart
Čech complex of the area `DSCOH` (whose cohomology is known to be finitely generated when the
coefficient system is the degree-zero part of a finitely generated graded module, see
`Work.DSCOH.chartCech_finite_vanishing`).
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] [LinearOrder ι]

/-- A tuple is *increasing* if its entries are strictly increasing. -/
def IsIncr {m : ℕ} (τ : Fin (m + 1) → ι) : Prop := ∀ i j, i < j → τ i < τ j

lemma IsIncr.tupDel {m : ℕ} {τ : Fin (m + 2) → ι} (h : IsIncr τ) (i : Fin (m + 2)) :
    IsIncr (tupDel i τ) := by
  intro a b hab
  rw [tupDel_apply, tupDel_apply]
  exact h _ _ ((Fin.succAbove_lt_succAbove_iff).mpr hab)

/-- The increasing tuples of length `m+1`. -/
abbrev IncrTuple (m : ℕ) : Type a := {τ : Fin (m + 1) → ι // IsIncr τ}

/-- The terms of the sorted complex: cochains on the increasing tuples. -/
abbrev Stc (𝒜 : CoeffSys R ι) (m : ℕ) : Type a := ∀ τ : IncrTuple (ι := ι) m, 𝒜.M (tupRng τ.1)

/-- The differential of the sorted complex. -/
noncomputable def stcD (𝒜 : CoeffSys R ι) (m : ℕ) : Stc 𝒜 m →ₗ[R] Stc 𝒜 (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) •
      𝒜.res (tupRng_del_subset i τ.1) (z ⟨tupDel i τ.1, τ.2.tupDel i⟩)
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

/-- The comparison map from the honest tuple complex to the sorted complex. -/
noncomputable def toStc (𝒜 : CoeffSys R ι) (m : ℕ) : 𝒜.Htc m →ₗ[R] Stc 𝒜 m where
  toFun z := fun τ => z τ.1
  map_add' z z' := rfl
  map_smul' r z := rfl

@[simp] lemma toStc_apply (𝒜 : CoeffSys R ι) (m : ℕ) (z : 𝒜.Htc m) (τ : IncrTuple (ι := ι) m) :
    toStc 𝒜 m z τ = z τ.1 := rfl

/-- The comparison map is a morphism of complexes. -/
lemma toStc_comm (𝒜 : CoeffSys R ι) (m : ℕ) :
    (stcD 𝒜 m).comp (toStc 𝒜 m) = (toStc 𝒜 (m + 1)).comp (CoeffSys.htcD (𝒜 := 𝒜) m) := by
  apply LinearMap.ext
  intro z
  funext τ
  rfl

end Work.DSM5b
