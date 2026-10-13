import Submission.Work.DSM5b.HCF.Basic

/-!
# Sub-systems and quotient coefficient systems

A *sub-system* of a coefficient system `𝒜` is a family of submodules `N S ≤ 𝒜.M S` stable under
the restriction maps.  It is itself a coefficient system (`SubSys.toCoeff`), and the quotient
modules `𝒜.M S ⧸ N S` form the *quotient* coefficient system (`SubSys.quot`), with the maps
`SubSys.quotRes` induced by `Submodule.mapQ` (well defined because the sub-system is stable under
restrictions).

These are the ingredients of the size filtration of a coefficient system used to compare the honest
tuple complex with the sorted (increasing-tuple) one: the filtration
`0 ≤ 𝒜_{≥|ι|} ≤ … ≤ 𝒜_{≥0} = 𝒜` (with `𝒜_{≥k}` the sub-system of the coefficients supported on the
subsets of size at least `k`) has, for consecutive quotients, the systems supported on the subsets of
a *single* size, whose honest complexes are direct sums of the "surjection complexes"
(`Submission/Work/DSM5b/HCF/Surj.lean`).
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

namespace CoeffSys

/-- A sub-system of a coefficient system: a family of submodules stable under the restrictions. -/
structure SubSys (𝒜 : CoeffSys R ι) where
  N : ∀ S, Submodule R (𝒜.M S)
  res_mem : ∀ ⦃S T : Finset ι⦄ (h : S ⊆ T) ⦃x : 𝒜.M S⦄, x ∈ N S → 𝒜.res h x ∈ N T

/-- The sub-system, as a coefficient system (the submodules with the restricted maps). -/
noncomputable def SubSys.toCoeff (𝒜 : CoeffSys R ι) (𝒮 : 𝒜.SubSys) : CoeffSys R ι where
  M := fun S => ↥(𝒮.N S)
  inst₁ := fun _ => inferInstance
  inst₂ := fun _ => inferInstance
  res := fun {_ _} h =>
    { toFun := fun x => ⟨𝒜.res h x.1, 𝒮.res_mem h x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro r x; ext; simp }
  res_self := by
    intro S
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact 𝒜.res_self_apply x.1
  res_comp := by
    intro S T V h₁ h₂
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact 𝒜.res_comp_apply h₁ h₂ x.1

/-- The quotient restriction map `𝒜.M S ⧸ 𝒮.N S → 𝒜.M T ⧸ 𝒮.N T` for `S ⊆ T`, induced by
`𝒜.res h`. -/
noncomputable def SubSys.quotRes (𝒜 : CoeffSys R ι) (𝒮 : 𝒜.SubSys) {S T : Finset ι} (h : S ⊆ T) :
    (𝒜.M S ⧸ 𝒮.N S) →ₗ[R] (𝒜.M T ⧸ 𝒮.N T) :=
  Submodule.mapQ (𝒮.N S) (𝒮.N T) (𝒜.res h) (fun x hx => 𝒮.res_mem h hx)

/-- The quotient restriction map, evaluated at a representative. -/
@[simp] lemma SubSys.quotRes_mkQ (𝒜 : CoeffSys R ι) (𝒮 : 𝒜.SubSys) {S T : Finset ι} (h : S ⊆ T)
    (m : 𝒜.M S) :
    𝒮.quotRes 𝒜 h (Quotient.mk (Submodule.quotientRel (𝒮.N S)) m) =
      Quotient.mk (Submodule.quotientRel (𝒮.N T)) (𝒜.res h m) := rfl

/-- The quotient coefficient system by a sub-system. -/
noncomputable def SubSys.quot (𝒜 : CoeffSys R ι) (𝒮 : 𝒜.SubSys) : CoeffSys R ι where
  M := fun S => 𝒜.M S ⧸ 𝒮.N S
  inst₁ := fun _ => inferInstance
  inst₂ := fun _ => inferInstance
  res := fun {_ _} h => 𝒮.quotRes 𝒜 h
  res_self := by
    intro S
    apply LinearMap.ext
    intro x
    induction x using Quotient.inductionOn with
    | _ m =>
      simp only [SubSys.quotRes_mkQ, 𝒜.res_self_apply, LinearMap.id_apply]
  res_comp := by
    intro S T V h₁ h₂
    apply LinearMap.ext
    intro x
    induction x using Quotient.inductionOn with
    | _ m =>
      simp only [LinearMap.comp_apply, SubSys.quotRes_mkQ, 𝒜.res_comp_apply]

/-- The sub-system of the coefficients supported on subsets of size at least `k`. -/
noncomputable def sizeSubSys (𝒜 : CoeffSys R ι) (k : ℕ) : 𝒜.SubSys where
  N := fun S => if k ≤ S.card then ⊤ else ⊥
  res_mem := by
    intro S T h x hx
    by_cases hk : k ≤ T.card
    · rw [if_pos hk]
      exact Submodule.mem_top
    · have hcard : S.card ≤ T.card := Finset.card_le_card h
      have hkS : ¬ k ≤ S.card := by omega
      rw [if_neg hkS] at hx
      have hx0 : x = 0 := (Submodule.mem_bot R).mp hx
      rw [hx0, map_zero]
      exact Submodule.zero_mem _

/-- The consecutive terms of the size filtration are nested: the coefficients supported on
subsets of size at least `k+1` form a sub-system of those supported on subsets of size at least `k`.
This is the inclusion whose cokernel is the "exactly `k`" system. -/
lemma sizeSubSys_mono (𝒜 : CoeffSys R ι) (k : ℕ) (S : Finset ι) :
    (sizeSubSys 𝒜 (k + 1)).N S ≤ (sizeSubSys 𝒜 k).N S := by
  by_cases hk : k ≤ S.card
  · rw [show (sizeSubSys 𝒜 k).N S = ⊤ from if_pos hk]
    exact le_top
  · have hlt : S.card < k := Nat.lt_of_not_le hk
    rw [show (sizeSubSys 𝒜 k).N S = ⊥ from if_neg hk,
      show (sizeSubSys 𝒜 (k + 1)).N S = ⊥ from if_neg (by omega)]

-- The "exactly `k`" coefficient system (the cokernel of `sizeSubSys_mono`) is the quotient of
-- `(sizeSubSys 𝒜 k).toCoeff 𝒜` by the sub-system induced by `sizeSubSys 𝒜 (k+1)`; its honest
-- complex is the direct sum, over the `k`-element subsets `S₀`, of the "surjection complexes"
-- (`Work.DSM5b.SurjTerm`/`Work.DSM5b.surjD`), whose cohomology is computed by
-- `Work.DSM5b.HCF.surj_cohomology`.

end CoeffSys

end Work.DSM5b
