import Submission.Work.DSM5b.HCF.SubSys

/-!
# The size filtration of a coefficient system and its consecutive quotients

For a coefficient system `𝒜`, the sub-systems `sizeSubSys 𝒜 k` (coefficients supported on subsets of
size at least `k`) are nested by `sizeSubSys_mono`, and the consecutive quotient

  `exactlyCoeff 𝒜 k`

is the coefficient system supported on the subsets of size *exactly* `k`: the quotient of
`(sizeSubSys 𝒜 k).toCoeff 𝒜` by the range of the inclusion of `sizeSubSys 𝒜 (k+1)` (the sub-system
`nextSizeSub`).

On the honest tuple complexes this yields the maps

  `sizeIncl 𝒜 k m : Htc (𝒜_{≥k+1}) m →ₗ Htc (𝒜_{≥k}) m`
  `sizeQuot 𝒜 k m : Htc (𝒜_{≥k}) m →ₗ Htc (exactlyCoeff 𝒜 k) m`

which are the terms of the short exact sequence of complexes
`0 → Htc (𝒜_{≥k+1}) → Htc (𝒜_{≥k}) → Htc (𝒜_{=k}) → 0`; the cohomology of the third complex is a
direct sum of "surjection complexes" (`Submission/Work/DSM5b/HCF/Surj.lean`), whose cohomology is
computed by `Work.DSM5b.HCF.surj_cohomology`.

## Obstruction encountered (recorded so that it is not rediscovered)

Writing `exactlyCoeff 𝒜 k` as the quotient `(nextSizeSub).quot ((sizeSubSys 𝒜 k).toCoeff 𝒜)` — i.e.
taking the *sub-system* `(sizeSubSys 𝒜 k).toCoeff 𝒜` as the ambient system and quotienting by the
image of `sizeSubSys 𝒜 (k+1)` — does not elaborate: the field types of `SubSys ((…).toCoeff 𝒜)`
require the instance `Module R ((SubSys.toCoeff 𝒜 (sizeSubSys 𝒜 k)).M S)`, and type class search
fails to unfold `SubSys.toCoeff`'s `M := fun S => ↥(𝒮.N S)` to reach the subtype instance (the error
is `failed to synthesize instance of type class Module R (…M S)`, with the ambient module still
containing metavariables).  Adding the instance fields explicitly to `SubSys.toCoeff` does not help.

**Fix to use next:** define `exactlyCoeff` *directly*, with the modules

  `fun S => ↥((sizeSubSys 𝒜 k).N S) ⧸ (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range`

spelled out (so that no `toCoeff`-as-ambient is involved), and the restriction maps induced on the
quotients by `Submodule.liftQ`.  The maps `sizeIncl`/`sizeQuot` on `Htc` are then termwise the
inclusion and the quotient map of modules, and the exactness of the filtration SES is termwise the
exactness of `0 → ↥(N_{k+1} S) → ↥(N_k S) → ↥(N_k S) ⧸ image → 0`.

-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

namespace CoeffSys

/-- The restriction map of the size sub-system, with the ambient module spelled out as the subtype
`↥((sizeSubSys 𝒜 k).N S)` (so that no `CoeffSys` projection is involved in the types). -/
noncomputable def sizeRestrict (𝒜 : CoeffSys R ι) (k : ℕ) {S T : Finset ι} (h : S ⊆ T) :
    ↥((sizeSubSys 𝒜 k).N S) →ₗ[R] ↥((sizeSubSys 𝒜 k).N T) where
  toFun x := ⟨𝒜.res h x.1, (sizeSubSys 𝒜 k).res_mem h x.2⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp] lemma sizeRestrict_apply (𝒜 : CoeffSys R ι) (k : ℕ) {S T : Finset ι} (h : S ⊆ T)
    (x : ↥((sizeSubSys 𝒜 k).N S)) :
    (sizeRestrict 𝒜 k h x : 𝒜.M T) = 𝒜.res h (x : 𝒜.M S) := rfl

lemma sizeRestrict_self (𝒜 : CoeffSys R ι) (k : ℕ) (S : Finset ι) :
    sizeRestrict 𝒜 k (le_refl S) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (𝒜.res_self_apply x.1)

lemma sizeRestrict_comp (𝒜 : CoeffSys R ι) (k : ℕ) {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V)
    (x : ↥((sizeSubSys 𝒜 k).N S)) :
    sizeRestrict 𝒜 k h₂ (sizeRestrict 𝒜 k h₁ x) = sizeRestrict 𝒜 k (h₁.trans h₂) x := by
  exact Subtype.ext (𝒜.res_comp_apply h₁ h₂ x.1)

/-- `sizeRestrict` maps the image of the smaller size sub-system into the image of the smaller size
sub-system: the naturality of the inclusion. -/
lemma sizeRestrict_inclusion (𝒜 : CoeffSys R ι) (k : ℕ) {S T : Finset ι} (h : S ⊆ T)
    (y : ↥((sizeSubSys 𝒜 (k + 1)).N S)) :
    sizeRestrict 𝒜 k h (Submodule.inclusion (sizeSubSys_mono 𝒜 k S) y) =
      Submodule.inclusion (sizeSubSys_mono 𝒜 k T)
        ⟨𝒜.res h y.1, (sizeSubSys 𝒜 (k + 1)).res_mem h y.2⟩ := by
  exact Subtype.ext rfl

/-- The restriction map of the "exactly `k`" system, induced on the quotients by
`sizeRestrict`: it is well defined because `sizeRestrict` maps the image of the smaller size
sub-system into the image of the smaller size sub-system (`sizeRestrict_inclusion`). -/
noncomputable def exactlyCoeffRes (𝒜 : CoeffSys R ι) (k : ℕ) {S T : Finset ι} (h : S ⊆ T) :
    ↥((sizeSubSys 𝒜 k).N S) ⧸ (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range →ₗ[R]
      ↥((sizeSubSys 𝒜 k).N T) ⧸ (Submodule.inclusion (sizeSubSys_mono 𝒜 k T)).range :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (sizeRestrict 𝒜 k h)) (by
    intro x hx
    obtain ⟨y, -, hyx⟩ := LinearMap.mem_range.mp hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, sizeRestrict_inclusion]
    simp)

/-- The restriction map of the "exactly `k`" system, evaluated at a representative. -/
@[simp] lemma exactlyCoeffRes_mkQ (𝒜 : CoeffSys R ι) (k : ℕ) {S T : Finset ι} (h : S ⊆ T)
    (m : ↥((sizeSubSys 𝒜 k).N S)) :
    exactlyCoeffRes 𝒜 k h
        (Submodule.mkQ (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range m) =
      Submodule.mkQ (Submodule.inclusion (sizeSubSys_mono 𝒜 k T)).range
        (sizeRestrict 𝒜 k h m) := rfl

/-- The "exactly `k`" coefficient system: the coefficients supported on the subsets of size exactly
`k`, i.e. the quotient of the coefficients supported on the subsets of size at least `k` by those
supported on the subsets of size at least `k+1`. -/
noncomputable def exactlyCoeff (𝒜 : CoeffSys R ι) (k : ℕ) : CoeffSys R ι where
  M := fun S => ↥((sizeSubSys 𝒜 k).N S) ⧸ (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range
  res := fun {_ _} h => exactlyCoeffRes 𝒜 k h
  res_self := by
    intro S
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range x
    simp only [exactlyCoeffRes_mkQ, LinearMap.comp_apply, sizeRestrict_self,
      LinearMap.id_apply]
  res_comp := by
    intro S T V h₁ h₂
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (Submodule.inclusion (sizeSubSys_mono 𝒜 k S)).range x
    simp only [LinearMap.comp_apply, exactlyCoeffRes_mkQ, sizeRestrict_comp]

/-- The terms of the `k`-th stage of the size filtration, with the modules spelled out (no
`CoeffSys` projection in the types). -/
abbrev SizeC (𝒜 : CoeffSys R ι) (k m : ℕ) : Type a :=
  ∀ τ : Fin (m + 1) → ι, ↥((sizeSubSys 𝒜 k).N (tupRng τ))

/-- The differential of the `k`-th stage of the size filtration (the honest tuple differential of
the sub-system, with the restriction maps `sizeRestrict`). -/
noncomputable def sizeD (𝒜 : CoeffSys R ι) (k m : ℕ) : SizeC 𝒜 k m →ₗ[R] SizeC 𝒜 k (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) • sizeRestrict 𝒜 k (tupRng_del_subset i τ) (z (tupDel i τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

/-- The termwise inclusion of the stages of the size filtration. -/
noncomputable def sizeIncl (𝒜 : CoeffSys R ι) (k m : ℕ) :
    SizeC 𝒜 (k + 1) m →ₗ[R] SizeC 𝒜 k m where
  toFun z := fun τ => ⟨(z τ).1, sizeSubSys_mono 𝒜 k (tupRng τ) (z τ).2⟩
  map_add' z z' := by
    funext τ
    exact Subtype.ext rfl
  map_smul' r z := by
    funext τ
    exact Subtype.ext rfl

@[simp] lemma sizeIncl_apply (𝒜 : CoeffSys R ι) (k m : ℕ) (z : SizeC 𝒜 (k + 1) m)
    (τ : Fin (m + 1) → ι) :
    ((sizeIncl 𝒜 k m z τ : ↥((sizeSubSys 𝒜 k).N (tupRng τ))) : 𝒜.M (tupRng τ)) =
      (z τ : 𝒜.M (tupRng τ)) := rfl

/-- The terms of the consecutive quotient (the "exactly `k`" stage), with the modules spelled out. -/
abbrev SizeQ (𝒜 : CoeffSys R ι) (k m : ℕ) : Type a :=
  ∀ τ : Fin (m + 1) → ι,
    ↥((sizeSubSys 𝒜 k).N (tupRng τ)) ⧸ (Submodule.inclusion (sizeSubSys_mono 𝒜 k (tupRng τ))).range

/-- The termwise quotient map of the stages of the size filtration. -/
noncomputable def sizeQuot (𝒜 : CoeffSys R ι) (k m : ℕ) : SizeC 𝒜 k m →ₗ[R] SizeQ 𝒜 k m where
  toFun z := fun τ => Submodule.mkQ _ (z τ)
  map_add' z z' := by
    funext τ
    exact map_add (Submodule.mkQ _) (z τ) (z' τ)
  map_smul' r z := by
    funext τ
    exact map_smul (Submodule.mkQ _) r (z τ)

/-- The differential of the consecutive-quotient ("exactly `k`") stage of the size filtration. -/
noncomputable def sizeDq (𝒜 : CoeffSys R ι) (k m : ℕ) : SizeQ 𝒜 k m →ₗ[R] SizeQ 𝒜 k (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) • exactlyCoeffRes 𝒜 k (tupRng_del_subset i τ) (z (tupDel i τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

-- The remaining obligations of the termwise short exact sequence
-- `0 → SizeC 𝒜 (k+1) m → SizeC 𝒜 k m → SizeQ 𝒜 k m → 0`:
--   * `sizeIncl` is termwise injective, `sizeQuot` termwise surjective;
--   * `LinearMap.ker (sizeQuot 𝒜 k m) = LinearMap.range (sizeIncl 𝒜 k m)`;
--   * `sizeIncl`/`sizeQuot` commute with `sizeD` (so that the sequence is a sequence of complexes).

end CoeffSys

end Work.DSM5b
