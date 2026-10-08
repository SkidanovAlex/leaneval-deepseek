import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Weight spaces of representations of finite abelian groups

This file sets up the vocabulary for the weight-space (isotypic) decomposition of a
representation `ρ : Z →* Module.End k V` of a finite **abelian** group `Z` over an
algebraically closed field `k` in which `|Z|` is invertible.

* `weightSpace ρ χ` is the common eigenspace `V_χ = ⨅ z, ker (ρ z - χ z • 1)` of all `ρ z`
  with eigenvalue `(χ z : k)`, for a character `χ : Z →* kˣ`.
* `charProj ρ χ` is the projection `(|Z| : k)⁻¹ • ∑ z, (χ z)⁻¹ • ρ z` onto `V_χ`.
* `sum_eq_zero_of_ne_one` is the orthogonality relation `∑ z, χ z = 0` for a nontrivial
  character, which makes `charProj` vanish on the other weight spaces.
* `restrictRep` restricts a representation to an invariant submodule.
* `iSup_eigenspace_eq_top_of_pow_eq_one` is the single-operator spectral decomposition used
  to run the descent which proves that the weight spaces span `V`.

The main statements (`Work.CharPrelim.weightSpace_finDim`, `Work.CharPrelim.weightSpace_span`,
`Work.CharPrelim.weightSpace_indep`, `Work.CharPrelim.weightSpace_decomposition`) live in their
own files.
-/

noncomputable section

open Classical

namespace Work.CharPrelim

variable {k V Z : Type*}

section Basic

variable [Field k] [AddCommGroup V] [Module k V] [Group Z]

/-- **The weight space of the character `χ`**: the common eigenspace of all `ρ z` with
eigenvalue `(χ z : k)`. -/
def weightSpace (ρ : Z →* Module.End k V) (χ : Z →* kˣ) : Submodule k V :=
  ⨅ z, LinearMap.ker ((ρ z : Module.End k V) - (χ z : k) • 1)

/-- Membership in a weight space, unwound. -/
theorem mem_weightSpace (ρ : Z →* Module.End k V) (χ : Z →* kˣ) (v : V) :
    v ∈ weightSpace ρ χ ↔ ∀ z : Z, ρ z v = (χ z : k) • v := by
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

/-- Every weight space is contained in the eigenspace of each `ρ z`. -/
theorem weightSpace_le_ker (ρ : Z →* Module.End k V) (χ : Z →* kˣ) (z : Z) :
    weightSpace ρ χ ≤ LinearMap.ker ((ρ z : Module.End k V) - (χ z : k) • 1) :=
  iInf_le _ z

end Basic

section Abelian

variable [Field k] [AddCommGroup V] [Module k V] [CommGroup Z]

/-- Each `ρ z` preserves the weight space of every character (`Z` is abelian, so the `ρ z`
commute). -/
theorem mapsTo_weightSpace (ρ : Z →* Module.End k V) (χ : Z →* kˣ) (z : Z) :
    ∀ x ∈ weightSpace ρ χ, ρ z x ∈ weightSpace ρ χ := by
  intro v hv
  rw [mem_weightSpace] at hv ⊢
  intro z'
  have hcomm : ρ z' (ρ z v) = ρ z (ρ z' v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm z' z]
  rw [hcomm, hv z', map_smul]

/-- Submodule form of `mapsTo_weightSpace`. -/
theorem weightSpace_le_comap_weightSpace (ρ : Z →* Module.End k V) (χ : Z →* kˣ) (z : Z) :
    weightSpace ρ χ ≤ Submodule.comap (ρ z) (weightSpace ρ χ) :=
  fun x hv => mapsTo_weightSpace ρ χ z x hv

end Abelian

section Sum

variable [Field k] [Group Z] [Fintype Z]

/-- **Character orthogonality over the group**: the sum of the values of a nontrivial
character `η : Z →* kˣ` is zero. -/
theorem sum_eq_zero_of_ne_one {η : Z →* kˣ} (hη : η ≠ 1) :
    ∑ z : Z, (η z : k) = 0 := by
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.mp hη
  simp only [MonoidHom.one_apply] at hg
  have hg' : (η g : k) ≠ 1 := fun h => hg (Units.val_inj.mp h)
  have key : (η g : k) * (∑ z : Z, (η z : k)) = ∑ z : Z, (η z : k) := by
    rw [Finset.mul_sum]
    trans ∑ z : Z, (η (g * z) : k)
    · exact Finset.sum_congr rfl (fun z _ => by rw [map_mul, Units.val_mul])
    · exact Fintype.sum_equiv (Equiv.mulLeft g) (fun z => (η (g * z) : k))
        (fun z => (η z : k)) (fun z => rfl)
  have hzero : ((η g : k) - 1) * (∑ z : Z, (η z : k)) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hg'
  · exact h

end Sum

section Proj

variable [Field k] [AddCommGroup V] [Module k V] [Group Z] [Fintype Z]

/-- **The projection onto the weight space of `χ`**: `(|Z| : k)⁻¹ • ∑ z, (χ z)⁻¹ • ρ z`. -/
def charProj (ρ : Z →* Module.End k V) (χ : Z →* kˣ) : Module.End k V :=
  ((Nat.card Z : ℕ) : k)⁻¹ • ∑ z : Z, ((χ z : k)⁻¹) • (ρ z)

end Proj

section Restrict

variable [Field k] [AddCommGroup V] [Module k V] [Group Z]

/-- Restriction of a representation to an invariant submodule. -/
def restrictRep (ρ : Z →* Module.End k V) (W : Submodule k V)
    (hmaps : ∀ z : Z, ∀ x ∈ W, ρ z x ∈ W) : Z →* Module.End k W where
  toFun z := (ρ z).restrict (hmaps z)
  map_one' := by ext x; simp [LinearMap.coe_restrict_apply]
  map_mul' a b := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.restrict_apply, Submodule.coe_mk, map_mul]

/-- The restricted representation acts as `ρ` does. -/
theorem restrictRep_apply (ρ : Z →* Module.End k V) (W : Submodule k V)
    (hmaps : ∀ z : Z, ∀ x ∈ W, ρ z x ∈ W) (z : Z) (x : W) :
    ((restrictRep ρ W hmaps z) x : V) = ρ z x :=
  LinearMap.coe_restrict_apply (hmaps z) x

/-- The weight spaces of a restricted representation are contained in the weight spaces of the
ambient representation. -/
theorem weightSpace_restrictRep_le (ρ : Z →* Module.End k V) (W : Submodule k V)
    (hmaps : ∀ z : Z, ∀ x ∈ W, ρ z x ∈ W) (χ : Z →* kˣ) :
    Submodule.map W.subtype (weightSpace (restrictRep ρ W hmaps) χ) ≤ weightSpace ρ χ := by
  rintro x ⟨y, hy, rfl⟩
  have hy' : ∀ z : Z, (ρ z).restrict (hmaps z) y = (χ z : k) • y := by
    intro z
    exact (mem_weightSpace (restrictRep ρ W hmaps) χ y).mp hy z
  refine (mem_weightSpace ρ χ (W.subtype y : V)).mpr (fun z => ?_)
  have h' := LinearMap.coe_restrict_apply (hmaps z) y
  rw [hy' z] at h'
  simpa using h'.symm

end Restrict

section Eigen

variable [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Spectral decomposition of a finite order operator**: if `T ^ n = 1` and `n` is
invertible in `k`, then the eigenspaces of `T` span. -/
theorem iSup_eigenspace_eq_top_of_pow_eq_one (T : Module.End k V) {n : ℕ} (hn : (n : k) ≠ 0)
    (hT : T ^ n = 1) : (⨆ μ : k, T.eigenspace μ) = ⊤ := by
  have hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial k) :=
    (Polynomial.X_pow_sub_one_separable_iff.mpr hn).squarefree
  have haeval : Polynomial.aeval T (Polynomial.X ^ n - 1 : Polynomial k) = 0 := by
    simp [Polynomial.aeval_X, hT]
  exact Module.End.IsSemisimple.iSup_eigenspace_eq_top
    (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval)

end Eigen

end Work.CharPrelim
