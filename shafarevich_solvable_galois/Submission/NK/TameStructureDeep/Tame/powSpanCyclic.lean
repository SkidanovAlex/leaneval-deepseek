import Mathlib
import Submission.NK.TameStructureDeep.Tame.primeToPart
import Submission.NK.TameStructureDeep.Tame.CorrectedInterface
import Submission.NK.TameStructureDeep.Tame.inertiaQuotient
import Submission.NK.TameStructureDeep.Tame.mem_adjoin_root_of_fixed
import Submission.NK.TameStructureDeep.Tame.mem_correctedWildInertia_of_forall
import Submission.NK.LocalTame.All
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

/-!
# Pro-cyclicity of the tame inertia `I_κ/V_κ`

For a uniformiser `π` of `κ = K_𝔭`, `κ^{ur}` the maximal unramified and `κ^{tr}` the maximal
tamely ramified extension inside a separable closure `K'`, write

* `I = Gal(K'/κ^{ur}) = κ^{ur}.fixingSubgroup` (the inertia subgroup),
* `V = Gal(K'/κ^{tr}) = κ^{tr}.fixingSubgroup` (the corrected wild inertia).

The goal of this chapter is the classical computation `I/V = Gal(κ^{tr}/κ^{ur}) ≅ ∏_{ℓ ≠ p} ℤ_ℓ`,
in the finite-quotient form used by the workspace: `I/V` is pro-cyclic.

## The route

* `P_m := V ⊔ ⟨σ^m : σ ∈ I⟩` is *closed*: it is the image of the compact `V × I` under
  `(v, σ) ↦ v σ^m` — the key point being that modulo `V` the `m`-th power map is multiplicative
  (`pow_mul_pow_mul_inv_mem_correctedWildInertia`), so the image is already a subgroup.
* The fixed field of `P_m` is the layer `L = κ^{ur} ⊔ κ⟮γ⟯` for `γ` a `primeToPart 𝔭 m`-th root of
  `π` (the hard direction is `mem_adjoin_root_of_fixed`).
* Hence, by the infinite Galois correspondence, `L.fixingSubgroup = P_m`, and the Kummer pairing
  `σ ↦ σ γ / γ` identifies `I/P_m = Gal(L/κ^{ur})` with the (cyclic) group of
  `primeToPart 𝔭 m`-th roots of unity.
* A general group-theoretic criterion (`isProCyclic_quotient_of_forall_isCyclic_powSpan`) then
  gives pro-cyclicity of `I/V`.
-/
open scoped Classical
open IntermediateField

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

noncomputable section

/-! ## The Kummer character of an inertia element -/

section KummerChar

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The power formula for the Kummer character.**  If `σ` fixes `κ^{ur}` (i.e. `σ` is in the
inertia subgroup) and `β ^ n = π` with `p ∤ n`, `β ≠ 0`, then the `k`-th power of `σ` acts on `β`
by the `k`-th power of the Kummer character `σ β / β`. -/
lemma pow_apply_root {p n : ℕ} (hn : ¬ p ∣ n) {π : κ} {σ : Gal(K'/κ)}
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup)
    {β : K'} (hβ : β ^ n = algebraMap κ K' π) (hβne : β ≠ 0) (k : ℕ) :
    (σ ^ k) β = (σ β / β) ^ k * β := by
  have hchar : σ β / β ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p :=
    kummerChar_mem_unramifiedClosure (K' := K') hn hσ hβ hβne
  have hfix : ∀ τ : Gal(K'/κ),
      τ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup →
      τ (σ β / β) = σ β / β := fun τ hτ =>
    (IntermediateField.mem_fixingSubgroup_iff _ τ).mp hτ _ hchar
  induction k with
  | zero => simp
  | succ k ih =>
      have hσβ : σ β = (σ β / β) * β := (div_mul_cancel₀ (σ β) hβne).symm
      conv_lhs => rw [pow_succ, AlgEquiv.mul_apply, hσβ]
      rw [map_mul, hfix _ (Subgroup.pow_mem _ hσ k), ih,
        mul_left_comm (σ β / β) ((σ β / β) ^ k) β, pow_succ (σ β / β) k, mul_assoc]

/-- **An inertia element fixes `κ^{ur}` pointwise, hence acts on `ζ * β` by `ζ * σ β`.** -/
lemma apply_mul_mem_unramifiedClosure {p : ℕ} {σ : Gal(K'/κ)}
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup)
    {ζ : K'} (hζ : ζ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p) (β : K') :
    σ (ζ * β) = ζ * σ β := by
  rw [map_mul, (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ ζ hζ]

/-- **The inverse of the Kummer character is the Kummer character of the inverse.** -/
lemma kummerChar_inv {p n : ℕ} (hn : ¬ p ∣ n) {π : κ} {σ : Gal(K'/κ)}
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup)
    {β : K'} (hβ : β ^ n = algebraMap κ K' π) (hβne : β ≠ 0) :
    σ⁻¹ β / β = (σ β / β)⁻¹ := by
  rw [inv_apply_root (K' := K') hn hσ hβ hβne]
  exact mul_div_cancel_right₀ _ hβne

/-- **`d`-th roots of the uniformiser are fixed by `m`-th powers of inertia elements when
`d ∣ m`.**  The Kummer character of `σ` on a `d`-th root of `π` is a `d`-th root of unity, hence is
killed by the `m`-th power when `d ∣ m`. -/
lemma pow_apply_root_eq_self {p d m : ℕ} (hn : ¬ p ∣ d) (hdm : d ∣ m) {π : κ}
    {σ : Gal(K'/κ)}
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup)
    {γ : K'} (hγ : γ ^ d = algebraMap κ K' π) (hγne : γ ≠ 0) : (σ ^ m) γ = γ := by
  have hπne : algebraMap κ K' π ≠ 0 := by rw [← hγ]; exact pow_ne_zero d hγne
  have hpow : (σ γ / γ) ^ d = 1 := by
    have h1 : (σ γ) ^ d = algebraMap κ K' π := by rw [← map_pow, hγ, AlgEquiv.commutes]
    rw [div_pow, h1, hγ, div_self hπne]
  have hm : (σ γ / γ) ^ m = 1 := by
    obtain ⟨t, rfl⟩ := hdm
    rw [pow_mul, hpow, one_pow]
  rw [pow_apply_root (K' := K') hn hσ hγ hγne m, hm, one_mul]

/-- **The `m`-th power map is multiplicative on the inertia subgroup modulo the corrected wild
inertia.**  For `x, y ∈ I_κ = Gal(K'/κ^{ur})` the element `x ^ m y ^ m ((xy)^m)⁻¹` fixes `κ^{tr}`:
it fixes `κ^{ur}`, and on an `n`-th root `β` of `π` (`p ∤ n`) the Kummer characters multiply,
`(xy) β / β = (x β / β) (y β / β)`, so the three characters cancel. -/
theorem pow_mul_pow_mul_inv_mem_correctedWildInertia {p : ℕ} (hp : p ≠ 1) {π : κ} (hπ : π ≠ 0)
    (m : ℕ) {x y : Gal(K'/κ)}
    (hx : x ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup)
    (hy : y ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup) :
    x ^ m * y ^ m * ((x * y) ^ m)⁻¹ ∈ correctedWildInertia (K' := K') p π := by
  have hc : x ^ m * y ^ m * ((x * y) ^ m)⁻¹ ∈
      (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup :=
    mul_mem (mul_mem (Subgroup.pow_mem _ hx m) (Subgroup.pow_mem _ hy m))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mul_mem hx hy) m))
  refine mem_correctedWildInertia_of_forall hp _ ?_ ?_
  · intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hc z hz
  · intro n hn β hβ
    have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
    have hβne : β ≠ 0 := by
      intro h
      have h1 : algebraMap κ K' π = 0 := by rw [← hβ, h, zero_pow hn0]
      exact hπ (by simpa using h1)
    have hχmem : ∀ {σ : Gal(K'/κ)},
        σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup →
        σ β / β ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p :=
      fun hσ => kummerChar_mem_unramifiedClosure (K' := K') hn hσ hβ hβne
    have hχxy : (x * y) β / β = (x β / β) * (y β / β) :=
      div_mul_apply_root (K' := K') hn hx hy hβ hβne
    -- the three factors, computed on `β`
    have h1 : ((x * y) ^ m)⁻¹ β = (((x * y) β / β) ^ m)⁻¹ * β := by
      rw [← inv_pow]
      rw [pow_apply_root (K' := K') hn (Subgroup.inv_mem _ (mul_mem hx hy)) hβ hβne m]
      rw [kummerChar_inv (K' := K') hn (mul_mem hx hy) hβ hβne, inv_pow]
    have h2 : (y ^ m) ((((x * y) β / β) ^ m)⁻¹ * β) =
        (((x * y) β / β) ^ m)⁻¹ * ((y β / β) ^ m * β) := by
      rw [apply_mul_mem_unramifiedClosure (K' := K') (Subgroup.pow_mem _ hy m)
        (inv_mem (pow_mem (hχmem (mul_mem hx hy)) m)) β,
        pow_apply_root (K' := K') hn hy hβ hβne m]
    have h3a : (x ^ m) ((((x * y) β / β) ^ m)⁻¹ * ((y β / β) ^ m * β)) =
        (((x * y) β / β) ^ m)⁻¹ * ((x ^ m) ((y β / β) ^ m * β)) :=
      apply_mul_mem_unramifiedClosure (K' := K') (Subgroup.pow_mem _ hx m)
        (inv_mem (pow_mem (hχmem (mul_mem hx hy)) m)) ((y β / β) ^ m * β)
    have h3b : (x ^ m) ((y β / β) ^ m * β) = (y β / β) ^ m * ((x ^ m) β) :=
      apply_mul_mem_unramifiedClosure (K' := K') (Subgroup.pow_mem _ hx m)
        (pow_mem (hχmem hy) m) β
    have h3 : (x ^ m) ((((x * y) β / β) ^ m)⁻¹ * ((y β / β) ^ m * β)) =
        (((x * y) β / β) ^ m)⁻¹ * ((y β / β) ^ m * ((x β / β) ^ m * β)) := by
      rw [h3a, h3b, pow_apply_root (K' := K') hn hx hβ hβne m]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, h2, h3, hχxy]
    have ha : x β / β ≠ 0 := div_ne_zero ((map_ne_zero x).mpr hβne) hβne
    have hb : y β / β ≠ 0 := div_ne_zero ((map_ne_zero y).mpr hβne) hβne
    rw [mul_pow, mul_inv]
    field_simp

end KummerChar

end
/-! ## The subgroup `V_κ · {σ ^ m : σ ∈ I_κ}` of `G_κ` -/

noncomputable section

section Main

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
  [IsSepClosure (𝔭.adicCompletion K) K']

/-- The corrected wild inertia `V_κ = Gal(K'/κ^{tr})` as a subgroup of `G_κ = Gal(K'/κ)`. -/
abbrev Vsub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    (π : 𝔭.adicCompletionIntegers K) : Subgroup (Gal(K'/(𝔭.adicCompletion K))) :=
  correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) π

/-- The inertia subgroup `I_κ = Gal(K'/κ^{ur})` as a subgroup of `G_κ`. -/
abbrev Isub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K'] :
    Subgroup (Gal(K'/(𝔭.adicCompletion K))) :=
  IntermediateField.fixingSubgroup
    (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭))

/-- A uniformiser of `κ` is nonzero. -/
lemma uniformizer_coe_ne_zero {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) :
    (π : 𝔭.adicCompletion K) ≠ 0 := by
  have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  intro h
  refine hirr.ne_zero ?_
  apply Subtype.ext
  simpa using h
/-- The image of a uniformiser in `K'` is nonzero. -/
lemma uniformizer_algebraMap_ne_zero {π : 𝔭.adicCompletionIntegers K}
    (hπ : IsUniformizerAt 𝔭 π) :
    algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 := by
  intro h
  have h0 : (π : 𝔭.adicCompletion K) = 0 := by simpa using h
  exact uniformizer_coe_ne_zero 𝔭 hπ h0
/-- `V_κ` is normal in `G_κ`. -/
lemma Vsub_normal (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) :
    (Vsub 𝔭 K' π).Normal :=
  correctedWildInertia_normal (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
    (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭) (uniformizer_coe_ne_zero 𝔭 hπ)
/-- `I_κ = Gal(K'/κ^{ur})` is normal in `G_κ`. -/
lemma Isub_normal (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] : (Isub 𝔭 K').Normal := by
  haveI hgal : IsGalois (𝔭.adicCompletion K)
      (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭)) :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
  haveI hgal2 : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  show (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
    (resCharAt 𝔭)).fixingSubgroup.Normal
  exact inferInstance

/-- `V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩`, the subgroup generated by the corrected wild inertia and the
`m`-th powers of the inertia subgroup. -/
abbrev powSpanSub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    (π : 𝔭.adicCompletionIntegers K) (m : ℕ) : Subgroup (Gal(K'/(𝔭.adicCompletion K))) :=
  Vsub 𝔭 K' π ⊔ Subgroup.closure
    (Set.range fun x : ↥(Isub 𝔭 K') => (x : Gal(K'/(𝔭.adicCompletion K))) ^ m)

/-- The set of products `v * σ ^ m` (`v ∈ V_κ`, `σ ∈ I_κ`) as a subgroup of `G_κ`: this is the
set whose compactness gives the closedness of `V_κ ⊔ ⟨σ ^ m⟩`. -/
def powSpanImage (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (m : ℕ) :
    Subgroup (Gal(K'/(𝔭.adicCompletion K))) where
  carrier := Set.range fun z : ↥(Vsub 𝔭 K' π) × ↥(Isub 𝔭 K') =>
    (z.1 : Gal(K'/(𝔭.adicCompletion K))) * (z.2 : Gal(K'/(𝔭.adicCompletion K))) ^ m
  one_mem' := ⟨(1, 1), by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
    obtain ⟨⟨v₁, hv₁⟩, ⟨σ₁, hσ₁⟩⟩ := z₁
    obtain ⟨⟨v₂, hv₂⟩, ⟨σ₂, hσ₂⟩⟩ := z₂
    have hV := Vsub_normal 𝔭 K' hπ
    have hpow : σ₁ ^ m * σ₂ ^ m * ((σ₁ * σ₂) ^ m)⁻¹ ∈ Vsub 𝔭 K' π :=
      pow_mul_pow_mul_inv_mem_correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (p := resCharAt 𝔭) (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭).ne_one
        (uniformizer_coe_ne_zero 𝔭 hπ) m hσ₁ hσ₂
    refine ⟨(⟨v₁ * (σ₁ ^ m * v₂ * (σ₁ ^ m)⁻¹) * (σ₁ ^ m * σ₂ ^ m * ((σ₁ * σ₂) ^ m)⁻¹), ?_⟩,
      ⟨σ₁ * σ₂, mul_mem hσ₁ hσ₂⟩), ?_⟩
    · exact mul_mem (mul_mem hv₁ (hV.conj_mem v₂ hv₂ (σ₁ ^ m))) hpow
    · group
  inv_mem' := by
    rintro g ⟨z, rfl⟩
    obtain ⟨⟨v, hv⟩, ⟨σ, hσ⟩⟩ := z
    have hV := Vsub_normal 𝔭 K' hπ
    refine ⟨(⟨(σ ^ m)⁻¹ * v⁻¹ * σ ^ m, hV.conj_mem v⁻¹ (Subgroup.inv_mem _ hv) (σ ^ m)⁻¹⟩,
      ⟨σ⁻¹, Subgroup.inv_mem _ hσ⟩), ?_⟩
    show (σ ^ m)⁻¹ * v⁻¹ * σ ^ m * (σ⁻¹) ^ m = (v * σ ^ m)⁻¹
    rw [inv_pow]
    group





/-- `V_κ ≤ I_κ`. -/
lemma Vsub_le_Isub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} : Vsub 𝔭 K' π ≤ Isub 𝔭 K' := by
  have h := correctedWildInertia_le_inertia (κ := 𝔭.adicCompletion K) (K' := K')
    (resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  rwa [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
    (K' := K') (resCharAt 𝔭)] at h

/-- The subgroup of the `m`-th powers of the inertia subgroup is contained in the inertia
subgroup. -/
lemma closure_pow_le_Isub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K'] (m : ℕ) :
    Subgroup.closure
      (Set.range fun x : ↥(Isub 𝔭 K') => (x : Gal(K'/(𝔭.adicCompletion K))) ^ m) ≤ Isub 𝔭 K' := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨σ, hσeq⟩
  rw [← hσeq]
  exact Subgroup.pow_mem _ σ.2 m

/-- The subgroup `V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩` is normal in `G_κ`. -/
lemma powSpanImage_normal (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (m : ℕ) :
    (powSpanImage 𝔭 K' hπ m).Normal := by
  haveI hV := Vsub_normal 𝔭 K' hπ
  haveI hI := Isub_normal 𝔭 K'
  have hconjpow : ∀ (g σ : Gal(K'/(𝔭.adicCompletion K))) (k : ℕ),
      (g * σ * g⁻¹) ^ k = g * σ ^ k * g⁻¹ := by
    intro g σ k
    induction k with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, ih]; group
  refine Subgroup.Normal.mk ?_
  rintro n ⟨z, rfl⟩ g
  obtain ⟨⟨v, hv⟩, ⟨σ, hσ⟩⟩ := z
  refine ⟨(⟨g * v * g⁻¹, hV.conj_mem v hv g⟩, ⟨g * σ * g⁻¹, hI.conj_mem σ hσ g⟩), ?_⟩
  show g * v * g⁻¹ * (g * σ * g⁻¹) ^ m = g * (v * σ ^ m) * g⁻¹
  rw [hconjpow]
  group

/-- **The joining of `V_κ` with the subgroup generated by the `m`-th powers of the inertia
subgroup** is the set of products `v * σ ^ m`. -/
theorem powSpanSub_eq_image (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (m : ℕ) :
    powSpanSub 𝔭 K' π m = powSpanImage 𝔭 K' hπ m := by
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · intro v hv
      exact ⟨(⟨v, hv⟩, ⟨1, Subgroup.one_mem _⟩), by simp⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨σ, rfl⟩
      exact ⟨(⟨1, Subgroup.one_mem _⟩, σ), by simp⟩
  · rintro g ⟨z, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left z.1.2)
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨z.2, rfl⟩))

/-- The subgroup `V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩` is normal in `G_κ`. -/
lemma powSpanSub_normal (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (m : ℕ) :
    (powSpanSub 𝔭 K' π m).Normal :=
  powSpanSub_eq_image 𝔭 K' hπ m ▸ powSpanImage_normal 𝔭 K' hπ m


/-- **`V_κ ⊔ ⟨σ ^ m⟩` is closed in `G_κ`**: it is the image of the compact set `V_κ × I_κ` under
the continuous map `(v, σ) ↦ v σ ^ m`. -/
theorem isClosed_powSpanSub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (m : ℕ) :
    IsClosed ((powSpanSub 𝔭 K' π m : Subgroup (Gal(K'/(𝔭.adicCompletion K)))) :
      Set (Gal(K'/(𝔭.adicCompletion K)))) := by
  haveI hgal : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  let Gκ := Gal(K'/(𝔭.adicCompletion K))
  let φ : Gκ × Gκ → Gκ := fun z => z.1 * z.2 ^ m
  have hcont : Continuous φ := by
    rw [show φ = fun z : Gκ × Gκ => z.1 * z.2 ^ m from rfl]
    exact continuous_fst.mul (continuous_snd.pow m)
  have hVc : IsCompact ((Vsub 𝔭 K' π : Subgroup Gκ) : Set Gκ) :=
    (InfiniteGalois.fixingSubgroup_isClosed (K := K')
      (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) (π : 𝔭.adicCompletion K))).isCompact
  have hIc : IsCompact ((Isub 𝔭 K' : Subgroup Gκ) : Set Gκ) :=
    (InfiniteGalois.fixingSubgroup_isClosed (K := K')
      (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭))).isCompact
  have himg : IsCompact (φ '' (((Vsub 𝔭 K' π : Set Gκ) ×ˢ (Isub 𝔭 K' : Set Gκ)))) :=
    (hVc.prod hIc).image hcont
  have hset : φ '' (((Vsub 𝔭 K' π : Set Gκ) ×ˢ (Isub 𝔭 K' : Set Gκ)))
      = ((powSpanImage 𝔭 K' hπ m : Subgroup Gκ) : Set Gκ) := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hz1, hz2⟩ := hz
      exact ⟨(⟨z.1, hz1⟩, ⟨z.2, hz2⟩), rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨((z.1 : Gκ), (z.2 : Gκ)), ⟨z.1.2, z.2.2⟩, rfl⟩
  have hcoe : ((powSpanSub 𝔭 K' π m : Subgroup Gκ) : Set Gκ)
      = ((powSpanImage 𝔭 K' hπ m : Subgroup Gκ) : Set Gκ) := by
    rw [powSpanSub_eq_image 𝔭 K' hπ m]
  rw [hcoe]
  exact hset ▸ himg.isClosed

/-- **The fixed field of `V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩` is the layer `κ^{ur} ⟦γ⟧`.** -/
theorem fixedField_powSpanSub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hγtr : γ ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :
    IntermediateField.fixedField (powSpanSub 𝔭 K' π m) =
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ⊔
        IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K') := by
  haveI hgal : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  have hd0 : primeToPart 𝔭 m ≠ 0 := (primeToPart_pos 𝔭 hm).ne'
  have hndvd : ¬ (resCharAt 𝔭) ∣ primeToPart 𝔭 m := not_dvd_primeToPart 𝔭 hm.ne'
  have hLle : (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')) ≤
      NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) (π : 𝔭.adicCompletion K) :=
    IntermediateField.adjoin_le_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hγtr
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxV : x ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) (π : 𝔭.adicCompletion K) := by
      have hfixV : ∀ σ ∈ (Vsub 𝔭 K' π : Subgroup (Gal(K'/(𝔭.adicCompletion K)))), σ x = x :=
        fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)
      have hmem : x ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup
          (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭) (π : 𝔭.adicCompletion K))) := by
        rw [IntermediateField.mem_fixedField_iff]
        exact hfixV
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    refine mem_adjoin_root_of_fixed 𝔭 hm hπ hγ hxV ?_
    intro σ hσ
    exact hx (σ ^ m) (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨σ, hσ⟩, rfl⟩))
  · refine sup_le ?_ ?_
    · rw [IntermediateField.le_iff_le]
      refine sup_le ?_ ?_
      · intro v hv
        exact Vsub_le_Isub 𝔭 K' hv
      · exact closure_pow_le_Isub 𝔭 K' m
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      change γ ∈ IntermediateField.fixedField (powSpanSub 𝔭 K' π m)
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hle : powSpanSub 𝔭 K' π m ≤
          (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')).fixingSubgroup := by
        refine sup_le ?_ ?_
        · exact IntermediateField.fixingSubgroup_le hLle
        · refine (Subgroup.closure_le _).mpr ?_
          rintro g ⟨τ, rfl⟩
          refine (NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff γ _).mpr ?_
          refine pow_apply_root_eq_self (K' := K') hndvd (primeToPart_dvd 𝔭 hm.ne') τ.2 hγ ?_
          intro h
          exact (uniformizer_algebraMap_ne_zero 𝔭 hπ) (by rw [← hγ, h, zero_pow hd0])
      exact (NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff γ σ).mp
        (hle hσ)

/-- **The Kummer pairing `σ ↦ σ γ / γ`**, for `γ` a `primeToPart 𝔭 m`-th root of the
uniformiser, as a monoid homomorphism into the group of `primeToPart 𝔭 m`-th roots of unity. -/
noncomputable def kummerPairing (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) :
    ↥(Isub 𝔭 K') →* ↥(rootsOfUnity (primeToPart 𝔭 m) K') :=
  letI : NeZero (primeToPart 𝔭 m) := ⟨(primeToPart_pos 𝔭 hm).ne'⟩
  let hndvd : ¬ (resCharAt 𝔭) ∣ primeToPart 𝔭 m := not_dvd_primeToPart 𝔭 hm.ne'
  let hγne : γ ≠ 0 := fun h =>
    (uniformizer_algebraMap_ne_zero 𝔭 hπ) (by rw [← hγ, h, zero_pow (primeToPart_pos 𝔭 hm).ne'])
  { toFun := fun σ => rootsOfUnity.mkOfPowEq
      (((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) γ / γ) (by
        have h2 : ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K)))
            (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) =
            algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) :=
          AlgEquiv.commutes ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K)))
            (π : 𝔭.adicCompletion K)
        have hne : γ ^ primeToPart 𝔭 m ≠ 0 := by
          rw [hγ]
          exact uniformizer_algebraMap_ne_zero 𝔭 hπ
        have hpow : (((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) γ)
            ^ primeToPart 𝔭 m = γ ^ primeToPart 𝔭 m := by
          rw [← map_pow, hγ, h2]
        rw [div_pow, hpow, div_self hne])
    map_one' := by
      apply Subtype.ext; apply Units.ext
      simp only [OneMemClass.coe_one, rootsOfUnity.coe_mkOfPowEq, Units.val_one]
      rw [AlgEquiv.one_apply, div_self hγne]
    map_mul' := by
      intro σ τ
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, rootsOfUnity.coe_mkOfPowEq]
      exact div_mul_apply_root (K' := K') hndvd σ.2 τ.2 hγ hγne }

/-- The value of the Kummer pairing, as an element of `K'`. -/
lemma kummerPairing_coe (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) (σ : ↥(Isub 𝔭 K')) :
    (((kummerPairing 𝔭 K' hm hπ γ hγ σ : ↥(rootsOfUnity (primeToPart 𝔭 m) K')) : K'ˣ) : K')
      = (((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) γ / γ) := by
  haveI : NeZero (primeToPart 𝔭 m) := ⟨(primeToPart_pos 𝔭 hm).ne'⟩
  exact rootsOfUnity.coe_mkOfPowEq _

/-- **The kernel of the Kummer pairing is the fixing subgroup of the layer `κ^{ur} ⟦γ⟧`.** -/
theorem kummerPairing_ker (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hγtr : γ ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :
    (kummerPairing 𝔭 K' hm hπ γ hγ).ker
      = (powSpanSub 𝔭 K' π m).subgroupOf (Isub 𝔭 K') := by
  haveI hgal : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  haveI hne : NeZero (primeToPart 𝔭 m) := ⟨(primeToPart_pos 𝔭 hm).ne'⟩
  have hγne : γ ≠ 0 := fun h =>
    (uniformizer_algebraMap_ne_zero 𝔭 hπ) (by rw [← hγ, h, zero_pow (primeToPart_pos 𝔭 hm).ne'])
  have hPclosed : IsClosed (powSpanSub 𝔭 K' π m).carrier := by
    show IsClosed (((powSpanSub 𝔭 K' π m : Subgroup (Gal(K'/(𝔭.adicCompletion K)))) :
      Set (Gal(K'/(𝔭.adicCompletion K)))))
    exact isClosed_powSpanSub 𝔭 K' hπ m
  have hfix := InfiniteGalois.fixingSubgroup_fixedField (K := K')
    (⟨powSpanSub 𝔭 K' π m, hPclosed⟩ : ClosedSubgroup (Gal(K'/(𝔭.adicCompletion K))))
  have hL : IntermediateField.fixingSubgroup
        (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ⊔
          IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K'))
      = powSpanSub 𝔭 K' π m := by
    rw [← fixedField_powSpanSub 𝔭 K' hm hπ γ hγ hγtr]
    exact hfix
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hσ
    have h1 : (((kummerPairing 𝔭 K' hm hπ γ hγ σ : ↥(rootsOfUnity (primeToPart 𝔭 m) K')) : K'ˣ) :
        K') = 1 := by
      rw [hσ]; rfl
    rw [kummerPairing_coe 𝔭 K' hm hπ γ hγ σ] at h1
    have h2 : ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) γ = γ :=
      (div_eq_one_iff_eq hγne).mp h1
    have hmem : ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) ∈
        IntermediateField.fixingSubgroup
          (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭) ⊔
          IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')) := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨σ.2,
        (NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff γ _).mpr h2⟩
    rw [hL] at hmem
    exact hmem
  · intro hσ
    have hmem : ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) ∈
        IntermediateField.fixingSubgroup
          (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭) ⊔
          IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')) := by
      rw [hL]; exact hσ
    rw [IntermediateField.fixingSubgroup_sup] at hmem
    have h2 : ((σ : ↥(Isub 𝔭 K')) : Gal(K'/(𝔭.adicCompletion K))) γ = γ :=
      (NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff γ _).mp hmem.2
    apply Subtype.ext; apply Units.ext
    simp only [OneMemClass.coe_one, Units.val_one]
    rw [kummerPairing_coe 𝔭 K' hm hπ γ hγ σ, h2, div_self hγne]

/-- **The quotient of the inertia subgroup by `V_κ ⊔ ⟨σ ^ m⟩` is cyclic**: it is isomorphic to a
subgroup of the (cyclic) group of `primeToPart 𝔭 m`-th roots of unity, via the Kummer pairing. -/
theorem isCyclic_quotientImage_powSpanSub (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π)
    [hP : (powSpanSub 𝔭 K' π m).Normal] (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hγtr : γ ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :
    IsCyclic ↥(NK.LocalTame.quotientImage (powSpanSub 𝔭 K' π m) (Isub 𝔭 K')) := by
  haveI hne : NeZero (primeToPart 𝔭 m) := ⟨(primeToPart_pos 𝔭 hm).ne'⟩
  haveI hcycRoots : IsCyclic ↥(rootsOfUnity (primeToPart 𝔭 m) K') :=
    rootsOfUnity.isCyclic K' (primeToPart 𝔭 m)
  have hrange : IsCyclic ↥((kummerPairing 𝔭 K' hm hπ γ hγ).range) := Subgroup.isCyclic _
  have e1 : (↥(Isub 𝔭 K') ⧸ (kummerPairing 𝔭 K' hm hπ γ hγ).ker) ≃*
      ↥((kummerPairing 𝔭 K' hm hπ γ hγ).range) :=
    (QuotientGroup.quotientMulEquivOfEq
        (MonoidHom.ker_rangeRestrict (kummerPairing 𝔭 K' hm hπ γ hγ)).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (kummerPairing 𝔭 K' hm hπ γ hγ).rangeRestrict (MonoidHom.rangeRestrict_surjective _))
  have h1 : IsCyclic (↥(Isub 𝔭 K') ⧸ (kummerPairing 𝔭 K' hm hπ γ hγ).ker) :=
    (MulEquiv.isCyclic e1).mpr hrange
  have hq : IsCyclic (↥(Isub 𝔭 K') ⧸ (powSpanSub 𝔭 K' π m).subgroupOf (Isub 𝔭 K')) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientMulEquivOfEq
      (kummerPairing_ker 𝔭 K' hm hπ γ hγ hγtr))).mp h1
  exact (MulEquiv.isCyclic (quotientImageMulEquivQuotient
    (V := powSpanSub 𝔭 K' π m) (I := Isub 𝔭 K'))).mpr hq

/-- **The group-theoretic bookkeeping of the criterion.**  If the quotient of `I_κ` by
`V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩` is cyclic, then so is the quotient by the subgroup appearing in the
criterion `isProCyclic_quotient_of_forall_isCyclic_powSpan` (which uses the normal closure of the
`m`-th powers *inside* `I_κ`). -/
theorem isCyclic_quotient_normalClosure (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {m : ℕ} (hm : 0 < m)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π)
    [hVn : (Vsub 𝔭 K' π).Normal] [hP : (powSpanSub 𝔭 K' π m).Normal] (γ : K')
    (hγ : γ ^ primeToPart 𝔭 m =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hγtr : γ ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :
    IsCyclic (↥(Isub 𝔭 K') ⧸ (Subgroup.subgroupOf (Vsub 𝔭 K' π) (Isub 𝔭 K') ⊔
      Subgroup.normalClosure (Set.range fun x : ↥(Isub 𝔭 K') => x ^ m))) := by
  have hcle : (Subgroup.closure
      (Set.range fun x : ↥(Isub 𝔭 K') => (x : Gal(K'/(𝔭.adicCompletion K))) ^ m)).subgroupOf
        (Isub 𝔭 K') ≤
      Subgroup.normalClosure (Set.range fun x : ↥(Isub 𝔭 K') => x ^ m) := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hsub : Subgroup.closure
        (Set.range fun x : ↥(Isub 𝔭 K') => (x : Gal(K'/(𝔭.adicCompletion K))) ^ m) ≤
        (Subgroup.normalClosure (Set.range fun x : ↥(Isub 𝔭 K') => x ^ m)).map
          (Isub 𝔭 K').subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨σ, rfl⟩
      exact ⟨σ ^ m, Subgroup.subset_closure
          (Group.subset_conjugatesOfSet (Set.mem_range_self σ)),
        map_pow (Isub 𝔭 K').subtype σ m⟩
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hsub hy)
    rw [Subtype.ext hzy] at hz
    exact hz
  have hle : (powSpanSub 𝔭 K' π m).subgroupOf (Isub 𝔭 K') ≤
      Subgroup.subgroupOf (Vsub 𝔭 K' π) (Isub 𝔭 K') ⊔
        Subgroup.normalClosure (Set.range fun x : ↥(Isub 𝔭 K') => x ^ m) := by
    rw [powSpanSub, Subgroup.subgroupOf_sup (Vsub_le_Isub 𝔭 K') (closure_pow_le_Isub 𝔭 K' m)]
    exact sup_le le_sup_left (hcle.trans le_sup_right)
  have hcyc := isCyclic_quotientImage_powSpanSub 𝔭 K' hm hπ
    (hP := powSpanSub_normal 𝔭 K' hπ m) γ hγ hγtr
  have hq : IsCyclic (↥(Isub 𝔭 K') ⧸ (powSpanSub 𝔭 K' π m).subgroupOf (Isub 𝔭 K')) :=
    (MulEquiv.isCyclic (quotientImageMulEquivQuotient
      (V := powSpanSub 𝔭 K' π m) (I := Isub 𝔭 K'))).mp hcyc
  haveI : (Subgroup.subgroupOf (Vsub 𝔭 K' π) (Isub 𝔭 K') ⊔
      Subgroup.normalClosure (Set.range fun x : ↥(Isub 𝔭 K') => x ^ m)).Normal :=
    Subgroup.sup_normal _ _
  refine isCyclic_of_surjective
    (QuotientGroup.map _ _ (MonoidHom.id ↥(Isub 𝔭 K')) (by simpa using hle)) ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  exact ⟨QuotientGroup.mk' _ x, by rw [QuotientGroup.map_mk']; rfl⟩

end Main

end

end NK.TameStructureDeep.Tame
