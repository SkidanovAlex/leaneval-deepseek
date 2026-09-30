import Mathlib
import Submission.Work.Pi6.SRANGE.rTensor_injective_of_torsionFree_quotient
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The kernel of `ι ⊗ S` is the same for two presentations of the same quotient

Setting.  Let `ι₁ : B₁ ↪ Z₁` and `ι₂ : B₂ ↪ Z₂` be inclusions of `ℤ`-modules with `Z₁`, `Z₂`
torsion free, and let `b : B₁ → B₂`, `z : Z₁ → Z₂` satisfy `z ∘ ι₁ = ι₂ ∘ b`.  Assume moreover

* `h1` : `z ⁻¹' (range ι₂) = range ι₁`   (i.e. `z` induces an *injective* map `Z₁/B₁ → Z₂/B₂`),
* `h2` : `range z + range ι₂ = Z₂`       (i.e. that map is *surjective*);

equivalently the induced map of quotients `Z₁ ⧸ B₁ ≅ Z₂ ⧸ B₂` is an isomorphism.  Then for *every*
commutative ring `S` the map `b ⊗ S` induces an isomorphism between the failure of exactness of
`ι₁ ⊗ S` and that of `ι₂ ⊗ S`:

`ker (ι₁ ⊗ S) → ker (ι₂ ⊗ S)`, `x ↦ (b ⊗ S) x`

is bijective.

The mathematical content is the computation `ker (ι ⊗ S) ≅ Tor₁^ℤ(Z/B, S)`:  because `Z₁` and
`B₁` are torsion free (hence flat over the PID `ℤ`), the failure of exactness of `B ⊗ S → Z ⊗ S`
only depends on the quotient `Z/B`; our hypotheses say exactly that the two quotients agree.

Formally we avoid Tor: set `φ := (ι₁, b) : B₁ → Z₁ × B₂` and `ψ := z ∘ fst - ι₂ ∘ snd : Z₁ × B₂ → Z₂`.
The hypotheses are precisely `range φ = ker ψ` and `ψ` surjective, so

* `0 → B₁ →ᵠ Z₁ × B₂ →ᵠ Z₂ → 0` is exact with flat cokernel `Z₂` — hence `φ ⊗ S` is injective,
  which is the injectivity half;
* `ψ` is surjective — hence by right exactness `range (φ ⊗ S) = ker (ψ ⊗ S)`, which, combined with
  the decomposition `z₁ × z₂` of `(Z₁ × B₂) ⊗ S`, gives the surjectivity half.

-/

namespace Work.Pi6.SRANGE

theorem ker_rTensor_incl_bijective (S : Type) [CommRing S]
    {B₁ Z₁ B₂ Z₂ : Type*}
    [AddCommGroup B₁] [Module ℤ B₁] [AddCommGroup Z₁] [Module ℤ Z₁]
    [AddCommGroup B₂] [Module ℤ B₂] [AddCommGroup Z₂] [Module ℤ Z₂]
    (ι₁ : B₁ →ₗ[ℤ] Z₁) (hι₁ : Function.Injective ι₁)
    (hZ₁ : Module.IsTorsionFree ℤ Z₁)
    (ι₂ : B₂ →ₗ[ℤ] Z₂) (hι₂ : Function.Injective ι₂)
    (hZ₂ : Module.IsTorsionFree ℤ Z₂)
    (b : B₁ →ₗ[ℤ] B₂) (z : Z₁ →ₗ[ℤ] Z₂) (hz : z.comp ι₁ = ι₂.comp b)
    (h1 : ∀ x : Z₁, z x ∈ LinearMap.range ι₂ → x ∈ LinearMap.range ι₁)
    (h2 : ∀ w : Z₂, ∃ (w' : Z₁) (v : B₂), z w' + ι₂ v = w) :
    (∀ x₁ x₂ : TensorProduct ℤ B₁ S, (ι₁.rTensor S) x₁ = 0 → (ι₁.rTensor S) x₂ = 0 →
        (b.rTensor S) x₁ = (b.rTensor S) x₂ → x₁ = x₂)
    ∧ (∀ y : TensorProduct ℤ B₂ S, (ι₂.rTensor S) y = 0 →
        ∃ x : TensorProduct ℤ B₁ S, (ι₁.rTensor S) x = 0 ∧ (b.rTensor S) x = y) := by
  -- Fix the canonical `ℤ`-module structure on the product (two competing instances exist).
  letI : Module ℤ (Z₁ × B₂) := Prod.instModule
  -- The total maps whose exactness encodes the hypotheses.
  let φ : B₁ →ₗ[ℤ] Z₁ × B₂ := LinearMap.prod ι₁ b
  let ψ : Z₁ × B₂ →ₗ[ℤ] Z₂ :=
    (z.comp (LinearMap.fst ℤ Z₁ B₂)) - (ι₂.comp (LinearMap.snd ℤ Z₁ B₂))
  have hz' : ∀ u : B₁, z (ι₁ u) = ι₂ (b u) := fun u => by
    have h := congrArg (fun f : B₁ →ₗ[ℤ] Z₂ => f u) hz
    simpa [LinearMap.comp_apply] using h
  have hψφ : ψ.comp φ = 0 := by
    ext u
    simp [ψ, φ, LinearMap.prod_apply, LinearMap.comp_apply, hz' u]
  have hsurjψ : Function.Surjective ψ := by
    intro y
    obtain ⟨w', v, hv⟩ := h2 y
    exact ⟨(w', -v), by simp [ψ, LinearMap.comp_apply, LinearMap.sub_apply, hv]⟩
  have hkerψ : LinearMap.ker ψ ≤ LinearMap.range φ := by
    intro x hx
    obtain ⟨w, v⟩ := x
    have hx' : z w = ι₂ v := by
      have : z w - ι₂ v = 0 := hx
      exact sub_eq_zero.mp this
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (h1 w (LinearMap.mem_range.mpr ⟨v, hx'.symm⟩))
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    have hbu : b u = v := hι₂ (by rw [← hz' u, hu, hx'])
    simp [φ, LinearMap.prod_apply, hu, hbu]
  have hrangeφ : LinearMap.range φ ≤ LinearMap.ker ψ := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    exact congrArg (fun f : B₁ →ₗ[ℤ] Z₂ => f u) hψφ
  have hinjφ : Function.Injective φ := by
    intro u v huv
    apply hι₁
    have := congrArg (fun x => x.1) huv
    simpa [φ, LinearMap.prod_apply] using this
  have hExact : Function.Exact φ ψ := LinearMap.exact_iff.mpr (le_antisymm hkerψ hrangeφ)
  -- `Z₂` is torsion free, hence flat over the PID `ℤ`.
  haveI : Module.IsTorsionFree ℤ Z₂ := hZ₂
  haveI : Module.Flat ℤ Z₂ := inferInstance
  -- Injectivity half: `φ ⊗ S` is injective.
  have hφr : Function.Injective (φ.rTensor S) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj S φ).mp
      (LinearMap.lTensor_injective_of_exact_of_flat ψ hsurjψ φ hinjφ hExact S)
  -- Surjectivity half: right exactness of `- ⊗ S` on the exact sequence for `φ`, `ψ`.
  have hex : Function.Exact (φ.rTensor S) (ψ.rTensor S) := rTensor_exact S hExact hsurjψ
  -- `(Z₁ × B₂) ⊗ S` is the product of `Z₁ ⊗ S` and `B₂ ⊗ S` (component detection).
  have hdec : ∀ t : TensorProduct ℤ (Z₁ × B₂) S,
      (TensorProduct.map (LinearMap.inl ℤ Z₁ B₂) (LinearMap.id : S →ₗ[ℤ] S))
          ((LinearMap.fst ℤ Z₁ B₂).rTensor S t)
      + (TensorProduct.map (LinearMap.inr ℤ Z₁ B₂) (LinearMap.id : S →ₗ[ℤ] S))
          ((LinearMap.snd ℤ Z₁ B₂).rTensor S t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul w v =>
      obtain ⟨w₁, w₂⟩ := w
      simp only [LinearMap.rTensor_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
        TensorProduct.map_tmul, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.id_apply]
      rw [← TensorProduct.add_tmul]
      simp
    | add p q hp hq =>
      simp only [map_add]
      conv_rhs => rw [← hp, ← hq]
      abel
  have hzero_of : ∀ t : TensorProduct ℤ (Z₁ × B₂) S,
      (LinearMap.fst ℤ Z₁ B₂).rTensor S t = 0 →
      (LinearMap.snd ℤ Z₁ B₂).rTensor S t = 0 → t = 0 := by
    intro t h₁ h₂
    have h := hdec t
    rw [h₁, h₂] at h
    simpa using h.symm
  -- Bookkeeping identities relating `φ`, `ψ` to the components.
  have hfst_comp : (LinearMap.fst ℤ Z₁ B₂).comp φ = ι₁ := by ext u; rfl
  have hsnd_comp : (LinearMap.snd ℤ Z₁ B₂).comp φ = b := by ext u; rfl
  have hinr_fst : (LinearMap.fst ℤ Z₁ B₂).comp (LinearMap.inr ℤ Z₁ B₂) = 0 := by ext v; rfl
  have hinr_snd : (LinearMap.snd ℤ Z₁ B₂).comp (LinearMap.inr ℤ Z₁ B₂) = LinearMap.id := by
    ext v; rfl
  have hcompψ : ψ.comp (LinearMap.inr ℤ Z₁ B₂) = -ι₂ := by
    ext v
    simp [ψ, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.sub_apply]
  constructor
  · -- Injectivity of `b ⊗ S` on `ker (ι₁ ⊗ S)`.
    intro x₁ x₂ hi1 hi2 hb'
    have h₁ : (LinearMap.fst ℤ Z₁ B₂).rTensor S (φ.rTensor S (x₁ - x₂)) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfst_comp]
      simp [map_sub, hi1, hi2]
    have h₂ : (LinearMap.snd ℤ Z₁ B₂).rTensor S (φ.rTensor S (x₁ - x₂)) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hsnd_comp]
      simp [map_sub, hb']
    have hz0 : φ.rTensor S (x₁ - x₂) = 0 := hzero_of _ h₁ h₂
    have : x₁ - x₂ = 0 := hφr (by rw [hz0, map_zero])
    exact sub_eq_zero.mp this
  · -- Surjectivity of `b ⊗ S` onto `ker (ι₂ ⊗ S)`.
    intro y hy
    have hψw : (ψ.rTensor S) ((LinearMap.inr ℤ Z₁ B₂).rTensor S y) = 0 := by
      rw [← LinearMap.rTensor_comp_apply, hcompψ, LinearMap.rTensor_neg]
      simp [hy]
    have hw : (LinearMap.inr ℤ Z₁ B₂).rTensor S y ∈ Set.range (φ.rTensor S) :=
      (hex _).mp hψw
    obtain ⟨x, hx⟩ := hw
    refine ⟨x, ?_, ?_⟩
    · have h₁ : (LinearMap.fst ℤ Z₁ B₂).rTensor S (φ.rTensor S x) = 0 := by
        rw [hx, ← LinearMap.rTensor_comp_apply, hinr_fst]
        simp
      rwa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfst_comp] at h₁
    · have h₂ : (LinearMap.snd ℤ Z₁ B₂).rTensor S (φ.rTensor S x) = y := by
        rw [hx, ← LinearMap.rTensor_comp_apply, hinr_snd]
        simp
      rwa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hsnd_comp] at h₂

end Work.Pi6.SRANGE
