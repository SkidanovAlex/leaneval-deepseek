import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coherence from an isometry extension along a constant shift

This file proves `Work.Coherence.coherent_of_isometry_extension`.

Setting `a := φ x₀ - τ x₀`, the hypothesis `hφshift` says that for every `x ∈ S` the value `φ x`
is the shift of `τ x` by the *constant* vector `a`.  The proof uses the `ℤ`-linear map

`degreeShift x₀ a : f ↦ (f 1 / x₀ 1) • a`,

which vanishes on `ℤ[S]^0` (all of whose elements satisfy `f 1 = 0`) and takes the value `a` on
every class function of degree `x₀ 1`, hence on every element of `S`.  The extension of `τ` is
then simply `τ' = τ + degreeShift x₀ a`; it agrees with `τ` on `ℤ[S]^0` and with `φ` on `S`.

The hypothesis `hφorth` says that the "`x₀`-row" of the Gram matrix of `(φ x)_{x ∈ S}` is the
`x₀`-row of the Gram matrix of `S`.  Together with `hφshift` and the fact that `τ` is an isometry
on `ℤ[S]^0` this forces the *full* Gram matrix of `(φ x)_{x ∈ S}` to be that of `S`: for
`x y ∈ S`, with `u = x - x₀`, `v = y - x₀` (both in `ℤ[S]^0`),

`⟨τ' x, τ' y⟩ = ⟨τ u + φ x₀, τ v + φ x₀⟩ = ⟨u,v⟩ + ⟨u,x₀⟩ + ⟨x₀,v⟩ + ⟨x₀,x₀⟩
 = ⟨u + x₀, v + x₀⟩ = ⟨x,y⟩`.

Hence `τ'` is an isometry on the whole lattice `ℤ[S]`, and its values on `S` are the virtual
characters `φ x`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

variable {H G : Type*}

section Aux

variable [Group H] [Fintype H] [Group G] [Fintype G]

/-! ### The degree shift -/

/-- For `x₀ : H → ℂ` and `a : G → ℂ`, the `ℤ`-linear map `f ↦ (f 1 / x₀ 1) • a`.  It vanishes on
the degree-zero part of `ℤ[S]` and is constant `= a` on all class functions of degree `x₀ 1`. -/
def degreeShift (x₀ : H → ℂ) (a : G → ℂ) : (H → ℂ) →ₗ[ℤ] (G → ℂ) :=
  (LinearMap.proj (R := ℤ) (φ := fun _ : H => ℂ) (1 : H)).smulRight ((x₀ 1)⁻¹ • a)

/-- The defining formula of the degree shift. -/
theorem degreeShift_apply (x₀ : H → ℂ) (a : G → ℂ) (f : H → ℂ) :
    degreeShift x₀ a f = (f 1 * (x₀ 1)⁻¹) • a := by
  simp only [degreeShift, LinearMap.smulRight_apply, LinearMap.proj_apply, smul_smul]

/-- The defining formula of the degree shift, unfolded on the sum `τ + degreeShift x₀ a`. -/
theorem add_degreeShift_apply (x₀ : H → ℂ) (a : G → ℂ) (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ))
    (f : H → ℂ) :
    (τ + degreeShift x₀ a) f = τ f + (f 1 * (x₀ 1)⁻¹) • a := by
  rw [LinearMap.add_apply, degreeShift_apply]

/-! ### Moving a `ℤ`-linear map through an integral combination -/

theorem map_sum_intCast_smul {ι : Type*} (s : Finset ι) (γ : ι → (H → ℂ)) (c : ι → ℤ)
    (σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) :
    σ (∑ x ∈ s, (c x : ℂ) • γ x) = ∑ x ∈ s, (c x : ℂ) • σ (γ x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => by
    conv_lhs => rw [Int.cast_smul_eq_zsmul, map_zsmul]
    conv_rhs => rw [Int.cast_smul_eq_zsmul]

/-! ### Inner products of a family with the same Gram matrix -/

theorem cfInner_family_coeff {S : Finset (H → ℂ)} (hS : Orthonormal S) {γ : S → (G → ℂ)}
    (hγ : ∀ x y : S, cfInner (γ x) (γ y) = cfInner (x : H → ℂ) (y : H → ℂ))
    {g : G → ℂ} {d : S → ℤ} (hg : g = ∑ x : S, (d x : ℂ) • γ x) (y : S) :
    cfInner g (γ y) = (d y : ℂ) := by
  subst hg
  rw [cfInner_sum_left, Finset.sum_eq_single y]
  · rw [cfInner_smul_left, hγ y y]
    have hyy : cfInner (y : H → ℂ) (y : H → ℂ) = 1 := by
      rw [hS _ y.2 _ y.2]; simp
    rw [hyy, mul_one]
  · intro b _ hb
    rw [cfInner_smul_left, hγ b y]
    have hne : (b : H → ℂ) ≠ (y : H → ℂ) := fun h => hb (Subtype.ext h)
    rw [hS _ b.2 _ y.2]
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ y) h

theorem cfInner_family_eq_sum_coeff_mul {S : Finset (H → ℂ)} (hS : Orthonormal S)
    {γ : S → (G → ℂ)}
    (hγ : ∀ x y : S, cfInner (γ x) (γ y) = cfInner (x : H → ℂ) (y : H → ℂ))
    {f g : G → ℂ} {c d : S → ℤ} (hf : f = ∑ x : S, (c x : ℂ) • γ x)
    (hg : g = ∑ x : S, (d x : ℂ) • γ x) :
    cfInner f g = ∑ x : S, (c x : ℂ) * (d x : ℂ) := by
  subst hf
  rw [cfInner_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cfInner_smul_left, cfInner_conj_symm, cfInner_family_coeff hS hγ hg x]
  simp

/-- It suffices to check the isometry property on the Gram matrix of the orthonormal set `S`. -/
theorem isometryOnAll_of_pairwise {S : Finset (H → ℂ)} (hS : Orthonormal S)
    {σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hσ : ∀ x ∈ S, ∀ y ∈ S, cfInner (σ x) (σ y) = cfInner x y) : IsometryOnAll S σ := by
  refine ⟨fun α hα β hβ => ?_⟩
  obtain ⟨c, hc⟩ := mem_zSpan.mp hα
  obtain ⟨d, hd⟩ := mem_zSpan.mp hβ
  subst hc
  subst hd
  have hγ : ∀ x y : S, cfInner (σ (x : H → ℂ)) (σ (y : H → ℂ))
      = cfInner (x : H → ℂ) (y : H → ℂ) := fun x y => hσ x x.2 y y.2
  have h1 : σ (∑ x : S, (c x : ℂ) • (x : H → ℂ))
      = ∑ x : S, (c x : ℂ) • σ (x : H → ℂ) :=
    map_sum_intCast_smul Finset.univ (fun x : S => (x : H → ℂ)) c σ
  have h2 : σ (∑ x : S, (d x : ℂ) • (x : H → ℂ))
      = ∑ x : S, (d x : ℂ) • σ (x : H → ℂ) :=
    map_sum_intCast_smul Finset.univ (fun x : S => (x : H → ℂ)) d σ
  rw [h1, h2]
  have hL : cfInner (∑ x : S, (c x : ℂ) • σ (x : H → ℂ))
      (∑ x : S, (d x : ℂ) • σ (x : H → ℂ)) = ∑ x : S, (c x : ℂ) * (d x : ℂ) :=
    cfInner_family_eq_sum_coeff_mul hS hγ rfl rfl
  have hR : cfInner (∑ x : S, (c x : ℂ) • (x : H → ℂ))
      (∑ x : S, (d x : ℂ) • (x : H → ℂ)) = ∑ x : S, (c x : ℂ) * (d x : ℂ) :=
    cfInner_eq_sum_coeff_mul hS rfl rfl
  rw [hL, hR]

/-- The four-term expansion of `⟨A + B, C + D⟩`. -/
theorem cfInner_add_add (A B C D : G → ℂ) :
    cfInner (A + B) (C + D)
      = (cfInner A C + cfInner B C) + (cfInner A D + cfInner B D) := by
  simp only [cfInner_add_left, cfInner_add_right]

end Aux

section Main

theorem coherent_of_isometry_extension {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Orthonormal S) {x₀ : H → ℂ} (hx₀ : x₀ ∈ S) (hdeg : ∀ x ∈ S, x 1 = x₀ 1)
    (hd : x₀ 1 ≠ 0) (hτ : IsometryOn S τ) {φ : (H → ℂ) → (G → ℂ)}
    (hφorth : ∀ x ∈ S, cfInner (φ x₀) (φ x) = cfInner x₀ x)
    (hφshift : ∀ x ∈ S, φ x - τ x = φ x₀ - τ x₀)
    (hφchar : ∀ x ∈ S, IsVChar (φ x)) : Coherent S τ := by
  -- `τ' x = φ x` on `S`.
  have hval : ∀ x ∈ S, (τ + degreeShift x₀ (φ x₀ - τ x₀)) x = φ x := by
    intro x hx
    rw [LinearMap.add_apply, degreeShift_apply, hdeg x hx, mul_inv_cancel₀ hd, one_smul,
      ← hφshift x hx]
    exact add_sub_cancel _ _
  -- `x - x₀` lies in the degree-zero lattice for `x ∈ S`.
  have hsub_mem : ∀ x ∈ S, x - x₀ ∈ ZSpan0 S := by
    intro x hx
    rw [mem_zSpan0]
    refine ⟨AddSubgroup.sub_mem _ (self_mem_zSpan hx) (self_mem_zSpan hx₀), ?_⟩
    rw [Pi.sub_apply, hdeg x hx, sub_self]
  -- `τ (x - x₀) = φ x - φ x₀`.
  have htau_sub : ∀ x ∈ S, τ (x - x₀) = φ x - φ x₀ := by
    intro x hx
    rw [map_sub]
    exact (sub_eq_sub_iff_sub_eq_sub.mp (hφshift x hx)).symm
  -- `τ' x = τ (x - x₀) + φ x₀` splits the correction off.
  have hsplit : ∀ x ∈ S, (τ + degreeShift x₀ (φ x₀ - τ x₀)) x = τ (x - x₀) + φ x₀ := by
    intro x hx
    rw [hval x hx, htau_sub x hx]
    exact (sub_add_cancel _ _).symm
  -- The Gram matrix of `(φ x)_{x ∈ S}` agrees with that of `S`.
  have hgram : ∀ x ∈ S, ∀ y ∈ S,
      cfInner ((τ + degreeShift x₀ (φ x₀ - τ x₀)) x)
        ((τ + degreeShift x₀ (φ x₀ - τ x₀)) y) = cfInner x y := by
    intro x hx y hy
    have hA : cfInner (φ x) (φ x₀) = cfInner x x₀ := by
      calc cfInner (φ x) (φ x₀)
          = starRingEnd ℂ (cfInner (φ x₀) (φ x)) := cfInner_conj_symm _ _
        _ = starRingEnd ℂ (cfInner x₀ x) := by rw [hφorth x hx]
        _ = cfInner x x₀ := (cfInner_conj_symm _ _).symm
    have hB : cfInner (φ x₀) (φ x₀) = cfInner x₀ x₀ := hφorth x₀ hx₀
    have hcrossL : cfInner (τ (x - x₀)) (φ x₀) = cfInner (x - x₀) x₀ := by
      rw [htau_sub x hx, cfInner_sub_left, hA, hB, ← cfInner_sub_left]
    have hcrossR : cfInner (φ x₀) (τ (y - x₀)) = cfInner x₀ (y - x₀) := by
      rw [htau_sub y hy, cfInner_sub_right, hφorth y hy, hB, ← cfInner_sub_right]
    have e1 : cfInner ((τ + degreeShift x₀ (φ x₀ - τ x₀)) x)
          ((τ + degreeShift x₀ (φ x₀ - τ x₀)) y)
        = (cfInner (x - x₀) (y - x₀) + cfInner x₀ (y - x₀))
          + (cfInner (x - x₀) x₀ + cfInner x₀ x₀) := by
      rw [hsplit x hx, hsplit y hy, cfInner_add_add,
        hτ.inner_eq (x - x₀) (hsub_mem x hx) (y - x₀) (hsub_mem y hy), hcrossL, hcrossR, hB]
    have hExy : cfInner x y = cfInner ((x - x₀) + x₀) ((y - x₀) + x₀) := by
      simp only [sub_add_cancel]
    have e2 : cfInner x y
        = (cfInner (x - x₀) (y - x₀) + cfInner x₀ (y - x₀))
          + (cfInner (x - x₀) x₀ + cfInner x₀ x₀) := by
      rw [hExy, cfInner_add_add]
    rw [e1, e2]
  -- Agreement with `τ` on the degree-zero lattice.
  have hagree : ∀ α ∈ ZSpan0 S, (τ + degreeShift x₀ (φ x₀ - τ x₀)) α = τ α := by
    intro α hα
    have h0 : α 1 = 0 := hα.2
    rw [LinearMap.add_apply, degreeShift_apply, h0]
    simp
  exact ⟨τ + degreeShift x₀ (φ x₀ - τ x₀), hagree, isometryOnAll_of_pairwise hS hgram,
    fun χ hχ => by rw [hval χ hχ]; exact hφchar χ hχ⟩

end Main

end Work.Coherence
