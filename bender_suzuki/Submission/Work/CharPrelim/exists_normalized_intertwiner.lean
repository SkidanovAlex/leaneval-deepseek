import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped MonoidAlgebra

namespace Work.CharPrelim

/-- **Normalized intertwiner.**  Let `ρ` be an irreducible finite-dimensional complex
representation of a normal subgroup `K` of a group `G`, let `g₀ ∈ G` with `g₀ ^ n ∈ K`, and let
`P₀` realize the action of `g₀` on the `K`-representation `ρ` (`P₀` intertwines `ρ` with its
`g₀`-conjugate).  Then one can rescale `P₀` by a scalar so that the resulting intertwiner `P`
satisfies the normalized relation `P ^ n = ρ (g₀ ^ n)`. -/
theorem exists_normalized_intertwiner {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {K : Subgroup G} [K.Normal]
    (ρ : Representation ℂ ↥K V) (hρ : ρ.IsIrreducible)
    (g₀ : G) (n : ℕ) (hk : g₀ ^ (n : ℤ) ∈ K) (P₀ : V ≃ₗ[ℂ] V)
    (hP₀ : ∀ k : ↥K, (P₀ : V →ₗ[ℂ] V) ∘ₗ ρ k =
      ρ ⟨g₀ * (k : G) * g₀⁻¹, (inferInstance : K.Normal).conj_mem (k : G) k.2 g₀⟩
        ∘ₗ (P₀ : V →ₗ[ℂ] V)) :
    ∃ P : V ≃ₗ[ℂ] V,
      (∀ k : ↥K, (P : V →ₗ[ℂ] V) ∘ₗ ρ k =
        ρ ⟨g₀ * (k : G) * g₀⁻¹, (inferInstance : K.Normal).conj_mem (k : G) k.2 g₀⟩
          ∘ₗ (P : V →ₗ[ℂ] V)) ∧
      ((P ^ (n : ℤ) : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = ρ ⟨g₀ ^ (n : ℤ), hk⟩ := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨P₀, hP₀, ?_⟩
    have h1 : (⟨g₀ ^ ((0:ℕ):ℤ), hk⟩ : ↥K) = 1 := Subtype.ext (by simp)
    rw [h1]; simp; rfl
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    haveI hρi : ρ.IsIrreducible := hρ
    haveI : Nontrivial V :=
      IsSimpleModule.nontrivial ℂ[↥K] ρ.asModule
    have hPj : ∀ j : ℕ, ∀ k : ↥K,
        ((P₀ ^ j : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) ∘ₗ ρ k =
          ρ ⟨g₀ ^ j * (k : G) * (g₀ ^ j)⁻¹,
              (inferInstance : K.Normal).conj_mem (k : G) k.2 (g₀ ^ j)⟩
            ∘ₗ ((P₀ ^ j : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
      intro j
      induction j with
      | zero => intro k; simp
      | succ j ih =>
          intro k
          have hpow : ((P₀ ^ (j+1) : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
              ((P₀ ^ j : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) ∘ₗ ((P₀ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
            rw [pow_succ, LinearEquiv.coe_toLinearMap_mul]
            rfl
          rw [hpow, LinearMap.comp_assoc, hP₀ k]
          conv_lhs => rw [← LinearMap.comp_assoc]
          rw [ih ⟨g₀ * (k:G) * g₀⁻¹, (inferInstance : K.Normal).conj_mem (k:G) k.2 g₀⟩]
          conv_lhs => rw [LinearMap.comp_assoc]
          congr 1
          congr 1
          apply Subtype.ext
          group
    have hk' : g₀ ^ n ∈ K := by simpa [zpow_natCast] using hk
    set gn : ↥K := ⟨g₀ ^ (n : ℤ), hk⟩ with hgn
    have hgn' : gn = ⟨g₀ ^ n, hk'⟩ := Subtype.ext (by simp [hgn, zpow_natCast])
    have hTint : ∀ k : ↥K,
        (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) ∘ₗ ρ k =
          ρ k ∘ₗ (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) := by
      intro k
      have hkey : ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) * ρ k =
          ρ ⟨g₀ ^ n * (k : G) * (g₀ ^ n)⁻¹,
              (inferInstance : K.Normal).conj_mem (k : G) k.2 (g₀ ^ n)⟩
            * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := hPj n k
      calc (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) ∘ₗ ρ k
          = ρ gn⁻¹ * (((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) * ρ k) := mul_assoc _ _ _
        _ = ρ gn⁻¹ * (ρ ⟨g₀ ^ n * (k : G) * (g₀ ^ n)⁻¹,
                (inferInstance : K.Normal).conj_mem (k : G) k.2 (g₀ ^ n)⟩
              * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) := by rw [hkey]
        _ = (ρ gn⁻¹ * ρ ⟨g₀ ^ n * (k : G) * (g₀ ^ n)⁻¹,
                (inferInstance : K.Normal).conj_mem (k : G) k.2 (g₀ ^ n)⟩)
              * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := (mul_assoc _ _ _).symm
        _ = ρ (gn⁻¹ * ⟨g₀ ^ n * (k : G) * (g₀ ^ n)⁻¹,
                (inferInstance : K.Normal).conj_mem (k : G) k.2 (g₀ ^ n)⟩)
              * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by rw [← map_mul]
        _ = ρ (k * gn⁻¹) * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
              congr 1
              apply congrArg ρ
              apply Subtype.ext
              rw [hgn']
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              group
        _ = (ρ k * ρ gn⁻¹) * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by rw [map_mul]
        _ = ρ k * (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) := mul_assoc _ _ _
    let T : ρ.IntertwiningMap ρ :=
      LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
        (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V))
        (fun k v => by
          have h := LinearMap.congr_fun (hTint k) v
          simpa [LinearMap.comp_apply] using h)
    obtain ⟨c, hc⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).2 T
    have hTc : (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) = c • LinearMap.id := by
      have h2 : (algebraMap ℂ (ρ.IntertwiningMap ρ) c).toLinearMap = T.toLinearMap :=
        congrArg Representation.IntertwiningMap.toLinearMap hc
      rw [Representation.IntertwiningMap.algebraMap_apply,
          Representation.IntertwiningMap.toLinearMap_smul] at h2
      rw [show Representation.IntertwiningMap.toLinearMap (1 : ρ.IntertwiningMap ρ) = LinearMap.id
            from Representation.IntertwiningMap.toLinearMap_id ρ] at h2
      rw [h2]
      rfl
    have hbij : Function.Bijective (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) := by
      have h1 : Function.Bijective (ρ gn⁻¹) := Representation.apply_bijective ρ gn⁻¹
      have h2 : Function.Bijective (((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) :=
        (P₀ ^ n : V ≃ₗ[ℂ] V).bijective
      have h3 : Function.Bijective ((ρ gn⁻¹) ∘ (((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V))) :=
        h1.comp h2
      exact h3
    have hc0 : c ≠ 0 := by
      intro hcz
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h0 : (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) v = 0 := by
        rw [hTc, hcz]; simp
      have h1 : (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) v =
          (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) 0 := by rw [h0, map_zero]
      exact hv (hbij.injective h1)
    have hPn : ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = c • ρ gn := by
      have hid : ρ gn * ρ gn⁻¹ = (1 : V →ₗ[ℂ] V) := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)
          = ρ gn * (ρ gn⁻¹ * ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) := by
              rw [← mul_assoc, hid, one_mul]
        _ = ρ gn * (c • LinearMap.id) := by rw [hTc]
        _ = c • ρ gn := by
              rw [Algebra.mul_smul_comm]
              exact congrArg (c • ·) (mul_one (ρ gn))
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹ : ℂ) hnpos
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, zero_pow hn] at ha
      exact inv_ne_zero hc0 ha.symm
    have hPbij : Function.Bijective (a • (P₀ : V →ₗ[ℂ] V)) := by
      refine ⟨?_, ?_⟩
      · intro x y h
        apply P₀.injective
        simpa [LinearMap.smul_apply, ha0] using h
      · intro y
        refine ⟨P₀.symm (a⁻¹ • y), ?_⟩
        simp [LinearMap.smul_apply, ha0]
    let P : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective (a • (P₀ : V →ₗ[ℂ] V)) hPbij
    have hPco : (P : V →ₗ[ℂ] V) = a • (P₀ : V →ₗ[ℂ] V) := rfl
    have hle : ((P₀ ^ n : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = (P₀ : V →ₗ[ℂ] V) ^ n :=
      map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom P₀ n
    have hPpow : (P : V →ₗ[ℂ] V) ^ n = ρ gn := by
      rw [hPco, smul_pow, ← hle, hPn, smul_smul, ha, inv_mul_cancel₀ hc0, one_smul]
    refine ⟨P, ?_, ?_⟩
    · intro k
      rw [hPco, LinearMap.smul_comp, hP₀ k, LinearMap.comp_smul]
    · have hlepow : ((P ^ (n : ℤ) : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = (P : V →ₗ[ℂ] V) ^ n := by
        rw [zpow_natCast]
        exact map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom P n
      rw [hlepow, hPpow]

end Work.CharPrelim
