import Mathlib
import Submission.Work.SSGRoute.E1aFinal.HasseDefs
import Submission.Work.SSGRoute.ExtChain.C2Lift
import Submission.Work.SSGRoute.ExtChain.c2_h90_brick
import Submission.Work.SSGRoute.ExtChain.c2_hasse_brick
import Submission.Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.E1aFinal

open CategoryTheory

noncomputable section

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
variable {σ : Ω ≃ₐ[k] Ω}

/-! ## The two arithmetic lifts

Let `τ = res k K σ : Gal(K/k)` be an involution `≠ 1` (the generator of `H`).  The two classical
inputs of the Hasse principle at `H` are:

* **(fixed)** every `τ`-fixed class in `C_K` is the class of a `τ`-fixed idèle;
* **(anti-fixed)** every `τ`-anti-fixed class in `C_K` is the class of a `τ`-anti-fixed idèle.

The first uses Hilbert 90 in the trace form `c2_h90_brick`, the second is Hasse's norm theorem in
the involution form `c2_hasse_brick`.
-/

/-- The action of `τ` on the principal idèles, in the normal form matching
`NK.GlobalCFT.Galois.globalCFT_smul_principalIdele`. -/
theorem smul_principalIdele (τ : ↥K ≃ₐ[k] ↥K) (u : (↥K)ˣ) :
    τ • NK.GlobalCFT.Idele.principalIdele ↥K u
      = NK.GlobalCFT.Idele.principalIdele ↥K (Units.map τ.toMulEquiv.toMonoidHom u) :=
  NK.GlobalCFT.Galois.globalCFT_smul_principalIdele τ u

/-- The action of `τ` on the units of `K`, in the same normal form. -/
theorem smul_units (τ : ↥K ≃ₐ[k] ↥K) (u : (↥K)ˣ) :
    τ • u = Units.map τ.toMulEquiv.toMonoidHom u :=
  AlgEquiv.smul_units_def τ u

/-- **The fixed lift.**  A `τ`-fixed class of idèles is represented by a `τ`-fixed idèle. -/
theorem exists_fixed_lift_idele (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (c : NK.GlobalCFT.IdeleClassGroup ↥K) (hc : SSGRoute.res k K σ • c = c) :
    ∃ y : NK.GlobalCFT.Idele ↥K,
      SSGRoute.res k K σ • y = y ∧ NK.GlobalCFT.IdeleClassGroup.mk ↥K y = c := by
  classical
  set τ : ↥K ≃ₐ[k] ↥K := SSGRoute.res k K σ with hτdef
  have hτsq : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, hσ, map_one]
  have hτne : τ ≠ 1 := by rw [hτdef]; exact hnt
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτsq
  obtain ⟨y₀, hy₀⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective ↥K c
  -- the difference `y₀⁻¹ * (τ • y₀)` is a principal idèle
  have hmk : NK.GlobalCFT.IdeleClassGroup.mk ↥K (τ • y₀) = c := by
    rw [← NK.GlobalCFT.IdeleClassGroup.smul_mk τ y₀, hy₀]
    exact hc
  have hmem : y₀⁻¹ * (τ • y₀) ∈ NK.GlobalCFT.Idele.principalSubgroup ↥K :=
    NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff.mp (hy₀.trans hmk.symm)
  obtain ⟨u, hu⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hmem
  -- `u` has norm one
  have hτy₀ : τ • y₀ = y₀ * NK.GlobalCFT.Idele.principalIdele ↥K u := by
    rw [hu, mul_inv_cancel_left]
  have h1 : τ • (y₀⁻¹ * (τ • y₀)) = (τ • y₀)⁻¹ * y₀ := by
    rw [smul_mul', smul_inv', ← mul_smul, hττ, one_smul]
  have hτu : τ • u = u⁻¹ := by
    refine NK.HassePrinciple.principalIdele_injective ↥K ?_
    rw [smul_units, ← smul_principalIdele, hu, map_inv, hu, mul_inv_rev, inv_inv]
    exact h1
  have hnorm : u * (τ • u) = 1 := by rw [hτu, mul_inv_cancel]
  obtain ⟨v, hv⟩ := Work.SSGRoute.ExtChain.c2_h90_brick τ hτsq hτne u hnorm
  have hv' : u = v * (Units.map τ.toMulEquiv.toMonoidHom v)⁻¹ := by
    rw [hv, smul_units]
  refine ⟨y₀ * NK.GlobalCFT.Idele.principalIdele ↥K v, ?_, ?_⟩
  · have hy1 : τ • (y₀ * NK.GlobalCFT.Idele.principalIdele ↥K v)
        = (y₀ * NK.GlobalCFT.Idele.principalIdele ↥K u)
          * NK.GlobalCFT.Idele.principalIdele ↥K (Units.map τ.toMulEquiv.toMonoidHom v) := by
      rw [smul_mul', smul_principalIdele, hτy₀]
    rw [hy1, hv', map_mul, map_inv]
    apply Additive.ofMul.injective
    simp only [Work.SSGRoute.ExtChain.c2_ofMul_mul, Work.SSGRoute.ExtChain.c2_ofMul_inv]
    abel
  · rw [map_mul, hy₀]
    have h1 : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.GlobalCFT.Idele.principalIdele ↥K v) = 1 := by
      rw [NK.GlobalCFT.IdeleClassGroup.mk_apply, QuotientGroup.eq_one_iff]
      exact NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨v, rfl⟩
    rw [h1, mul_one]

/-- **The anti-fixed lift.**  A `τ`-anti-fixed class of idèles is represented by a `τ`-anti-fixed
idèle.  This is Hasse's norm theorem for the quadratic extension `K / K^τ`. -/
theorem exists_anti_lift_idele (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (c : NK.GlobalCFT.IdeleClassGroup ↥K) (hc : SSGRoute.res k K σ • c = c⁻¹) :
    ∃ y : NK.GlobalCFT.Idele ↥K,
      SSGRoute.res k K σ • y = y⁻¹ ∧ NK.GlobalCFT.IdeleClassGroup.mk ↥K y = c := by
  classical
  set τ : ↥K ≃ₐ[k] ↥K := SSGRoute.res k K σ with hτdef
  have hτsq : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, hσ, map_one]
  have hτne : τ ≠ 1 := by rw [hτdef]; exact hnt
  obtain ⟨y₀, hy₀⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective ↥K c
  -- `y₀ * (τ • y₀)` is a principal idèle
  have hmk : NK.GlobalCFT.IdeleClassGroup.mk ↥K (y₀ * (τ • y₀)) = 1 := by
    rw [map_mul, ← NK.GlobalCFT.IdeleClassGroup.smul_mk τ y₀, hy₀, hc, mul_inv_cancel]
  have hmem : y₀ * (τ • y₀) ∈ NK.GlobalCFT.Idele.principalSubgroup ↥K := by
    rw [← QuotientGroup.eq_one_iff, ← NK.GlobalCFT.IdeleClassGroup.mk_apply]
    exact hmk
  obtain ⟨w₀, hw₀⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hmem
  -- Hasse's norm theorem in involution form
  obtain ⟨w, hw⟩ := Work.SSGRoute.ExtChain.c2_hasse_brick τ hτsq hτne y₀ w₀ hw₀.symm
  have hτy₀ : τ • y₀ = NK.GlobalCFT.Idele.principalIdele ↥K w₀ * y₀⁻¹ := by
    rw [hw₀]
    apply Additive.ofMul.injective
    simp only [Work.SSGRoute.ExtChain.c2_ofMul_mul, Work.SSGRoute.ExtChain.c2_ofMul_inv]
    abel
  have hw' : NK.GlobalCFT.Idele.principalIdele ↥K w₀
      = NK.GlobalCFT.Idele.principalIdele ↥K w
        * NK.GlobalCFT.Idele.principalIdele ↥K (Units.map τ.toMulEquiv.toMonoidHom w) := by
    rw [hw, map_mul, smul_units]
  refine ⟨y₀ * (NK.GlobalCFT.Idele.principalIdele ↥K w)⁻¹, ?_, ?_⟩
  · have hy1 : τ • (y₀ * (NK.GlobalCFT.Idele.principalIdele ↥K w)⁻¹)
        = (τ • y₀) * (NK.GlobalCFT.Idele.principalIdele ↥K (Units.map τ.toMulEquiv.toMonoidHom w))⁻¹ := by
      rw [smul_mul', smul_inv', smul_principalIdele]
    have hy2 : (y₀ * (NK.GlobalCFT.Idele.principalIdele ↥K w)⁻¹)⁻¹
        = NK.GlobalCFT.Idele.principalIdele ↥K w * y₀⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [hy1, hy2, hτy₀, hw']
    apply Additive.ofMul.injective
    simp only [Work.SSGRoute.ExtChain.c2_ofMul_mul, Work.SSGRoute.ExtChain.c2_ofMul_inv]
    abel
  · rw [map_mul, hy₀]
    have h1 : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.GlobalCFT.Idele.principalIdele ↥K w) = 1 := by
      rw [NK.GlobalCFT.IdeleClassGroup.mk_apply, QuotientGroup.eq_one_iff]
      exact NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨w, rfl⟩
    rw [map_inv, h1, inv_one, mul_one]

/-- The generator `σ̄` of `H = ⟨σ̄⟩` generates `H`. -/
theorem zpowers_gen_eq_top (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (σ : Ω ≃ₐ[k] Ω) :
    Subgroup.zpowers (gen (k := k) (K := K) (σ := σ)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro y
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

/-- **(S1) The split case of the `C₂`-lattice Hasse principle.**  If the `ℤ`-lattice `M` with its
`H`-action has a `ℤ`-basis on which the generator `σ̄` of `H = ⟨σ̄⟩` acts diagonally with
eigenvalues `±1` (i.e. `M` is a direct sum of copies of the trivial and the sign representation),
then the coefficient change `Kˣ → 𝕀_K` makes `Ext¹_H(M, Kˣ) → Ext¹_H(M, 𝕀_K)` injective.

This is the split case of `Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general`, which is proved in
this workspace (`Work.SSGRoute.ExtChain.c2_lattice_lift`, via the `±1`-adapted-basis normal form and
the two involution bricks `c2_h90_brick` / `c2_hasse_brick`): the general lattice Hasse principle
implies the present split case, whose hypothesis `IsSplit M` is not needed for it.  The file also
records, as proved helper lemmas, the two arithmetic lifts of the direct route
(`exists_fixed_lift_idele`: a `σ̄`-fixed idèle class has a `σ̄`-fixed representative, from Hilbert 90;
`exists_anti_lift_idele`: a `σ̄`-anti-fixed class has a `σ̄`-anti-fixed representative, from Hasse's
norm theorem in involution form). -/
theorem hasseExt1_C2_lattice_split (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
    [Module.Finite ℤ M.V] [Module.Free ℤ M.V] (h : IsSplit M) :
    HasseStat M :=
  Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general p k Ω K σ hσ hnt M

end

end Work.SSGRoute.E1aFinal
