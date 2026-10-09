import Submission.Work.SSGRoute.ZDataTwo.Mu2ArithDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer correspondence at the base field

Every globally additive, locally constant cochain `z : G_k → 𝔽₂` is the Kummer character of some
`a ∈ kˣ`: `z σ = kummerChar a σ` for all `σ`.

This is `Work.SSGRoute.exists_kummerChar_of_additive_locConst` with the intermediate field `K`
replaced by the base field `k` (i.e. with `K = ⊥` and the identification `↥⊥ ≅ k` made
definitional), which is the form in which the `μ₂` local Tate system consumes it: combined with
`Work.SSGRoute.grunwald_surjective_two` it gives that every locally constant additive character of
a decomposition group `decomp k A` is the restriction of the Kummer character of a *global* unit
(`Work.SSGRoute.ZDataTwo.exists_kummerChar_agreeing_on_decomp`).

The proof is the proof of the intermediate-field version, with the `fixingSubgroup` machinery
dropped: `z ↦ Multiplicative.ofAdd ∘ z` is a homomorphism with open kernel, `zr` converts it into
a character with values in the square roots of unity of `k`, `kummer_character_realization_inf`
(Hilbert 90) realizes it by a Kummer resolvent `γ`, and the `kummerIdx` chase converts the
realization into the stated identity.
-/

namespace Work.SSGRoute.ZDataTwo

open scoped Classical

theorem exists_kummerChar_of_additive_locConst_base {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (z : (Ω ≃ₐ[k] Ω) → ZMod 2) (hz : ∀ g h : Ω ≃ₐ[k] Ω, z (g * h) = z g + z h)
    (hzc : SSGRoute.IsLocConstOn (⊤ : Subgroup (Ω ≃ₐ[k] Ω)) z) :
    ∃ a : kˣ, ∀ σ : Ω ≃ₐ[k] Ω,
      z σ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ := by
  classical
  have hz_one : z 1 = 0 := by
    have h := hz 1 1
    simp only [mul_one] at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h, ← two_mul, h2, zero_mul]
  let f : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz_one]
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (z (g * h)) =
          Multiplicative.ofAdd (z g) * Multiplicative.ofAdd (z h)
        rw [hz g h, ofAdd_add] }
  have hopen_f : IsOpen (f.ker : Set (Ω ≃ₐ[k] Ω)) := by
    obtain ⟨U, hUopen, hU⟩ := hzc
    refine Subgroup.isOpen_of_mem_nhds f.ker (g := 1) ?_
    refine Filter.mem_of_superset (hUopen.mem_nhds ?_) ?_
    · simpa using U.one_mem
    · intro u hu
      show Multiplicative.ofAdd (z u) = 1
      have h0 : z u = 0 := by
        have h := hU 1 (Subgroup.mem_top 1) u hu (Subgroup.mem_top u)
        simpa [hz_one] using h
      simp [h0]
  let zrK : Multiplicative (ZMod 2) ≃* ↥(rootsOfUnity 2 k) :=
    zr (isPrimitiveRoot_primRootUnit (F := k) (p := 2) hζ)
  let ω : (Ω ≃ₐ[k] Ω) →* ↥(rootsOfUnity 2 k) := zrK.toMonoidHom.comp f
  have hopen_ω : IsOpen (ω.ker : Set (Ω ≃ₐ[k] Ω)) := by
    have hkerω : (ω.ker : Subgroup (Ω ≃ₐ[k] Ω)) = f.ker := by
      ext σ
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show zrK (f σ) = 1 ↔ f σ = 1
      constructor
      · intro h
        exact zrK.injective (by rw [h, map_one])
      · intro h; rw [h, map_one]
    rw [show (ω.ker : Set (Ω ≃ₐ[k] Ω)) = (f.ker : Set (Ω ≃ₐ[k] Ω)) from by rw [hkerω]]
    exact hopen_f
  haveI hsep : IsSepClosure k Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  obtain ⟨γ, hγmem, hγdiv⟩ :=
    kummer_character_realization_inf (U := k) (L := Ω) (n := 2) (by norm_num) ω hopen_ω
  obtain ⟨x, hx⟩ := hγmem
  have hγ0 : γ ≠ 0 := by
    have h1 : γ / γ = 1 := by simpa using hγdiv 1
    intro h0
    rw [h0, div_zero] at h1
    exact zero_ne_one h1
  have hx0 : x ≠ 0 := by
    intro h0
    refine hγ0 ?_
    have h2 : γ * γ = 0 := by rw [← pow_two, ← hx, h0, map_zero]
    exact (mul_eq_zero.mp h2).elim id id
  let a : kˣ := Units.mk0 x hx0
  let γu : Ωˣ := Units.mk0 γ hγ0
  have hγu : γu ^ 2 = Units.map (algebraMap k Ω) a := by
    apply Units.ext
    show γ ^ 2 = (algebraMap k Ω) x
    exact hx.symm
  refine ⟨a, ?_⟩
  intro σ
  have hratio : Work.Kummer.kummerRatio σ γu =
      Units.map (algebraMap k Ω) (((ω σ : ↥(rootsOfUnity 2 k)) : kˣ)) := by
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    show (σ : Ω → Ω) γ / γ = algebraMap k Ω (((ω σ : ↥(rootsOfUnity 2 k)) : kˣ) : k)
    exact hγdiv σ
  rw [Work.SSGRoute.kummerChar_apply]
  rw [kummerIdx_congr 2 hζ a (kummerSqrt_pow (Ω := Ω) a) hγu σ]
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
        (Multiplicative.ofAdd (kummerIdx 2 hζ a γu hγu σ)) : Ωˣ)
      = (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
        (Multiplicative.ofAdd (z σ)) : Ωˣ) := by
    rw [← kummerIdx_spec 2 hζ a γu hγu σ, hratio]
    show Units.map (algebraMap k Ω)
        (((zr (isPrimitiveRoot_primRootUnit (F := k) (p := 2) hζ)
          (Multiplicative.ofAdd (z σ)) : ↥(rootsOfUnity 2 k)) : kˣ))
      = (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
          (Multiplicative.ofAdd (z σ)) : Ωˣ)
    exact units_map_zr_eq (E := Ω) hζ (Multiplicative.ofAdd (z σ))
  have hfin : Multiplicative.ofAdd (kummerIdx 2 hζ a γu hγu σ)
      = Multiplicative.ofAdd (z σ) :=
    (zr (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)).injective (Subtype.ext hkey)
  exact (congrArg Multiplicative.toAdd hfin).symm

end Work.SSGRoute.ZDataTwo
