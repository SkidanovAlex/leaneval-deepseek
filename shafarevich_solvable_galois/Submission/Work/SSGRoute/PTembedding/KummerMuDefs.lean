import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
import Submission.Work.SSGRoute.LTDArch.Defs
import Submission.Work.SSGRoute.PTembedding.localKummer_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic coefficient module `μ_p ⊆ Ω` and its identification with `DualMod p T`
-/

open SSGRoute
open Work.SSGRoute

namespace Work.SSGRoute.PTembedding
namespace MupCard

noncomputable section

set_option linter.style.haveILetI false

/-! ## Rank-one `𝔽_p[G]`-modules and the scalar of the action -/

section RankOne

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {T : Type} [AddCommGroup T]
  [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]

omit [SMulCommClass G (ZMod p) T] in
/-- The chosen generator `Ach.t0 p T h` is transported by `g` to a scalar multiple of itself. -/
theorem exists_smul_t0_eq (h : Module.finrank (ZMod p) T = 1) (g : G) :
    ∃ c : ZMod p, g • Ach.t0 p T h = c • Ach.t0 p T h := by
  refine ⟨(Ach.rankOneEquiv p T h).symm (g • Ach.t0 p T h), ?_⟩
  have ht : Ach.t0 p T h = Ach.rankOneEquiv p T h 1 := rfl
  rw [ht, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]

/-- The scalar by which `g` acts on the chosen generator. -/
noncomputable def rankOneScalar (h : Module.finrank (ZMod p) T = 1) (g : G) : ZMod p :=
  Classical.choose (exists_smul_t0_eq h g)

theorem rankOneScalar_spec (h : Module.finrank (ZMod p) T = 1) (g : G) :
    g • Ach.t0 p T h = rankOneScalar h g • Ach.t0 p T h :=
  Classical.choose_spec (exists_smul_t0_eq h g)

theorem rankOneScalar_ne_zero (h : Module.finrank (ZMod p) T = 1) (g : G) :
    rankOneScalar h g ≠ 0 := by
  intro h0
  have h2 := rankOneScalar_spec h g
  rw [h0, zero_smul] at h2
  have h3 : Ach.t0 p T h = 0 := by
    have hh := congrArg (fun x => g⁻¹ • x) h2
    rwa [smul_zero, inv_smul_smul] at hh
  exact Ach.t0_ne_zero p T h h3

/-- The dual action on `Ach.coord p T h` is by the inverse scalar. -/
theorem smul_coord_eq_inv_smul (h : Module.finrank (ZMod p) T = 1) (g : G) :
    g • Ach.coord p T h = (rankOneScalar h g)⁻¹ • Ach.coord p T h := by
  have hc : rankOneScalar h g ≠ 0 := rankOneScalar_ne_zero h g
  have hgt : g • Ach.t0 p T h = rankOneScalar h g • Ach.t0 p T h := rankOneScalar_spec h g
  have hsm : rankOneScalar h g • (g⁻¹ • Ach.t0 p T h) = Ach.t0 p T h := by
    calc rankOneScalar h g • (g⁻¹ • Ach.t0 p T h)
        = g⁻¹ • (rankOneScalar h g • Ach.t0 p T h) :=
          (smul_comm g⁻¹ (rankOneScalar h g) (Ach.t0 p T h)).symm
      _ = g⁻¹ • (g • Ach.t0 p T h) := by rw [← hgt]
      _ = Ach.t0 p T h := inv_smul_smul g (Ach.t0 p T h)
  have hinv : g⁻¹ • Ach.t0 p T h = (rankOneScalar h g)⁻¹ • Ach.t0 p T h := by
    have h2 := congrArg (fun x => (rankOneScalar h g)⁻¹ • x) hsm
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    exact h2
  ext s
  have hs : g⁻¹ • s = (rankOneScalar h g)⁻¹ • s := by
    have e1 : s = (Ach.coord p T h s) • Ach.t0 p T h := (Ach.smul_coord_t0 p T h s).symm
    conv_lhs => rw [e1]
    conv_rhs => rw [e1]
    rw [smul_comm, hinv, smul_smul, smul_smul, mul_comm]
  rw [DualMod.dualSMul_apply, hs, map_smul, LinearMap.smul_apply]

end RankOne

/-! ## The cyclotomic action on `T` and on `DualMod p T` -/

section CyclotomicAction

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : Ω} {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- If `g ∈ Gal(K/k)` maps the primitive `p`-th root of unity `ζ ∈ K` to `ζ^m`, then
`(m : ZMod p) • (g • t) = t` for every `t : T`. -/
theorem nsmul_smul_eq_of_smul_zeta_eq_pow (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    ∀ t : T, (m : ZMod p) • (g • t) = t := by
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := Ω) g
  have hσζ : σ • ζ = ζ ^ m := by
    have h2 : ((AlgEquiv.restrictNormalHom K σ) (⟨ζ, hζK⟩ : K) : Ω) = σ • ζ := by
      rw [AlgEquiv.smul_def]
      exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ (⟨ζ, hζK⟩ : K)
    have h4 : (g (⟨ζ, hζK⟩ : K) : Ω) = ζ ^ m := by
      rw [← AlgEquiv.smul_def, hm, IntermediateField.coe_pow]
    rw [← h2, hσ, h4]
  intro t
  have h := hT.2 σ m hσζ t
  have hres : (SSGRoute.res k K) σ = g := hσ
  rw [hres] at h
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) m (g • t)] at h
  exact h

/-- **The action on `T` is the inverse of the cyclotomic character.** -/
theorem smul_eq_inv_of_smul_zeta_eq_pow (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    ∀ t : T, g • t = ((m : ZMod p))⁻¹ • t := by
  have hkey := nsmul_smul_eq_of_smul_zeta_eq_pow hζK hT g m hm
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h0
    have h : Ach.t0 p T hT.1 = 0 := by
      have h1 := hkey (Ach.t0 p T hT.1)
      rw [h0, zero_smul] at h1
      exact h1.symm
    exact Ach.t0_ne_zero p T hT.1 h
  intro t
  calc g • t = ((m : ZMod p))⁻¹ • ((m : ZMod p) • (g • t)) := by
        rw [inv_smul_smul₀ hm0]
    _ = ((m : ZMod p))⁻¹ • t := by rw [hkey t]

/-- **`g` acts on `DualMod p T` by the cyclotomic character.** -/
theorem dualMod_smul_eq (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m)
    (φ : Work.SSGRoute.DualMod p T) :
    g • φ = (m : ZMod p) • φ := by
  have hkey := nsmul_smul_eq_of_smul_zeta_eq_pow hζK hT g m hm
  ext t
  have h1 : g⁻¹ • t = (m : ZMod p) • t := by
    have h := hkey (g⁻¹ • t)
    rw [smul_inv_smul] at h
    exact h.symm
  rw [DualMod.dualSMul_apply, LinearMap.smul_apply, h1, map_smul, smul_eq_mul]

end CyclotomicAction

/-! ## `μ_p ⊆ K` as an `𝔽_p`-module -/

section MuAdd

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- `μ_p ⊆ K` as an additive group. -/
abbrev MuAdd (p : ℕ) (K : IntermediateField k Ω) : Type := Additive (rootsOfUnity p K)

theorem toMul_nsmul {G : Type*} [Monoid G] (n : ℕ) (x : Additive G) :
    Additive.toMul (n • x) = Additive.toMul x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, toMul_add, ih, pow_succ]

theorem ofMul_nsmul {G : Type*} [Monoid G] (n : ℕ) (x : G) :
    n • (Additive.ofMul x) = Additive.ofMul (x ^ n) := by
  apply Additive.toMul.injective
  show Additive.toMul (n • Additive.ofMul x) = Additive.toMul (Additive.ofMul (x ^ n))
  rw [toMul_nsmul (G := G) n (Additive.ofMul x)]
  rfl

theorem smul_nsmul_comm {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (g : G) (n : ℕ) (x : M) : g • (n • x) = n • (g • x) := by
  induction n with
  | zero => rw [zero_nsmul, smul_zero, zero_nsmul]
  | succ n ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]

theorem nsmulMuAdd_eq_zero (K : IntermediateField k Ω) (x : MuAdd p K) : p • x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  show (Additive.toMul x : rootsOfUnity p K) ^ p = 1
  apply Subtype.ext
  show ((Additive.toMul x : rootsOfUnity p K) : Kˣ) ^ p = 1
  exact (mem_rootsOfUnity p ((Additive.toMul x : rootsOfUnity p K) : Kˣ)).mp (Additive.toMul x).2

noncomputable instance instModuleMuAdd (K : IntermediateField k Ω) : Module (ZMod p) (MuAdd p K) :=
  AddCommGroup.zmodModule (nsmulMuAdd_eq_zero (p := p) K)

theorem zmod_smul_eq_nsmul_val {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (r : ZMod p) (m : M) : r • m = r.val • m :=
  Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul p r m

noncomputable instance instSMulCommClassMuAdd (K : IntermediateField k Ω) :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p) (MuAdd p K) where
  smul_comm g c x := by
    rw [zmod_smul_eq_nsmul_val (p := p) c x, zmod_smul_eq_nsmul_val (p := p) c (g • x),
      smul_nsmul_comm]

end MuAdd

/-! ## The generator of `μ_p ⊆ K`, its cyclotomic structure -/

section MuCyclic

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω}

/-- The unit of `K` determined by the primitive root `ζ ∈ K`. -/
noncomputable def zetaUnit (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : Kˣ :=
  Units.mk0 (⟨ζ, hζK⟩ : K)
    (fun h => hζ.ne_zero (Fact.out : p.Prime).ne_zero (by simpa using congrArg Subtype.val h))

@[simp] theorem zetaUnit_val (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K) = ⟨ζ, hζK⟩ := rfl

theorem zetaUnit_pow (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaUnit (p := p) ζ hζ hζK ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, zetaUnit_val, Units.val_one]
  exact Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)

theorem zetaUnit_ne_one (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaUnit (p := p) ζ hζ hζK ≠ 1 := by
  intro h
  apply hζ.ne_one (Fact.out : p.Prime).one_lt
  have h2 : ((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K) = (1 : K) := by rw [h]; rfl
  rw [zetaUnit_val] at h2
  exact congrArg Subtype.val h2

/-- The element `ζ` of `rootsOfUnity p K`. -/
noncomputable def zrou (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : rootsOfUnity p K :=
  ⟨zetaUnit (p := p) ζ hζ hζK, (mem_rootsOfUnity p _).mpr (zetaUnit_pow ζ hζ hζK)⟩

@[simp] theorem zrou_coe (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ((zrou (p := p) ζ hζ hζK : rootsOfUnity p K) : Kˣ) = zetaUnit (p := p) ζ hζ hζK := rfl

/-- The chosen `𝔽_p`-generator of `μ_p ⊆ K`: the class of the primitive root `ζ`. -/
noncomputable def zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : MuAdd p K :=
  Additive.ofMul (zrou (p := p) ζ hζ hζK)

@[simp] theorem zetaGen_eq (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaGen (p := p) ζ hζ hζK = Additive.ofMul (zrou (p := p) ζ hζ hζK) := rfl

theorem zetaGen_ne_zero (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaGen (p := p) ζ hζ hζK ≠ 0 := by
  intro h
  have h1 : zrou (p := p) ζ hζ hζK = 1 := by
    simpa [zetaGen_eq] using congrArg Additive.toMul h
  exact zetaUnit_ne_one ζ hζ hζK (by simpa [zrou] using Subtype.ext_iff.mp h1)

/-- `g` maps the primitive root `ζ ∈ K` to a power of itself. -/
theorem exists_smul_zeta_eq_pow (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) :
    ∃ m : ℕ, g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m := by
  have hx : (⟨ζ, hζK⟩ : K) ^ p = 1 :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)
  have hpow : ((g (⟨ζ, hζK⟩ : K) : K) : Ω) ^ p = 1 := by
    rw [← IntermediateField.coe_pow, ← map_pow, hx, map_one]
    rfl
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨i, ?_⟩
  rw [AlgEquiv.smul_def]
  apply Subtype.ext
  rw [IntermediateField.coe_pow]
  exact hi.symm

@[simp] theorem toMul_smul_muAdd (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (a : MuAdd p K) :
    Additive.toMul (g • a) = MupKummer.muMapOfField k K p g (Additive.toMul a) := rfl

theorem nsmul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (n : ℕ) :
    Additive.toMul (n • zetaGen (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ n := by
  rw [zetaGen_eq, toMul_nsmul]
  rfl

theorem zmod_smul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (c : ZMod p) :
    Additive.toMul (c • zetaGen (p := p) ζ hζ hζK)
      = (zrou (p := p) ζ hζ hζK) ^ c.val := by
  rw [zmod_smul_eq_nsmul_val, nsmul_zetaGen_toMul]

theorem smul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    Additive.toMul (g • zetaGen (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ m := by
  rw [zetaGen_eq]
  show MupKummer.muMapOfField k K p g (zrou (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ m
  apply Subtype.ext
  rw [MupKummer.muMapOfField_coe, SubmonoidClass.coe_pow, zrou_coe]
  apply Units.ext
  rw [Work.SSGRoute.PT.algEquivUnitsMapOfField_coe, Units.val_pow_eq_pow_val, zetaUnit_val]
  simpa [AlgEquiv.smul_def] using hm

theorem smul_zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    g • zetaGen (p := p) ζ hζ hζK = (m : ZMod p) • zetaGen (p := p) ζ hζ hζK := by
  have hmod : (zrou (p := p) ζ hζ hζK) ^ m
      = (zrou (p := p) ζ hζ hζK) ^ (m : ZMod p).val := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, zrou_coe]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.val_natCast, zetaUnit_val]
    have hp1 : (⟨ζ, hζK⟩ : K) ^ p = 1 :=
      Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)
    conv_lhs => rw [← Nat.mod_add_div m p]
    rw [pow_add, pow_mul, hp1, one_pow, mul_one]
  apply Additive.toMul.injective
  rw [smul_zetaGen_toMul ζ hζ hζK g m hm, zmod_smul_zetaGen_toMul ζ hζ hζK (m : ZMod p)]
  exact hmod

theorem smul_zetaGen_eq_zero_iff (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (c : ZMod p) : c • zetaGen (p := p) ζ hζ hζK = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h1 : (zrou (p := p) ζ hζ hζK) ^ c.val = 1 := by
      rw [← zmod_smul_zetaGen_toMul ζ hζ hζK c]
      rw [h]
      rfl
    have h2 : (zetaUnit (p := p) ζ hζ hζK) ^ c.val = 1 := by
      have h3 := Subtype.ext_iff.mp h1
      rwa [SubmonoidClass.coe_pow, zrou_coe] at h3
    have h4 : (⟨ζ, hζK⟩ : K) ^ c.val = 1 := by
      have h5 : (((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K)) ^ c.val = (1 : K) := by
        rw [← Units.val_pow_eq_pow_val, h2]; rfl
      rwa [zetaUnit_val] at h5
    have h6 : ζ ^ c.val = 1 := by
      have h7 : (((⟨ζ, hζK⟩ : K) ^ c.val : K) : Ω) = ((1 : K) : Ω) := congrArg Subtype.val h4
      rw [IntermediateField.coe_pow] at h7
      simpa using h7
    have h9 : p ∣ c.val := hζ.dvd_of_pow_eq_one c.val h6
    have h10 : c.val < p := ZMod.val_lt c
    have h11 : c.val = 0 := by
      by_contra hne
      have hpos : 0 < c.val := Nat.pos_of_ne_zero hne
      have hle : p ≤ c.val := Nat.le_of_dvd hpos h9
      omega
    rw [← ZMod.natCast_zmod_val c, h11, Nat.cast_zero]
  · intro h; rw [h, zero_smul]

theorem exists_smul_zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (x : MuAdd p K) : ∃ c : ZMod p, x = c • zetaGen (p := p) ζ hζ hζK := by
  have hup : (((Additive.toMul x : rootsOfUnity p K) : Kˣ) : K) ^ p = 1 :=
    (mem_rootsOfUnity' p ((Additive.toMul x : rootsOfUnity p K) : Kˣ)).mp (Additive.toMul x).2
  have hupΩ : (((Additive.toMul x : rootsOfUnity p K) : Kˣ) : Ω) ^ p = 1 := by
    have h1 : (((((Additive.toMul x : rootsOfUnity p K) : Kˣ) : K)) ^ p : Ω)
        = ((1 : K) : Ω) := congrArg Subtype.val hup
    simpa using h1
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hupΩ
  refine ⟨i, ?_⟩
  have hcoee : ((Additive.toMul x : rootsOfUnity p K) : Kˣ) = (zetaUnit (p := p) ζ hζ hζK) ^ i := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, zetaUnit_val]
    exact Subtype.ext (by rw [IntermediateField.coe_pow]; exact hi.symm)
  have hu_eq : (Additive.toMul x : rootsOfUnity p K) = (zrou (p := p) ζ hζ hζK) ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, zrou_coe]
    exact hcoee
  rw [show x = Additive.ofMul (Additive.toMul x) from rfl, hu_eq,
    Nat.cast_smul_eq_nsmul (ZMod p) i (zetaGen (p := p) ζ hζ hζK)]
  exact (ofMul_nsmul i (zrou (p := p) ζ hζ hζK)).symm

end MuCyclic

/-! ## The coefficient isomorphism `DualMod p T ≃ₗ μ_p` -/

section CoeffIso

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : Ω} {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- The linear map `φ ↦ φ (Ach.t0) • ζ` from `DualMod p T` to `μ_p ⊆ K`. -/
noncomputable def dualModToMu (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T →ₗ[ZMod p] MuAdd p K where
  toFun φ := φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK
  map_add' φ ψ := by
    rw [LinearMap.add_apply, add_smul]
  map_smul' c φ := by
    rw [RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, mul_smul]

@[simp] theorem dualModToMu_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModToMu hT hζ hζK φ = φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK := rfl

theorem dualModToMu_surjective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Surjective (dualModToMu (p := p) (K := K) hT hζ hζK) := by
  intro x
  obtain ⟨c, hc⟩ := exists_smul_zetaGen (p := p) ζ hζ hζK x
  refine ⟨c • Ach.coord p T hT.1, ?_⟩
  rw [dualModToMu_apply, LinearMap.smul_apply, Ach.coord_t0, smul_eq_mul, mul_one]
  exact hc.symm

theorem dualModToMu_injective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Injective (dualModToMu (p := p) (K := K) hT hζ hζK) := by
  intro φ ψ h
  rw [dualModToMu_apply, dualModToMu_apply] at h
  have h' : (φ (Ach.t0 p T hT.1) - ψ (Ach.t0 p T hT.1)) • zetaGen (p := p) ζ hζ hζK = 0 := by
    rw [sub_smul, h, sub_self]
  have h2 : φ (Ach.t0 p T hT.1) = ψ (Ach.t0 p T hT.1) :=
    sub_eq_zero.mp ((smul_zetaGen_eq_zero_iff ζ hζ hζK _).mp h')
  ext t
  rw [← Ach.smul_coord_t0 p T hT.1 t, map_smul, map_smul, h2]

/-- **The coefficient isomorphism** `DualMod p T ≃ₗ[ZMod p] μ_p ⊆ K` for a cyclotomic dual
`T`. -/
noncomputable def dualModEquivMu
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T ≃ₗ[ZMod p] MuAdd p K :=
  LinearEquiv.ofBijective (dualModToMu (p := p) (K := K) hT hζ hζK)
    ⟨dualModToMu_injective hT hζ hζK, dualModToMu_surjective hT hζ hζK⟩

@[simp] theorem dualModEquivMu_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModEquivMu hT hζ hζK φ = φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK :=
  rfl

/-- **The coefficient isomorphism is `Gal(K/k)`-equivariant.** -/
theorem dualModEquivMu_smul
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (g : K ≃ₐ[k] K)
    (φ : Work.SSGRoute.DualMod p T) :
    dualModEquivMu hT hζ hζK (g • φ) = g • dualModEquivMu hT hζ hζK φ := by
  obtain ⟨m, hm⟩ := exists_smul_zeta_eq_pow (p := p) ζ hζ hζK g
  have h1 : g • φ = (m : ZMod p) • φ := dualMod_smul_eq hζK hT g m hm φ
  have h2 : g • zetaGen (p := p) ζ hζ hζK = (m : ZMod p) • zetaGen (p := p) ζ hζ hζK :=
    smul_zetaGen ζ hζ hζK g m hm
  calc dualModEquivMu hT hζ hζK (g • φ)
      = (g • φ) (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK :=
        dualModEquivMu_apply hT hζ hζK (g • φ)
    _ = ((m : ZMod p) • φ) (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK := by rw [h1]
    _ = ((m : ZMod p) * φ (Ach.t0 p T hT.1)) • zetaGen (p := p) ζ hζ hζK := by
          rw [LinearMap.smul_apply, smul_eq_mul]
    _ = (φ (Ach.t0 p T hT.1) * (m : ZMod p)) • zetaGen (p := p) ζ hζ hζK := by rw [mul_comm]
    _ = φ (Ach.t0 p T hT.1) • ((m : ZMod p) • zetaGen (p := p) ζ hζ hζK) := by rw [mul_smul]
    _ = φ (Ach.t0 p T hT.1) • (g • zetaGen (p := p) ζ hζ hζK) := by rw [← h2]
    _ = g • (φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK) := by
          rw [← smul_comm g (φ (Ach.t0 p T hT.1)) (zetaGen (p := p) ζ hζ hζK)]
    _ = g • dualModEquivMu hT hζ hζK φ := by rw [dualModEquivMu_apply]

end CoeffIso

/-! ## The natural action of a subgroup of `G_k` on `Ωˣ` -/

section SubgroupAction

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- The natural action of a subgroup `H ≤ G_k` on `Additive Ωˣ` (restriction of the action of
`G_k`). -/
noncomputable instance instDistribMulActionSubgroupAddUnits (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    DistribMulAction ↥H (Additive (Units Ω)) where
  smul h a := (h : Ω ≃ₐ[k] Ω) • a
  one_smul a := by
    show ((1 : ↥H) : Ω ≃ₐ[k] Ω) • a = a
    rw [show ((1 : ↥H) : Ω ≃ₐ[k] Ω) = 1 from rfl, one_smul]
  mul_smul h₁ h₂ a := by
    show ((h₁ * h₂ : ↥H) : Ω ≃ₐ[k] Ω) • a = (h₁ : Ω ≃ₐ[k] Ω) • ((h₂ : Ω ≃ₐ[k] Ω) • a)
    rw [show ((h₁ * h₂ : ↥H) : Ω ≃ₐ[k] Ω)
        = (h₁ : Ω ≃ₐ[k] Ω) * (h₂ : Ω ≃ₐ[k] Ω) from rfl, mul_smul]
  smul_zero h := smul_zero _
  smul_add h a b := smul_add _ _ _

@[simp] theorem subgroupAddUnits_smul (H : Subgroup (Ω ≃ₐ[k] Ω)) (h : ↥H)
    (a : Additive (Units Ω)) :
    h • a = (h : Ω ≃ₐ[k] Ω) • a := rfl

end SubgroupAction

end

end MupCard
end Work.SSGRoute.PTembedding
