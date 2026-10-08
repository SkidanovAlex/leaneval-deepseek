import Mathlib
import Submission.Work.ThmF.Prove.S3.RingAutEqFrobeniusPow
import Submission.Work.ThmF.Prove.S3.ConjRangeLeRange
import Submission.Work.ThmF.Prove.S3.ExistsRingEquivOfNormalizes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThmF.Prove.S3

open scoped IsMulCommutative

/-- The annihilator of a simple module is a maximal ideal, hence the kernel of the representation
map `F[G] → End F V` is maximal. -/
theorem ker_asAlgebraHom_isMaximal {F G V : Type*} [Field F] [CommMonoid G] [AddCommGroup V]
    [Module F V] (ρ : Representation F G V)
    (h : IsSimpleModule (MonoidAlgebra F G) (Representation.asModule ρ)) :
    (RingHom.ker (Representation.asAlgebraHom ρ : MonoidAlgebra F G →+* Module.End F V)).IsMaximal := by
  have hann : Module.annihilator (MonoidAlgebra F G) (Representation.asModule ρ)
      = RingHom.ker (Representation.asAlgebraHom ρ : MonoidAlgebra F G →+* Module.End F V) := by
    ext r
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro h1
      exact LinearMap.ext (fun v => h1 v)
    · intro h1 v
      exact congrFun (congrArg (fun f : Module.End F V => (f : V → V)) h1) v
  rw [← hann]
  exact h.annihilator_isMaximal

/-- **Schur + Frobenius.**  Let `K ⊴ L` with `K` abelian, and let `V` be a simple
`𝔽_ℓ[K]`-module on which `K` acts faithfully.  Then for every `g ∈ L` there is `i` with
`g k g⁻¹ = k ^ (ℓ ^ i)` for all `k ∈ K`.

The proof passes to the field `E = 𝔽_ℓ[K]/𝔪` (`𝔪` the kernel of the action), which is a finite
field of characteristic `ℓ` embedding into `End V`; conjugation by `ρ g` is a ring automorphism of
`E`, hence a power of the Frobenius `ringAut_eq_frobenius_pow`, and faithfulness of `ρ` on `K`
turns the resulting identity of operators into one in `K`. -/
theorem conj_eq_pow_prime_of_simple
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type} [Group L] {K : Subgroup L} (hKn : K.Normal)
    [IsMulCommutative ↥K]
    {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V] [FiniteDimensional (ZMod ℓ) V] [Nontrivial V]
    (ρ : Representation (ZMod ℓ) L V)
    (hsimp : IsSimpleModule (MonoidAlgebra (ZMod ℓ) ↥K) (Representation.asModule (ρ.comp K.subtype)))
    (hfaith : ∀ k : ↥K, ρ (k : L) = 1 → k = 1)
    (g : L) (k : ↥K) :
    ∃ i : ℕ, (⟨g * (k : L) * g⁻¹, hKn.conj_mem (k : L) k.2 g⟩ : ↥K) = k ^ ℓ ^ i := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  let R := MonoidAlgebra (ZMod ℓ) ↥K
  let φ : R →ₐ[ZMod ℓ] Module.End (ZMod ℓ) V := Representation.asAlgebraHom (ρ.comp K.subtype)
  let I : Ideal R := RingHom.ker (φ : R →+* Module.End (ZMod ℓ) V)
  have hImax : I.IsMaximal := ker_asAlgebraHom_isMaximal (ρ.comp K.subtype) hsimp
  haveI : I.IsMaximal := hImax
  letI hFieldE : Field (R ⧸ I) := Ideal.Quotient.field I
  have hI : ∀ a ∈ I, φ a = 0 := fun a ha => by
    have ha' : a ∈ RingHom.ker (φ : R →+* Module.End (ZMod ℓ) V) := ha
    exact (RingHom.mem_ker (f := (φ : R →+* Module.End (ZMod ℓ) V))).mp ha'
  let φbar : (R ⧸ I) →ₐ[ZMod ℓ] Module.End (ZMod ℓ) V := Ideal.Quotient.liftₐ I φ hI
  have hφbar_mk : ∀ r : R, φbar (Ideal.Quotient.mk I r) = φ r := by
    intro r
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact (show (φ : R →+* Module.End (ZMod ℓ) V) r = φ r from rfl)
  have hφbar_inj : Function.Injective φbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : φ a = φ b := by
      have h1 := hxy
      rwa [hφbar_mk, hφbar_mk] at h1
    have hab' : (φ : R →+* Module.End (ZMod ℓ) V) a = (φ : R →+* Module.End (ZMod ℓ) V) b := hab
    rw [Ideal.Quotient.eq]
    exact (RingHom.mem_ker (f := (φ : R →+* Module.End (ZMod ℓ) V))).mpr
      (by rw [map_sub, hab', sub_self])
  -- finiteness and characteristic of `E`
  have hFinV : Finite V := Module.finite_of_finite (ZMod ℓ)
  have hFinEnd : Finite (Module.End (ZMod ℓ) V) :=
    Finite.of_injective (fun f : Module.End (ZMod ℓ) V => (f : V → V))
      (fun f g h => LinearMap.ext (fun v => congrFun h v))
  have hFinE : Finite (R ⧸ I) := Finite.of_injective φbar hφbar_inj
  haveI : Fintype (R ⧸ I) := Fintype.ofFinite _
  haveI hcharEnd : CharP (Module.End (ZMod ℓ) V) ℓ :=
    Module.charP_end (R := ZMod ℓ) (M := V) (p := ℓ) (by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, (Ideal.torsionOf_eq_bot_iff_of_isTorsionFree (R := ZMod ℓ) (M := V) v).mpr hv⟩)
  -- `E` has the characteristic of `R` (the algebra map is injective); we state the `CharP`
  -- instance on the *field* structure of `E` (`CharP.mk`, so that it is the instance that
  -- `ringAut_eq_frobenius_pow` sees) rather than transporting it along the quotient ring.
  haveI hcharE : CharP (R ⧸ I) ℓ := CharP.mk (fun x => by
    rw [← map_natCast (Ideal.Quotient.mk I) x]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show (x : R) ∈ RingHom.ker (φ : R →+* Module.End (ZMod ℓ) V) ↔ ℓ ∣ x
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero_iff (Module.End (ZMod ℓ) V) ℓ x)
  -- the elements `e k` of `R ⧸ I`
  let e : ↥K →* (R ⧸ I) := (Ideal.Quotient.mk I).toMonoidHom.comp (MonoidAlgebra.of (ZMod ℓ) ↥K)
  have he_apply : ∀ k : ↥K, e k = Ideal.Quotient.mk I (MonoidAlgebra.of (ZMod ℓ) ↥K k) := fun k => rfl
  have hφbar_e : ∀ k : ↥K, φbar (e k) = ρ (k : L) := by
    intro k
    rw [he_apply k, hφbar_mk]
    exact Representation.asAlgebraHom_of (ρ.comp K.subtype) k
  -- conjugation lands in the image
  have hconj : ∀ r : R, (ρ g) * φ r * (ρ g⁻¹) ∈ φ.range := fun r => conj_range_le_range hKn ρ g r
  have huu' : (ρ g) * (ρ g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hu'u : (ρ g⁻¹) * (ρ g) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hnorm : ∀ x : R ⧸ I, ∃ y : R ⧸ I, φbar y = (ρ g) * φbar x * (ρ g⁻¹) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := (AlgHom.mem_range φ).mp (hconj a)
    exact ⟨Ideal.Quotient.mk I b, by rw [hφbar_mk, hφbar_mk, hb]⟩
  have hmain : ∃ σ : (R ⧸ I) ≃+* (R ⧸ I),
      ∀ x : R ⧸ I, φbar (σ x) = (ρ g) * φbar x * (ρ g⁻¹) :=
    exists_ringEquiv_of_normalizes (E := R ⧸ I) (F := ZMod ℓ) (V := V)
      (φ := φbar) (hφ := hφbar_inj) (u := ρ g) (u' := ρ g⁻¹)
      (hu := huu') (hu' := hu'u) (hnorm := hnorm)
  obtain ⟨σ, hσ⟩ := hmain
  obtain ⟨i, hi⟩ := ringAut_eq_frobenius_pow (F := R ⧸ I) hℓ hcharE σ
  refine ⟨i, ?_⟩
  set k' : ↥K := ⟨g * (k : L) * g⁻¹, hKn.conj_mem (k : L) k.2 g⟩ with hk'
  have hEnd : (ρ (↑k' : L)) = (ρ (((k ^ (ℓ ^ i) : ↥K) : L))) := by
    have he_frob : σ (e k) = (e k) ^ (ℓ ^ i) := hi (e k)
    have h1 : (ρ (↑k' : L)) = (ρ g) * (ρ (k : L)) * (ρ g⁻¹) := by
      have hcoe : (↑k' : L) = g * (k : L) * g⁻¹ := rfl
      rw [hcoe, map_mul, map_mul]
    calc (ρ (↑k' : L)) = (ρ g) * (ρ (k : L)) * (ρ g⁻¹) := h1
      _ = (ρ g) * φbar (e k) * (ρ g⁻¹) := by rw [hφbar_e k]
      _ = φbar (σ (e k)) := (hσ (e k)).symm
      _ = φbar ((e k) ^ (ℓ ^ i)) := by rw [he_frob]
      _ = (φbar (e k)) ^ (ℓ ^ i) := map_pow φbar (e k) (ℓ ^ i)
      _ = (ρ (k : L)) ^ (ℓ ^ i) := by rw [hφbar_e k]
      _ = ρ (((k ^ (ℓ ^ i) : ↥K) : L)) := by rw [Subgroup.coe_pow, map_pow]
  have hkk' : k' = k ^ ℓ ^ i := by
    have h3 : k' * (k ^ ℓ ^ i)⁻¹ = 1 := by
      apply hfaith
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, hEnd]
      rw [← map_mul, mul_inv_cancel, map_one]
    exact div_eq_one.mp (by simpa [div_eq_mul_inv] using h3)
  exact hkk'

end Work.ThmF.Prove.S3
