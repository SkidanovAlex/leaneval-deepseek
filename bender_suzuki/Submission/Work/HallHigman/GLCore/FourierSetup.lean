/-
Auxiliary definitions and basic lemmas for L8 of the GL-core design
(`Work.HallHigman.GLCore.fourier_finrank`, the "Fourier lemma" of
`NOTES_LEAD_ft_hallhigman.md` §2.2, Step 4c).

Setting: `K` a field, `V` a nontrivial `K`-vector space, `E` a finite group acting on `V`
through `σ : E →* Module.End K V`.  All commutators of `E` lie in the centre `Z(E)`, the centre
acts by scalars through an injective character `λ` (`centerUnit`), and `|E|` is invertible in `K`.

On the way to `dim End_K V = |E/Z(E)| · dim End_E(V)` we build here

* `centerUnit σ hsc` : the character `Z(E) →* Kˣ` giving the scalar action of the centre;
* `commChar σ hsc hcomm f` : the character `e ↦ λ([e,f])` of `E`;
* `fourierP σ` : the projector `Y ↦ |E|⁻¹ Σ_{e∈E} σ e · Y · σ e⁻¹` onto the commutant `End_E(V)`;
* `fourierTheta σ` : the map `((E ⧸ Z(E)) → End_E(V)) → End_K V`, `β ↦ Σ_q σ(out q) β_q`.
-/
import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

open Finset

universe u v w

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V]
variable {E : Type*} [Group E] [Fintype E]

omit [Fintype E] in
/-- For a central element `x`, conjugation by any `a` is the identity. -/
theorem conj_eq_of_mem_center {x : E} (hx : x ∈ Subgroup.center E) (a : E) :
    a * x * a⁻¹ = x := by
  rw [Subgroup.mem_center_iff.mp hx a, mul_assoc, mul_inv_cancel, mul_one]

omit [Fintype E] in
/-- The commutator identity `[a·b, f] = [b,f]·[a,f]` when the commutators with `f` are central. -/
theorem commutator_mul_commutator (a b f : E)
    (h : b * f * b⁻¹ * f⁻¹ ∈ Subgroup.center E) :
    (a * b) * f * (a * b)⁻¹ * f⁻¹ = (b * f * b⁻¹ * f⁻¹) * (a * f * a⁻¹ * f⁻¹) := by
  have hx : a * (b * f * b⁻¹ * f⁻¹) * a⁻¹ = b * f * b⁻¹ * f⁻¹ :=
    conj_eq_of_mem_center h a
  rw [← hx]
  group

/-- The homomorphism `E →* Z(E)`, `e ↦ [e,f]` (all commutators being central). -/
noncomputable def commHom
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) (f : E) :
    E →* Subgroup.center E where
  toFun e := ⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    show (a * b) * f * (a * b)⁻¹ * f⁻¹ = (a * f * a⁻¹ * f⁻¹) * (b * f * b⁻¹ * f⁻¹)
    rw [commutator_mul_commutator a b f (hcomm b f)]
    exact Subgroup.mem_center_iff.mp (hcomm a f) (b * f * b⁻¹ * f⁻¹)

/-- The scalar by which a central element of `E` acts on `V`, as a unit of `K`. -/
noncomputable def centerUnit (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c) :
    Subgroup.center E →* Kˣ where
  toFun z := Units.mk0 (Classical.choose (hsc z.1 z.2)) (by
    have hne : (σ z.1 : Module.End K V) ≠ 0 := by
      intro h
      have h1 : (1 : Module.End K V) = 0 := by
        calc (1 : Module.End K V) = σ (↑z * (↑z)⁻¹) := by rw [mul_inv_cancel, map_one]
          _ = σ ↑z * σ ((↑z)⁻¹) := by rw [map_mul]
          _ = 0 := by rw [h, zero_mul]
      exact one_ne_zero h1
    intro hc0
    apply hne
    rw [Classical.choose_spec (hsc z.1 z.2), hc0, map_zero])
  map_one' := by
    apply Units.ext
    simp only [Units.val_one, Units.val_mk0]
    apply FaithfulSMul.algebraMap_injective K (Module.End K V)
    rw [map_one,
      ← Classical.choose_spec (hsc (1 : Subgroup.center E).1 (1 : Subgroup.center E).2)]
    exact map_one σ
  map_mul' := by
    intro z w
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    apply FaithfulSMul.algebraMap_injective K (Module.End K V)
    rw [map_mul, ← Classical.choose_spec (hsc z.1 z.2), ← Classical.choose_spec (hsc w.1 w.2),
      ← map_mul, ← Classical.choose_spec (hsc (z * w).1 (z * w).2), Subgroup.coe_mul]

omit [Fintype E] in
/-- The defining property of `centerUnit`. -/
theorem centerUnit_spec (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (z : Subgroup.center E) :
    (σ ↑z : Module.End K V) = algebraMap K (Module.End K V) ((centerUnit σ hsc z : Kˣ) : K) := by
  change (σ ↑z : Module.End K V)
      = algebraMap K (Module.End K V) (Classical.choose (hsc z.1 z.2))
  exact Classical.choose_spec (hsc z.1 z.2)

/-- The character `e ↦ λ([e,f])` of `E`, for `f : E`. -/
noncomputable def commChar (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) (f : E) : E →* K :=
  (Units.coeHom K).comp ((centerUnit σ hsc).comp (commHom hcomm f))

omit [Fintype E] in
/-- The value of `commChar` is the scalar attached to the commutator `[e,f]`. -/
theorem commChar_apply (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) (f e : E) :
    commChar σ hsc hcomm f e
      = ((centerUnit σ hsc ⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩ : Kˣ) : K) := rfl

omit [Fintype E] in
/-- `centerUnit` attains the value `1` only at the identity. -/
theorem centerUnit_eq_one_iff (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1) (z : Subgroup.center E) :
    centerUnit σ hsc z = 1 ↔ (z : E) = 1 := by
  constructor
  · intro h
    apply hfaith z.1 z.2
    have h2 : ((centerUnit σ hsc z : Kˣ) : K) = 1 := by rw [h]; rfl
    rw [centerUnit_spec σ hsc z, h2, map_one]
  · intro h
    apply Units.ext
    simp only [Units.val_one]
    apply FaithfulSMul.algebraMap_injective K (Module.End K V)
    rw [map_one, ← centerUnit_spec σ hsc z, h]
    exact map_one σ

omit [Fintype E] in
/-- `centerUnit` is injective, by faithfulness of the action of the centre. -/
theorem centerUnit_injective (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1) :
    Function.Injective (centerUnit σ hsc) := by
  intro z w hzw
  have h1 : centerUnit σ hsc (z * w⁻¹) = 1 := by
    rw [map_mul, hzw, map_inv, mul_inv_cancel]
  have h2 : ((z * w⁻¹ : Subgroup.center E) : E) = 1 :=
    (centerUnit_eq_one_iff σ hsc hfaith _).mp h1
  refine Subtype.ext ?_
  have h3 : (z : E) * (w : E)⁻¹ = 1 := by simpa using h2
  rwa [mul_inv_eq_one] at h3

omit [Fintype E] in
/-- For `f ∉ Z(E)` the character `e ↦ λ([e,f])` is nontrivial. -/
theorem commChar_ne_one (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) {f : E}
    (hf : f ∉ Subgroup.center E) : commChar σ hsc hcomm f ≠ 1 := by
  intro h
  apply hf
  rw [Subgroup.mem_center_iff]
  intro e
  have he : commChar σ hsc hcomm f e = 1 := by rw [h]; rfl
  rw [commChar_apply] at he
  have hcu : centerUnit σ hsc ⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩ = 1 := by
    apply Units.ext
    simpa using he
  have h1 : e * f * e⁻¹ * f⁻¹ = 1 :=
    (centerUnit_eq_one_iff σ hsc hfaith _).mp hcu
  have h4 : e * f * e⁻¹ = f := by
    calc e * f * e⁻¹ = (e * f * e⁻¹ * f⁻¹) * f := by group
      _ = 1 * f := by rw [h1]
      _ = f := by rw [one_mul]
  calc e * f = (e * f * e⁻¹) * e := by group
    _ = f * e := by rw [h4]

/-- The sum of the character `e ↦ λ([e,f])` vanishes for `f ∉ Z(E)`: this is the
"sum of a nontrivial homomorphism into `Kˣ`" (`sum_hom_units_eq_zero`). -/
theorem sum_commChar_eq_zero (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) {f : E}
    (hf : f ∉ Subgroup.center E) : ∑ e : E, commChar σ hsc hcomm f e = 0 :=
  sum_hom_units_eq_zero (commChar σ hsc hcomm f) (commChar_ne_one σ hsc hfaith hcomm hf)

/-- The conjugation sum `Σ_e σ(e f e⁻¹)` equals `(Σ_e λ([e,f])) • σ f`. -/
theorem conj_sum_eq (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) (f : E) :
    ∑ e : E, σ (e * f * e⁻¹) = (∑ e : E, commChar σ hsc hcomm f e) • σ f := by
  have hpt : ∀ e : E, σ (e * f * e⁻¹) = commChar σ hsc hcomm f e • σ f := by
    intro e
    have h : e * f * e⁻¹ = (e * f * e⁻¹ * f⁻¹) * f := by group
    have hcu : (σ (e * f * e⁻¹ * f⁻¹) : Module.End K V)
        = algebraMap K (Module.End K V)
          ((centerUnit σ hsc ⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩ : Kˣ) : K) :=
      centerUnit_spec σ hsc ⟨e * f * e⁻¹ * f⁻¹, hcomm e f⟩
    rw [h, map_mul, commChar_apply, hcu, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl (fun e _ => hpt e)

/-- The Fourier projector `Y ↦ |E|⁻¹ Σ_{e∈E} σ e · Y · σ e⁻¹`. -/
noncomputable def fourierP (σ : E →* Module.End K V) :
    Module.End K V →ₗ[K] Module.End K V :=
  (Nat.card E : K)⁻¹ • ∑ e : E, (LinearMap.mulLeft K (σ e)).comp (LinearMap.mulRight K (σ e⁻¹))

omit [Nontrivial V] in
/-- Evaluation formula for `fourierP`. -/
theorem fourierP_apply (σ : E →* Module.End K V) (Y : Module.End K V) :
    fourierP σ Y = (Nat.card E : K)⁻¹ • ∑ e : E, σ e * Y * σ e⁻¹ := by
  simp only [fourierP, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

omit [Nontrivial V] in
/-- `fourierP` lands in the commutant `End_E(V)`. -/
theorem fourierP_mem_commutantOf (σ : E →* Module.End K V) (Y : Module.End K V) :
    fourierP σ Y ∈ commutantOf σ := by
  rw [mem_commutantOf_iff]
  intro e
  have hσ' : (σ e⁻¹) * σ e = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hpt : ∀ f : E, σ e * (σ f * Y * σ f⁻¹) * σ e⁻¹ = σ (e * f) * Y * σ (e * f)⁻¹ := by
    intro f
    rw [map_mul, mul_inv_rev, map_mul]
    simp only [mul_assoc]
  have hinner : (σ e * (∑ f : E, σ f * Y * σ f⁻¹)) * σ e⁻¹
      = ∑ f : E, σ f * Y * σ f⁻¹ := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun f _ => hpt f)]
    exact Equiv.sum_comp (Equiv.mulLeft e) (fun f => σ f * Y * σ f⁻¹)
  have hconj : σ e * fourierP σ Y * σ e⁻¹ = fourierP σ Y := by
    rw [fourierP_apply, mul_smul_comm, smul_mul_assoc, hinner]
  calc σ e * fourierP σ Y = (σ e * fourierP σ Y * σ e⁻¹) * σ e := by
        rw [mul_assoc, hσ', mul_one]
    _ = fourierP σ Y * σ e := by rw [hconj]

omit [Nontrivial V] in
/-- `fourierP` is the identity on the commutant `End_E(V)`. -/
theorem fourierP_eq_self (σ : E →* Module.End K V) (hE : (Nat.card E : K) ≠ 0)
    {β : Module.End K V} (hβ : β ∈ commutantOf σ) : fourierP σ β = β := by
  have hpt : ∀ f : E, σ f * β * σ f⁻¹ = β := by
    intro f
    have hf : (σ f) * σ f⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc σ f * β * σ f⁻¹ = (σ f * β) * σ f⁻¹ := rfl
      _ = (β * σ f) * σ f⁻¹ := by rw [mem_commutantOf_iff.mp hβ f]
      _ = β * (σ f * σ f⁻¹) := by rw [mul_assoc]
      _ = β * 1 := by rw [hf]
      _ = β := mul_one β
  have hsum : (∑ f : E, σ f * β * σ f⁻¹) = ∑ _f : E, β :=
    Finset.sum_congr rfl (fun f _ => hpt f)
  have hE' : (Fintype.card E : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact hE
  rw [fourierP_apply, hsum, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K]
  rw [show (Nat.card E : K) = (Fintype.card E : K) from by rw [Nat.card_eq_fintype_card],
    smul_smul, inv_mul_cancel₀ hE', one_smul]

omit [Nontrivial V] in
/-- A central element acts on the source and target of `fourierP` in a compatible way. -/
theorem fourierP_smul_center (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    {z : E} (hz : z ∈ Subgroup.center E) (X : Module.End K V) :
    fourierP σ (σ z * X) = σ z * fourierP σ X := by
  obtain ⟨c, hc⟩ := hsc z hz
  have h1 : (σ z : Module.End K V) = c • (1 : Module.End K V) := by
    rw [hc, Algebra.algebraMap_eq_smul_one]
  rw [h1, smul_mul_assoc, one_mul, map_smul, smul_mul_assoc, one_mul]

/-- The map `Θ : ((E ⧸ Z(E)) → End_E(V)) → End_K V`, `β ↦ Σ_q σ(out q) β_q`, where `out` is a
section of `E → E ⧸ Z(E)`.  It is `K`-linear by construction. -/
noncomputable def fourierTheta [Fintype (E ⧸ Subgroup.center E)] (σ : E →* Module.End K V) :
    ((E ⧸ Subgroup.center E) → commutantOf σ) →ₗ[K] Module.End K V :=
  ∑ q : E ⧸ Subgroup.center E,
    (LinearMap.mulLeft K (σ (Quotient.out q))).comp
      ((commutantOf σ).subtype.comp (LinearMap.proj q))

omit [Nontrivial V] [Fintype E] in
/-- Evaluation formula for `fourierTheta`. -/
theorem fourierTheta_apply [Fintype (E ⧸ Subgroup.center E)] (σ : E →* Module.End K V)
    (β : (E ⧸ Subgroup.center E) → commutantOf σ) :
    fourierTheta σ β = ∑ q : E ⧸ Subgroup.center E,
      σ (Quotient.out q) * ((β q : commutantOf σ) : Module.End K V) := by
  simp only [fourierTheta, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Submodule.subtype_apply, LinearMap.proj_apply]

end Work.HallHigman.GLCore
