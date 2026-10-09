import Mathlib
import Submission.NK.NUV2.RouteB.CongCount.CongConeCoset
import Submission.NK.NUV2.RouteB.CongCount.CongRayAux
import Submission.NK.NUV2.RouteB.RayCount.Defs
import Submission.NK.NUV2.RouteB.RayCount.mem_unitCongSubgroup_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cone count of a ray class: the multiplicity of the torsion units

For a modulus `𝔪` with `𝔪.pos = ∅`, a nonzero integral ideal `𝔡` coprime to the support of `𝔪` and
`X : ℝ`, the number of ideals of `𝓞 K` in the ray class of `𝔡` modulo `U(𝔪)`, of norm `≤ X`, counted
with multiplicity `torsionOrder K`, equals the number of points of the fundamental cone lying in
`𝔡⁻¹` which satisfy `IsCongElem K 𝔪 (u * -)` for some unit `u` and have `norm * |N𝔡| ≤ X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.CongCount

open NK.NUV2.RouteB
open NK.GlobalCFT.IdeleClassGroup (count_spanSingleton_eq)

variable {K : Type} [Field K] [NumberField K]

/-! ## Passing from an integral fractional ideal to an ideal -/

/-- The ideal attached to an integral fractional ideal: `I.comap (algebraMap (𝓞 K) K)`. -/
noncomputable def idealOfIntegral (I : FractionalIdeal (𝓞 K)⁰ K) : Ideal (𝓞 K) :=
  (I : Submodule (𝓞 K) K).comap (Algebra.linearMap (𝓞 K) K)

theorem mem_idealOfIntegral {I : FractionalIdeal (𝓞 K)⁰ K} {z : 𝓞 K} :
    z ∈ idealOfIntegral I ↔ ((z : 𝓞 K) : K) ∈ I := by
  rw [idealOfIntegral, Submodule.mem_comap]
  simp only [Algebra.linearMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact Iff.rfl

theorem coe_idealOfIntegral {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≤ 1) :
    ((idealOfIntegral I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    rw [← hzx]
    exact (mem_idealOfIntegral).mp hz
  · intro x hx
    have hx1 : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := hI hx
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hx1
    refine (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨z, ?_, hz⟩
    rw [mem_idealOfIntegral]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    rw [hz]
    exact hx

/-- The `q`-adic valuation of a unit of `𝓞 K` is one. -/
theorem valuation_unit (q : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    (q.valuation K) ((u : 𝓞 K) : K) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hmem u.isUnit)

/-- An element which is `≡ 1` modulo `𝔪` at a support prime is a local unit there. -/
theorem valuation_eq_one_of_cong (𝔪 : Modulus K) {q : HeightOneSpectrum (𝓞 K)} {x : K}
    (hx : (q.valuation K) (x - 1) ≤ WithZero.exp (-(𝔪.exps q : ℤ)))
    (hq : 𝔪.exps q ≠ 0) : (q.valuation K) x = 1 := by
  have hm : (1 : ℤ) ≤ (𝔪.exps q : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hlt : (q.valuation K) (x - 1) < (q.valuation K) (1 : K) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hx ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  rw [show x = (x - 1) + 1 by ring]
  rw [Valuation.map_add_eq_of_lt_right (q.valuation K) hlt, Valuation.map_one]

/-! ## The ideal attached to a point of the cone -/

/-- The ideal `𝔡 · (β)` attached to a point `β` of `𝔡⁻¹`. -/
noncomputable def idealOfCone (𝔡 : (Ideal (𝓞 K))⁰) (β : K) : Ideal (𝓞 K) :=
  idealOfIntegral (FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
    ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))

/-- The fractional ideal of `idealOfCone 𝔡 β` is `(β) · 𝔡`. -/
theorem coe_idealOfCone {𝔡 : (Ideal (𝓞 K))⁰} {β : K}
    (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    ((idealOfCone 𝔡 β : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  refine coe_idealOfIntegral ?_
  calc FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hβ) _
    _ = 1 := inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡))

theorem idealOfCone_ne_zero {𝔡 : (Ideal (𝓞 K))⁰} {β : K}
    (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (hβ0 : β ≠ 0) :
    idealOfCone 𝔡 β ≠ 0 := by
  intro h
  have hcoe := coe_idealOfCone hβ
  rw [h] at hcoe
  simp only [Ideal.zero_eq_bot, FractionalIdeal.coeIdeal_bot] at hcoe
  have hne : FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ0)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡))
  exact hne hcoe.symm

/-- The norm of the ideal of a cone point. -/
theorem absNorm_idealOfCone {𝔡 : (Ideal (𝓞 K))⁰} {β : K}
    (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    (Ideal.absNorm (idealOfCone 𝔡 β) : ℝ) =
      NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K β) *
        (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by
  have hcoe := coe_idealOfCone hβ
  have h2 : (FractionalIdeal.absNorm (((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) : ℝ)
      = (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
    norm_num
  have h3 : (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) : ℝ)
      = NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K β) := by
    rw [FractionalIdeal.absNorm_span_singleton, NumberField.mixedEmbedding.norm_eq_norm,
      Rat.cast_abs]
  calc (Ideal.absNorm (idealOfCone 𝔡 β) : ℝ)
      = (FractionalIdeal.absNorm ((idealOfCone 𝔡 β : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
        rw [FractionalIdeal.coeIdeal_absNorm]; norm_num
    _ = (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
          ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) : ℝ) := by rw [hcoe]
    _ = (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) : ℝ) *
        (FractionalIdeal.absNorm (((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) : ℝ) := by
        rw [map_mul]
        norm_num
    _ = NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K β) *
        (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by rw [h3, h2]

/-! ## The ideal of a point congruent to `1` modulo `𝔪` is coprime to the support -/

theorem not_dvd_idealOfCone (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {β : K} {u : (𝓞 K)ˣ} (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (hcong : NK.NUV2.RouteB.IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β))
    {q : HeightOneSpectrum (𝓞 K)} (hq : 𝔪.exps q ≠ 0) :
    ¬ q.asIdeal ∣ idealOfCone 𝔡 β := by
  intro hdiv
  have hβ0 : β ≠ 0 := by
    intro h0
    have hx := hcong.1 q hq
    have h1 : Valued.v (algebraMap K (q.adicCompletion K) (((u : 𝓞 K) : K) * β - 1)) = 1 := by
      rw [h0, mul_zero, zero_sub, map_neg, map_one, Valuation.map_neg, Valuation.map_one]
    rw [h1] at hx
    have h2 : WithZero.exp (-(𝔪.exps q : ℤ)) < 1 := by
      rw [← WithZero.exp_zero]
      refine WithZero.exp_lt_exp.mpr ?_
      have : (1 : ℤ) ≤ (𝔪.exps q : ℤ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
      omega
    exact absurd hx (not_le.mpr h2)
  have hvalβ : (q.valuation K) β = 1 := by
    have hx : (q.valuation K) (((u : 𝓞 K) : K) * β - 1) ≤
        WithZero.exp (-(𝔪.exps q : ℤ)) := by
      have h := hcong.1 q hq
      rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h
    have h1 := valuation_eq_one_of_cong 𝔪 hx hq
    rw [Valuation.map_mul, valuation_unit q u, one_mul] at h1
    exact h1
  have hcount0 : FractionalIdeal.count K q
      ((idealOfCone 𝔡 β : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    rw [coe_idealOfCone hβ,
      FractionalIdeal.count_mul K q (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ0)
        (FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡)),
      count_spanSingleton_eq q hβ0, hvalβ, WithZero.log_one, neg_zero, zero_add,
      count_coe_eq_zero_of_not_dvd (baseIdeal_ne_zero 𝔡) (hcop q hq)]
  have hle : ((idealOfCone 𝔡 β : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((q.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr (Ideal.dvd_iff_le.mp hdiv)
  have hmono : FractionalIdeal.count K q ((q.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ FractionalIdeal.count K q
          ((idealOfCone 𝔡 β : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.count_mono K q
      (FractionalIdeal.coeIdeal_ne_zero.mpr (idealOfCone_ne_zero hβ hβ0)) hle
  rw [FractionalIdeal.count_self, hcount0] at hmono
  exact absurd hmono (by norm_num)

/-! ## The two carriers -/

/-- The set of points of the fundamental cone counted by `rayConeCount`. -/
def coneCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (X : ℝ) : Set K :=
  {β : K | β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧ β ≠ 0 ∧
    NumberField.mixedEmbedding K β ∈ NumberField.mixedEmbedding.fundamentalCone K ∧
    (∃ u : (𝓞 K)ˣ, NK.NUV2.RouteB.IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β)) ∧
    NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K β) *
      (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) ≤ X}

/-- The set of ideals counted by `rayClassCnt`. -/
def idealCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (X : ℝ) : Set (Ideal (𝓞 K)) :=
  {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ 0 ∧
    (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ 𝔞) ∧
    NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) 𝔞 =
      NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) (𝔡 : Ideal (𝓞 K)) ∧
    (Ideal.absNorm 𝔞 : ℝ) ≤ X}

theorem mem_coneCarrier {𝔪 : Modulus K} {𝔡 : (Ideal (𝓞 K))⁰} {X : ℝ} {β : K} :
    β ∈ coneCarrier 𝔪 𝔡 X ↔
      β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧ β ≠ 0 ∧
      NumberField.mixedEmbedding K β ∈ NumberField.mixedEmbedding.fundamentalCone K ∧
      (∃ u : (𝓞 K)ˣ, NK.NUV2.RouteB.IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β)) ∧
      NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K β) *
        (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) ≤ X := Iff.rfl

/-- The class of the ideal of a point satisfying `IsCongElem` up to units. -/
theorem classOfIdeal_idealOfCone (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {β : K} {u : (𝓞 K)ˣ} (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (hβ0 : β ≠ 0) (hcong : NK.NUV2.RouteB.IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β)) :
    NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) (idealOfCone 𝔡 β) =
      NK.HeckeL.classOfIdeal K (CongSubgroup K 𝔪) (𝔡 : Ideal (𝓞 K)) := by
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (((u : 𝓞 K) : K) * β)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    have hunit : FractionalIdeal.spanSingleton (𝓞 K)⁰ (((u : 𝓞 K) : K)) = 1 := by
      rw [RingOfIntegers.coe_eq_algebraMap, ← FractionalIdeal.coeIdeal_span_singleton,
        show Ideal.span {(u : 𝓞 K)} = ⊤ from Ideal.span_singleton_eq_top.mpr u.isUnit,
        FractionalIdeal.coeIdeal_top]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hunit, one_mul]
  refine (NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff K 𝔪 (idealOfCone 𝔡 β)
    (𝔡 : Ideal (𝓞 K)) (idealOfCone_ne_zero hβ hβ0) (baseIdeal_ne_zero 𝔡)
    (fun q hq => not_dvd_idealOfCone 𝔪 𝔡 hcop hβ hcong hq) hcop).mpr
    ⟨((u : 𝓞 K) : K) * β, mul_ne_zero (by simp) hβ0, hcong, ?_⟩
  rw [coe_idealOfCone hβ, hspan, mul_comm]

/-- The ideal of a point of the cone carrier lies in the ideal carrier. -/
theorem idealOfCone_mem_idealCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {X : ℝ} {β : K} (hβ : β ∈ coneCarrier 𝔪 𝔡 X) :
    idealOfCone 𝔡 β ∈ idealCarrier 𝔪 𝔡 X := by
  obtain ⟨h1, h2, h3, ⟨u, hcong⟩, h5⟩ := hβ
  exact ⟨idealOfCone_ne_zero h1 h2, fun q hq => not_dvd_idealOfCone 𝔪 𝔡 hcop h1 hcong hq,
    classOfIdeal_idealOfCone 𝔪 𝔡 hcop h1 h2 hcong,
    le_of_eq (absNorm_idealOfCone h1) |>.trans h5⟩

/-! ## Elementary identities for unit coercions -/

theorem unit_coe_mul_coe (a b : (𝓞 K)ˣ) :
    (((a * b : (𝓞 K)ˣ) : 𝓞 K) : K) = ((a : 𝓞 K) : K) * ((b : 𝓞 K) : K) := by
  simp only [RingOfIntegers.coe_eq_algebraMap, Units.val_mul, map_mul]

theorem unit_coe_inv_mul (ζ : (𝓞 K)ˣ) (β : K) :
    (((ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((ζ : 𝓞 K) : K) * β) = β := by
  have h2 : (((ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((ζ : 𝓞 K) : K)) = 1 := by
    rw [← unit_coe_mul_coe ζ⁻¹ ζ, inv_mul_cancel]
    simp
  rw [← mul_assoc, h2, one_mul]

theorem mixedEmbedding_unit_mul (ζ : (𝓞 K)ˣ) (β : K) :
    NumberField.mixedEmbedding K (((ζ : 𝓞 K) : K) * β)
      = ζ • NumberField.mixedEmbedding K β := by
  rw [NumberField.mixedEmbedding.unitSMul_smul, map_mul]

theorem spanSingleton_unit (u : (𝓞 K)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (((u : 𝓞 K) : K)) = 1 := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← FractionalIdeal.coeIdeal_span_singleton,
    show Ideal.span {(u : 𝓞 K)} = ⊤ from Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

/-! ## The generator of a ray class in the cone -/

theorem exists_coneGen (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ∈ idealCarrier 𝔪 𝔡 X) :
    ∃ β : K, β ∈ coneCarrier 𝔪 𝔡 X ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ β =
        (𝔞 : FractionalIdeal (𝓞 K)⁰ K) *
          ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  obtain ⟨h𝔞0, hcop𝔞, hclass, hnorm⟩ := h𝔞
  obtain ⟨α, hα0, hcong, hαeq⟩ :=
    (NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff K 𝔪 𝔞 (𝔡 : Ideal (𝓞 K)) h𝔞0
      (baseIdeal_ne_zero 𝔡) hcop𝔞 hcop).mp hclass
  have h𝔡I : ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡)
  have hspanα : FractionalIdeal.spanSingleton (𝓞 K)⁰ α =
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) *
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [hαeq, mul_assoc,
      mul_comm (FractionalIdeal.spanSingleton (𝓞 K)⁰ α)
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ h𝔡I, one_mul]
  have hαmem : α ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, hspanα]
    calc (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
        ≤ 1 * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
          mul_le_mul_left (coeIdeal_le_one 𝔞) _
      _ = _ := one_mul _
  have hnormα : NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K α) *
        (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) ≤ X := by
    have keyℚ : (Ideal.absNorm 𝔞 : ℚ) = (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℚ) *
        |Algebra.norm ℚ α| := by
      rw [← FractionalIdeal.coeIdeal_absNorm (K := K) 𝔞,
        ← FractionalIdeal.coeIdeal_absNorm (K := K) (𝔡 : Ideal (𝓞 K)), hαeq, map_mul,
        FractionalIdeal.absNorm_span_singleton]
    have key : (Ideal.absNorm 𝔞 : ℝ) = (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) *
        NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K α) := by
      rw [NumberField.mixedEmbedding.norm_eq_norm, Rat.cast_abs]
      exact_mod_cast keyℚ
    calc NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K α) *
          (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ)
        = (Ideal.absNorm 𝔞 : ℝ) := by rw [key]; ring
      _ ≤ X := hnorm
  have hαnorm : NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K α) ≠ 0 := by
    rw [NumberField.mixedEmbedding.norm_eq_norm]
    intro h
    have h' : |Algebra.norm ℚ α| = 0 := by exact_mod_cast h
    exact absurd h' (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hα0))
  obtain ⟨ω, hω⟩ := fundamentalCone.exists_unit_smul_mem (K := K)
    (x := NumberField.mixedEmbedding K α) hαnorm
  refine ⟨((ω : 𝓞 K) : K) * α, ⟨?_, ?_, ?_, ⟨ω⁻¹, ?_⟩, ?_⟩, ?_⟩
  · have h : FractionalIdeal.spanSingleton (𝓞 K)⁰ (((ω : 𝓞 K) : K) * α) ≤
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, spanSingleton_unit, one_mul]
      exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hαmem
    exact FractionalIdeal.spanSingleton_le_iff_mem.mp h
  · exact mul_ne_zero (by simp) hα0
  · rw [mixedEmbedding_unit_mul ω α]
    exact hω
  · rw [unit_coe_inv_mul ω α]
    exact hcong
  · rw [mixedEmbedding_unit_mul, NumberField.mixedEmbedding.norm_unit_smul]
    exact hnormα
  · rw [show FractionalIdeal.spanSingleton (𝓞 K)⁰ (((ω : 𝓞 K) : K) * α)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ α from ?_, hspanα]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, spanSingleton_unit, one_mul]

/-- A chosen generator of the ray class of `𝔞` lying in the fundamental cone. -/
noncomputable def coneGen (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) (𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X}) : K :=
  Classical.choose (exists_coneGen 𝔪 𝔡 hcop X 𝔞.1 𝔞.2)

theorem coneGen_mem (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) (𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X}) :
    coneGen 𝔪 𝔡 hcop X 𝔞 ∈ coneCarrier 𝔪 𝔡 X :=
  (Classical.choose_spec (exists_coneGen 𝔪 𝔡 hcop X 𝔞.1 𝔞.2)).1

theorem span_coneGen (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) (𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X}) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen 𝔪 𝔡 hcop X 𝔞) =
      (𝔞.1 : FractionalIdeal (𝓞 K)⁰ K) *
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  (Classical.choose_spec (exists_coneGen 𝔪 𝔡 hcop X 𝔞.1 𝔞.2)).2

theorem coneGen_ne_zero (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) (𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X}) :
    coneGen 𝔪 𝔡 hcop X 𝔞 ≠ 0 :=
  (coneGen_mem 𝔪 𝔡 hcop X 𝔞).2.1

/-! ## The torsion action on the cone carrier and the multiplicity count -/

theorem torsion_mul_mem_coneCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) {X : ℝ} {β : K}
    (hβ : β ∈ coneCarrier 𝔪 𝔡 X) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ NumberField.Units.torsion K) :
    (((ζ : 𝓞 K) : K) * β) ∈ coneCarrier 𝔪 𝔡 X := by
  obtain ⟨h1, h2, h3, ⟨u, hcong⟩, h5⟩ := hβ
  refine ⟨?_, ?_, ?_, ⟨u * ζ⁻¹, ?_⟩, ?_⟩
  · have h : FractionalIdeal.spanSingleton (𝓞 K)⁰ (((ζ : 𝓞 K) : K) * β) ≤
        ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, spanSingleton_unit, one_mul]
      exact FractionalIdeal.spanSingleton_le_iff_mem.mpr h1
    exact FractionalIdeal.spanSingleton_le_iff_mem.mp h
  · exact mul_ne_zero (by simp) h2
  · rw [mixedEmbedding_unit_mul]
    exact fundamentalCone.torsion_smul_mem_of_mem h3 hζ
  · have hid : (((u * ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((ζ : 𝓞 K) : K) * β)
        = ((u : 𝓞 K) : K) * β := by
      rw [unit_coe_mul_coe u ζ⁻¹]
      have h2' : (((ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((ζ : 𝓞 K) : K)) = 1 := by
        rw [← unit_coe_mul_coe ζ⁻¹ ζ, inv_mul_cancel]
        simp
      calc ((u : 𝓞 K) : K) * (((ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((ζ : 𝓞 K) : K) * β)
          = ((u : 𝓞 K) : K) * ((((ζ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)
              * (((ζ : 𝓞 K) : K))) * β := by ring
        _ = ((u : 𝓞 K) : K) * β := by rw [h2']; ring
    rw [hid]
    exact hcong
  · rw [mixedEmbedding_unit_mul, NumberField.mixedEmbedding.norm_unit_smul]
    exact h5

/-- The map `(ideal in the ray class, torsion unit) ↦ torsion unit • cone generator`. -/
noncomputable def psiFun (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) :
    {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} × NumberField.Units.torsion K →
      {β : K // β ∈ coneCarrier 𝔪 𝔡 X} :=
  fun p => ⟨((((p.2 : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
      * coneGen 𝔪 𝔡 hcop X p.1,
    torsion_mul_mem_coneCarrier 𝔪 𝔡 (coneGen_mem 𝔪 𝔡 hcop X p.1) p.2.2⟩

theorem psiFun_injective (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) : Function.Injective (psiFun 𝔪 𝔡 hcop X) := by
  rintro ⟨𝔞₁, ζ₁⟩ ⟨𝔞₂, ζ₂⟩ h
  simp only [psiFun, Subtype.mk_eq_mk] at h
  have h𝔡I : ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡)
  have hsp : (𝔞₁.1 : FractionalIdeal (𝓞 K)⁰ K) = (𝔞₂.1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have hu1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen 𝔪 𝔡 hcop X 𝔞₁)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰
          (((((ζ₁ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
            * coneGen 𝔪 𝔡 hcop X 𝔞₁) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, spanSingleton_unit, one_mul]
    have hu2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen 𝔪 𝔡 hcop X 𝔞₂)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰
          (((((ζ₂ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
            * coneGen 𝔪 𝔡 hcop X 𝔞₂) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, spanSingleton_unit, one_mul]
    have hmid : FractionalIdeal.spanSingleton (𝓞 K)⁰
          (((((ζ₁ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
            * coneGen 𝔪 𝔡 hcop X 𝔞₁)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰
          (((((ζ₂ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
            * coneGen 𝔪 𝔡 hcop X 𝔞₂) := by
      rw [h]
    have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen 𝔪 𝔡 hcop X 𝔞₁)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen 𝔪 𝔡 hcop X 𝔞₂) :=
      hu1.trans (hmid.trans hu2.symm)
    rw [span_coneGen, span_coneGen] at h1
    have h2 := congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K =>
      I * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) h1
    rw [mul_assoc, inv_mul_cancel₀ h𝔡I, mul_one, mul_assoc, inv_mul_cancel₀ h𝔡I,
      mul_one] at h2
    exact h2
  have h𝔞 : 𝔞₁ = 𝔞₂ := Subtype.ext (FractionalIdeal.coeIdeal_injective hsp)
  have hζ : ζ₁ = ζ₂ := by
    have hcoe : ((((ζ₁ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K)
        = ((((ζ₂ : NumberField.Units.torsion K) : (𝓞 K)ˣ) : 𝓞 K) : K) := by
      refine mul_right_cancel₀ (coneGen_ne_zero 𝔪 𝔡 hcop X 𝔞₂) ?_
      rw [h𝔞] at h
      exact h
    exact Subtype.ext (Units.ext (RingOfIntegers.coe_injective hcoe))
  rw [h𝔞, hζ]

theorem psiFun_surjective (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) : Function.Surjective (psiFun 𝔪 𝔡 hcop X) := by
  rintro ⟨β, hβ⟩
  have h𝔞 : idealOfCone 𝔡 β ∈ idealCarrier 𝔪 𝔡 X :=
    idealOfCone_mem_idealCarrier 𝔪 𝔡 hcop hβ
  have h𝔡I : ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡)
  have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (coneGen 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    rw [span_coneGen, coe_idealOfCone hβ.1, mul_assoc, mul_inv_cancel₀ h𝔡I, mul_one]
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hsp
  have hz' : ((z : 𝓞 K) : K) * coneGen 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩ = β := by
    rw [Units.smul_def, Algebra.smul_def] at hz
    exact hz
  have hcone : NumberField.mixedEmbedding K (coneGen 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩)
      ∈ fundamentalCone K := (coneGen_mem 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩).2.2.1
  have hzmem : z ∈ NumberField.Units.torsion K := by
    refine (fundamentalCone.unit_smul_mem_iff_mem_torsion hcone z).mp ?_
    have h1 : z • NumberField.mixedEmbedding K (coneGen 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩)
        = NumberField.mixedEmbedding K β := by
      rw [← mixedEmbedding_unit_mul z (coneGen 𝔪 𝔡 hcop X ⟨idealOfCone 𝔡 β, h𝔞⟩), hz']
    rw [h1]
    exact hβ.2.2.1
  refine ⟨(⟨idealOfCone 𝔡 β, h𝔞⟩, ⟨z, hzmem⟩), ?_⟩
  apply Subtype.ext
  simp only [psiFun]
  exact hz'

/-- **The cone count is the torsion order times the ideal count.** -/
theorem natCard_coneCarrier_eq_torsion_mul_idealCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) :
    Nat.card {β : K // β ∈ coneCarrier 𝔪 𝔡 X} =
      NumberField.Units.torsionOrder K *
        Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} := by
  have hbij : Function.Bijective (psiFun 𝔪 𝔡 hcop X) :=
    ⟨psiFun_injective 𝔪 𝔡 hcop X, psiFun_surjective 𝔪 𝔡 hcop X⟩
  calc Nat.card {β : K // β ∈ coneCarrier 𝔪 𝔡 X}
      = Nat.card ({𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} ×
          NumberField.Units.torsion K) :=
        Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} *
          Nat.card (NumberField.Units.torsion K) := Nat.card_prod _ _
    _ = Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} *
          NumberField.Units.torsionOrder K := rfl
    _ = NumberField.Units.torsionOrder K *
          Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ∈ idealCarrier 𝔪 𝔡 X} := Nat.mul_comm _ _

end NK.NUV2.RouteB.CongCount
