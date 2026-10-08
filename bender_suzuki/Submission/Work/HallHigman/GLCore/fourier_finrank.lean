import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.FourierSetup
import Submission.Work.HallHigman.GLCore.sum_over_center_cosets
import Submission.Work.HallHigman.GLCore.fourier_master_identity
import Submission.Work.HallHigman.GLCore.fourierP_mul_of_notMem_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.HallHigman.GLCore

open Finset

universe u v w

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V]
variable {E : Type*} [Group E] [Fintype E]

omit [Nontrivial V] in
/-- A central element `z` acts on the Fourier projector in a compatible way:
`σ z · P(σ z⁻¹ · X) = P X`. -/
theorem fourierP_center_conj (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    {z : E} (hz : z ∈ Subgroup.center E) (X : Module.End K V) :
    σ z * fourierP σ (σ z⁻¹ * X) = fourierP σ X := by
  have hz' : z⁻¹ ∈ Subgroup.center E := (Subgroup.center E).inv_mem hz
  have hzz : (σ z : Module.End K V) * σ z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [fourierP_smul_center σ hsc hz' X, ← mul_assoc, hzz, one_mul]

/-- The coordinates of `Θ β` can be recovered from `Θ β`: `β q = P(σ(out q)⁻¹ · Θ β)`.  All the
terms of the associated sum disappear by `fourierP_mul_of_notMem_center` except the one at `q`. -/
theorem fourierTheta_extract (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0) [Fintype (E ⧸ Subgroup.center E)]
    (β : (E ⧸ Subgroup.center E) → commutantOf σ) (q₀ : E ⧸ Subgroup.center E) :
    ((β q₀ : commutantOf σ) : Module.End K V)
      = fourierP σ (σ ((Quotient.out q₀)⁻¹) * fourierTheta σ β) := by
  have hne : ∀ q : E ⧸ Subgroup.center E, q ≠ q₀ →
      ((Quotient.out q₀)⁻¹ * Quotient.out q : E) ∉ Subgroup.center E := by
    intro q hq hmem
    apply hq
    have h2 : (Quotient.mk'' (Quotient.out q₀) : E ⧸ Subgroup.center E)
        = Quotient.mk'' (Quotient.out q) := (QuotientGroup.eq).mpr hmem
    rw [Quotient.out_eq', Quotient.out_eq'] at h2
    exact h2.symm
  rw [fourierTheta_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single q₀]
  · have h4 : (σ ((Quotient.out q₀)⁻¹)
        * (σ (Quotient.out q₀) * ((β q₀ : commutantOf σ) : Module.End K V)))
        = ((β q₀ : commutantOf σ) : Module.End K V) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [h4, fourierP_eq_self σ hE (β q₀).2]
  · intro q _ hqne
    rw [show (σ ((Quotient.out q₀)⁻¹) * (σ (Quotient.out q) * (β q : Module.End K V)))
        = σ ((Quotient.out q₀)⁻¹ * Quotient.out q) * ((β q : commutantOf σ) : Module.End K V)
        from by rw [← mul_assoc, ← map_mul]]
    exact fourierP_mul_of_notMem_center σ hsc hfaith hcomm (hne q hqne) (β q).2
  · intro h
    exact absurd (Finset.mem_univ q₀) h

/-- `Θ` is injective: its coordinates are recovered by `fourierTheta_extract`. -/
theorem fourierTheta_injective (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0) [Fintype (E ⧸ Subgroup.center E)] :
    Function.Injective (fourierTheta σ) := by
  intro β γ hβγ
  funext q₀
  apply Subtype.ext
  rw [fourierTheta_extract σ hsc hfaith hcomm hE β q₀,
    fourierTheta_extract σ hsc hfaith hcomm hE γ q₀, hβγ]

/-- `Θ` is surjective: the master identity, decomposed coset by coset (every coset of `Z(E)`
contributes `|Z(E)|` times its representative's term), shows that `β q = P(σ(out q)⁻¹ · Y)` is a
preimage of `Y`. -/
theorem fourierTheta_surjective (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0) [Fintype ↥(Subgroup.center E)]
    [Fintype (E ⧸ Subgroup.center E)] : Function.Surjective (fourierTheta σ) := by
  intro Y
  let β : (E ⧸ Subgroup.center E) → commutantOf σ :=
    fun q => ⟨fourierP σ (σ ((Quotient.out q)⁻¹) * Y), fourierP_mem_commutantOf σ _⟩
  refine ⟨β, ?_⟩
  have hZ : (Nat.card (Subgroup.center E) : K) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card (Subgroup.center E)
    exact hE (by rw [hm, Nat.cast_mul, h, zero_mul])
  have hkey : (Nat.card (Subgroup.center E) : K) • Y
      = (Nat.card (Subgroup.center E) : K) • fourierTheta σ β := by
    rw [← fourier_master_identity σ hsc hfaith hcomm hE Y, sum_over_center_cosets,
      fourierTheta_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hpt : ∀ z : Subgroup.center E,
        σ (Quotient.out q * (z : E)) * fourierP σ (σ ((Quotient.out q * (z : E))⁻¹) * Y)
        = σ (Quotient.out q) * fourierP σ (σ ((Quotient.out q)⁻¹) * Y) := by
      intro z
      have h1 : (σ ((Quotient.out q * (z : E))⁻¹) : Module.End K V)
          = σ ((z : E)⁻¹) * σ ((Quotient.out q)⁻¹) := by
        rw [mul_inv_rev, map_mul]
      have h2 : (σ (Quotient.out q * (z : E)) : Module.End K V)
          = σ (Quotient.out q) * σ (z : E) := map_mul _ _ _
      have h3 : ((σ ((z : E)⁻¹) * σ ((Quotient.out q)⁻¹)) * Y)
          = σ ((z : E)⁻¹) * (σ ((Quotient.out q)⁻¹) * Y) := by rw [mul_assoc]
      rw [h2, h1, h3, mul_assoc, fourierP_center_conj σ hsc z.2 (σ ((Quotient.out q)⁻¹) * Y)]
    calc ∑ z : Subgroup.center E,
            σ (Quotient.out q * (z : E)) * fourierP σ (σ ((Quotient.out q * (z : E))⁻¹) * Y)
        = ∑ _z : Subgroup.center E,
            (σ (Quotient.out q) * fourierP σ (σ ((Quotient.out q)⁻¹) * Y)) :=
          Finset.sum_congr rfl (fun z _ => hpt z)
      _ = (Nat.card (Subgroup.center E) : K)
            • (σ (Quotient.out q) * fourierP σ (σ ((Quotient.out q)⁻¹) * Y)) := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
            Nat.cast_smul_eq_nsmul]
  have hYY : Y = fourierTheta σ β := by
    have h := congrArg (fun z : Module.End K V => (Nat.card (Subgroup.center E) : K)⁻¹ • z) hkey
    rwa [smul_smul, inv_mul_cancel₀ hZ, one_smul, smul_smul, inv_mul_cancel₀ hZ, one_smul] at h
  exact hYY.symm

/-- **L8 of the GL-core design** (Step 4c, "the Fourier lemma", the heart of the proof of
Hall--Higman B, see `NOTES_LEAD_ft_hallhigman.md` §2.2): let `E` be a finite group of order
invertible in `K` acting on `V` through `σ`, with `Z(E)` acting by scalars through an injective
`λ`, and with all commutators central.  Then
`dim End_K V = |E / Z(E)| · dim End_E(V)`.

The projector `P(Y) = |E|⁻¹ Σ_f σ(f) Y σ(f)⁻¹` onto `End_E(V)` satisfies
`Σ_{e∈E} σ(e) P(σ(e)⁻¹ Y) = |Z(E)|·Y` (surjectivity of `Θ`), and `P(σ(g) β) = 0` for
`β ∈ End_E(V)` and `g ∉ Z(E)` (injectivity of `Θ`); both follow from
`Σ_e λ([e,f]) = 0` for `f ∉ Z(E)`, which is `sum_hom_units_eq_zero` applied to the nontrivial
homomorphism `e ↦ λ([e,f])` of the finite group `E` into `Kˣ`. -/
lemma fourier_finrank {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {E : Type*} [Group E] [Finite E]
    (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0) :
    Module.finrank K (Module.End K V)
      = Nat.card (E ⧸ Subgroup.center E) * Module.finrank K (Work.HallHigman.commutantOf σ) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype ↥(Subgroup.center E) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Subgroup.center E) := Fintype.ofFinite _
  have hbij : Function.Bijective (fourierTheta σ) :=
    ⟨fourierTheta_injective σ hsc hfaith hcomm hE,
      fourierTheta_surjective σ hsc hfaith hcomm hE⟩
  rw [(LinearEquiv.finrank_eq (LinearEquiv.ofBijective (fourierTheta σ) hbij)).symm,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact nsmul_eq_mul _ _

end Work.HallHigman.GLCore
