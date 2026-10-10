import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.finHalfData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `G1plusOwn.exists_unramified_level_factors`

The *algebraic* (cocycle) bookkeeping of the level-existence statement
`Work.SSGRoute.PT.G1plusOwn.exists_unramified_level_factors` (clause (6) of `G1⁺`'s finite half):
the **period subgroup** of a `1`-cocycle `b` on the decomposition group `D_A`,
`{u ∈ D_A | ∀ g ∈ D_A, b (g*u) = b g}`, on which `b` vanishes, together with the compactness step
producing a finite normal level `M ⊇ K` with `D_A ∩ Gal(Ω/M) ⊆ periodSub`, and the resulting
factorisation of `b` through `Gal(Ω/k) →* Gal(M/k)`.

The two steps listed as "not yet here" in the first version of this note are now proved below
(`sup_inertia_inf_decomp_le_periodSub` + `exists_normal_inf_le_periodSub` +
`exists_level_decomp_le_periodSub`), using `krullTopology_mem_nhds_one_iff_of_normal` to refine the
constancy subgroup of `hl` to a *normal* one and `Subgroup.mul_normal`.

What remains for the full statement is the **arithmetic** half: an *unramified* such level, see
`Submission/Work/SSGRoute/PT/G1plusOwn/NOTE_unramified_level_factors_route.md` §2 (and §5).

-/

open scoped TensorProduct Topology
namespace Work.SSGRoute

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Period

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (↥K ≃ₐ[k] ↥K) T] [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) T]
  {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (↥K ≃ₐ[k] ↥K) M] [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) M]

/-- A `1`-cocycle on `D_A` takes the value `0` at `1`. -/
theorem b_one_eq_zero (A : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) : b 1 = 0 := by
  have h := hb 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, map_one, one_smul] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- **The period subgroup** of a `1`-cocycle `b` on the decomposition group `D_A`: the `u ∈ D_A`
with `b (g*u) = b g` for every `g ∈ D_A`.  Closure under products is the cocycle identity applied
twice; closure under inverses uses `b u = b (1*u) = b 1 = 0`. -/
def periodSub (A : ValuationSubring Ω)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    Subgroup (Ω ≃ₐ[k] Ω) where
  carrier := {u | u ∈ SSGRoute.decomp k A ∧
    ∀ g ∈ SSGRoute.decomp k A, b (g * u) = b g}
  mul_mem' := by
    rintro u v ⟨huD, hu⟩ ⟨hvD, hv⟩
    exact ⟨mul_mem huD hvD, fun g hg => by
      rw [← mul_assoc, hv (g * u) (mul_mem hg huD), hu g hg]⟩
  one_mem' := ⟨one_mem _, fun g _ => by rw [mul_one]⟩
  inv_mem' := by
    rintro u ⟨huD, hu⟩
    have h1 : b 1 = 0 := b_one_eq_zero (T := T) A hb
    have hu0 : b u = 0 := by simpa using (hu 1 (one_mem _)).trans h1
    refine ⟨inv_mem huD, fun g hg => ?_⟩
    have hc := hb (g * u⁻¹) (mul_mem hg (inv_mem huD)) u huD
    rw [mul_assoc, inv_mul_cancel, mul_one, hu0, smul_zero, add_zero] at hc
    exact hc.symm

lemma mem_periodSub {A : ValuationSubring Ω}
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) {u : Ω ≃ₐ[k] Ω} :
    u ∈ periodSub (T := T) A b hb ↔
      u ∈ SSGRoute.decomp k A ∧ ∀ g ∈ SSGRoute.decomp k A, b (g * u) = b g := Iff.rfl

lemma periodSub_le_decomp (A : ValuationSubring Ω)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    periodSub (T := T) A b hb ≤ SSGRoute.decomp k A := fun _ hu => hu.1

/-- On the period subgroup a cocycle vanishes (`b u = b (1*u) = b 1 = 0`). -/
lemma eq_zero_of_mem_periodSub (A : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    {u : Ω ≃ₐ[k] Ω} (hu : u ∈ periodSub (T := T) A b hb) : b u = 0 := by
  have h1 : b 1 = 0 := b_one_eq_zero (T := T) A hb
  simpa using (hu.2 1 (one_mem _)).trans h1

/-- The constancy subgroup of a locally constant cochain lies in the period subgroup. -/
lemma inf_le_periodSub (A : ValuationSubring Ω)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (U : Subgroup (Ω ≃ₐ[k] Ω))
    (hU : ∀ g ∈ SSGRoute.decomp k A, ∀ u ∈ U, u ∈ SSGRoute.decomp k A → b (g * u) = b g) :
    U ⊓ SSGRoute.decomp k A ≤ periodSub (T := T) A b hb := by
  rintro u ⟨huU, huD⟩
  exact ⟨huD, fun g hg => hU g hg u huU huD⟩

/-- The inertia lies in the period subgroup, provided it fixes `K` (this is exactly
`¬ IsRamifiedIn` at the level `K`): `b (γ * ι) = b γ + res γ • b ι = b γ`. -/
lemma inertiaSub_le_periodSub (A : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0)
    (hramK : (inertiaSub k Ω A) ≤ K.fixingSubgroup) :
    inertiaSub k Ω A ≤ periodSub (T := T) A b hb := by
  intro ι hι
  have hιD : ι ∈ SSGRoute.decomp k A := inertiaSub_le_decomp k Ω A hι
  have hbι : b ι = 0 := hiner ι ((mem_inertiaSub k Ω A ι).mp hι)
  exact ⟨hιD, fun g hg => by rw [hb g hg ι hιD, hbι, smul_zero, add_zero]⟩

/-- The fixing subgroup of a finite normal level is contained in the level subgroup: an element
fixing `M` pointwise acts trivially on `B ∩ M` modulo the maximal ideal. -/
lemma inf_fixingSubgroup_le_levelSub (A : ValuationSubring Ω)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] :
    SSGRoute.decomp k A ⊓ M.fixingSubgroup ≤ levelSub A M := by
  rintro x ⟨hxD, hxf⟩
  refine ⟨hxD, fun y => ?_⟩
  have hyM : ((y : ↥M) : Ω) ∈ M := (y : ↥M).2
  have hy : x ((y : ↥M) : Ω) = ((y : ↥M) : Ω) :=
    (IntermediateField.mem_fixingSubgroup_iff M x).mp hxf _ hyM
  rw [hy, sub_self, Valuation.map_zero]
  exact zero_lt_one

/-- The trace of `U ⊔ I_A` on `D_A` lies in the period subgroup, for a **normal** `U` with the
constancy property: `↑(I_A ⊔ U) = I_A * U` by `Subgroup.mul_normal` (the second factor normal), so
`x ∈ (I_A ⊔ U) ∩ D_A` is a single product `ι * u`, and the cocycle identity gives
`b x = b (g * (ι*u)) = b g`. -/
lemma sup_inertia_inf_decomp_le_periodSub (A : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0)
    (U : Subgroup (Ω ≃ₐ[k] Ω)) [U.Normal]
    (hU : ∀ g ∈ SSGRoute.decomp k A, ∀ u ∈ U, u ∈ SSGRoute.decomp k A → b (g * u) = b g) :
    (U ⊔ inertiaSub k Ω A) ⊓ SSGRoute.decomp k A ≤ periodSub (T := T) A b hb := by
  intro x hx
  have hxD : x ∈ SSGRoute.decomp k A := hx.2
  have hxword : x ∈ ((inertiaSub k Ω A ⊔ U : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := by
    rw [sup_comm]; exact hx.1
  rw [Subgroup.mul_normal (inertiaSub k Ω A) U, Set.mem_mul] at hxword
  obtain ⟨ι, hι, u, hu, hxeq⟩ := hxword
  have hιD : ι ∈ SSGRoute.decomp k A := inertiaSub_le_decomp k Ω A hι
  have huD : u ∈ SSGRoute.decomp k A := by
    have h : u = ι⁻¹ * x := by rw [← hxeq]; group
    rw [h]; exact mul_mem (inv_mem hιD) hxD
  have hbu : b u = 0 := by
    have h := hU 1 (one_mem _) u hu huD
    rw [one_mul] at h
    exact h.trans (b_one_eq_zero (T := T) A hb)
  refine ⟨by rw [← hxeq]; exact mul_mem hιD huD, fun g hg => ?_⟩
  have hgι : g * ι ∈ SSGRoute.decomp k A := mul_mem hg hιD
  have h1 : b (g * ι) = b g := by
    rw [hb g hg ι hιD, hiner ι ((mem_inertiaSub k Ω A ι).mp hι), smul_zero, add_zero]
  rw [← hxeq, ← mul_assoc, hb (g * ι) hgι u huD, h1, hbu, smul_zero, add_zero]

/-- A **normal** open subgroup with the constancy property (the `IsLocConstOn` datum can be
refined by Krull's correspondence: every open subgroup contains the fixing subgroup of a finite
normal level). -/
lemma exists_normal_inf_le_periodSub (A : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), U.Normal ∧ IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      U ⊓ SSGRoute.decomp k A ≤ periodSub (T := T) A b hb := by
  obtain ⟨U₀, hU₀open, hU₀⟩ := hl
  have hmem : ((U₀ : Set (Ω ≃ₐ[k] Ω))) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) :=
    hU₀open.mem_nhds U₀.one_mem
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω (U₀ : Set (Ω ≃ₐ[k] Ω))).mp hmem
  haveI := hEfin
  haveI := hEnorm
  refine ⟨E.fixingSubgroup, ?_, E.fixingSubgroup_isOpen,
    inf_le_periodSub (T := T) A b hb E.fixingSubgroup
      (fun g hg u hu huD => hU₀ g hg u (hEsub hu) huD)⟩
  exact IsGalois.fixingSubgroup_normal_of_isGalois E

/-- **The level-existence, first half.**  For a locally constant `1`-cocycle `b` on `D_A` vanishing
on the inertia there is a finite normal level `L ⊇ K` with `D_A ⊓ L.fixingSubgroup ≤ periodSub`.
(`L` need not be unramified at `A`; that is the arithmetic half, see the route note.) -/
theorem exists_level_decomp_le_periodSub (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧ SSGRoute.decomp k A ⊓ L.fixingSubgroup ≤ periodSub (T := T) A b hb := by
  obtain ⟨U, hUnorm, hUopen, hUle⟩ := exists_normal_inf_le_periodSub (T := T) A hb hl
  haveI := hUnorm
  have hVopen : IsOpen (((U ⊔ inertiaSub k Ω A : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω))) := by
    have hmem : (((U ⊔ inertiaSub k Ω A : Subgroup (Ω ≃ₐ[k] Ω))) :
        Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) :=
      Filter.mem_of_superset (hUopen.mem_nhds U.one_mem)
        (fun y hy => Subgroup.mem_sup_left hy)
    exact Subgroup.isOpen_of_mem_nhds _ hmem
  have hIopen : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ →
      σ ∈ (U ⊔ inertiaSub k Ω A : Subgroup (Ω ≃ₐ[k] Ω)) :=
    fun _ hσ => Subgroup.mem_sup_right ((mem_inertiaSub k Ω A _).mpr hσ)
  obtain ⟨M₀, hM₀fin, hM₀norm, hM₀le⟩ :=
    exists_levelSub_le_of_isOpen k Ω A hA (U ⊔ inertiaSub k Ω A) hVopen hIopen
  haveI := hM₀fin
  haveI := hM₀norm
  refine ⟨M₀ ⊔ K, inferInstance, inferInstance, le_sup_right, ?_⟩
  intro x hx
  have hxM₀ : x ∈ levelSub A M₀ := inf_fixingSubgroup_le_levelSub A M₀
    ⟨hx.1, IntermediateField.fixingSubgroup_antitone le_sup_left hx.2⟩
  exact sup_inertia_inf_decomp_le_periodSub (T := T) A hb hiner U
    (fun g hg u hu huD => (hUle ⟨hu, huD⟩).2 g hg) ⟨hM₀le hxM₀, hx.1⟩

/-- **The factorisation.**  If `b` vanishes on `D_A ∩ Gal(Ω/L)`, then `b` factors on `D_A` through
the restriction map `Gal(Ω/k) →* Gal(L/k)`. -/
theorem exists_factor_of_periodSub (A : ValuationSubring Ω) {L : IntermediateField k Ω}
    [FiniteDimensional k L] [Normal k L]
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hsub : SSGRoute.decomp k A ⊓ L.fixingSubgroup ≤ periodSub (T := T) A b hb) :
    ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  classical
  refine ⟨fun τ => if h : ∃ σ : Ω ≃ₐ[k] Ω,
      σ ∈ SSGRoute.decomp k A ∧ AlgEquiv.restrictNormalHom L σ = τ
    then b h.choose else 0, ?_⟩
  intro σ hσ
  have hex : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ SSGRoute.decomp k A ∧
      AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ := ⟨σ, hσ, rfl⟩
  have hbeta : (fun τ => if h : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ SSGRoute.decomp k A ∧
        AlgEquiv.restrictNormalHom L σ' = τ then b h.choose else 0)
      (AlgEquiv.restrictNormalHom L σ) = (if h : ∃ σ' : Ω ≃ₐ[k] Ω,
      σ' ∈ SSGRoute.decomp k A ∧ AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ
    then b h.choose else 0) := rfl
  rw [hbeta, dif_pos hex]
  obtain ⟨hcD, hceq⟩ := hex.choose_spec
  have hxker : σ⁻¹ * hex.choose ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom ↥L) (σ⁻¹ * hex.choose) = 1
    rw [map_mul, map_inv, hceq, inv_mul_cancel]
  have hxinf : σ⁻¹ * hex.choose ∈ SSGRoute.decomp k A ⊓ L.fixingSubgroup :=
    ⟨(SSGRoute.decomp k A).mul_mem ((SSGRoute.decomp k A).inv_mem hσ) hcD, hxker⟩
  have hb0 : b (σ⁻¹ * hex.choose) = 0 :=
    eq_zero_of_mem_periodSub (T := T) A hb (hsub hxinf)
  have hc := hb σ hσ (σ⁻¹ * hex.choose) hxinf.1
  have hsimp : σ * (σ⁻¹ * hex.choose) = hex.choose := by group
  rw [hsimp, hb0, smul_zero, add_zero] at hc
  exact hc.symm

end Period

end Work.SSGRoute
