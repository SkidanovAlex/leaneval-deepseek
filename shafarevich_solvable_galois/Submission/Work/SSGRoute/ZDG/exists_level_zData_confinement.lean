import Mathlib
import Submission.Work.SSGRoute.auxFieldExponentP
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.exists_level_vanishing_minimal_ramification
import Submission.Work.SSGRoute.ZConstruction.RamificationConfinement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDG

open scoped Pointwise

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# A single level witnessing vanishing, exponent-`p` and commutators, inertia at `S`, and
`z`-confinement of its ramification

`Work.SSGRoute.ZDG.exists_level_zData_confinement` assembles, in one field `L`, the properties
that the `z`-data companion level of Schmidt--Wingberg §4 must satisfy:

* `L ⊇ K` is finite and normal over `k` and `z` vanishes on `Gal(Ω/L)` (clauses 1--3);
* `Gal(Ω/L)` contains the `p`-th powers and the commutators of `Gal(Ω/K)` (clauses 4--5);
* `Gal(Ω/L)` contains the inertia (inside `Gal(Ω/K)`) of every place `k`-conjugate into `S`
  (clause 6, the *vanishing at `S`* condition);
* every place ramified in `L`, outside the conjugates of `S` and unramified in `K`, is witnessed by
  a conjugate `Q` at which `z` does *not* vanish on the inertia of `Gal(Ω/K)` (clause 7, the
  *confinement* of the ramification of `L`).

The construction is that of `auxFieldExponentP` and
`exists_level_vanishing_minimal_ramification`: with `H = K.fixingSubgroup` and
`Z = {g ∈ H | z g = 0}` (a subgroup, open because `z` is locally constant), the level is the fixed
field of `W = {x | ∀ g, g x g⁻¹ ∈ Z}`, the largest normal subgroup of `G_k` contained in `Z`.  The
minimality of `W` is exactly the confinement of clause 7, and clause 6 follows from the hypothesis
`hI` applied at the translates `g • B` of a place `B` conjugate into `S`.
-/

/-- **The `z`-data confinement level.**  There is a single finite normal level `L ⊇ K` which kills
`z` on `Gal(Ω/L)`, contains the `p`-th powers and commutators of `Gal(Ω/K)`, contains the inertia at
the places conjugate into `S`, and whose ramification outside `cs(S)` is explained by the places
where `z` is ramified. -/
theorem exists_level_zData_confinement (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [Normal k K]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z)
    (S : Finset (ValuationSubring Ω))
    (hI : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ Normal k L ∧ K ≤ L ∧
      (∀ σ ∈ L.fixingSubgroup, z σ = 0) ∧
      (∀ σ ∈ K.fixingSubgroup, σ ^ p ∈ L.fixingSubgroup) ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
        σ * τ * σ⁻¹ * τ⁻¹ ∈ L.fixingSubgroup) ∧
      (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → σ ∈ L.fixingSubgroup) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ¬ SSGRoute.IsRamifiedIn k K B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsRamifiedIn k L B →
        ∃ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q ∧
          ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k Q σ ∧ z σ ≠ 0) := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- `Gal(Ω/K)` is normal in `G_k`, because `K/k` is normal.
  have hHnorm : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker K]
    infer_instance
  -- `z` is additive on the group `H = K.fixingSubgroup`, with values in a group of exponent `p`.
  have hz1 : z 1 = 0 := by
    have h1 : (1 : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := K.fixingSubgroup.one_mem
    have h : z (1 * 1) = z 1 + z 1 := hzadd 1 h1 1 h1
    rw [one_mul] at h
    exact (add_left_cancel (show z 1 + 0 = z 1 + z 1 by rw [add_zero]; exact h)).symm
  have hz_inv : ∀ g ∈ K.fixingSubgroup, z g⁻¹ = - z g := by
    intro g hg
    have h : z (g * g⁻¹) = z g + z g⁻¹ := hzadd g hg g⁻¹ (K.fixingSubgroup.inv_mem hg)
    rw [mul_inv_cancel, hz1] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)
  -- `z (g ^ n) = n • z g`; in particular `z (g ^ p) = 0` since `E` has exponent `p`.
  have hz_pow : ∀ (n : ℕ) (g : Ω ≃ₐ[k] Ω), g ∈ K.fixingSubgroup → z (g ^ n) = n • z g := by
    intro n
    induction n with
    | zero => intro g _; simp [hz1]
    | succ n ih =>
      intro g hg
      have hgm : g ^ n ∈ K.fixingSubgroup := K.fixingSubgroup.pow_mem hg n
      rw [pow_succ, hzadd (g ^ n) hgm g hg, ih g hg]
      exact (succ_nsmul (z g) n).symm
  -- `z` kills commutators of `H`, `E` being abelian.
  have hz_comm : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      z (g * h * g⁻¹ * h⁻¹) = 0 := by
    intro g hg h hh
    have hg' : g⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hg
    have hh' : h⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hh
    have h1 : z (g * h * g⁻¹ * h⁻¹) = z (g * h) + z (g⁻¹ * h⁻¹) := by
      rw [mul_assoc (g * h) g⁻¹ h⁻¹]
      exact hzadd (g * h) (K.fixingSubgroup.mul_mem hg hh) (g⁻¹ * h⁻¹)
        (K.fixingSubgroup.mul_mem hg' hh')
    rw [h1, hzadd g hg h hh, hzadd g⁻¹ hg' h⁻¹ hh', hz_inv g hg, hz_inv h hh]
    abel
  -- The subgroup of `H` on which `z` vanishes.
  let Z : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {g | g ∈ K.fixingSubgroup ∧ z g = 0}
      mul_mem' := by
        intro a b ha hb
        exact ⟨K.fixingSubgroup.mul_mem ha.1 hb.1,
          by rw [hzadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨K.fixingSubgroup.one_mem, hz1⟩
      inv_mem' := by
        intro a ha
        refine ⟨K.fixingSubgroup.inv_mem ha.1, ?_⟩
        have h := hzadd a ha.1 a⁻¹ (K.fixingSubgroup.inv_mem ha.1)
        rw [mul_inv_cancel, hz1, ha.2, zero_add] at h
        exact h.symm }
  have hZmem : ∀ g : Ω ≃ₐ[k] Ω, g ∈ Z ↔ g ∈ K.fixingSubgroup ∧ z g = 0 := by
    intro g
    change (g ∈ K.fixingSubgroup ∧ z g = 0) ↔ (g ∈ K.fixingSubgroup ∧ z g = 0)
    exact Iff.rfl
  -- A *normal* open subgroup of `G_k` on which `z` vanishes (from local constancy of `z`).
  have hexU : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ U.Normal ∧
      ∀ u ∈ U, u ∈ K.fixingSubgroup → z u = 0 := by
    obtain ⟨U₀, hU₀open, hU₀c⟩ := hzloc
    have hmem : (U₀ : Set (Ω ≃ₐ[k] Ω)) ∈ nhds 1 :=
      isOpen_iff_mem_nhds.mp hU₀open 1 U₀.one_mem
    obtain ⟨M, hMfin, hMnorm, hMle⟩ :=
      (krullTopology_mem_nhds_one_iff_of_normal k Ω (U₀ : Set (Ω ≃ₐ[k] Ω))).mp hmem
    haveI : FiniteDimensional k M := hMfin
    haveI : Normal k M := hMnorm
    refine ⟨M.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen M, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker M]
      infer_instance
    · intro u hu huK
      have h := hU₀c 1 K.fixingSubgroup.one_mem u (hMle hu) huK
      rw [one_mul, hz1] at h
      exact h
  obtain ⟨U, hUo, hUn, hUvan⟩ := hexU
  -- The largest normal subgroup of `G_k` contained in `Z`, as an explicit intersection.
  let W : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {x | ∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z}
      mul_mem' := by
        intro x y hx hy g
        have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [h]; exact Z.mul_mem (hx g) (hy g)
      one_mem' := by
        intro g
        have h : g * 1 * g⁻¹ = 1 := by group
        rw [h]; exact Z.one_mem
      inv_mem' := by
        intro x hx g
        have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [h]; exact Z.inv_mem (hx g) }
  have hWmem : ∀ x : Ω ≃ₐ[k] Ω, x ∈ W ↔ ∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z := by
    intro x
    change (∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z) ↔ (∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z)
    exact Iff.rfl
  have hWZ : W ≤ Z := by
    intro x hx
    have h := (hWmem x).mp hx 1
    simpa using h
  have hWnorm : W.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hWmem]
    intro h
    have heq : h * (g * x * g⁻¹) * h⁻¹ = (h * g) * x * (h * g)⁻¹ := by group
    rw [heq]
    exact (hWmem x).mp hx (h * g)
  have hUWK : U ⊓ K.fixingSubgroup ≤ W := by
    intro x hx
    rw [hWmem x]
    intro g
    exact ⟨hHnorm.conj_mem x hx.2 g,
      hUvan (g * x * g⁻¹) (hUn.conj_mem x hx.1 g) (hHnorm.conj_mem x hx.2 g)⟩
  have hWopen : IsOpen (W : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono hUWK (hUo.inter (IntermediateField.fixingSubgroup_isOpen K))
  have hWclosed : IsClosed (W : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen W hWopen
  have hLfix : (IntermediateField.fixedField W).fixingSubgroup = W :=
    InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) ⟨W, hWclosed⟩
  have hKL : K ≤ IntermediateField.fixedField W :=
    (IntermediateField.le_iff_le W K).mpr (hWZ.trans (fun g hg => ((hZmem g).mp hg).1))
  have hLfd : FiniteDimensional k (IntermediateField.fixedField W) :=
    (InfiniteGalois.isOpen_iff_finite (k := k) (K := Ω) (IntermediateField.fixedField W)).mp
      (by rw [hLfix]; exact hWopen)
  have hLnorm : Normal k (IntermediateField.fixedField W) :=
    ((InfiniteGalois.normal_iff_isGalois (k := k) (K := Ω)
      (IntermediateField.fixedField W)).mp (by rw [hLfix]; exact hWnorm)).to_normal
  -- Minimality of `W` (the confinement of the ramification of `L`).
  have hmin : ∀ B : ValuationSubring Ω, IsFinPlace k B → ¬ IsRamifiedIn k K B →
      (∀ τ : Ω ≃ₐ[k] Ω, ∀ σ ∈ K.fixingSubgroup, IsInertia k (τ • B) σ → z σ = 0) →
      ¬ IsRamifiedIn k (IntermediateField.fixedField W) B := by
    intro B _hB hKunram hcond hramB
    obtain ⟨σ, hσI, hσN⟩ := hramB
    apply hσN
    rw [hLfix]
    rw [hWmem σ]
    have hσK : σ ∈ K.fixingSubgroup :=
      mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn K B hKunram σ hσI
    intro g
    exact ⟨hHnorm.conj_mem σ hσK g,
      hcond g (g * σ * g⁻¹) (hHnorm.conj_mem σ hσK g) ((isInertia_conj B g σ).mpr hσI)⟩
  refine ⟨IntermediateField.fixedField W, hLfd, hLnorm, hKL, ?_, ?_, ?_, ?_, ?_⟩
  · -- `z` vanishes on `Gal(Ω/L)`.
    intro g hg
    rw [hLfix] at hg
    exact ((hZmem g).mp (hWZ hg)).2
  · -- `p`-th powers of `Gal(Ω/K)` lie in `Gal(Ω/L)`.
    intro σ hσ
    rw [hLfix]
    rw [hWmem (σ ^ p)]
    intro b
    have hb : b * σ ^ p * b⁻¹ = (b * σ * b⁻¹) ^ p :=
      (conj_pow (a := b) (b := σ) (i := p)).symm
    have hmem : b * σ * b⁻¹ ∈ K.fixingSubgroup := hHnorm.conj_mem σ hσ b
    refine ⟨?_, ?_⟩
    · rw [hb]; exact K.fixingSubgroup.pow_mem hmem p
    · rw [hb, hz_pow p (b * σ * b⁻¹) hmem,
        ← Nat.cast_smul_eq_nsmul (ZMod p) p (z (b * σ * b⁻¹)), ZMod.natCast_self, zero_smul]
  · -- Commutators of `Gal(Ω/K)` lie in `Gal(Ω/L)`.
    intro σ hσ τ hτ
    rw [hLfix]
    rw [hWmem (σ * τ * σ⁻¹ * τ⁻¹)]
    intro b
    have hmemσ : b * σ * b⁻¹ ∈ K.fixingSubgroup := hHnorm.conj_mem σ hσ b
    have hmemτ : b * τ * b⁻¹ ∈ K.fixingSubgroup := hHnorm.conj_mem τ hτ b
    have hb : b * (σ * τ * σ⁻¹ * τ⁻¹) * b⁻¹ =
        (b * σ * b⁻¹) * (b * τ * b⁻¹) * (b * σ * b⁻¹)⁻¹ * (b * τ * b⁻¹)⁻¹ := by
      group
    have hmem' : (b * σ * b⁻¹) * (b * τ * b⁻¹) * (b * σ * b⁻¹)⁻¹ * (b * τ * b⁻¹)⁻¹ ∈
        K.fixingSubgroup :=
      K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem
        (K.fixingSubgroup.mul_mem hmemσ hmemτ) (K.fixingSubgroup.inv_mem hmemσ))
        (K.fixingSubgroup.inv_mem hmemτ)
    refine ⟨?_, ?_⟩
    · rw [hb]; exact hmem'
    · rw [hb]
      exact hz_comm (b * σ * b⁻¹) hmemσ (b * τ * b⁻¹) hmemτ
  · -- The inertia at the places conjugate into `S` lies in `Gal(Ω/L)`.
    intro B hB σ hσ hσI
    rw [hLfix]
    rw [hWmem σ]
    intro g
    refine ⟨hHnorm.conj_mem σ hσ g, ?_⟩
    have hIσ : IsInertia k (g • B) (g * σ * g⁻¹) := (isInertia_conj B g σ).mpr hσI
    obtain ⟨A, hA, hAB⟩ := hB
    exact hI (g • B) ⟨A, hA, isConjPlace_smul hAB g⟩ (g * σ * g⁻¹)
      (hHnorm.conj_mem σ hσ g) hIσ
  · -- The ramification of `L` outside `cs(S)` is explained by the ramification of `z`.
    intro B hBfin hKunram hnotS hram
    by_contra hcon
    exact (hmin B hBfin hKunram (fun τ σ hσ hσI => by
      by_contra hne
      exact hcon ⟨τ • B, ⟨τ, rfl⟩, σ, hσ, hσI, hne⟩)) hram

end Work.SSGRoute.ZDG
