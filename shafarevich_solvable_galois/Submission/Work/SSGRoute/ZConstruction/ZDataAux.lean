import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.ZDataLevelStep
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces
import Submission.Work.SSGRoute.line_complement_decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The spanning gate of Schmidt--Wingberg §4 from the *auxiliary class* (p. 18)

`Work.SSGRoute.z_data_general_of_gates` (`ZConstruction/ZDataReduction.lean`) reduces the `z`-data of
Schmidt--Wingberg's Theorem 13 to the one-dimensional gate `Work.SSGRoute.MupGate` and the spanning
gate `Work.SSGRoute.SpanningGate` (local data of `y` spanning `E`, in dimension `≥ 2`).

This file proves the paper's **induction step** for the spanning gate, i.e. the step "pp. 18--19" of
Schmidt--Wingberg: with `E = E₀ ⊕ L` (`L` a line, `Work.SSGRoute.line_complement_decomposition`),

* the induction hypothesis at the hyperplane `E₀` gives `z₀` with the `z`-data for `y₀ = π₀ ∘ y` at
  `(Λ, S)`;
* `z₀` vanishes above a finite Galois level `N ⊇ Λ` (`Work.SSGRoute.exists_level_vanishing_finite`);
* enlarging `S` to `S' := S ∪ Ram(N|k)` (`Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces`)
  and applying the **auxiliary-class obligation** `Work.SSGRoute.AuxExists` to the line component
  `y₁ = π₁ ∘ y` produces the auxiliary class `yAux` with the same local data as `y₁` on `cs(S)` and
  *vanishing* on `cs(S') ∖ cs(S)`;
* the one-dimensional gate `Work.SSGRoute.MupGate` applied to `yAux` at `(N, S')` gives `z₁`;
* the assembly `Work.SSGRoute.hasZData_sum_of_level_data` concludes `HasZData K Λ S y (z₀ + z₁)`.

**What this isolates.**  `Work.SSGRoute.AuxExists` is the *only* new obligation: it is the
formulation, in the `HasZData` vocabulary of this node, of the paper's class `ỹ` of p. 18 --- the
realisation, at the enlarged pair `(N, S')`, of the local data of the line component of the datum,
with the prescribed vanishing at the new places.  Its proof is the Tate--Poitou degree-one
realisation together with the diagram chase at the bottom of p. 18 (the orthogonality of the datum of
`ν` against the dual Selmer group).  Everything else --- the level, the enlarged place set, the
splitting, the transports and the assembly --- is proved here.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The level of a cochain, in the action-free form used by the induction.**  An additive, locally
constant cochain on `G_K` vanishes on the Galois group of a finite dimensional Galois intermediate
field `N ⊇ K`.  (This is `Work.SSGRoute.exists_fixingField_vanishing_finite` with the (unused)
coefficient action supplied by the trivial action, and with the level enlarged so that it contains
`K`.) -/
theorem exists_level_vanishing_finite {K : IntermediateField k Ω} [FiniteDimensional k K]
    [Normal k K] {E : Type} [AddCommGroup E] {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ N : IntermediateField k Ω, K ≤ N ∧ FiniteDimensional k N ∧ IsGalois k N ∧
      ∀ g ∈ N.fixingSubgroup, z g = 0 := by
  letI : DistribMulAction (K ≃ₐ[k] K) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  obtain ⟨F, hFfin, hFgal, hFv⟩ := exists_fixingField_vanishing_finite (K := K) hzadd hzloc
  haveI : FiniteDimensional k F := hFfin
  haveI : IsGalois k F := hFgal
  refine ⟨F ⊔ K, le_sup_right, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · intro g hg
    exact hFv g (IntermediateField.fixingSubgroup_le le_sup_left hg)

/-- **The auxiliary-class obligation of Schmidt--Wingberg §4 (p. 18).**  For every finite Galois
level `N ⊇ Λ` and every enlargement `S' ⊇ S` of the place set containing the places ramified in
`N` (up to conjugacy), every one-dimensional datum `y₁` at `(Λ,S)` has an *auxiliary class* `yAux`
at `(N,S')` with the same local data as `y₁` on `cs(S)` and vanishing on the local groups of the
places of `cs(S') ∖ cs(S)`.

This is exactly the class `ỹ` of the paper's p. 18: its construction is the Poitou--Tate degree-one
realisation of the prescribed local data (the datum of the line component `y₁`), together with the
diagram chase showing that the datum is orthogonal to the dual Selmer group.  It is the single
arithmetic obligation left by `Work.SSGRoute.z_data_general_of_mup_and_aux`. -/
def AuxExists (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) : Prop :=
  ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
    ∀ (S' : Finset (ValuationSubring Ω)),
    (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ S', SSGRoute.IsConjPlace k A' B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
      ∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
    ∀ (L : Type) [AddCommGroup L] [Module (ZMod p) L] [Finite L],
      Module.finrank (ZMod p) L = 1 →
    ∀ (y₁ : (Ω ≃ₐ[k] Ω) → L), ZHyp (p := p) K Λ S y₁ →
    ∃ yAux : (Ω ≃ₐ[k] Ω) → L,
      ZHyp (p := p) K N S' yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0)

/-- **The spanning step of the induction of §4.**  Given the induction hypothesis at all smaller
coefficient modules, the one-dimensional gate and the auxiliary-class obligation, the `z`-data holds
for a datum whose local data spans the coefficient module of dimension `≥ 2`. -/
theorem z_data_of_spanning_of_aux {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (hAmb : ZAmbient (p := p) K Λ S) (hmup : MupGate (p := p) K)
    (haux : AuxExists (p := p) K Λ S)
    (hIH : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E'] [Finite E'],
      Module.finrank (ZMod p) E' < Module.finrank (ZMod p) E →
      ∀ y' : (Ω ≃ₐ[k] Ω) → E', ZHyp (p := p) K Λ S y' →
      ∃ z' : (Ω ≃ₐ[k] Ω) → E', HasZData K Λ S y' z')
    (y : (Ω ≃ₐ[k] Ω) → E) (hy : ZHyp (p := p) K Λ S y)
    (hspan : csData (p := p) K S y = ⊤)
    (hdim : 2 ≤ Module.finrank (ZMod p) E) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  classical
  -- 1. the splitting `E = L ⊕ E₀` and the line component `y₁`
  obtain ⟨Lsub, E₀, _hc, hL1, hE₀lt, π₀, π₁, hsum, _hπ₀, _hπ₁⟩ :=
    line_complement_decomposition p E hdim
  set y₀ : (Ω ≃ₐ[k] Ω) → ↥E₀ := fun σ => π₀ (y σ) with hy₀
  set y₁ : (Ω ≃ₐ[k] Ω) → ↥Lsub := fun σ => π₁ (y σ) with hy₁
  have hy₀hyp : ZHyp (p := p) K Λ S y₀ := ZHyp.mapAdd (f := π₀.toAddMonoidHom) hy
  have hy₁hyp : ZHyp (p := p) K Λ S y₁ := ZHyp.mapAdd (f := π₁.toAddMonoidHom) hy
  -- 2. the induction hypothesis at the hyperplane `E₀`
  obtain ⟨z₀', hz₀'⟩ := hIH ↥E₀ hE₀lt y₀ hy₀hyp
  -- 3. transport `z₀'` to `E` and take its level
  have hz₀E : HasZData K Λ S (fun σ => (π₀ (y σ) : E)) (fun σ => (z₀' σ : E)) :=
    hasZData_map (A := ↥E₀) (B := E) (f := (Submodule.subtype E₀).toAddMonoidHom)
      (fun _ _ h => Subtype.ext h) hz₀'
  set z₀ : (Ω ≃ₐ[k] Ω) → E := fun σ => (z₀' σ : E) with hz₀
  obtain ⟨N₀, hKN₀, hN₀fin, hN₀gal, hN₀v⟩ :=
    exists_level_vanishing_finite (K := K) hz₀E.1 hz₀E.2.1
  haveI : FiniteDimensional k N₀ := hN₀fin
  haveI : IsGalois k N₀ := hN₀gal
  haveI : FiniteDimensional k ↥(N₀ ⊔ Λ) := IntermediateField.finiteDimensional_sup N₀ Λ
  haveI : IsGalois k ↥(N₀ ⊔ Λ) := inferInstance
  have hΛN : Λ ≤ N₀ ⊔ Λ := le_sup_right
  have hNv : ∀ g ∈ (N₀ ⊔ Λ).fixingSubgroup, z₀ g = 0 :=
    fun g hg => hN₀v g (IntermediateField.fixingSubgroup_le le_sup_left hg)
  -- 4. the enlarged place set
  obtain ⟨S', hS'fin, hS'disj, hS'sub, hS'ram⟩ :=
    ZConstruction.exists_finset_ramifiedPlaces p (Fact.out : p.Prime) k Ω (N₀ ⊔ Λ) S
      hAmb.hSfin hAmb.hSdisj
  -- 5. the auxiliary class at `(N,S')`, and the one-dimensional gate for it
  obtain ⟨yAux, hyAuxHyp, hyAuxAgree, hyAuxVanish⟩ :=
    haux (N₀ ⊔ Λ) hΛN S' hS'fin hS'disj hS'sub (fun B hB hram => hS'ram B hB (Or.inl hram))
      ↥Lsub hL1 y₁ hy₁hyp
  have hAmbN : ZAmbient (p := p) K (N₀ ⊔ Λ) S' :=
    { hKΛ := le_trans hAmb.hKΛ hΛN, ζ := hAmb.ζ, hζ := hAmb.hζ, hζK := hAmb.hζK,
      hSfin := hS'fin, hSdisj := hS'disj,
      hSram := fun B hB hram => hS'ram B hB hram }
  obtain ⟨z₁', hz₁'⟩ := hmup (N₀ ⊔ Λ) S' hAmbN ↥Lsub hL1.le yAux hyAuxHyp
  have hz₁E : HasZData K (N₀ ⊔ Λ) S' (fun σ => (yAux σ : E)) (fun σ => (z₁' σ : E)) :=
    hasZData_map (A := ↥Lsub) (B := E) (f := (Submodule.subtype Lsub).toAddMonoidHom)
      (fun _ _ h => Subtype.ext h) hz₁'
  -- 6. the level `N` is normal, and the assembly
  have hNnorm : ((N₀ ⊔ Λ).fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois (N₀ ⊔ Λ)
  have hmain : HasZData K Λ S (fun σ => (π₀ (y σ) : E) + (π₁ (y σ) : E))
      (z₀ + fun σ => (z₁' σ : E)) :=
    hasZData_sum_of_level_data (K := K) (Λ := Λ) (N := N₀ ⊔ Λ) (S := S) (S' := S')
      (y := fun σ => (π₀ (y σ) : E) + (π₁ (y σ) : E))
      (y₀ := fun σ => (π₀ (y σ) : E)) (y₁ := fun σ => (π₁ (y σ) : E))
      (yAux := fun σ => (yAux σ : E)) (z₀ := z₀) (z₁ := fun σ => (z₁' σ : E))
      hNnorm hΛN
      (fun B hB => hS'sub B hB)
      (fun B hB hram => hS'ram B hB (Or.inl hram))
      (fun σ => rfl)
      hz₀E
      (fun g hg => hNv g hg)
      hz₁E
      (fun B hB hconj σ hσ => congrArg Subtype.val (hyAuxAgree B hB hconj σ hσ))
      (fun B hB hnot hS' σ hσ => congrArg Subtype.val (hyAuxVanish B hB hnot hS' σ hσ))
  exact ⟨z₀ + fun σ => (z₁' σ : E),
    hasZData_congr (fun σ => hsum (y σ)) hmain⟩

/-- **The full `z`-data from the one-dimensional gate and the auxiliary-class obligation.**  Strong
induction on `finrank (ZMod p) E`: dimension `≤ 1` is `MupGate`, the spanning case in dimension
`≥ 2` is `z_data_of_spanning_of_aux`, and the remaining (non-spanning) cases are the peeling step
`Work.SSGRoute.hasZData_of_fixes_data`. -/
theorem z_data_general_of_mup_and_aux {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)} (hAmb : ZAmbient (p := p) K Λ S)
    (hmup : MupGate (p := p) K) (haux : AuxExists (p := p) K Λ S) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
      (y : (Ω ≃ₐ[k] Ω) → E), ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  have key : ∀ (m : ℕ), ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E],
      Module.finrank (ZMod p) E = m → ∀ (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro E _instE _instM _instF hfin y hy
      by_cases hdim : Module.finrank (ZMod p) E ≤ 1
      · exact hmup Λ S hAmb E hdim y hy
      · push_neg at hdim
        by_cases hsp : csData (p := p) K S y = ⊤
        · refine z_data_of_spanning_of_aux hAmb hmup haux ?_ y hy hsp hdim
          intro E' _ _ _ hlt y' hy'
          exact ih (Module.finrank (ZMod p) E') (by rw [← hfin]; exact hlt) E' rfl y' hy'
        · haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
          obtain ⟨C, hc⟩ := Submodule.exists_isCompl (csData (p := p) K S y)
          have hlt : Module.finrank (ZMod p) ↥(csData (p := p) K S y) <
              Module.finrank (ZMod p) E := Submodule.finrank_lt hsp
          have hltm : Module.finrank (ZMod p) ↥(csData (p := p) K S y) < m := by
            rw [← hfin]; exact hlt
          have hy' : ZHyp (p := p) K Λ S
              (fun σ => (csData (p := p) K S y).projectionOnto C hc (y σ)) :=
            ZHyp.mapAdd (f := ((csData (p := p) K S y).projectionOnto C hc).toAddMonoidHom) hy
          obtain ⟨z', hz'⟩ := ih _ hltm ↥(csData (p := p) K S y) rfl _ hy'
          have hmap := hasZData_map (A := ↥(csData (p := p) K S y)) (B := E)
            (f := (Submodule.subtype (csData (p := p) K S y)).toAddMonoidHom)
            (fun _ _ h => Subtype.ext h) hz'
          refine ⟨fun σ => (z' σ : E), hasZData_of_fixes_data
            (π := (Submodule.subtype (csData (p := p) K S y)).comp
              ((csData (p := p) K S y).projectionOnto C hc)) ?_ hmap⟩
          intro B hB hconj σ hσK hσd
          have hmem : y σ ∈ csData (p := p) K S y := mem_csData (p := p) (K := K) hB hconj hσK hσd
          show ((Submodule.subtype (csData (p := p) K S y)).comp
            ((csData (p := p) K S y).projectionOnto C hc)) (y σ) = y σ
          rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left _ hmem]
          rfl
  intro E _instE _instM _instF y hy
  exact key (Module.finrank (ZMod p) E) E rfl y hy

/-- **The spanning gate from the one-dimensional gate and the auxiliary-class obligation.** -/
theorem spanningGate_of_mup_and_aux {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (hmup : MupGate (p := p) K)
    (haux : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), AuxExists (p := p) K Λ S) :
    SpanningGate (p := p) K := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF _hdim y hy _
  exact z_data_general_of_mup_and_aux hAmb hmup (haux Λ S) E y hy

/-- **The auxiliary-class obligation in the *weakened* form.**  Same prescriptions as
`Work.SSGRoute.AuxExists`, but the composite `yAux` is required to satisfy only four of the six
clauses of `ZHyp` at the enlarged pair `(N,S')`: additivity, local constancy, the unramifiedness
outside `cs(S')` at the places not split in `N`, and the vanishing on the involutions.  The two
remaining clauses (`hyT` and `hy0` at `(N,S')`) are *consequences* of the two prescriptions:
* at a place conjugate into `S'` but not into `S`, the prescribed vanishing gives them;
* at a place conjugate into `S`, the agreement with `y₁` and the corresponding clause of `ZHyp` of
  the datum `y₁` at `(Λ,S)` give them.
This is the form in which a realisation of the local data (a class with prescribed local components,
ramified only where allowed) delivers the obligation. -/
def AuxExistsWeakened (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) : Prop :=
  ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
    ∀ (S' : Finset (ValuationSubring Ω)),
    (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ S', SSGRoute.IsConjPlace k A' B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
      ∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
    ∀ (L : Type) [AddCommGroup L] [Module (ZMod p) L] [Finite L],
      Module.finrank (ZMod p) L = 1 →
    ∀ (y₁ : (Ω ≃ₐ[k] Ω) → L), ZHyp (p := p) K Λ S y₁ →
    ∃ yAux : (Ω ≃ₐ[k] Ω) → L,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yAux (g * h) = yAux g + yAux h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → yAux c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0)

/-- **The weakened auxiliary-class obligation implies the obligation.** -/
theorem auxExists_of_weakened {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    (h : AuxExistsWeakened (p := p) K Λ S) : AuxExists (p := p) K Λ S := by
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub hS'ram L _instLf _instLm _instLfin hL y₁ hy₁
  obtain ⟨yAux, hadd, hloc, hyS, hinf, hagree, hvanish⟩ :=
    h N hΛN S' hS'fin hS'disj hS'sub hS'ram L hL y₁ hy₁
  have hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0 := by
    intro B hB hconj σ hσK hσI
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
      exact hy₁.hyT B hB hconjS σ hσK hσI
    · rw [hvanish B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
  have hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → yAux σ = 0 := by
    intro B hB hconj hbad σ hσK hσd
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
      exact hy₁.hy0 B hB hconjS hbad σ hσK hσd
    · rw [hvanish B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
  exact ⟨yAux, { add := hadd, locconst := hloc, hyS := hyS, hyT := hyT, hy0 := hy0, hyinf := hinf },
    hagree, hvanish⟩

end Work.SSGRoute
