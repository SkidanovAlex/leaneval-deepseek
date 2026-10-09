import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
import Submission.Work.SSGRoute.ZConstruction.LevelExistence
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Work.SSGRoute.z_data_mup_level
import Submission.Work.SSGRoute.z_data_two_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induction on `dim_{𝔽_p} E` of Schmidt--Wingberg §4: infrastructure

`Work.SSGRoute.z_data_general` (the `z`-data of the auxiliary class, module
`ZConstruction/ZDataGeneral.lean`) is the general-coefficient case of Schmidt--Wingberg's
Theorem 13; the one-dimensional case (`finrank ≤ 1`) is the file
`Submission/Work/SSGRoute/z_data_mup_level.lean` (odd `p`) and its `p = 2` sibling.  The present file
assembles the *general* case from the one-dimensional one, exactly as the paper does (pp. 18--19):
with `E = E₀ ⊕ L` (`L` a line), one applies the induction hypothesis to the `E₀`-component and the
one-dimensional case to the `L`-component and adds the two classes; the extra two clauses of the
one-dimensional input -- the **confinement** of its ramification at good places to `M`-split places
(`M` a level containing the field cut out by the other summand) and its **vanishing** on the local
groups of a prescribed set `T''` of good places (the ramification of the other summand) -- are
exactly the hypotheses `hconf`/`hkill` of the already-proved assembly lemma
`Work.SSGRoute.hasZData_of_component_data`.

This file contains the parts of that induction which are independent of the arithmetic input:

* `Work.SSGRoute.ZHyp` -- the hypotheses of the target theorem on the datum `y`, packaged, with the
  transport `Work.SSGRoute.ZHyp.comp` along a `ZMod p`-linear map (the two components `y₀ = (1-π)∘y`
  and `y₁ = π∘y` of a splitting satisfy the same hypotheses);
* `Work.SSGRoute.Conf` -- the confinement clause at a level `M`, with monotonicity in the level;
* `Work.SSGRoute.exists_rankOne_projection` -- the linear-algebra input of the induction: for
  `finrank (ZMod p) E ≥ 2` there is a line `L ⊆ E` with a complement;
* `Work.SSGRoute.exists_fixingField_vanishing_finite` -- the *level of a cochain* in the form used by
  the induction: a finite-dimensional **Galois** intermediate field `L ⊇ K` on whose Galois group a
  given additive, locally constant cochain vanishes;
* `Work.SSGRoute.exists_galois_level_sup` -- the level `M' = M ⊔ L₁ ⊔ L₀` of the induction step
  (finite-dimensional and Galois over `k`).

The remaining step (the strong induction on `Module.finrank (ZMod p) E`, whose statement is
recorded in the docstring of `z_data_general_of_level` below) is a pure assembly: with `L₁` the level
of `y₁ = π∘y` and `L₀` the level of the induction-hypothesis witness `z₀`, one takes
`M' := M ⊔ L₁ ⊔ L₀`, applies the induction hypothesis to `y₀ := (1-π)∘y` at level `M'`, applies the
one-dimensional input to `y₁` at level `M'` with `T''` the (representatives of the) good places at
which `z₀` ramifies, and concludes with `hasZData_of_component_data`.  The two consistency
hypotheses of the input are then met as follows:
* `hyT''` (`y₁` vanishes on `decomp k Q ⊓ G_K` for `Q` conjugate to a place of `T''`): the
  confinement of `z₀` at level `M' ⊇ L₁` makes every such `Q` split completely in `M'`, hence in
  `L₁`, hence `y₁` vanishes there (by `exists_fixingField_vanishing_finite` applied to `y₁` and
  `kills_decomp_of_split_of_vanishes`);
* `hyunr` (`y₁` unramified outside `cs(S) ∪ Ram(M'|k) ∪ T''`): the input is applied at level `M'`,
  and every place at which `y₁` is ramified is ramified in its level `L₁ ⊆ M'`, hence in `M'`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace Work.SSGRoute

open _root_.SSGRoute

open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- The hypotheses of `Work.SSGRoute.shafarevich_z_construction` on the datum `y`, packaged.
(Only the clauses that are *conditions on `y`* are collected here; the ambient data `p, k, Ω, K, Λ,
S` are parameters.) -/
structure ZHyp (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) {E : Type}
    [AddCommGroup E] (y : (Ω ≃ₐ[k] Ω) → E) : Prop where
  add : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h
  locconst : SSGRoute.IsLocConstOn K.fixingSubgroup y
  hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0
  hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0
  hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
    (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0
  hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0

/-- The **confinement clause** at level `M`: every *good* place at which `z` is ramified has all its
conjugates split completely in `M`.  This is the shape consumed by
`Work.SSGRoute.hasZData_add_of_split_confined` (`hconf`). -/
def Conf (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (M : IntermediateField k Ω) {E : Type} [AddCommGroup E]
    (z : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
    (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
    ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q → SSGRoute.IsSplitIn k M Q

/-- The confinement clause is monotone in the level. -/
theorem Conf.mono {K Λ M M' : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] {z : (Ω ≃ₐ[k] Ω) → E} (hle : M ≤ M')
    (h : Conf K Λ S M' z) : Conf K Λ S M z :=
  fun B hB hram Q hQ =>
    le_trans (h B hB hram Q hQ) (IntermediateField.fixingSubgroup_le hle)

/-- **Transport of the hypotheses along a `ZMod p`-linear map.**  Each clause of `ZHyp` is either an
additivity statement (preserved by a linear map) or of the form "`y σ = 0`" at specific `σ`
(preserved because a linear map sends `0` to `0`). -/
theorem ZHyp.comp {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)} {E : Type}
    [AddCommGroup E] [Module (ZMod p) E] {y : (Ω ≃ₐ[k] Ω) → E} (h : ZHyp (p := p) K Λ S y)
    (π : E →ₗ[ZMod p] E) : ZHyp (p := p) K Λ S fun σ => π (y σ) where
  add g hg h' hh := by rw [h.add g hg h' hh, map_add]
  locconst := by
    obtain ⟨U, hUo, hU⟩ := h.locconst
    exact ⟨U, hUo, fun g hg u hu huK => by
      show π (y (g * u)) = π (y g)
      rw [hU g hg u hu huK]⟩
  hyS B hB hnot hsp σ hσ hσI := by rw [h.hyS B hB hnot hsp σ hσ hσI, map_zero]
  hyT B hB hconj σ hσ hσI := by rw [h.hyT B hB hconj σ hσ hσI, map_zero]
  hy0 B hB hconj hbad σ hσ hσd := by rw [h.hy0 B hB hconj hbad σ hσ hσd, map_zero]
  hyinf c hc hc2 := by rw [h.hyinf c hc hc2, map_zero]

/-- **The linear algebra of the induction step.**  A finite module over `ZMod p` of `𝔽_p`-dimension
at least `2` has a line `L` with a complement `E₀`; the two summands of the paper's induction are the
`E₀`-component and the `L`-component of `E`. -/
theorem exists_rankOne_projection (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (h : 2 ≤ Module.finrank (ZMod p) E) :
    ∃ (L E₀ : Submodule (ZMod p) E) (_ : IsCompl L E₀),
      Module.finrank (ZMod p) L = 1 ∧ Module.finrank (ZMod p) E₀ < Module.finrank (ZMod p) E := by
  haveI : Nontrivial E := by
    have hpos : 0 < Module.finrank (ZMod p) E := by omega
    exact Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨E₀, hc⟩ := Submodule.exists_isCompl (ZMod p ∙ v : Submodule (ZMod p) E)
  have hL : Module.finrank (ZMod p) (ZMod p ∙ v) = 1 := finrank_span_singleton hv
  have hadd := Submodule.finrank_add_eq_of_isCompl hc
  exact ⟨ZMod p ∙ v, E₀, hc, hL, by omega⟩

/-- **The level of a cochain.**  An additive cochain on `G_K = K.fixingSubgroup` which is locally
constant on `G_K` vanishes on the Galois group of a finite-dimensional **Galois** intermediate field
`L` (the Galois closure over `k` of the field produced by `exists_fixingField_vanishing`, hence
finite-dimensional and Galois over `k`, as the level parameter `M` of the one-dimensional input must
be). -/
theorem exists_fixingField_vanishing_finite {K : IntermediateField k Ω} [FiniteDimensional k K]
    [Normal k K] {E : Type} [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ IsGalois k L ∧
      ∀ g ∈ L.fixingSubgroup, z g = 0 := by
  obtain ⟨U, hUopen, _hUnorm, hUz⟩ := exists_normal_open_of_z_eq_zero (K := K) z hzadd hzloc
  have hGKopen : IsOpen ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  obtain ⟨M, hMfin, hMnorm, hMle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := k) (L := Ω)
      (U ⊓ K.fixingSubgroup) (hUopen.inter hGKopen)
  haveI : FiniteDimensional k M := hMfin
  haveI : Normal k M := hMnorm
  haveI : IsGalois k M := by
    rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  exact ⟨M, hMfin, ‹IsGalois k M›, fun g hg => hUz g (hMle hg).1 (hMle hg).2⟩

/-! ## The compositum level of the induction step

The induction step also uses that the compositum `M ⊔ L₁ ⊔ L₀` of the running level `M` with the two
levels `L₁` (`y₁`) and `L₀` (`z₀`) is finite-dimensional and Galois over `k`.  This is available from
the instances `IntermediateField.finiteDimensional_sup` and
`IsGalois k ↑(L₁ ⊔ L₂)` (`FieldTheory/Galois/GaloisClosure.lean`); elaborating it needs a raised
`synthInstance.maxHeartbeats`, which is why it is recorded here rather than proved inline. -/


/-- **The `z`-data is monotone in the level `Λ`.**  If `z` has the `z`-data for the pair
`(Λ', S)` with `Λ ≤ Λ'`, then it has the `z`-data for `(Λ, S)`.

This is the *level change* that Schmidt--Wingberg's induction uses in the direction opposite to
`Λ ↦ Λ·L`: the one-dimensional input is applied at the *enlarged* pair
`(Λ' = Λ·L, S)`, where `L` is the level of the first summand, and the answer for `(Λ, S)` is
recovered.  The verification is clause-by-clause:

* clause 5 for `Λ` (unramified at the places outside `cs(S)` that are not split in `Λ`) follows from
  clause 5 for `Λ'`, because a place that is not split in `Λ'` is not split in `Λ` (`Λ ≤ Λ'`);
* clause 6 for `Λ` is checked at a good place `B` of `Λ`.  If `B` splits in `Λ'`, then `B` is a good
  place of `Λ'` and clause 6 for `Λ'` applies; if `B` does not split in `Λ'`, then clause 5 for `Λ'`
  makes `z` unramified at `B`, so the trigger of clause 6 (ramification of `z` at `B`) is false and
  the clause is vacuous. -/
theorem hasZData_of_le_level {K Λ Λ' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [AddCommGroup E] {y z : (Ω ≃ₐ[k] Ω) → E}
    (hle : Λ ≤ Λ') (h : HasZData K Λ' S y z) : HasZData K Λ S y z := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := h
  refine ⟨ha, hl, hg, hi, ?_, ?_⟩
  · intro B hB hnot hns σ hσ hσI
    exact hs B hB hnot (fun hsp => hns (le_trans hsp (IntermediateField.fixingSubgroup_le hle)))
      σ hσ hσI
  · intro B hB hnot hsp htrig
    by_cases hsp' : SSGRoute.IsSplitIn k Λ' B
    · exact hb B hB hnot hsp' htrig
    · obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
      exact absurd (hs B hB hnot (fun hsp => hsp' hsp) σ hσK hσI) hσne

end Work.SSGRoute
