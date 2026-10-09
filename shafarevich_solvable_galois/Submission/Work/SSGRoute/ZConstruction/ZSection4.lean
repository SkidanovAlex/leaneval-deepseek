import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.TransferReduction
import Submission.Work.SSGRoute.ZConstruction.LineAndZeroWitness
import Submission.Work.SSGRoute.ZConstruction.TransferLevel
import Submission.Work.SSGRoute.ZConstruction.ZDataBridge
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The §4 assembly at the level of the node's conclusion

Schmidt–Wingberg's §4 induction (`ZConstruction/AuxExistsGapInduction.lean`,
`ZConstruction/ZDataGlue.lean`) is phrased for the paper's **`z`-data** `Work.SSGRoute.HasZData`,
whose sixth clause asks for the *cyclicity of the local image* of the witness `z` at the junk places
where `z` ramifies.  The node's conclusion `Work.SSGRoute.ZConstruction.IsZConclusion` has a
**weaker** sixth clause (the transfer form `∃ V`), and the two are not equivalent clause by clause
(`ZConstruction/NOTE_session25.lean` §6).  The present file starts the §4 induction at the *node's*
level, i.e. with `IsZConclusion` as the goal, so that the criteria of
`ZConstruction/TransferLevel.lean` can be used inside the induction and the residual `CaseC` gate is
weakened to the data on which those criteria fail.

The central content is the **assembly of the two summands**, which at the `IsZConclusion` level is a
statement about the *sum* of two witnesses:

* the first five clauses are additive (`isZData5_add`), since each is a pointwise statement about the
  cochain (the cocycle clause uses `res k K = 1` on `G_K`);
* the sixth clause is supplied by the building block
  `Work.SSGRoute.exists_V_of_transfer_add_of_common_level`, which needs the two summands to vanish on
  a *common normal level* `G_M` (so that their transfers vanish there, the transfer being additive)
  together with the cyclicity of `decomp k B ⫽ (decomp k B ⊓ G_M)`.

This gives `isZConclusion_add_of_common_level`: `IsZConclusion` is closed under addition of two
witnesses with a common cyclic level.  Two further elementary pieces of the §4 induction are included:
the trivial solution for the zero datum (`isZConclusion_zero`) and the *peeling* step
(`isZConclusion_of_fixes_data`: a witness for `π ∘ y` is a witness for `y` when `π` fixes the datum
on the `cs(S)`-local groups).

## Main definitions and results

* `Work.SSGRoute.zAdd_of_isCocycleOn`
* `Work.SSGRoute.isZData5_add`
* `Work.SSGRoute.isZConclusion_add_of_common_level`
* `Work.SSGRoute.isZConclusion_zero`
* `Work.SSGRoute.isZConclusion_of_fixes_data`
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [Normal k K]
  [Fintype (K ≃ₐ[k] K)]
variable {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- **A `1`-cocycle on `G_K` is additive there.**  The action is through `res k K`, which is trivial on
`G_K`. -/
theorem zAdd_of_isCocycleOn {z : (Ω ≃ₐ[k] Ω) → E}
    (h : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z) :
    ∀ g ∈ K.fixingSubgroup, ∀ h' ∈ K.fixingSubgroup, z (g * h') = z g + z h' := by
  intro g hg h' hh
  rw [h g hg h' hh, (res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr hg, one_smul]

/-- **The five elementary conjuncts of the conclusion are additive in the witness and the datum.**
Every clause is a pointwise statement about the cochain (the cocycle clause becomes additivity on
`G_K` because the action is trivial there), so the sum of two witnesses satisfies the five clauses for
the sum of the two data. -/
theorem isZData5_add {S : Finset (ValuationSubring Ω)} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    {y₁ y₂ z₁ z₂ : (Ω ≃ₐ[k] Ω) → E}
    (h₁ : ZConstruction.IsZData5 (K := K) (Λ := Λ) (E := E) S sec y₁ z₁)
    (h₂ : ZConstruction.IsZData5 (K := K) (Λ := Λ) (E := E) S sec y₂ z₂) :
    ZConstruction.IsZData5 (K := K) (Λ := Λ) (E := E) S sec
      (fun σ => y₁ σ + y₂ σ) (fun σ => z₁ σ + z₂ σ) := by
  obtain ⟨hc₁, hl₁, ha₁, hi₁, hu₁⟩ := h₁
  obtain ⟨hc₂, hl₂, ha₂, hi₂, hu₂⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    show z₁ (g * h) + z₂ (g * h) = (z₁ g + z₂ g) + (res k K) g • (z₁ h + z₂ h)
    rw [hc₁ g hg h hh, hc₂ g hg h hh, smul_add]
    abel
  · obtain ⟨U₁, hU₁o, hU₁⟩ := hl₁
    obtain ⟨U₂, hU₂o, hU₂⟩ := hl₂
    refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
    · simpa using hU₁o.inter hU₂o
    · intro g hg u hu huK
      show z₁ (g * u) + z₂ (g * u) = z₁ g + z₂ g
      rw [hU₁ g hg u hu.1 huK, hU₂ g hg u hu.2 huK]
  · intro B hB hconj σ hσK hσd
    show z₁ σ + z₂ σ = y₁ σ + y₂ σ
    rw [ha₁ B hB hconj σ hσK hσd, ha₂ B hB hconj σ hσK hσd]
  · intro c hc hc2
    show z₁ c + z₂ c = (0 : E)
    rw [hi₁ c hc hc2, hi₂ c hc hc2, add_zero]
  · intro B hB hnot hsp σ hσK hσI
    show z₁ σ + z₂ σ = (0 : E)
    rw [hu₁ B hB hnot hsp σ hσK hσI, hu₂ B hB hnot hsp σ hσK hσI, add_zero]

/-- **The §4 assembly at the `IsZConclusion` level: `IsZConclusion` is closed under addition of two
witnesses with a common cyclic level.**

If `z₁` is a witness for the datum `y₁` and `z₂` for `y₂` (in the sense of the node's conclusion),
if both vanish on the fixing subgroup of a common **normal** level `M ⊇ K`, and if the image of the
decomposition group of every junk place in `Gal(M|k)` is cyclic, then `z₁ + z₂` is a witness for
`y₁ + y₂`.

The five elementary conjuncts are `isZData5_add`; the sixth is
`Work.SSGRoute.exists_V_of_transfer_add_of_common_level`, with `V = G_M`: the transfer of each summand
vanishes on `G_M` (`Work.SSGRoute.transfer_eq_zero_of_mem_level`), the transfer being additive in the
cochain, and the cyclicity is the hypothesis on `M`.  No confinement or vanishing hypothesis of the
paper's `HasZData`-level assembly is needed. -/
theorem isZConclusion_add_of_common_level {S : Finset (ValuationSubring Ω)}
    {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)} (hsec : ∀ s, SSGRoute.res k K (sec s) = s) (hKΛ : K ≤ Λ)
    {y₁ y₂ z₁ z₂ : (Ω ≃ₐ[k] Ω) → E}
    (h₁ : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y₁ z₁)
    (h₂ : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y₂ z₂)
    {M : IntermediateField k Ω} [FiniteDimensional k M] [Normal k M] (hKM : K ≤ M)
    (hz₁M : ∀ g ∈ M.fixingSubgroup, z₁ g = 0) (hz₂M : ∀ g ∈ M.fixingSubgroup, z₂ g = 0)
    (hcyc : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
        ∃ m : ℤ, δ⁻¹ * g ^ m ∈ M.fixingSubgroup) :
    ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec
      (fun σ => y₁ σ + y₂ σ) (fun σ => z₁ σ + z₂ σ) := by
  obtain ⟨hc₁, hl₁, ha₁, hi₁, hu₁, _hb₁⟩ := h₁
  obtain ⟨hc₂, hl₂, ha₂, hi₂, hu₂, _hb₂⟩ := h₂
  obtain ⟨hc, hl, ha, hi, hu⟩ :=
    isZData5_add (sec := sec) (h₁ := ⟨hc₁, hl₁, ha₁, hi₁, hu₁⟩)
      (h₂ := ⟨hc₂, hl₂, ha₂, hi₂, hu₂⟩)
  refine ⟨hc, hl, ha, hi, hu, ?_⟩
  intro B hB hnotconj hsplitΛ
  have hsplitK : SSGRoute.IsSplitIn k K B :=
    le_trans hsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
  exact exists_V_of_transfer_add_of_common_level (K := K) (M := M) (z₁ := z₁) (z₂ := z₂) hsec
    (zAdd_of_isCocycleOn hc₁) (zAdd_of_isCocycleOn hc₂) hKM hz₁M hz₂M B hB hsplitK
    (hcyc B hB hnotconj hsplitΛ)

/-- **The trivial solution.**  The zero cochain is a witness for the zero datum: the five clauses and
the sixth (with `V = ⊤`, every summand being `0`) are immediate. -/
theorem isZConclusion_zero (S : Finset (ValuationSubring Ω))
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec
      (0 : (Ω ≃ₐ[k] Ω) → E) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g _ h _
    simp
  · exact ⟨⊤, isOpen_univ, fun g _ u _ _ => by simp⟩
  · intro B _ _ σ _ _
    simp
  · intro c _ _
    simp
  · intro B _ _ _ σ _ _
    simp
  · intro B _ _ _
    exact ⟨⊤, isOpen_univ, (fun δ _ u _ => Subgroup.mem_top _),
      ⟨1, (SSGRoute.decomp k B).one_mem, fun δ _ => ⟨0, by simp⟩⟩,
      fun δ _ => by simp⟩

/-- **The peeling step at the `IsZConclusion` level.**  If an additive `π : E → E` fixes the datum
`y` pointwise on the `cs(S)`-local groups, then a witness for the projected datum `π ∘ y` is a witness
for `y`: of the six clauses only the agreement clause mentions the datum, and there `π (y σ) = y σ`. -/
theorem isZConclusion_of_fixes_data {S : Finset (ValuationSubring Ω)}
    {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)} {y : (Ω ≃ₐ[k] Ω) → E} {z : (Ω ≃ₐ[k] Ω) → E}
    (π : E →ₗ[ZMod p] E)
    (hfix : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → π (y σ) = y σ)
    (hz : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec
      (fun σ => π (y σ)) z) :
    ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y z := by
  obtain ⟨hc, hl, ha, hi, hu, hb⟩ := hz
  refine ⟨hc, hl, ?_, hi, hu, hb⟩
  intro B hB hconj σ hσK hσd
  rw [ha B hB hconj σ hσK hσd]
  show π (y σ) = y σ
  exact hfix B hB hconj σ hσK hσd

/-- **Naturality of the node's conclusion in the coefficients.**  An additive map `φ : E → E'` which
commutes with the `Gal(K|k)`-action (only the `s •`-equivariance is needed, not `𝔽_p`-linearity)
carries a witness for `y` to a witness for `φ ∘ y`.

This is the transport used by the §4 induction to move the two summands of a decomposition of the
coefficient module into the ambient module: the sixth clause is the only one using the action, and
there the summands transform termwise (`map_sum` plus `hφ`), while the other five clauses are pointwise
statements transported by `map_add`/`map_zero` or left alone. -/
theorem isZConclusion_map {E' : Type} [AddCommGroup E'] [Module (ZMod p) E']
    [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E']
    {S : Finset (ValuationSubring Ω)} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    {y z : (Ω ≃ₐ[k] Ω) → E} (φ : E →+ E')
    (hφ : ∀ (s : K ≃ₐ[k] K) (v : E), φ (s • v) = s • φ v)
    (hz : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y z) :
    ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E') S sec
      (fun σ => φ (y σ)) (fun σ => φ (z σ)) := by
  obtain ⟨hc, hl, ha, hi, hu, hb⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    show φ (z (g * h)) = φ (z g) + (res k K) g • φ (z h)
    rw [hc g hg h hh, map_add, hφ]
  · obtain ⟨U, hUo, hU⟩ := hl
    exact ⟨U, hUo, fun g hg u hu huK => by
      show φ (z (g * u)) = φ (z g)
      rw [hU g hg u hu huK]⟩
  · intro B hB hconj σ hσK hσd
    show φ (z σ) = φ (y σ)
    rw [ha B hB hconj σ hσK hσd]
  · intro c hc' hc2
    show φ (z c) = (0 : E')
    rw [hi c hc' hc2, map_zero]
  · intro B hB hnot hsp σ hσK hσI
    show φ (z σ) = (0 : E')
    rw [hu B hB hnot hsp σ hσK hσI, map_zero]
  · intro B hB hnotconj hsplitΛ
    obtain ⟨V, hVo, hVn, hVc, hVv⟩ := hb B hB hnotconj hsplitΛ
    refine ⟨V, hVo, hVn, hVc, fun δ hδ => ?_⟩
    have hvv : (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = (0 : E) := hVv δ hδ
    have h2 : (∑ s : K ≃ₐ[k] K, s • φ (z ((sec s)⁻¹ * δ * sec s)))
        = ∑ s : K ≃ₐ[k] K, φ (s • z ((sec s)⁻¹ * δ * sec s)) :=
      Finset.sum_congr rfl fun s _ => (hφ s _).symm
    rw [h2, ← map_sum, hvv, map_zero]

include p in
/-- **The §4 assembly with the *unramified* clause-6 route.**  If in addition both summands vanish on
the inertia of every conjugate of every junk place, then the sum's transfer kills that inertia, and the
sixth conjunct for the sum follows from the lane's
`Work.SSGRoute.transfer_vanishes_of_unramified` — no level and no cyclicity hypothesis. -/
theorem isZConclusion_add_of_unramified {S : Finset (ValuationSubring Ω)}
    {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)} (hsec : ∀ s, SSGRoute.res k K (sec s) = s) (hKΛ : K ≤ Λ)
    {y₁ y₂ z₁ z₂ : (Ω ≃ₐ[k] Ω) → E}
    (h₁ : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y₁ z₁)
    (h₂ : ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y₂ z₂)
    (hunram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ∀ (s : K ≃ₐ[k] K) (σ : Ω ≃ₐ[k] Ω), σ ∈ K.fixingSubgroup →
        SSGRoute.IsInertia k ((sec s)⁻¹ • B) σ → z₁ σ + z₂ σ = 0) :
    ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec
      (fun σ => y₁ σ + y₂ σ) (fun σ => z₁ σ + z₂ σ) := by
  obtain ⟨hc₁, hl₁, ha₁, hi₁, hu₁, _hb₁⟩ := h₁
  obtain ⟨hc₂, hl₂, ha₂, hi₂, hu₂, _hb₂⟩ := h₂
  obtain ⟨hc, hl, ha, hi, hu⟩ :=
    isZData5_add (sec := sec) (h₁ := ⟨hc₁, hl₁, ha₁, hi₁, hu₁⟩)
      (h₂ := ⟨hc₂, hl₂, ha₂, hi₂, hu₂⟩)
  refine ⟨hc, hl, ha, hi, hu, ?_⟩
  intro B hB hnotconj hsplitΛ
  have hsplitK : SSGRoute.IsSplitIn k K B :=
    le_trans hsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
  exact transfer_vanishes_of_unramified p k Ω K (E := E) (fun σ => z₁ σ + z₂ σ)
    (zAdd_of_isCocycleOn hc) hl sec hsec B hB hsplitK
    (fun s σ hσ hI => hunram B hB hnotconj hsplitΛ s σ hσ hI)

/-- **The paper's `z`-data imply the node's conclusion, per datum.**

This exposes the lane's bridge `Work.SSGRoute.shafarevich_z_construction_of_zData`
(`ZDataBridge.lean`, sorry-free) — which converts a witness satisfying the *paper's* `z`-data
conditions (`Work.SSGRoute.HasZData`: the five elementary clauses together with the local-cyclicity
clause, with the sharpened trigger on *ramification*) into a witness for the node's conclusion — as a
rung between the two levels of the §4 induction.

With it, the one-dimensional gate `Work.SSGRoute.MupGate` (whose output is a `HasZData` witness) is
usable as the base case of the `IsZConclusion`-level induction of this file, and every `HasZData`-level
result of the lane feeds into the `IsZConclusion`-level assembly
`Work.SSGRoute.isZConclusion_add_of_common_level`.  The converse (upgrading a witness of the node's
conclusion to the paper's `z`-data) is *not* available and cannot be: the two sixth clauses are not
equivalent, see `ZConstruction/NOTE_session25.lean` §6. -/
theorem exists_isZConclusion_of_exists_hasZData [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hKΛ : K ≤ Λ) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    {y : (Ω ≃ₐ[k] Ω) → E}
    (h : ∃ z : (Ω ≃ₐ[k] Ω) → E, Work.SSGRoute.HasZData (K := K) (Λ := Λ) (E := E) S y z) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y z :=
  Work.SSGRoute.shafarevich_z_construction_of_zData (K := K) (Λ := Λ) hKΛ S y sec hsec h

/-- **The Case B (peeling) step of the §4 induction at the node's level.**

If the induction hypothesis is available for every datum of `(Λ,S)` whose values lie in the span of
the `cs(S)`-local data of `y` (`Work.SSGRoute.csData`), then a witness for `y` itself follows: project
`y` onto that span along a complement and use the peeling step
`Work.SSGRoute.isZConclusion_of_fixes_data`.

This is the *image-dimension* form of the induction hypothesis prescribed by
`ZConstruction/NOTE_session25.lean` §7b: it stays inside the ambient module `E`, so no
`Gal(K|k)`-equivariance of the projection (which would fail for a non-stable span) is needed — the
sixth clause of `IsZConclusion` does not mention the datum at all. -/
theorem isZConclusion_peel_csData [FiniteDimensional k Λ] [IsGalois k Λ] [Finite E]
    {S : Finset (ValuationSubring Ω)} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    {y : (Ω ≃ₐ[k] Ω) → E} (hy : ZHyp (p := p) K Λ S y)
    (hIH : ∀ (y' : (Ω ≃ₐ[k] Ω) → E), ZHyp (p := p) K Λ S y' →
      (∀ σ : Ω ≃ₐ[k] Ω, y' σ ∈ csData (p := p) K S y) →
      ∃ z : (Ω ≃ₐ[k] Ω) → E,
        ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y' z) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      ZConstruction.IsZConclusion (K := K) (Λ := Λ) (E := E) S sec y z := by
  classical
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  obtain ⟨C, hc⟩ := Submodule.exists_isCompl (csData (p := p) K S y)
  let π := (Submodule.subtype (csData (p := p) K S y)).comp
    ((csData (p := p) K S y).projectionOnto C hc)
  have hy' : ZHyp (p := p) K Λ S (fun σ => π (y σ)) :=
    ZHyp.mapAdd (f := π.toAddMonoidHom) hy
  have hmem : ∀ σ : Ω ≃ₐ[k] Ω, π (y σ) ∈ csData (p := p) K S y :=
    fun σ => (Submodule.projectionOnto (csData (p := p) K S y) C hc (y σ)).2
  obtain ⟨z, hz⟩ := hIH _ hy' hmem
  refine ⟨z, isZConclusion_of_fixes_data (p := p) (K := K) (Λ := Λ) (E := E) π ?_ hz⟩
  intro B hB hconj σ hσK hσd
  show π (y σ) = y σ
  rw [show π (y σ) = ((csData (p := p) K S y).projectionOnto C hc (y σ) : E) from rfl,
    Submodule.projectionOnto_apply_of_mem_left hc
      (mem_csData (p := p) (K := K) hB hconj hσK hσd)]

end Work.SSGRoute
