import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.stage_local_shrinking_cohomological
import Submission.Work.SSGRoute.exists_localLift_outside_T1
import Submission.Work.SSGRoute.stage_global_lifting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Steps 1–2 of the proof of Theorem 15 (SW §5)

Given Scholz solutions at τ at every level, produce at level n a Scholz solution φ_n = (flowGroupMap Φ) ∘ φ_m
that lifts to τ+1 and whose local extensions split over T¹ (`IsSolvableStage`).

**Sketch** (paper pp. 22–26).
1. **Step 1a.** Choose Φ with Prop 6, k = 2, via `Work.CohomologicalShrinking.exists_shrinking_H2_tate`.
   - Take T = ⊕_{v∈T¹∪{∞}} Ind_{D_v}^G 𝔽_p (coinduced modules; instance `coindSMulCommClass`), with
     D_v = image of a decomposition group or ⟨c⟩.
   - The local extension classes lie in H²(φ(D_v), E_m) = H²(G, E_m ⊗ Ind) (Shapiro), because φ_m(D_v)
     ≅ D_v(K/ℚ) by (i). Kill them.
   - Then φ_n = Φ∘φ_m has split local extensions at T¹ ∪ ∞.
   - (i) and (ii) pass to Φ∘φ_m: images of trivial or cyclic totally ramified local groups.
2. **Step 1b/1c.** Local solvability at the remaining places.
   - Unramified places: `SSGRoute.local_tame_lifting`.1 (D/I ≅ Ẑ, Frobenius F).
   - Places ramified in N/K: by (ii) the local group is cyclic totally ramified of order p^a, and a preimage
     in Γ^{τ+1} has order p^{a+ε}, ε ≤ 1. Use `local_tame_lifting`.2 with the μ hypothesis from
     `HasRootsOfUnity` (ℓ splits in K ∋ ζ_{p^{i+1}}).
3. **Step 2.** The global obstruction to lifting φ is φ*(class of Γ^{τ+1} → Γ^τ).
   - Dictionary: `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2`, and the H²-classification in
     `Work.GroupCohomology`.
   - The obstruction is locally trivial everywhere, so `SSGRoute.sha2_image_of_Hm2` (base ℚ, T = μ_p^∨)
     gives x ∈ Ĥ^{-2}(G, E_m ⊗ T) controlling it.
   - Shrink again with `exists_shrinking_Hm2_tate`, whose `hm2Map` is `Work.Tate.Hm2Map` of
     `(gradedMapLin …).rTensor T`.
   - Naturality: the extension class at level n pulled back along flowGroupMap equals the push-forward of
     the class at level m along E_m → E_n.
4. The composite of the two shrinkings (`OperatorMap.comp`, `exists_operatorMap_of_le`) keeps the Step-1
   splitting: it is inherited by images.

**Assets.** `Prop5Data` from `SSGRoute.prop5Data_exists`; `flowGroupMap`, `flowQuotMap`, `flowNormal`,
`gradedMapLin`, `OperatorMap`; `Work.AbsoluteKummer` (continuous H², finite-level description
`Factorisation.exists_finiteGalois_Z2`).

**Imports.** Interfaces, `SSGRoute.prop5Data_exists`, `SSGRoute.local_tame_lifting`,
`SSGRoute.sha2_image_of_Hm2`, `Submission.Work.AbsoluteGalois.All`,
`Submission.Work.AbsoluteKummer.All`.

Delegate: (1a), (1b/1c), (2), and the naturality of extension classes under flowGroupMap, each as a separate
lemma.
-/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

/-! ## The decomposition of `solvableStage_of_scholz` (SW §5, Steps 1–2)

**Status (2026-10-01).**  The proof in this file is complete; the only remaining axiom on its
dependency chain is the Poitou–Tate input of `Work.SSGRoute.stage_global_lifting` (via
`Work.SSGRoute.sha2_image_of_Hm2`, `sha2_dual_control` and the `PT/` lane).  The three delegated
pieces are:

* `SSGRoute.stage_local_shrinking_cohomological` (Step 1a, Prop 6 with `k = 2`): for every level
  `m ≥ m₀` and every Scholz solution `φ` at level `m`, an operator map `Φ₁ : F(m) ⇢ F(n)` such that
  `φM := flowGroupMap Φ₁ ∘ φ` has **split** local extensions at all places of `T¹` *and* at all
  involutions.  Both clauses come from the Shapiro/Proposition-6 argument with
  `T = (⊕_{v∈T¹} Ind_{D_v}^G 𝔽_p) ⊕ Ind_{⟨c⟩}^G 𝔽_p` (the real places are part of the paper's `T`, so
  no separate two-torsion group theory is used — see `AUDIT_p2_two_torsion_atom.lean.md`);
* `SSGRoute.exists_localLift_outside_T1` (Steps 1b/1c, from `local_tame_lifting`): `φM` is locally
  liftable, with *open* kernel, at every finite place outside `T¹`;
* `SSGRoute.stage_global_lifting` (Step 2, `sha2_image_of_Hm2` + `exists_shrinking_Hm2_tate`): at
  level `m₀G` those local data give `Φ₂ : F(m₀G) ⇢ F(n)` and a continuous lift
  `ψ : G_ℚ →* Γ^{τ+1}_n` of `flowGroupMap Φ₂ ∘ φM`, keeping the `T¹` splitting.

The final solution is `φn = flowGroupMap Φ₂ ∘ φM`; `scholzSolution_comp_flowGroupMap` (proved here)
shows it is Scholz at level `n`, `ψ` is the required lift, and the `T¹`-splitting is the local clause
of `IsSolvableStage`.  Level bookkeeping: the first shrinking has target `m₀G` (not `n`) because
`stage_global_lifting` needs the level-`m` solution itself to be locally trivial at *every* place.

Two glue lemmas are proved in this file: `scholzSolution_comp_flowGroupMap` (Scholz solutions pass to
images under `flowGroupMap`) and `isOpen_comap_subtype` (relative openness), together with
`flowGroupMap_surjective`/`flowQuotMap_surjective` and the cyclicity transfer `isCyclic_map_of_isCyclic`. -/


/-! ## The decomposition of `solvableStage_of_scholz` (SW §5, Steps 1–2)

The proof below is assembled from exactly three delegated lemmas (all in
`Submission/Work/SSGRoute/`), each of which is one of the steps the paper performs, plus two
elementary glue lemmas proved in this file.

**Level bookkeeping.**  The conclusion at level `n` is produced from a Scholz solution at a much
larger level by *shrinking*: an operator map `Φ : F(m) ⇢ F(n)` pushes a solution `φ` at level `m`
to the solution `flowGroupMap Φ ∘ φ` at level `n`.  Two shrinkings are composed:

* `stage_local_shrinking` (Step 1a, Prop 6 with `k = 2`): applied with target level `m₀G`
  (the threshold of the second shrinking), it produces `Φ₁ : F(m₀L) ⇢ F(m₀G)` such that the
  pushed solution `φM = flowGroupMap Φ₁ ∘ φ'` has *split* local extensions at all places of `T¹`
  and at all involutions;
* `stage_local_solvable` (Steps 1b/1c, from `SSGRoute.local_tame_lifting`): for such a `φM`, the
  local extension splits — or at least is liftable — at every finite place outside `T¹`;
* `stage_global_lifting` (Step 2, `sha2_image_of_Hm2` + `exists_shrinking_Hm2_tate`): applied at
  level `m₀G` with target `n`, this yields `Φ₂ : F(m₀G) ⇢ F(n)` together with a global lift
  `ψ : G_ℚ → Γ^{τ+1}_n` of `flowGroupMap Φ₂ ∘ φM` whose kernel is open, and it keeps the `T¹`
  splitting.  (Its hypotheses are exactly the local data produced by the previous two steps.)

The final solution is `φn = flowGroupMap Φ₂ ∘ φM`, which is Scholz at level `n` by
`scholzSolution_comp_flowGroupMap`; the lift `ψ` and the `T¹`-splitting then give
`IsSolvableStage p K n i j` verbatim.

**Why the *first* shrinking must have target `m₀G` (and not `n`).**  Step 2 needs the level-`m`
solution itself to be locally trivial at *every* place (that is the hypothesis of
`sha2_image_of_Hm2`); a failing local extension at a place of `T¹` is repaired only by the
shrinking, which kills the local extension *class at the source level*.  Hence the first
shrinking is applied at level `m₀L` with target `m₀G`: the killed classes are the level-`m₀L`
ones, so the induced level-`m₀G` local extensions split.
-/


/-! ## Glue lemmas for the rank change `F(m) ⇢ F(n)`

The whole induction step of Theorem 15 produces, at the level `n`, a solution of the `τ`-problem
out of a solution at a larger level `m ≥ n` by pushing forward along a surjective `G`-operator
homomorphism `Φ : F(m) ⇢ F(n)` (Schmidt–Wingberg's "shrinking").  This section records the two
elementary facts about that push-forward that the rest of the chapter needs. -/

section Glue

variable {p : ℕ} {G : Type*} [Group G]

/-- The image of a cyclic subgroup under a homomorphism is cyclic. -/
theorem isCyclic_map_of_isCyclic {N P : Type*} [Group N] [Group P] (f : N →* P) (H : Subgroup N)
    (h : IsCyclic ↥H) : IsCyclic ↥(Subgroup.map f H) := by
  let F : ↥H →* ↥(Subgroup.map f H) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- **Relative openness of the preimage of an open subgroup.**  If `K ≤ G` is an open subgroup of
the topological group `G` and `H ≤ G` is any subgroup, then `K ∩ H` is open in the subspace
topology on `H`.  This is the form in which the openness of the kernel of a *local* lift
(`l : D_A →* Γ^{τ+1}` with `ker(φ|D_A) ≤ ker l`) is inherited from the openness of `ker φ`. -/
theorem isOpen_comap_subtype {H K : Subgroup SSGRoute.GalQ} (hK : IsOpen (K : Set SSGRoute.GalQ)) :
    IsOpen ((K.comap H.subtype : Subgroup ↥H) : Set ↥H) := by
  have h : (K.comap H.subtype : Set ↥H) = H.subtype ⁻¹' (K : Set SSGRoute.GalQ) := rfl
  rw [h]
  exact hK.preimage continuous_subtype_val

/-- `flowQuotMap` is surjective (it is induced by a surjective operator map). -/
theorem flowQuotMap_surjective {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowQuotMap p G i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

/-- `flowGroupMap` is surjective. -/
theorem flowGroupMap_surjective {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowGroupMap p G i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective (p := p) i j Φ γ.left
  have key : flowGroupMap p G i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p G i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

end Glue

/-- **Scholz solutions are stable under the rank change `F(m) ⇢ F(n)`.**  A surjective
`G`-operator homomorphism `Φ : F(m) ⇢ F(n)` induces `flowGroupMap Φ : Γ_m^τ →* Γ_n^τ`, and the
push-forward of a Scholz solution at level `m` is a Scholz solution at level `n`:

* surjectivity and open kernel are inherited (the kernel can only grow);
* `flowQuot` is natural (`flowQuot_flowGroupMap`);
* conditions (i), (ii) of Theorem 15 are inherited by images: `φ σ = 1` implies
  `(flowGroupMap Φ ∘ φ) σ = 1`, the image of a cyclic group is cyclic, and the "elements are hit by
  inertia" condition is preserved by applying `flowGroupMap Φ`. -/
theorem scholzSolution_comp_flowGroupMap (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ) :
    SSGRoute.IsScholzSolution p K n i j ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) := by
  obtain ⟨hflow, hsch⟩ := hφ
  obtain ⟨hsurj, hopen, hres⟩ := hflow
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (flowGroupMap_surjective (p := p) i j Φ).comp hsurj
  · refine Subgroup.isOpen_mono ?_ hopen
    intro σ hσ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ ⊢
    rw [hσ, map_one]
  · intro σ
    rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hres σ
  · intro A hA σ hσ hσK
    rw [MonoidHom.comp_apply, hsch.1 A hA σ hσ hσK, map_one]
  · intro c hc hcK
    rw [MonoidHom.comp_apply, hsch.2.1 c hc hcK, map_one]
  · intro A hA h
    obtain ⟨σ, hσ, hσK, hne⟩ := h
    have hne' : φ σ ≠ 1 := fun hc => hne (by rw [MonoidHom.comp_apply, hc, map_one])
    obtain ⟨h1, h2, h3⟩ := hsch.2.2 A hA ⟨σ, hσ, hσK, hne'⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [← Subgroup.map_map (K := SSGRoute.decomp ℚ A) (f := φ)
        (g := flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)]
      exact isCyclic_map_of_isCyclic _ _ h2
    · intro σ' hσ'
      obtain ⟨τ, hτ, hτφ⟩ := h3 σ' hσ'
      exact ⟨τ, hτ, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hτφ]⟩

/-- **`IsSolvableStage` from a lift that kills the `T¹`-part of the kernel.**  This isolates the
final, purely group-theoretic step of "Steps 1–2": once one has a Scholz solution `φ` at level `n`
together with a (continuous, not necessarily proper) lift `ψ` to `τ + 1` whose kernel contains the
local kernels `ker(φ) ∩ D_A` for the places `A` of `T¹`, the local groups `l_A := ψ|_{D_A}` supply
the local splittings required by `IsSolvableStage`. -/
theorem isSolvableStage_of_lift (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hφ : SSGRoute.IsScholzSolution p K n i j φ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : SSGRoute.LiftsFlow ψ φ) (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hloc : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1 → ψ σ = 1) :
    SSGRoute.IsSolvableStage p K n i j := by
  refine ⟨φ, ψ, hφ, hψ, hopen, ?_⟩
  intro A hA
  exact ⟨ψ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A)),
    fun σ => hψ σ.1,
    fun σ hσ => hloc A hA σ.1 σ.2 hσ⟩

open SSGRoute
theorem solvableStage_of_scholz (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hIH : ∀ n : ℕ, 1 ≤ n →
      ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
        SSGRoute.IsScholzSolution p K n i j φ)
    (n : ℕ) (hn : 1 ≤ n) :
    SSGRoute.IsSolvableStage p K n i j := by
  -- **Step 2** at the final level `n`: the threshold `m₀G` of the second (global) shrinking.
  obtain ⟨m₀G, hm₀G, hG⟩ := stage_global_lifting p K i j hj hji hμ n hn
  have hm₀G1 : 1 ≤ m₀G := le_trans hn hm₀G
  -- **Step 1a** with target level `m₀G`: the first (local) shrinking, obtained by the
  -- Shapiro/Proposition-6 argument for *both* clauses (the real places are in the paper's `T`).
  obtain ⟨m₀L, hm₀L, hL⟩ := stage_local_shrinking_cohomological p K i j hj hji hμ m₀G hm₀G1
  have hm₀L1 : 1 ≤ m₀L := le_trans hm₀G1 hm₀L
  -- A Scholz solution at level `m₀L` (the induction hypothesis), pushed down to level `m₀G`.
  obtain ⟨φ', hφ'⟩ := hIH m₀L hm₀L1
  obtain ⟨Φ₁, hΦ₁T1, hΦ₁inv⟩ := hL m₀L le_rfl φ' hφ'
  set φM : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G i j :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ₁).comp φ' with hφM
  have hφMscholz : SSGRoute.IsScholzSolution p K m₀G i j φM :=
    scholzSolution_comp_flowGroupMap p K Φ₁ φ' hφ'
  have hφMopen : IsOpen (φM.ker : Set SSGRoute.GalQ) := hφMscholz.1.2.1
  -- **Step 1b/1c**: local solvability, with *open* kernel, at the places outside `T¹`.
  have hOther : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      ¬ SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) :=
    exists_localLift_outside_T1 p K i j hj hji hμ m₀G φM hφMscholz
  -- **Step 1a** again: at the places of `T¹` the shrinking gives the local *splitting*; the
  -- openness of the kernel follows because `l` factors through `φM` and `ker φM` is open.
  have hT1 : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
        (∀ σ : ↥(SSGRoute.decomp ℚ A), φM σ = 1 → l σ = 1) := by
    intro A hA
    obtain ⟨l, hl₁, hl₂⟩ := hΦ₁T1 A hA
    exact ⟨l, hl₁, Subgroup.isOpen_mono (fun σ hσ => hl₂ σ hσ)
      (isOpen_comap_subtype (H := SSGRoute.decomp ℚ A) hφMopen), hl₂⟩
  -- The same at the real places.
  have hInv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(Subgroup.zpowers c), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(Subgroup.zpowers c)) := by
    intro c hc
    obtain ⟨l, hl₁, hl₂⟩ := hΦ₁inv c hc
    exact ⟨l, hl₁, Subgroup.isOpen_mono (fun σ hσ => hl₂ σ hσ)
      (isOpen_comap_subtype (H := Subgroup.zpowers c) hφMopen)⟩
  -- **Step 2**: the second shrinking produces the lift at level `n`.
  obtain ⟨Φ₂, ψ, hψ, hopen, hlocT1⟩ := hG m₀G le_rfl φM hφMscholz hOther hT1 hInv
  exact ⟨(Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ₂).comp φM, ψ,
    scholzSolution_comp_flowGroupMap p K Φ₂ φM hφMscholz, hψ, hopen, hlocT1⟩

end Work.SSGRoute
