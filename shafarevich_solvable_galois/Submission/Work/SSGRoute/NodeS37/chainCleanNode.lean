import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.properStageAssemblyData
import Submission.Work.SSGRoute.step4_tool_S_exists
import Submission.Work.SSGRoute.step4_y_escape_v2.GesEFromZmodV2
import Submission.Work.SSGRoute.step4_y_localdata
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The Step-4 arithmetic chain (`N1` + `N4`) of the node `step4_y_exists_v2`

* `step4_frattini_newPlace_v3` (node **N1** of `_NOTE_STEP4_DESIGN.md`): at a place whose whole
  decomposition group over `ℚ` is killed by the level-`τ` solution `D.phi`, every additive
  `ZMod p`-valued function on `Gal(ℚ̄/↥K)` vanishing on `Gal(ℚ̄/Λ)` vanishes on the whole
  decomposition group over `↥K`.  The proof is the Frattini argument: `D.psi` maps `G_K` onto
  `F(n)/F(n)^{(τ+1)}`, so such a function descends to the free factor; it kills `p`-th powers and
  commutators, hence the second term of the `p`-central series, which contains the graded piece
  `flowEKer = F(n)^{(i,j)}/F(n)^{(i,j+1)}` for `i ≥ 2`.
* `step4_y_localData_escape_v3` (node **N4**): the step-4 local data with the escape at `D.Λ`,
  using `Grünwald` with escape (`grunwald_escape_support_E`, node N3) and `N1`.

Everything else in the chain is imported from proved modules. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open Filter
open scoped Topology
open scoped Pointwise

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- An additive `ZMod p`-valued function kills the second term of the descending `p`-central
series (`P^p[P, P]`). -/
theorem ySeriesTwo_kill_v3 {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] (h : P → ZMod p)
    (hadd : ∀ x y : P, h (x * y) = h x + h y) :
    ∀ x ∈ Work.Shrinking.pCentralSeries p P 1, h x = 0 := by
  have h1 : h 1 = 0 := by
    have h2 := hadd 1 1
    rw [mul_one] at h2
    exact add_left_cancel (show h 1 + h 1 = h 1 + 0 from by rw [add_zero]; exact h2.symm)
  have hinv : ∀ x : P, h x⁻¹ = - h x := by
    intro x
    have h2 : h x + h x⁻¹ = 0 := by rw [← hadd x x⁻¹, mul_inv_cancel, h1]
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h2)
  -- REWRITTEN (node lane, session 42): the `•`-notation no longer matches `succ_nsmul` /
  -- `nsmul_eq_mul` because of the global `instance (priority := 1300) ssgDistribSMulToSMulSt3`
  -- declared at `properStageAssemblyData.lean:378` (it shadows the standard `SMul` instances
  -- with a definitionally-but-not-syntactically equal one).  The exponent induction below is
  -- therefore carried out in the value group `ZMod p` itself (`(k : ZMod p) * h x`), which
  -- uses no `SMul` instance at all.
  have key : ∀ k : ℕ, ∀ x : P, h (x ^ k) = (k : ZMod p) * h x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, h1, Nat.cast_zero, zero_mul]
    | succ k ih => intro x; rw [pow_succ, hadd, ih, Nat.cast_succ, add_mul, one_mul]
  have hpow : ∀ x : P, h (x ^ p) = 0 := by
    intro x
    rw [key p x, ZMod.natCast_self, zero_mul]
  have hcomm : ∀ a b : P, h (a * b * a⁻¹ * b⁻¹) = 0 := by
    intro a b
    rw [hadd, hadd, hadd, hinv, hinv]
    abel
  let K₀ : Subgroup P :=
    { carrier := {x | h x = 0}
      mul_mem' := fun hx hy => by
        show h (_ * _) = 0
        rw [hadd, hx, hy, add_zero]
      one_mem' := h1
      inv_mem' := fun hx => by
        show h _⁻¹ = 0
        rw [hinv, hx, neg_zero] }
  have hK₀ : ∀ x : P, x ∈ K₀ ↔ h x = 0 := fun x => Iff.rfl
  have hstep : Work.Shrinking.pCentralStep p (⊤ : Subgroup P) ≤ K₀ := by
    rw [Work.Shrinking.pCentralStep]
    refine sup_le ?_ ?_
    · rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
      rintro x ⟨y, -, rfl⟩
      exact (hK₀ (y ^ p)).mpr (hpow y)
    · refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_)
      rw [commutatorElement_def]
      exact (hK₀ (a * b * a⁻¹ * b⁻¹)).mpr (hcomm a b)
  intro x hx
  rw [show (1 : ℕ) = 0 + 1 from rfl, Work.Shrinking.pCentralSeries_succ,
    Work.Shrinking.pCentralSeries_zero] at hx
  exact (hK₀ x).mp (hstep hx)

/-- **Frattini vanishing at a place of new ramification** (node N1 of the step-4 design). -/
theorem step4_frattini_newPlace_v3 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hi : 2 ≤ i)
    (D : Work.SSGRoute.Step4CokerData p K n i j) (A : ValuationSubring SSGRoute.QBar)
    (hAφ : ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (hχ : ∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y)
    (hχΛ : ∀ δ ∈ (Work.SSGRoute.overK K D.Λ D.hKΛ).fixingSubgroup, χ δ = 0) :
    ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0 := by
  classical
  -- ## the structural facts about `D.psi`
  have hsurj : Function.Surjective D.psi := by
    intro y
    obtain ⟨x, hx⟩ := Work.SSGRoute.flowGroupMap_surjective_local p (K ≃ₐ[ℚ] K)
      (tauSucc i j).1 (tauSucc i j).2 D.Φ y
    obtain ⟨σ, hσ⟩ := (D.data.2.2.1).1 x
    exact ⟨σ, by
      show D.psi σ = y
      rw [show D.psi σ = flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 D.Φ
          (D.ψm σ) from rfl, hσ, hx]⟩
  have hker : D.psi.ker = D.Λ.fixingSubgroup := by
    simpa only [Step4CokerData.psi] using D.hΛker
  have hquot : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (D.psi σ)
        = AlgEquiv.restrictNormalHom K σ := by
    intro σ
    rw [show D.psi σ = flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 D.Φ (D.ψm σ)
        from rfl, flowQuot_flowGroupMap]
    exact (D.data.2.2.1).2.2 σ
  have hproj : ∀ σ : SSGRoute.GalQ,
      flowGroupProj p (K ≃ₐ[ℚ] K) n i j (D.psi σ) = D.phi σ := by
    intro σ
    rw [show D.psi σ = flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 D.Φ
        (D.ψm σ) from rfl, ← MonoidHom.comp_apply,
      show (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).comp
            (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 D.Φ)
          = (flowGroupMap p (K ≃ₐ[ℚ] K) i j D.Φ).comp
            (flowGroupProj p (K ≃ₐ[ℚ] K) D.m i j) from
        flowGroupProj_comp_flowGroupMap p (K ≃ₐ[ℚ] K) i j D.Φ,
      MonoidHom.comp_apply, flowGroupProj_eq_of_liftsFlowAt_local p K (D.data.2.1 σ)]
    rfl
  -- ## the fixing-subgroup correspondence between the `↥K`- and the `ℚ`-side
  have htransfer : ∀ (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup),
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩
          ∈ (Work.SSGRoute.overK K D.Λ D.hKΛ).fixingSubgroup) ↔ σ ∈ D.Λ.fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hh x hx
      exact hh x hx
    · intro hh x hx
      exact hh x hx
  -- ## `ψ(G_K)` contains the normal subgroup `F(n)/F(n)^{(τ+1)}`
  have hnorm_le : flowNormal p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      ≤ (K.fixingSubgroup).map D.psi := by
    intro y hy
    have hy1 : flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 y = 1 := by
      have h2 : y ∈ (flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).ker := by
        rwa [flowQuot_ker]
      exact MonoidHom.mem_ker.mp h2
    obtain ⟨σ, hσ⟩ := hsurj y
    refine Subgroup.mem_map.mpr ⟨σ, ?_, hσ⟩
    have h1 : AlgEquiv.restrictNormalHom K σ = 1 := by rw [← hquot σ, hσ, hy1]
    rw [← MonoidHom.mem_ker] at h1
    rwa [show (AlgEquiv.restrictNormalHom K).ker = K.fixingSubgroup from
      @IntermediateField.restrictNormalHom_ker ℚ SSGRoute.QBar _ _ _ K ‹Normal ℚ K›] at h1
  -- ## the descent of `χ` to `ψ(G_K)`
  have hcompat : ∀ u v : ↥(K.fixingSubgroup), D.psi u = D.psi v →
      χ ((IntermediateField.fixingSubgroupEquiv K) u)
        = χ ((IntermediateField.fixingSubgroupEquiv K) v) := by
    intro u v huv
    have hmem : (u : SSGRoute.GalQ)⁻¹ * (v : SSGRoute.GalQ) ∈ D.psi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [hker] at hmem
    have hcorr : ((IntermediateField.fixingSubgroupEquiv K)
          ⟨(u : SSGRoute.GalQ)⁻¹ * (v : SSGRoute.GalQ),
            K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem u.2) v.2⟩
          ∈ (Work.SSGRoute.overK K D.Λ D.hKΛ).fixingSubgroup) :=
      (htransfer _ _).mpr hmem
    have hzero : χ ((IntermediateField.fixingSubgroupEquiv K)
        ⟨(u : SSGRoute.GalQ)⁻¹ * (v : SSGRoute.GalQ),
          K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem u.2) v.2⟩) = 0 := hχΛ _ hcorr
    have hmul : ((IntermediateField.fixingSubgroupEquiv K) v)
        = ((IntermediateField.fixingSubgroupEquiv K) u) *
          ((IntermediateField.fixingSubgroupEquiv K)
            ⟨(u : SSGRoute.GalQ)⁻¹ * (v : SSGRoute.GalQ),
              K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem u.2) v.2⟩) := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [hmul, hχ, hzero, add_zero]
  have hex : ∀ y : ↥((K.fixingSubgroup).map D.psi), ∃ u : ↥(K.fixingSubgroup), D.psi u = y.1 := by
    intro y
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨a, ha⟩, hay⟩
  let χbar : ↥((K.fixingSubgroup).map D.psi) → ZMod p := fun y =>
    χ ((IntermediateField.fixingSubgroupEquiv K) (hex y).choose)
  have χbar_spec : ∀ (u : ↥(K.fixingSubgroup)) (y : ↥((K.fixingSubgroup).map D.psi)),
      D.psi u = y.1 → χbar y = χ ((IntermediateField.fixingSubgroupEquiv K) u) := by
    intro u y hy
    exact hcompat (hex y).choose u (by rw [(hex y).choose_spec, hy])
  have χbar_add : ∀ x y : ↥((K.fixingSubgroup).map D.psi),
      χbar (x * y) = χbar x + χbar y := by
    intro x y
    have hxy : D.psi ((hex x).choose * (hex y).choose) = (x * y).1 := by
      rw [map_mul, (hex x).choose_spec, (hex y).choose_spec]; rfl
    rw [χbar_spec ((hex x).choose * (hex y).choose) (x * y) hxy,
      χbar_spec (hex x).choose x (hex x).choose_spec,
      χbar_spec (hex y).choose y (hex y).choose_spec]
    rw [show (IntermediateField.fixingSubgroupEquiv K) ((hex x).choose * (hex y).choose)
        = ((IntermediateField.fixingSubgroupEquiv K) (hex x).choose)
          * ((IntermediateField.fixingSubgroupEquiv K) (hex y).choose) from map_mul _ _ _]
    exact hχ _ _
  -- ## the additive map on the free operator group
  let q2 : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n →*
      flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    (QuotientGroup.mk'
        ((flowTerm p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤)).comp
      (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)).symm.toMonoidHom
  have hmemq2 : ∀ f : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n,
      flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 f)
        ∈ (K.fixingSubgroup).map D.psi := by
    intro f
    refine hnorm_le ?_
    rw [← flowInl_range (p := p) (G := K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2]
    exact ⟨q2 f, rfl⟩
  let h : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n → ZMod p := fun f =>
    χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 f), hmemq2 f⟩
  have haddh : ∀ f g : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n,
      h (f * g) = h f + h g := by
    intro f g
    have h2 : flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 (f * g))
        = flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 f)
          * flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 g) := by
      rw [map_mul, map_mul]
    show χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 (f * g)), _⟩
        = χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 f), _⟩
          + χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 g), _⟩
    rw [show (⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 (f * g)), hmemq2 (f * g)⟩
        : ↥((K.fixingSubgroup).map D.psi))
        = ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 f), hmemq2 f⟩
          * ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (q2 g), hmemq2 g⟩
        from Subtype.ext h2]
    exact χbar_add _ _
  have hkill := ySeriesTwo_kill_v3 (p := p) h haddh
  -- ## conclusion
  intro δ hδ
  set u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm δ with hu
  have hδeq : δ = (IntermediateField.fixingSubgroupEquiv K) u := by
    rw [hu]; exact (MulEquiv.apply_symm_apply _ _).symm
  have hmemD : (u : SSGRoute.GalQ) ∈ SSGRoute.decomp ℚ A := by
    have h1 : (IntermediateField.fixingSubgroupEquiv K) u ∈ SSGRoute.decomp ↥K A := hδeq ▸ hδ
    exact (local_transport_decomp K A (u : SSGRoute.GalQ) u.2).mp h1
  have hmemE : D.psi (u : SSGRoute.GalQ) ∈ flowEKer p (K ≃ₐ[ℚ] K) n i j := by
    rw [flowEKer, MonoidHom.mem_ker, hproj]
    exact hAφ _ hmemD
  rw [Work.SSGRoute.flowEKer_eq_map_ker] at hmemE
  obtain ⟨y, hyker, hyeq⟩ := Subgroup.mem_map.mp hmemE
  obtain ⟨t, ht⟩ := Work.SSGRoute.flowEKerLift_surjective p (K ≃ₐ[ℚ] K) n i j ⟨y, hyker⟩
  have htval : (Work.SSGRoute.flowEKerLift p (K ≃ₐ[ℚ] K) n i j t
      : flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) = y := by
    have h2 := congrArg (fun z : ↥((flowQuotientProj p (K ≃ₐ[ℚ] K) n i j).ker) =>
      (z : flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)) ht
    simpa using h2
  have hty : (QuotientGroup.mk'
        ((flowTerm p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
        (Subgroup.inclusion (le_top : flowTerm p (K ≃ₐ[ℚ] K) n i j ≤ ⊤) t)
      = y := by
    rw [← htval]
    rfl
  have hq2t : q2 (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) = y := by
    show (QuotientGroup.mk'
        ((flowTerm p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
        ((Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)).symm
          (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)) = y
    rw [show (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)).symm
        (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)
        = Subgroup.inclusion le_top t from Subtype.ext rfl]
    exact hty
  have hψ : flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      (q2 (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)) = D.psi (u : SSGRoute.GalQ) := by
    rw [hq2t]; exact hyeq
  have hχbar_eq : χbar ⟨D.psi (u : SSGRoute.GalQ),
        Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩⟩
      = χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
          (q2 (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)), hmemq2 _⟩ := by
    have hsub : (⟨D.psi (u : SSGRoute.GalQ), Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩⟩
        : ↥((K.fixingSubgroup).map D.psi))
        = ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
            (q2 (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)), hmemq2 _⟩ :=
      Subtype.ext hψ.symm
    rw [hsub]
  calc χ δ
      = χ ((IntermediateField.fixingSubgroupEquiv K) u) := by rw [hδeq]
    _ = χbar ⟨D.psi (u : SSGRoute.GalQ), Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩⟩ :=
        (χbar_spec u _ rfl).symm
    _ = χbar ⟨flowInl p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
          (q2 (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)), hmemq2 _⟩ := hχbar_eq
    _ = h (t : Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) := rfl
    _ = 0 := hkill _ (by
        have hle1 : refinedTerm p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) i j
            ≤ pSeries p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) 2 :=
          le_trans (refinedTerm_le_pSeries p _ i j) (pSeries_antitone p _ hi)
        exact hle1 t.2)


/-- Schmidt--Wingberg's Fourth Step datum with the escape at `D.Λ`, for stages `(i,j)` with
`2 ≤ i`.  This replaces the escape-free `step4_yLarge_exists`, which is false.

It is proved for every coker datum `D`, with no shrinking and no Hochschild--Serre transgression.
The obstruction to the prescribed local data is orthogonality against the characters of
`Gal(Λ/K)`. Those characters vanish on the decomposition groups of the `Tnew` places, by
`step4_frattini_newPlace`.

Route:
* take the place set `S` of `step4_tool_S_exists`, and replace its elements that are
  `↥K`-conjugate to a place of `Tnew` by that place (the `S'` trick of `step4_y_localdata_core`);
* the local datum is `ηt A` transported to `decomp ↥K A` for `A ∈ Tnew`, and `0` elsewhere
  (continuity from `step4_localDatum_open_vanishing`);
* apply `grunwald_escape_support_E` with `L := D.Λ`. `hTcov` comes from the tool's `hSram`, and
  `hsupp` comes from `step4_frattini_newPlace` together with `hTnewφ`;
* `hesc` is the escape clause of that conclusion. -/
theorem step4_y_localData_escape_v3 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hTnewfin : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A)
    (hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (hηt : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A,
        ηt A hA (σ * τ) = ηt A hA σ + ηt A hA τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (ηt A hA)) :
    Nonempty (Step4YLocalData D Tnew ηt) := by
  classical
  haveI hGalK : IsGalois ℚ K := isGalois_of_normal K
  -- ## the `p = 2` input
  have hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1 :=
    fun _ => no_two_torsion_fixingSubgroup p K i (le_trans hj hji) hμ
  -- ## the primitive `p`-th root of unity in `K`
  obtain ⟨ζ₀, hζ₀K, hζ₀⟩ := hμ
  have hζ : IsPrimitiveRoot (ζ₀ ^ (p ^ i)) p :=
    hζ₀.pow (pow_pos (Fact.out : p.Prime).pos _) (Nat.pow_succ p i)
  have hζK : ζ₀ ^ (p ^ i) ∈ K := by
    rw [← zpow_natCast]
    exact K.pow_mem hζ₀K _
  -- ## the place set of the tool
  obtain ⟨S, hSfin, hSdisj, hSram, hSconj, hScover⟩ := step4_tool_S_exists p K n i j D
  have hTnew_fin' : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ↥K A := fun A hA =>
    (local_transport_isFinPlace K A).mpr (hTnewfin A hA)
  have hTnew_disj' : ∀ A ∈ Tnew, ∀ B ∈ Tnew, SSGRoute.IsConjPlace ↥K A B → A = B :=
    fun A hA B hB hc =>
      D.hSdisj A (hTnewS A hA) B (hTnewS B hB) (isConjPlace_of_isConjPlace_over_K hc)
  -- ## the modified place set `S'`
  set S' : Finset (ValuationSubring SSGRoute.QBar) :=
    (S.filter (fun A => ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A A₀)) ∪ Tnew with hS'_def
  have hTnewS' : ∀ A ∈ Tnew, A ∈ S' := fun A hA => Finset.mem_union_right _ hA
  have hSfin' : ∀ A ∈ S', SSGRoute.IsFinPlace ↥K A := by
    intro A hA
    rw [hS'_def] at hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hSfin A (Finset.mem_filter.mp hA).1
    · exact hTnew_fin' A hA
  have hSdisj' : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace ↥K A B → A = B := by
    intro A hA B hB hc
    rw [hS'_def] at hA hB
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact hSdisj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hc
    · exact absurd hc ((Finset.mem_filter.mp hA).2 B hB)
    · exact absurd (isConjPlace_symm hc) ((Finset.mem_filter.mp hB).2 A hA)
    · exact hTnew_disj' A hA B hB hc
  have hSconj' : ∀ A ∈ S', ∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A := by
    intro A hA
    rw [hS'_def] at hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hSconj A (Finset.mem_filter.mp hA).1
    · exact ⟨A, hTnewS A hA, isConjPlace_refl A⟩
  have hScover' : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ B) →
      ∃ A ∈ S', SSGRoute.IsConjPlace ↥K A B := by
    intro B hB hc
    obtain ⟨A, hA, hAB⟩ := hScover B hB hc
    by_cases h : ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A A₀
    · exact ⟨A, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA, h⟩), hAB⟩
    · push_neg at h
      obtain ⟨A₀, hA₀, hAA₀⟩ := h
      exact ⟨A₀, Finset.mem_union_right _ hA₀,
        isConjPlace_trans (isConjPlace_symm hAA₀) hAB⟩
  -- ## the covering clause of the Grünwald statement
  have hTcov : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨
        SSGRoute.IsRamifiedIn ↥K (overK K D.Λ D.hKΛ) B) →
      ∃ A ∈ S', SSGRoute.IsConjPlace ↥K A B := by
    intro B hB hrel
    obtain ⟨A, hA, hAB⟩ := hSram B hB (hrel.elim (fun hp => Or.inr hp) (fun hr => Or.inl hr))
    by_cases h : ∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A A₀
    · exact ⟨A, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA, h⟩), hAB⟩
    · push_neg at h
      obtain ⟨A₀, hA₀, hAA₀⟩ := h
      exact ⟨A₀, Finset.mem_union_right _ hA₀,
        isConjPlace_trans (isConjPlace_symm hAA₀) hAB⟩
  -- ## the local datum on `S'`
  set f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
      E p (K ≃ₐ[ℚ] K) n i j :=
    fun A x => if h : A ∈ Tnew then
      ηt A h (((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ)
      else 0 with hf_def
  -- the `↥K`-side membership of the transported element is the `ℚ`-side one
  have hmemK : ∀ (A : ValuationSubring SSGRoute.QBar) (x : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      x ∈ SSGRoute.decomp ↥K A →
      ((((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ)) ∈ SSGRoute.decomp ℚ A := by
    intro A x hx
    refine (local_transport_decomp K A
      (((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
        SSGRoute.GalQ) ((IntermediateField.fixingSubgroupEquiv K).symm x).2).mp ?_
    show (IntermediateField.fixingSubgroupEquiv K)
      ((IntermediateField.fixingSubgroupEquiv K).symm x) ∈ SSGRoute.decomp ↥K A
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have hf : ∀ A ∈ S', ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y := by
    intro A hA x hx y hy
    by_cases hAT : A ∈ Tnew
    · rw [hf_def]
      simp only [dif_pos hAT]
      have hcoe : ((((IntermediateField.fixingSubgroupEquiv K).symm (x * y) :
            ↥(K.fixingSubgroup)) : SSGRoute.GalQ))
          = ((((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
              SSGRoute.GalQ) *
            (((IntermediateField.fixingSubgroupEquiv K).symm y : ↥(K.fixingSubgroup)) :
              SSGRoute.GalQ)) := by
        rw [map_mul]
        rfl
      rw [hcoe]
      exact (hηt A hAT).1 _ (hmemK A x hx) _ (hmemK A y hy)
    · rw [hf_def]
      simp only [dif_neg hAT, zero_add]
  have hfc : ∀ A ∈ S', ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0 := by
    intro A hA
    by_cases hAT : A ∈ Tnew
    · -- the open subgroup on which `ηt A` vanishes, pulled back along the two Krull bases
      obtain ⟨U₁, hU₁open, hU₁⟩ := (hηt A hAT).2
      have hmem : (U₁ : Set SSGRoute.GalQ) ∈ 𝓝 (1 : SSGRoute.GalQ) :=
        hU₁open.mem_nhds U₁.one_mem
      rw [krullTopology_mem_nhds_one_iff ℚ SSGRoute.QBar (U₁ : Set SSGRoute.GalQ)] at hmem
      obtain ⟨E, hEfin, hEsub⟩ := hmem
      haveI hEfin' : FiniteDimensional ℚ ↥E := hEfin
      haveI hsup : FiniteDimensional ℚ ↥(E ⊔ K : IntermediateField ℚ SSGRoute.QBar) :=
        IntermediateField.finiteDimensional_sup E K
      haveI hKup : FiniteDimensional ↥K (overK K (E ⊔ K) le_sup_right) :=
        finiteDimensional_overK_of_finite K (E ⊔ K) le_sup_right
      refine ⟨(overK K (E ⊔ K) le_sup_right).fixingSubgroup,
        IntermediateField.fixingSubgroup_isOpen _, ?_⟩
      intro x hx hxdec
      rw [hf_def]
      simp only [dif_pos hAT]
      have hxfix : ∀ y ∈ (E ⊔ K : IntermediateField ℚ SSGRoute.QBar), x y = y := by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hx
        exact fun y hy => hx y hy
      have hσU : ((((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ)) ∈ U₁ := by
        apply hEsub
        apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
        intro y hy
        rw [coe_symm_fixingSubgroupEquiv K x]
        exact hxfix y ((le_sup_left : (E : IntermediateField ℚ SSGRoute.QBar) ≤ E ⊔ K) hy)
      have hσdec : ((((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ)) ∈ SSGRoute.decomp ℚ A := hmemK A x hxdec
      have h1 := hU₁ 1 (Subgroup.one_mem _) _ hσU hσdec
      rw [one_mul] at h1
      have hη1 : ηt A hAT 1 = 0 := by
        have h := (hηt A hAT).1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
        rw [one_mul] at h
        exact (add_left_cancel (show ηt A hAT 1 + 0 = ηt A hAT 1 + ηt A hAT 1 from by
          rw [add_zero, ← h])).symm
      rw [hη1] at h1
      exact h1
    · refine ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, ?_⟩
      intro x _ _
      rw [hf_def]
      simp only [dif_neg hAT]
  have hsupp : ∀ A ∈ S',
      (∀ δ ∈ SSGRoute.decomp ↥K A, f A δ = 0) ∨
      (∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K D.Λ D.hKΛ).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0) := by
    intro A hA
    by_cases hAT : A ∈ Tnew
    · exact Or.inr (step4_frattini_newPlace_v3 p K n i j hi D A (hTnewφ A hAT))
    · refine Or.inl ?_
      intro δ _
      rw [hf_def]
      simp only [dif_neg hAT]
  -- ## Grünwald with escape
  haveI hΛfd : FiniteDimensional ℚ ↥D.Λ := D.fdΛ
  haveI hΛgal : IsGalois ℚ ↥D.Λ := D.galΛ
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n i j) :=
    Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n i j
  obtain ⟨ε, hεadd, hεloc, hεagr, hεesc⟩ :=
    gesE_of_zmod_escape_v2 p K (ζ₀ ^ (p ^ i)) hζ hζK hKimag
      D.Λ D.hKΛ S' hSfin' hSdisj' hTcov (E p (K ≃ₐ[ℚ] K) n i j) f hf hfc hsupp
  refine ⟨⟨S', ε, hSfin', hSdisj', hSconj', hScover', hεadd, hεloc, ?_, ?_, hεesc⟩⟩
  · -- the agreement clause on `Tnew`
    intro A hA δ hδ
    have h1 := hεagr A (hTnewS' A hA) δ hδ
    rw [h1, hf_def]
    simp only [dif_pos hA]
  · -- the vanishing clause at the places of `S'` outside the classes of `Tnew`
    intro A hA hno δ hδ
    have hAnot : A ∉ Tnew := fun hAT => hno A hAT (isConjPlace_refl A)
    have h1 := hεagr A hA δ hδ
    rw [h1, hf_def]
    simp only [dif_neg hAnot]


end Work.SSGRoute
