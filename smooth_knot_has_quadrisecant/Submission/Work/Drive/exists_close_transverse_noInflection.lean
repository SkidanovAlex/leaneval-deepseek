import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.interior_zeroSet_projection_empty
import Submission.Work.Drive.rank_patchAll
import Submission.Work.Drive.rank_patchB
import Submission.Work.Drive.exists_close_nonzero_curvature
import Submission.Work.Drive.exists_close_endpointTangentsOffChord
import Submission.Work.Drive.trigRelation_trivial
import Submission.Work.Drive.jets_surjective

/-!
# `Work.Drive.exists_close_transverse_noInflection`
-/

open scoped Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Rank `> finrank W` version of `interior_zeroSet_projection_empty`.** -/
theorem interior_zeroSet_projection_empty_of_rank
    {V W F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {Kv : Set V} (hKv : IsCompact Kv) {K : Set W} (hK : IsCompact K)
    (hrank : ∀ p ∈ Kv ×ˢ K, Ψ p = 0 →
      Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p).range) :
    interior {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} = ∅ := by
  classical
  set S : Set V := {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} with hSdef
  set Z : Set (V × W) := (Kv ×ˢ K) ∩ {p : V × W | Ψ p = 0} with hZdef
  have hZc : IsCompact Z := by
    rw [hZdef]
    exact (hKv.prod hK).inter_right (isClosed_singleton.preimage hΨ.continuous)
  have hSeq : S = Prod.fst '' Z := by
    rw [hSdef, hZdef]
    ext v
    constructor
    · rintro ⟨hvK, w, hwK, hw⟩
      exact ⟨(v, w), ⟨⟨hvK, hwK⟩, hw⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩
      exact ⟨hp1, p.2, hp2, hp3⟩
  have hchart : ∀ p : Z, ∃ (O : Set (V × W)) (γ : V × W → V × W) (C : Set (V × W)),
      IsOpen O ∧ p.1 ∈ O ∧ (∀ x ∈ O, Ψ x = 0 → x ∈ γ '' C) ∧
        dimH (γ '' C) ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    intro p
    obtain ⟨hpmem, hp0⟩ := p.2
    have hdim : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p.1).range :=
      hrank p.1 hpmem hp0
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl (fderiv ℝ Ψ p.1).range
    set πL : F →ₗ[ℝ] (fderiv ℝ Ψ p.1).range :=
      Submodule.projectionOnto (fderiv ℝ Ψ p.1).range q hq with hπL
    set π : F →L[ℝ] (fderiv ℝ Ψ p.1).range := LinearMap.toContinuousLinearMap πL with hπ
    set g : V × W → (fderiv ℝ Ψ p.1).range := fun x => π (Ψ x) with hg
    have h1 : HasFDerivAt g (π.comp (fderiv ℝ Ψ p.1)) p.1 := by
      have h2 := (ContinuousLinearMap.hasFDerivAt π).comp p.1
        ((hΨ.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt)
      simpa [hg, Function.comp_def] using h2
    have hgc : fderiv ℝ g p.1 = π.comp (fderiv ℝ Ψ p.1) := h1.fderiv
    have hsurj : (fderiv ℝ g p.1).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      obtain ⟨x, hx⟩ := y.2
      refine ⟨x, ?_⟩
      show fderiv ℝ g p.1 x = y
      rw [hgc]
      show π ((fderiv ℝ Ψ p.1) x) = y
      have hy : (fderiv ℝ Ψ p.1) x = (y : F) := hx
      rw [hy]
      show π (y : F) = y
      simp only [hπ, hπL, LinearMap.coe_toContinuousLinearMap']
      exact Submodule.projectionOnto_apply_left hq y
    have hkerrank : Module.finrank ℝ (fderiv ℝ g p.1).ker ≤ Module.finrank ℝ V - 1 := by
      have key : Module.finrank ℝ (fderiv ℝ g p.1).range +
          Module.finrank ℝ (fderiv ℝ g p.1).ker = Module.finrank ℝ (V × W) :=
        LinearMap.finrank_range_add_finrank_ker _
      rw [hsurj, finrank_top, Module.finrank_prod] at key
      omega
    have hcontdiff : ContDiffAt ℝ 1 g p.1 := by
      have h3 : ContDiffAt ℝ 1 (fun x : V × W => π (Ψ x)) p.1 :=
        (π.contDiff.comp hΨ).contDiffAt (x := p.1)
      simpa [hg] using h3
    obtain ⟨O, hOo, hpO, γ₀, C₀, L, hLip, hcov⟩ :=
      exists_lipschitz_param_of_fderiv_surjective (f := g) (a := p.1) hcontdiff hsurj
    refine ⟨O, (fun x : V × W =>
        if h : x ∈ (fderiv ℝ g p.1).ker then γ₀ ⟨x, h⟩ else 0),
      Subtype.val '' C₀, hOo, hpO, ?_, ?_⟩
    · intro x hx hx0
      have hxg : g x = g p.1 := by
        show π (Ψ x) = π (Ψ p.1)
        rw [hx0, hp0, map_zero]
      obtain ⟨z, hzC, hzγ⟩ := hcov x hx hxg
      refine ⟨(z : V × W), ⟨z, hzC, rfl⟩, ?_⟩
      simp only [dif_pos z.2]
      exact hzγ
    · have hset : (fun x : V × W =>
          if h : x ∈ (fderiv ℝ g p.1).ker then γ₀ ⟨x, h⟩ else 0) '' (Subtype.val '' C₀)
          = γ₀ '' C₀ := by
        ext y
        constructor
        · rintro ⟨x, ⟨z, hzC, rfl⟩, hxy⟩
          refine ⟨z, hzC, ?_⟩
          simpa only [dif_pos z.2] using hxy
        · rintro ⟨z, hzC, rfl⟩
          exact ⟨(z : V × W), ⟨z, hzC, rfl⟩, by simp only [dif_pos z.2]⟩
      rw [hset]
      calc dimH (γ₀ '' C₀) ≤ dimH C₀ := hLip.dimH_image_le
        _ ≤ dimH (Set.univ : Set ((fderiv ℝ g p.1).ker)) := dimH_mono (Set.subset_univ _)
        _ = ((Module.finrank ℝ ((fderiv ℝ g p.1).ker) : ℕ) : ENNReal) :=
            Real.dimH_univ_eq_finrank _
        _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by exact_mod_cast hkerrank
  choose O γ C hOo hpO hcov hdim using hchart
  have hZcover : Z ⊆ ⋃ p : Z, O p := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hZc.elim_finite_subcover O (fun p => hOo p) hZcover
  have hpiece : ∀ p : Z, dimH (Prod.fst '' (Z ∩ O p)) ≤
      ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    intro p
    calc dimH (Prod.fst '' (Z ∩ O p))
        ≤ dimH (Prod.fst '' (γ p '' C p)) := by
          refine dimH_mono ?_
          rintro v ⟨q, ⟨hqZ, hqO⟩, rfl⟩
          obtain ⟨w, hw, hwq⟩ := hcov p q hqO hqZ.2
          exact ⟨γ p w, ⟨w, hw, rfl⟩, by rw [hwq]⟩
      _ ≤ dimH (γ p '' C p) :=
          (ContinuousLinearMap.fst ℝ V W).lipschitz.lipschitzOnWith.dimH_image_le
      _ ≤ _ := hdim p
  have hsubS : S ⊆ ⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p) := by
    rw [hSeq]
    rintro v ⟨q, hqZ, rfl⟩
    have h1 : q ∈ ⋃ p ∈ (t : Set Z), O p := by
      have h2 := ht hqZ
      simpa only [Set.mem_iUnion, Finset.mem_coe] using h2
    rw [Set.mem_iUnion] at h1
    obtain ⟨p, h1⟩ := h1
    rw [Set.mem_iUnion] at h1
    obtain ⟨hp, hqOp⟩ := h1
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ⟨q, ⟨hqZ, hqOp⟩, rfl⟩⟩⟩
  have hbound : dimH S ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    calc dimH S ≤ dimH (⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p)) := dimH_mono hsubS
      _ = ⨆ p ∈ (t : Set Z), dimH (Prod.fst '' (Z ∩ O p)) :=
          dimH_bUnion (t.finite_toSet.countable) _
      _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := iSup₂_le fun p _ => hpiece p
  by_contra hne
  have hSne : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hdimS : dimH S = ((Module.finrank ℝ V : ℕ) : ENNReal) :=
    Real.dimH_of_nonempty_interior hSne
  rw [hdimS] at hbound
  have hpos : 1 ≤ Module.finrank ℝ V := by
    obtain ⟨v, hv⟩ := hSne
    have hvS : v ∈ S := interior_subset hv
    rw [hSdef] at hvS
    obtain ⟨hvK, w, hwK, hw⟩ := hvS
    have h1 : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ (v, w)).range :=
      hrank (v, w) ⟨hvK, hwK⟩ hw
    have h2 : Module.finrank ℝ (fderiv ℝ Ψ (v, w)).range +
        Module.finrank ℝ (fderiv ℝ Ψ (v, w)).ker = Module.finrank ℝ (V × W) :=
      LinearMap.finrank_range_add_finrank_ker _
    rw [Module.finrank_prod] at h2
    omega
  have hlt : ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) <
      ((Module.finrank ℝ V : ℕ) : ENNReal) :=
    by exact_mod_cast Nat.sub_lt hpos Nat.zero_lt_one
  exact absurd hbound (not_le.mpr hlt)



/-! ## The data map of a parameter triple -/

/-- The data of a curve at a parameter triple (positions at `a, b, m` and the three
velocities). -/
def dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : TripleData :=
  (r w.1, r w.2.1, r w.2.2, velocity r w.1, velocity r w.2.1, velocity r w.2.2)

@[simp] lemma dataP_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataP (dataOf r w) = r w.1 := rfl
@[simp] lemma dataQ_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataQ (dataOf r w) = r w.2.1 := rfl
@[simp] lemma dataM_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataM (dataOf r w) = r w.2.2 := rfl
@[simp] lemma dataA_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataA (dataOf r w) = velocity r w.1 := rfl
@[simp] lemma dataB_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataB (dataOf r w) = velocity r w.2.1 := rfl
@[simp] lemma dataC_dataOf (r : ℝ → Space) (w : ℝ × ℝ × ℝ) : dataC (dataOf r w) = velocity r w.2.2 := rfl

/-- The coefficientwise jet of the perturbation family at a parameter triple: the derivative of
`c ↦ dataOf (pertV r c) w` at any coefficient vector. -/
def jetLin (w : ℝ × ℝ × ℝ) : Coeff →L[ℝ] TripleData :=
  (linSum fun j => trigBasis j w.1).prod
    ((linSum fun j => trigBasis j w.2.1).prod
      ((linSum fun j => trigBasis j w.2.2).prod
        ((linSum fun j => trigBasisD j w.1).prod
          ((linSum fun j => trigBasisD j w.2.1).prod
            (linSum fun j => trigBasisD j w.2.2)))))

@[simp] lemma jetLin_apply (w : ℝ × ℝ × ℝ) (c : Coeff) :
    jetLin w c =
      (linSum (fun j => trigBasis j w.1) c, linSum (fun j => trigBasis j w.2.1) c,
        linSum (fun j => trigBasis j w.2.2) c, linSum (fun j => trigBasisD j w.1) c,
        linSum (fun j => trigBasisD j w.2.1) c, linSum (fun j => trigBasisD j w.2.2) c) := rfl

lemma linSum_trigBasis_eq (t : ℝ) (c : Coeff) :
    linSum (fun j => trigBasis j t) c = perturbCorr (eCoeff c) t := by
  rw [linSum_apply, perturbCorr]
  exact Finset.sum_congr rfl fun j _ => by rw [coeffProj_apply]

lemma linSum_trigBasisD_eq (t : ℝ) (c : Coeff) :
    linSum (fun j => trigBasisD j t) c = perturbVelCorr (eCoeff c) t := by
  rw [linSum_apply, perturbVelCorr]
  exact Finset.sum_congr rfl fun j _ => by rw [coeffProj_apply]

theorem hasFDerivAt_dataSlice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ)
    (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => dataOf (pertV r c) w) (jetLin w) c₀ := by
  have hP : HasFDerivAt (fun c : Coeff => pertV r c w.1) (linSum fun j => trigBasis j w.1) c₀ :=
    hasFDerivAt_pertV_slice r w.1 c₀
  have hQ : HasFDerivAt (fun c : Coeff => pertV r c w.2.1) (linSum fun j => trigBasis j w.2.1) c₀ :=
    hasFDerivAt_pertV_slice r w.2.1 c₀
  have hM : HasFDerivAt (fun c : Coeff => pertV r c w.2.2) (linSum fun j => trigBasis j w.2.2) c₀ :=
    hasFDerivAt_pertV_slice r w.2.2 c₀
  have hAeq : (fun c : Coeff => velocity (pertV r c) w.1) = fun c => pertVelV r c w.1 := by
    funext c; exact velocity_pertV hr.smooth c w.1
  have hBeq : (fun c : Coeff => velocity (pertV r c) w.2.1) = fun c => pertVelV r c w.2.1 := by
    funext c; exact velocity_pertV hr.smooth c w.2.1
  have hCeq : (fun c : Coeff => velocity (pertV r c) w.2.2) = fun c => pertVelV r c w.2.2 := by
    funext c; exact velocity_pertV hr.smooth c w.2.2
  have hA : HasFDerivAt (fun c : Coeff => velocity (pertV r c) w.1)
      (linSum fun j => trigBasisD j w.1) c₀ := by
    rw [hAeq]; exact hasFDerivAt_pertVelV_slice r w.1 c₀
  have hB : HasFDerivAt (fun c : Coeff => velocity (pertV r c) w.2.1)
      (linSum fun j => trigBasisD j w.2.1) c₀ := by
    rw [hBeq]; exact hasFDerivAt_pertVelV_slice r w.2.1 c₀
  have hC : HasFDerivAt (fun c : Coeff => velocity (pertV r c) w.2.2)
      (linSum fun j => trigBasisD j w.2.2) c₀ := by
    rw [hCeq]; exact hasFDerivAt_pertVelV_slice r w.2.2 c₀
  have hcomb := hP.prodMk (hQ.prodMk (hM.prodMk (hA.prodMk (hB.prodMk hC))))
  simpa [dataOf, jetLin] using hcomb

/-! ## The data map of the perturbed curve -/

/-- The data of the perturbed curve at a parameter triple, with the velocities written in the
perturbation vocabulary. -/
def dataMap (r : ℝ → Space) : Coeff × (ℝ × ℝ × ℝ) → TripleData :=
  fun p => (pertV r p.1 p.2.1, pertV r p.1 p.2.2.1, pertV r p.1 p.2.2.2,
    pertVelV r p.1 p.2.1, pertVelV r p.1 p.2.2.1, pertVelV r p.1 p.2.2.2)

lemma dataMap_apply (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (w : ℝ × ℝ × ℝ) :
    dataMap r (c, w) = dataOf (pertV r c) w := by
  simp [dataMap, dataOf, velocity_pertV hr.smooth]

@[simp] lemma dataP_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataP (dataMap r p) = pertV r p.1 p.2.1 := rfl
@[simp] lemma dataQ_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataQ (dataMap r p) = pertV r p.1 p.2.2.1 := rfl
@[simp] lemma dataM_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataM (dataMap r p) = pertV r p.1 p.2.2.2 := rfl
@[simp] lemma dataA_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataA (dataMap r p) = pertVelV r p.1 p.2.1 := rfl
@[simp] lemma dataB_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataB (dataMap r p) = pertVelV r p.1 p.2.2.1 := rfl
@[simp] lemma dataC_dataMap (r : ℝ → Space) (p : Coeff × (ℝ × ℝ × ℝ)) :
    dataC (dataMap r p) = pertVelV r p.1 p.2.2.2 := rfl

lemma contDiff_dataMap {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (dataMap r) := by
  have hV : ContDiff ℝ 1 (fun z : Coeff × ℝ => pertV r z.1 z.2) :=
    (contDiff_pertV_joint hr.smooth).of_le le_top
  have hW : ContDiff ℝ 1 (fun z : Coeff × ℝ => pertVelV r z.1 z.2) :=
    (contDiff_pertVelV_joint hr.smooth).of_le le_top
  have e1 : ContDiff ℝ 1 (fun p : Coeff × (ℝ × ℝ × ℝ) => (p.1, p.2.1)) := by fun_prop
  have e2 : ContDiff ℝ 1 (fun p : Coeff × (ℝ × ℝ × ℝ) => (p.1, p.2.2.1)) := by fun_prop
  have e3 : ContDiff ℝ 1 (fun p : Coeff × (ℝ × ℝ × ℝ) => (p.1, p.2.2.2)) := by fun_prop
  exact (hV.comp e1).prodMk ((hV.comp e2).prodMk ((hV.comp e3).prodMk
    ((hW.comp e1).prodMk ((hW.comp e2).prodMk (hW.comp e3)))))

theorem hasFDerivAt_dataMap_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ)
    (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => dataMap r (c, w)) (jetLin w) c₀ :=
  (hasFDerivAt_dataSlice hr w c₀).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun c => (dataMap_apply r hr c w))

/-! ## The four strata maps -/

/-- The stratum `P_a` (the chord of a collinear triple is tangent at `a`). -/
def stratA (r : ℝ → Space) : Coeff × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchA (dataMap r p)

/-- The stratum `P_b`. -/
def stratB (r : ℝ → Space) : Coeff × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchB (dataMap r p)

/-- The stratum `P_m`. -/
def stratM (r : ℝ → Space) : Coeff × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchM (dataMap r p)

/-- The parameter triple of a configuration. -/
def cfgTriple (w : Cfg) : ℝ × ℝ × ℝ := (cfgA w, cfgB w, cfgM w)

/-- The stratum `P_abm` in multiplier form: the two tangent–chord vectors `y_a`, `y_m` are
parallel to `y_b`. -/
def stratPsi (r : ℝ → Space) : Coeff × Cfg → Space × Space × Space :=
  fun p => (dataColl (dataMap r (p.1, cfgTriple p.2)),
    dataYa (dataMap r (p.1, cfgTriple p.2)) -
      cfgLam p.2 • dataYb (dataMap r (p.1, cfgTriple p.2)),
    dataYm (dataMap r (p.1, cfgTriple p.2)) -
      cfgMu p.2 • dataYb (dataMap r (p.1, cfgTriple p.2)))

lemma contDiff_stratA {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (stratA r) :=
  rpa_contDiff_patchA.comp (contDiff_dataMap hr)

lemma contDiff_stratB {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (stratB r) :=
  rpb_contDiff_patchB.comp (contDiff_dataMap hr)

lemma contDiff_stratM {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (stratM r) :=
  rpm_contDiff_patchM.comp (contDiff_dataMap hr)

lemma contDiff_dataColl : ContDiff ℝ 1 (fun X : TripleData => dataColl X) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1 (fun X : TripleData => (dataP X - dataQ X, dataP X - dataM X)) := by
    unfold dataP dataQ dataM
    fun_prop
  simpa [dataColl, Function.comp_def] using hcross.comp h1

lemma contDiff_dataYa : ContDiff ℝ 1 (fun X : TripleData => dataYa X) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1 (fun X : TripleData => (dataA X, dataP X - dataQ X)) := by
    unfold dataA dataP dataQ
    fun_prop
  simpa [dataYa, Function.comp_def] using hcross.comp h1

lemma contDiff_dataYb : ContDiff ℝ 1 (fun X : TripleData => dataYb X) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1 (fun X : TripleData => (dataB X, dataP X - dataQ X)) := by
    unfold dataB dataP dataQ
    fun_prop
  simpa [dataYb, Function.comp_def] using hcross.comp h1

lemma contDiff_dataYm : ContDiff ℝ 1 (fun X : TripleData => dataYm X) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1 (fun X : TripleData => (dataC X, dataP X - dataQ X)) := by
    unfold dataC dataP dataQ
    fun_prop
  simpa [dataYm, Function.comp_def] using hcross.comp h1

/-- The target map of the `Psi` stratum, as a function of the data. -/
def PhiPsi (lam mu : ℝ) (X : TripleData) : Space × Space × Space :=
  (dataColl X, dataYa X - lam • dataYb X, dataYm X - mu • dataYb X)

lemma contDiff_PhiPsi (lam mu : ℝ) : ContDiff ℝ 1 (PhiPsi lam mu) :=
  (contDiff_dataColl.prodMk ((contDiff_dataYa.sub (contDiff_dataYb.const_smul lam)).prodMk
    (contDiff_dataYm.sub (contDiff_dataYb.const_smul mu))))

lemma contDiff_cfgTriple : ContDiff ℝ 1 (fun p : Coeff × Cfg => (p.1, cfgTriple p.2)) := by
  have h1 : ContDiff ℝ 1 (fun p : Coeff × Cfg => p.1) := contDiff_fst
  have h2 : ContDiff ℝ 1 (fun w : Cfg => cfgTriple w) :=
    (contDiff_cfgA.of_le le_top).prodMk
      ((contDiff_cfgB.of_le le_top).prodMk (contDiff_cfgM.of_le le_top))
  exact h1.prodMk (h2.comp contDiff_snd)

lemma contDiff_stratPsi {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (stratPsi r) := by
  have hdm : ContDiff ℝ 1 (fun p : Coeff × Cfg => dataMap r (p.1, cfgTriple p.2)) :=
    (contDiff_dataMap hr).comp contDiff_cfgTriple
  have hcoll : ContDiff ℝ 1 (fun p : Coeff × Cfg => dataColl (dataMap r (p.1, cfgTriple p.2))) :=
    contDiff_dataColl.comp hdm
  have hya : ContDiff ℝ 1 (fun p : Coeff × Cfg => dataYa (dataMap r (p.1, cfgTriple p.2))) :=
    contDiff_dataYa.comp hdm
  have hyb : ContDiff ℝ 1 (fun p : Coeff × Cfg => dataYb (dataMap r (p.1, cfgTriple p.2))) :=
    contDiff_dataYb.comp hdm
  have hym : ContDiff ℝ 1 (fun p : Coeff × Cfg => dataYm (dataMap r (p.1, cfgTriple p.2))) :=
    contDiff_dataYm.comp hdm
  have hlam : ContDiff ℝ 1 (fun p : Coeff × Cfg => cfgLam p.2) :=
    (contDiff_cfgLam.of_le le_top).comp contDiff_snd
  have hmu : ContDiff ℝ 1 (fun p : Coeff × Cfg => cfgMu p.2) :=
    (contDiff_cfgMu.of_le le_top).comp contDiff_snd
  exact hcoll.prodMk ((hya.sub (hlam.smul hyb)).prodMk (hym.sub (hmu.smul hyb)))

/-! ## Constancy of the data components along the knob directions -/

lemma dataYb_const_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => dataYb (x + s • rpa_dirA a)) 0 0 :=
  hasDerivAt_const_along fun s => by simp [dataYb, dataB, dataP, dataQ, rpa_dirA]

lemma dataYm_const_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => dataYm (x + s • rpa_dirA a)) 0 0 :=
  hasDerivAt_const_along fun s => by simp [dataYm, dataC, dataP, dataQ, rpa_dirA]

lemma dataYa_const_dirC (x : TripleData) (c : Space) :
    HasDerivAt (fun s : ℝ => dataYa (x + s • rpm_dirC c)) 0 0 :=
  hasDerivAt_const_along fun s => by simp [dataYa, dataA, dataP, dataQ, rpm_dirC]

lemma dataYb_const_dirC (x : TripleData) (c : Space) :
    HasDerivAt (fun s : ℝ => dataYb (x + s • rpm_dirC c)) 0 0 :=
  hasDerivAt_const_along fun s => by simp [dataYb, dataB, dataP, dataQ, rpm_dirC]

lemma fderiv_PhiPsi_dirM (lam mu : ℝ) (X : TripleData) (u : Space) :
    (fderiv ℝ (PhiPsi lam mu) X) (rpa_dirM u)
      = (cross3 u (dataP X - dataQ X), 0, 0) := by
  have hdiff : DifferentiableAt ℝ (PhiPsi lam mu) X :=
    ((contDiff_PhiPsi lam mu).differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := PhiPsi lam mu) (p := X) (e := rpa_dirM u) hdiff
  have h2 : HasDerivAt (fun s : ℝ => PhiPsi lam mu (X + s • rpa_dirM u))
      (cross3 u (dataP X - dataQ X), 0, 0) 0 := by
    have hC := rpa_hasDerivAt_dataColl_dirM X u
    have hA := rpa_hasDerivAt_dataYa_dirM X u
    have hB := rpb_hasDerivAt_dataYb_dirM X u
    have hM := rpm_hasDerivAt_dataYm_dirM X u
    have h2a := hA.sub (hB.const_smul lam)
    have h2b := hM.sub (hB.const_smul mu)
    have := hC.prodMk (h2a.prodMk h2b)
    simpa [PhiPsi, sub_zero, smul_zero] using this
  exact h1.unique h2

lemma fderiv_PhiPsi_dirA (lam mu : ℝ) (X : TripleData) (v : Space) :
    (fderiv ℝ (PhiPsi lam mu) X) (rpa_dirA v)
      = (0, cross3 v (dataP X - dataQ X), 0) := by
  have hdiff : DifferentiableAt ℝ (PhiPsi lam mu) X :=
    ((contDiff_PhiPsi lam mu).differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := PhiPsi lam mu) (p := X) (e := rpa_dirA v) hdiff
  have h2 : HasDerivAt (fun s : ℝ => PhiPsi lam mu (X + s • rpa_dirA v))
      (0, cross3 v (dataP X - dataQ X), 0) 0 := by
    have hC := rpa_hasDerivAt_dataColl_dirA X v
    have hA := rpa_hasDerivAt_dataYa_dirA X v
    have hB := dataYb_const_dirA X v
    have hM := dataYm_const_dirA X v
    have h2a := hA.sub (hB.const_smul lam)
    have h2b := hM.sub (hB.const_smul mu)
    have := hC.prodMk (h2a.prodMk h2b)
    simpa [PhiPsi, sub_zero, smul_zero] using this
  exact h1.unique h2

lemma fderiv_PhiPsi_dirC (lam mu : ℝ) (X : TripleData) (w : Space) :
    (fderiv ℝ (PhiPsi lam mu) X) (rpm_dirC w)
      = (0, 0, cross3 w (dataP X - dataQ X)) := by
  have hdiff : DifferentiableAt ℝ (PhiPsi lam mu) X :=
    ((contDiff_PhiPsi lam mu).differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := PhiPsi lam mu) (p := X) (e := rpm_dirC w) hdiff
  have h2 : HasDerivAt (fun s : ℝ => PhiPsi lam mu (X + s • rpm_dirC w))
      (0, 0, cross3 w (dataP X - dataQ X)) 0 := by
    have hC := rpm_hasDerivAt_dataColl_dirC X w
    have hA := dataYa_const_dirC X w
    have hB := dataYb_const_dirC X w
    have hM := rpm_hasDerivAt_dataYm_dirC X w
    have h2a := hA.sub (hB.const_smul lam)
    have h2b := hM.sub (hB.const_smul mu)
    have := hC.prodMk (h2a.prodMk h2b)
    simpa [PhiPsi, sub_zero, smul_zero] using this
  exact h1.unique h2

/-! ## The coefficientwise derivative of each stratum, and its rank -/

open ContinuousLinearMap in
lemma fderiv_slice_eq_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : Coeff × W → F} (hΦ : ContDiff ℝ 1 Φ) (p : Coeff × W) :
    fderiv ℝ (fun c : Coeff => Φ (c, p.2)) p.1
      = (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ Coeff W) := by
  have h1 := (hΦ.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt.comp p.1
    (hasFDerivAt_prodMk_left p.1 p.2)
  simpa [Function.comp_def] using h1.fderiv

lemma range_fderiv_slice_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : Coeff × W → F} (hΦ : ContDiff ℝ 1 Φ) (p : Coeff × W) :
    (fderiv ℝ (fun c : Coeff => Φ (c, p.2)) p.1).range ≤ (fderiv ℝ Φ p).range := by
  rw [fderiv_slice_eq_comp hΦ p]
  exact LinearMap.range_comp_le_range _ _

/-! ## The coefficientwise derivative of each stratum and its rank -/

lemma fderiv_stratA_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff) :
    fderiv ℝ (fun c : Coeff => stratA r (c, w)) c₀
      = (fderiv ℝ patchA (dataMap r (c₀, w))).comp (jetLin w) := by
  have h := (rpa_contDiff_patchA.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt.comp c₀
    (hasFDerivAt_dataMap_slice hr w c₀)
  simpa [stratA, Function.comp_def] using h.fderiv

lemma fderiv_stratB_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff) :
    fderiv ℝ (fun c : Coeff => stratB r (c, w)) c₀
      = (fderiv ℝ patchB (dataMap r (c₀, w))).comp (jetLin w) := by
  have h := (rpb_contDiff_patchB.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt.comp c₀
    (hasFDerivAt_dataMap_slice hr w c₀)
  simpa [stratB, Function.comp_def] using h.fderiv

lemma fderiv_stratM_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff) :
    fderiv ℝ (fun c : Coeff => stratM r (c, w)) c₀
      = (fderiv ℝ patchM (dataMap r (c₀, w))).comp (jetLin w) := by
  have h := (rpm_contDiff_patchM.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt.comp c₀
    (hasFDerivAt_dataMap_slice hr w c₀)
  simpa [stratM, Function.comp_def] using h.fderiv

lemma fderiv_stratPsi_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : Cfg) (c₀ : Coeff) :
    fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀
      = (fderiv ℝ (PhiPsi (cfgLam w) (cfgMu w)) (dataMap r (c₀, cfgTriple w))).comp
          (jetLin (cfgTriple w)) := by
  have h := ((contDiff_PhiPsi (cfgLam w) (cfgMu w)).contDiffAt.hasStrictFDerivAt
      (by norm_num)).hasFDerivAt.comp c₀
    (hasFDerivAt_dataMap_slice hr (cfgTriple w) c₀)
  simpa [stratPsi, PhiPsi, cfgTriple, Function.comp_def] using h.fderiv

theorem rank_stratA_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff)
    (hJ : Function.Surjective (jetLin w))
    (hd : dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)) ≠ 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => stratA r (c, w)) c₀).toLinearMap)) := by
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpa_dirM u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirM u)),
      fun u => Classical.choose_spec (hJ (rpa_dirM u))⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpa_dirA u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirA u)),
      fun u => Classical.choose_spec (hJ (rpa_dirA u))⟩
  have hD := fderiv_stratA_slice hr w c₀
  have h₁ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratA r (c, w)) c₀) (δ₁ u)
      = (rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u, 0) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₁ u, rpa_fderiv_dirM]
    simp only [rpa_crossLin_apply]
  have h₂ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratA r (c, w)) c₀) (δ₂ u)
      = (0, rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₂ u, rpa_fderiv_dirA]
    simp only [rpa_crossLin_apply]
  have hres := two_knob_rank
    (D := (fderiv ℝ (fun c : Coeff => stratA r (c, w)) c₀).toLinearMap)
    (f := rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)))) δ₁ δ₂ h₁ h₂
  rw [rpa_finrank_range_crossLin hd] at hres
  omega

theorem rank_stratB_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff)
    (hJ : Function.Surjective (jetLin w))
    (hd : dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)) ≠ 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => stratB r (c, w)) c₀).toLinearMap)) := by
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpa_dirM u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirM u)),
      fun u => Classical.choose_spec (hJ (rpa_dirM u))⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpb_dirB u :=
    ⟨fun u => Classical.choose (hJ (rpb_dirB u)),
      fun u => Classical.choose_spec (hJ (rpb_dirB u))⟩
  have hD := fderiv_stratB_slice hr w c₀
  have h₁ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratB r (c, w)) c₀) (δ₁ u)
      = (rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u, 0) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₁ u, rpb_fderiv_dirM]
    simp only [rpa_crossLin_apply]
  have h₂ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratB r (c, w)) c₀) (δ₂ u)
      = (0, rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₂ u, rpb_fderiv_dirB]
    simp only [rpa_crossLin_apply]
  have hres := two_knob_rank
    (D := (fderiv ℝ (fun c : Coeff => stratB r (c, w)) c₀).toLinearMap)
    (f := rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)))) δ₁ δ₂ h₁ h₂
  rw [rpa_finrank_range_crossLin hd] at hres
  omega

theorem rank_stratM_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : ℝ × ℝ × ℝ) (c₀ : Coeff)
    (hJ : Function.Surjective (jetLin w))
    (hd : dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)) ≠ 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => stratM r (c, w)) c₀).toLinearMap)) := by
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpa_dirM u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirM u)),
      fun u => Classical.choose_spec (hJ (rpa_dirM u))⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin w (δ u) = rpm_dirC u :=
    ⟨fun u => Classical.choose (hJ (rpm_dirC u)),
      fun u => Classical.choose_spec (hJ (rpm_dirC u))⟩
  have hD := fderiv_stratM_slice hr w c₀
  have h₁ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratM r (c, w)) c₀) (δ₁ u)
      = (rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u, 0) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₁ u, rpm_fderiv_dirM]
    simp only [rpa_crossLin_apply]
  have h₂ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratM r (c, w)) c₀) (δ₂ u)
      = (0, rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w))) u) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₂ u, rpm_fderiv_dirC]
    simp only [rpa_crossLin_apply]
  have hres := two_knob_rank
    (D := (fderiv ℝ (fun c : Coeff => stratM r (c, w)) c₀).toLinearMap)
    (f := rpa_crossLin (dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)))) δ₁ δ₂ h₁ h₂
  rw [rpa_finrank_range_crossLin hd] at hres
  omega

theorem rank_stratPsi_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : Cfg) (c₀ : Coeff)
    (hJ : Function.Surjective (jetLin (cfgTriple w)))
    (hd : dataP (dataMap r (c₀, cfgTriple w)) - dataQ (dataMap r (c₀, cfgTriple w)) ≠ 0) :
    6 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀).toLinearMap)) := by
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin (cfgTriple w) (δ u) = rpa_dirM u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirM u)),
      fun u => Classical.choose_spec (hJ (rpa_dirM u))⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin (cfgTriple w) (δ u) = rpa_dirA u :=
    ⟨fun u => Classical.choose (hJ (rpa_dirA u)),
      fun u => Classical.choose_spec (hJ (rpa_dirA u))⟩
  obtain ⟨δ₃, hδ₃⟩ : ∃ δ : Space → Coeff, ∀ u, jetLin (cfgTriple w) (δ u) = rpm_dirC u :=
    ⟨fun u => Classical.choose (hJ (rpm_dirC u)),
      fun u => Classical.choose_spec (hJ (rpm_dirC u))⟩
  have hD := fderiv_stratPsi_slice hr w c₀
  have h₁ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀) (δ₁ u)
      = (rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) -
          dataQ (dataMap r (c₀, cfgTriple w))) u, 0, 0) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₁ u, fderiv_PhiPsi_dirM]
    simp only [rpa_crossLin_apply]
  have h₂ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀) (δ₂ u)
      = (0, rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) -
          dataQ (dataMap r (c₀, cfgTriple w))) u, 0) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₂ u, fderiv_PhiPsi_dirA]
    simp only [rpa_crossLin_apply]
  have h₃ : ∀ u : Space, (fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀) (δ₃ u)
      = (0, 0, rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) -
          dataQ (dataMap r (c₀, cfgTriple w))) u) := by
    intro u
    rw [hD, ContinuousLinearMap.comp_apply, hδ₃ u, fderiv_PhiPsi_dirC]
    simp only [rpa_crossLin_apply]
  have hres := three_knob_rank
    (D := (fderiv ℝ (fun c : Coeff => stratPsi r (c, w)) c₀).toLinearMap)
    (f₁ := rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) - dataQ (dataMap r (c₀, cfgTriple w))))
    (f₂ := rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) - dataQ (dataMap r (c₀, cfgTriple w))))
    (f₃ := rpa_crossLin (dataP (dataMap r (c₀, cfgTriple w)) - dataQ (dataMap r (c₀, cfgTriple w))))
    δ₁ δ₂ δ₃ h₁ h₂ h₃
  rw [rpa_finrank_range_crossLin hd] at hres
  omega

/-! ## The richness hypothesis, the chord bound, and the bad sets -/

/-- The hypothesis supplied by the jet-surjectivity of the perturbation family. -/
def JetSurj : Prop :=
  ∀ (a b m : ℝ), a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
    m ∈ Set.Icc 0 (2 * Real.pi) →
    (1 - Real.cos (a - b)) * (1 - Real.cos (a - m)) * (1 - Real.cos (b - m)) ≠ 0 →
    Function.Surjective (jetLin (a, b, m))

lemma cos_ne_one_of_csep_pos {a b : ℝ} (ha : a ∈ Set.Icc 0 (2 * Real.pi))
    (hb : b ∈ Set.Icc 0 (2 * Real.pi)) (h : 0 < csep a b) : 1 - Real.cos (a - b) ≠ 0 := by
  intro hcon
  have hcos : Real.cos (a - b) = 1 := by linarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (a - b)).mp hcos
  have hmin : 0 < min |a - b| (2 * Real.pi - |a - b|) := by simpa [csep] using h
  have h1 : 0 < |a - b| := lt_of_lt_of_le hmin (min_le_left _ _)
  have h2 : |a - b| < 2 * Real.pi := by
    have := lt_of_lt_of_le hmin (min_le_right _ _)
    linarith
  have hn0 : n ≠ 0 := by
    intro h0
    have hzero : a - b = 0 := by rw [← hn, h0]; simp
    rw [hzero, abs_zero] at h1
    exact lt_irrefl (0:ℝ) h1
  have habs : |a - b| = |((n : ℤ) : ℝ)| * (2 * Real.pi) := by
    rw [← hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hone : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have : 2 * Real.pi ≤ |a - b| := by
    rw [habs]
    nlinarith [hone, Real.pi_pos]
  linarith

lemma jetLin_surjective_of_tripleSet {k : ℕ} {w : ℝ × ℝ × ℝ} (hJ : JetSurj)
    (hw : w ∈ tripleSet k) : Function.Surjective (jetLin w) := by
  obtain ⟨ha, hb, hm, hab, ham, hbm⟩ := hw
  exact hJ w.1 w.2.1 w.2.2 ha hb hm
    (mul_ne_zero (mul_ne_zero (cos_ne_one_of_csep_pos ha hb (lt_of_lt_of_le (by positivity) hab))
      (cos_ne_one_of_csep_pos ha hm (lt_of_lt_of_le (by positivity) ham)))
      (cos_ne_one_of_csep_pos hb hm (lt_of_lt_of_le (by positivity) hbm)))

lemma jetLin_surjective_of_Kn {k : ℕ} {L : ℝ} {w : Cfg} (hJ : JetSurj) (hw : w ∈ Kn k L) :
    Function.Surjective (jetLin (cfgTriple w)) := by
  obtain ⟨-, -, ha, hb, hm, hab, ham, hbm⟩ := Kn_spec k L hw
  exact hJ (cfgA w) (cfgB w) (cfgM w) ha hb hm
    (mul_ne_zero (mul_ne_zero (cos_ne_one_of_csep_pos ha hb (lt_of_lt_of_le (by positivity) hab))
      (cos_ne_one_of_csep_pos ha hm (lt_of_lt_of_le (by positivity) ham)))
      (cos_ne_one_of_csep_pos hb hm (lt_of_lt_of_le (by positivity) hbm)))

/-- Distinct points of the parameter box separated in the circular metric have distinct images
under a knot. -/
lemma pertV_ne_of_csep_pos {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff}
    (hS : IsSmoothKnot (pertV r c)) :
    ∀ {s t : ℝ}, s ∈ Set.Icc 0 (2 * Real.pi) → t ∈ Set.Icc 0 (2 * Real.pi) →
      0 < csep s t → pertV r c s ≠ pertV r c t := by
  have hper : Function.Periodic (pertV r c) (2 * Real.pi) := by
    simpa [period] using pertV_periodic hr c
  intro s t hs ht hst hcon
  have hra := red_ne_of_csep_pos hs ht hst
  have h1 : pertV r c s = pertV r c (red s) := (pertV_red hper hs).symm
  have h2 : pertV r c t = pertV r c (red t) := (pertV_red hper ht).symm
  exact hra (hS.injective_on_period (red_mem_Ico hs) (red_mem_Ico ht) (by rw [← h1, ← h2, hcon]))

lemma chord_ne_zero_of {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff}
    (hS : IsSmoothKnot (pertV r c)) {a b m : ℝ}
    (ha : a ∈ Set.Icc 0 (2 * Real.pi)) (hb : b ∈ Set.Icc 0 (2 * Real.pi))
    (hm : m ∈ Set.Icc 0 (2 * Real.pi))
    (hab : 0 < csep a b) (ham : 0 < csep a m) (hbm : 0 < csep b m) :
    (pertV r c a - pertV r c b ≠ 0) ∧ (pertV r c a - pertV r c m ≠ 0) ∧
      (pertV r c b - pertV r c m ≠ 0) :=
  ⟨sub_ne_zero.mpr (pertV_ne_of_csep_pos hr hS ha hb hab),
   sub_ne_zero.mpr (pertV_ne_of_csep_pos hr hS ha hm ham),
   sub_ne_zero.mpr (pertV_ne_of_csep_pos hr hS hb hm hbm)⟩

/-- The three linear strata, indexed by `Fin 3`. -/
def stratABC (r : ℝ → Space) (j : Fin 3) : Coeff × (ℝ × ℝ × ℝ) → Space × Space :=
  match j with
  | ⟨0, _⟩ => stratA r
  | ⟨1, _⟩ => stratB r
  | _ => stratM r

lemma contDiff_stratABC {r : ℝ → Space} (hr : IsSmoothKnot r) (j : Fin 3) :
    ContDiff ℝ 1 (stratABC r j) := by
  fin_cases j
  · exact contDiff_stratA hr
  · exact contDiff_stratB hr
  · exact contDiff_stratM hr

theorem rank_stratABC_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (j : Fin 3)
    (w : ℝ × ℝ × ℝ) (c₀ : Coeff) (hJ : Function.Surjective (jetLin w))
    (hd : dataP (dataMap r (c₀, w)) - dataQ (dataMap r (c₀, w)) ≠ 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => stratABC r j (c, w)) c₀).toLinearMap)) :=
  match j with
  | ⟨0, _⟩ => rank_stratA_slice hr w c₀ hJ hd
  | ⟨1, _⟩ => rank_stratB_slice hr w c₀ hJ hd
  | ⟨2, _⟩ => rank_stratM_slice hr w c₀ hJ hd

/-- The bad set of the linear stratum `j` at separation scale `k`. -/
def badABC (r : ℝ → Space) (r₀ : ℝ) (i : ℕ × Fin 3) : Set Coeff :=
  {c : Coeff | c ∈ Kv r₀ ∧ ∃ w ∈ tripleSet i.1, stratABC r i.2 (c, w) = 0}

/-- The bad set of the parallel stratum at separation scale `k` and multiplier bound `L`. -/
def badPsi (r : ℝ → Space) (r₀ : ℝ) (i : ℕ × ℕ) : Set Coeff :=
  {c : Coeff | c ∈ Kv r₀ ∧ ∃ w ∈ Kn i.1 (i.2 : ℝ), stratPsi r (c, w) = 0}

/-- The bad set of the inflection stratum. -/
def badInfl (r : ℝ → Space) (r₀ : ℝ) : Set Coeff :=
  {c : Coeff | c ∈ Kv r₀ ∧ ∃ t ∈ Set.Icc 0 (2 * Real.pi),
    cross3 (pertVelV r c t) (deriv (pertVelV r c) t) = 0}

lemma isCompact_badFst {W : Type*} [TopologicalSpace W] {K : Set W} (hK : IsCompact K)
    {F : Type*} [TopologicalSpace F] [Zero F] [T1Space F] {Ψ : Coeff × W → F}
    (hΨ : Continuous Ψ) (r₀ : ℝ) :
    IsCompact ((Kv r₀ ×ˢ K) ∩ Ψ ⁻¹' {0}) :=
  (isCompact_Kv r₀).prod hK |>.inter_right (isClosed_singleton.preimage hΨ)

lemma isClosed_badSet {W : Type*} [TopologicalSpace W] {K : Set W} (hK : IsCompact K)
    {F : Type*} [TopologicalSpace F] [Zero F] [T1Space F] {Ψ : Coeff × W → F}
    (hΨ : Continuous Ψ) (r₀ : ℝ) :
    IsClosed {c : Coeff | c ∈ Kv r₀ ∧ ∃ w ∈ K, Ψ (c, w) = 0} := by
  have hcomp := isCompact_badFst hK hΨ r₀
  have himg : Prod.fst '' ((Kv r₀ ×ˢ K) ∩ Ψ ⁻¹' {0})
      = {c : Coeff | c ∈ Kv r₀ ∧ ∃ w ∈ K, Ψ (c, w) = 0} := by
    ext c
    constructor
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩
      exact ⟨hp1, p.2, hp2, hp3⟩
    · rintro ⟨hc, w, hw, h0⟩
      exact ⟨(c, w), ⟨⟨hc, hw⟩, h0⟩, rfl⟩
  rw [← himg]
  exact (hcomp.image continuous_fst).isClosed

theorem badABC_empty_interior {r : ℝ → Space} {r₀ : ℝ} (hr : IsSmoothKnot r)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c)) (hJ : JetSurj) (i : ℕ × Fin 3) :
    interior (badABC r r₀ i) = ∅ := by
  refine interior_zeroSet_projection_empty_of_rank (hΨ := contDiff_stratABC hr i.2)
    (hKv := isCompact_Kv r₀) (hK := isCompact_tripleSet i.1) ?_
  intro p hp hp0
  have hpcKv : p.1 ∈ Kv r₀ := hp.1
  have hpwK : p.2 ∈ tripleSet i.1 := hp.2
  have hJw := jetLin_surjective_of_tripleSet hJ hpwK
  obtain ⟨ha, hb, hm, hab, ham, hbm⟩ := hpwK
  have hchord := chord_ne_zero_of hr (hS p.1 hpcKv) ha hb hm
    (lt_of_lt_of_le (by positivity) hab) (lt_of_lt_of_le (by positivity) ham)
    (lt_of_lt_of_le (by positivity) hbm)
  have hd : dataP (dataMap r (p.1, p.2)) - dataQ (dataMap r (p.1, p.2)) ≠ 0 := by
    simpa using hchord.1
  have hrank := rank_stratABC_slice hr i.2 p.2 p.1 hJw hd
  have hle := range_fderiv_slice_le (contDiff_stratABC hr i.2) p
  have hmono := Submodule.finrank_mono hle
  have hfin : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by
    simp [Module.finrank_prod, Module.finrank_self]
  omega

theorem badPsi_empty_interior {r : ℝ → Space} {r₀ : ℝ} (hr : IsSmoothKnot r)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c)) (hJ : JetSurj) (i : ℕ × ℕ) :
    interior (badPsi r r₀ i) = ∅ := by
  refine interior_zeroSet_projection_empty_of_rank (hΨ := contDiff_stratPsi hr)
    (hKv := isCompact_Kv r₀) (hK := isCompact_Kn i.1 (i.2 : ℝ)) ?_
  intro p hp hp0
  have hpcKv : p.1 ∈ Kv r₀ := hp.1
  have hpwK : p.2 ∈ Kn i.1 (i.2 : ℝ) := hp.2
  have hJw := jetLin_surjective_of_Kn hJ hpwK
  obtain ⟨-, -, ha, hb, hm, hab, ham, hbm⟩ := Kn_spec i.1 (i.2 : ℝ) hpwK
  have hchord := chord_ne_zero_of hr (hS p.1 hpcKv) ha hb hm
    (lt_of_lt_of_le (by positivity) hab) (lt_of_lt_of_le (by positivity) ham)
    (lt_of_lt_of_le (by positivity) hbm)
  have hd : dataP (dataMap r (p.1, cfgTriple p.2)) - dataQ (dataMap r (p.1, cfgTriple p.2))
      ≠ 0 := by
    simpa [cfgTriple] using hchord.1
  have hrank := rank_stratPsi_slice hr p.2 p.1 hJw hd
  have hle := range_fderiv_slice_le (contDiff_stratPsi hr) p
  have hmono := Submodule.finrank_mono hle
  have hfin : Module.finrank ℝ Cfg = 5 := finrank_euclideanSpace_fin
  omega

/-! ## Nonvanishing curvature and its preservation -/

/-- Two vectors of `Space` are linearly independent iff their cross product is nonzero. -/
lemma linearIndependent_pair_iff_cross3_ne_zero (v a : Space) :
    LinearIndependent ℝ ![v, a] ↔ cross3 v a ≠ 0 := by
  constructor
  · intro hLI hcross
    rcases (cross3_eq_zero_iff_smul_local (u := v) (v := a)).mp hcross with h | ⟨t, ht⟩
    · exact hLI.ne_zero 0 (by simpa using h)
    · have h2 : (∑ i : Fin 2, (![t, -1] : Fin 2 → ℝ) i • ![v, a] i) = 0 := by
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [ht]
        module
      have h3 := (Fintype.linearIndependent_iff (R := ℝ) (v := ![v, a])).mp hLI ![t, -1] h2 1
      norm_num at h3
  · intro hne
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum0 : g 0 • v + g 1 • a = 0 := by
      simpa [Fin.sum_univ_two] using hg
    have hsum1 : g 1 • a + g 0 • v = 0 := by rw [add_comm]; exact hsum0
    fin_cases i
    · by_contra h0
      have h1 : g 0 • v = -(g 1 • a) := by
        rw [eq_neg_iff_add_eq_zero]; exact hsum0
      have hc := congrArg (fun x : Space => cross3 x a) h1
      rw [cross3_smul_left, cross3_neg_left, cross3_smul_left, cross3_self, smul_zero,
        neg_zero] at hc
      exact hne ((smul_eq_zero.mp hc).resolve_left h0)
    · by_contra h1
      have h2 : g 1 • a = -(g 0 • v) := by
        rw [eq_neg_iff_add_eq_zero]; exact hsum1
      have hc := congrArg (fun x : Space => cross3 v x) h2
      rw [cross3_smul_right, cross3_neg_right, cross3_smul_right, cross3_self, smul_zero,
        neg_zero] at hc
      exact hne ((smul_eq_zero.mp hc).resolve_left h1)

lemma periodic_velocity {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) (2 * Real.pi) := by
  simpa [velocity, period] using periodic_deriv' hr.periodic

/-- The perturbed velocity, as a function of `(c, t)`. -/
def velPair (r : ℝ → Space) : Coeff × ℝ → Space := fun q => pertVelV r q.1 q.2

lemma contDiff_velPair {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) : ContDiff ℝ ⊤ (velPair r) :=
  contDiff_pertVelV_joint hr

lemma hasFDerivAt_velPair {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (q : Coeff × ℝ) :
    HasFDerivAt (velPair r) (fderiv ℝ (velPair r) q) q :=
  ((contDiff_velPair hr).contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt

lemma deriv_velPair {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (c : Coeff) (t : ℝ) :
    deriv (fun s : ℝ => velPair r (c, s)) t = fderiv ℝ (velPair r) (c, t) (0, 1) := by
  have h2 : HasFDerivAt (fun s : ℝ => (c, s)) (ContinuousLinearMap.inr ℝ Coeff ℝ) t :=
    hasFDerivAt_prodMk_right c t
  have h := (hasFDerivAt_velPair hr (c, t)).comp t h2
  have h4 : HasDerivAt (fun s : ℝ => velPair r (c, s))
      ((fderiv ℝ (velPair r) (c, t)) (0, 1)) t := by
    have := h.hasDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.compSL_apply] using this
  exact h4.deriv

lemma continuous_deriv_velPair {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    Continuous (fun q : Coeff × ℝ => deriv (fun s : ℝ => velPair r (q.1, s)) q.2) := by
  have hfun : (fun q : Coeff × ℝ => deriv (fun s : ℝ => velPair r (q.1, s)) q.2)
      = fun q => fderiv ℝ (velPair r) q (0, 1) := funext fun q => deriv_velPair hr q.1 q.2
  rw [hfun]
  exact ((contDiff_velPair hr).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The curvature functional of the perturbation family. -/
def curvFun (r : ℝ → Space) : Coeff × ℝ → Space :=
  fun q => cross3 (velPair r q) (deriv (fun s : ℝ => velPair r (q.1, s)) q.2)

lemma continuous_curvFun {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) : Continuous (curvFun r) := by
  have hcross : Continuous (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).continuous
  exact hcross.comp (((contDiff_velPair hr).continuous).prodMk (continuous_deriv_velPair hr))

lemma pertV_zero (r : ℝ → Space) : pertV r (0 : Coeff) = r := by
  funext t
  simp [pertV, perturb, perturbCorr]

lemma velPair_zero {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    (fun t : ℝ => velPair r ((0 : Coeff), t)) = velocity r := by
  funext t
  show pertVelV r 0 t = velocity r t
  rw [← velocity_pertV hr (0 : Coeff) t, pertV_zero]

lemma accPair_zero {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    (fun t : ℝ => deriv (fun s : ℝ => velPair r ((0 : Coeff), s)) t) = deriv (velocity r) := by
  rw [velPair_zero hr]

lemma pertVelV_zero {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (t : ℝ) :
    pertVelV r (0 : Coeff) t = velocity r t := by
  rw [← velocity_pertV hr (0 : Coeff) t, pertV_zero]

lemma curvFun_zero {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (t : ℝ) :
    curvFun r ((0 : Coeff), t) = cross3 (velocity r t) (deriv (velocity r) t) := by
  have hf : (fun s : ℝ => velPair r ((0 : Coeff), s)) = velocity r := by
    funext s; exact pertVelV_zero hr s
  have hp : velPair r ((0 : Coeff), t) = velocity r t := pertVelV_zero hr t
  simp only [curvFun, hp, hf]

/-- **Nonvanishing curvature is stable under the perturbation family.** -/
theorem exists_curvPreserve_bound {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hnoinfl : ∀ t, cross3 (velocity r t) (deriv (velocity r) t) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Kv ρ, ∀ t : ℝ,
      cross3 (pertVelV r c t) (deriv (fun s : ℝ => pertVelV r c s) t) ≠ 0 := by
  classical
  have hK : IsCompact (Kv (1:ℝ) ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) :=
    (isCompact_Kv 1).prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous (continuous_curvFun hr.smooth).continuousOn
  have hcont0 : Continuous (fun t : ℝ => cross3 (velocity r t) (deriv (velocity r) t)) := by
    have hvel : Continuous (velocity r) := by
      show Continuous (deriv r); exact hr.smooth.continuous_deriv le_top
    have hacc : Continuous (fun t : ℝ => deriv (velocity r) t) := by
      show Continuous (deriv (deriv r))
      exact (hr.smooth.deriv' (n := ⊤)).continuous_deriv le_top
    have hcross : Continuous (fun p : Space × Space => cross3 p.1 p.2) := by
      simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).continuous
    exact hcross.comp (hvel.prodMk hacc)
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨0, le_rfl, by positivity⟩ : (Set.Icc (0:ℝ) (2 * Real.pi)).Nonempty)
    hcont0.norm.continuousOn
  have hμ : 0 < ‖curvFun r ((0 : Coeff), t₀)‖ := by
    rw [curvFun_zero hr.smooth t₀]
    exact norm_pos_iff.mpr (hnoinfl t₀)
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc)
    (‖curvFun r ((0 : Coeff), t₀)‖ / 2) (by linarith)
  refine ⟨min (δ / 2) 1, lt_min (by positivity) one_pos, ?_⟩
  intro c hc t
  have hcn : ‖c‖ ≤ min (δ / 2) 1 := by
    rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc; exact hc
  have hc1 : ‖c‖ ≤ 1 := le_trans hcn (min_le_right _ _)
  have hcδ : ‖c‖ ≤ δ / 2 := le_trans hcn (min_le_left _ _)
  have hmemC : ∀ t' ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      (c, t') ∈ Kv (1:ℝ) ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) :=
    fun t' ht' => ⟨by rw [Kv, Metric.mem_closedBall, dist_zero_right]; exact hc1, ht'⟩
  have hmemO : ∀ t' ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      ((0 : Coeff), t') ∈ Kv (1:ℝ) ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) :=
    fun t' ht' => ⟨by rw [Kv, Metric.mem_closedBall, dist_zero_right]; simp, ht'⟩
  have hstep : ∀ t' ∈ Set.Icc (0:ℝ) (2 * Real.pi), curvFun r (c, t') ≠ 0 := by
    intro t' ht'
    have hdist : dist (c, t') ((0 : Coeff), t') < δ := by
      have h1 : (c, t') - ((0 : Coeff), t') = (c, (0:ℝ)) := by
        ext <;> simp
      rw [dist_eq_norm, h1, Prod.norm_mk]
      simp only [norm_zero, max_eq_left (norm_nonneg c)]
      linarith
    have h2 := hδ (c, t') (hmemC t' ht') ((0 : Coeff), t') (hmemO t' ht') hdist
    intro hzero
    have h3 : ‖curvFun r ((0 : Coeff), t')‖ < ‖curvFun r ((0 : Coeff), t₀)‖ / 2 := by
      calc ‖curvFun r ((0 : Coeff), t')‖
          = dist (curvFun r ((0 : Coeff), t')) (curvFun r (c, t')) := by
            rw [hzero, dist_eq_norm, sub_zero]
        _ = dist (curvFun r (c, t')) (curvFun r ((0 : Coeff), t')) := dist_comm _ _
        _ < ‖curvFun r ((0 : Coeff), t₀)‖ / 2 := h2
    have h4 : ‖curvFun r ((0 : Coeff), t₀)‖ ≤ ‖curvFun r ((0 : Coeff), t')‖ := by
      rw [curvFun_zero hr.smooth t₀, curvFun_zero hr.smooth t']
      exact hmin ht'
    linarith
  -- periodicity in `t`
  have hperV : Function.Periodic (pertV r c) (2 * Real.pi) := by
    simpa [period] using pertV_periodic hr c
  have hper1 : Function.Periodic (fun s : ℝ => pertVelV r c s) (2 * Real.pi) := by
    have hv : (fun s : ℝ => pertVelV r c s) = velocity (pertV r c) :=
      funext fun s => (velocity_pertV hr.smooth c s).symm
    rw [hv]
    exact periodic_deriv' hperV
  have hper2 : Function.Periodic (fun s : ℝ => deriv (fun u : ℝ => pertVelV r c u) s) (2 * Real.pi) :=
    periodic_deriv' hper1
  have hperC : Function.Periodic (fun s : ℝ => cross3 (pertVelV r c s)
      (deriv (fun u : ℝ => pertVelV r c u) s)) (2 * Real.pi) :=
    fun s => by simp only [hper1 s, hper2 s]
  obtain ⟨t', ht'I, ht'eq⟩ := hperC.exists_mem_Ico (by positivity : (0:ℝ) < 2 * Real.pi) t 0
  have ht' : t' ∈ Set.Icc (0:ℝ) (2 * Real.pi) := Set.Ico_subset_Icc_self (by simpa using ht'I)
  rw [ht'eq]
  exact hstep t' ht'

/-! ## The identification of the strata with the geometric data -/

lemma stratA_apply (r : ℝ → Space) (c : Coeff) (w : ℝ × ℝ × ℝ) :
    stratA r (c, w) =
      (collinearityValue (pertV r c) w.1 w.2.1 w.2.2,
        cross3 (pertVelV r c w.1) (pertV r c w.1 - pertV r c w.2.1)) := by
  simp [stratA, patchA, dataColl, dataYa, collinearityValue_eq, dataMap, dataP, dataQ, dataM, dataA, dataB, dataC]

lemma stratB_apply (r : ℝ → Space) (c : Coeff) (w : ℝ × ℝ × ℝ) :
    stratB r (c, w) =
      (collinearityValue (pertV r c) w.1 w.2.1 w.2.2,
        cross3 (pertVelV r c w.2.1) (pertV r c w.1 - pertV r c w.2.1)) := by
  simp [stratB, patchB, dataColl, dataYb, collinearityValue_eq, dataMap, dataP, dataQ, dataM, dataA, dataB, dataC]

lemma stratM_apply (r : ℝ → Space) (c : Coeff) (w : ℝ × ℝ × ℝ) :
    stratM r (c, w) =
      (collinearityValue (pertV r c) w.1 w.2.1 w.2.2,
        cross3 (pertVelV r c w.2.2) (pertV r c w.1 - pertV r c w.2.1)) := by
  simp [stratM, patchM, dataColl, dataYm, collinearityValue_eq, dataMap, dataP, dataQ, dataM, dataA, dataB, dataC]

lemma cfgTriple_mkCfg (l mu a b m : ℝ) : cfgTriple (mkCfg l mu a b m) = (a, b, m) := by
  simp [cfgTriple, cfgA_mkCfg, cfgB_mkCfg, cfgM_mkCfg]

lemma stratPsi_apply (r : ℝ → Space) (c : Coeff) (w : Cfg) :
    stratPsi r (c, w) = (collinearityValue (pertV r c) (cfgA w) (cfgB w) (cfgM w),
      cross3 (pertVelV r c (cfgA w)) (pertV r c (cfgA w) - pertV r c (cfgB w)) -
        cfgLam w • cross3 (pertVelV r c (cfgB w)) (pertV r c (cfgA w) - pertV r c (cfgB w)),
      cross3 (pertVelV r c (cfgM w)) (pertV r c (cfgA w) - pertV r c (cfgB w)) -
        cfgMu w • cross3 (pertVelV r c (cfgB w)) (pertV r c (cfgA w) - pertV r c (cfgB w))) := by
  simp [stratPsi, PhiPsi, dataColl, dataYa, dataYb, dataYm, collinearityValue_eq, dataMap,
    dataP, dataQ, dataM, dataA, dataB, dataC, cfgTriple]

/-! ## Baire: a good coefficient vector -/

theorem exists_good_coeff {r₁ : ℝ → Space} {r₀ : ℝ} (hr : IsSmoothKnot r₁) (hr₀ : 0 < r₀)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r₁ c)) (hJ : JetSurj) :
    ∃ c ∈ interior (Kv r₀),
      (∀ (j : Fin 3) (k : ℕ) (w : ℝ × ℝ × ℝ), w ∈ tripleSet k → stratABC r₁ j (c, w) ≠ 0) ∧
      (∀ (k L : ℕ) (w : Cfg), w ∈ Kn k L → stratPsi r₁ (c, w) ≠ 0) := by
  classical
  set bad : ((ℕ × Fin 3) ⊕ (ℕ × ℕ)) → Set Coeff := fun i =>
    match i with
    | Sum.inl j => badABC r₁ r₀ j
    | Sum.inr j => badPsi r₁ r₀ j with hbad
  have hopen : ∀ i, IsOpen ((bad i)ᶜ) := by
    rintro (j | j)
    · exact (isClosed_badSet (isCompact_tripleSet j.1) (contDiff_stratABC hr j.2).continuous
        r₀).isOpen_compl
    · exact (isClosed_badSet (isCompact_Kn j.1 (j.2 : ℝ)) (contDiff_stratPsi hr).continuous
        r₀).isOpen_compl
  have hdense : ∀ i, Dense ((bad i)ᶜ) := by
    rintro (j | j)
    · exact interior_eq_empty_iff_dense_compl.mp (badABC_empty_interior hr hS hJ j)
    · exact interior_eq_empty_iff_dense_compl.mp (badPsi_empty_interior hr hS hJ j)
  have hBaire : Dense (⋂ i, (bad i)ᶜ) := dense_iInter_of_isOpen hopen hdense
  have hUne : (interior (Kv r₀)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Kv]
    exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self hr₀)
  obtain ⟨c, hcmem, hcU⟩ := hBaire.exists_mem_open isOpen_interior hUne
  have hcKv : c ∈ Kv r₀ := interior_subset hcU
  refine ⟨c, hcU, ?_, ?_⟩
  · intro j k w hw
    have h1 := Set.mem_iInter.mp hcmem (Sum.inl (k, j))
    intro hzero
    exact h1 ⟨hcKv, w, hw, hzero⟩
  · intro k L w hw
    have h1 := Set.mem_iInter.mp hcmem (Sum.inr (k, L))
    intro hzero
    exact h1 ⟨hcKv, w, hw, hzero⟩

/-! ## The main theorem -/

theorem exists_close_transverse_noInflection_of_jet (hJ : JetSurj)
    {r : ℝ → Space} (hr : IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → Space, IsSmoothKnot r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      (∀ a b m : ℝ, a ∈ Set.Ico 0 period → b ∈ Set.Ico 0 period → m ∈ Set.Ico 0 period →
        collinearityValue r' a b m = 0 →
        (r' a - r' b ≠ 0 ∧ r' a - r' m ≠ 0 ∧ r' m - r' b ≠ 0) →
        (PartialRankTwo r' a b m ∧ EndpointTangentsOffChord r' a b m)) ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε := by
  classical
  -- step 1: first remove the inflections
  obtain ⟨r₁, h₁, hnoinfl₁, hclose₁⟩ := exists_close_nonzero_curvature hr (ε/2) (by linarith)
  have hnoinfl₁' : ∀ t : ℝ, cross3 (velocity r₁ t) (deriv (velocity r₁) t) ≠ 0 :=
    fun t => (linearIndependent_pair_iff_cross3_ne_zero _ _).mp (hnoinfl₁ t)
  -- step 2: nonvanishing curvature is preserved on a ball
  obtain ⟨ρ, hρpos, hρ⟩ := exists_curvPreserve_bound h₁ hnoinfl₁'
  -- step 3: the smallness constants
  obtain ⟨ε₀, hε₀pos, hsm⟩ := smallCorrectionKnot h₁
  set Kc : ℝ := max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1 with hKcdef
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r₀ : ℝ := min (min (ρ/2) (ε₀/(100*Kc))) (ε/(100*Kc)) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hr₀leρ : r₀ ≤ ρ := by
    have h2 : r₀ ≤ ρ/2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr₀leε : r₀ ≤ ε/(100*Kc) := min_le_right _ _
  have hr₀leε₀ : r₀ ≤ ε₀/(100*Kc) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hbound : ∀ c ∈ Kv r₀, ‖eCoeff c‖ ≤ Kc * r₀ := by
    intro c hc
    have hcn : ‖c‖ ≤ r₀ := by rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc; exact hc
    have hop : ‖eCoeff c‖ ≤ ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ :=
      ContinuousLinearMap.le_opNorm (eCoeff : Coeff →L[ℝ] (Fin 9 → Space)) c
    have hkey : ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ ≤ Kc * r₀ :=
      mul_le_mul (le_max_left _ _) hcn (norm_nonneg c)
        (le_trans (norm_nonneg _) (le_max_left _ _))
    linarith
  have hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r₁ c) := by
    intro c hc
    refine isSmoothKnot_pertV h₁ hε₀pos hsm ?_
    have h1 := hbound c hc
    have h2 : Kc * r₀ ≤ ε₀/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε₀ hKcpos.le
      rwa [show Kc * (ε₀/(100*Kc)) = ε₀/100 from by field_simp] at this
    linarith
  -- step 4: Baire
  obtain ⟨c, hcU, hgoodABC, hgoodPsi⟩ := exists_good_coeff h₁ hr₀pos hS hJ
  have hcKv : c ∈ Kv r₀ := interior_subset hcU
  have hcn : ‖c‖ ≤ r₀ := by rw [Kv, Metric.mem_closedBall, dist_zero_right] at hcKv; exact hcKv
  refine ⟨pertV r₁ c, hS c hcKv, ?_, ?_, ?_⟩
  · -- the curvature is preserved
    intro t
    have hρc : c ∈ Kv ρ := by
      rw [Kv, Metric.mem_closedBall, dist_zero_right]; linarith
    have h := hρ c hρc t
    have hvel : (fun s : ℝ => pertVelV r₁ c s) = velocity (pertV r₁ c) :=
      funext fun s => (velocity_pertV h₁.smooth c s).symm
    have h' : cross3 (velocity (pertV r₁ c) t) (deriv (velocity (pertV r₁ c)) t) ≠ 0 := by
      rw [← hvel]
      exact h
    exact (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr h'
  · -- the flat transversality conditions
    intro a b m ha hb hm hcol hdist
    have haI : a ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨ha.1, le_of_lt (by simpa [period] using ha.2)⟩
    have hbI : b ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hb.1, le_of_lt (by simpa [period] using hb.2)⟩
    have hmI : m ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hm.1, le_of_lt (by simpa [period] using hm.2)⟩
    have ha2 : a < 2 * Real.pi := by simpa [period] using ha.2
    have hb2 : b < 2 * Real.pi := by simpa [period] using hb.2
    have hm2 : m < 2 * Real.pi := by simpa [period] using hm.2
    have hab : a ≠ b := fun h => hdist.1 (by rw [h, sub_self])
    have ham : a ≠ m := fun h => hdist.2.1 (by rw [h, sub_self])
    have hbm : b ≠ m := fun h => hdist.2.2 (by rw [h, sub_self])
    have hcsep1 : 0 < csep a b := by
      have hlt : |a - b| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hb2], by linarith [ha2, hbI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hab)) (sub_pos.mpr hlt)
    have hcsep2 : 0 < csep a m := by
      have hlt : |a - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hm2], by linarith [ha2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr ham)) (sub_pos.mpr hlt)
    have hcsep3 : 0 < csep b m := by
      have hlt : |b - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [hbI.1, hm2], by linarith [hb2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hbm)) (sub_pos.mpr hlt)
    obtain ⟨k, hk⟩ := exists_div_succ_le (lt_min (lt_min hcsep1 hcsep2) hcsep3)
    have hk1 : (1:ℝ)/(k+1) ≤ csep a b :=
      hk.trans (le_trans (min_le_left _ _) (min_le_left _ _))
    have hk2 : (1:ℝ)/(k+1) ≤ csep a m :=
      hk.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have hk3 : (1:ℝ)/(k+1) ≤ csep b m := hk.trans (min_le_right _ _)
    have hw : (a, b, m) ∈ tripleSet k := ⟨haI, hbI, hmI, hk1, hk2, hk3⟩
    have hA := hgoodABC 0 k (a, b, m) hw
    have hB := hgoodABC 1 k (a, b, m) hw
    have hM := hgoodABC 2 k (a, b, m) hw
    -- the three tangent–chord vectors are nonzero
    have hyA : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratA r₁ (c, (a, b, m)) = 0 := by rw [stratA_apply, hcol, hzero]; rfl
      exact hA hz
    have hyB : cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratB r₁ (c, (a, b, m)) = 0 := by rw [stratB_apply, hcol, hzero]; rfl
      exact hB hz
    have hyM : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratM r₁ (c, (a, b, m)) = 0 := by rw [stratM_apply, hcol, hzero]; rfl
      exact hM hz
    have hya : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c a] at hyA
    have hyb : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c b] at hyB
    have hym : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c m] at hyM
    -- the tangent–chord vectors are not all parallel
    have hnoPar : ¬ ∃ la mu : ℝ,
        cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ∧
        cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) := by
      rintro ⟨la, mu, hla, hmu⟩
      obtain ⟨j, hj⟩ := exists_nat_ge (max |la| |mu|)
      have hmem : mkCfg la mu a b m ∈ Kn k j :=
        mem_Kn_mkCfg (le_trans (le_max_left _ _) hj) (le_trans (le_max_right _ _) hj)
          haI hbI hmI hk1 hk2 hk3
      have hzero : stratPsi r₁ (c, mkCfg la mu a b m) = 0 := by
        rw [stratPsi_apply, cfgA_mkCfg, cfgB_mkCfg, cfgM_mkCfg, cfgLam_mkCfg, cfgMu_mkCfg,
          hcol, hla, hmu]
        simp
      exact hgoodPsi k j _ hmem hzero
    have hmb : pertV r₁ c m - pertV r₁ c b ≠ 0 := hdist.2.2
    refine ⟨?_, ?_⟩
    · -- rank two
      have hcp0 : collParam a b m (0 : Fin 3) = a := rfl
      have hcp1 : collParam a b m (1 : Fin 3) = b := rfl
      have hcp2 : collParam a b m (2 : Fin 3) = m := rfl
      have hpar : (¬ ∃ la : ℝ, cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) ∨
          (¬ ∃ mu : ℝ, cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) := by
        by_contra hcon
        push_neg at hcon
        exact hnoPar ⟨hcon.1.choose, hcon.2.choose, hcon.1.choose_spec, hcon.2.choose_spec⟩
      rcases hpar with hpar | hpar
      · have hc : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨0, 1, by norm_num, ?_⟩
        rw [hcp0, hcp1, velocity_pertV h₁.smooth c a, velocity_pertV h₁.smooth c b]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        have hzero' : cross3 (cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
            (cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b)) = 0 := by
          rw [cross3_anticomm, hzero, neg_zero]
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b))).mp hzero' with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
      · have hc : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨1, 2, by decide, ?_⟩
        rw [hcp1, hcp2, velocity_pertV h₁.smooth c b, velocity_pertV h₁.smooth c m]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b))).mp hzero with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
    · -- endpoint tangents off the chord
      obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ,
          pertV r₁ c a - pertV r₁ c m = ρ • (pertV r₁ c a - pertV r₁ c b) := by
        have hcol' : cross3 (pertV r₁ c a - pertV r₁ c b) (pertV r₁ c a - pertV r₁ c m) = 0 := by
          rwa [collinearityValue_eq] at hcol
        rcases (cross3_eq_zero_iff_smul_local (u := pertV r₁ c a - pertV r₁ c b)
          (v := pertV r₁ c a - pertV r₁ c m)).mp hcol' with h | h
        · exact absurd h hdist.1
        · exact h
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hρ
        exact hdist.2.1 hρ
      have hρ1 : ρ ≠ 1 := by
        intro h1
        have h2 : pertV r₁ c a - pertV r₁ c m = pertV r₁ c a - pertV r₁ c b := by
          rw [hρ, h1, one_smul]
        have h5 := congrArg (fun x : Space => pertV r₁ c a - x) h2
        rw [sub_sub_cancel, sub_sub_cancel] at h5
        exact hdist.2.2 (by rw [h5, sub_self])
      have hρm : pertV r₁ c b - pertV r₁ c m = (ρ - 1) • (pertV r₁ c a - pertV r₁ c b) := by
        have h1 : pertV r₁ c b - pertV r₁ c m
            = -(pertV r₁ c a - pertV r₁ c b) + (pertV r₁ c a - pertV r₁ c m) := by abel
        rw [h1, hρ, sub_smul, one_smul]
        abel
      have hρm0 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
      have hya' : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hya
      have hyb' : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hyb
      have hym' : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hym
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hya'
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb'
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hya')
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
  · -- closeness
    intro t
    have hb1 : ‖eCoeff c‖ ≤ Kc * r₀ := hbound c hcKv
    have hb2 : Kc * r₀ ≤ ε/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε hKcpos.le
      rwa [show Kc * (ε/(100*Kc)) = ε/100 from by field_simp] at this
    constructor
    · have hdiff : pertV r₁ c t - r t = perturbCorr (eCoeff c) t + (r₁ t - r t) := by
        simp [pertV, perturb]
        abel
      rw [hdiff]
      have h2 : ‖perturbCorr (eCoeff c) t‖ ≤ 9 * ‖eCoeff c‖ := norm_perturbCorr_le _ _
      have h5 : ‖r₁ t - r t‖ < ε/2 := (hclose₁ t).1
      calc ‖perturbCorr (eCoeff c) t + (r₁ t - r t)‖
          ≤ ‖perturbCorr (eCoeff c) t‖ + ‖r₁ t - r t‖ := norm_add_le _ _
        _ < ε := by linarith
    · have hdiff : velocity (pertV r₁ c) t - velocity r t
          = perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t) := by
        rw [velocity_pertV h₁.smooth c t]
        simp [pertVelV, perturbVel]
        abel
      rw [hdiff]
      have h2 : ‖perturbVelCorr (eCoeff c) t‖ ≤ 36 * ‖eCoeff c‖ := norm_perturbVelCorr_le _ _
      have h5 : ‖velocity r₁ t - velocity r t‖ < ε/2 := (hclose₁ t).2
      calc ‖perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t)‖
          ≤ ‖perturbVelCorr (eCoeff c) t‖ + ‖velocity r₁ t - velocity r t‖ := norm_add_le _ _
        _ < ε := by linarith

/-! ## The richness hypothesis `JetSurj`

The nine trigonometric basis functions of degree `≤ 4` realise arbitrary values and first
derivatives at any three pairwise distinct parameters of `[0, 2π]`: this is
`Work.Drive.jets_surjective` (proved in `Submission/Work/Drive/jets_surjective.lean`), stated
for parameters in `[0, 2π)`.  Since every parameter of `[0, 2π]` has a representative there
(`Work.Drive.red`) and the basis is `2π`-periodic (`trigBasis_red`, `trigBasisD_red`), the
richness holds on the whole closed interval. -/

/-- `linSum` evaluated on the coefficient vector `eCoeff.symm c'`. -/
lemma linSum_eCoeff_symm (D : Fin 9 → ℝ) (c' : Fin 9 → Space) :
    linSum D (eCoeff.symm c') = ∑ j, D j • c' j := by
  rw [linSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeffProj_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- **The jet map is surjective on `[0, 2π)`.**  From `Work.Drive.jets_surjective`, transported
through the continuous linear equivalence `eCoeff : Coeff ≃L[ℝ] (Fin 9 → Space)`. -/
theorem jetLin_surjective_of_Ico (p q r : ℝ)
    (hp : p ∈ Set.Ico 0 (2 * Real.pi)) (hq : q ∈ Set.Ico 0 (2 * Real.pi))
    (hr : r ∈ Set.Ico 0 (2 * Real.pi))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Function.Surjective (jetLin (p, q, r)) := by
  intro τ
  obtain ⟨c', h1, h2, h3, h4, h5, h6⟩ :=
    jets_surjective p q r hp hq hr hpq hpr hqr
      (dataP τ) (dataQ τ) (dataM τ) (dataA τ) (dataB τ) (dataC τ)
  refine ⟨eCoeff.symm c', ?_⟩
  have eP : (jetLin (p, q, r) (eCoeff.symm c')).1 = τ.1 := by
    show linSum (fun j => trigBasis j p) (eCoeff.symm c') = dataP τ
    rw [linSum_eCoeff_symm, h1]
  have eQ : (jetLin (p, q, r) (eCoeff.symm c')).2.1 = τ.2.1 := by
    show linSum (fun j => trigBasis j q) (eCoeff.symm c') = dataQ τ
    rw [linSum_eCoeff_symm, h3]
  have eM : (jetLin (p, q, r) (eCoeff.symm c')).2.2.1 = τ.2.2.1 := by
    show linSum (fun j => trigBasis j r) (eCoeff.symm c') = dataM τ
    rw [linSum_eCoeff_symm, h5]
  have eA : (jetLin (p, q, r) (eCoeff.symm c')).2.2.2.1 = τ.2.2.2.1 := by
    show linSum (fun j => trigBasisD j p) (eCoeff.symm c') = dataA τ
    rw [linSum_eCoeff_symm, h2]
  have eB : (jetLin (p, q, r) (eCoeff.symm c')).2.2.2.2.1 = τ.2.2.2.2.1 := by
    show linSum (fun j => trigBasisD j q) (eCoeff.symm c') = dataB τ
    rw [linSum_eCoeff_symm, h4]
  have eC : (jetLin (p, q, r) (eCoeff.symm c')).2.2.2.2.2 = τ.2.2.2.2.2 := by
    show linSum (fun j => trigBasisD j r) (eCoeff.symm c') = dataC τ
    rw [linSum_eCoeff_symm, h6]
  exact Prod.ext eP (Prod.ext eQ (Prod.ext eM (Prod.ext eA (Prod.ext eB eC))))

/-- `cos` of a difference is `1` when the circular separation vanishes. -/
lemma cos_eq_one_of_csep_eq_zero {a b : ℝ} (h : csep a b = 0) :
    Real.cos (a - b) = 1 := by
  have h2 : min |a - b| (2 * Real.pi - |a - b|) = 0 := by simpa [csep] using h
  rcases le_total |a - b| (2 * Real.pi - |a - b|) with hle | hle
  · have h1 : |a - b| = 0 := by rwa [min_eq_left hle] at h2
    rw [abs_eq_zero.mp h1, Real.cos_zero]
  · have h1 : 2 * Real.pi - |a - b| = 0 := by rwa [min_eq_right hle] at h2
    have h3 : |a - b| = 2 * Real.pi := by linarith
    rcases (abs_eq (by positivity : (0:ℝ) ≤ 2 * Real.pi)).mp h3 with h3' | h3'
    · rw [h3', Real.cos_two_pi]
    · rw [h3', Real.cos_neg, Real.cos_two_pi]

/-- The circular separation of two parameters of `[0, 2π]` is positive as soon as the cosine
of their difference differs from `1`. -/
lemma csep_pos_of_cos_ne_one {a b : ℝ} (ha : a ∈ Set.Icc 0 (2 * Real.pi))
    (hb : b ∈ Set.Icc 0 (2 * Real.pi)) (h : Real.cos (a - b) ≠ 1) : 0 < csep a b := by
  have hnn : 0 ≤ csep a b := by
    rw [csep]
    refine le_min (abs_nonneg _) ?_
    have hab : |a - b| ≤ 2 * Real.pi := by
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    linarith
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exact absurd (cos_eq_one_of_csep_eq_zero heq.symm) h

/-- The jet map only depends on the parameters through `red`. -/
lemma jetLin_red (a b m : ℝ) (ha : a ∈ Set.Icc 0 (2 * Real.pi))
    (hb : b ∈ Set.Icc 0 (2 * Real.pi)) (hm : m ∈ Set.Icc 0 (2 * Real.pi)) :
    jetLin (a, b, m) = jetLin (red a, red b, red m) := by
  have e1 : (fun j : Fin 9 => trigBasis j a) = fun j => trigBasis j (red a) :=
    funext fun j => (trigBasis_red j ha).symm
  have e2 : (fun j : Fin 9 => trigBasis j b) = fun j => trigBasis j (red b) :=
    funext fun j => (trigBasis_red j hb).symm
  have e3 : (fun j : Fin 9 => trigBasis j m) = fun j => trigBasis j (red m) :=
    funext fun j => (trigBasis_red j hm).symm
  have e4 : (fun j : Fin 9 => trigBasisD j a) = fun j => trigBasisD j (red a) :=
    funext fun j => (trigBasisD_red j ha).symm
  have e5 : (fun j : Fin 9 => trigBasisD j b) = fun j => trigBasisD j (red b) :=
    funext fun j => (trigBasisD_red j hb).symm
  have e6 : (fun j : Fin 9 => trigBasisD j m) = fun j => trigBasisD j (red m) :=
    funext fun j => (trigBasisD_red j hm).symm
  refine ContinuousLinearMap.ext fun c => ?_
  simp only [jetLin_apply]
  rw [e1, e2, e3, e4, e5, e6]

/-- **The richness of the degree-four trigonometric family**, in the form needed by the
generic-position argument: at any three parameters of `[0, 2π]` whose pairwise differences are
not multiples of `2π`, the jet map is surjective. -/
theorem jetSurj_holds : JetSurj := by
  intro a b m ha hb hm hcos
  have hab : Real.cos (a - b) ≠ 1 := by
    intro hc
    exact hcos (by simp [hc])
  have ham : Real.cos (a - m) ≠ 1 := by
    intro hc
    exact hcos (by simp [hc])
  have hbm : Real.cos (b - m) ≠ 1 := by
    intro hc
    exact hcos (by simp [hc])
  rw [jetLin_red a b m ha hb hm]
  exact jetLin_surjective_of_Ico (red a) (red b) (red m) (red_mem_Ico ha) (red_mem_Ico hb)
    (red_mem_Ico hm) (red_ne_of_csep_pos ha hb (csep_pos_of_cos_ne_one ha hb hab))
    (red_ne_of_csep_pos ha hm (csep_pos_of_cos_ne_one ha hm ham))
    (red_ne_of_csep_pos hb hm (csep_pos_of_cos_ne_one hb hm hbm))

/-- **`Work.Drive.exists_close_transverse_noInflection`.** -/
theorem exists_close_transverse_noInflection {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      (∀ a b m : ℝ, a ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        b ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        m ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        LeanEval.KnotTheory.Quadrisecant.collinearityValue r' a b m = 0 →
        (r' a - r' b ≠ 0 ∧ r' a - r' m ≠ 0 ∧ r' m - r' b ≠ 0) →
        (LeanEval.KnotTheory.Quadrisecant.PartialRankTwo r' a b m ∧
          LeanEval.KnotTheory.Quadrisecant.EndpointTangentsOffChord r' a b m)) ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε :=
  exists_close_transverse_noInflection_of_jet jetSurj_holds hr ε hε

end

end Work.Drive
