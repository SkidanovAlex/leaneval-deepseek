import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Sig2.ThetaDefs
import Submission.Work.HP.Sig2.ThetaPoissonSetup
import Submission.Work.HP.Sig2.rhoD_eq_tsum_coords
import Submission.Work.HP.Sig2.theta_eq_tsum_coords
import Submission.Work.HP.Sig2.theta_lower
import Submission.Work.HP.Sig2.perp_norm_eq
import Submission.Work.HP.Sig2.summable_gauss_quad
import Submission.Work.HP.Sig2.summable_shifted_gauss
import Submission.Work.HP.Lat.TransfExactDefs

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise

namespace Work.HP.Lat

open Work.HP

variable {ι : Type*} [Fintype ι]

/-! ## Scaling a lattice -/

/-- Scaling a linearly independent family of vectors by a nonzero constant. -/
lemma scale_indep {n : ℕ} (c : ℝ) (hc : c ≠ 0) {f : Fin n → (ι → ℝ)}
    (hf : LinearIndependent ℝ f) : LinearIndependent ℝ (fun j => c • f j) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro g hg j
  apply hf g
  have h1 : ∑ k, g k • (c • f k) = c • ∑ k, g k • f k := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_comm]
  rw [h1] at hg
  exact (smul_eq_zero.mp hg).resolve_left hc

/-- Scaling a linearly independent family by a nonzero constant (both directions). -/
lemma scale_indep_iff {n : ℕ} (c : ℝ) (hc : c ≠ 0) {f : Fin n → (ι → ℝ)} :
    LinearIndependent ℝ (fun j => c • f j) ↔ LinearIndependent ℝ f := by
  constructor
  · intro h
    have h' := scale_indep c⁻¹ (inv_ne_zero hc) h
    have heq : (fun j => c⁻¹ • (c • f j)) = f := by
      funext j; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rwa [heq] at h'
  · exact scale_indep c hc

/-- A nonzero scalar multiple of a discrete lattice is discrete. -/
theorem scaleLat_discrete (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    DiscreteTopology (scaleLat c L) := by
  let φ : scaleLat c L → L := fun v => ⟨c⁻¹ • (v : ι → ℝ), (scaleLat_mem_smul hc).mp v.2⟩
  have hcont : Continuous φ :=
    Continuous.subtype_mk (continuous_subtype_val.const_smul (c⁻¹)) _
  have hinj : Function.Injective φ := by
    intro v w h
    apply Subtype.ext
    have h1 : c⁻¹ • (v : ι → ℝ) = c⁻¹ • (w : ι → ℝ) := congrArg Subtype.val h
    have h2 := congrArg (fun x : ι → ℝ => c • x) h1
    simpa [smul_smul, mul_inv_cancel₀ hc, one_smul] using h2
  exact DiscreteTopology.of_continuous_injective hcont hinj

/-- Scaling a lattice by a nonzero real does not change its `ℤ`-rank. -/
theorem scaleLat_finrank (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ (ι → ℝ)) :
    Module.finrank ℤ (scaleLat c L) = Module.finrank ℤ L := by
  have hinj : Function.Injective (scaleLM (ι := ι) c) := by
    intro v w h
    have h1 : c⁻¹ • scaleLM c v = c⁻¹ • scaleLM c w := congrArg (fun x : ι → ℝ => c⁻¹ • x) h
    simpa [scaleLM_apply, smul_smul, inv_mul_cancel₀ hc, one_smul] using h1
  exact (Submodule.equivMapOfInjective (scaleLM (ι := ι) c) hinj L).finrank_eq.symm

/-- The successive minima of a scaled lattice are scaled. -/
theorem lamR_scaleLat (c : ℝ) (hc : 0 < c) (L : Submodule ℤ (ι → ℝ)) (i : ℕ) :
    lamR (scaleLat c L) i = c * lamR L i := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hmem : ∀ r : ℝ, (0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ scaleLat c L) ∧
        LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r)
      ↔ c⁻¹ * r ∈ {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ L) ∧
        LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r} := by
    intro r
    constructor
    · rintro ⟨hr0, f, hfL, hfI, hfr⟩
      choose g hgL hgf using fun j => hfL j
      have hgf' : f = fun j => c • g j := by
        funext j; rw [← hgf j, scaleLM_apply]
      have hgI : LinearIndependent ℝ g := (scale_indep_iff c hc0).mp (hgf' ▸ hfI)
      refine ⟨mul_nonneg (inv_nonneg.mpr hc.le) hr0, g, hgL, hgI, fun j => ?_⟩
      have h2 : rNorm (f j) = c * rNorm (g j) := by
        rw [hgf', Transf.rNorm_smul, abs_of_pos hc]
      calc rNorm (g j) = c⁻¹ * (c * rNorm (g j)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
        _ = c⁻¹ * rNorm (f j) := by rw [h2]
        _ ≤ c⁻¹ * r := mul_le_mul_of_nonneg_left (hfr j) (inv_nonneg.mpr hc.le)
    · rintro ⟨hr0, f, hfL, hfI, hfr⟩
      refine ⟨?_, fun j => c • f j, fun j => ⟨f j, hfL j, rfl⟩, scale_indep c hc0 hfI, fun j => ?_⟩
      · have : r = c * (c⁻¹ * r) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
        rw [this]; exact mul_nonneg hc.le hr0
      · rw [Transf.rNorm_smul, abs_of_pos hc]
        calc c * rNorm (f j) ≤ c * (c⁻¹ * r) := mul_le_mul_of_nonneg_left (hfr j) hc.le
          _ = r := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hset : {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ scaleLat c L) ∧
      LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r}
      = c • {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ L) ∧
      LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r} := by
    ext r
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0]
    rw [show c⁻¹ • r = c⁻¹ * r from smul_eq_mul c⁻¹ r]
    exact hmem r
  rw [lamR, lamR, hset, Real.sInf_smul_of_nonneg (a := c) hc.le, smul_eq_mul]

/-- The dual of a scaled lattice. -/
theorem dualLat_scaleLat (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ (ι → ℝ)) :
    dualLat (scaleLat c L) = scaleLat c⁻¹ (dualLat L) := by
  have hspan1 : Submodule.span ℝ (scaleLat c L : Set (ι → ℝ))
      ≤ Submodule.span ℝ (L : Set (ι → ℝ)) := by
    rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span hw)
  have hspan2 : Submodule.span ℝ (L : Set (ι → ℝ))
      ≤ Submodule.span ℝ (scaleLat c L : Set (ι → ℝ)) := by
    rw [Submodule.span_le]
    intro w hw
    have hw' : w = c⁻¹ • (c • w) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hw']
    exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span ⟨w, hw, rfl⟩)
  have hspan : Submodule.span ℝ (scaleLat c L : Set (ι → ℝ))
      = Submodule.span ℝ (L : Set (ι → ℝ)) := le_antisymm hspan1 hspan2
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨c • y, ⟨?_, ?_⟩, ?_⟩
    · rw [← hspan]; exact Submodule.smul_mem _ c hy1
    · intro z hz
      obtain ⟨k, hk⟩ := hy2 (c • z) ⟨z, hz, rfl⟩
      refine ⟨k, ?_⟩
      show dotR (c • y) z = (k : ℝ)
      have hk' : dotR y (c • z) = (k : ℝ) := hk
      rw [Transf.dotR_smul_left]
      rw [Transf.dotR_smul_right] at hk'
      linarith
    · rw [scaleLM_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨u, hu, hfl⟩
    rw [← hfl]
    refine ⟨?_, ?_⟩
    · rw [scaleLM_apply]
      exact Submodule.smul_mem _ c⁻¹ (hspan.symm ▸ hu.1)
    · intro z hz
      obtain ⟨w, hw, hfl'⟩ := hz
      obtain ⟨k, hk⟩ := hu.2 w hw
      refine ⟨k, ?_⟩
      rw [← hfl']
      show dotR (c⁻¹ • u) (c • w) = (k : ℝ)
      rw [Transf.dotR_smul_left, Transf.dotR_smul_right, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      exact hk

/-- The zeroth successive minimum is `0`. -/
theorem lamR_zero (L : Submodule ℤ (ι → ℝ)) : lamR L 0 = 0 := by
  refine le_antisymm ?_ (Transf.lamR_nonneg L 0)
  rw [lamR]
  refine csInf_le (Transf.bddBelow_lamRset L 0) ?_
  exact ⟨le_refl 0, fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type,
    fun j => j.elim0⟩

/-- A subgroup of `ℝ^ι` whose nonzero elements are all at norm at least `ε` is discrete. -/
theorem discreteTopology_of_separated (H : Submodule ℤ (ι → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ x ∈ H, x ≠ 0 → ε ≤ rNorm x) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hU : IsOpen {y : ι → ℝ | rNorm (y - (x : ι → ℝ)) < ε / 2} := by
    have hcont : Continuous fun y : ι → ℝ => rNorm (y - (x : ι → ℝ)) := by
      simp only [rNorm]
      fun_prop
    exact isOpen_lt hcont continuous_const
  have hset : ({x} : Set H) = Subtype.val ⁻¹' {y : ι → ℝ | rNorm (y - (x : ι → ℝ)) < ε / 2} := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_self, Transf.rNorm_zero]
      linarith
    · intro hy
      rw [Set.mem_singleton_iff]
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
      by_contra hne
      have hne' : (y : ι → ℝ) - (x : ι → ℝ) ≠ 0 := by
        intro h
        exact hne (Subtype.ext (sub_eq_zero.mp h))
      have hle := hsep ((y : ι → ℝ) - (x : ι → ℝ)) (Submodule.sub_mem H y.2 x.2) hne'
      linarith
  rw [hset]
  exact hU.preimage continuous_subtype_val


/-! ## The dual lattice: span, rank, discreteness -/

/-- The real dimension of the span of a discrete lattice is its `ℤ`-rank. -/
theorem finrank_span_eq (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Module.finrank ℝ (Submodule.span ℝ (Λ : Set (ι → ℝ))) = Module.finrank ℤ Λ := by
  rw [← Sig2.ThetaPoisson.span_real_latCoe Λ, Sig2.ThetaPoisson.finrank_span_latCoe Λ]
  exact (Module.finrank_eq_card_chooseBasisIndex ℤ Λ).symm

/-- The dual basis vectors `A j * = latDualMap L (single j 1)` are `ℝ`-linearly independent. -/
theorem linearIndependent_latDualMap (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    LinearIndependent ℝ (fun j : Sig2.ThetaPoisson.Idx L =>
      Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hpair : ∀ j : Sig2.ThetaPoisson.Idx L,
      dotR (Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))) (Sig2.ThetaPoisson.latCoe L i)
        = if j = i then 1 else 0 := by
    intro j
    rw [← Sig2.ThetaPoisson.latMap_single L i,
      Sig2.ThetaPoisson.dotR_latDualMap_latMap L (Pi.single j (1 : ℤ)) (Pi.single i (1 : ℝ))]
    rw [Finset.sum_eq_single j]
    · by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, Pi.single_eq_of_ne h]
        simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hsum : (∑ j, c j * (if j = i then (1 : ℝ) else 0)) = 0 := by
    have h0 : (∑ j, dotR (c j • Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ)))
        (Sig2.ThetaPoisson.latCoe L i)) = 0 := by
      have h1 : dotR (∑ j, c j • Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ)))
          (Sig2.ThetaPoisson.latCoe L i) = 0 := by
        rw [hc]
        simp [dotR]
      rwa [Sig2.ThetaPoisson.dotR_sum_left'] at h1
    have hcongr : (∑ j, c j * (if j = i then (1 : ℝ) else 0))
        = ∑ j, dotR (c j • Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ)))
            (Sig2.ThetaPoisson.latCoe L i) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Sig2.ThetaPoisson.dotR_smul_left', hpair j]
    rw [hcongr, h0]
  rw [Finset.sum_eq_single i] at hsum
  · simpa using hsum
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The span of the dual lattice is contained in the span of the lattice. -/
theorem span_dualLat_le (L : Submodule ℤ (ι → ℝ)) :
    Submodule.span ℝ (dualLat L : Set (ι → ℝ)) ≤ Submodule.span ℝ (L : Set (ι → ℝ)) := by
  rw [Submodule.span_le]
  intro y hy
  exact hy.1

/-- An integer vector has squared norm at least `1`. -/
lemma one_le_sum_sq {κ : Type*} [Fintype κ] {m : κ → ℤ} (hm : m ≠ 0) :
    (1 : ℝ) ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (funext h)
  have h2 : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) ^ 2 := by
    have h3 : (1 : ℤ) ≤ m i ∨ m i ≤ -1 := by omega
    rcases h3 with h3 | h3
    · have : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) := by exact_mod_cast h3
      nlinarith
    · have : ((m i : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h3
      nlinarith
  exact le_trans h2 (Finset.single_le_sum (fun j _ => sq_nonneg ((m j : ℤ) : ℝ))
    (Finset.mem_univ i))

/-- The dual lattice of a discrete lattice is discrete. -/
theorem discreteTopology_dualLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    DiscreteTopology (dualLat L) := by
  obtain ⟨ε, hε, hbound⟩ := Sig2.posdef_lower_bound (Sig2.ThetaPoisson.latGram L)⁻¹
    (Sig2.ThetaPoisson.latGram_posDef L).inv
  refine discreteTopology_of_separated (dualLat L) (Real.sqrt ε) (Real.sqrt_pos.mpr hε) ?_
  intro y hy hyne
  obtain ⟨m, rfl⟩ := Sig2.ThetaPoisson.latDualMap_surjective L hy
  have hm : m ≠ 0 := by
    intro h
    apply hyne
    rw [h]
    show Sig2.ThetaPoisson.latDualMap L 0 = 0
    rw [Sig2.ThetaPoisson.latDualMap_def]
    have hz : (fun i : Sig2.ThetaPoisson.Idx L => ((0 : Sig2.ThetaPoisson.Idx L → ℤ) i : ℝ)) = 0 := by
      funext i; simp
    rw [hz, Matrix.mulVec_zero, map_zero]
  have h1 : ε ≤ (rNorm (Sig2.ThetaPoisson.latDualMap L m)) ^ 2 := by
    have h2 := hbound (fun i => (m i : ℝ))
    rw [Sig2.ThetaPoisson.rNorm_latDualMap_sq]
    calc ε ≤ ε * ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
          conv_lhs => rw [← mul_one ε]
          exact mul_le_mul_of_nonneg_left (one_le_sum_sq hm) hε.le
      _ ≤ _ := h2
  rw [← Real.sqrt_sq (Transf.rNorm_nonneg _)]
  exact Real.sqrt_le_sqrt h1

/-- The real span of the dual lattice has real dimension the `ℤ`-rank of the lattice. -/
theorem finrank_span_dualLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    Module.finrank ℝ (Submodule.span ℝ (dualLat L : Set (ι → ℝ))) = Module.finrank ℤ L := by
  refine le_antisymm ?_ ?_
  · rw [← finrank_span_eq L]
    exact Submodule.finrank_mono (span_dualLat_le L)
  · have hle : Submodule.span ℝ (Set.range (fun j : Sig2.ThetaPoisson.Idx L =>
        Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))))
        ≤ Submodule.span ℝ (dualLat L : Set (ι → ℝ)) := by
      rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      exact Submodule.subset_span (Sig2.ThetaPoisson.latDualMap_mem_dualLat L (Pi.single j (1 : ℤ)))
    have h1 : Fintype.card (Sig2.ThetaPoisson.Idx L) ≤
        Module.finrank ℝ (Submodule.span ℝ (dualLat L : Set (ι → ℝ))) := by
      have h0 := Submodule.finrank_mono hle
      rwa [finrank_span_eq_card (linearIndependent_latDualMap L)] at h0
    have h2 : Fintype.card (Sig2.ThetaPoisson.Idx L) = Module.finrank ℤ L :=
      (Module.finrank_eq_card_chooseBasisIndex ℤ L).symm
    omega

/-- The real spans of a discrete lattice and of its dual coincide. -/
theorem span_dualLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    Submodule.span ℝ (dualLat L : Set (ι → ℝ)) = Submodule.span ℝ (L : Set (ι → ℝ)) := by
  haveI := discreteTopology_dualLat L
  exact Submodule.eq_of_le_of_finrank_eq (span_dualLat_le L)
    (by rw [finrank_span_dualLat L, finrank_span_eq L])

/-- The dual lattice has the same `ℤ`-rank as the lattice. -/
theorem finrank_dualLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    Module.finrank ℤ (dualLat L) = Module.finrank ℤ L := by
  haveI := discreteTopology_dualLat L
  rw [← finrank_span_eq (dualLat L), finrank_span_dualLat L]

/-- Reflexivity of the dual for a discrete lattice: `(L^*)^* = L`. -/
theorem dualLat_dualLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    dualLat (dualLat L) = L := by
  have hspan := span_dualLat L
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxspan, hxint⟩
    have hxsp : x ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := hspan ▸ hxspan
    obtain ⟨u, hu⟩ : ∃ u : Sig2.ThetaPoisson.Idx L → ℝ, Sig2.ThetaPoisson.latMap L u = x :=
      LinearMap.mem_range.mp ((Sig2.ThetaPoisson.mem_range_latMap L).mpr hxsp)
    have hint : ∀ j : Sig2.ThetaPoisson.Idx L, ∃ k : ℤ, u j = (k : ℝ) := by
      intro j
      have hmem : Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ)) ∈ dualLat L :=
        Sig2.ThetaPoisson.latDualMap_mem_dualLat L (Pi.single j (1 : ℤ))
      obtain ⟨k, hk⟩ := hxint _ hmem
      refine ⟨k, ?_⟩
      have h1 : dotR (Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))) x = u j := by
        rw [← hu, Sig2.ThetaPoisson.dotR_latDualMap_latMap L (Pi.single j (1 : ℤ)) u]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb]
          simp
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have h2 : dotR x (Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))) = (k : ℝ) := hk
      have h3 : dotR (Sig2.ThetaPoisson.latDualMap L (Pi.single j (1 : ℤ))) x = (k : ℝ) := by
        rw [← h2]
        exact (Transf.dotR_comm x _).symm
      rw [← h1, h3]
    choose m hm using hint
    have hxu : x = Sig2.ThetaPoisson.latMap L (fun j => (m j : ℝ)) := by
      rw [← hu]
      congr 1
      funext j
      exact hm j
    rw [hxu]
    exact Sig2.ThetaPoisson.latMap_int_mem L m
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hspan]
      exact Submodule.subset_span hx
    · intro y hy
      obtain ⟨k, hk⟩ := hy.2 x hx
      refine ⟨k, ?_⟩
      calc ∑ i, x i * y i = ∑ i, y i * x i := Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = (k : ℝ) := hk

/-! ## The analytic core (Gaussian/Poisson bounds) -/

section AnalyticCore

open Work.HP.Sig2
open Work.HP.Sig2.ThetaPoisson

lemma rNorm_neg_aux (x : ι → ℝ) : rNorm (-x) = rNorm x := by
  simp only [rNorm, Pi.neg_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

lemma rNorm_nonneg_aux (x : ι → ℝ) : 0 ≤ rNorm x := Real.sqrt_nonneg _

/-- The shifted theta sum of a lattice is summable. -/
theorem summable_theta_coords (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s)
    (u : Idx Λ → ℝ) :
    Summable (fun n : Idx Λ → ℤ => Real.exp (-(Real.pi / s ^ 2) *
      (∑ i, ∑ j, ((n i : ℝ) - u i) * latGram Λ i j * ((n j : ℝ) - u j)))) := by
  have hβ : 0 < Real.pi / s ^ 2 := by positivity
  have h1 := summable_shifted_gauss (latGram Λ) (latGram_posDef Λ) (Real.pi / s ^ 2) hβ
    (fun i => -u i)
  refine h1.congr (fun n => ?_)
  simp only [qForm, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/-- `theta Λ s t ≤ theta Λ s 0` for `t` in the real span of `Λ`. -/
theorem theta_le_theta_zero (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s)
    (t : ι → ℝ) (ht : t ∈ Submodule.span ℝ (Λ : Set (ι → ℝ))) :
    theta Λ s t ≤ theta Λ s 0 := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((mem_range_latMap Λ).mpr ht)
  rw [theta_cos_identity Λ s hs t u hu]
  have hθ : 0 < theta Λ s 0 := theta_zero_pos Λ s hs
  have hρ : 0 < rhoD Λ s := rhoD_pos Λ s hs
  have hbd : ∀ w : dualLat Λ, ‖dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t)‖
      ≤ dualWeight Λ s w := by
    intro w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dualWeight_nonneg Λ s w)]
    calc dualWeight Λ s w * |Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t)|
        ≤ dualWeight Λ s w * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (dualWeight_nonneg Λ s w)
      _ = dualWeight Λ s w := mul_one _
  have hsum : Summable (fun w : dualLat Λ =>
      dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t)) :=
    Summable.of_norm_bounded (summable_dual_weight Λ s hs) hbd
  have hS : (∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t))
      ≤ rhoD Λ s := by
    calc (∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t))
        ≤ ∑' w : dualLat Λ, dualWeight Λ s w :=
          Summable.tsum_le_tsum (fun w => by
            have := Real.cos_le_one (2 * Real.pi * dotR ((w : ι → ℝ)) t)
            nlinarith [dualWeight_nonneg Λ s w]) hsum (summable_dual_weight Λ s hs)
      _ = rhoD Λ s := dualWeight_tsum Λ s
  rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
  exact mul_le_mul_of_nonneg_left hS hθ.le

lemma arith_deep {p s2 γ r A : ℝ} (hp : 0 < p) (hs2 : 0 < s2) (hγ : 0 ≤ 1 - γ)
    (hA : r ^ 2 ≤ A) :
    -(p / s2) * A ≤ -(p * (1 - γ) * r ^ 2 / s2) + -(p * γ / s2) * A := by
  have h1 : p * (1 - γ) * r ^ 2 / s2 ≤ p * (1 - γ) * A / s2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hs2.le
  have h2 : (p / s2) * A = p * γ / s2 * A + p * (1 - γ) * A / s2 := by
    field_simp <;> ring
  nlinarith [h1, h2]

/-- **Deep-hole tail bound.**  If every point of `Λ` is at distance at least `r` from `t`, then
`θ_Λ(s,t) ≤ e^{-π(1-γ)r²/s²} θ_Λ(s/√γ, 0)`. -/
theorem theta_deep_hole (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (t : ι → ℝ)
    (ht : t ∈ Submodule.span ℝ (Λ : Set (ι → ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hdist : ∀ z ∈ Λ, r ≤ rNorm (t - z)) :
    theta Λ s t ≤ Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) *
      theta Λ (s / Real.sqrt γ) 0 := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((mem_range_latMap Λ).mpr ht)
  have hγpos : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hs' : 0 < s / Real.sqrt γ := div_pos hs hγpos
  have hsq : (s / Real.sqrt γ) ^ 2 = s ^ 2 / γ := by
    rw [div_pow, Real.sq_sqrt hγ.le]
  have hstep : theta Λ s t ≤ Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) *
      theta Λ (s / Real.sqrt γ) t := by
    rw [theta_eq_tsum_coords Λ s t u hu, theta_eq_tsum_coords Λ (s / Real.sqrt γ) t u hu,
      ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_theta_coords Λ s hs u)
      ((summable_theta_coords Λ (s / Real.sqrt γ) hs' u).mul_left _)
    set A : ℝ := ∑ i, ∑ j, ((n i : ℝ) - u i) * latGram Λ i j * ((n j : ℝ) - u j) with hA
    set x : ι → ℝ := latMap Λ (fun i => (n i : ℝ)) with hx
    have hfun : (fun i => (n i : ℝ) - u i) = (fun i => (n i : ℝ)) - u := by
      ext i; simp
    have hsub : x - t = latMap Λ (fun i => (n i : ℝ) - u i) := by
      rw [hx, ← hu, ← map_sub, hfun]
    have hAeq : A = (rNorm (x - t)) ^ 2 := by
      rw [hA, hsub, ← latGram_quad Λ (fun i => (n i : ℝ) - u i), hfun]
    have hA0 : 0 ≤ A := by rw [hAeq]; positivity
    have hAge : r ^ 2 ≤ A := by
      rw [hAeq]
      have hz : x ∈ Λ := latMap_int_mem Λ n
      have h1 : r ≤ rNorm (t - x) := hdist _ hz
      have h2 : rNorm (x - t) = rNorm (t - x) := by
        rw [show x - t = -(t - x) from by abel, rNorm_neg_aux]
      rw [h2]
      nlinarith [h1, rNorm_nonneg_aux (t - x)]
    have hγ' : (0 : ℝ) ≤ 1 - γ := by linarith
    rw [← Real.exp_add, Real.exp_le_exp, hsq]
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    have hpi : Real.pi / (s ^ 2 / γ) = Real.pi * γ / s ^ 2 := by
      field_simp <;> ring
    rw [hpi]
    exact arith_deep Real.pi_pos hs2 hγ' hAge
  refine le_trans hstep ?_
  exact mul_le_mul_of_nonneg_left (theta_le_theta_zero Λ (s / Real.sqrt γ) hs' t ht)
    (Real.exp_nonneg _)

/-- The unshifted theta function in terms of the Gram determinant and the dual theta sum. -/
theorem theta_zero_eq_rhoD (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s) :
    theta Λ s 0 = (s ^ Fintype.card (Idx Λ) / Real.sqrt (latGram Λ).det) * rhoD Λ s := by
  have h0 : latMap Λ (0 : Idx Λ → ℝ) = 0 := map_zero _
  have h := theta_eq_poisson_cos Λ s hs (0 : Idx Λ → ℝ)
  rw [h0] at h
  rw [h, rhoD_eq_tsum_coords Λ s]
  congr 1
  refine tsum_congr fun m => ?_
  rw [show (∑ j, (m j : ℝ) * (0 : Idx Λ → ℝ) j) = 0 from by simp, mul_zero, Real.cos_zero,
    mul_one]

/-- The ratio of the unshifted theta functions at two parameters. -/
theorem theta_zero_ratio (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    theta Λ s' 0 = (s' / s) ^ Fintype.card (Idx Λ) * (rhoD Λ s' / rhoD Λ s) * theta Λ s 0 := by
  have hdet : (0 : ℝ) < Real.sqrt (latGram Λ).det := by
    rw [Real.sqrt_pos]
    exact (latGram_posDef Λ).det_pos
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs'0 : s' ≠ 0 := ne_of_gt hs'
  have hρ : rhoD Λ s ≠ 0 := ne_of_gt (rhoD_pos Λ s hs)
  have hρ' : rhoD Λ s' ≠ 0 := ne_of_gt (rhoD_pos Λ s' hs')
  rw [theta_zero_eq_rhoD Λ s' hs', theta_zero_eq_rhoD Λ s hs, div_pow]
  field_simp <;> ring

/-- **Key inequality.**  If some `t ∈ span Λ` is at distance at least `r` from `Λ`, then
`2 - ρ_s(Λ*) ≤ (1/√γ)^R e^{-π(1-γ)r²/s²} ρ_{s/√γ}(Λ*)`. -/
theorem key_ineq (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (t : ι → ℝ)
    (ht : t ∈ Submodule.span ℝ (Λ : Set (ι → ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hdist : ∀ z ∈ Λ, r ≤ rNorm (t - z)) :
    2 - rhoD Λ s ≤ (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ) *
      Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * rhoD Λ (s / Real.sqrt γ) := by
  have hγpos : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hs' : 0 < s / Real.sqrt γ := div_pos hs hγpos
  have hθ : 0 < theta Λ s 0 := theta_zero_pos Λ s hs
  have hρ : 0 < rhoD Λ s := rhoD_pos Λ s hs
  have hlow := theta_lower Λ s hs t ht
  have hup := theta_deep_hole Λ s hs hγ hγ1 t ht hr hdist
  have hconst : s / Real.sqrt γ / s = 1 / Real.sqrt γ := by
    field_simp <;> ring
  have hratio := theta_zero_ratio Λ (s := s) (s' := s / Real.sqrt γ) hs hs'
  rw [hconst] at hratio
  have h1 : ((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0
      ≤ Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * theta Λ (s / Real.sqrt γ) 0 :=
    le_trans hlow hup
  rw [hratio] at h1
  have h1' : ((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0
      ≤ (Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * (rhoD Λ (s / Real.sqrt γ) / rhoD Λ s)) * theta Λ s 0 := by
    convert h1 using 1 <;> ring
  have h2 : ((2 - rhoD Λ s) / rhoD Λ s)
      ≤ Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * (rhoD Λ (s / Real.sqrt γ) / rhoD Λ s) := by
    by_contra hcon
    push_neg at hcon
    have hlt := mul_lt_mul_of_pos_right hcon hθ
    linarith [h1']
  have h3 := mul_le_mul_of_nonneg_right h2 hρ.le
  have hdiv : (2 - rhoD Λ s) / rhoD Λ s * rhoD Λ s = (2 - rhoD Λ s) :=
    div_mul_cancel₀ _ (ne_of_gt hρ)
  have hdiv2 : Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * (rhoD Λ (s / Real.sqrt γ) / rhoD Λ s) * rhoD Λ s
      = Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * rhoD Λ (s / Real.sqrt γ) := by
    field_simp <;> ring
  rw [hdiv, hdiv2] at h3
  calc 2 - rhoD Λ s
      ≤ Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * rhoD Λ (s / Real.sqrt γ) := h3
    _ = (1 / Real.sqrt γ) ^ Fintype.card (Idx Λ)
        * Real.exp (-(Real.pi * (1 - γ) * r ^ 2 / s ^ 2)) * rhoD Λ (s / Real.sqrt γ) := by ring

end AnalyticCore


/-! ## Deep holes and mass bounds -/

/-- A lattice whose real span is covered by open `r`-balls centred at lattice points has
`λ_R ≤ 2r`. -/
theorem span_small_eq_span (Λ : Submodule ℤ (ι → ℝ)) {r : ℝ} (hr : 0 < r)
    (h : ∀ t ∈ Submodule.span ℝ (Λ : Set (ι → ℝ)), ∃ z ∈ Λ, rNorm (t - z) < r) :
    Submodule.span ℝ {z : ι → ℝ | z ∈ Λ ∧ rNorm z ≤ 2 * r}
      = Submodule.span ℝ (Λ : Set (ι → ℝ)) := by
  have hle : Submodule.span ℝ {z : ι → ℝ | z ∈ Λ ∧ rNorm z ≤ 2 * r}
      ≤ Submodule.span ℝ (Λ : Set (ι → ℝ)) := by
    rw [Submodule.span_le]
    rintro z ⟨hzΛ, -⟩
    exact Submodule.subset_span hzΛ
  refine le_antisymm hle ?_
  by_contra hnot
  obtain ⟨u, huV, hur, huorth⟩ :=
    Sig2.perp_norm_eq hle (fun heq => hnot (le_of_eq heq.symm)) hr
  obtain ⟨z, hzΛ, hlt⟩ := h u huV
  have hzS : z ∈ {z : ι → ℝ | z ∈ Λ ∧ rNorm z ≤ 2 * r} := by
    refine ⟨hzΛ, ?_⟩
    have hzeq : z = u - (u - z) := by abel
    have h1 : rNorm z < 2 * r := by
      calc rNorm z = rNorm (u - (u - z)) := congrArg rNorm hzeq
        _ ≤ rNorm u + rNorm (u - z) := Transf.rNorm_sub_le u (u - z)
        _ < r + r := by rw [hur]; linarith
        _ = 2 * r := by ring
    exact le_of_lt h1
  have hzW : z ∈ Submodule.span ℝ {z : ι → ℝ | z ∈ Λ ∧ rNorm z ≤ 2 * r} :=
    Submodule.subset_span hzS
  have hz0 : dotR u z = 0 := huorth z hzW
  have huuz : dotR u z = rNorm u ^ 2 - dotR u (u - z) := by
    have hzeq : z = u - (u - z) := by abel
    conv_lhs => rw [hzeq]
    rw [Transf.dotR_sub_right, ← Transf.rNorm_sq]
  have hbound : dotR u (u - z) < r * r := by
    have hcs : dotR u (u - z) ≤ rNorm u * rNorm (u - z) :=
      (le_abs_self _).trans (Transf.dotR_cauchy u (u - z))
    rw [hur] at hcs
    nlinarith [hlt, hr]
  have hpos : 0 < dotR u z := by
    rw [huuz, hur]
    linarith
  exact absurd hz0 (ne_of_gt hpos)

/-- Covering the real span by open `r`-balls forces `λ_R ≤ 2r`. -/
theorem lamR_le_two_mul (N : Submodule ℤ (ι → ℝ)) [DiscreteTopology N]
    (hrank : Module.finrank ℤ N = Module.finrank ℝ (Submodule.span ℝ (N : Set (ι → ℝ))))
    (r : ℝ) (hr : 0 < r)
    (hcover : ∀ t ∈ Submodule.span ℝ (N : Set (ι → ℝ)), ∃ z ∈ N, rNorm (t - z) < r) :
    lamR N (Module.finrank ℤ N) ≤ 2 * r := by
  rw [lamR]
  refine csInf_le (Transf.bddBelow_lamRset N (Module.finrank ℤ N)) ?_
  have hspan := span_small_eq_span N hr hcover
  obtain ⟨f, hfS, -, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ {z : ι → ℝ | z ∈ N ∧ rNorm z ≤ 2 * r}
  have hcard : Module.finrank ℝ (Submodule.span ℝ {z : ι → ℝ | z ∈ N ∧ rNorm z ≤ 2 * r})
      = Module.finrank ℤ N := by
    rw [hspan]; exact hrank.symm
  refine ⟨by linarith, fun j => f (Fin.cast hcard.symm j), ?_, ?_, ?_⟩
  · intro j; exact (hfS (Fin.cast hcard.symm j)).1
  · exact hfind.comp (Fin.cast hcard.symm) (Fin.cast_injective hcard.symm)
  · intro j; exact (hfS (Fin.cast hcard.symm j)).2

/-- If `2r < λ_R`, some point of the real span is at distance at least `r` from the lattice. -/
theorem exists_far_point (N : Submodule ℤ (ι → ℝ)) [DiscreteTopology N]
    (hrank : Module.finrank ℤ N = Module.finrank ℝ (Submodule.span ℝ (N : Set (ι → ℝ))))
    {r : ℝ} (hr : 0 < r) (hlam : 2 * r < lamR N (Module.finrank ℤ N)) :
    ∃ v ∈ Submodule.span ℝ (N : Set (ι → ℝ)), ∀ z : N, r ≤ rNorm ((z : ι → ℝ) - v) := by
  by_contra hcon
  push_neg at hcon
  have hcover : ∀ t ∈ Submodule.span ℝ (N : Set (ι → ℝ)), ∃ z ∈ N, rNorm (t - z) < r := by
    intro t ht
    obtain ⟨z, hlt⟩ := hcon t ht
    refine ⟨z, z.2, ?_⟩
    have h2 : rNorm ((z : ι → ℝ) - t) = rNorm (t - (z : ι → ℝ)) := by
      rw [show (z : ι → ℝ) - t = -(t - (z : ι → ℝ)) from by abel, rNorm_neg_aux]
    rwa [h2] at hlt
  have h1 := lamR_le_two_mul N hrank r hr hcover
  linarith

/-! ## The dual mass and the theta ratio -/

/-- The dual theta sum of the double dual is the theta sum of the lattice. -/
theorem rhoD_dualLat_eq_theta (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M]
    {σ : ℝ} (hσ : 0 < σ) : rhoD (dualLat M) σ = theta M σ⁻¹ 0 := by
  rw [rhoD, dualLat_dualLat M, theta]
  refine tsum_congr fun z => ?_
  rw [sub_zero]
  congr 1
  have h1 : Real.pi / (σ⁻¹) ^ 2 = Real.pi * σ ^ 2 := by
    rw [inv_pow, div_inv_eq_mul]
  rw [h1]

/-- The unshifted theta function grows at most like `(σ'/σ) ^ R`. -/
theorem theta_zero_le_ratio (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M] {σ σ' : ℝ}
    (hσ : 0 < σ) (hσ' : σ ≤ σ') :
    theta M σ' 0 ≤ (σ' / σ) ^ Fintype.card (Sig2.ThetaPoisson.Idx M) * theta M σ 0 := by
  have hσ'0 : 0 < σ' := lt_of_lt_of_le hσ hσ'
  have h1 : rhoD M σ' ≤ rhoD M σ := by
    rw [rhoD]
    refine Summable.tsum_le_tsum (fun w => ?_) (Sig2.summable_dual_weight M σ' hσ'0)
      (Sig2.summable_dual_weight M σ hσ)
    rw [Real.exp_le_exp]
    have hA : (0 : ℝ) ≤ (rNorm ((w : ι → ℝ))) ^ 2 := sq_nonneg _
    have h2 : σ ^ 2 ≤ σ' ^ 2 := by nlinarith
    have h3 : Real.pi * σ ^ 2 * (rNorm ((w : ι → ℝ))) ^ 2
        ≤ Real.pi * σ' ^ 2 * (rNorm ((w : ι → ℝ))) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hA
      refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
      linarith
    linarith
  rw [theta_zero_ratio M hσ (lt_of_lt_of_le hσ hσ')]
  have hdiv : rhoD M σ' / rhoD M σ ≤ 1 :=
    (div_le_one (Sig2.rhoD_pos M σ hσ)).mpr h1
  calc (σ' / σ) ^ Fintype.card (Sig2.ThetaPoisson.Idx M) * (rhoD M σ' / rhoD M σ) * theta M σ 0
      ≤ (σ' / σ) ^ Fintype.card (Sig2.ThetaPoisson.Idx M) * 1 * theta M σ 0 := by
        refine mul_le_mul_of_nonneg_right ?_ (Sig2.theta_zero_pos M σ hσ).le
        exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = (σ' / σ) ^ Fintype.card (Sig2.ThetaPoisson.Idx M) * theta M σ 0 := by ring

/-- Summability of a Gaussian over a discrete lattice, in subtype form. -/
theorem summable_subtype_gauss (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M] (s : ℝ) (hs : 0 < s)
    (t : ι → ℝ) (u : Sig2.ThetaPoisson.Idx M → ℝ) (hu : Sig2.ThetaPoisson.latMap M u = t) :
    Summable (fun z : M => Real.exp (-(Real.pi / s ^ 2) * (rNorm ((z : ι → ℝ) - t)) ^ 2)) := by
  let e : (Sig2.ThetaPoisson.Idx M → ℤ) ≃ M := ((Sig2.ThetaPoisson.latBasis M).equivFun.symm).toEquiv
  refine (Equiv.summable_iff e).mp ?_
  refine (summable_theta_coords M s hs u).congr (fun n => ?_)
  congr 1
  rw [show ((e n : M) : ι → ℝ) = Sig2.ThetaPoisson.latMap M (fun i => (n i : ℝ)) from
    Sig2.ThetaPoisson.latMap_equivFun M n]
  rw [← hu]
  rw [show Sig2.ThetaPoisson.latMap M (fun i => (n i : ℝ)) - Sig2.ThetaPoisson.latMap M u
      = Sig2.ThetaPoisson.latMap M (fun i => (n i : ℝ) - u i) from by
        rw [← map_sub]; rfl]
  rw [Sig2.ThetaPoisson.latGram_quad]

/-- The unshifted theta function is monotone in its parameter. -/
theorem theta_zero_mono (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M] {σ σ' : ℝ}
    (hσ' : 0 < σ') (hσ : σ' ≤ σ) : theta M σ' 0 ≤ theta M σ 0 := by
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ' hσ
  obtain ⟨u, hu⟩ : ∃ u : Sig2.ThetaPoisson.Idx M → ℝ, Sig2.ThetaPoisson.latMap M u = 0 :=
    ⟨0, map_zero _⟩
  have h1 : Summable (fun z : M => Real.exp (-(Real.pi / σ' ^ 2) * (rNorm (z : ι → ℝ)) ^ 2)) :=
    (summable_subtype_gauss M σ' hσ' 0 u hu).congr (fun z => by rw [sub_zero])
  have h2 : Summable (fun z : M => Real.exp (-(Real.pi / σ ^ 2) * (rNorm (z : ι → ℝ)) ^ 2)) :=
    (summable_subtype_gauss M σ hσ0 0 u hu).congr (fun z => by rw [sub_zero])
  have hA : theta M σ' 0 = ∑' z : M, Real.exp (-(Real.pi / σ' ^ 2) * (rNorm (z : ι → ℝ)) ^ 2) := by
    rw [theta]
    refine tsum_congr fun z => ?_
    rw [sub_zero]
  have hB : theta M σ 0 = ∑' z : M, Real.exp (-(Real.pi / σ ^ 2) * (rNorm (z : ι → ℝ)) ^ 2) := by
    rw [theta]
    refine tsum_congr fun z => ?_
    rw [sub_zero]
  rw [hA, hB]
  refine Summable.tsum_le_tsum (fun z => ?_) h1 h2
  rw [Real.exp_le_exp]
  have hA' : (0 : ℝ) ≤ (rNorm ((z : ι → ℝ))) ^ 2 := sq_nonneg _
  have h3 : Real.pi / σ ^ 2 ≤ Real.pi / σ' ^ 2 := by
    refine div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ?_
    nlinarith
  nlinarith [hA']

/-- `theta M 1 0 ≤ 1 + e^{π(s²-1)λ²} s^{-R} theta M 1 0` when all nonzero vectors of `M` have
norm at least `λ`.  This is the `δ`-bound of Banaszczyk's argument. -/
theorem theta_one_le_shell (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M]
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : ∀ z : M, z ≠ 0 → lam ≤ rNorm (z : ι → ℝ))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    theta M 1 0 ≤ 1 + Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) *
      (s ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹ * theta M 1 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Sig2.ThetaPoisson.Idx M → ℝ, Sig2.ThetaPoisson.latMap M u = 0 :=
    ⟨0, map_zero _⟩
  have hsum0 : Summable (fun z : M => Real.exp (-(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2)) := by
    refine (summable_subtype_gauss M 1 one_pos 0 u hu).congr (fun z => ?_)
    rw [sub_zero]
    congr 1
    norm_num
  have hsum1 : Summable (fun z : M => Real.exp (-(Real.pi * s ^ 2) * (rNorm (z : ι → ℝ)) ^ 2)) := by
    refine (summable_subtype_gauss M s⁻¹ (inv_pos.mpr hs0) 0 u hu).congr (fun z => ?_)
    rw [sub_zero]
    congr 1
    rw [inv_pow, div_inv_eq_mul]
  have hθ1 : theta M 1 0 = ∑' z : M, Real.exp (-(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2) := by
    rw [theta]
    refine tsum_congr fun z => ?_
    rw [sub_zero]
    congr 1
    rw [one_pow, div_one]
  have hθs : theta M s⁻¹ 0 = ∑' z : M, Real.exp (-(Real.pi * s ^ 2) * (rNorm (z : ι → ℝ)) ^ 2) := by
    rw [theta]
    refine tsum_congr fun z => ?_
    rw [sub_zero]
    congr 1
    rw [inv_pow, div_inv_eq_mul]
  have hmass : (∑' z : M, (if z = 0 then (0 : ℝ)
      else Real.exp (-(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2)))
      ≤ Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) *
        ∑' z : M, Real.exp (-(Real.pi * s ^ 2) * (rNorm (z : ι → ℝ)) ^ 2) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun z => ?_) ?_ ?_
    · by_cases hz : z = 0
      · rw [if_pos hz]; positivity
      · rw [if_neg hz, ← Real.exp_add, Real.exp_le_exp]
        have h1 : lam ≤ rNorm (z : ι → ℝ) := hlam z hz
        have h2 : lam ^ 2 ≤ (rNorm (z : ι → ℝ)) ^ 2 := by
          nlinarith [hlam0, Transf.rNorm_nonneg ((z : ι → ℝ))]
        have hs2 : s ^ 2 ≤ 1 := by
          have := mul_le_mul_of_nonneg_left hs1 hs0.le
          nlinarith
        have e1 : -(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2
            + Real.pi * s ^ 2 * (rNorm (z : ι → ℝ)) ^ 2
            = Real.pi * (s ^ 2 - 1) * (rNorm (z : ι → ℝ)) ^ 2 := by ring
        have hPa : Real.pi * (s ^ 2 - 1) ≤ 0 := by nlinarith [hs2, Real.pi_pos]
        have e2 : Real.pi * (s ^ 2 - 1) * (rNorm (z : ι → ℝ)) ^ 2
            ≤ Real.pi * (s ^ 2 - 1) * lam ^ 2 := by
          nlinarith [h2, hPa]
        linarith [e1, e2]
    · refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hsum0
      · by_cases hz : z = 0
        · rw [if_pos hz]
        · rw [if_neg hz]; exact Real.exp_nonneg _
      · by_cases hz : z = 0
        · rw [if_pos hz]; exact Real.exp_nonneg _
        · rw [if_neg hz]
    · exact hsum1.mul_left _
  have hsplit : theta M 1 0 = 1 + ∑' z : M, (if z = 0 then (0 : ℝ)
      else Real.exp (-(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2)) := by
    rw [hθ1]
    have h := Summable.tsum_eq_add_tsum_ite hsum0 (0 : M)
    rw [h]
    congr 1
    simp
  have hΘs : theta M s⁻¹ 0 ≤ (s ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹ * theta M 1 0 := by
    have h := theta_zero_le_ratio M (σ := (1 : ℝ)) (σ' := s⁻¹) one_pos
      ((one_le_inv₀ hs0).mpr hs1)
    rwa [div_one, inv_pow] at h
  calc theta M 1 0
      = 1 + ∑' z : M, (if z = 0 then (0 : ℝ)
          else Real.exp (-(Real.pi) * (rNorm (z : ι → ℝ)) ^ 2)) := hsplit
    _ ≤ 1 + Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) *
          ∑' z : M, Real.exp (-(Real.pi * s ^ 2) * (rNorm (z : ι → ℝ)) ^ 2) :=
          add_le_add (le_refl 1) hmass
    _ = 1 + Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) * theta M s⁻¹ 0 := by rw [hθs]
    _ ≤ 1 + Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) *
          ((s ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹ * theta M 1 0) := by
          exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hΘs (Real.exp_nonneg _))
    _ = 1 + Real.exp (Real.pi * (s ^ 2 - 1) * lam ^ 2) *
          (s ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹ * theta M 1 0 := by ring

/-! ## Numerical thresholds -/

/-- For `R ≥ 2` the hole threshold `Ehole R` is strictly below `1 - 2 * Edelta R`. -/
theorem Ehole_lt_Edelta {R : ℕ} (hR : 2 ≤ R) : Ehole R < 1 - 2 * Edelta R := by
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  set a : ℝ := Real.sqrt (Real.pi / 2) * Real.exp ((1 : ℝ) / 2 - Real.pi / 4) with ha
  set b : ℝ := Real.sqrt (2 * Real.pi) * Real.exp ((1 : ℝ) / 2 - Real.pi) with hb
  have ha2 : a ^ 2 = Real.pi / 2 * Real.exp (1 - Real.pi / 2) := by
    rw [ha, mul_pow, Real.sq_sqrt (by positivity)]
    rw [show (Real.exp ((1 : ℝ) / 2 - Real.pi / 4)) ^ 2 = Real.exp (1 - Real.pi / 2) from by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
  have hb2 : b ^ 2 = 2 * Real.pi * Real.exp (1 - 2 * Real.pi) := by
    rw [hb, mul_pow, Real.sq_sqrt (by positivity)]
    rw [show (Real.exp ((1 : ℝ) / 2 - Real.pi)) ^ 2 = Real.exp (1 - 2 * Real.pi) from by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hX : Real.exp (-(0.57 : ℝ)) ≤ 0.5673 := by
    have h57 : (1.763 : ℝ) ≤ Real.exp 0.57 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.57) 4
      have h2 : (1.763 : ℝ) ≤ ∑ i ∈ Finset.range 4, (0.57 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ]
      linarith
    have hmul : Real.exp (-(0.57 : ℝ)) * Real.exp 0.57 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h1 : Real.exp (-(0.57 : ℝ)) * 1.763 ≤ 1 := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h57 (Real.exp_nonneg _)
    have h2 : Real.exp (-(0.57 : ℝ)) ≤ 1 / 1.763 := (le_div_iff₀ (by norm_num)).mpr h1
    have h3 : (1 : ℝ) / 1.763 ≤ 0.5673 := by norm_num
    linarith
  have hY : Real.exp (-(5.28 : ℝ)) ≤ 0.005587 := by
    have h528 : (179 : ℝ) ≤ Real.exp 5.28 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5.28) 9
      have h2 : (179 : ℝ) ≤ ∑ i ∈ Finset.range 9, (5.28 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ]
      linarith
    have hmul : Real.exp (-(5.28 : ℝ)) * Real.exp 5.28 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h1 : Real.exp (-(5.28 : ℝ)) * 179 ≤ 1 := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h528 (Real.exp_nonneg _)
    have h2 : Real.exp (-(5.28 : ℝ)) ≤ 1 / 179 := (le_div_iff₀ (by norm_num)).mpr h1
    have h3 : (1 : ℝ) / 179 ≤ 0.005587 := by norm_num
    linarith
  have haa : a ^ 2 ≤ 1.575 * Real.exp (-(0.57 : ℝ)) := by
    rw [ha2]
    have h1 : Real.pi / 2 ≤ 1.575 := by linarith
    have h2 : Real.exp (1 - Real.pi / 2) ≤ Real.exp (-(0.57 : ℝ)) := by
      rw [Real.exp_le_exp]; linarith
    exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by norm_num)
  have hbb : b ^ 2 ≤ 6.3 * Real.exp (-(5.28 : ℝ)) := by
    rw [hb2]
    have h1 : 2 * Real.pi ≤ 6.3 := by linarith
    have h2 : Real.exp (1 - 2 * Real.pi) ≤ Real.exp (-(5.28 : ℝ)) := by
      rw [Real.exp_le_exp]; linarith
    exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by norm_num)
  have hmain : a ^ 2 + 2 * b ^ 2 < 1 := by
    linarith [haa, hbb, hX, hY]
  have ha1 : a ≤ 1 := le_of_lt (by nlinarith [ha0, hmain, sq_nonneg b])
  have hb1 : b ≤ 1 := le_of_lt (by nlinarith [hb0, hmain, sq_nonneg a])
  have hEho : Ehole R = a ^ R := by
    have h1 : Real.exp ((R : ℝ) / 2 - Real.pi * R / 4)
        = (Real.exp ((1 : ℝ) / 2 - Real.pi / 4)) ^ R := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [ha, mul_pow, Ehole, h1, mul_comm]
  have hEd : Edelta R = b ^ R := by
    have h1 : Real.exp ((R : ℝ) / 2 - Real.pi * R)
        = (Real.exp ((1 : ℝ) / 2 - Real.pi)) ^ R := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hb, mul_pow, Edelta, h1, mul_comm]
  have haR : a ^ R ≤ a ^ 2 := by
    have h : a ^ R = a ^ 2 * a ^ (R - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    calc a ^ 2 * a ^ (R - 2) ≤ a ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ ha0.le ha1) (by positivity)
      _ = a ^ 2 := mul_one _
  have hbR : b ^ R ≤ b ^ 2 := by
    have h : b ^ R = b ^ 2 * b ^ (R - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    calc b ^ 2 * b ^ (R - 2) ≤ b ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hb0.le hb1) (by positivity)
      _ = b ^ 2 := mul_one _
  rw [hEho, hEd]
  linarith [haR, hbR, hmain]

/-! ## Rank one -/

/-- For a lattice of rank one, `λ₁(L)·λ₁(L*) ≤ 1`. -/
theorem transference_rank_one (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (hR : Module.finrank ℤ L = 1) : lamR L 1 * lamR (dualLat L) 1 ≤ 1 := by
  have hcard : Fintype.card (Sig2.ThetaPoisson.Idx L) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ L, hR]
  haveI : Subsingleton (Sig2.ThetaPoisson.Idx L) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
  obtain ⟨j⟩ : Nonempty (Sig2.ThetaPoisson.Idx L) := Fintype.card_pos_iff.mp (by omega)
  haveI : Nonempty (Sig2.ThetaPoisson.Idx L) := ⟨j⟩
  have hgen : ∀ z ∈ L, ∃ c : ℤ, (z : ι → ℝ)
      = (c : ℝ) • Sig2.ThetaPoisson.latCoe L j := by
    intro z hz
    refine ⟨(Sig2.ThetaPoisson.latBasis L).equivFun ⟨z, hz⟩ j, ?_⟩
    have key : (↑((⟨z, hz⟩ : L)) : ι → ℝ)
        = (↑((Sig2.ThetaPoisson.latBasis L).equivFun ⟨z, hz⟩ j) : ℝ) •
          Sig2.ThetaPoisson.latCoe L j := by
      conv_lhs =>
        rw [← LinearEquiv.symm_apply_apply (Sig2.ThetaPoisson.latBasis L).equivFun ⟨z, hz⟩]
      rw [Sig2.ThetaPoisson.latMap_equivFun, Sig2.ThetaPoisson.latMap_apply,
        Finset.sum_eq_single j]
      · intro b _ hb
        exact absurd (Subsingleton.elim b j) hb
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    exact key
  have hg0 : Sig2.ThetaPoisson.latCoe L j ≠ 0 := by
    intro h
    have h' : (Sig2.ThetaPoisson.latBasis L j : L) = 0 := Subtype.ext h
    exact (Sig2.ThetaPoisson.latBasis L).linearIndependent.ne_zero j h'
  have hgpos : 0 < rNorm (Sig2.ThetaPoisson.latCoe L j) := Transf.rNorm_pos_iff.mpr hg0
  set w : ι → ℝ := (rNorm (Sig2.ThetaPoisson.latCoe L j))⁻¹ ^ 2 • Sig2.ThetaPoisson.latCoe L j
    with hw
  have hwmem : w ∈ dualLat L := by
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Sig2.ThetaPoisson.latBasis L j).2)
    · intro z hz
      obtain ⟨c, hc⟩ := hgen z hz
      refine ⟨c, ?_⟩
      rw [hc, hw]
      show dotR ((rNorm (Sig2.ThetaPoisson.latCoe L j))⁻¹ ^ 2 • Sig2.ThetaPoisson.latCoe L j)
        ((c : ℝ) • Sig2.ThetaPoisson.latCoe L j) = (c : ℝ)
      rw [Transf.dotR_smul_left, Transf.dotR_smul_right, ← Transf.rNorm_sq]
      have hne : rNorm (Sig2.ThetaPoisson.latCoe L j) ≠ 0 := ne_of_gt hgpos
      field_simp
  have hw0 : w ≠ 0 := by
    rw [hw]
    intro h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact pow_ne_zero 2 (inv_ne_zero (ne_of_gt hgpos)) h1
    · exact hg0 h1
  have hrnw : rNorm w = (rNorm (Sig2.ThetaPoisson.latCoe L j))⁻¹ := by
    rw [hw, Transf.rNorm_smul, abs_of_nonneg (by positivity)]
    have hne : rNorm (Sig2.ThetaPoisson.latCoe L j) ≠ 0 := ne_of_gt hgpos
    field_simp
  have h1 : lamR L 1 ≤ rNorm (Sig2.ThetaPoisson.latCoe L j) :=
    Transf.lamR_le_rNorm L (Sig2.ThetaPoisson.latBasis L j).2 hg0
  have h2 : lamR (dualLat L) 1 ≤ rNorm w := Transf.lamR_le_rNorm (dualLat L) hwmem hw0
  rw [hrnw] at h2
  calc lamR L 1 * lamR (dualLat L) 1
      ≤ rNorm (Sig2.ThetaPoisson.latCoe L j) * (rNorm (Sig2.ThetaPoisson.latCoe L j))⁻¹ :=
        mul_le_mul h1 h2 (Transf.lamR_nonneg (dualLat L) 1) (Transf.rNorm_nonneg _)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hgpos)


/-- **The core of Banaszczyk's argument.**  If all nonzero vectors of a discrete lattice `M` of
rank `R ≥ 2` have norm at least `√R`, then the `R`-th minimum of the dual lattice is at most `√R`. -/
theorem transference_core (M : Submodule ℤ (ι → ℝ)) [DiscreteTopology M] (R : ℕ)
    (hR : Module.finrank ℤ M = R) (hR2 : 2 ≤ R)
    (hlam : ∀ z : M, z ≠ 0 → Real.sqrt (R : ℝ) ≤ rNorm (z : ι → ℝ)) :
    lamR (dualLat M) R ≤ Real.sqrt (R : ℝ) := by
  haveI hdisc : DiscreteTopology (dualLat M) := discreteTopology_dualLat M
  have hR' : Module.finrank ℤ (dualLat M) = R := by rw [finrank_dualLat M, hR]
  have hcard : Fintype.card (Sig2.ThetaPoisson.Idx (dualLat M)) = R := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (dualLat M), hR']
  by_contra hcon
  push_neg at hcon
  set r : ℝ := Real.sqrt (R : ℝ) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrank : Module.finrank ℤ (dualLat M) =
      Module.finrank ℝ (Submodule.span ℝ (dualLat M : Set (ι → ℝ))) :=
    (finrank_span_eq (dualLat M)).symm
  have h2r : 2 * r < lamR (dualLat M) (Module.finrank ℤ (dualLat M)) := by
    rw [hR', hrdef]; linarith
  obtain ⟨v, hv, hdist⟩ := exists_far_point (dualLat M) hrank hr0 h2r
  have hdist' : ∀ z ∈ dualLat M, r ≤ rNorm (v - z) := by
    intro z hz
    have h := hdist ⟨z, hz⟩
    have h2 : rNorm (v - z) = rNorm ((z : ι → ℝ) - v) := by
      rw [show v - z = -((z : ι → ℝ) - v) from by abel, rNorm_neg_aux]
    rw [h2]
    exact h
  have hγ0 : (0 : ℝ) < 2 / Real.pi := by positivity
  have hγ1 : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hkey := key_ineq (dualLat M) 1 one_pos hγ0 hγ1 v hv hr0.le hdist'
  have hconst : (1 / Real.sqrt (2 / Real.pi)) ^
        Fintype.card (Sig2.ThetaPoisson.Idx (dualLat M)) *
      Real.exp (-(Real.pi * (1 - 2 / Real.pi) * r ^ 2 / 1 ^ 2)) = Ehole R := by
    have hbase : (1 / Real.sqrt (2 / Real.pi)) ^
        Fintype.card (Sig2.ThetaPoisson.Idx (dualLat M)) = (Real.sqrt (Real.pi / 2)) ^ R := by
      rw [hcard]
      congr 1
      rw [one_div, ← inv_div (2 : ℝ) Real.pi, Real.sqrt_inv]
    have hexp : Real.exp (-(Real.pi * (1 - 2 / Real.pi) * r ^ 2 / 1 ^ 2))
        = Real.exp ((R : ℝ) / 2 - Real.pi * R / 4) := by
      congr 1
      rw [hrdef, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (R : ℝ)), one_pow]
      field_simp <;> ring
    rw [hbase, hexp, Ehole, mul_comm]
  have hρ1 : rhoD (dualLat M) 1 = theta M 1 0 := by
    rw [rhoD_dualLat_eq_theta M one_pos, inv_one]
  have hρ2 : rhoD (dualLat M) (1 / Real.sqrt (2 / Real.pi))
      = theta M (Real.sqrt (2 / Real.pi)) 0 := by
    rw [rhoD_dualLat_eq_theta M (by positivity)]
    congr 1
    rw [one_div, inv_inv]
  have hΘ : theta M (Real.sqrt (2 / Real.pi)) 0 ≤ theta M 1 0 :=
    theta_zero_mono M (by positivity) (by rw [Real.sqrt_le_one]; linarith [Real.pi_gt_three])
  have hhole : 2 - theta M 1 0 ≤ Ehole R * theta M 1 0 := by
    rw [hρ1, hconst, hρ2] at hkey
    exact hkey.trans (mul_le_mul_of_nonneg_left hΘ (by rw [Ehole]; positivity))
  have hs0 : (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hs1 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact (Real.one_le_sqrt).mpr (by nlinarith [Real.pi_gt_three])
  have hcardM : Fintype.card (Sig2.ThetaPoisson.Idx M) = R := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ M, hR]
  have hdi := theta_one_le_shell M (Real.sqrt (R : ℝ)) (Real.sqrt_nonneg _) hlam hs0 hs1
  have hdconst : Real.exp (Real.pi * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2 - 1) *
        (Real.sqrt (R : ℝ)) ^ 2) *
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹
      = Edelta R := by
    have hexp : Real.exp (Real.pi * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2 - 1) *
        (Real.sqrt (R : ℝ)) ^ 2) = Real.exp ((R : ℝ) / 2 - Real.pi * R) := by
      congr 1
      rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (R : ℝ))]
      field_simp <;> ring
    have hbase : ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Sig2.ThetaPoisson.Idx M))⁻¹
        = (Real.sqrt (2 * Real.pi)) ^ R := by
      rw [hcardM, ← inv_pow, inv_inv]
    rw [hexp, hbase, Edelta, mul_comm]
  rw [hdconst] at hdi
  set D : ℝ := theta M 1 0 with hDdef
  have hD0 : 0 < D := Sig2.theta_zero_pos M 1 one_pos
  have hA0 : 0 ≤ Ehole R := by rw [Ehole]; positivity
  have hnum := Ehole_lt_Edelta hR2
  have hBhalf : Edelta R < 1 / 2 := by linarith
  have h1 : D * (1 - Edelta R) ≤ 1 := by linarith [hdi]
  have h2 : D ≤ 1 / (1 - Edelta R) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 - Edelta R)]
    linarith
  have h3 : 2 - D ≤ Ehole R * (1 / (1 - Edelta R)) :=
    hhole.trans (mul_le_mul_of_nonneg_left h2 hA0)
  have h4 : (1 - 2 * Edelta R) / (1 - Edelta R) ≤ 2 - D := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - Edelta R)]
    linarith
  have hpos : 0 < 1 - Edelta R := by linarith
  have h5 : (1 - 2 * Edelta R) / (1 - Edelta R) ≤ Ehole R / (1 - Edelta R) := by
    have h6 : Ehole R * (1 / (1 - Edelta R)) = Ehole R / (1 - Edelta R) := by ring
    rw [h6] at h3
    exact le_trans h4 h3
  have h7 := mul_le_mul_of_nonneg_right h5 hpos.le
  rw [div_mul_cancel₀ _ (ne_of_gt hpos), div_mul_cancel₀ _ (ne_of_gt hpos)] at h7
  linarith

/-- `λ₁(L) · λ_R(L^*) ≤ R` for every discrete lattice `L` of rank `R`. -/
theorem lamR_dual_le (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (R : ℕ)
    (hR : Module.finrank ℤ L = R) : lamR L 1 * lamR (dualLat L) R ≤ (R : ℝ) := by
  rcases R with _ | _ | R
  · rw [lamR_zero, mul_zero]; norm_num
  · rw [Nat.cast_one]
    exact transference_rank_one L hR
  · by_cases hlamzero : lamR L 1 = 0
    · rw [hlamzero, zero_mul]; positivity
    · have hlampos : 0 < lamR L 1 := lt_of_le_of_ne (Transf.lamR_nonneg L 1) (Ne.symm hlamzero)
      set c : ℝ := Real.sqrt ((R : ℝ) + 2) / lamR L 1 with hc
      have hc0 : 0 < c := by rw [hc]; positivity
      have hcne : c ≠ 0 := ne_of_gt hc0
      haveI : DiscreteTopology (scaleLat c L) := scaleLat_discrete c hcne L
      have hfin : Module.finrank ℤ (scaleLat c L) = R + 2 := by
        rw [scaleLat_finrank c hcne L, hR]
      have hlamM : ∀ z : scaleLat c L, z ≠ 0 →
          Real.sqrt (((R + 2 : ℕ) : ℝ)) ≤ rNorm (z : ι → ℝ) := by
        intro z hz
        have h1 : lamR (scaleLat c L) 1 ≤ rNorm (z : ι → ℝ) :=
          Transf.lamR_le_rNorm _ z.2 (fun h => hz (Subtype.ext h))
        have h2 : lamR (scaleLat c L) 1 = Real.sqrt ((R : ℝ) + 2) := by
          rw [lamR_scaleLat c hc0 L 1, hc]
          field_simp
        rw [h2] at h1
        rwa [show ((R : ℝ) + 2) = (((R + 2 : ℕ) : ℝ)) from by push_cast; ring] at h1
      have hcore := transference_core (scaleLat c L) (R + 2) hfin (by omega) hlamM
      rw [dualLat_scaleLat c hcne L,
        lamR_scaleLat c⁻¹ (inv_pos.mpr hc0) (dualLat L) (R + 2)] at hcore
      have h4 : lamR (dualLat L) (R + 2) ≤ c * Real.sqrt ((R : ℝ) + 2) := by
        have h := mul_le_mul_of_nonneg_left hcore hc0.le
        rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at h
        have hcast : (((R + 2 : ℕ)) : ℝ) = (R : ℝ) + 2 := by push_cast; ring
        rwa [hcast] at h
      have h5 : c * Real.sqrt ((R : ℝ) + 2) = ((R + 2 : ℕ) : ℝ) / lamR L 1 := by
        have hsq : Real.sqrt ((R : ℝ) + 2) * Real.sqrt ((R : ℝ) + 2) = ((R + 2 : ℕ) : ℝ) := by
          rw [← sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (R : ℝ) + 2)]
          push_cast
          ring
        rw [hc, div_mul_eq_mul_div, mul_comm (Real.sqrt _), hsq]
      have h6 : lamR L 1 * lamR (dualLat L) (R + 2)
          ≤ lamR L 1 * (((R + 2 : ℕ) : ℝ) / lamR L 1) :=
        mul_le_mul_of_nonneg_left (h4.trans (le_of_eq h5)) hlampos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hlampos)] at h6
      exact h6

/-- **Banaszczyk's transference theorem**, extreme cases.  For a lattice `L` of rank `R` inside
`ℝ^ι` with dual `L^* = dualLat L`: `λ_1(L)·λ_R(L^*) ≤ R` and `λ_R(L)·λ_1(L^*) ≤ R`.

The proof follows Banaszczyk 1993: after scaling so that `λ₁(L) = √R`, the shifted Poisson
summation formula (`theta_cos_identity`) gives both a lower bound (`theta_lower`) and, using a
deep hole of the dual lattice (`exists_far_point`, `key_ineq`), an upper bound for the theta
function at the hole; combined with the shell bound for the mass `θ(1,0) - 1`
(`theta_one_le_shell`) this yields a numerical contradiction for `R ≥ 2`.  Rank `0` and rank `1`
are treated directly. -/
theorem transference_exact {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (R : ℕ) (hR : Module.finrank ℤ L = R) :
    lamR L 1 * lamR (dualLat L) R ≤ (R : ℝ) ∧
    lamR L R * lamR (dualLat L) 1 ≤ (R : ℝ) := by
  refine ⟨lamR_dual_le L R hR, ?_⟩
  haveI : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have h := lamR_dual_le (dualLat L) R (by rw [finrank_dualLat L, hR])
  rwa [dualLat_dualLat L, mul_comm] at h

end Work.HP.Lat
