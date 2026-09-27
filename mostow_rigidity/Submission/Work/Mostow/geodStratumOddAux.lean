import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.strataGapUniform
import Submission.Work.Mostow.torsionNearIdGeodesic
import Submission.Work.Mostow.conjCountGeodV2
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.fermiLineTwo

/-!
# Reduction of the geodesic stratum (`k = 1`, odd ambient dimension) to its element step

The target statement of `Submission/Work/Mostow/geodStratumOddProved.lean` differs from the
*element step* `GeodStep m` below only by the classification of a near-identity element:

* `nearGrp Λ z η ≠ ⊥` gives `g ∈ Λ ∖ {1}` with `NearIdAt g z η` (`nearGrp_ne_bot_iff'`);
* if `orderOf g = 0`, the conclusion holds with `C = 1` (`exists_of_nearIdAt_infiniteOrder'`);
* otherwise `g` is torsion and `Work.Mostow.torsionNearIdGeodesic` (with the covolume gap
  `Work.Mostow.strataGapUniform` as the `hgap` input) produces `h` and a *fixed-vector-free*
  `R : E m ≃ₗᵢ[ℝ] E m` with `g * h = h * blk 1 m 1 R`: `g` is conjugate to the block `blk 1 m 1 R`,
  the rotation about a geodesic;
* conjugating `Λ`, `D`, `z` by `h⁻¹` (`isDiscrete_map_conj`, `conj_fundamentalDomain`,
  `volH_smul_image`, `nearIdAt_conj_iff`) brings the problem into the exact shape of the element
  step, and the answer is transported back (`hdist` and `orderOf` are conjugation invariant).

This file is self-contained: it does not import `Submission/Work/Mostow/geodStratum.lean` (which
is under construction elsewhere), re-proving the three one-line helpers it needs.  The element
step itself is proved in a separate module.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- `nearGrp` is nontrivial exactly when some non-identity element of `Λ` is `η`-near-identity
at `z`. -/
lemma nearGrp_ne_bot_iff' {n : ℕ} (Λ : Subgroup (PO n 1)) (z : E n) (η : ℝ) :
    nearGrp Λ z η ≠ ⊥ ↔ ∃ g ∈ Λ, g ≠ 1 ∧ NearIdAt g z η := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ g : PO n 1, g ∈ Λ → NearIdAt g z η → g = 1 := by
      intro g hg1 hg2
      by_contra hne
      exact hc ⟨g, hg1, hne, hg2⟩
    exact h (Subgroup.closure_eq_bot_iff.mpr (fun g hg => hc' g hg.1 hg.2))
  · rintro ⟨g, hgΛ, hg1, hgnear⟩ hbot
    have hmem : g ∈ (⊥ : Subgroup (PO n 1)) := by
      rw [← hbot]
      exact Subgroup.subset_closure ⟨hgΛ, hgnear⟩
    exact hg1 (Subgroup.mem_bot.mp hmem)

/-- `NearIdAt` bounds the displacement of its centre. -/
lemma hdist_le_of_nearIdAt' {n : ℕ} (hI : HypIsometryProp n) {g : PO n 1} {z : E n} {η : ℝ}
    (h : NearIdAt g z η) : hdist z (g • z) < η :=
  h z (by rw [(hI.2.2.1 z z).mpr rfl]; norm_num)

/-- An infinite-order `η`-near-identity element already witnesses the conclusion, with `C = 1`. -/
lemma exists_of_nearIdAt_infiniteOrder' {n : ℕ} (hI : HypIsometryProp n)
    (Λ : Subgroup (PO n 1)) (z : E n) (η C : ℝ) (hη : 0 < η) (hC : 1 ≤ C)
    (h : ∃ g ∈ Λ, orderOf g = 0 ∧ NearIdAt g z η) :
    ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ C * η := by
  obtain ⟨g, hgΛ, hgord, hgnear⟩ := h
  refine ⟨g, hgΛ, hgord, le_trans (le_of_lt (hdist_le_of_nearIdAt' hI hgnear)) ?_⟩
  nlinarith [hC, hη]

/-- `orderOf` vanishes exactly for elements of infinite order. -/
lemma orderOf_eq_zero_iff' {n : ℕ} (g : PO n 1) :
    orderOf g = 0 ↔ ¬ IsOfFinOrder g := orderOf_eq_zero_iff

/-- **The element step** of the geodesic stratum: if a fixed-vector-free block `blk 1 m 1 R` lies
in a discrete `Λ` with a fundamental domain of volume `≤ V` and is `η`-near-identity at `z`
(`η ≤ η₀(V)`), then some *infinite-order* element of `Λ` moves `z` by at most `C η`, with `C`
depending only on `m`.  This is the geometric core of the geodesic stratum; it is proved in the
module `Submission/Work/Mostow/geodStep.lean`. -/
def GeodStep (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ V : ℝ, 0 < V → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (Λ : Subgroup (PO (1 + m) 1)) (D : Set (E (1 + m))) (R : E m ≃ₗᵢ[ℝ] E m)
        (z : E (1 + m)),
        IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + m)) →
        volH (1 + m) D ≤ ENNReal.ofReal V → blk 1 m 1 R ∈ Λ →
        (∀ w : E m, R w = w → w = 0) → NearIdAt (blk 1 m 1 R) z η →
        ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ C * η

/-- `(MulAut.conj h⁻¹) x = h⁻¹ * x * h`. -/
lemma conjInv_apply' {n : ℕ} (h x : PO n 1) :
    (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
  show MulAut.conj h⁻¹ x = h⁻¹ * x * h
  rw [MulAut.conj_apply, inv_inv]

/-- Conjugation preserves finite order (the direction needed to transport `orderOf`). -/
lemma isOfFinOrder_conj' {n : ℕ} {g b : PO n 1} (h : IsOfFinOrder b) :
    IsOfFinOrder (g⁻¹ * b * g) := by
  rw [isOfFinOrder_iff_pow_eq_one] at h ⊢
  obtain ⟨m, hm, hbm⟩ := h
  refine ⟨m, hm, ?_⟩
  have hcp : (g⁻¹ * b * g) ^ m = g⁻¹ * b ^ m * g := by
    have h' := map_pow (MulAut.conj g⁻¹).toMonoidHom b m
    simpa [conjInv_apply'] using h'.symm
  rw [hcp, hbm, mul_one, inv_mul_cancel]

/-- **The geodesic stratum lemma**, reduced to the element step `GeodStep m`. -/
theorem geodStratum_of_block (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hAall : ∀ k, 1 ≤ k → POActionProp k) (hIall : ∀ k, 1 ≤ k → HypIsometryProp k)
    (hCov : ∀ j, 2 ≤ j → j < 1 + m → CovolLB j) (hstep : GeodStep m) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ (Λ : Subgroup (PO (1 + m) 1)) (D : Set (E (1 + m))) (z : E (1 + m)),
          IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + m)) →
          volH (1 + m) D ≤ ENNReal.ofReal V → nearGrp Λ z η ≠ ⊥ →
          Finite ↥(nearGrp Λ z η) →
          ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ C * η := by
  obtain ⟨C₀, hC₀pos, hstepV⟩ := hstep
  -- the statement for positive `V`, by the classification of a near-identity element
  have hP : ∀ V : ℝ, 0 < V → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ (Λ : Subgroup (PO (1 + m) 1)) (D : Set (E (1 + m))) (z : E (1 + m)),
          IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + m)) →
          volH (1 + m) D ≤ ENNReal.ofReal V → nearGrp Λ z η ≠ ⊥ →
          Finite ↥(nearGrp Λ z η) →
          ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ max C₀ 1 * η := by
    intro V hV
    obtain ⟨η₀₁, hη₀₁pos, hstepη⟩ := hstepV V hV
    obtain ⟨θ₀, c, α, hθ₀, hc, hα, hgap⟩ := strataGapUniform m hm hev hAall hIall hCov
    obtain ⟨η₀₂, hη₀₂pos, hclass⟩ :=
      torsionNearIdGeodesic m hm hev hAall hIall θ₀ c α hθ₀ hc hα hgap V
    refine ⟨min η₀₁ η₀₂, lt_min hη₀₁pos hη₀₂pos, ?_⟩
    intro η hηpos hηle Λ D z hdisc hD hvol hnearne hfin
    have hη₁ : η ≤ η₀₁ := le_trans hηle (min_le_left _ _)
    have hη₂ : η ≤ η₀₂ := le_trans hηle (min_le_right _ _)
    obtain ⟨g, hgΛ, hgne, hgnear⟩ := (nearGrp_ne_bot_iff' Λ z η).mp hnearne
    by_cases hord : orderOf g = 0
    · exact exists_of_nearIdAt_infiniteOrder' (hIall (1 + m) (by omega)) Λ z η (max C₀ 1)
        hηpos (le_max_right _ _) ⟨g, hgΛ, hord, hgnear⟩
    · have hfinord : IsOfFinOrder g := by
        by_contra hc'
        exact hord ((orderOf_eq_zero_iff' g).mpr hc')
      obtain ⟨h, R, hRfree, hconj⟩ :=
        hclass η hηpos hη₂ Λ D z g hdisc hD hvol hgΛ hgne hfinord hgnear
      have hAh : POActionProp (1 + m) := hAall (1 + m) (by omega)
      have hIh : HypIsometryProp (1 + m) := hIall (1 + m) (by omega)
      have hb : blk 1 m 1 R = h⁻¹ * g * h := by
        have h2 : h⁻¹ * (g * h) = h⁻¹ * (h * blk 1 m 1 R) := by rw [hconj]
        have h3 : h⁻¹ * g * h = h⁻¹ * (g * h) := mul_assoc _ _ _
        have h4 : h⁻¹ * (h * blk 1 m 1 R) = blk 1 m 1 R := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        calc blk 1 m 1 R = h⁻¹ * (h * blk 1 m 1 R) := h4.symm
          _ = h⁻¹ * (g * h) := h2.symm
          _ = h⁻¹ * g * h := h3.symm
      set Λ' : Subgroup (PO (1 + m) 1) := Λ.map (MulAut.conj h⁻¹).toMonoidHom with hΛ'def
      have hmem' : blk 1 m 1 R ∈ Λ' := by
        have h5 : (MulAut.conj h⁻¹).toMonoidHom g = blk 1 m 1 R := by
          rw [conjInv_apply', hb]
        rw [← h5]
        exact Subgroup.mem_map_of_mem _ hgΛ
      have hdisc' : IsDiscrete (SetLike.coe Λ') := isDiscrete_map_conj hdisc h
      have hD' : IsFundamentalDomain Λ' ((fun u : E (1 + m) => h⁻¹ • u) '' D) (volH (1 + m)) :=
        conj_fundamentalDomain (1 + m) hAh hIh Λ D hD h⁻¹
      have hvol' : volH (1 + m) ((fun u : E (1 + m) => h⁻¹ • u) '' D) ≤ ENNReal.ofReal V := by
        rw [volH_smul_image hAh hIh h⁻¹ D]; exact hvol
      have hnear' : NearIdAt (blk 1 m 1 R) (h⁻¹ • z) η := by
        rw [hb]
        refine (nearIdAt_conj_iff hAh hIh h g (h⁻¹ • z) η).mpr ?_
        rw [← hAh.2.2.2.2.1, mul_inv_cancel, hAh.2.2.2.1]
        exact hgnear
      obtain ⟨γ', hγ'Λ', hγ'ord, hγ'dis⟩ :=
        hstepη η hηpos hη₁ Λ' ((fun u : E (1 + m) => h⁻¹ • u) '' D) R (h⁻¹ • z)
          hdisc' hD' hvol' hmem' hRfree hnear'
      obtain ⟨γ, hγΛ, hγmap⟩ := Subgroup.mem_map.mp hγ'Λ'
      refine ⟨γ, hγΛ, ?_, ?_⟩
      · have h2 : γ' = h⁻¹ * γ * h := hγmap.symm.trans (conjInv_apply' h γ)
        rw [h2] at hγ'ord
        rw [orderOf_eq_zero_iff'] at hγ'ord
        rw [orderOf_eq_zero_iff']
        intro hfin
        exact hγ'ord (isOfFinOrder_conj' hfin)
      · have hγ'eq : γ' = h⁻¹ * γ * h := hγmap.symm.trans (conjInv_apply' h γ)
        have hdis : hdist z (γ • z) = hdist (h⁻¹ • z) (γ' • (h⁻¹ • z)) := by
          have hs : h • (h⁻¹ • z) = z := by
            rw [← hAh.2.2.2.2.1, mul_inv_cancel, hAh.2.2.2.1]
          have hact : γ' • (h⁻¹ • z) = h⁻¹ • (γ • z) := by
            rw [hγ'eq, hAh.2.2.2.2.1 (h⁻¹ * γ) h (h⁻¹ • z),
              hAh.2.2.2.2.1 h⁻¹ γ (h • (h⁻¹ • z)), hs]
          rw [hact]
          exact (hIh.2.2.2.2.2.2.1 h⁻¹ z (γ • z)).symm
        rw [hdis]
        exact le_trans hγ'dis (by nlinarith [le_max_left C₀ 1, hηpos])
  refine ⟨max C₀ 1, lt_max_of_lt_left hC₀pos, ?_⟩
  intro V
  by_cases hV : 0 < V
  · exact hP V hV
  · obtain ⟨η₀, hη₀pos, hmain⟩ := hP 1 one_pos
    refine ⟨η₀, hη₀pos, ?_⟩
    intro η hηpos hηle Λ D z hdisc hD hvol hnearne hfin
    exact hmain η hηpos hηle Λ D z hdisc hD
      (le_trans hvol (ENNReal.ofReal_le_ofReal (by linarith [not_lt.mp hV]))) hnearne hfin

end Work.Mostow
