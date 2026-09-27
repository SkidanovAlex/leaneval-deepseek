import Mathlib
import Submission.Work.Mostow.thinStrataGap
import Submission.Work.Mostow.strataGoodCase
import Submission.Work.Mostow.nearId_rotN_bound
import Submission.Work.Mostow.notNearIdAtBlkOne
import Submission.Work.Mostow.adaptFixedStratum

set_option synthInstance.maxHeartbeats 800000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### Elementary helpers -/

/-- A nonzero vector exists in a positive-dimensional Euclidean space. -/
lemma sgu_exists_ne_zero (m : ℕ) (hm : 1 ≤ m) : ∃ w : E m, w ≠ 0 := by
  refine ⟨(EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) : E m), ?_⟩
  intro h0
  have h1 : ‖(EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) : E m)‖ = 0 := by
    rw [h0, norm_zero]
  have h2 : ‖(EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) : E m)‖ = 1 := by
    simpa using PiLp.norm_single 2 (fun _ : Fin m => ℝ) (⟨0, hm⟩ : Fin m) (1 : ℝ)
  linarith

/-- A fixed-free linear isometry of a positive-dimensional space is not the identity. -/
lemma sgu_ne_one_of_free {m : ℕ} (hm : 1 ≤ m) {R : E m ≃ₗᵢ[ℝ] E m}
    (hR : ∀ w : E m, R w = w → w = 0) : R ≠ 1 := by
  intro h
  obtain ⟨w, hw⟩ := sgu_exists_ne_zero m hm
  exact hw (hR w (by simp [h]))

/-- `rotN R = 0` only for `R = 1`. -/
lemma sgu_rotN_eq_zero {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (h : rotN R = 0) : R = 1 := by
  have h1 : ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m)) = 0 := norm_eq_zero.mp h
  refine LinearIsometryEquiv.ext (fun x => ?_)
  have h2 := congrArg (fun f : E m →L[ℝ] E m => f x) h1
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] at h2
  exact sub_eq_zero.mp h2

/-- An isometry that is not the identity has positive `rotN`. -/
lemma sgu_rotN_pos_of_ne_one {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (h : R ≠ 1) : 0 < rotN R := by
  rcases lt_or_eq_of_le (norm_nonneg ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m))) with hlt | heq
  · simpa only [rotN] using hlt
  · exact absurd (sgu_rotN_eq_zero R heq.symm) h

/-- **Separation transfer.** If `S` is fixed-free and every non-identity element of `Λ` fixing the
standard stratum pointwise has `rotN S ≤ rotN` of its normal part, then every non-identity element
of `Λ` commuting with `blk k m 1 S` with trivial `resStd` also satisfies that inequality. -/
lemma sgu_sep_of_fix {k m : ℕ} (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) {S : E m ≃ₗᵢ[ℝ] E m}
    (hSfree : ∀ w : E m, S w = w → w = 0) {Λ : Subgroup (PO (k + m) 1)}
    (hsep : ∀ c : PO (k + m) 1, c ∈ Λ →
      (∀ v : E k, c • coordEmb k m v = coordEmb k m v) → c ≠ 1 →
      rotN S ≤ rotN (nrmStd k m c)) :
    ∀ c : PO (k + m) 1, c ∈ Λ →
      c ∈ Subgroup.centralizer ({blk k m 1 S} : Set (PO (k + m) 1)) →
      resStd k m c = 1 → c ≠ 1 → rotN S ≤ rotN (nrmStd k m c) := by
  intro c hcΛ hccen hres hcne
  have hP := POBasic.ofProp hA
  have hfix : fixSet (blk k m 1 S) = stdTG k m :=
    fixSet_blk_eq_stdTG k m hAk hIk hA hI S hSfree
  have hcomm : blk k m 1 S * c = c * blk k m 1 S :=
    hccen (blk k m 1 S) (Set.mem_singleton _)
  have hstab : c ∈ SetStabStd k m := by
    intro u
    rw [← hfix]
    constructor
    · intro hu
      rw [fixSet, Set.mem_setOf_eq] at hu ⊢
      rw [← hP.mul_smul, hcomm, hP.mul_smul, hu]
    · intro hu
      rw [fixSet, Set.mem_setOf_eq] at hu ⊢
      have h2 : c⁻¹ • (blk k m 1 S • (c • u)) = u := by
        rw [hu, ← hP.mul_smul, inv_mul_cancel, hP.one_smul]
      have hconj : c⁻¹ * blk k m 1 S * c = blk k m 1 S := by
        calc c⁻¹ * blk k m 1 S * c = c⁻¹ * (blk k m 1 S * c) := by rw [mul_assoc]
          _ = c⁻¹ * (c * blk k m 1 S) := by rw [hcomm]
          _ = (c⁻¹ * c) * blk k m 1 S := by rw [mul_assoc]
          _ = blk k m 1 S := by rw [inv_mul_cancel, one_mul]
      have h3 : (c⁻¹ * blk k m 1 S * c) • u = u := by
        rw [hP.mul_smul (c⁻¹ * blk k m 1 S) c u, hP.mul_smul c⁻¹ (blk k m 1 S) (c • u)]
        exact h2
      rwa [hconj] at h3
  have hdec : c = blk k m (resStd k m c) (nrmStd k m c) := stab_eq_blk k m hAk hIk hA hI c hstab
  have hfixpt : ∀ v : E k, c • coordEmb k m v = coordEmb k m v := by
    intro v
    rw [hdec, hres, rhd_blk_smul_coordEmb k m hAk hIk hA hI (1 : PO k 1) (nrmStd k m c) v,
      hAk.2.2.2.1 v]
  exact hsep c hcΛ hfixpt hcne

/-! ### Dimension casts -/

lemma sgu_volH_cast {a b : ℕ} (e : a = b) (s : Set (E a)) :
    volH b ((e ▸ s) : Set (E b)) = volH a s := by
  cases e; rfl

lemma sgu_isDiscrete_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) :
    IsDiscrete (Λ : Set (PO b 1)) →
      IsDiscrete (((e.symm ▸ Λ) : Subgroup (PO a 1)) : Set (PO a 1)) := by
  cases e; exact id

lemma sgu_isFundamentalDomain_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1))
    (D : Set (E b)) : IsFundamentalDomain Λ D (volH b) →
      IsFundamentalDomain ((e.symm ▸ Λ) : Subgroup (PO a 1)) ((e.symm ▸ D) : Set (E a)) (volH a) := by
  cases e; exact id

lemma sgu_mem_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) (x : PO a 1) :
    x ∈ (e.symm ▸ Λ : Subgroup (PO a 1)) ↔ (e ▸ x : PO b 1) ∈ Λ := by
  cases e; exact Iff.rfl

/-! ### The fixed-good-case normal form -/

/-- The conclusion of the fixed-good stratum inequality at normal dimension `M`, with the tangential
dimension `1 + m - M`. -/
def strataGoodStmt (m M : ℕ) (c α : ℝ) : Prop :=
  ∀ (Λ : Subgroup (PO ((1 + m - M) + M) 1)) (D : Set (E ((1 + m - M) + M)))
    (R : E M ≃ₗᵢ[ℝ] E M) (θ : ℝ),
    IsDiscrete (Λ : Set (PO ((1 + m - M) + M) 1)) →
    IsFundamentalDomain Λ D (volH ((1 + m - M) + M)) →
    blk (1 + m - M) M 1 R ∈ Λ → (∀ w : E M, R w = w → w = 0) → 0 < rotN R →
    rotN R ≤ 2 * θ → 0 < θ → θ ≤ 1 →
    (∀ c' : PO ((1 + m - M) + M) 1, c' ∈ Λ →
      c' ∈ Subgroup.centralizer ({blk (1 + m - M) M 1 R} : Set (PO ((1 + m - M) + M) 1)) →
      resStd (1 + m - M) M c' = 1 → c' ≠ 1 →
      rotN R ≤ rotN (nrmStd (1 + m - M) M c')) →
    ENNReal.ofReal (c * θ ^ (-α)) ≤ volH ((1 + m - M) + M) D

/-! ## The main theorem -/

theorem strataGapUniform (m : ℕ) (hm : 4 ≤ m) (hev : Even m) (hA : ∀ k, 1 ≤ k → Submission.Mostow.POActionProp k) (hI : ∀ k, 1 ≤ k → Submission.Mostow.HypIsometryProp k) (hCov : ∀ j, 2 ≤ j → j < 1 + m → Submission.Mostow.CovolLB j) : ∃ θ₀ c α : ℝ, 0 < θ₀ ∧ 0 < c ∧ 0 < α ∧ ∀ (j m' : ℕ) (hjm : j + m' = 1 + m) (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m') 1)) (D : Set (Submission.Mostow.E (j + m'))) (R : Submission.Mostow.E m' ≃ₗᵢ[ℝ] Submission.Mostow.E m') (u : Submission.Mostow.E (j + m')) (θ : ℝ), 2 ≤ j → 1 ≤ m' → _root_.IsDiscrete (SetLike.coe Λ) → MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (j + m')) → Submission.Mostow.blk j m' 1 R ∈ Λ → (∀ w : Submission.Mostow.E m', R w = w → w = 0) → Submission.Mostow.NearIdAt (Submission.Mostow.blk j m' 1 R) u θ → 0 < θ → θ ≤ θ₀ → ENNReal.ofReal (c * θ ^ (-α)) ≤ Submission.Mostow.volH (j + m') D := by
  obtain ⟨C0, hC0pos, hC0bound⟩ := nearId_rotN_bound
  -- the good-case family
  have hgood : ∀ M : ℕ, 1 ≤ M → M ≤ m - 1 →
      ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ strataGoodStmt m M c α :=
    fun M hM1 hMm => strataGoodCase (1 + m - M) M (by omega) hM1
  let Cg : ℕ → ℝ := fun M => if h : 1 ≤ M ∧ M ≤ m - 1 then (hgood M h.1 h.2).choose else 1
  let Ag : ℕ → ℝ := fun M => if h : 1 ≤ M ∧ M ≤ m - 1 then (hgood M h.1 h.2).choose_spec.choose else 1
  have hCg_eq : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), Cg M = (hgood M h1 h2).choose := by
    intro M h1 h2
    dsimp only [Cg]
    rw [dif_pos ⟨h1, h2⟩]
  have hAg_eq : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), Ag M = (hgood M h1 h2).choose_spec.choose := by
    intro M h1 h2
    dsimp only [Ag]
    rw [dif_pos ⟨h1, h2⟩]
  have hCgpos : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), 0 < Cg M := by
    intro M h1 h2
    rw [hCg_eq M h1 h2]
    exact (hgood M h1 h2).choose_spec.choose_spec.1
  have hAgpos : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), 0 < Ag M := by
    intro M h1 h2
    rw [hAg_eq M h1 h2]
    exact (hgood M h1 h2).choose_spec.choose_spec.2.1
  have hCgspec : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), strataGoodStmt m M (Cg M) (Ag M) := by
    intro M h1 h2
    rw [hCg_eq M h1 h2, hAg_eq M h1 h2]
    exact (hgood M h1 h2).choose_spec.choose_spec.2.2
  -- the finite minimum of the good constants
  let Ms : Finset ℕ := Finset.Icc 1 (m - 1)
  have hMs : Ms.Nonempty := by
    refine ⟨1, ?_⟩
    show (1 : ℕ) ∈ Finset.Icc 1 (m - 1)
    rw [Finset.mem_Icc]; omega
  let cvals : Finset ℝ := Ms.image (fun M => Cg M * C0 ^ (-(Ag M)))
  let avals : Finset ℝ := Ms.image Ag
  set c : ℝ := cvals.min' (hMs.image (fun M => Cg M * C0 ^ (-(Ag M)))) with hcdef
  set α : ℝ := avals.min' (hMs.image Ag) with hαdef
  have hmemMs : ∀ M : ℕ, 1 ≤ M → M ≤ m - 1 → M ∈ Ms := by
    intro M h1 h2; dsimp only [Ms]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hMem : ∀ M : ℕ, M ∈ Ms → 1 ≤ M ∧ M ≤ m - 1 :=
    fun M hM => Finset.mem_Icc.mp (show M ∈ Finset.Icc 1 (m - 1) from hM)
  have hcle : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), c ≤ Cg M * C0 ^ (-(Ag M)) := by
    intro M h1 h2
    rw [hcdef]
    exact Finset.min'_le cvals _ (Finset.mem_image_of_mem (fun M => Cg M * C0 ^ (-(Ag M)))
      (hmemMs M h1 h2))
  have hαle : ∀ M (h1 : 1 ≤ M) (h2 : M ≤ m - 1), α ≤ Ag M := by
    intro M h1 h2
    rw [hαdef]
    exact Finset.min'_le avals _ (Finset.mem_image_of_mem Ag (hmemMs M h1 h2))
  have hcpos : 0 < c := by
    rw [hcdef]
    obtain ⟨M, hM, hMeq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem cvals (hMs.image (fun M => Cg M * C0 ^ (-(Ag M)))))
    rw [← hMeq]
    exact mul_pos (hCgpos M (hMem M hM).1 (hMem M hM).2) (Real.rpow_pos_of_pos hC0pos _)
  have hαpos : 0 < α := by
    rw [hαdef]
    obtain ⟨M, hM, hMeq⟩ := Finset.mem_image.mp (Finset.min'_mem avals (hMs.image Ag))
    rw [← hMeq]
    exact hAgpos M (hMem M hM).1 (hMem M hM).2
  -- the induction over the normal dimension
  have MAIN : ∀ M : ℕ, 1 ≤ M → M ≤ m - 1 →
      ∀ (Λ : Subgroup (PO ((1 + m - M) + M) 1)) (D : Set (E ((1 + m - M) + M)))
        (R : E M ≃ₗᵢ[ℝ] E M) (θ : ℝ),
        IsDiscrete (Λ : Set (PO ((1 + m - M) + M) 1)) →
        IsFundamentalDomain Λ D (volH ((1 + m - M) + M)) →
        blk (1 + m - M) M 1 R ∈ Λ → (∀ w : E M, R w = w → w = 0) →
        0 < θ → θ ≤ min 1 (1 / C0) → rotN R ≤ 2 * C0 * θ →
        ENNReal.ofReal (c * θ ^ (-α)) ≤ volH ((1 + m - M) + M) D := by
      intro M
      refine Nat.strong_induction_on M ?_
      intro M ih hM1 hMm Λ D R θ hdisc hD hb hfree hθ0 hθle hrot
      have hθ1 : θ ≤ 1 := le_trans hθle (min_le_left _ _)
      have hθC : θ ≤ 1 / C0 := le_trans hθle (min_le_right _ _)
      have hθC' : C0 * θ ≤ 1 := by
        rw [mul_comm]; exact (le_div_iff₀ hC0pos).mp hθC
      have hRne : R ≠ 1 := sgu_ne_one_of_free hM1 hfree
      have hRpos : 0 < rotN R := sgu_rotN_pos_of_ne_one R hRne
      have hAj : POActionProp (1 + m - M) := hA _ (by omega)
      have hIj : HypIsometryProp (1 + m - M) := hI _ (by omega)
      have hAamb : POActionProp ((1 + m - M) + M) := hA _ (by omega)
      have hIamb : HypIsometryProp ((1 + m - M) + M) := hI _ (by omega)
      obtain ⟨S, hSpos, hSle, hbS, hSsep⟩ :=
        exists_min_pointwiseStab (1 + m - M) M (by omega) hAamb hIamb Λ hdisc R hb hRpos
      by_cases hSfree : ∀ w : E M, S w = w → w = 0
      · -- ### the fixed-free (good) case
        have hsepgood := sgu_sep_of_fix hAj hIj hAamb hIamb hSfree hSsep
        have hrotS : rotN S ≤ 2 * (C0 * θ) := by nlinarith [hSle, hrot]
        have hgc : ENNReal.ofReal (Cg M * (C0 * θ) ^ (-(Ag M)))
            ≤ volH ((1 + m - M) + M) D :=
          hCgspec M hM1 hMm Λ D S (C0 * θ) hdisc hD hbS hSfree hSpos hrotS (by positivity) hθC' hsepgood
        have h1 : c ≤ Cg M * C0 ^ (-(Ag M)) := hcle M hM1 hMm
        have h2 : θ ^ (-α) ≤ θ ^ (-(Ag M)) :=
          Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 (by linarith [hαle M hM1 hMm])
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hgc
        calc c * θ ^ (-α) ≤ (Cg M * C0 ^ (-(Ag M))) * θ ^ (-(Ag M)) :=
              mul_le_mul h1 h2 (Real.rpow_nonneg hθ0.le _)
                (mul_nonneg (hCgpos M hM1 hMm).le (Real.rpow_nonneg hC0pos.le _))
          _ = Cg M * (C0 * θ) ^ (-(Ag M)) := by
              rw [Real.mul_rpow hC0pos.le hθ0.le]; ring
      · -- ### the bad case: adapt to the fixed stratum of `S`
        push_neg at hSfree
        obtain ⟨k₂, M₂, hk₂M₂, Λ₂, D₂, R₂, hk₂2, hM₂1, hM₂lt, hdisc₂, hD₂, hvol₂, hb₂, hfree₂,
          hrot₂⟩ :=
          adaptFixedStratum (1 + m - M) M (by omega) hM1 hA hI Λ D S hdisc hD hbS hSpos hSfree
        have hk₂ : k₂ = 1 + m - M₂ := by omega
        subst hk₂
        have hM₂m : M₂ ≤ m - 1 := by omega
        have hrot₂' : rotN R₂ ≤ 2 * C0 * θ := by nlinarith [hrot₂, hSle, hrot]
        have hih := ih M₂ hM₂lt hM₂1 hM₂m (hk₂M₂.symm ▸ Λ₂) (hk₂M₂.symm ▸ D₂) R₂ θ
          (sgu_isDiscrete_cast hk₂M₂ Λ₂ hdisc₂)
          (sgu_isFundamentalDomain_cast hk₂M₂ Λ₂ D₂ hD₂)
          ((sgu_mem_cast hk₂M₂ Λ₂ (blk (1 + m - M₂) M₂ 1 R₂)).mpr hb₂)
          hfree₂ hθ0 hθle hrot₂'
        rwa [sgu_volH_cast hk₂M₂.symm D₂, hvol₂] at hih
  refine ⟨min 1 (1 / C0), c, α, lt_min one_pos (by positivity), hcpos, hαpos, ?_⟩
  intro j m' hjm
  have hj' : j = 1 + m - m' := by omega
  subst hj'
  intro Λ D R u θ hj hm1m hdisc hD hb hfree hni hθ0 hθle
  rcases eq_or_lt_of_le hm1m with h1 | h2
  · have hm1 : m' = 1 := h1.symm
    subst hm1
    exact absurd hni (notNearIdAtBlkOne (1 + m - 1) (hA _ (by omega)) (hI _ (by omega))
      (hA _ (by omega)) (hI _ (by omega)) R hfree u θ (le_trans hθle (min_le_left _ _)))
  · have hθ1 : θ ≤ 1 := le_trans hθle (min_le_left _ _)
    have hrot : rotN R ≤ C0 * θ :=
      hC0bound (1 + m - m') m' R u θ (hA _ (by omega)) (hI _ (by omega)) (hA _ (by omega))
        (hI _ (by omega)) h2 hθ0 hθ1 hni
    have hrot' : rotN R ≤ 2 * C0 * θ := by nlinarith [hrot, hC0pos.le, hθ0.le]
    have hMm : m' ≤ m - 1 := by omega
    exact MAIN m' hm1m hMm Λ D R θ hdisc hD hb hfree hθ0 hθle hrot'

end

end Work.Mostow
