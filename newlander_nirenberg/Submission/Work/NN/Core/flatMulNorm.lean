import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The `C^{m,α}` norm of `φ·w` for `φ` flat outside a polydisc

This file proves `Work.NN.Core.flatMulNorm`: if `φ : ℂⁿ → ℂ` is smooth and vanishes on the closed
complement of the open polydisc `P(ρ) = polydisc 0 ρ`, and `w` is `C^m` on `P(ρ)` with finite
`C^{m,α}` norm there, and the product `z ↦ φ z * w z` is `C^m` on all of `ℂⁿ`, then the
`C^{m,α}` norm of the product over `ℂⁿ` is bounded by a constant times the product of the
`C^{m,α}` norms of the two factors.

The key point is that the product is *supported* in the closed polydisc, and — because it is `C^m`
— all of its iterated derivatives up to order `m` vanish on the closed complement of `P(ρ)`.
Hence its `C^{m,α}` norm over `ℂⁿ` is bounded by the one over `P(ρ)`
(`holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing`), where the Leibniz bound
`Work.CR.Flat.Holder.holderNorm_mul_le` applies.
-/

noncomputable section

open scoped NNReal ENNReal Topology
open Set Filter

namespace Work.NN.Core

/-! ## Geometry -/

/-- A point of the closed complement `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc is a limit
of points of the open exterior `{z | ∃ j, ρ j < ‖z j‖}`. -/
lemma mem_closure_polydisc_exterior {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {z : Fin n → ℂ} (hz : ∃ j, ρ j ≤ ‖z j‖) :
    z ∈ closure {w : Fin n → ℂ | ∃ j, ρ j < ‖w j‖} := by
  classical
  obtain ⟨j, hj⟩ := hz
  set w₀ : Fin n → ℂ := Pi.single j (z j) with hw₀
  set f : ℝ → (Fin n → ℂ) := fun t => z + t • w₀ with hf
  have hfcont : Continuous f := by
    rw [hf]; exact continuous_const.add (continuous_id.smul continuous_const)
  have hf0 : f 0 = z := by simp [hf]
  have hsub : f '' Set.Ioi (0 : ℝ) ⊆ {w : Fin n → ℂ | ∃ i, ρ i < ‖w i‖} := by
    rintro y ⟨t, ht, rfl⟩
    rw [Set.mem_Ioi] at ht
    refine ⟨j, ?_⟩
    have h1 : (f t) j = (1 + (t : ℂ)) * z j := by
      simp only [hf, Pi.add_apply, Pi.smul_apply, hw₀, Pi.single_eq_same, Complex.real_smul]
      ring
    have h2 : ‖(1 + (t : ℂ))‖ = 1 + t := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
    rw [h1, norm_mul, h2]
    nlinarith [hj, hρ j, norm_nonneg (z j), ht]
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨ε / 2, by rw [Set.mem_Ioi]; linarith, by
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
      linarith⟩
  have h1 : z ∈ f '' closure (Set.Ioi (0 : ℝ)) := ⟨0, h0, hf0⟩
  exact closure_mono hsub (image_closure_subset_closure_image hfcont h1)

/-- Every point of the closed polydisc `{z | ∀ j, ‖z j‖ ≤ ρ j}` is a limit of points of the
open polydisc. -/
lemma mem_closure_polydisc_of_forall_norm_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {z : Fin n → ℂ} (hz : ∀ j, ‖z j‖ ≤ ρ j) :
    z ∈ closure (Work.CR.Flat.polydisc 0 ρ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / (‖z‖ + 1)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδle : δ ≤ ε / (‖z‖ + 1) := min_le_right _ _
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨(1 - δ) • z, ?_, ?_⟩
  · rw [Work.CR.Flat.mem_polydisc]
    intro j
    have hcpos : 0 < 1 - δ := by linarith
    have hcle : 1 - δ < 1 := by linarith
    have hcoord : ((1 - δ) • z) j = (((1 - δ : ℝ)) : ℂ) * z j := by
      rw [Pi.smul_apply, Complex.real_smul]
    rw [hcoord, Pi.zero_apply, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcpos]
    nlinarith [hz j, hρ j, hcpos, hcle]
  · rw [dist_eq_norm]
    have hsub : z - (1 - δ) • z = δ • z := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_sub,
        Complex.ofReal_one]
      ring
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : δ * ‖z‖ ≤ (ε / (‖z‖ + 1)) * ‖z‖ :=
      mul_le_mul_of_nonneg_right hδle (norm_nonneg z)
    have h2 : (ε / (‖z‖ + 1)) * ‖z‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg z]
    linarith

/-! ## Vanishing of the iterated derivatives on the closed complement -/

/-- If a `C^m` function vanishes on the closed complement of the open polydisc, then all of its
iterated derivatives of order `≤ m` vanish there. -/
lemma iteratedFDeriv_eq_zero_of_vanishing_closedComplement {n : ℕ} {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {m : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ m g)
    (hvan : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → g z = 0) :
    ∀ i ≤ m, ∀ z, (∃ j, ρ j ≤ ‖z j‖) → iteratedFDeriv ℝ i g z = 0 := by
  intro i hi z hz
  set U : Set (Fin n → ℂ) := {w | ∃ j, ρ j < ‖w j‖} with hU
  have hUopen : IsOpen U := by
    rw [hU, show {w : Fin n → ℂ | ∃ j, ρ j < ‖w j‖} = ⋃ j, {w | ρ j < ‖w j‖} from by
      ext w; simp]
    exact isOpen_iUnion fun j => isOpen_lt continuous_const ((continuous_apply j).norm)
  have hvanU : Set.EqOn (iteratedFDeriv ℝ i g)
      (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ)) U := by
    intro y hy
    have hA : iteratedFDerivWithin ℝ i g U y =
        iteratedFDerivWithin ℝ i (fun _ => (0 : ℂ)) U y :=
      iteratedFDerivWithin_congr
        (fun w hw => hvan w (by obtain ⟨k, hk⟩ := hw; exact ⟨k, le_of_lt hk⟩)) hy i
    have hB : iteratedFDerivWithin ℝ i g U y = iteratedFDeriv ℝ i g y :=
      (iteratedFDerivWithin_of_isOpen (s := U) i hUopen) hy
    have hC : iteratedFDerivWithin ℝ i (fun _ => (0 : ℂ)) U y =
        iteratedFDeriv ℝ i (fun _ => (0 : ℂ)) y :=
      (iteratedFDerivWithin_of_isOpen (s := U) i hUopen) hy
    rw [← hB, hA, hC, iteratedFDeriv_fun_zero]
    rfl
  have hcont : Continuous (iteratedFDeriv ℝ i g) :=
    hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)
  have hzcl : z ∈ closure U := mem_closure_polydisc_exterior hρ hz
  exact Set.EqOn.closure hvanU hcont continuous_const hzcl

/-! ## The metric lemma at the boundary -/

/-- If `h` is continuous and vanishes on the closed complement of the open polydisc, and `x` lies
in the polydisc while `y` lies in its closed complement, then the divided difference term at
`(x,y)` is bounded by the supremum of the corresponding terms with `y` replaced by a point of the
polydisc. -/
lemma ofReal_term_le_iSup_of_vanishing {n : ℕ} {α : ℝ} (hα0 : 0 < α)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {V : Type*} [NormedAddCommGroup V]
    {h : (Fin n → ℂ) → V} (hcont : Continuous h)
    (hzero : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → h z = 0)
    {x y : Fin n → ℂ} (hx : x ∈ Work.CR.Flat.polydisc 0 ρ) (hy : ∃ j, ρ j ≤ ‖y j‖) :
    ENNReal.ofReal (‖h x - h y‖ / ‖x - y‖ ^ α)
      ≤ ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ⨆ (_ : x ≠ z),
          ENNReal.ofReal (‖h x - h z‖ / ‖x - z‖ ^ α) := by
  obtain ⟨jy, hjy⟩ := hy
  have hxjy : ‖x jy‖ < ρ jy := by
    have h' := (Work.CR.Flat.mem_polydisc.mp hx) jy; simpa using h'
  have hxle : ∀ i, ‖x i‖ ≤ ρ i := fun i => by
    have h' := (Work.CR.Flat.mem_polydisc.mp hx) i; simpa using h'.le
  have hy0 : h y = 0 := hzero y ⟨jy, hjy⟩
  have key : ∃ y' : Fin n → ℂ, (∃ j, ρ j ≤ ‖y' j‖) ∧ ‖x - y'‖ ≤ ‖x - y‖ ∧
      y' ∈ closure (Work.CR.Flat.polydisc 0 ρ) := by
    by_cases hxj : x jy = 0
    · refine ⟨Function.update x jy (ρ jy : ℂ), ⟨jy, ?_⟩, ?_, ?_⟩
      · rw [Function.update_self, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ jy)]
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))]
        intro i
        rw [Pi.sub_apply]
        by_cases hi : i = jy
        · rw [hi]
          rw [Function.update_self, hxj, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (hρ jy)]
          calc ρ jy ≤ ‖y jy - x jy‖ := by rw [hxj, sub_zero]; exact hjy
            _ = ‖x jy - y jy‖ := norm_sub_rev _ _
            _ = ‖(x - y) jy‖ := by rw [Pi.sub_apply]
            _ ≤ ‖x - y‖ := norm_le_pi_norm _ _
        · rw [Function.update_of_ne hi, sub_self, norm_zero]; positivity
      · apply mem_closure_polydisc_of_forall_norm_le hρ
        intro i
        by_cases hi : i = jy
        · rw [hi, Function.update_self, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ jy)]
        · rw [Function.update_of_ne hi]; exact hxle i
    · have hxjpos : 0 < ‖x jy‖ := norm_pos_iff.mpr hxj
      refine ⟨Function.update x jy (((ρ jy / ‖x jy‖ : ℝ) : ℂ) * x jy), ⟨jy, ?_⟩, ?_, ?_⟩
      · rw [Function.update_self, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (div_pos (hρ jy) hxjpos), div_mul_cancel₀ _ (ne_of_gt hxjpos)]
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))]
        intro i
        rw [Pi.sub_apply]
        by_cases hi : i = jy
        · rw [hi]
          rw [Function.update_self]
          have hne : ‖x jy‖ ≠ 0 := ne_of_gt hxjpos
          have hval : ‖x jy - ((ρ jy / ‖x jy‖ : ℝ) : ℂ) * x jy‖ = ρ jy - ‖x jy‖ := by
            have he : x jy - ((ρ jy / ‖x jy‖ : ℝ) : ℂ) * x jy
                = (1 - ((ρ jy / ‖x jy‖ : ℝ) : ℂ)) * x jy := by ring
            rw [he, norm_mul]
            have h1 : ‖(1 : ℂ) - ((ρ jy / ‖x jy‖ : ℝ) : ℂ)‖ = ρ jy / ‖x jy‖ - 1 := by
              rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
              have hle : (1 : ℝ) - ρ jy / ‖x jy‖ ≤ 0 := by
                have h1le : 1 ≤ ρ jy / ‖x jy‖ :=
                  (le_div_iff₀ hxjpos).mpr (by rw [one_mul]; exact hxjy.le)
                linarith
              rw [abs_of_nonpos hle]; ring
            rw [h1]
            rw [show ρ jy / ‖x jy‖ - 1 = (ρ jy - ‖x jy‖) / ‖x jy‖ by
              rw [sub_div, div_self (ne_of_gt hxjpos)]]
            rw [div_mul_cancel₀ _ hne]
          rw [hval]
          calc ρ jy - ‖x jy‖ ≤ ‖y jy‖ - ‖x jy‖ := by linarith [hjy]
            _ ≤ ‖y jy - x jy‖ := norm_sub_norm_le _ _
            _ = ‖x jy - y jy‖ := norm_sub_rev _ _
            _ = ‖(x - y) jy‖ := by rw [Pi.sub_apply]
            _ ≤ ‖x - y‖ := norm_le_pi_norm _ _
        · rw [Function.update_of_ne hi, sub_self, norm_zero]; positivity
      · apply mem_closure_polydisc_of_forall_norm_le hρ
        intro i
        by_cases hi : i = jy
        · rw [hi, Function.update_self, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos (hρ jy) hxjpos), div_mul_cancel₀ _ (ne_of_gt hxjpos)]
        · rw [Function.update_of_ne hi]; exact hxle i
  obtain ⟨y', hy'C, hdist, hy'cl⟩ := key
  have hy'0 : h y' = 0 := hzero y' hy'C
  have hxy' : x ≠ y' := by
    intro hEq
    obtain ⟨k, hk⟩ := hy'C
    have hk' : ‖x k‖ < ρ k := by
      have h' := (Work.CR.Flat.mem_polydisc.mp hx) k; simpa using h'
    rw [hEq] at hk'
    exact absurd hk (not_le.mpr hk')
  have hpos : 0 < ‖x - y'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy')
  have hstep1 : ENNReal.ofReal (‖h x - h y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal (‖h x - h y'‖ / ‖x - y'‖ ^ α) := by
    rw [hy0, sub_zero, hy'0, sub_zero]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos hpos α) ?_)
    exact Real.rpow_le_rpow (norm_nonneg _) hdist hα0.le
  refine hstep1.trans ?_
  set G : (Fin n → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (‖h x - h z‖ / ‖x - z‖ ^ α) with hGdef
  set Sup : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ⨆ (_ : x ≠ z), G z with hSupdef
  have hGy' : G y' ≤ Sup := by
    have hGcontAt : ContinuousAt G y' := by
      rw [hGdef]
      refine ENNReal.continuous_ofReal.continuousAt.comp ?_
      refine ContinuousAt.div (f := fun z => ‖h x - h z‖) (g := fun z => ‖x - z‖ ^ α) ?_ ?_ ?_
      · exact ((continuous_const.sub (hcont.comp continuous_id)).norm).continuousAt
      · exact ((continuous_const.sub continuous_id).norm.rpow_const
          (fun z => Or.inr hα0.le)).continuousAt
      · show ‖x - y'‖ ^ α ≠ 0
        exact ne_of_gt (Real.rpow_pos_of_pos hpos α)
    have hGP : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ, G z ≤ Sup := by
      intro z hz
      rw [hSupdef]
      by_cases hzx : x = z
      · subst hzx
        have h0 : G x = 0 := by
          rw [hGdef]
          simp [Real.zero_rpow hα0.ne']
        rw [h0]; exact bot_le
      · exact le_iSup₂_of_le z hz (le_iSup_of_le hzx le_rfl)
    haveI hne : (𝓝 y' ⊓ 𝓟 (Work.CR.Flat.polydisc 0 ρ)).NeBot :=
      mem_closure_iff_clusterPt.mp hy'cl
    have htend : Tendsto G (𝓝 y' ⊓ 𝓟 (Work.CR.Flat.polydisc 0 ρ)) (𝓝 (G y')) :=
      hGcontAt.tendsto.mono_left inf_le_left
    have hev : ∀ᶠ z in (𝓝 y' ⊓ 𝓟 (Work.CR.Flat.polydisc 0 ρ)), G z ≤ Sup :=
      Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr hGP)
    have hclosed : IsClosed (Set.Iic Sup) := isClosed_Iic
    have hmem : G y' ∈ Set.Iic Sup := hclosed.mem_of_tendsto htend hev
    exact hmem
  change G y' ≤ ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ⨆ (_ : x ≠ z), G z
  rw [← hSupdef]
  exact hGy'

/-! ## Reduction of the norm over `ℂⁿ` to the norm over the polydisc -/

/-- If a `C^m` function vanishes on the closed complement of the open polydisc, then its
`C^{m,α}` norm over all of `ℂⁿ` is bounded by its `C^{m,α}` norm over the polydisc. -/
theorem holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing {n : ℕ} {α : ℝ}
    (hα0 : 0 < α) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {m : ℕ}
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ m g)
    (hvan : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → g z = 0) :
    Work.CR.Flat.holderNorm m α g Set.univ
      ≤ Work.CR.Flat.holderNorm m α g (Work.CR.Flat.polydisc 0 ρ) := by
  have hPopen : IsOpen (Work.CR.Flat.polydisc 0 ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_le_sum fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcont : Continuous (iteratedFDeriv ℝ i g) :=
    hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast him)
  have hzero : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → iteratedFDeriv ℝ i g z = 0 :=
    fun z hz => iteratedFDeriv_eq_zero_of_vanishing_closedComplement hρ hg hvan i him z hz
  have hxc_of : ∀ x : Fin n → ℂ, x ∉ Work.CR.Flat.polydisc 0 ρ → ∃ j, ρ j ≤ ‖x j‖ := by
    intro x hx
    by_contra h
    push Not at h
    exact hx (by
      rw [Work.CR.Flat.mem_polydisc]
      intro j
      simpa using h j)
  refine add_le_add ?_ ?_
  · rw [Work.CR.Flat.iterDerivNorm, Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x _ => ?_
    by_cases hx : x ∈ Work.CR.Flat.polydisc 0 ρ
    · refine le_iSup₂_of_le x hx ?_
      rw [iteratedFDerivWithin_univ,
        iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hx]
    · rw [iteratedFDerivWithin_univ, hzero x (hxc_of x hx)]
      simp
  · rw [Work.CR.Flat.holderSeminorm, Work.CR.Flat.holderSeminorm]
    simp only [iteratedFDerivWithin_univ]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    by_cases hxP : x ∈ Work.CR.Flat.polydisc 0 ρ
    · by_cases hyP : y ∈ Work.CR.Flat.polydisc 0 ρ
      · rw [← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hxP,
          ← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hyP]
        exact Work.CR.Flat.le_holderSeminorm i α g (Work.CR.Flat.polydisc 0 ρ) hxP hyP hxy
      · refine (ofReal_term_le_iSup_of_vanishing (h := iteratedFDeriv ℝ i g) hα0 hρ hcont
          hzero hxP (hxc_of y hyP)).trans ?_
        refine le_iSup₂_of_le x hxP ?_
        refine iSup₂_le fun z hz => iSup_le fun hxz => ?_
        rw [← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hxP,
          ← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hz]
        exact le_iSup₂_of_le z hz (le_iSup_of_le hxz le_rfl)
    · by_cases hyP : y ∈ Work.CR.Flat.polydisc 0 ρ
      · have h1 : ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖
            = ‖iteratedFDeriv ℝ i g y - iteratedFDeriv ℝ i g x‖ := norm_sub_rev _ _
        have h2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
        rw [h1, h2]
        refine (ofReal_term_le_iSup_of_vanishing (h := iteratedFDeriv ℝ i g) hα0 hρ hcont
            hzero hyP (hxc_of x hxP)).trans ?_
        refine le_iSup₂_of_le y hyP ?_
        refine iSup₂_le fun z hz => iSup_le fun hyz => ?_
        rw [← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hyP,
          ← iteratedFDerivWithin_of_isOpen (s := Work.CR.Flat.polydisc 0 ρ) i hPopen hz]
        exact le_iSup₂_of_le z hz (le_iSup_of_le hyz le_rfl)
      · rw [hzero x (hxc_of x hxP), hzero y (hxc_of y hyP)]
        simp

/-! ## The main theorem -/

/-- **The requested statement.** -/
theorem flatMulNorm {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ w : (Fin n → ℂ) → ℂ), ContDiff ℝ ⊤ φ →
      (∀ z, (∃ j, ρ j ≤ ‖z j‖) → φ z = 0) →
      ContDiffOn ℝ (m : ℕ∞) w (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ →
      ContDiff ℝ m (fun z => φ z * w z) →
      Work.CR.Flat.holderNorm m α (fun z => φ z * w z) Set.univ
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm m α φ Set.univ
          * Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ) := by
  refine ⟨((m : ℝ) + 1) * 2 ^ (m + 1), by positivity, ?_⟩
  intro φ w hφ hφ0 hw hwf hgw
  have hPopen : IsOpen (Work.CR.Flat.polydisc 0 ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hconst : ENNReal.ofReal (((m : ℝ) + 1) * 2 ^ (m + 1))
      = ((m : ℝ≥0∞) + 1) * 2 ^ (m + 1) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    norm_num
  have hred : Work.CR.Flat.holderNorm m α (fun z => φ z * w z) Set.univ
      ≤ Work.CR.Flat.holderNorm m α (fun z => φ z * w z) (Work.CR.Flat.polydisc 0 ρ) :=
    holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing hα0 hρ hgw
      (fun z hz => by rw [hφ0 z hz, zero_mul])
  have hφfin : Work.CR.Flat.holderNorm m α φ (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ :=
    Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded hPopen
      (fun x hx => by
        have hx' : ∀ j, ‖x j‖ < ρ j := fun j => by
          have h' := (Work.CR.Flat.mem_polydisc.mp hx) j; simpa using h'
        rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => (hρ j).le))]
        intro j
        exact le_trans (hx' j).le
          (Finset.single_le_sum (fun i _ => (hρ i).le) (Finset.mem_univ j)))
      hα0 hα1 (hφ.of_le (le_top))
  have hmul := Work.CR.Flat.Holder.holderNorm_mul_le (f := φ) (g := w)
    (Ω := Work.CR.Flat.polydisc 0 ρ) ((hφ.contDiffOn).of_le le_top) hw hPopen.uniqueDiffOn
    hφfin hwf
  calc Work.CR.Flat.holderNorm m α (fun z => φ z * w z) Set.univ
      ≤ Work.CR.Flat.holderNorm m α (fun z => φ z * w z) (Work.CR.Flat.polydisc 0 ρ) := hred
    _ ≤ ((m : ℝ≥0∞) + 1) * 2 ^ (m + 1)
          * Work.CR.Flat.holderNorm m α φ (Work.CR.Flat.polydisc 0 ρ)
          * Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ) := hmul
    _ ≤ ((m : ℝ≥0∞) + 1) * 2 ^ (m + 1)
          * Work.CR.Flat.holderNorm m α φ Set.univ
          * Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ) := by
        gcongr
        exact Work.CR.Flat.holderNorm_mono_set isOpen_univ hPopen (fun x _ => trivial) m α φ
    _ = ENNReal.ofReal (((m : ℝ) + 1) * 2 ^ (m + 1))
          * Work.CR.Flat.holderNorm m α φ Set.univ
          * Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ) := by rw [hconst]

end Work.NN.Core
