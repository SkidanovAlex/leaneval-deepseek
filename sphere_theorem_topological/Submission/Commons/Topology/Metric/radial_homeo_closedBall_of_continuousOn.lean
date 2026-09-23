import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber

open Set Metric Filter
open scoped Topology

namespace Commons.Topology.Metric

theorem radial_homeo_closedBall_of_continuousOn
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {h : V → ℝ} {D ε α : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hcont : ContinuousOn h (Metric.closedBall 0 α))
    (h0 : h 0 = D) (hle : ∀ x, h x ≤ D) (hmax : ∀ x, x ≠ 0 → h x < D)
    (hout : ∀ u : V, ‖u‖ = α → h u < D - ε)
    (hmono : ∀ u : V, ‖u‖ = 1 → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ α →
      D - ε ≤ h (t₂ • u) → h (t₁ • u) > h (t₂ • u)) :
    ∃ Φ : {u : V // ‖u‖ ≤ α ∧ D - ε ≤ h u} ≃ₜ Metric.closedBall (0 : V) 1,
      Φ ⁻¹' (Metric.sphere (0 : Metric.closedBall (0 : V) 1) 1)
        = {u : {u : V // ‖u‖ ≤ α ∧ D - ε ≤ h u} | h (u : V) = D - ε} := by
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : CompactSpace ↥(Set.Icc (0 : ℝ) α) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hsphere : ∀ u : V, u ∈ Metric.sphere (0 : V) 1 ↔ ‖u‖ = 1 :=
    fun u => mem_sphere_zero_iff_norm
  -- ## root existence
  have hroot_exists : ∀ u : ↥(Metric.sphere (0 : V) 1),
      ∃! t : ↥(Set.Icc (0 : ℝ) α), h ((t : ℝ) • (u : V)) = D - ε := by
    intro u
    have hu1 : ‖(u : V)‖ = 1 := (hsphere (u : V)).mp u.2
    have hgcont : ContinuousOn (fun t : ℝ => h (t • (u : V))) (Set.Icc 0 α) := by
      refine hcont.comp ?_ ?_
      · exact (continuous_id.smul continuous_const).continuousOn
      · intro t ht
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hu1,
          mul_one]
        exact ht.2
    have hgα : h (α • (u : V)) < D - ε := by
      refine hout _ ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα, hu1, mul_one]
    have hmem : D - ε ∈ Set.Icc (h (α • (u : V))) (h ((0 : ℝ) • (u : V))) := by
      refine ⟨hgα.le, ?_⟩
      rw [zero_smul, h0]; linarith
    obtain ⟨t, ht, htroot⟩ := (intermediate_value_Icc' hα.le hgcont) hmem
    have htroot' : h (t • (u : V)) = D - ε := htroot
    refine ⟨⟨t, ht⟩, htroot', ?_⟩
    intro t' ht'
    apply Subtype.ext
    rcases lt_trichotomy (t' : ℝ) t with hlt | heq | hgt
    · exfalso
      have hh := hmono (u : V) hu1 (t' : ℝ) t t'.2.1 hlt ht.2 (le_of_eq htroot'.symm)
      rw [ht'] at hh
      linarith [htroot']
    · exact heq
    · exfalso
      have hh := hmono (u : V) hu1 t (t' : ℝ) ht.1 hgt t'.2.2 (le_of_eq ht'.symm)
      rw [htroot'] at hh
      linarith [ht']
  -- ## root uniqueness (real version)
  have hroot_unique : ∀ u : ↥(Metric.sphere (0 : V) 1), ∀ t₁ t₂ : ℝ,
      t₁ ∈ Set.Icc 0 α → t₂ ∈ Set.Icc 0 α →
      h (t₁ • (u : V)) = D - ε → h (t₂ • (u : V)) = D - ε → t₁ = t₂ := by
    intro u t₁ t₂ ht₁ ht₂ hr₁ hr₂
    have hu1 : ‖(u : V)‖ = 1 := (hsphere (u : V)).mp u.2
    rcases lt_trichotomy t₁ t₂ with hh | hh | hh
    · exfalso
      have h2 := hmono (u : V) hu1 t₁ t₂ ht₁.1 hh ht₂.2 (le_of_eq hr₂.symm)
      rw [hr₁, hr₂] at h2
      linarith
    · exact hh
    · exfalso
      have h2 := hmono (u : V) hu1 t₂ t₁ ht₂.1 hh ht₁.2 (le_of_eq hr₁.symm)
      rw [hr₁, hr₂] at h2
      linarith
  -- ## closed graph set
  have hclosed : IsClosed {p : ↥(Metric.sphere (0 : V) 1) × ↥(Set.Icc (0 : ℝ) α) |
      h ((p.2 : ℝ) • (p.1 : V)) = D - ε} := by
    let F : ↥(Metric.sphere (0 : V) 1) × ↥(Set.Icc (0 : ℝ) α) → Metric.closedBall (0 : V) α :=
      fun p => ⟨(p.2 : ℝ) • (p.1 : V), by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg p.2.2.1, (hsphere (p.1 : V)).mp p.1.2, mul_one]
        exact p.2.2.2⟩
    have hFcont : Continuous F :=
      Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst))
        (fun p => (F p).2)
    have hOnBall : Continuous (fun x : Metric.closedBall (0 : V) α => h (x : V)) :=
      hcont.domRestrict
    have hcont' : Continuous
        (fun p : ↥(Metric.sphere (0 : V) 1) × ↥(Set.Icc (0 : ℝ) α) =>
          h ((p.2 : ℝ) • (p.1 : V))) := by
      have h := hOnBall.comp hFcont
      convert h using 1
      ext p
      rfl
    exact isClosed_eq hcont' continuous_const
  -- ## continuous radial root
  obtain ⟨f, hfcont, hfmem⟩ :=
    Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber
      {p : ↥(Metric.sphere (0 : V) 1) × ↥(Set.Icc (0 : ℝ) α) |
        h ((p.2 : ℝ) • (p.1 : V)) = D - ε} hclosed hroot_exists
  let rad : ↥(Metric.sphere (0 : V) 1) → ℝ := fun u => (f u : ℝ)
  have hradcont : Continuous rad := continuous_subtype_val.comp hfcont
  have hradmem : ∀ u, rad u ∈ Set.Icc 0 α := fun u => (f u).2
  have hradroot : ∀ u, h (rad u • (u : V)) = D - ε := fun u => hfmem u
  have hradpos : ∀ u, 0 < rad u := by
    intro u
    rcases (hradmem u).1.eq_or_lt with hh | hh
    · exfalso
      have hr := hradroot u
      rw [← hh, zero_smul, h0] at hr
      linarith
    · exact hh
  -- ## the unit direction of a nonzero vector
  have nrm_mem : ∀ x : {x : V // x ≠ 0},
      ‖(x : V)‖⁻¹ • (x : V) ∈ Metric.sphere (0 : V) 1 := by
    intro x
    rw [hsphere, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (x : V))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2)]
  let nrm : {x : V // x ≠ 0} → Metric.sphere (0 : V) 1 :=
    fun x => ⟨‖(x : V)‖⁻¹ • (x : V), nrm_mem x⟩
  have hnrm_cont : Continuous nrm :=
    Continuous.subtype_mk
      (((continuous_norm.comp continuous_subtype_val).inv₀
          (fun x => norm_ne_zero_iff.mpr x.2)).smul
        continuous_subtype_val)
      nrm_mem
  have smul_nrm : ∀ (x : V) (hx : x ≠ 0), ‖x‖ • ((nrm ⟨x, hx⟩) : V) = x := by
    intro x hx
    show ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have nrm_congr : ∀ (a b : V) (ha : a ≠ 0) (hb : b ≠ 0), a = b →
      nrm ⟨a, ha⟩ = nrm ⟨b, hb⟩ := by
    intro a b ha hb hab
    cases hab
    exact Subtype.ext rfl
  have nrm_smul_pos : ∀ (c : ℝ) (hc : 0 < c) (x : V) (hx : x ≠ 0) (hcx : c • x ≠ 0),
      nrm ⟨c • x, hcx⟩ = nrm ⟨x, hx⟩ := by
    intro c hc x hx hcx
    apply Subtype.ext
    show ‖c • x‖⁻¹ • (c • x) = ‖x‖⁻¹ • x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    have hscal : (c * ‖x‖)⁻¹ * c = ‖x‖⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
    rw [hscal]
  -- ## the "outward" map `psi` (closedBall -> region)
  have psiN_cont : Continuous
      (fun x : {y : V // y ≠ 0} => rad (nrm x) • (x : V)) :=
    (hradcont.comp hnrm_cont).smul continuous_subtype_val
  let psi : V → V := fun y => if hy : y = 0 then 0 else rad (nrm ⟨y, hy⟩) • y
  have psi_of_ne : ∀ (y : V) (hy : y ≠ 0), psi y = rad (nrm ⟨y, hy⟩) • y := by
    intro y hy
    show (if hy' : y = 0 then (0 : V) else rad (nrm ⟨y, hy'⟩) • y)
      = rad (nrm ⟨y, hy⟩) • y
    rw [dif_neg hy]
  have psi_zero : psi 0 = 0 := by
    show (if hy' : (0 : V) = 0 then (0 : V) else rad (nrm ⟨0, hy'⟩) • 0) = 0
    rw [dif_pos rfl]
  have psi_bound : ∀ y : V, ‖psi y‖ ≤ α * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · subst hy; rw [psi_zero, norm_zero, mul_zero]
    · rw [psi_of_ne y hy, norm_smul, Real.norm_eq_abs]
      have hmem := hradmem (nrm ⟨y, hy⟩)
      have habs : |rad (nrm ⟨y, hy⟩)| ≤ α := abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
      exact mul_le_mul_of_nonneg_right habs (norm_nonneg y)
  have psi_contOn : ContinuousOn psi {y : V | y ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine psiN_cont.congr (fun x => ?_)
    show rad (nrm x) • (x : V) = psi (x : V)
    rw [psi_of_ne (x : V) x.2]
  have psi_contAt_zero : ContinuousAt psi 0 := by
    change Tendsto psi (𝓝 0) (𝓝 (psi 0))
    rw [psi_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) psi_bound ?_
    have hcont : Continuous (fun y : V => α * ‖y‖) := continuous_const.mul continuous_norm
    simpa using hcont.tendsto (0 : V)
  have psi_cont : Continuous psi := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y = 0
    · subst hy; exact psi_contAt_zero
    · exact psi_contOn.continuousAt (isOpen_ne.mem_nhds hy)
  -- ## the "inward" map `phi` (region -> closedBall)
  let phiScalar : V → ℝ := fun x => if hx : x = 0 then 0 else (rad (nrm ⟨x, hx⟩))⁻¹
  let phi : V → V := fun x => phiScalar x • x
  have phi_of_ne : ∀ (x : V) (hx : x ≠ 0), phi x = (rad (nrm ⟨x, hx⟩))⁻¹ • x := by
    intro x hx
    show (if hx' : x = 0 then (0 : ℝ) else (rad (nrm ⟨x, hx'⟩))⁻¹) • x
      = (rad (nrm ⟨x, hx⟩))⁻¹ • x
    rw [dif_neg hx]
  have phi_zero : phi 0 = 0 := by
    show (if hx' : (0 : V) = 0 then (0 : ℝ) else (rad (nrm ⟨0, hx'⟩))⁻¹) • (0 : V) = 0
    rw [dif_pos rfl, zero_smul]
  have psi_phi : ∀ x : V, psi (phi x) = x := by
    intro x
    by_cases hx : x = 0
    · subst hx; rw [phi_zero, psi_zero]
    · have hphi_ne : phi x ≠ 0 := by
        rw [phi_of_ne x hx]
        exact smul_ne_zero (inv_ne_zero (ne_of_gt (hradpos (nrm ⟨x, hx⟩)))) hx
      have h1 : psi (phi x) = rad (nrm ⟨phi x, hphi_ne⟩) • (phi x) :=
        psi_of_ne (phi x) hphi_ne
      have h3 : nrm ⟨phi x, hphi_ne⟩ = nrm ⟨x, hx⟩ := by
        have hab : phi x = (rad (nrm ⟨x, hx⟩))⁻¹ • x := phi_of_ne x hx
        have hcxn : (rad (nrm ⟨x, hx⟩))⁻¹ • x ≠ 0 :=
          smul_ne_zero (inv_ne_zero (ne_of_gt (hradpos _))) hx
        rw [nrm_congr (phi x) ((rad (nrm ⟨x, hx⟩))⁻¹ • x) hphi_ne hcxn hab]
        exact nrm_smul_pos (rad (nrm ⟨x, hx⟩))⁻¹ (inv_pos.mpr (hradpos _)) x hx hcxn
      have h2 : phi x = (rad (nrm ⟨x, hx⟩))⁻¹ • x := phi_of_ne x hx
      rw [h1, h3, h2, smul_smul, mul_inv_cancel₀ (ne_of_gt (hradpos _)), one_smul]
  have phi_psi : ∀ y : V, phi (psi y) = y := by
    intro y
    by_cases hy : y = 0
    · subst hy; rw [psi_zero, phi_zero]
    · have hpsi_ne : psi y ≠ 0 := by
        rw [psi_of_ne y hy]
        exact smul_ne_zero (ne_of_gt (hradpos (nrm ⟨y, hy⟩))) hy
      have h1 : phi (psi y) = (rad (nrm ⟨psi y, hpsi_ne⟩))⁻¹ • (psi y) :=
        phi_of_ne (psi y) hpsi_ne
      have h3 : nrm ⟨psi y, hpsi_ne⟩ = nrm ⟨y, hy⟩ := by
        have hab : psi y = rad (nrm ⟨y, hy⟩) • y := psi_of_ne y hy
        have hcxn : rad (nrm ⟨y, hy⟩) • y ≠ 0 := smul_ne_zero (ne_of_gt (hradpos _)) hy
        rw [nrm_congr (psi y) (rad (nrm ⟨y, hy⟩) • y) hpsi_ne hcxn hab]
        exact nrm_smul_pos (rad (nrm ⟨y, hy⟩)) (hradpos _) y hy hcxn
      have h2 : psi y = rad (nrm ⟨y, hy⟩) • y := psi_of_ne y hy
      rw [h1, h3, h2, smul_smul, inv_mul_cancel₀ (ne_of_gt (hradpos _)), one_smul]
  -- ## `psi` lands in the region
  have psi_mem : ∀ y : Metric.closedBall (0 : V) 1,
      ‖psi (y : V)‖ ≤ α ∧ D - ε ≤ h (psi (y : V)) := by
    intro y
    have hy1 : ‖(y : V)‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
    by_cases hy : (y : V) = 0
    · rw [hy, psi_zero]
      refine ⟨by rw [norm_zero]; exact hα.le, ?_⟩
      rw [h0]; linarith
    · have hρpos := hradpos (nrm ⟨(y : V), hy⟩)
      have hρmem := hradmem (nrm ⟨(y : V), hy⟩)
      have hu1 : ‖((nrm ⟨(y : V), hy⟩) : V)‖ = 1 := (hsphere _).mp (nrm ⟨(y : V), hy⟩).2
      have hy_smul : ‖(y : V)‖ • ((nrm ⟨(y : V), hy⟩) : V) = (y : V) := smul_nrm (y : V) hy
      refine ⟨?_, ?_⟩
      · rw [psi_of_ne (y : V) hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hρpos)]
        calc rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖
            ≤ rad (nrm ⟨(y : V), hy⟩) * 1 :=
              mul_le_mul_of_nonneg_left hy1 (le_of_lt hρpos)
          _ ≤ α := by rw [mul_one]; exact hρmem.2
      · have hrepr : psi (y : V)
            = (rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖) • ((nrm ⟨(y : V), hy⟩) : V) := by
          calc psi (y : V) = rad (nrm ⟨(y : V), hy⟩) • (y : V) := psi_of_ne (y : V) hy
            _ = rad (nrm ⟨(y : V), hy⟩) • (‖(y : V)‖ • ((nrm ⟨(y : V), hy⟩) : V)) :=
                (congrArg (fun t => rad (nrm ⟨(y : V), hy⟩) • t) hy_smul).symm
            _ = (rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖) • ((nrm ⟨(y : V), hy⟩) : V) :=
                (smul_smul _ _ _)
        rw [hrepr]
        have hle : rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖ ≤ rad (nrm ⟨(y : V), hy⟩) := by
          calc rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖
              ≤ rad (nrm ⟨(y : V), hy⟩) * 1 :=
                mul_le_mul_of_nonneg_left hy1 (le_of_lt hρpos)
            _ = rad (nrm ⟨(y : V), hy⟩) := mul_one _
        rcases eq_or_lt_of_le hle with heq | hlt
        · rw [heq, hradroot (nrm ⟨(y : V), hy⟩)]
        · have hh := hmono ((nrm ⟨(y : V), hy⟩) : V) hu1
              (rad (nrm ⟨(y : V), hy⟩) * ‖(y : V)‖) (rad (nrm ⟨(y : V), hy⟩))
              (mul_nonneg (le_of_lt hρpos) (norm_nonneg _)) hlt hρmem.2
              (le_of_eq (hradroot (nrm ⟨(y : V), hy⟩)).symm)
          rw [hradroot (nrm ⟨(y : V), hy⟩)] at hh
          linarith
  -- ## `phi` lands in the closed unit ball
  have phi_mem : ∀ x : {x : V // ‖x‖ ≤ α ∧ D - ε ≤ h x}, ‖phi (x : V)‖ ≤ 1 := by
    intro x
    have hxα : ‖(x : V)‖ ≤ α := x.2.1
    have hxh : D - ε ≤ h (x : V) := x.2.2
    by_cases hx : (x : V) = 0
    · rw [hx, phi_zero, norm_zero]; norm_num
    · rw [phi_of_ne (x : V) hx, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hradpos _)))]
      have hle : ‖(x : V)‖ ≤ rad (nrm ⟨(x : V), hx⟩) := by
        by_contra hcon
        rw [not_le] at hcon
        have hu1 : ‖((nrm ⟨(x : V), hx⟩) : V)‖ = 1 := (hsphere _).mp (nrm ⟨(x : V), hx⟩).2
        have hx_smul : ‖(x : V)‖ • ((nrm ⟨(x : V), hx⟩) : V) = (x : V) := smul_nrm (x : V) hx
        have h2 : D - ε ≤ h (‖(x : V)‖ • ((nrm ⟨(x : V), hx⟩) : V)) := by
          rw [hx_smul]; exact hxh
        have hh := hmono ((nrm ⟨(x : V), hx⟩) : V) hu1 (rad (nrm ⟨(x : V), hx⟩)) ‖(x : V)‖
            (le_of_lt (hradpos _)) hcon hxα h2
        rw [hradroot (nrm ⟨(x : V), hx⟩)] at hh
        linarith
      calc (rad (nrm ⟨(x : V), hx⟩))⁻¹ * ‖(x : V)‖
          ≤ (rad (nrm ⟨(x : V), hx⟩))⁻¹ * rad (nrm ⟨(x : V), hx⟩) :=
            mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (le_of_lt (hradpos _)))
        _ = 1 := inv_mul_cancel₀ (ne_of_gt (hradpos _))
  -- ## key characterisation of the boundary
  have hkey : ∀ x : {x : V // ‖x‖ ≤ α ∧ D - ε ≤ h x},
      ‖phi (x : V)‖ = 1 ↔ h (x : V) = D - ε := by
    intro x
    by_cases hx : (x : V) = 0
    · rw [hx, phi_zero, norm_zero]
      constructor
      · intro hcon; norm_num at hcon
      · intro hcon; rw [h0] at hcon; linarith
    · rw [phi_of_ne (x : V) hx, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hradpos _)))]
      constructor
      · intro hcon
        have hρ : rad (nrm ⟨(x : V), hx⟩) ≠ 0 := ne_of_gt (hradpos _)
        have hx_eq : ‖(x : V)‖ = rad (nrm ⟨(x : V), hx⟩) := by
          have h2 := congrArg (fun t => rad (nrm ⟨(x : V), hx⟩) * t) hcon
          rw [mul_one] at h2
          rw [← mul_assoc, mul_inv_cancel₀ hρ, one_mul] at h2
          exact h2
        have hx_smul : ‖(x : V)‖ • ((nrm ⟨(x : V), hx⟩) : V) = (x : V) := smul_nrm (x : V) hx
        calc h (x : V) = h (‖(x : V)‖ • ((nrm ⟨(x : V), hx⟩) : V)) := by rw [hx_smul]
          _ = h (rad (nrm ⟨(x : V), hx⟩) • ((nrm ⟨(x : V), hx⟩) : V)) := by rw [hx_eq]
          _ = D - ε := hradroot (nrm ⟨(x : V), hx⟩)
      · intro hcon
        have hx_eq : ‖(x : V)‖ = rad (nrm ⟨(x : V), hx⟩) :=
          hroot_unique (nrm ⟨(x : V), hx⟩) ‖(x : V)‖ (rad (nrm ⟨(x : V), hx⟩))
            ⟨norm_nonneg _, x.2.1⟩ (hradmem _)
            (by rw [smul_nrm (x : V) hx]; exact hcon) (hradroot _)
        rw [hx_eq, inv_mul_cancel₀ (ne_of_gt (hradpos _))]
  -- ## the equivalence and the homeomorphism
  let eEq : Metric.closedBall (0 : V) 1 ≃ {x : V // ‖x‖ ≤ α ∧ D - ε ≤ h x} :=
    { toFun := fun y => ⟨psi (y : V), psi_mem y⟩
      invFun := fun x => ⟨phi (x : V), mem_closedBall_zero_iff.mpr (phi_mem x)⟩
      left_inv := fun y => Subtype.ext (phi_psi (y : V))
      right_inv := fun x => Subtype.ext (psi_phi (x : V)) }
  have heEq_cont : Continuous eEq :=
    Continuous.subtype_mk (psi_cont.comp continuous_subtype_val) psi_mem
  let hom : Metric.closedBall (0 : V) 1 ≃ₜ {x : V // ‖x‖ ≤ α ∧ D - ε ≤ h x} :=
    Continuous.homeoOfEquivCompactToT2 (f := eEq) heEq_cont
  refine ⟨hom.symm, ?_⟩
  ext x
  rw [Set.mem_preimage, Set.mem_ofPred_eq]
  have hhom : hom ⟨phi (x : V), mem_closedBall_zero_iff.mpr (phi_mem x)⟩ = x := by
    apply Subtype.ext
    show psi (phi (x : V)) = (x : V)
    exact psi_phi (x : V)
  have hsymm : hom.symm x = ⟨phi (x : V), mem_closedBall_zero_iff.mpr (phi_mem x)⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact hhom.symm
  rw [hsymm]
  show (⟨phi (x : V), mem_closedBall_zero_iff.mpr (phi_mem x)⟩ : Metric.closedBall (0 : V) 1)
      ∈ Metric.sphere (0 : Metric.closedBall (0 : V) 1) 1 ↔ h (x : V) = D - ε
  rw [mem_sphere, Subtype.dist_eq]
  rw [show (↑(0 : Metric.closedBall (0 : V) 1) : V) = 0 from rfl, dist_zero_right]
  exact hkey x

end Commons.Topology.Metric