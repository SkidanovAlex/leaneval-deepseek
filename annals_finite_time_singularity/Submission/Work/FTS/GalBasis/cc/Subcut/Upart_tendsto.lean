import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta
import Submission.Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_z
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The localisation family `UN N`

`UN N = {p | p.1 ∉ Ioo (plo N) (phiN N) ∨ p.2 ∉ Ioo (qlo N) (qhi N)}` (`Subcut.Defs`) is the
complement of the expanding open plateau, hence an antitone family of measurable sets whose
intersection is null on the domain `Iz × Iθ`.  The two facts proved here are the hypotheses of the
generic dominated-convergence lemma `tendsto_iterated_indicator_of_ae` below. -/

/-- Membership in `UN N` spelled out: the complement of the open plateau. -/
theorem mem_UN_iff (N : ℕ) (z θ : ℝ) :
    (z, θ) ∈ UN N ↔
      ¬ (plo N < z ∧ z < phiN N ∧ qlo N < θ ∧ θ < qhi N) := by
  simp only [UN, Uz, Ut, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro (h | h) ⟨h1, h2, h3, h4⟩
    · exact h ⟨h1, h2⟩
    · exact h ⟨h3, h4⟩
  · intro h
    by_cases hz : plo N < z ∧ z < phiN N
    · exact Or.inr fun hθ => h ⟨hz.1, hz.2, hθ.1, hθ.2⟩
    · exact Or.inl hz

theorem plo_mono (N : ℕ) : plo (N + 1) ≤ plo N := by
  rw [plo, plo]
  gcongr
  linarith

theorem qlo_mono (N : ℕ) : qlo (N + 1) ≤ qlo N := by
  rw [qlo, qlo]
  gcongr
  linarith

theorem phiN_mono (N : ℕ) : phiN N ≤ phiN (N + 1) := by
  rw [phiN, phiN]
  push_cast
  linarith

theorem qhi_mono (N : ℕ) : qhi N ≤ qhi (N + 1) := by
  rw [qhi, qhi]
  gcongr
  linarith

theorem Uz_antitone (N : ℕ) : Uz (N + 1) ⊆ Uz N := by
  intro z hz
  simp only [Uz, Set.mem_setOf_eq] at hz ⊢
  exact fun h => hz (Set.Ioo_subset_Ioo (plo_mono N) (phiN_mono N) h)

theorem Ut_antitone (N : ℕ) : Ut (N + 1) ⊆ Ut N := by
  intro θ hθ
  simp only [Ut, Set.mem_setOf_eq] at hθ ⊢
  exact fun h => hθ (Set.Ioo_subset_Ioo (qlo_mono N) (qhi_mono N) h)

theorem UN_antitone (N : ℕ) : UN (N + 1) ⊆ UN N := by
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl (Uz_antitone N hp)
  · exact Or.inr (Ut_antitone N hp)

/-- The failure set `⋂ N, UN N` is contained in `{z ≤ 0} ∪ {θ ≤ 0} ∪ {π/2 ≤ θ}`: a point of the
open quadrant `(0,∞) × (0,π/2)` lies in the open plateau
`(2/(N+1), N+1) × (2/(N+1), π/2 - 2/(N+1))` for all sufficiently large `N`. -/
theorem inter_UN_subset {p : ℝ × ℝ} (hp : ∀ N : ℕ, p ∈ UN N) :
    p.1 ≤ 0 ∨ p.2 ≤ 0 ∨ Real.pi / 2 ≤ p.2 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hc : 0 < min p.1 p.2 := lt_min h1 h2
  have hd : 0 < Real.pi / 2 - p.2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (max (2 / min p.1 p.2) (2 / (Real.pi / 2 - p.2))) p.1)
  have hn1 : 2 / min p.1 p.2 < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : 2 / (Real.pi / 2 - p.2) < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : p.1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hkey : ∀ {c : ℝ}, 0 < c → 2 / c < (n : ℝ) → 2 / ((n : ℝ) + 1) < c := by
    intro c hc' hlt
    have h2' : 2 / c < (n : ℝ) + 1 := by linarith
    have h1' : 2 < ((n : ℝ) + 1) * c := (div_lt_iff₀ hc').mp h2'
    rwa [div_lt_iff₀' (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
  have e1 : 2 / ((n : ℝ) + 1) < min p.1 p.2 := hkey hc hn1
  have e2 : 2 / ((n : ℝ) + 1) < Real.pi / 2 - p.2 := hkey hd hn2
  have hall : plo n < p.1 ∧ p.1 < phiN n ∧ qlo n < p.2 ∧ p.2 < qhi n :=
    ⟨by simpa only [plo] using lt_of_lt_of_le e1 (min_le_left _ _),
      by simpa only [phiN] using by linarith,
      by simpa only [qlo] using lt_of_lt_of_le e1 (min_le_right _ _),
      by simpa only [qhi] using by linarith⟩
  exact (((mem_UN_iff n p.1 p.2).mp (hp n)) hall).elim

/-- **The a.e. escape from the localisation family**: for almost every point of the domain
`Iz × Iθ`, the expanding plateau eventually contains it, i.e. `p ∉ UN N` for some `N`.  The only
exceptional points are `z = 0` and `θ ∈ {0, π/2}`, which are null for the product measure. -/
theorem ae_eventually_notMem_UN :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      ∃ N : ℕ, p ∉ UN N := by
  set μz : Measure ℝ := volume.restrict Work.Spaces.Iz with hμz
  set μθ : Measure ℝ := volume.restrict Work.Spaces.Iθ with hμθ
  have hz0 : μz (Set.Iic (0 : ℝ)) = 0 := by
    rw [hμz, Measure.restrict_apply measurableSet_Iic]
    have hset : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iz = {0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Work.Spaces.Iz, Set.mem_Ici,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; linarith
      · rintro rfl; exact ⟨le_refl (0 : ℝ), le_refl (0 : ℝ)⟩
    rw [hset]; simp
  have hθ0 : μθ (Set.Iic (0 : ℝ)) = 0 := by
    rw [hμθ, Measure.restrict_apply measurableSet_Iic]
    have hset : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iθ = {0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Work.Spaces.Iθ, Set.mem_Icc,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; linarith
      · rintro rfl
        exact ⟨le_refl (0 : ℝ), ⟨le_refl (0 : ℝ), by linarith [Real.pi_pos]⟩⟩
    rw [hset]; simp
  have hθπ : μθ (Set.Ici (Real.pi / 2)) = 0 := by
    rw [hμθ, Measure.restrict_apply measurableSet_Ici]
    have hset : Set.Ici (Real.pi / 2) ∩ Work.Spaces.Iθ = {Real.pi / 2} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ici, Work.Spaces.Iθ, Set.mem_Icc,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, ⟨h2, h3⟩⟩; linarith
      · rintro rfl
        exact ⟨le_refl _, ⟨by linarith [Real.pi_pos], le_refl _⟩⟩
    rw [hset]; simp
  have hnull1 : (μz.prod μθ) {p : ℝ × ℝ | p.1 ≤ 0} = 0 := by
    have heq : {p : ℝ × ℝ | p.1 ≤ 0} = Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
    rw [heq, Measure.prod_prod, hz0, zero_mul]
  have hnull2 : (μz.prod μθ) {p : ℝ × ℝ | p.2 ≤ 0} = 0 := by
    have heq : {p : ℝ × ℝ | p.2 ≤ 0} = (Set.univ : Set ℝ) ×ˢ Set.Iic (0 : ℝ) := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, true_and]
    rw [heq, Measure.prod_prod, hθ0, mul_zero]
  have hnull3 : (μz.prod μθ) {p : ℝ × ℝ | Real.pi / 2 ≤ p.2} = 0 := by
    have heq : {p : ℝ × ℝ | Real.pi / 2 ≤ p.2} =
        (Set.univ : Set ℝ) ×ˢ Set.Ici (Real.pi / 2) := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici, Set.mem_univ, true_and]
    rw [heq, Measure.prod_prod, hθπ, mul_zero]
  have hsub : {p : ℝ × ℝ | ∀ N : ℕ, p ∈ UN N} ⊆
      {p : ℝ × ℝ | p.1 ≤ 0} ∪
        ({p : ℝ × ℝ | p.2 ≤ 0} ∪ {p : ℝ × ℝ | Real.pi / 2 ≤ p.2}) := by
    intro p hp
    rcases inter_UN_subset hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hnull : (μz.prod μθ) {p : ℝ × ℝ | ∀ N : ℕ, p ∈ UN N} = 0 :=
    measure_mono_null hsub (by
      rw [measure_union_null_iff, measure_union_null_iff]
      exact ⟨hnull1, hnull2, hnull3⟩)
  refine MeasureTheory.ae_iff.mpr ?_
  have hset : {p : ℝ × ℝ | ¬ ∃ N : ℕ, p ∉ UN N} =
      {p : ℝ × ℝ | ∀ N : ℕ, p ∈ UN N} := by
    ext p; simp only [Set.mem_setOf_eq, not_exists, not_not]
  rw [hset]
  exact hnull

/-! ## The generic dominated-convergence lemma -/

/-- **Vanishing of the `ℋ⁴`-mass carried by an antitone family of measurable sets that escapes
every point**: if `U N` is measurable, antitone, and eventually excludes almost every point of the
domain `Iz × Iθ`, then `∫_z ∫_θ HkIntegrand α 4 f z θ · 1_{U N}(z,θ) → 0`.

The proof is a dominated convergence on the product measure
`μ = (volume.restrict Iz).prod (volume.restrict Iθ)`: the integrands are dominated by
`p ↦ HkIntegrand α 4 f p.1 p.2` (integrable by `HkMem`) and converge pointwise a.e. to `0`, and
Fubini (`MeasureTheory.integral_prod`) identifies the product integral with the iterated integral
of the statement.  This is the two-variable version of
`Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta`. -/
theorem tendsto_iterated_indicator_of_ae {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {U : ℕ → Set (ℝ × ℝ)} (hmeas : ∀ N : ℕ, MeasurableSet (U N))
    (hanti : ∀ N : ℕ, U (N + 1) ⊆ U N)
    (hlim : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      ∃ N : ℕ, p ∉ U N) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ * (U N).indicator (fun _ => (1 : ℝ)) (z, θ))
      Filter.atTop (nhds 0) := by
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  set μz : Measure ℝ := volume.restrict Work.Spaces.Iz with hμz
  set μθ : Measure ℝ := volume.restrict Work.Spaces.Iθ with hμθ
  set HH : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α 4 f p.1 p.2 with hHH
  set GG : ℕ → ℝ × ℝ → ℝ :=
    fun N p => HH p * (U N).indicator (fun _ => (1 : ℝ)) p with hGG
  -- Measurability of the integrand on the product measure.
  have hHmeas : AEStronglyMeasurable HH (μz.prod μθ) := by
    rw [hμz, hμθ, hHH]
    exact Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (hsm.continuousOn_HkIntegrand α 4)
  -- Integrability of the angular slices.
  have hHmemθ : ∀ᵐ z ∂μz, Integrable (fun θ => HH (z, θ)) μθ := by
    rw [hμz, hμθ]
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
    have h1 : Integrable (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iθ) := hmem.1 z hz
    simpa only [hHH] using h1
  -- Integrability of the norm of the inner integral.
  have hHmemZ : Integrable (fun z => ∫ θ, ‖HH (z, θ)‖ ∂μθ) μz := by
    rw [hμz, hμθ]
    have h1 : Integrable (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 f z θ
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := hmem.2
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hHH]
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
  -- Integrability of the integrand on the product.
  have hHint : Integrable HH (μz.prod μθ) :=
    (MeasureTheory.integrable_prod_iff hHmeas).mpr ⟨hHmemθ, hHmemZ⟩
  -- Measurability of the truncated integrands.
  have hGGmeas : ∀ N, AEStronglyMeasurable (GG N) (μz.prod μθ) := by
    intro N
    exact hHmeas.mul (Measurable.indicator measurable_const (hmeas N)).aestronglyMeasurable
  -- Domination of the truncated integrands.
  have hGGbound : ∀ N, ∀ᵐ p ∂μz.prod μθ, ‖GG N p‖ ≤ HH p := by
    intro N
    filter_upwards with p
    have hHp : 0 ≤ HH p := by
      simp only [hHH]; exact Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2
    by_cases hp : p ∈ U N
    · have hval : GG N p = HH p := by
        simp only [hGG, Set.indicator_of_mem hp, mul_one]
      rw [hval, Real.norm_of_nonneg hHp]
    · have hval : GG N p = 0 := by
        simp only [hGG, Set.indicator_of_notMem hp, mul_zero]
      rw [hval, norm_zero]
      exact hHp
  have hGGint : ∀ N, Integrable (GG N) (μz.prod μθ) :=
    fun N => Integrable.mono' hHint (hGGmeas N) (hGGbound N)
  -- Pointwise (a.e.) convergence to zero.
  have hGlim : ∀ᵐ p ∂μz.prod μθ, Tendsto (fun N => GG N p) Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hlim] with p hp
    obtain ⟨N₀, hN₀⟩ := hp
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have hnotmem : p ∉ U N := fun hmem' => hN₀ (antitone_nat_of_succ_le hanti hN hmem')
    simp only [hGG, Set.indicator_of_notMem hnotmem, mul_zero]
  -- Dominated convergence on the product measure.
  have hDCT : Tendsto (fun N => ∫ p, GG N p ∂(μz.prod μθ)) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μz.prod μθ) (F := GG) (f := fun _ : ℝ × ℝ => (0 : ℝ))
      HH hGGmeas hHint hGGbound hGlim
    simpa using h
  -- Fubini identifies the product integral with the iterated integral of the statement.
  refine hDCT.congr' (Filter.Eventually.of_forall fun N => ?_)
  rw [MeasureTheory.integral_prod (GG N) (hGGint N), hμz, hμθ]

/-- The localisation set `UN N = {p | p.1 ∉ Ioo (plo N) (phiN N) ∨ p.2 ∉ Ioo (qlo N) (qhi N)}`, where
`plo N = qlo N = 2/(N+1)`, `phiN N = N+1`, `qhi N = π/2 - 2/(N+1)` — the complement of the expanding open
plateau, i.e. the region where the cutoff and all its mixed derivatives can be non-zero — carries vanishing
`ℋ⁴`-mass of `f`.

Route.  `UN N ⊆ (Uz N × univ) ∪ (univ × Ut N)`, so the iterated integral is at most the sum of
`Work.FTS.GalBasis.cc.zShrinkInt α f (Uz N ∩ Iz)` and `Work.FTS.GalBasis.cc.thetaShrinkInt α f (Ut N ∩ Iθ)`.
Both families of sets are measurable, antitone, and eventually exclude every point of `Iz` resp. `Iθ` after
removing the two null points `0` and `π/2` from the angular family (a point of `Iθ` other than the two endpoints
lies in the open plateau for large `N`; the excluded points have measure zero, so `thetaShrinkInt` is unchanged
by removing them, using `MeasureTheory.integral_congr_ae`).  Then apply the two already-proved lemmas
`Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_z` and
`Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta`; pulling the `z`-indicator out of the inner integral
(`MeasureTheory.integral_const_mul` / `integral_mul_const`, or Tonelli) is the only bookkeeping. -/
theorem Upart_tendsto {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ *
          (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
      Filter.atTop (nhds 0) :=
  tendsto_iterated_indicator_of_ae hsm hmem measurableSet_UN UN_antitone
    ae_eventually_notMem_UN

end

end Work.FTS.GalBasis.cc.Subcut
