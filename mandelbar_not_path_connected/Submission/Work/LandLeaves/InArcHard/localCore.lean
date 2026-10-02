import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.boundedOrbit_of_ball
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.rayPt_iterate_angDouble
import Submission.Work.ELTop.All
import Submission.Work.TopJordan.Main
import Submission.Work.SeedSimple2.COP.local_angle
import Submission.Work.SeedSimple2.COP.punctured_ball
import Submission.Work.LandLeaves.InArcHard.extAngleLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.LandLeaves.InArcHard.Core

noncomputable section

/-! ## 1. The second return map `τ = (T_c)^{2k}` and its local structure at a repelling point -/

/-- The holomorphic second return map `τ = (T_c)^{2k}`. -/
def tauC (c : ℂ) (k : ℕ) : ℂ → ℂ := (Tantibar c)^[2 * k]

@[simp] theorem tauC_apply (c : ℂ) (k : ℕ) (z : ℂ) :
    tauC c k z = (Tantibar c)^[2 * k] z := rfl

/-- `τ` is a polynomial, hence differentiable. -/
theorem differentiable_tauC (c : ℂ) (k : ℕ) : Differentiable ℂ (tauC c k) := by
  have h2 : (Work.Landing.Tsq c)^[k] = tauC c k := by
    rw [Work.LandLeaves.Tsq_eq_iterate_two, ← Function.iterate_mul]
    rfl
  rw [← h2]
  have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  exact h1.iterate k

/-- `τ` fixes the repelling periodic point. -/
theorem tauC_fixed {c : ℂ} {k : ℕ} {y : ℂ} (hrep : Work.Landing.IsRepelling c k y) :
    tauC c k y = y := by
  obtain ⟨hper, -⟩ := hrep
  simp only [tauC_apply]
  rw [show 2 * k = k * 2 from by ring, Function.iterate_mul]
  exact (show Function.IsFixedPt ((Tantibar c)^[k]) y from hper.2).iterate 2

/-- `τ` is injective on a small ball around the repelling point. -/
theorem exists_tauC_injOn {c : ℂ} {k : ℕ} {y : ℂ} (hrep : Work.Landing.IsRepelling c k y) :
    ∃ r > 0, Set.InjOn (tauC c k) (Metric.ball y r) := by
  obtain ⟨r, r', κ, g, hr, hrr', hκ0, hκ1, hgy, hcontr, hτg, hgτ⟩ :=
    exists_local_repelling_branch hrep
  have hr'pos : 0 < r' := lt_trans hr hrr'
  have hcont : Continuous (tauC c k) := (differentiable_tauC c k).continuous
  have hmem : tauC c k ⁻¹' Metric.ball y r' ∈ 𝓝 y := by
    have h := hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (tauC c k y) hr'pos)
    rwa [tauC_fixed hrep] at h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
  have key : ∀ z ∈ Metric.ball y (min r δ), g (tauC c k z) = z := by
    intro z hz
    have hzr : z ∈ Metric.ball y r := Metric.ball_subset_ball (min_le_left r δ) hz
    have hzd : z ∈ Metric.ball y δ := Metric.ball_subset_ball (min_le_right r δ) hz
    have hzr' : tauC c k z ∈ Metric.ball y r' := hδ hzd
    refine hgτ z ?_ ?_
    · rw [Metric.mem_ball, dist_eq_norm] at hzr; exact le_of_lt hzr
    · rw [Metric.mem_ball, dist_eq_norm] at hzr'; exact le_of_lt hzr'
  refine ⟨min r δ, lt_min hr hδpos, fun z1 hz1 z2 hz2 heq => ?_⟩
  rw [← key z1 hz1, ← key z2 hz2, heq]

/-- **The Böttcher coordinate of the dynamical plane is continuous off the filled Julia set.** -/
theorem continuousOn_dynPhi_gen {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) :
    ContinuousOn (Work.EL.dynPhi c φ) (Work.EL.K c)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Set.domRestrict (Work.EL.K c)ᶜ (Work.EL.dynPhi c φ)
      = fun z => ((hN.e z : Work.Top.exteriorDisc) : ℂ) := by
    funext z
    exact hN.he z
  rw [h]
  exact continuous_subtype_val.comp hN.e.continuous

/-- **Local angle continuity at an interior point of a ray.**  At a point `rayPt hN e t₀` with
`0 < e < 1` and `t₀ > 1` the external angle is continuous, with the explicit tolerance `η`. -/
theorem extAngle_close_at_gen {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {e η : ℝ} (he0 : 0 < e) (he1 : e < 1) (hη : 0 < η) {t₀ : ℝ} (ht₀ : 1 < t₀) :
    ∃ δ > 0, ∀ z : ℂ, ‖z - Work.EL.rayPt hN e t₀‖ < δ →
      z ∉ Work.EL.K c ∧
      |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - e| < η := by
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    Work.Top.extAngle_close_of_Phi_close (Mb := Work.EL.K c)
      (Φ := Work.EL.dynPhi c φ) hN he0 he1 ht₀ hη
  have hpK : Work.EL.rayPt hN e t₀ ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN ht₀
  have hpPhi : Work.EL.dynPhi c φ (Work.EL.rayPt hN e t₀) = Work.Top.NakaneData.rayPoint e t₀ :=
    Work.Top.NakaneData.Phi_rayPt hN ht₀
  have hpnorm : ‖Work.Top.NakaneData.rayPoint e t₀‖ = t₀ := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
  have hcont : ContinuousAt (Work.EL.dynPhi c φ) (Work.EL.rayPt hN e t₀) :=
    (continuousOn_dynPhi_gen hN).continuousAt (hN.isClosed_mb.isOpen_compl.mem_nhds hpK)
  have hεpos : 0 < min δ₀ t₀ := lt_min hδ₀pos (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min δ₀ t₀) hεpos
  refine ⟨δ, hδpos, fun z hz => ?_⟩
  have hd : dist (Work.EL.dynPhi c φ z) (Work.EL.dynPhi c φ (Work.EL.rayPt hN e t₀))
      < min δ₀ t₀ := hδ (by rwa [dist_eq_norm])
  rw [dist_eq_norm, hpPhi] at hd
  have hzK : z ∉ Work.EL.K c := by
    intro hzK
    have h0 : Work.EL.dynPhi c φ z = 0 := hN.Phi_eq_zero_of_mem z hzK
    rw [h0, zero_sub, norm_neg, hpnorm] at hd
    exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (lt_irrefl t₀)
  refine ⟨hzK, hδ₀ z hzK (lt_of_lt_of_le hd (min_le_left _ _))⟩

/-- **`τ` maps rays to rays**: the image of the ray of angle `θ` is contained in the ray of angle
`(angDouble)^[2k] θ = Int.fract (4^k θ)`. -/
theorem tauC_mem_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {k : ℕ} {θ : ℝ} {z : ℂ}
    (hz : z ∈ Work.EL.paramRay hN θ) :
    tauC c k z ∈ Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] θ) := by
  have hz' : z ∈ Work.Top.NakaneData.paramRay hN θ := hz
  rw [Work.Top.NakaneData.paramRay_eq_range] at hz'
  obtain ⟨⟨t, ht⟩, htz⟩ := hz'
  simp only [tauC_apply]
  rw [← htz, ← rayPt_iterate_angDouble hN hφ ht]
  exact Work.EL.rayPt_mem_paramRay hN (one_lt_pow₀ ht (by positivity))


/-! ## 2. The angular four-case table for the `N = 4^k`-fold covering

At a point of the ray `R(P.a)` (resp. `R(P.b)`) of a co-landing pair `P`, a nearby point has an
external angle `φ = e + σ` with `e` the angle of that ray.  The image angle is
`Int.fract (N φ)`, and the sign of `σ` is preserved; comparing the arc membership of `φ` in
`(P.a, P.b)` with that of `Int.fract (N φ)` in `(P'.a, P'.b)` is the four-case table below.
-/

theorem fract_fract_sub' {y a : ℝ} : Int.fract (Int.fract y - a) = Int.fract (y - a) := by
  have h : Int.fract y - a = (y - a) - (⌊y⌋ : ℤ) := by
    have hh := Int.fract_add_floor y
    linarith
  rw [h, Int.fract_sub_intCast]

theorem fract_eq_add_one' {x : ℝ} (h1 : -1 < x) (h2 : x < 0) : Int.fract x = x + 1 := by
  have hx : x = (x + 1) - (1 : ℤ) := by push_cast; ring
  conv_lhs => rw [hx]
  rw [Int.fract_sub_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

/-- **The angular core, first ray.**  If `φ = a + σ` with `σ ≠ 0`, `|σ| < η` and `η` small
compared with the two arc lengths, then the arc membership of `φ` in `(a,b)` is equivalent to
that of `Int.fract (N φ)` in `(a', b')` (where `a' ≡ N a`, `b' ≡ N b`), and neither angle is
congruent to an endpoint. -/
theorem angle_correspondence_a {a b a' b' φ σ η N : ℝ}
    (hN1 : 1 < N) (hφ : φ = a + σ)
    (ha' : ∃ k : ℤ, a' = N * a + k) (hb' : ∃ k : ℤ, b' = N * b + k)
    (hσ0 : σ ≠ 0) (hσ1 : |σ| < η)
    (hμ0 : 0 < Work.EL.arcLen a b) (hμ1 : Work.EL.arcLen a b < 1)
    (hμ'0 : 0 < Work.EL.arcLen a' b') (hμ'1 : Work.EL.arcLen a' b' < 1)
    (hημ : η ≤ Work.EL.arcLen a b / 2) (hη1μ : η ≤ (1 - Work.EL.arcLen a b) / 2)
    (hημ' : N * η ≤ Work.EL.arcLen a' b' / 2)
    (hη1μ' : N * η ≤ (1 - Work.EL.arcLen a' b') / 2) :
    (Work.EL.InArc φ a b ↔ Work.EL.InArc (Int.fract (N * φ)) a' b') ∧
    (∀ k : ℤ, φ ≠ a + k) ∧ (∀ k : ℤ, φ ≠ b + k) ∧
    (∀ k : ℤ, Int.fract (N * φ) ≠ a' + k) ∧
    (∀ k : ℤ, Int.fract (N * φ) ≠ b' + k) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN1
  have hσgt : -η < σ := (abs_lt.mp hσ1).1
  have hσlt : σ < η := (abs_lt.mp hσ1).2
  rcases lt_or_gt_of_ne hσ0 with hσneg | hσpos
  · -- `σ < 0`: both arcs are `false`
    have hσneg1 : -1 < σ := by linarith [hσgt, hημ, hμ1]
    have hNneg : -1 < N * σ := by
      have h1 : -(N * η) < N * σ := by
        have h := mul_lt_mul_of_pos_left hσgt hN0
        simpa [mul_neg] using h
      linarith [h1, hημ', hμ'1]
    have hρ : Int.fract (φ - a) = σ + 1 := by
      rw [hφ, show a + σ - a = σ by ring]
      exact fract_eq_add_one' hσneg1 hσneg
    have hρ' : Int.fract (N * φ - a') = N * σ + 1 := by
      obtain ⟨k, hk⟩ := ha'
      rw [hφ, hk, show N * (a + σ) - (N * a + (k : ℝ)) = N * σ - (k : ℝ) by ring,
        Int.fract_sub_intCast]
      exact fract_eq_add_one' hNneg (mul_neg_of_pos_of_neg hN0 hσneg)
    have hρbig : Work.EL.arcLen a b < σ + 1 := by linarith [hσgt, hη1μ, hμ1]
    have hρ'big : Work.EL.arcLen a' b' < N * σ + 1 := by
      have h1 : -(N * η) < N * σ := by
        have h := mul_lt_mul_of_pos_left hσgt hN0
        simpa [mul_neg] using h
      linarith [h1, hη1μ', hμ'1]
    have hn1 : ¬ Work.EL.InArc φ a b := by
      rw [Work.EL.InArc, hρ]
      intro h
      linarith [h.2, hρbig]
    have hn2 : ¬ Work.EL.InArc (Int.fract (N * φ)) a' b' := by
      rw [Work.EL.InArc, fract_fract_sub', hρ']
      intro h
      linarith [h.2, hρ'big]
    refine ⟨⟨fun h => absurd h hn1, fun h => absurd h hn2⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hσneg1] : (0 : ℝ) < σ + 1))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (φ - a) = Work.EL.arcLen a b := by
        rw [hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
        rfl
      rw [hρ] at h0
      exact absurd h0 (ne_of_gt hρbig)
    · intro k hk
      apply (ne_of_gt (by linarith : (0 : ℝ) < N * σ + 1))
      rw [← hρ', ← fract_fract_sub', hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (N * φ - a') = Work.EL.arcLen a' b' := by
        rw [← fract_fract_sub', hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
          Int.fract_add_intCast]
        rfl
      rw [hρ'] at h0
      exact absurd h0 (ne_of_gt hρ'big)
  · -- `σ > 0`: both arcs are `true`
    have hσ1lt : σ < 1 := by linarith [hσlt, hημ, hμ1]
    have hNlt : N * σ < 1 := by
      have h1 : N * σ < N * η := mul_lt_mul_of_pos_left hσlt hN0
      linarith [h1, hη1μ', hμ'1]
    have hρ : Int.fract (φ - a) = σ := by
      rw [hφ, show a + σ - a = σ by ring,
        Int.fract_eq_self.mpr ⟨le_of_lt hσpos, hσ1lt⟩]
    have hρ' : Int.fract (N * φ - a') = N * σ := by
      obtain ⟨k, hk⟩ := ha'
      rw [hφ, hk, show N * (a + σ) - (N * a + (k : ℝ)) = N * σ - (k : ℝ) by ring,
        Int.fract_sub_intCast, Int.fract_eq_self.mpr ⟨le_of_lt (mul_pos hN0 hσpos), hNlt⟩]
    have hρsmall : σ < Work.EL.arcLen a b := by linarith [hσlt, hημ, hμ1]
    have hρ'small : N * σ < Work.EL.arcLen a' b' := by
      have h1 : N * σ < N * η := mul_lt_mul_of_pos_left hσlt hN0
      linarith [h1, hημ', hμ'1]
    have h1 : Work.EL.InArc φ a b := by
      refine ⟨?_, ?_⟩
      · rw [hρ]; exact hσpos
      · rw [hρ]; exact hρsmall
    have h2 : Work.EL.InArc (Int.fract (N * φ)) a' b' := by
      refine ⟨?_, ?_⟩
      · rw [fract_fract_sub', hρ']; exact mul_pos hN0 hσpos
      · rw [fract_fract_sub', hρ']; exact hρ'small
    refine ⟨⟨fun _ => h2, fun _ => h1⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply hσ0
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (φ - a) = Work.EL.arcLen a b := by
        rw [hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
        rfl
      rw [hρ] at h0
      exact absurd h0 (ne_of_lt hρsmall)
    · intro k hk
      apply (ne_of_gt (mul_pos hN0 hσpos))
      rw [← hρ', ← fract_fract_sub', hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (N * φ - a') = Work.EL.arcLen a' b' := by
        rw [← fract_fract_sub', hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
          Int.fract_add_intCast]
        rfl
      rw [hρ'] at h0
      exact absurd h0 (ne_of_lt hρ'small)

/-- **The angular core, second ray.**  The same statement as `angle_correspondence_a` for
`φ = b + σ`: now `σ < 0` gives the far arc and `σ > 0` the near arc. -/
theorem angle_correspondence_b {a b a' b' φ σ η N : ℝ}
    (hN1 : 1 < N) (hφ : φ = b + σ)
    (ha' : ∃ k : ℤ, a' = N * a + k) (hb' : ∃ k : ℤ, b' = N * b + k)
    (hσ0 : σ ≠ 0) (hσ1 : |σ| < η)
    (hμ0 : 0 < Work.EL.arcLen a b) (hμ1 : Work.EL.arcLen a b < 1)
    (hμ'0 : 0 < Work.EL.arcLen a' b') (hμ'1 : Work.EL.arcLen a' b' < 1)
    (hημ : η ≤ Work.EL.arcLen a b / 2) (hη1μ : η ≤ (1 - Work.EL.arcLen a b) / 2)
    (hημ' : N * η ≤ Work.EL.arcLen a' b' / 2)
    (hη1μ' : N * η ≤ (1 - Work.EL.arcLen a' b') / 2) :
    (Work.EL.InArc φ a b ↔ Work.EL.InArc (Int.fract (N * φ)) a' b') ∧
    (∀ k : ℤ, φ ≠ a + k) ∧ (∀ k : ℤ, φ ≠ b + k) ∧
    (∀ k : ℤ, Int.fract (N * φ) ≠ a' + k) ∧
    (∀ k : ℤ, Int.fract (N * φ) ≠ b' + k) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN1
  have hσgt : -η < σ := (abs_lt.mp hσ1).1
  have hσlt : σ < η := (abs_lt.mp hσ1).2
  have hfl : b - a = Work.EL.arcLen a b + ((⌊b - a⌋ : ℤ) : ℝ) := by
    have h := Int.floor_add_fract (b - a)
    rw [Work.EL.arcLen]
    linarith
  have hρ : Int.fract (φ - a) = Work.EL.arcLen a b + σ := by
    conv_lhs => rw [hφ]
    rw [show b + σ - a = (b - a) + σ by ring, hfl]
    rw [show Work.EL.arcLen a b + ((⌊b - a⌋ : ℤ) : ℝ) + σ
        = (Work.EL.arcLen a b + σ) + ((⌊b - a⌋ : ℤ) : ℝ) by ring, Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ0, hσgt, hημ]
      · linarith [hμ0, h]
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ1, h]
      · linarith [hμ1, hσlt, hη1μ]
  have hρ' : Int.fract (N * φ - a') = Work.EL.arcLen a' b' + N * σ := by
    obtain ⟨k₁, hk₁⟩ := ha'
    obtain ⟨k₂, hk₂⟩ := hb'
    have h4 : N * (b - a)
        = Work.EL.arcLen a' b' + ((⌊b' - a'⌋ : ℝ) - ((k₂ - k₁ : ℤ) : ℝ)) := by
      have h := Int.floor_add_fract (b' - a')
      have hf : Int.fract (b' - a') = Work.EL.arcLen a' b' := rfl
      have hb : b' - a' = N * (b - a) + ((k₂ - k₁ : ℤ) : ℝ) := by
        rw [hk₁, hk₂]; push_cast; ring
      linarith
    conv_lhs => rw [hφ, hk₁]
    rw [show N * (b + σ) - (N * a + (k₁ : ℝ))
          = N * (b - a) + N * σ - (k₁ : ℝ) by ring, h4]
    rw [show Work.EL.arcLen a' b' + ((⌊b' - a'⌋ : ℝ) - ((k₂ - k₁ : ℤ) : ℝ)) + N * σ
          - (k₁ : ℝ)
          = (Work.EL.arcLen a' b' + N * σ)
            + ((⌊b' - a'⌋ - (k₂ - k₁) - k₁ : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · have h1 : -(N * η) < N * σ := by
          have h' := mul_lt_mul_of_pos_left hσgt hN0
          simpa [mul_neg] using h'
        linarith [h1, hημ', hμ'0]
      · have h'' : 0 < N * σ := mul_pos hN0 h
        linarith [hμ'0, h'']
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · have h'' : N * σ < 0 := mul_neg_of_pos_of_neg hN0 h
        linarith [hμ'1, h'']
      · have h1 : N * σ < N * η := mul_lt_mul_of_pos_left hσlt hN0
        linarith [h1, hη1μ', hμ'1]
  rcases lt_or_gt_of_ne hσ0 with hσneg | hσpos
  · -- `σ < 0`: both arcs are `true`
    have h1 : Work.EL.InArc φ a b := by
      refine ⟨?_, ?_⟩
      · rw [hρ]; linarith [hσgt, hημ, hμ0]
      · rw [hρ]; linarith [hσneg]
    have h2 : Work.EL.InArc (Int.fract (N * φ)) a' b' := by
      refine ⟨?_, ?_⟩
      · rw [fract_fract_sub', hρ']
        have h' : -(N * η) < N * σ := by
          have h'' := mul_lt_mul_of_pos_left hσgt hN0
          simpa [mul_neg] using h''
        linarith [h', hημ', hμ'0]
      · rw [fract_fract_sub', hρ']
        have h'' : N * σ < 0 := mul_neg_of_pos_of_neg hN0 hσneg
        linarith
    refine ⟨⟨fun _ => h2, fun _ => h1⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hμ0, hσgt, hημ] :
        (0 : ℝ) < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      apply (ne_of_lt (by linarith [hσneg] :
        (Work.EL.arcLen a b + σ) < Work.EL.arcLen a b))
      rw [← hρ, hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
      rfl
    · intro k hk
      apply (ne_of_gt (by
        have h' : -(N * η) < N * σ := by
          have h'' := mul_lt_mul_of_pos_left hσgt hN0
          simpa [mul_neg] using h''
        linarith [h', hημ', hμ'0] :
        (0 : ℝ) < Work.EL.arcLen a' b' + N * σ))
      rw [← hρ', ← fract_fract_sub', hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      apply (ne_of_lt (by
        have h'' : N * σ < 0 := mul_neg_of_pos_of_neg hN0 hσneg
        linarith :
        (Work.EL.arcLen a' b' + N * σ) < Work.EL.arcLen a' b'))
      rw [← hρ', ← fract_fract_sub', hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
        Int.fract_add_intCast]
      rfl
  · -- `σ > 0`: both arcs are `false`
    have hn1 : ¬ Work.EL.InArc φ a b := by
      rw [Work.EL.InArc, hρ]
      intro h
      linarith [h.2]
    have hn2 : ¬ Work.EL.InArc (Int.fract (N * φ)) a' b' := by
      rw [Work.EL.InArc, fract_fract_sub', hρ']
      intro h
      have h'' : 0 < N * σ := mul_pos hN0 hσpos
      linarith [h.2, h'']
    refine ⟨⟨fun h => absurd h hn1, fun h => absurd h hn2⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hμ0, hσpos] : (0 : ℝ) < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      apply (ne_of_gt (by linarith [hσpos] :
        Work.EL.arcLen a b < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
      rfl
    · intro k hk
      apply (ne_of_gt (by
        have h'' : 0 < N * σ := mul_pos hN0 hσpos
        linarith [hμ'0, h''] :
        (0 : ℝ) < Work.EL.arcLen a' b' + N * σ))
      rw [← hρ', ← fract_fract_sub', hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      apply (ne_of_gt (by
        have h'' : 0 < N * σ := mul_pos hN0 hσpos
        linarith :
        Work.EL.arcLen a' b' < Work.EL.arcLen a' b' + N * σ))
      rw [← hρ', ← fract_fract_sub', hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
        Int.fract_add_intCast]
      rfl


/-! ## 3. The clopen ("side transfer") argument near the landing point -/

/-- The tail of a landing ray lies in any prescribed ball around the landing point. -/
theorem exists_level_ball_of_landsN' {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {a : ℝ} {y : ℂ} (ha : Work.EL.LandsN hN a y) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ > 1, ∀ s ∈ Set.Ioo 1 s₀, Work.EL.rayPt hN a s ∈ Metric.ball y ε := by
  have hmem : {s : ℝ | Work.EL.rayPt hN a s ∈ Metric.ball y ε} ∈ 𝓝[>] (1 : ℝ) :=
    ha (Metric.ball_mem_nhds y hε)
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hmem
  exact ⟨s₀, hs₀, fun s hs => hsub hs⟩

/-- Near the repelling point `y`, a point different from `y` is not mapped to `y` by `τ`. -/
theorem tauC_ne_y_near {c : ℂ} {k : ℕ} {y : ℂ} (hrep : Work.Landing.IsRepelling c k y) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → z ≠ y → tauC c k z ≠ y := by
  obtain ⟨r, hr, hinj⟩ := exists_tauC_injOn hrep
  refine ⟨r, hr, fun z hz hzy hτ => hzy ?_⟩
  refine hinj hz (Metric.mem_ball.mpr (by simpa using hr)) ?_
  rw [hτ, tauC_fixed hrep]

/-- **The side transfer near the landing point.**  With `P = (u,v,y)` and `P'` the pair of the
`4^k`-images, the far side of `P` is carried to the far side of `P'` on a punctured neighbourhood
of `y`: the local side correspondence at the ray points (the angular four-case table) together
with the local "no sibling ray" fact propagates along the preconnected punctured ball by a clopen
argument. -/
theorem cop_sides_gen {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hN : Work.EL.DynB c φ) (hk : 0 < k) (hrep : Work.Landing.IsRepelling c k y)
    (P P' : Work.EL.CoPair hN) (hPy : P.y = y) (hP'y : P'.y = y)
    (hS : Work.EL.PairSides hN P) (hS' : Work.EL.PairSides hN P')
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0)
    (hPTa : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      tauC c k z ∈ Work.EL.paramRay hN P'.a → z ∈ Work.EL.paramRay hN P.a)
    (hPTb : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      tauC c k z ∈ Work.EL.paramRay hN P'.b → z ∈ Work.EL.paramRay hN P.b)
    (hLA : ∀ p : ℂ, p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b → ∃ δ > 0,
      ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
        tauC c k z ∉ Work.EL.pairCurve P' ∧
        (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P')) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → z ∉ Work.EL.pairCurve P →
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := by
  obtain ⟨ε₀, hε₀pos, hFne⟩ := tauC_ne_y_near (c := c) (k := k) (y := y) hrep
  obtain ⟨εa, hεapos, hptia⟩ := hPTa
  obtain ⟨εb, hεbpos, hptib⟩ := hPTb
  set ε : ℝ := min ε₀ (min εa εb) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₀pos (lt_min hεapos hεbpos)
  have hεε₀ : ε ≤ ε₀ := by rw [hεdef]; exact min_le_left _ _
  have hεεa : ε ≤ εa := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεεb : ε ≤ εb := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hball₀ : Metric.ball y ε ⊆ Metric.ball y ε₀ := Metric.ball_subset_ball hεε₀
  have hballa : Metric.ball y ε ⊆ Metric.ball y εa := Metric.ball_subset_ball hεεa
  have hballb : Metric.ball y ε ⊆ Metric.ball y εb := Metric.ball_subset_ball hεεb
  have hyK : y ∈ Work.EL.K c := hPy ▸ Work.ELTop.landsN_mem_K hN P.lands_a
  have hyX : y ∈ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl hPy.symm)
  -- ## Step 1: `τ` creates no point of the curve of `P'`
  have step1 : ∀ z : ℂ, z ∈ Metric.ball y ε → z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' := by
    intro z hz hzX hFY
    have hzne : z ≠ y := fun h1 => hzX (h1.symm ▸ hyX)
    have hFne : tauC c k z ≠ y := hFne z (hball₀ hz) hzne
    rw [Work.EL.mem_pairCurve_iff] at hFY
    rcases hFY with h | h | h
    · exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (hptia z (hballa hz) h))
    · exact hFne (h.trans hP'y)
    · exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inr (Or.inr (hptib z (hballb hz) h)))
  -- ## Step 2: the good and the bad set
  set Good₀ : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'))} with hGood₀
  set Bad : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'))} with hBad
  set Ω : Set ℂ := Metric.ball y ε \ {y} with hΩ
  -- ## Step 3: the thickening of the curve of `P` given by the local angle lemma
  set TT : Set ℂ := {p : ℂ | p ∈ Metric.ball y ε \ {y} ∧
      (p ∈ Work.EL.paramRay hN P.a ∨ p ∈ Work.EL.paramRay hN P.b)} with hTT
  have hδexists : ∀ p : TT, ∃ δ > 0, ∀ z : ℂ, z ∈ Metric.ball p.1 δ →
      z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') :=
    fun p => hLA p.1 p.2.2
  set δ : TT → ℝ := fun p => Classical.choose (hδexists p) with hδdef
  have hδpos : ∀ p : TT, 0 < δ p := fun p => by
    rw [hδdef]; exact (Classical.choose_spec (hδexists p)).1
  have hδspec : ∀ p : TT, ∀ z : ℂ, z ∈ Metric.ball p.1 (δ p) →
      z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := fun p => by
    rw [hδdef]; exact (Classical.choose_spec (hδexists p)).2
  set Good : Set ℂ := Good₀ ∪ ⋃ p : TT, Metric.ball p.1 (δ p) with hGood
  -- ## Openness
  have hcont_τ : Continuous (tauC c k) := (differentiable_tauC c k).continuous
  have hGood₀open : IsOpen Good₀ := by
    rw [hGood₀]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        tauC c k z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_far.inter (hS'.isOpen_far.preimage hcont_τ)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        tauC c k z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_near.inter (hS'.isOpen_near.preimage hcont_τ)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl.inter (h1.union h2)
  have hBadopen : IsOpen Bad := by
    rw [hBad]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        tauC c k z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_far.inter (hS'.isOpen_near.preimage hcont_τ)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        tauC c k z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_near.inter (hS'.isOpen_far.preimage hcont_τ)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl.inter (h1.union h2)
  have hGoodopen : IsOpen Good := by
    rw [hGood]
    exact hGood₀open.union (isOpen_iUnion fun p : TT => Metric.isOpen_ball)
  -- ## `Bad` and `Good` are disjoint
  have hdisj : Disjoint Bad Good := by
    rw [hGood, Set.disjoint_left]
    intro z hzB hzG
    rcases hzG with hzG₀ | hzU
    · rw [hBad] at hzB
      rw [hGood₀] at hzG₀
      obtain ⟨-, hBd⟩ := hzB
      obtain ⟨-, hGd⟩ := hzG₀
      rcases hBd with ⟨bP, bP'⟩ | ⟨bN, bN'⟩
      · rcases hGd with ⟨gP, gP'⟩ | ⟨gN, gN'⟩
        · exact hS'.disjoint.notMem_of_mem_left gP' bP'
        · exact hS.disjoint.notMem_of_mem_left bP gN
      · rcases hGd with ⟨gP, gP'⟩ | ⟨gN, gN'⟩
        · exact hS.disjoint.notMem_of_mem_left gP bN
        · exact hS'.disjoint.notMem_of_mem_left bN' gN'
    · rw [Set.mem_iUnion] at hzU
      obtain ⟨p, hzp⟩ := hzU
      rw [hBad] at hzB
      obtain ⟨hzX, hBd⟩ := hzB
      obtain ⟨hFzX, heq⟩ := hδspec p z hzp hzX
      rcases hBd with ⟨bP, bP'⟩ | ⟨bN, bN'⟩
      · exact hS'.disjoint.notMem_of_mem_left (heq.mp bP) bP'
      · exact hS.disjoint.notMem_of_mem_left (heq.mpr bN') bN
  -- ## Step 4: `Ω` is covered
  have hcover : Ω ⊆ Bad ∪ Good := by
    rw [hΩ, hGood]
    intro z hz
    obtain ⟨hzball, hzsing⟩ := hz
    by_cases hzX : z ∈ Work.EL.pairCurve P
    · right; right
      rw [Set.mem_iUnion]
      have hzTT : z ∈ TT := by
        rw [hTT]
        refine ⟨⟨hzball, hzsing⟩, ?_⟩
        rw [Work.EL.mem_pairCurve_iff] at hzX
        rcases hzX with h | h | h
        · exact Or.inl h
        · exact absurd (h.trans hPy) (fun h1 => hzsing (by simpa using h1))
        · exact Or.inr h
      exact ⟨⟨z, hzTT⟩, Metric.mem_ball_self (hδpos ⟨z, hzTT⟩)⟩
    · have hFzX : tauC c k z ∉ Work.EL.pairCurve P' := step1 z hzball hzX
      have hzAB : z ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
        rw [hS.union_eq]; exact hzX
      have hFAB : tauC c k z ∈ Work.EL.pairSide P' ∪ Work.EL.pairSideNear P' := by
        rw [hS'.union_eq]; exact hFzX
      rcases hzAB with hfar | hnear
      · rcases hFAB with hfar' | hnear'
        · right; left; rw [hGood₀]; exact ⟨hzX, Or.inl ⟨hfar, hfar'⟩⟩
        · left; rw [hBad]; exact ⟨hzX, Or.inl ⟨hfar, hnear'⟩⟩
      · rcases hFAB with hfar' | hnear'
        · left; rw [hBad]; exact ⟨hzX, Or.inr ⟨hnear, hfar'⟩⟩
        · right; left; rw [hGood₀]; exact ⟨hzX, Or.inr ⟨hnear, hnear'⟩⟩
  -- ## Step 5: the clopen argument
  have hpre : IsPreconnected Ω := by
    rw [hΩ]
    exact Work.SeedSimple2.COP.isPreconnected_ball_diff_singleton y ε
  have hor : Ω ⊆ Bad ∨ Ω ⊆ Good := hpre.subset_or_subset hBadopen hGoodopen hdisj hcover
  have hnotBad : ¬ Ω ⊆ Bad := by
    intro hsub
    obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN' hN P.lands_a hεpos
    set s : ℝ := (1 + s₀) / 2 with hsdef
    have hs1 : 1 < s := by rw [hsdef]; linarith
    have hss : s < s₀ := by rw [hsdef]; linarith
    have hzball : Work.EL.rayPt hN P.a s ∈ Metric.ball y ε := by
      rw [← hPy]; exact hnear s ⟨hs1, hss⟩
    have hzK : Work.EL.rayPt hN P.a s ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN hs1
    have hzne : Work.EL.rayPt hN P.a s ≠ y := fun h1 => hzK (h1.symm ▸ hyK)
    have hzΩ : Work.EL.rayPt hN P.a s ∈ Ω := by
      rw [hΩ]
      exact ⟨hzball, by simpa using hzne⟩
    have hzBad : Work.EL.rayPt hN P.a s ∈ Bad := hsub hzΩ
    rw [hBad] at hzBad
    exact hzBad.1 (by
      rw [Work.EL.mem_pairCurve_iff]
      exact Or.inl (Work.EL.rayPt_mem_paramRay hN hs1))
  have hΩG : Ω ⊆ Good := hor.resolve_left hnotBad
  -- ## The conclusion
  refine ⟨ε, hεpos, ?_⟩
  intro z hzball hzX
  have hzne : z ≠ y := fun h1 => hzX (h1.symm ▸ hyX)
  have hzΩ : z ∈ Ω := by
    rw [hΩ]
    exact ⟨hzball, by simpa using hzne⟩
  have hzGood : z ∈ Good := hΩG hzΩ
  rw [hGood] at hzGood
  rcases hzGood with hzG₀ | hzU
  · rw [hGood₀] at hzG₀
    obtain ⟨-, hGd⟩ := hzG₀
    constructor
    · intro hzA
      rcases hGd with ⟨-, gP'⟩ | ⟨gN, -⟩
      · exact gP'
      · exact absurd gN (hS.disjoint.notMem_of_mem_left hzA)
    · intro hzA'
      rcases hGd with ⟨gP, -⟩ | ⟨-, gN'⟩
      · exact gP
      · exact absurd gN' (hS'.disjoint.notMem_of_mem_left hzA')
  · rw [Set.mem_iUnion] at hzU
    obtain ⟨p, hzp⟩ := hzU
    exact (hδspec p z hzp hzX).2


/-! ## 4. The main chain: cyclic-order preservation by the `2k`-fold angle map -/

/-! ### 4.1 Elementary invariance helpers -/

theorem fract_ne_zero_of_pos_lt_one {x : ℝ} (h1 : 0 < x) (h2 : x < 1) : Int.fract x ≠ 0 := by
  rw [Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩]
  exact ne_of_gt h1

/-- `InArc` is invariant under integral shifts of both endpoints. -/
theorem InArc_add_int_iff {x a b : ℝ} (m n : ℤ) :
    Work.EL.InArc x (a + m) (b + n) ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show x - (a + (m : ℝ)) = (x - a) - (m : ℝ) by ring, Int.fract_sub_intCast,
      show b + (n : ℝ) - (a + (m : ℝ)) = (b - a) + ((n - m : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]

/-- `fract` is invariant under subtracting `fract`s. -/
theorem fract_fract_sub_eq (u v : ℝ) :
    Int.fract (Int.fract v - Int.fract u) = Int.fract (v - u) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊u⌋ - ⌊v⌋, ?_⟩
  have h1 := Int.fract_add_floor v
  have h2 := Int.fract_add_floor u
  push_cast
  linarith

/-- The arc length only sees the fractional parts. -/
theorem arcLen_fract_fract (u v : ℝ) :
    Work.EL.arcLen (Int.fract u) (Int.fract v) = Work.EL.arcLen u v := by
  unfold Work.EL.arcLen
  rw [show Int.fract v - Int.fract u = (v - u) + ((⌊u⌋ - ⌊v⌋ : ℤ) : ℝ) by
    have h1 := Int.fract_add_floor v
    have h2 := Int.fract_add_floor u
    push_cast
    linarith,
    Int.fract_add_intCast]

/-- A parameter ray whose angle lies in the far arc of a co-landing pair is contained in the
far side of that pair, in the `RawPair` form. -/
theorem paramRay_subset_rawSide_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {a b w : ℝ} {y : ℂ} (ha : Work.EL.LandsN hN a y) (hb : Work.EL.LandsN hN b y)
    (hab : a < b) (hb1 : b < a + 1) (h : Work.EL.InArc w a b) :
    Work.EL.paramRay hN w ⊆ Work.EL.RawPair.side hN ⟨a, b, y⟩ := by
  have h1 := Work.ELTop.paramRay_subset_pairSide_of_InArc hN
    (Work.LandLeaves.mkPair hN ha hb) hab hb1 h
  rwa [show Work.EL.pairSide (Work.LandLeaves.mkPair hN ha hb)
      = Work.EL.RawPair.side hN ⟨a, b, y⟩ from rfl] at h1

/-- `ccBet` is invariant under a cyclic rotation of the triple. -/
theorem ccBet_rot_aux {A B X : ℝ} (h : ccBet A B X) : ccBet B X A := by
  obtain ⟨h1, h2⟩ := h
  have hA : Int.fract (B - A) ≠ 0 := ne_of_gt (lt_trans h1 h2)
  have hAB : Int.fract (A - B) = 1 - Int.fract (B - A) := by
    have h' : A - B = -(B - A) := by ring
    rw [h', Int.fract_neg hA]
  have hXB : Int.fract (X - B) = Int.fract (X - A) - Int.fract (B - A) + 1 := by
    have hsub : X - B = (X - A) - (B - A) := by ring
    rw [hsub]
    have hw : X - A = Int.fract (X - A) + (⌊X - A⌋ : ℝ) := by
      have := Int.fract_add_floor (X - A); linarith
    have hv : B - A = Int.fract (B - A) + (⌊B - A⌋ : ℝ) := by
      have := Int.fract_add_floor (B - A); linarith
    have hkey : (X - A) - (B - A) =
        (Int.fract (X - A) - Int.fract (B - A) + 1)
          + ((⌊X - A⌋ - ⌊B - A⌋ - 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have h1 : 0 ≤ Int.fract (X - A) - Int.fract (B - A) + 1 := by
      linarith [Int.fract_nonneg (X - A), Int.fract_lt_one (B - A)]
    have h2' : Int.fract (X - A) - Int.fract (B - A) + 1 < 1 := by linarith
    rw [hkey, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h1, h2'⟩]
  rw [ccBet, hAB, hXB]
  constructor <;> linarith [Int.fract_lt_one (B - A)]

/-- `ccBet` is invariant under an integral shift of the middle argument. -/
theorem ccBet_add_int_mid_aux (a b x : ℝ) (m : ℤ) : ccBet a (b + m) x ↔ ccBet a b x := by
  unfold ccBet
  rw [show b + (m : ℝ) - a = (b - a) + (m : ℝ) by ring, Int.fract_add_intCast]

/-- **The `2k`-fold angle map is injective modulo `1` on the type**, in the concrete form used
below. -/
theorem fract_sub_angDouble_ne_zero {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {u w : ℝ} (hu : Work.Landing.rayAccum c φ u = {y})
    (hw : Work.Landing.rayAccum c φ w = {y}) (hne : Int.fract (w - u) ≠ 0) :
    Int.fract ((Work.Landing.angDouble)^[2 * k] w - (Work.Landing.angDouble)^[2 * k] u) ≠ 0 := by
  intro h0
  have hk : 0 < k := hrep.1.1
  obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
  have e1 := angDouble_iterate_two_mul hk w
  have e2 := angDouble_iterate_two_mul hk u
  rw [e1, e2] at hm
  have f1 : (4 : ℝ) ^ k * w - Int.fract ((4 : ℝ) ^ k * w) = (⌊(4 : ℝ) ^ k * w⌋ : ℝ) :=
    Int.self_sub_fract _
  have f2 : (4 : ℝ) ^ k * u - Int.fract ((4 : ℝ) ^ k * u) = (⌊(4 : ℝ) ^ k * u⌋ : ℝ) :=
    Int.self_sub_fract _
  have hkey : ∃ m' : ℤ, (4 : ℝ) ^ k * w = (4 : ℝ) ^ k * u + (m' : ℝ) := by
    refine ⟨m + ⌊(4 : ℝ) ^ k * w⌋ - ⌊(4 : ℝ) ^ k * u⌋, ?_⟩
    push_cast
    linarith
  obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hw hu hkey
  refine hne ?_
  rw [hmm, show u + (mm : ℝ) - u = (mm : ℝ) by ring, Int.fract_intCast]

/-! ### 4.2 The local angle transfer and the local preimage identity at `y` -/

/-- The `2k`-th iterate of the angle doubling map is multiplication by `4^k` modulo `1`. -/
theorem angDouble_it2m_add_int_aux (θ : ℝ) (k : ℕ) :
    ∃ m : ℤ, (Work.Landing.angDouble)^[2 * k] θ = (4 : ℝ) ^ k * θ + m := by
  rw [Work.LandLeaves.angDouble_eq_T]
  obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int θ (2 * k)
  refine ⟨m, ?_⟩
  rw [hm, show ((-2 : ℝ) ^ (2 * k)) = (4 : ℝ) ^ k by rw [pow_mul]; norm_num]

/-- The parameter ray depends on the angle only modulo `1`. -/
theorem paramRay_fract_gen_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (Int.fract θ) = Work.EL.paramRay hN θ := by
  have h := Work.ELTop.paramRay_add_int_aux hN (Int.fract θ) ⌊θ⌋
  rw [Int.fract_add_floor] at h
  exact h.symm

/-- `tauC c k` maps the ray of angle `θ` into the ray of angle `Int.fract (4^k θ)`. -/
theorem tauC_mem_paramRay_fract_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {k : ℕ} {θ : ℝ} {z : ℂ}
    (hz : z ∈ Work.EL.paramRay hN θ) :
    tauC c k z ∈ Work.EL.paramRay hN (Int.fract ((4 : ℝ) ^ k * θ)) := by
  have h1 := tauC_mem_paramRay (k := k) hN hφ hz
  obtain ⟨m, hm⟩ := angDouble_it2m_add_int_aux θ k
  rw [hm] at h1
  rw [Work.ELTop.paramRay_add_int_aux hN ((4 : ℝ) ^ k * θ) m] at h1
  rw [← paramRay_fract_gen_aux hN ((4 : ℝ) ^ k * θ)] at h1
  exact h1

/-- **The local angle transfer**: at a point `p` of one of the rays of a co-landing pair `P`, the
second return map `τ = (T_c)^{2k}` carries the far side of `P` to the far side of the
`4^k`-image pair `P'` on a neighbourhood of `p`, and creates no point of the curve of `P'`. -/
theorem local_angle_gen_aux {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hk : 0 < k)
    (P P' : Work.EL.CoPair hN) (hS : Work.EL.PairSides hN P)
    (hS' : Work.EL.PairSides hN P')
    (hPa : P.a ∈ Set.Ioo (0 : ℝ) 1) (hPb : P.b ∈ Set.Ioo (0 : ℝ) 1) (hab : P.a ≠ P.b)
    (ha' : ∃ m : ℤ, P'.a = (4 : ℝ) ^ k * P.a + m)
    (hb' : ∃ m : ℤ, P'.b = (4 : ℝ) ^ k * P.b + m)
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0)
    {p : ℂ} (hp : p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b) :
    ∃ δ > 0, ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := by
  have hμ0 : 0 < Work.EL.arcLen P.a P.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _)
      (Ne.symm (Work.SeedSimple2.COP.arcLen_ne_zero_of_mem_Ioo hPa hPb hab))
  have hμ1 : Work.EL.arcLen P.a P.b < 1 := Work.EL.arcLen_lt_one _ _
  have hμ'0 : 0 < Work.EL.arcLen P'.a P'.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _) (Ne.symm hnd')
  have hμ'1 : Work.EL.arcLen P'.a P'.b < 1 := Work.EL.arcLen_lt_one _ _
  set N : ℝ := (4 : ℝ) ^ k with hNdef
  have hN1 : 1 < N := by
    rw [hNdef]
    exact one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.mp hk)
  have hNpos : 0 < N := lt_trans zero_lt_one hN1
  have ha'' : ∃ m : ℤ, P'.a = N * P.a + m := by rw [hNdef]; exact ha'
  have hb'' : ∃ m : ℤ, P'.b = N * P.b + m := by rw [hNdef]; exact hb'
  set M : ℝ := min (min (Work.EL.arcLen P.a P.b) (1 - Work.EL.arcLen P.a P.b))
      (min (Work.EL.arcLen P'.a P'.b / N) ((1 - Work.EL.arcLen P'.a P'.b) / N)) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min hμ0 (by linarith))
      (lt_min (div_pos hμ'0 hNpos) (div_pos (by linarith) hNpos))
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hM1 : M ≤ Work.EL.arcLen P.a P.b := by
    rw [hMdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hM2 : M ≤ 1 - Work.EL.arcLen P.a P.b := by
    rw [hMdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hM3 : M ≤ Work.EL.arcLen P'.a P'.b / N := by
    rw [hMdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hM4 : M ≤ (1 - Work.EL.arcLen P'.a P'.b) / N := by
    rw [hMdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hημ : η ≤ Work.EL.arcLen P.a P.b / 2 := by rw [hηdef]; linarith
  have hη1μ : η ≤ (1 - Work.EL.arcLen P.a P.b) / 2 := by rw [hηdef]; linarith
  have hNμ' : N * (Work.EL.arcLen P'.a P'.b / N) = Work.EL.arcLen P'.a P'.b := by
    field_simp
  have hN1μ' : N * ((1 - Work.EL.arcLen P'.a P'.b) / N)
      = 1 - Work.EL.arcLen P'.a P'.b := by field_simp
  have hημ' : N * η ≤ Work.EL.arcLen P'.a P'.b / 2 := by
    have h := mul_le_mul_of_nonneg_left hM3 (le_of_lt hNpos)
    rw [hNμ'] at h
    have hrw : N * η = N * M / 2 := by rw [hηdef]; ring
    rw [hrw]; linarith
  have hη1μ' : N * η ≤ (1 - Work.EL.arcLen P'.a P'.b) / 2 := by
    have h := mul_le_mul_of_nonneg_left hM4 (le_of_lt hNpos)
    rw [hN1μ'] at h
    have hrw : N * η = N * M / 2 := by rw [hηdef]; ring
    rw [hrw]; linarith
  have hab_int : ∀ j : ℤ, P.b ≠ P.a + j := by
    intro j hj
    exact hμ0.ne' (by
      rw [Work.EL.arcLen, hj, show P.a + (j : ℝ) - P.a = (j : ℝ) by ring, Int.fract_intCast])
  have hab'_int : ∀ j : ℤ, P'.b ≠ P'.a + j := by
    intro j hj
    exact hnd' (by
      rw [Work.EL.arcLen, hj, show P'.a + (j : ℝ) - P'.a = (j : ℝ) by ring, Int.fract_intCast])
  rcases hp with hp | hp
  · have hp' : p ∈ Work.Top.NakaneData.paramRay hN P.a := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt hN P.a t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ := extAngle_close_at_gen hN hPa.1 hPa.2 hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt hN P.a t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, hzang⟩ := hδ z hzn
    set φa : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z with hφadef
    set σ : ℝ := φa - P.a with hσdef
    have hσabs : |σ| < η := by rw [hσdef, hφadef]; simpa using hzang
    have hφray : z ∈ Work.EL.paramRay hN φa := by
      rw [hφadef]; exact Work.Top.mem_paramRay_extAngle hN hzK
    have hφeq : φa = P.a + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφPa : φa = P.a := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inl (hφPa ▸ hφray))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_a (N := N) hN1 hφeq ha'' hb'' hσne hσabs
        hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    have hFmem : tauC c k z ∈ Work.EL.paramRay hN (Int.fract (N * φa)) := by
      have h := tauC_mem_paramRay_fract_aux (k := k) hN hφ hφray
      rw [← hNdef] at h
      exact h
    have hKy : P'.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P'.lands_a
    have hFzK : tauC c k z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN _ hFmem
    refine ⟨?_, ?_⟩
    · rw [Work.EL.mem_pairCurve_iff]
      simp only [not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFa j hj
      · intro heqy
        exact hFzK (by rw [heqy]; exact hKy)
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFb j hj
    · exact (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P hS hab_int hna hnb hφray).trans
        (heq.trans
          (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P' hS' hab'_int hFa hFb hFmem).symm)
  · have hp' : p ∈ Work.Top.NakaneData.paramRay hN P.b := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt hN P.b t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ := extAngle_close_at_gen hN hPb.1 hPb.2 hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt hN P.b t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, hzang⟩ := hδ z hzn
    set φa : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z with hφadef
    set σ : ℝ := φa - P.b with hσdef
    have hσabs : |σ| < η := by rw [hσdef, hφadef]; simpa using hzang
    have hφray : z ∈ Work.EL.paramRay hN φa := by
      rw [hφadef]; exact Work.Top.mem_paramRay_extAngle hN hzK
    have hφeq : φa = P.b + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφPb : φa = P.b := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inr (hφPb ▸ hφray)))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_b (N := N) hN1 hφeq ha'' hb'' hσne hσabs
        hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    have hFmem : tauC c k z ∈ Work.EL.paramRay hN (Int.fract (N * φa)) := by
      have h := tauC_mem_paramRay_fract_aux (k := k) hN hφ hφray
      rw [← hNdef] at h
      exact h
    have hKy : P'.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P'.lands_a
    have hFzK : tauC c k z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN _ hFmem
    refine ⟨?_, ?_⟩
    · rw [Work.EL.mem_pairCurve_iff]
      simp only [not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFa j hj
      · intro heqy
        exact hFzK (by rw [heqy]; exact hKy)
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFb j hj
    · exact (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P hS hab_int hna hnb hφray).trans
        (heq.trans
          (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P' hS' hab'_int hFa hFb hFmem).symm)

/-- **The local preimage identity at `y`**: near `y`, if `τ z` lies on the ray of an angle
congruent to `4^k u` modulo `1` and `R(u)` lands at `y`, then `z` itself lies on `R(u)`. -/
theorem tauC_preimage_tail_aux {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) {u : ℝ}
    (hu : Work.Landing.rayAccum c φ u = {y}) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → ∀ θ' : ℝ,
      (∃ m : ℤ, θ' = (4 : ℝ) ^ k * u + m) →
      tauC c k z ∈ Work.EL.paramRay hN θ' → z ∈ Work.EL.paramRay hN u := by
  obtain ⟨ε₀, hε₀, hinj⟩ := exists_tauC_injOn hrep
  have hL : Work.EL.LandsN hN u y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ u y).mpr (Work.LandLeaves.landsAt_of_rayAccum hφ hu)
  obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN' hN hL hε₀
  have hyK : y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hL
  have hpot_y : Work.EL.pot hN y = 0 := Work.EL.pot_of_mem hN hyK
  have hτy : tauC c k y = y := tauC_fixed hrep
  have hApos : 0 < (4 : ℝ) ^ k * Real.log s₀ :=
    mul_pos (by positivity) (Real.log_pos hs₀)
  have hcont : Continuous (fun z : ℂ => Work.EL.pot hN (tauC c k z)) :=
    hN.continuous_potential.comp (differentiable_tauC c k).continuous
  have hmem : {z : ℂ | Work.EL.pot hN (tauC c k z) < (4 : ℝ) ^ k * Real.log s₀} ∈ 𝓝 y :=
    (isOpen_lt hcont continuous_const).mem_nhds (by
      show Work.EL.pot hN (tauC c k y) < (4 : ℝ) ^ k * Real.log s₀
      rw [hτy, hpot_y]; exact hApos)
  obtain ⟨ε₁, hε₁, hbound⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro z hz θ' hθ' hτz
  have hz₀ : z ∈ Metric.ball y ε₀ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hz₁ : z ∈ Metric.ball y ε₁ := Metric.ball_subset_ball (min_le_right _ _) hz
  obtain ⟨m, hm⟩ := hθ'
  have hτz_top : tauC c k z ∈ Work.Top.NakaneData.paramRay hN θ' := hτz
  rw [Work.Top.NakaneData.paramRay_eq_range] at hτz_top
  obtain ⟨⟨t, ht⟩, ht_eq⟩ := hτz_top
  have htpos : 0 < t := lt_trans zero_lt_one ht
  obtain ⟨m', hm'⟩ := angDouble_it2m_add_int_aux u k
  have hray_eq : Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] u) t
      = Work.EL.rayPt hN θ' t := by
    rw [hm', hm, Work.ELTop.rayPt_add_int hN ((4 : ℝ) ^ k * u) t m',
      Work.ELTop.rayPt_add_int hN ((4 : ℝ) ^ k * u) t m]
  have ht_eq' : Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] u) t = tauC c k z :=
    hray_eq.trans ht_eq
  have hpotFz : Work.EL.pot hN (tauC c k z) = Real.log t := by
    rw [← ht_eq', Work.EL.pot_rayPt hN ht]
  have hlogt_lt : Real.log t < (4 : ℝ) ^ k * Real.log s₀ := by
    rw [← hpotFz]; exact hbound hz₁
  have hDpos : 0 < (4 : ℝ) ^ k := by positivity
  set s : ℝ := t ^ (((4 : ℝ) ^ k)⁻¹) with hsdef
  have hs1 : 1 < s := by
    rw [hsdef]; exact Real.one_lt_rpow ht (inv_pos.mpr hDpos)
  have hspow : s ^ (4 ^ k : ℕ) = t := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt htpos)]
    rw [show (((4 : ℕ) ^ k : ℕ) : ℝ) = (4 : ℝ) ^ k by push_cast; ring]
    rw [inv_mul_cancel₀ (ne_of_gt hDpos), Real.rpow_one]
  have hlog_s : Real.log s = ((4 : ℝ) ^ k)⁻¹ * Real.log t := by
    rw [hsdef, Real.log_rpow htpos]
  have hs_lt : s < s₀ := by
    refine (Real.log_lt_log_iff (Real.rpow_pos_of_pos htpos _)
      (lt_trans zero_lt_one hs₀)).mp ?_
    rw [hlog_s]
    calc ((4 : ℝ) ^ k)⁻¹ * Real.log t
        < ((4 : ℝ) ^ k)⁻¹ * ((4 : ℝ) ^ k * Real.log s₀) :=
          mul_lt_mul_of_pos_left hlogt_lt (inv_pos.mpr hDpos)
      _ = Real.log s₀ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul]
  have hrs : Work.EL.rayPt hN u s ∈ Metric.ball y ε₀ := hnear s ⟨hs1, hs_lt⟩
  have hF_ray : tauC c k (Work.EL.rayPt hN u s) = tauC c k z := by
    rw [show tauC c k (Work.EL.rayPt hN u s)
        = (Tantibar c)^[2 * k] (Work.EL.rayPt hN u s) from tauC_apply c k _,
      ← rayPt_iterate_angDouble hN hφ (θ := u) hs1, hspow]
    exact ht_eq'
  have hzeq : z = Work.EL.rayPt hN u s := hinj hz₀ hrs hF_ray.symm
  rw [hzeq]
  exact Work.EL.rayPt_mem_paramRay hN hs1


/-- `1`-periodicity of `LandsN` in the angle. -/
theorem landsN_add_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) (m : ℤ) (y : ℂ) :
    Work.EL.LandsN hN (θ + m) y ↔ Work.EL.LandsN hN θ y := by
  have h : (fun t : ℝ => Work.EL.rayPt hN (θ + m) t) = fun t : ℝ => Work.EL.rayPt hN θ t := by
    funext t; exact Work.ELTop.rayPt_add_int hN θ t m
  rw [Work.EL.LandsN, Work.EL.LandsN, h]

/-- The far side of a pair is invariant under integral shifts of the two angles. -/
theorem rawSide_add_int_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (a b : ℝ) (y : ℂ)
    (m n : ℤ) :
    Work.EL.RawPair.side hN (⟨a + m, b + n, y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.side hN ⟨a, b, y⟩ := by
  have hcurve : Work.EL.RawPair.curve hN (⟨a + m, b + n, y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.curve hN ⟨a, b, y⟩ := by
    simp only [Work.EL.RawPair.curve]
    rw [Work.ELTop.paramRay_add_int_aux hN a m, Work.ELTop.paramRay_add_int_aux hN b n]
  have hlen : Work.EL.arcLen (a + (m : ℝ)) (b + (n : ℝ)) = Work.EL.arcLen a b := by
    unfold Work.EL.arcLen
    rw [show b + (n : ℝ) - (a + (m : ℝ)) = (b - a) + ((n - m : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
  have hpt : Work.EL.rayPt hN (a + (m : ℝ) + Work.EL.arcLen (a + (m : ℝ)) (b + (n : ℝ)) / 2) 2
      = Work.EL.rayPt hN (a + Work.EL.arcLen a b / 2) 2 := by
    rw [hlen,
      show a + (m : ℝ) + Work.EL.arcLen a b / 2 = (a + Work.EL.arcLen a b / 2) + (m : ℝ)
        from by ring]
    exact Work.ELTop.rayPt_add_int hN (a + Work.EL.arcLen a b / 2) 2 m
  simp only [Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
  rw [hcurve, hpt]

/-- The far side of a pair is unchanged when the second angle is replaced by a congruent
representative. -/
theorem rawSide_fract {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (a b : ℝ) (y : ℂ) :
    Work.EL.RawPair.side hN (⟨a, a + Int.fract (b - a), y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.side hN ⟨a, b, y⟩ := by
  have hb : b = (a + Int.fract (b - a)) + ((⌊b - a⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor (b - a)
    push_cast
    linarith
  conv_rhs => rw [hb]
  simpa using (rawSide_add_int_aux hN a (a + Int.fract (b - a)) y 0 ⌊b - a⌋).symm

/-- The fractional part of a product in terms of the fractional part of the factor. -/
theorem fract_mul_eq (N u : ℝ) :
    Int.fract (N * u) = N * Int.fract u + (N * (⌊u⌋ : ℝ) - (⌊N * u⌋ : ℝ)) := by
  have h1 : N * u = N * Int.fract u + N * (⌊u⌋ : ℝ) := by
    rw [← mul_add, Int.fract_add_floor u]
  have h2 : Int.fract (N * u) = N * u - (⌊N * u⌋ : ℝ) := by
    linarith [Int.self_sub_fract (N * u)]
  rw [h2, h1]
  ring

theorem notMem_paramRay_of_fract_Ioo {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {x y s : ℝ}
    (hx1 : Int.fract y < x) (hx2 : x < Int.fract y + 1) (hs : 1 < s) :
    Work.EL.rayPt hN x s ∉ Work.EL.paramRay hN y := by
  refine Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN ?_)
    (Work.EL.rayPt_mem_paramRay hN hs)
  intro k hk
  have hval : Int.fract (y - x) = Int.fract y - x + 1 := by
    have hkey : y - x = (Int.fract y - x) + (⌊y⌋ : ℝ) := by
      have h := Int.fract_add_floor y; linarith
    rw [hkey, Int.fract_add_intCast]
    exact fract_eq_add_one' (by linarith) (by linarith)
  have h0 : Int.fract (y - x) = 0 := by
    rw [show y - x = (k : ℝ) by linarith, Int.fract_intCast]
  rw [hval] at h0
  linarith

/-! ## A pair of angles in `[0,1)` with distinct fractional parts is non-degenerate -/

/-- Two distinct angles of the half-open interval `[0,1)` represent different points of the
circle, so the cyclic arc between them is nondegenerate. -/
theorem arcLen_ne_zero_of_mem_Ico {a b : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (hb : b ∈ Set.Ico (0 : ℝ) 1) (h : a ≠ b) : Work.EL.arcLen a b ≠ 0 := by
  intro h0
  have hf : Int.fract (b - a) = 0 := h0
  obtain ⟨k, hk⟩ := Int.fract_eq_zero_iff.mp hf
  have hk' : (k : ℝ) = b - a := hk
  have h2 : (-(1 : ℝ) < (k : ℝ)) ∧ ((k : ℝ) < 1) := by
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hk']
  have h3 : k = 0 := by
    have h4 : (-1 : ℤ) < k := by exact_mod_cast h2.1
    have h5 : k < (1 : ℤ) := by exact_mod_cast h2.2
    omega
  rw [h3] at hk'
  push_cast at hk'
  exact h (by linarith)

/-! ## The local side transfer at a ray point, without normalising the angle into `(0,1)` -/

/-- **The local angle transfer, general form.**  At a point `p` of one of the two rays of a
co-landing pair `P` whose angles lie in the half-open interval `[0,1)`, the second return map
`τ = (T_c)^{2k}` carries the far side of `P` to the far side of the `4^k`-image pair `P'` on a
neighbourhood of `p`, and creates no point of the curve of `P'`.

This is `local_angle_gen_aux` with the hypothesis `P.a, P.b ∈ (0,1)` relaxed to `[0,1)`: the
external angle of a nearby point, lifted by a suitable integer
(`Work.LandLeaves.InArcHard.extAngle_close_at_gen_lift`), plays the role of the (unlifted)
external angle of the `(0,1)` case. -/
theorem localAngleGen_lift {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hk : 0 < k)
    (P P' : Work.EL.CoPair hN) (hS : Work.EL.PairSides hN P)
    (hS' : Work.EL.PairSides hN P')
    (hPa : P.a ∈ Set.Ico (0 : ℝ) 1) (hPb : P.b ∈ Set.Ico (0 : ℝ) 1) (hab : P.a ≠ P.b)
    (ha' : ∃ m : ℤ, P'.a = (4 : ℝ) ^ k * P.a + m)
    (hb' : ∃ m : ℤ, P'.b = (4 : ℝ) ^ k * P.b + m)
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0)
    {p : ℂ} (hp : p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b) :
    ∃ δ > 0, ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := by
  have hμ0 : 0 < Work.EL.arcLen P.a P.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _)
      (Ne.symm (arcLen_ne_zero_of_mem_Ico hPa hPb hab))
  have hμ1 : Work.EL.arcLen P.a P.b < 1 := Work.EL.arcLen_lt_one _ _
  have hμ'0 : 0 < Work.EL.arcLen P'.a P'.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _) (Ne.symm hnd')
  have hμ'1 : Work.EL.arcLen P'.a P'.b < 1 := Work.EL.arcLen_lt_one _ _
  set N : ℝ := (4 : ℝ) ^ k with hNdef
  have hN1 : 1 < N := by
    rw [hNdef]
    exact one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.mp hk)
  have hNpos : 0 < N := lt_trans zero_lt_one hN1
  have ha'' : ∃ m : ℤ, P'.a = N * P.a + m := by rw [hNdef]; exact ha'
  have hb'' : ∃ m : ℤ, P'.b = N * P.b + m := by rw [hNdef]; exact hb'
  set M : ℝ := min (min (Work.EL.arcLen P.a P.b) (1 - Work.EL.arcLen P.a P.b))
      (min (Work.EL.arcLen P'.a P'.b / N) ((1 - Work.EL.arcLen P'.a P'.b) / N)) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min hμ0 (by linarith))
      (lt_min (div_pos hμ'0 hNpos) (div_pos (by linarith) hNpos))
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hM1 : M ≤ Work.EL.arcLen P.a P.b := by
    rw [hMdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hM2 : M ≤ 1 - Work.EL.arcLen P.a P.b := by
    rw [hMdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hM3 : M ≤ Work.EL.arcLen P'.a P'.b / N := by
    rw [hMdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hM4 : M ≤ (1 - Work.EL.arcLen P'.a P'.b) / N := by
    rw [hMdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hημ : η ≤ Work.EL.arcLen P.a P.b / 2 := by rw [hηdef]; linarith
  have hη1μ : η ≤ (1 - Work.EL.arcLen P.a P.b) / 2 := by rw [hηdef]; linarith
  have hNμ' : N * (Work.EL.arcLen P'.a P'.b / N) = Work.EL.arcLen P'.a P'.b := by
    field_simp
  have hN1μ' : N * ((1 - Work.EL.arcLen P'.a P'.b) / N)
      = 1 - Work.EL.arcLen P'.a P'.b := by field_simp
  have hημ' : N * η ≤ Work.EL.arcLen P'.a P'.b / 2 := by
    have h := mul_le_mul_of_nonneg_left hM3 (le_of_lt hNpos)
    rw [hNμ'] at h
    have hrw : N * η = N * M / 2 := by rw [hηdef]; ring
    rw [hrw]; linarith
  have hη1μ' : N * η ≤ (1 - Work.EL.arcLen P'.a P'.b) / 2 := by
    have h := mul_le_mul_of_nonneg_left hM4 (le_of_lt hNpos)
    rw [hN1μ'] at h
    have hrw : N * η = N * M / 2 := by rw [hηdef]; ring
    rw [hrw]; linarith
  have hab_int : ∀ j : ℤ, P.b ≠ P.a + j := by
    intro j hj
    exact hμ0.ne' (by
      rw [Work.EL.arcLen, hj, show P.a + (j : ℝ) - P.a = (j : ℝ) by ring, Int.fract_intCast])
  have hab'_int : ∀ j : ℤ, P'.b ≠ P'.a + j := by
    intro j hj
    exact hnd' (by
      rw [Work.EL.arcLen, hj, show P'.a + (j : ℝ) - P'.a = (j : ℝ) by ring, Int.fract_intCast])
  rcases hp with hp | hp
  · have hp' : p ∈ Work.Top.NakaneData.paramRay hN P.a := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt hN P.a t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ :=
      Work.LandLeaves.InArcHard.extAngle_close_at_gen_lift hN (e := P.a) hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt hN P.a t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, m, hzang⟩ := hδ z hzn
    set φa : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z + (m : ℝ) with hφadef
    set σ : ℝ := φa - P.a with hσdef
    have hσabs : |σ| < η := by rw [hσdef, hφadef]; exact hzang
    have hφray : z ∈ Work.EL.paramRay hN φa := by
      have h1 : z ∈ Work.Top.NakaneData.paramRay hN
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z + (m : ℝ)) := by
        rw [Work.ELTop.paramRay_add_int hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) m]
        exact Work.Top.mem_paramRay_extAngle hN hzK
      rw [hφadef]
      exact h1
    have hφeq : φa = P.a + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφPa : φa = P.a := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inl (hφPa ▸ hφray))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_a (N := N) hN1 hφeq ha'' hb'' hσne hσabs
        hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    have hFmem : tauC c k z ∈ Work.EL.paramRay hN (Int.fract (N * φa)) := by
      have h := tauC_mem_paramRay_fract_aux (k := k) hN hφ hφray
      rw [← hNdef] at h
      exact h
    have hKy : P'.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P'.lands_a
    have hFzK : tauC c k z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN _ hFmem
    refine ⟨?_, ?_⟩
    · rw [Work.EL.mem_pairCurve_iff]
      simp only [not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFa j hj
      · intro heqy
        exact hFzK (by rw [heqy]; exact hKy)
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFb j hj
    · exact (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P hS hab_int hna hnb hφray).trans
        (heq.trans
          (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P' hS' hab'_int hFa hFb hFmem).symm)
  · have hp' : p ∈ Work.Top.NakaneData.paramRay hN P.b := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt hN P.b t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ :=
      Work.LandLeaves.InArcHard.extAngle_close_at_gen_lift hN (e := P.b) hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt hN P.b t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, m, hzang⟩ := hδ z hzn
    set φa : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z + (m : ℝ) with hφadef
    set σ : ℝ := φa - P.b with hσdef
    have hσabs : |σ| < η := by rw [hσdef, hφadef]; exact hzang
    have hφray : z ∈ Work.EL.paramRay hN φa := by
      have h1 : z ∈ Work.Top.NakaneData.paramRay hN
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z + (m : ℝ)) := by
        rw [Work.ELTop.paramRay_add_int hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) m]
        exact Work.Top.mem_paramRay_extAngle hN hzK
      rw [hφadef]
      exact h1
    have hφeq : φa = P.b + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφPb : φa = P.b := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inr (hφPb ▸ hφray)))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_b (N := N) hN1 hφeq ha'' hb'' hσne hσabs
        hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    have hFmem : tauC c k z ∈ Work.EL.paramRay hN (Int.fract (N * φa)) := by
      have h := tauC_mem_paramRay_fract_aux (k := k) hN hφ hφray
      rw [← hNdef] at h
      exact h
    have hKy : P'.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P'.lands_a
    have hFzK : tauC c k z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl hN _ hFmem
    refine ⟨?_, ?_⟩
    · rw [Work.EL.mem_pairCurve_iff]
      simp only [not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFa j hj
      · intro heqy
        exact hFzK (by rw [heqy]; exact hKy)
      · intro hmem
        obtain ⟨j, hj⟩ := Work.SeedSimple2.COP.exists_eq_add_int_of_mem_paramRay hN hFmem hmem
        exact hFb j hj
    · exact (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P hS hab_int hna hnb hφray).trans
        (heq.trans
          (Work.SeedSimple2.COP.mem_pairSide_iff_InArc hN P' hS' hab'_int hFa hFb hFmem).symm)

end

end Work.LandLeaves.InArcHard.Core
