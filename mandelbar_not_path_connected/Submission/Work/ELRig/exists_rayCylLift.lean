/-
# ELRig — `RayCylLift`: the ray-lift data of the parity route (`TailId`)

`Work.ELRig.exists_rayCylLift` produces, from a root-parabolic parameter `c`, the Leau–Fatou
flower of `z₁` and the two landing statements of the root portrait, the full `RayCylLift`
bundle: the two `1`-periodic curves `γ₁`, `γ₂ = ι γ₁` (`ι w = w̄ + 1/2`) in the repelling
coordinate `Ψ`, the level parametrisation `τ`, and **`TailId`**: in the far-left half plane
`{Re < -R}` the `Ψ`-preimages of the two root rays are exactly the two lifts.

The curves with their level parametrisation, periodicity, anti-symmetry and the coverage of the
two *ray tails* (levels below an explicit `t₀`) are `exists_liftCurvesV3`.  The content of this
file is the passage from the tail coverage to the *full* `TailId`.

## The three steps

**(1) `τ` attains every level `> 1`.**  The coverage of `V3` at the two levels `t < t₀` together
with `exists_preimage_rayTail` shows that `(1, b) ⊆ range τ` for `b := min t₀ t₁ > 1`.  The
periodicity of `γ₁` together with `Ψ_shift`, `rayPt_F_alpha1` and `rayPt_level_inj` gives the
self-similarity `τ (s+1) = (τ s)^1024`.  Hence `range τ` is closed under `x ↦ x^1024`, so
`(1, b^{1024^n}) ⊆ range τ` for all `n`, and the union of these intervals is `(1, ∞)`
(`range_eq_Ioi_of_pow1024`).  The strict monotonicity of `τ` (a `V3` field) is *not* needed for
this.

**(2) the lift leaves the injectivity half plane far to the left.**  With `M` bounding
`Re γ₁` on `[0,1]` (continuity of `γ₁`) and the periodicity `hiter : γ₁ u = γ₁ (u+m) - m` one
gets `s*` with `(γ₁ s).re < -R₀ - 1` for all `s ≤ s*`, where `R₀` is the injectivity half plane
of the flower.

**(3) `TailId`.**  Let `w` with `Re w < -R` and `Ψ w = rayPt α₁ t`, `t > 1`.  By (1) `t = τ s`;
if `(γ₁ s).re ≥ -R₀ - 1` then `s ≥ s*` by (2), so `t = τ s ≥ τ s*`, and the *potential* of
`rayPt α₁ t` is `log t ≥ log (τ s*) > 0`: a ray point of a far level stays at distance
`≥ δ` from `z₁`, while `Ψ (H_R) ⊆ ball z₁ δ` for `R` large (`Ψ_small`), contradiction.  Hence
`γ₁ s` and `w` both lie in the injectivity half plane `{Re < -R₀}` and have the same
`Ψ`-image, so `w = γ₁ s ∈ range γ₁`.  The same argument with the level `(τ s)^32` handles the
second ray (using `Ψ_anti` and `rayPt_g_alpha1`).

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.exists_liftCurvesV2
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.rayTail_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar)

/-- **A `1`-periodic level parametrisation that attains a non-degenerate interval of levels
attains them all.**  If `τ (s+1) = (τ s) ^ 1024`, all values of `τ` are `> 1`, and `τ` attains
every level of `(1, b)` for some `b > 1`, then `range τ = (1, ∞)`.

The range of `τ` is closed under `x ↦ x ^ 1024` (the self-similarity), so the seed interval
`(1, b)` produces the intervals `(1, b ^ (1024 ^ n))`, whose union is `(1, ∞)`. -/
theorem range_eq_Ioi_of_pow1024 {τ : ℝ → ℝ}
    (hper : ∀ s : ℝ, τ (s + 1) = (τ s) ^ (1024 : ℕ))
    (h1 : ∀ s : ℝ, 1 < τ s) {b : ℝ} (hb : 1 < b) (hseed : Set.Ioo 1 b ⊆ Set.range τ) :
    Set.range τ = Set.Ioi 1 := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨s, rfl⟩ := hx
    exact h1 s
  · intro t ht
    have hstep : ∀ n : ℕ, Set.Ioo 1 (b ^ (1024 ^ n)) ⊆ Set.range τ := by
      intro n
      induction n with
      | zero => simpa using hseed
      | succ n ih =>
        intro x ⟨hx1, hx2⟩
        have hxpos : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx1)
        have hbpow_pos : 0 ≤ b ^ (1024 ^ n) := by
          have hge : (1 : ℝ) ≤ b ^ (1024 ^ n) := one_le_pow₀ (le_of_lt hb)
          linarith
        have hu1 : 1 < x ^ (((1024 : ℕ) : ℝ)⁻¹) := Real.one_lt_rpow hx1 (by norm_num)
        have hu_pos : 0 ≤ x ^ (((1024 : ℕ) : ℝ)⁻¹) := le_of_lt (lt_trans zero_lt_one hu1)
        have hult : x ^ (((1024 : ℕ) : ℝ)⁻¹) < b ^ (1024 ^ n) := by
          refine (pow_lt_pow_iff_left₀ (a := x ^ (((1024 : ℕ) : ℝ)⁻¹))
            (b := b ^ (1024 ^ n)) hu_pos hbpow_pos (by norm_num : (1024 : ℕ) ≠ 0)).mp ?_
          show (x ^ (((1024 : ℕ) : ℝ)⁻¹)) ^ (1024 : ℕ) < (b ^ (1024 ^ n)) ^ (1024 : ℕ)
          rw [Real.rpow_inv_natCast_pow hxpos (by norm_num : (1024 : ℕ) ≠ 0), ← pow_mul,
            ← pow_succ]
          exact hx2
        obtain ⟨s, hs⟩ := ih ⟨hu1, hult⟩
        refine ⟨s + 1, ?_⟩
        rw [hper s, hs, Real.rpow_inv_natCast_pow hxpos (by norm_num : (1024 : ℕ) ≠ 0)]
    have htend : Tendsto (fun n : ℕ => b ^ (1024 ^ n)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hb).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 1024 by norm_num))
    obtain ⟨n, hn⟩ := (htend.eventually (Filter.eventually_gt_atTop t)).exists
    exact hstep n ⟨ht, hn⟩

theorem exists_rayCylLift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁)
    (h₂ : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁) :
    Nonempty (Work.ELRig.RayCylLift d fl) := by
  classical
  -- ===================== 1. the curves of `exists_liftCurvesV3` ==============================
  obtain ⟨R₀, hinj⟩ := fl.Ψ_inj
  obtain ⟨γ₁, γ₂, τ, t₀, ht₀, hτmono, hτ1, hΨ₁, hanti, hcont₁, hcont₂, hinj₁, hinj₂,
    hper₁, hper₂, hmem₁, hmem₂, hcov₁, hcov₂⟩ :=
    exists_liftCurvesV3 d fl h₁ h₂ (R := R₀) (R₀ := R₀) le_rfl hinj
  obtain ⟨t₁, ht₁, hpre₁⟩ := exists_preimage_rayTail d fl h₁ (R := R₀)
  -- ===================== 2. the level law of `τ` and `range τ = (1, ∞)` =====================
  have hτpow : ∀ s : ℝ, τ (s + 1) = (τ s) ^ (1024 : ℕ) := by
    intro s
    refine rayPt_level_inj d.hN (θ := Work.EL.alpha1) (hτ1 (s + 1))
      (one_lt_pow₀ (hτ1 s) (by norm_num)) ?_
    rw [← hΨ₁ (s + 1), hper₁ s, fl.Ψ_shift (γ₁ s), hΨ₁ s, rayPt_F_alpha1 d (hτ1 s)]
  have hseed : Set.Ioo 1 (min t₀ t₁) ⊆ Set.range τ := by
    rintro t ⟨ht1, htb⟩
    have htt₀ : t < t₀ := lt_of_lt_of_le htb (min_le_left _ _)
    have htt₁ : t < t₁ := lt_of_lt_of_le htb (min_le_right _ _)
    obtain ⟨w, hw, hΨw⟩ := hpre₁ t ht1 htt₁
    obtain ⟨s, hs⟩ := hcov₁ w hw ⟨t, ht1, htt₀, hΨw⟩
    exact ⟨s, rayPt_level_inj d.hN (θ := Work.EL.alpha1) (hτ1 s) ht1
      (by rw [← hΨ₁ s, hs, hΨw])⟩
  have hrange : Set.range τ = Set.Ioi 1 :=
    range_eq_Ioi_of_pow1024 hτpow hτ1 (lt_min ht₀ ht₁) hseed
  -- ===================== 3. the lift leaves the injectivity half plane on the far left ======
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) 1, (γ₁ u).re ≤ M := by
    obtain ⟨x, -, hxM⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
      ((Complex.continuous_re.comp hcont₁).continuousOn)
    exact ⟨(γ₁ x).re, fun u hu => hxM hu⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (M + R₀ + 1)
  have hiter : ∀ (u : ℝ) (m : ℕ), γ₁ u = γ₁ (u + m) - m := by
    intro u m
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep : γ₁ (u + ((m + 1 : ℕ) : ℝ)) = γ₁ (u + (m : ℝ)) + 1 := by
        have hu : u + ((m + 1 : ℕ) : ℝ) = (u + (m : ℝ)) + 1 := by push_cast; ring
        rw [hu, hper₁]
      rw [hstep, ih]
      push_cast
      ring
  have hsstar : ∃ sstar : ℝ, ∀ s : ℝ, s ≤ sstar → (γ₁ s).re < -R₀ - 1 := by
    refine ⟨-(n : ℝ), fun s hs => ?_⟩
    have hsn : (n : ℝ) ≤ -s := by linarith
    set m : ℕ := ⌈-s⌉.toNat with hm
    have hm_cast : ((m : ℤ)) = ⌈-s⌉ :=
      Int.toNat_of_nonneg (Int.ceil_nonneg (by linarith : (0 : ℝ) ≤ -s))
    have hm_real : (m : ℝ) = ((⌈-s⌉ : ℤ) : ℝ) := by exact_mod_cast hm_cast
    have hle_ceil : -s ≤ (m : ℝ) := by
      rw [hm_real]
      exact Int.le_ceil (-s)
    have hlt_ceil : (m : ℝ) < -s + 1 := by
      rw [hm_real]
      exact Int.ceil_lt_add_one (-s)
    have hm_ge : (n : ℝ) ≤ (m : ℝ) := le_trans hsn hle_ceil
    have hsum_ge : 0 ≤ s + (m : ℝ) := by linarith
    have hsum_lt : s + (m : ℝ) < 1 := by linarith
    have hMbound : (γ₁ (s + (m : ℝ))).re ≤ M :=
      hM (s + (m : ℝ)) ⟨hsum_ge, le_of_lt hsum_lt⟩
    have hrew : (γ₁ s).re = (γ₁ (s + (m : ℝ))).re - (m : ℝ) := by
      rw [hiter s m, Complex.sub_re, Complex.natCast_re]
    linarith
  obtain ⟨sstar, hsstar⟩ := hsstar
  -- ===================== 4. the potential controls the distance from `z₁` ====================
  have hz₁K : d.z₁ ∈ Work.EL.K c :=
    mem_K_of_iterate_eq_self (k := 5) (by norm_num) d.per_half
  have hpotcont : Continuous (Work.EL.pot d.hN) := by
    rw [show Work.EL.pot d.hN
      = Work.Top.potential (Work.EL.K c) (Work.EL.dynPhi c d.φ) by funext z; rfl]
    exact d.hN.continuous_potential
  have hpotz₁ : Work.EL.pot d.hN d.z₁ = 0 := Work.EL.pot_of_mem d.hN hz₁K
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ,
      ‖z - d.z₁‖ < δ → Work.EL.pot d.hN z < Real.log (τ sstar) := by
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hpotcont.continuousAt (Real.log (τ sstar))
        (Real.log_pos (hτ1 sstar))
    refine ⟨δ, hδpos, fun z hz => ?_⟩
    have h := hδ (show dist z d.z₁ < δ by rwa [dist_eq_norm])
    rw [Real.dist_eq, hpotz₁, sub_zero] at h
    exact (abs_lt.mp h).2
  obtain ⟨Rδ, hRδ⟩ := fl.Ψ_small δ hδpos
  obtain ⟨Rend, hRend⟩ := fl.Ψ_ends
  obtain ⟨Rinj, hRinj⟩ := fl.Ψ_inj
  set Rall : ℝ := max (max (max R₀ Rδ) (Rend + 1)) (Rinj + 1) with hRalldef
  have hmax₀ : R₀ ≤ max R₀ Rδ := le_max_left _ _
  have hmaxδ : Rδ ≤ max R₀ Rδ := le_max_right _ _
  have hmaxR : (max R₀ Rδ : ℝ) ≤ Rall := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₀Rall : R₀ ≤ Rall := le_trans hmax₀ hmaxR
  have hRδRall : Rδ ≤ Rall := le_trans hmaxδ hmaxR
  have hRendR : Rend + 1 ≤ Rall := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRinjR : Rinj + 1 ≤ Rall := le_max_right _ _
  have hRendlt : Rend < Rall := by linarith
  -- ===================== 5. the assembly =====================================================
  refine ⟨⟨γ₁, γ₂, τ, Rall, hτmono, hτ1, hΨ₁, hcont₁, hcont₂, hper₁, hper₂, hanti, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · -- `TailId` for the first ray
    intro w hw hmem
    change fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN Work.EL.alpha1 at hmem
    rw [Work.Top.NakaneData.paramRay_eq_range] at hmem
    obtain ⟨⟨t, ht1⟩, ht0⟩ := hmem
    have ht : Work.EL.rayPt d.hN Work.EL.alpha1 t = fl.Ψ w := ht0
    have htm : t ∈ Set.range τ := by rw [hrange]; exact ht1
    obtain ⟨s, hs⟩ := htm
    have hΨeq : fl.Ψ (γ₁ s) = fl.Ψ w := by rw [hΨ₁ s, hs, ht]
    have hwRδ : w.re < -Rδ := lt_of_lt_of_le hw (neg_le_neg hRδRall)
    have hwR₀ : w.re < -R₀ := lt_of_lt_of_le hw (neg_le_neg hR₀Rall)
    have hlow : (γ₁ s).re < -R₀ := by
      have hmain : (γ₁ s).re < -R₀ - 1 := by
        by_contra hcon
        have hsge : sstar ≤ s := by
          by_contra hlt
          exact hcon (hsstar s (le_of_lt (not_le.mp hlt)))
        have hτge : τ sstar ≤ τ s := hτmono.monotone hsge
        have hlev : Real.log (τ sstar) ≤ Work.EL.pot d.hN (fl.Ψ w) := by
          rw [← ht, Work.EL.pot_rayPt d.hN ht1, ← hs]
          exact Real.log_le_log (by linarith [hτ1 sstar]) hτge
        have hclose : Work.EL.pot d.hN (fl.Ψ w) < Real.log (τ sstar) :=
          hδ (fl.Ψ w) (hRδ w hwRδ).2
        linarith
      linarith
    exact ⟨s, hinj hlow hwR₀ hΨeq⟩
  · -- `TailId` for the second ray
    intro w hw hmem
    change fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN Work.EL.alpha2 at hmem
    rw [Work.Top.NakaneData.paramRay_eq_range] at hmem
    obtain ⟨⟨t, ht1⟩, ht0⟩ := hmem
    have ht : Work.EL.rayPt d.hN Work.EL.alpha2 t = fl.Ψ w := ht0
    have hu1 : 1 < t ^ (((32 : ℕ) : ℝ)⁻¹) := Real.one_lt_rpow ht1 (by norm_num)
    have humem : t ^ (((32 : ℕ) : ℝ)⁻¹) ∈ Set.range τ := by rw [hrange]; exact hu1
    obtain ⟨s, hs⟩ := humem
    have hpow : (t ^ (((32 : ℕ) : ℝ)⁻¹)) ^ (32 : ℕ) = t :=
      Real.rpow_inv_natCast_pow (le_of_lt (lt_trans zero_lt_one ht1)) (by norm_num)
    have hΨeq : fl.Ψ (γ₂ s) = fl.Ψ w := by
      rw [hanti s, fl.Ψ_anti (γ₁ s), hΨ₁ s, rayPt_g_alpha1 d (hτ1 s), hs, hpow, ht]
    have hwRδ : w.re < -Rδ := lt_of_lt_of_le hw (neg_le_neg hRδRall)
    have hwR₀ : w.re < -R₀ := lt_of_lt_of_le hw (neg_le_neg hR₀Rall)
    have hlow : (γ₂ s).re < -R₀ := by
      by_contra hcon
      have hsge : sstar ≤ s := by
        by_contra hlt
        refine hcon ?_
        have hgl := hsstar s (le_of_lt (not_le.mp hlt))
        have hre : (γ₂ s).re = (γ₁ s).re + 1 / 2 := by
          rw [hanti s]
          simp
        linarith
      have hτge : τ sstar ≤ τ s := hτmono.monotone hsge
      have hpow_le : τ sstar ≤ (τ s) ^ (32 : ℕ) :=
        le_trans hτge (le_self_pow₀ (le_of_lt (hτ1 s)) (by norm_num))
      have hlev : Real.log (τ sstar) ≤ Work.EL.pot d.hN (fl.Ψ w) := by
        rw [← ht, ← hpow, ← hs, Work.EL.pot_rayPt d.hN (one_lt_pow₀ (hτ1 s) (by norm_num))]
        exact Real.log_le_log (by linarith [hτ1 sstar]) hpow_le
      have hclose : Work.EL.pot d.hN (fl.Ψ w) < Real.log (τ sstar) :=
        hδ (fl.Ψ w) (hRδ w hwRδ).2
      linarith
    exact ⟨s, hinj hlow hwR₀ hΨeq⟩
  · -- `Ψ` misses `z₁` in the far left half plane
    intro w hw
    exact (hRδ w (lt_of_lt_of_le hw (neg_le_neg hRδRall))).1
  · -- the petal level: `Ψ_ends` at the level `Rend`, which is below `Rall`
    exact ⟨Rend, hRendlt, fun w hw him => hRend w hw him⟩
  · -- injectivity on the half plane at the level `Rinj < Rall`
    have hle : Rinj ≤ Rall := by linarith
    intro a ha b hb hab
    exact hRinj (lt_of_lt_of_le ha (neg_le_neg hle))
      (lt_of_lt_of_le hb (neg_le_neg hle)) hab

end Work.ELRig
