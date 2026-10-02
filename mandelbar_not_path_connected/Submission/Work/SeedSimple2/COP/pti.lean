import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.F_basics
import Submission.Work.ELRig.localInjOn_F
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.landsN_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

set_option maxHeartbeats 2000000

noncomputable section

namespace Work.SeedSimple2.COP

/-- **Level tail of a landing ray.**  If the ray of angle `a` lands at `y`, then for every
`ε > 0` the ray points of small level `s ∈ (1, s₀)` lie in the ball `ball y ε`. This is the
"eventually" content of the definition of landing, extracted with the basis
`Ioo 1 s₀` of `𝓝[>] 1`. -/
theorem exists_level_ball_of_landsN {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {a : ℝ} {y : ℂ} (ha : Work.EL.LandsN hN a y) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ > 1, ∀ s ∈ Set.Ioo 1 s₀, Work.EL.rayPt hN a s ∈ Metric.ball y ε := by
  have hmem : {s : ℝ | Work.EL.rayPt hN a s ∈ Metric.ball y ε} ∈ 𝓝[>] (1 : ℝ) :=
    ha (Metric.ball_mem_nhds y hε)
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hmem
  exact ⟨s₀, hs₀, fun s hs => hsub hs⟩

/-- **The preimage-tail identity near `z₁`** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L2`; design in `COP/NOTES_COP.md` §1): if the ray `R(a)` lands at `z₁` then, on a small ball around `z₁`, `F z` on a ray of an angle congruent to `1024 a` forces `z` itself to be on `R(a)`.

Proof (see the design note): take `ε₀` from `Work.ELRig.localInjOn_F` (using `deriv (F c) z₁ = 1`, i.e. `d.mult`); from `ha` get `s₀ > 1` with `rayPt a s ∈ ball z₁ ε₀` for `s ∈ (1,s₀)`; use continuity of `pot` at `z₁` (`d.hN.continuous_potential`, `pot z₁ = 0` via `Work.ELTop.landsN_mem_K`) and `F z₁ = z₁` (`Work.SeedSimple2.COP.F_z₁`) to get `ε₁ > 0` with `pot (F z) < 1024 * Real.log s₀` on `ball z₁ ε₁`.  For `z ∈ ball z₁ ε` (`ε := min ε₀ ε₁`) with `F z = rayPt θ' t` (`t > 1`), `Real.log t = pot (F z)` (`pot_rayPt`), so `s := t ^ (1/1024) ∈ (1, s₀)`;  `rayPt a s ∈ ball z₁ ε₀` and `F (rayPt a s) = rayPt ((T^[10]) a) (s^1024) = rayPt θ' t = F z` (`rayPt_iterate`, `T_iterate_eq_add_int`, `rayPt_add_int`), so injectivity gives `z = rayPt a s ∈ R(a)` (`rayPt_mem_paramRay`). -/
theorem pti {c : ℂ} (d : Work.EL.RootParabolic c) {a : ℝ}
    (ha : Work.EL.LandsN d.hN a d.z₁) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ε → ∀ θ' : ℝ,
      (∃ k : ℤ, θ' = 1024 * a + k) → Work.EL.F c z ∈ Work.EL.paramRay d.hN θ' →
      z ∈ Work.EL.paramRay d.hN a := by
  obtain ⟨ε₀, hε₀, hinj⟩ := exists_injOn_F d
  obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN d.hN ha hε₀
  -- `z₁` is in the filled Julia set, so its potential vanishes; `F` fixes it.
  have hz₁K : d.z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN ha
  have hpot_z₁ : Work.EL.pot d.hN d.z₁ = 0 := Work.EL.pot_of_mem d.hN hz₁K
  have hFz₁ : Work.EL.F c d.z₁ = d.z₁ := F_z₁ d
  have hLpos : 0 < 1024 * Real.log s₀ :=
    mul_pos (by norm_num) (Real.log_pos hs₀)
  -- `pot ∘ F` is continuous at `z₁`, where it takes the value `0 < 1024 log s₀`.
  have hcont : Continuous (fun z : ℂ => Work.EL.pot d.hN (Work.EL.F c z)) :=
    d.hN.continuous_potential.comp (Work.ELRig.differentiable_F c).continuous
  have hmem : {z : ℂ | Work.EL.pot d.hN (Work.EL.F c z) < 1024 * Real.log s₀} ∈ 𝓝 d.z₁ :=
    (isOpen_lt hcont continuous_const).mem_nhds (by
      simp only [Set.mem_ofPred_eq, hFz₁, hpot_z₁]
      exact hLpos)
  obtain ⟨ε₁, hε₁, hbound⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro z hz θ' hθ' hFz
  obtain ⟨k, hk⟩ := hθ'
  have hz₀ : z ∈ Metric.ball d.z₁ ε₀ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hz₁' : z ∈ Metric.ball d.z₁ ε₁ := Metric.ball_subset_ball (min_le_right _ _) hz
  -- write `F z` as a ray point of angle `θ'` and level `t > 1`
  have hFz' : Work.EL.F c z ∈ Work.Top.NakaneData.paramRay d.hN θ' := hFz
  rw [Work.Top.NakaneData.paramRay_eq_range] at hFz'
  obtain ⟨⟨t, ht⟩, ht_eq⟩ := hFz'
  have ht_eq' : Work.EL.rayPt d.hN θ' t = Work.EL.F c z := ht_eq
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hpotFz : Work.EL.pot d.hN (Work.EL.F c z) = Real.log t := by
    rw [← ht_eq', Work.EL.pot_rayPt d.hN ht]
  have hlogt_lt : Real.log t < 1024 * Real.log s₀ := by
    rw [← hpotFz]; exact hbound hz₁'
  -- the level `s = t ^ (1/1024)`
  set s : ℝ := t ^ ((1024 : ℝ)⁻¹) with hsdef
  have hs1 : 1 < s := by
    rw [hsdef]; exact Real.one_lt_rpow ht (by norm_num)
  have hspow : s ^ (1024 : ℕ) = t := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt htpos)]
    rw [show ((1024 : ℝ)⁻¹ * ((1024 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
  have hlog_s : Real.log s = (1024 : ℝ)⁻¹ * Real.log t := by
    rw [hsdef, Real.log_rpow htpos]
  have hs_lt : s < s₀ := by
    refine (Real.log_lt_log_iff (Real.rpow_pos_of_pos htpos _)
      (lt_trans zero_lt_one hs₀)).mp ?_
    rw [hlog_s]
    calc (1024 : ℝ)⁻¹ * Real.log t
        < (1024 : ℝ)⁻¹ * (1024 * Real.log s₀) :=
          mul_lt_mul_of_pos_left hlogt_lt (by norm_num)
      _ = Real.log s₀ := by
          rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (1024 : ℝ) ≠ 0), one_mul]
  have hrs : Work.EL.rayPt d.hN a s ∈ Metric.ball d.z₁ ε₀ := hnear s ⟨hs1, hs_lt⟩
  -- the angle congruence `T^[10] a ≡ 1024 a (mod ℤ)`
  obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int a 10
  have hm' : Work.EL.T^[10] a = 1024 * a + (m : ℝ) := by
    have h : ((-2 : ℝ) ^ 10) = 1024 := by norm_num
    rw [h] at hm
    exact hm
  -- `F` maps `rayPt a s` and `z` to the same point
  have hF_ray : Work.EL.F c (Work.EL.rayPt d.hN a s) = Work.EL.F c z := by
    rw [Work.ELRig.rayPt_iterate d.hN d.bottcher hs1, hspow, ← ht_eq', hm', hk,
      Work.ELTop.rayPt_add_int d.hN (1024 * a) t m,
      Work.ELTop.rayPt_add_int d.hN (1024 * a) t k]
  have hz_eq : z = Work.EL.rayPt d.hN a s := hinj hz₀ hrs hF_ray.symm
  rw [hz_eq]
  exact Work.EL.rayPt_mem_paramRay d.hN hs1

end Work.SeedSimple2.COP
