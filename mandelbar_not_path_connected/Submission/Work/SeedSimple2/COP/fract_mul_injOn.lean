import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.pti
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- **`F` is injective on the landing angles** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L3`): two landing angles at `z₁` with the same `F`-image angle (`Int.fract (1024 ·)`) are equal.  This is what makes the angle ordering of §4.2 *strict*.

Proof (design note `L3`): take `ε` from `Work.SeedSimple2.COP.pti d ha.2` and `s ∈ (1,s₁)` with `z := Work.EL.rayPt d.hN b s ∈ Metric.ball d.z₁ ε` (using `hb.2 : Work.EL.LandsN d.hN b d.z₁`, i.e. `rayPt b s → z₁` as `s → 1⁺`);  then `Work.EL.F c z ∈ Work.EL.paramRay d.hN (1024 * b)` (`Work.ELRig.rayPt_iterate` + `Work.ELRig.T_iterate_eq_add_int` + `Work.ELTop.paramRay_add_int`), and `h` turns `1024 * b` into `1024 * a + k` (`k : ℤ`), so `pti` gives `z ∈ Work.EL.paramRay d.hN a`.  With `z ∈ Work.EL.paramRay d.hN b` (`Work.EL.rayPt_mem_paramRay`) and `Work.ELTop.paramRay_disjoint`, `b = a + k` for some `k : ℤ`;  as `a, b ∈ Set.Ico 0 1` (from `LandAngles`), `k = 0` and `a = b`. -/
theorem fract_mul_injOn {c : ℂ} (d : Work.EL.RootParabolic c) {a b : ℝ}
    (ha : a ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (hb : b ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (h : Int.fract (1024 * a) = Int.fract (1024 * b)) : a = b := by
  obtain ⟨ε, hε, hpti⟩ := pti d ha.2
  obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN d.hN hb.2 hε
  -- a small level `s ∈ (1, s₀)`
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, 1 < s ∧ s < s₀ :=
    ⟨(1 + s₀) / 2, by linarith, by linarith⟩
  have hz : Work.EL.rayPt d.hN b s ∈ Metric.ball d.z₁ ε := hnear s ⟨hs1, hs2⟩
  -- the integer `k` with `1024 * b = 1024 * a + k`
  set k : ℤ := Int.floor (1024 * b) - Int.floor (1024 * a) with hkdef
  have hrepr : (1024 : ℝ) * b = 1024 * a + (k : ℝ) := by
    have h1 := Int.fract_add_floor ((1024 : ℝ) * a)
    have h2 := Int.fract_add_floor ((1024 : ℝ) * b)
    rw [hkdef]
    push_cast
    linarith [h1, h2, h]
  -- the angle congruence `T^[10] b ≡ 1024 b (mod ℤ)`
  obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int b 10
  have hm' : (Work.EL.T^[10]) b = 1024 * b + (m : ℝ) := by
    have hh : ((-2 : ℝ) ^ 10) = 1024 := by norm_num
    rw [hh] at hm
    exact hm
  have hangle : (Work.EL.T^[10]) b = (1024 * a + (k : ℝ)) + (m : ℝ) := by
    rw [hm', hrepr]
  have hparam : Work.EL.paramRay d.hN ((Work.EL.T^[10]) b)
      = Work.EL.paramRay d.hN (1024 * a + (k : ℝ)) := by
    rw [hangle]
    exact Work.ELTop.paramRay_add_int d.hN (1024 * a + (k : ℝ)) m
  have hs1024 : 1 < s ^ (1024 : ℕ) := one_lt_pow₀ hs1 (by norm_num)
  have hFz : Work.EL.F c (Work.EL.rayPt d.hN b s)
      = Work.EL.rayPt d.hN ((Work.EL.T^[10]) b) (s ^ (1024 : ℕ)) :=
    Work.ELRig.rayPt_iterate d.hN d.bottcher hs1
  have hFmem : Work.EL.F c (Work.EL.rayPt d.hN b s)
      ∈ Work.EL.paramRay d.hN (1024 * a + (k : ℝ)) := by
    rw [hFz, ← hparam]
    exact Work.EL.rayPt_mem_paramRay d.hN hs1024
  have hza : Work.EL.rayPt d.hN b s ∈ Work.EL.paramRay d.hN a :=
    hpti (Work.EL.rayPt d.hN b s) hz (1024 * a + (k : ℝ)) ⟨k, rfl⟩ hFmem
  have hzb : Work.EL.rayPt d.hN b s ∈ Work.EL.paramRay d.hN b :=
    Work.EL.rayPt_mem_paramRay d.hN hs1
  -- the intersection of the two rays forces `b ≡ a (mod ℤ)`
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ, b = a + (k' : ℝ) := by
    by_contra hc
    push Not at hc
    have hdisj := Work.ELTop.paramRay_disjoint d.hN (θ := a) (θ' := b) hc
    rw [Set.disjoint_left] at hdisj
    exact hdisj hza hzb
  -- `a, b ∈ [0,1)` forces `k' = 0`
  have hk'0 : k' = 0 := by
    have hlt : (k' : ℝ) < 1 := by linarith [hb.1.2, ha.1.1, hk']
    have hgt : -1 < (k' : ℝ) := by linarith [ha.1.2, hb.1.1, hk']
    have hlt' : k' < 1 := by exact_mod_cast hlt
    have hgt' : -1 < k' := by exact_mod_cast hgt
    omega
  rw [hk'0, Int.cast_zero, add_zero] at hk'
  exact hk'.symm

end Work.SeedSimple2.COP
