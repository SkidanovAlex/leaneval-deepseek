import Mathlib
import Submission.Work.SeedSimple2.Rotation.rotationZero_of_step
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.Angle
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.sidePreserve_core
import Submission.Work.ELRig.CylSides
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.landsN_map
import Submission.Work.SeedSimple2.Rotation.exists_arc_of_eventually_const
import Submission.Work.SeedSimple2.Rotation.exists_rayPt_mem_ball
import Submission.Work.SeedSimple2.Rotation.pairSide_imp_InArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.Rotation

/-! ## The angle arithmetic of the two root angles -/

theorem arcLen_alpha : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 = 33 / 1023 := by
  rw [Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2]
  norm_num

theorem alpha2_eq : Work.EL.alpha2 = Work.EL.alpha1 + 33 / 1023 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem mul_alpha1 : (1024 : ℝ) * Work.EL.alpha1 = 371 + Work.EL.alpha1 := by
  norm_num [Work.EL.alpha1]

theorem mul_alpha2 : (1024 : ℝ) * Work.EL.alpha2 = 404 + Work.EL.alpha2 := by
  norm_num [Work.EL.alpha2]

theorem notInArc_alpha1_add (k : ℤ) :
    ¬ Work.EL.InArc (Work.EL.alpha1 + (k : ℝ)) Work.EL.alpha1 Work.EL.alpha2 := by
  intro h
  rw [Work.EL.InArc] at h
  have h0 : Int.fract (Work.EL.alpha1 + (k : ℝ) - Work.EL.alpha1) = 0 := by
    rw [show Work.EL.alpha1 + (k : ℝ) - Work.EL.alpha1 = (k : ℝ) by ring, Int.fract_intCast]
  rw [h0] at h
  exact lt_irrefl 0 h.1

theorem notInArc_alpha2_add (k : ℤ) :
    ¬ Work.EL.InArc (Work.EL.alpha2 + (k : ℝ)) Work.EL.alpha1 Work.EL.alpha2 := by
  intro h
  rw [Work.EL.InArc] at h
  have h0 : Int.fract (Work.EL.alpha2 + (k : ℝ) - Work.EL.alpha1) = 33 / 1023 := by
    rw [show Work.EL.alpha2 + (k : ℝ) - Work.EL.alpha1
        = (Work.EL.alpha2 - Work.EL.alpha1) + (k : ℝ) by ring, Int.fract_add_intCast]
    rw [show Work.EL.alpha2 - Work.EL.alpha1 = 33 / 1023 by
      rw [alpha2_eq]; ring]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  rw [h0, arcLen_alpha] at h
  exact lt_irrefl _ h.2

/-! ## The main theorem -/

theorem arcBound_of_sidePreserve {c : ℂ} (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (P : Work.EL.CoPair d.hN) (hPa1 : P.a = Work.EL.alpha1) (hPb1 : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁)
    (hSP : ∃ ρ > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ρ → z ∉ Work.EL.pairCurve P →
      (z ∈ Work.EL.pairSide P ↔ Work.FSeed.F c z ∈ Work.EL.pairSide P)) :
    Work.SeedSimple2.Rotation.ArcBoundAt d := by
  intro θ hθ
  obtain ⟨hθIco, hθland⟩ := hθ
  obtain ⟨ρ, hρ, hSP'⟩ := hSP
  -- the two-sidedness of the pair
  have hab : Work.EL.alpha1 < Work.EL.alpha2 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hb1 : Work.EL.alpha2 < Work.EL.alpha1 + 1 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hnd : Work.EL.arcLen P.a P.b ≠ 0 := by
    rw [hPa1, hPb1]
    exact Work.ELTop.arcLen_ne_zero_of_lt hab hb1
  have hside : Work.EL.PairSides d.hN P := Work.ELTop.pairSides d.hN hJ P hnd
  -- the iterates of θ land at z₁
  have hfix5 : ∀ m : ℕ, ((Tantibar c)^[5])^[m] d.z₁ = d.z₁ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, d.per_half]
  have hland_pow : ∀ n : ℕ, Work.EL.LandsN d.hN ((1024 : ℝ) ^ n * θ) d.z₁ := by
    intro n
    have h1 : Work.EL.LandsN d.hN ((Work.EL.T^[10 * n]) θ) d.z₁ := by
      have h := Work.SeedSimple2.landsN_T_iterate d (10 * n) hθland
      rw [show (Tantibar c)^[10 * n] d.z₁ = ((Tantibar c)^[5])^[2 * n] d.z₁ by
        rw [show 10 * n = 5 * (2 * n) by ring, Function.iterate_mul], hfix5 (2 * n)] at h
      exact h
    obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int θ (10 * n)
    have hm' : (Work.EL.T^[10 * n]) θ = (1024 : ℝ) ^ n * θ + (m : ℝ) := by
      rw [hm]
      congr 1
      rw [show ((-2 : ℝ)) ^ (10 * n) = (1024 : ℝ) ^ n by rw [pow_mul]; norm_num]
    exact (Work.SeedSimple2.landsN_add_int d m).mp (hm' ▸ h1)
  -- the one-step equivalence
  have step : ∀ y : ℝ, Work.EL.LandsN d.hN y d.z₁ →
      (Work.EL.InArc y Work.EL.alpha1 Work.EL.alpha2 ↔
        Work.EL.InArc ((1024 : ℝ) * y) Work.EL.alpha1 Work.EL.alpha2) := by
    intro y hy
    by_cases hy1 : ∃ k : ℤ, y = Work.EL.alpha1 + (k : ℝ)
    · obtain ⟨k, rfl⟩ := hy1
      refine ⟨fun h => absurd h (notInArc_alpha1_add k), fun h => ?_⟩
      rw [show (1024 : ℝ) * (Work.EL.alpha1 + (k : ℝ))
          = Work.EL.alpha1 + ((371 + 1024 * k : ℤ) : ℝ) by
        have h1 := mul_alpha1
        push_cast
        linarith] at h
      exact absurd h (notInArc_alpha1_add (371 + 1024 * k))
    · by_cases hy2 : ∃ k : ℤ, y = Work.EL.alpha2 + (k : ℝ)
      · obtain ⟨k, rfl⟩ := hy2
        refine ⟨fun h => absurd h (notInArc_alpha2_add k), fun h => ?_⟩
        rw [show (1024 : ℝ) * (Work.EL.alpha2 + (k : ℝ))
            = Work.EL.alpha2 + ((404 + 1024 * k : ℤ) : ℝ) by
          have h1 := mul_alpha2
          push_cast
          linarith] at h
        exact absurd h (notInArc_alpha2_add (404 + 1024 * k))
      · push Not at hy1 hy2
        obtain ⟨t, ht1, htball⟩ := exists_rayPt_mem_ball d.hN hy hρ
        set z : ℂ := Work.EL.rayPt d.hN y t with hzdef
        have hzray : z ∈ Work.EL.paramRay d.hN y := Work.EL.rayPt_mem_paramRay d.hN ht1
        have hznc : z ∉ Work.EL.pairCurve P := by
          intro hc
          rw [Work.EL.mem_pairCurve_iff] at hc
          rcases hc with hc | hc | hc
          · rw [hPa1] at hc
            exact (Set.disjoint_left.mp
              (Work.ELTop.paramRay_disjoint d.hN (θ := Work.EL.alpha1) (θ' := y)
                (fun k hk => hy1 k hk)) hc) hzray
          · have hK : z ∈ Work.EL.K c := by
              rw [hc]
              exact Work.ELTop.landsN_mem_K d.hN P.lands_a
            exact (Work.EL.paramRay_subset_compl d.hN y hzray) hK
          · rw [hPb1] at hc
            exact (Set.disjoint_left.mp
              (Work.ELTop.paramRay_disjoint d.hN (θ := Work.EL.alpha2) (θ' := y)
                (fun k hk => hy2 k hk)) hc) hzray
        have hkey : z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P := by
          have h := hSP' z htball hznc
          simpa [Work.FSeed.F, Work.EL.F] using h
        obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int y 10
        have hm1024 : Work.EL.T^[10] y = (1024 : ℝ) * y + (m : ℝ) := by
          rw [hm]
          congr 1
          rw [show ((-2 : ℝ)) ^ 10 = 1024 by norm_num]
        have hparam : Work.EL.paramRay d.hN (Work.EL.T^[10] y)
            = Work.EL.paramRay d.hN ((1024 : ℝ) * y) := by
          rw [hm1024]
          exact Work.ELTop.paramRay_add_int d.hN ((1024 : ℝ) * y) m
        have hFz : Work.EL.F c z = Work.EL.rayPt d.hN (Work.EL.T^[10] y) (t ^ (1024 : ℕ)) := by
          rw [hzdef]
          exact Work.ELRig.rayPt_iterate d.hN d.bottcher ht1
        have hz' : Work.EL.F c z ∈ Work.EL.paramRay d.hN ((1024 : ℝ) * y) := by
          rw [hFz, ← hparam]
          exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ ht1 (by norm_num))
        have h1 : Work.EL.InArc y Work.EL.alpha1 Work.EL.alpha2 ↔ z ∈ Work.EL.pairSide P :=
          ⟨fun h => (hside.paramRay_far y (by rw [hPa1, hPb1]; exact h)) hzray,
           fun h => pairSide_imp_InArc d.hN P hPa1 hPb1 hside hzray h⟩
        have h2 : Work.EL.InArc ((1024 : ℝ) * y) Work.EL.alpha1 Work.EL.alpha2 ↔
            Work.EL.F c z ∈ Work.EL.pairSide P :=
          ⟨fun h => (hside.paramRay_far ((1024 : ℝ) * y) (by rw [hPa1, hPb1]; exact h)) hz',
           fun h => pairSide_imp_InArc d.hN P hPa1 hPb1 hside hz' h⟩
        exact h1.trans (hkey.trans h2.symm)
  -- the orbit stays in the same arc status
  have horb : ∀ n : ℕ, Work.EL.InArc ((1024 : ℝ) ^ n * θ) Work.EL.alpha1 Work.EL.alpha2 ↔
      Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := step ((1024 : ℝ) ^ n * θ) (hland_pow n)
      rw [show (1024 : ℝ) ^ (n + 1) * θ = (1024 : ℝ) * ((1024 : ℝ) ^ n * θ) by ring]
      exact h1.symm.trans ih
  -- the values of the orbit
  let w : ℕ → ℝ := fun n => Int.fract ((1024 : ℝ) ^ n * θ - Work.EL.alpha1)
  have hInArc_w : ∀ n : ℕ, Work.EL.InArc ((1024 : ℝ) ^ n * θ) Work.EL.alpha1 Work.EL.alpha2 ↔
      (0 < w n ∧ w n < 33 / 1023) := by
    intro n
    simp only [Work.EL.InArc, arcLen_alpha]
    rfl
  have hwstep : ∀ k : ℕ, (w k = 0 ∨ w k = 33 / 1023) → w (k + 1) = w k := by
    intro k hk
    rcases hk with hk | hk
    · have hk' : Int.fract ((1024 : ℝ) ^ k * θ - Work.EL.alpha1) = 0 := hk
      obtain ⟨j, hj⟩ := Int.fract_eq_zero_iff.mp hk'
      have hj' : (1024 : ℝ) ^ k * θ = Work.EL.alpha1 + (j : ℝ) := by linarith
      show Int.fract ((1024 : ℝ) ^ (k + 1) * θ - Work.EL.alpha1)
        = Int.fract ((1024 : ℝ) ^ k * θ - Work.EL.alpha1)
      rw [show (1024 : ℝ) ^ (k + 1) * θ = 1024 * ((1024 : ℝ) ^ k * θ) by ring, hj']
      rw [show (1024 : ℝ) * (Work.EL.alpha1 + (j : ℝ)) - Work.EL.alpha1
          = (Work.EL.alpha1 + (j : ℝ) - Work.EL.alpha1) + (((371 : ℤ) + 1023 * j : ℤ) : ℝ) by
        have h1 := mul_alpha1
        push_cast
        linarith,
        Int.fract_add_intCast]
    · have hk' : Int.fract ((1024 : ℝ) ^ k * θ - Work.EL.alpha1) = 33 / 1023 := hk
      obtain ⟨-, -, j, hj⟩ :=
        (Int.fract_eq_iff (a := (1024 : ℝ) ^ k * θ - Work.EL.alpha1) (b := 33 / 1023)).mp hk'
      have hj' : (1024 : ℝ) ^ k * θ = Work.EL.alpha2 + (j : ℝ) := by
        have h32 := alpha2_eq
        linarith
      show Int.fract ((1024 : ℝ) ^ (k + 1) * θ - Work.EL.alpha1)
        = Int.fract ((1024 : ℝ) ^ k * θ - Work.EL.alpha1)
      rw [show (1024 : ℝ) ^ (k + 1) * θ = 1024 * ((1024 : ℝ) ^ k * θ) by ring, hj']
      rw [show (1024 : ℝ) * (Work.EL.alpha2 + (j : ℝ)) - Work.EL.alpha1
          = (Work.EL.alpha2 + (j : ℝ) - Work.EL.alpha1) + (((404 : ℤ) + 1023 * j : ℤ) : ℝ) by
        have h1 := mul_alpha2
        have h32 := alpha2_eq
        push_cast
        linarith,
        Int.fract_add_intCast]
  -- the final case analysis
  by_cases hA : Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2
  · have hpos : ∀ n : ℕ, (0 : ℝ) < w n := by
      intro n
      exact ((hInArc_w n).mp ((horb n).mpr hA)).1
    exact exists_arc_of_eventually_const (v := w) (p := 0) le_rfl (by norm_num)
      (fun n => Int.fract_nonneg _) (fun n => Int.fract_lt_one _) (Or.inl hpos)
  · by_cases hex : ∃ n₀ : ℕ, w n₀ = 0 ∨ w n₀ = 33 / 1023
    · obtain ⟨n₀, hn₀⟩ := hex
      have hconst : ∀ n : ℕ, n₀ < n → w n = w n₀ := by
        have hiter : ∀ m : ℕ, w (n₀ + m) = w n₀ := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            have hm : w (n₀ + m) = 0 ∨ w (n₀ + m) = 33 / 1023 := by rw [ih]; exact hn₀
            have h := hwstep (n₀ + m) hm
            rw [show n₀ + (m + 1) = (n₀ + m) + 1 by ring]
            exact h.trans ih
        intro n hn
        obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hn)
        exact hiter e
      exact exists_arc_of_eventually_const (v := w) (p := 0) le_rfl (by norm_num)
        (fun n => Int.fract_nonneg _) (fun n => Int.fract_lt_one _) (Or.inr ⟨n₀, hconst⟩)
    · push Not at hex
      have hgt : ∀ n : ℕ, 33 / 1023 < w n := by
        intro n
        have hnot : ¬ (0 < w n ∧ w n < 33 / 1023) := by
          intro h
          exact hA ((horb n).mp ((hInArc_w n).mpr h))
        have h0 : 0 < w n := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (hex n).1)
        have h33 : 33 / 1023 ≤ w n := by
          by_contra hlt
          push Not at hlt
          exact hnot ⟨h0, hlt⟩
        exact lt_of_le_of_ne h33 (Ne.symm (hex n).2)
      exact exists_arc_of_eventually_const (v := w) (p := 33 / 1023) (by norm_num)
        (by norm_num) (fun n => Int.fract_nonneg _) (fun n => Int.fract_lt_one _) (Or.inl hgt)

end Work.SeedSimple2.Rotation
