/-
# `ELAssembly.Derived.Fields` — the tripod fields of `CertGeometry` are derivable

`NOTES.md` §7.8 records that the certificate fields `cutA_mem`, `cutB_mem`, `cutC_mem`,
`b2_mem_D` and `Dnest_sub` are not independent inputs: given the tripod `T` and the arithmetic
of the six arm-angle families, the level-`n` arm-`A` landing point lies in the arm `A`, the
tripod point lies in every level of the nest at `b₂`, and that nest is decreasing.

The mechanism is the **`T^6`-rigidity** of the tripod point:

* `F6 c = (T_c)^6` carries the level-`(n+1)` arm landing point to the level-`n` one
  (`Work.ELAssembly.armY_shift`), while the tripod point is fixed by `T^6`
  (`Work.ELAssembly.tripod_T6_fix`); consequently, if `(Za k).y = T.y` for some `k` then
  descending the `T^6`-relation gives `(Za 0).y = T.y = z₁` (`Work.ELAssembly.descent_of_fixed`),
  whence `T^6 z₁ = z₁`, contradicting the exact period `5` of `z₁`
  (`Work.ELAssembly.not_fixed_T6_of`).

With `(Za n).y ≠ T.y` in hand the arm memberships follow from `Work.ELAssembly.tripod_mem` (the
ray of angle `armA1 n` lies in the far arc `(22/63, 25/63)` of the tripod pair), the
`b₂`-memberships from the same lemma (the tripod rays lie in the near arcs
`(armA2 n, armA1 n + 1)`), and `Dnest_sub` from `Work.ELAssembly.Dnest_sub_of` (the levels of
the `b₂`-nest are nested as soon as the three *near sides* shrink, which
`Work.ELAssembly.nest_side_of_nearArc` derives from the near-arc nesting of the arm angles and
the disjointness of the consecutive pair curves).
-/
import Mathlib
import Submission.Work.ELAssembly.Derived.Bases
import Submission.Work.ELAssembly.armAngle_facts
import Submission.Work.ELAssembly.armAngle_order
import Submission.Work.ELAssembly.armY_shift
import Submission.Work.ELAssembly.tripod_T6_fix
import Submission.Work.ELAssembly.pairCurve_disjoint_of
import Submission.Work.ELAssembly.tripod_mem
import Submission.Work.ELAssembly.Dnest_sub_of
import Submission.Work.ELAssembly.Dmem_of
import Submission.Work.ELAssembly.D_adm_of
import Submission.Work.ELAssembly.CutNe
import Submission.Work.ELAssembly.NestSide
import Submission.Work.ELAssembly.armChainInputs_of
import Submission.Work.ELAssembly.pullD_pair
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELNest.bAng_nest_arc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## Angular arithmetic helpers -/

/-- If `0 < y - x < 1` then `x` and `y` are incongruent modulo `1`, in both directions. -/
theorem ne_add_int_of_sub {x y : ℝ} (h0 : 0 < y - x) (h1 : y - x < 1) :
    (∀ k : ℤ, y ≠ x + k) ∧ (∀ k : ℤ, x ≠ y + k) := by
  have key : ∀ k : ℤ, (k : ℝ) = y - x → False := by
    intro k hk
    have hp : (0 : ℝ) < (k : ℝ) := by rw [hk]; exact h0
    have hq : (k : ℝ) < 1 := by rw [hk]; exact h1
    have hkZ : 0 < k := by exact_mod_cast hp
    have hkZ1 : k < 1 := by exact_mod_cast hq
    omega
  refine ⟨fun k h => key k (by linarith), fun k h => ?_⟩
  refine key (-k) ?_
  push_cast
  linarith

/-! ## `T^6`-rigidity of the parabolic cycle -/

/-- **No point of the cycle of `z₁` is fixed by `T^6`.**  If `T^[6] (T^[j] z₁) = T^[j] z₁` for a
`j < 5`, then applying `T^[5-j]` to both sides gives `T^[11] z₁ = T^[5] z₁ = z₁`, i.e.
`T z₁ = z₁`, contradicting the exact period `5` of `z₁`. -/
theorem not_fixed_T6_of (d : Work.EL.RootParabolic c) (j : ℕ) (hj : j < 5) :
    ((Tantibar c)^[6]) (((Tantibar c)^[j]) d.z₁) ≠ ((Tantibar c)^[j]) d.z₁ := by
  intro h
  have h1 : ((Tantibar c)^[6 + j]) d.z₁ = ((Tantibar c)^[j]) d.z₁ := by
    rw [Function.iterate_add_apply]
    exact h
  have h2 : ((Tantibar c)^[5 - j]) (((Tantibar c)^[6 + j]) d.z₁)
      = ((Tantibar c)^[5 - j]) (((Tantibar c)^[j]) d.z₁) := by rw [h1]
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h2
  rw [show 5 - j + (6 + j) = 11 from by omega,
    show 5 - j + j = 5 from by omega] at h2
  have h5 : ∀ k : ℕ, ((Tantibar c)^[5 * k]) d.z₁ = d.z₁ := by
    intro k
    induction k with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add_apply, d.per_half, ih]
  have h11 : ((Tantibar c)^[11]) d.z₁ = (Tantibar c) d.z₁ := by
    rw [show (11 : ℕ) = 1 + 10 from rfl, Function.iterate_add_apply, Function.iterate_one,
      show (10 : ℕ) = 5 * 2 from rfl, h5 2]
  rw [d.per_half] at h2
  have hT : (Tantibar c) d.z₁ = d.z₁ := by rw [← h11]; exact h2
  exact d.ne_per 1 (by decide) (by simpa using hT)

/-- **The relation `T^6 (Z (k+1)) = Z k` propagates `T^6`-fixedness down all levels.**  If `Z n`
is the fixed point `y`, then `Z k = T^[6(n-k)] y = y` for every `k ≤ n`, so `Z 0 = y`. -/
theorem descent_of_fixed {Z : ℕ → ℂ}
    (hsh : ∀ m : ℕ, ((Tantibar c)^[6]) (Z (m + 1)) = Z m) {y : ℂ}
    (hfix : ((Tantibar c)^[6]) y = y) {n : ℕ} (h : Z n = y) : Z 0 = y := by
  have hf : ∀ m : ℕ, ((Tantibar c)^[6 * m]) y = y := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, hfix, ih]
  have key : ∀ j : ℕ, j ≤ n → Z (n - j) = y := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [Nat.sub_zero]
        exact h
    | succ j ih =>
        intro hj
        have hj' : j ≤ n := le_trans (Nat.le_succ j) hj
        have hstep : Z (n - (j + 1)) = ((Tantibar c)^[6]) (Z (n - (j + 1) + 1)) :=
          (hsh (n - (j + 1))).symm
        rw [show n - (j + 1) + 1 = n - j from by omega] at hstep
        rw [hstep, ih hj']
        exact hfix
  have h0 := key n le_rfl
  rw [Nat.sub_self] at h0
  exact h0

/-! ## The arm landing points are not the tripod point -/

/-- **The level-`n` arm-`A` landing point is not the tripod point.** -/
theorem Za_ne_tripod (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    ∀ n : ℕ, (N.Za n).y ≠ T.y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Za (m + 1)).y) = (N.Za m).y :=
    (armY_shift d N).1
  have hfix : ((Tantibar c)^[6]) T.y = T.y := tripod_T6_fix d.hN d.bottcher T
  intro n h
  have hz : (N.Za 0).y = T.y := descent_of_fixed (Z := fun k => (N.Za k).y) hsh hfix h
  have hz1 : T.y = d.z₁ := by rw [← hz, Za_y_base d N]
  exact not_fixed_T6_of d 0 (by norm_num) (by rw [← hz1]; exact hfix)

/-- **The level-`n` arm-`B` landing point is not the tripod point.** -/
theorem Zb_ne_tripod (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    ∀ n : ℕ, (N.Zb n).y ≠ T.y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Zb (m + 1)).y) = (N.Zb m).y :=
    (armY_shift d N).2.1
  have hfix : ((Tantibar c)^[6]) T.y = T.y := tripod_T6_fix d.hN d.bottcher T
  intro n h
  have hz : (N.Zb 0).y = T.y := descent_of_fixed (Z := fun k => (N.Zb k).y) hsh hfix h
  have hz1 : T.y = ((Tantibar c)^[2]) d.z₁ := by rw [← hz, Zb_y_base d N]
  exact not_fixed_T6_of d 2 (by norm_num) (by rw [← hz1]; exact hfix)

/-- **The level-`n` arm-`C` landing point is not the tripod point.** -/
theorem Zc_ne_tripod (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    ∀ n : ℕ, (N.Zc n).y ≠ T.y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Zc (m + 1)).y) = (N.Zc m).y :=
    (armY_shift d N).2.2
  have hfix : ((Tantibar c)^[6]) T.y = T.y := tripod_T6_fix d.hN d.bottcher T
  intro n h
  have hz : (N.Zc 0).y = T.y := descent_of_fixed (Z := fun k => (N.Zc k).y) hsh hfix h
  have hz1 : T.y = ((Tantibar c)^[4]) d.z₁ := by rw [← hz, Zc_y_base d N]
  exact not_fixed_T6_of d 4 (by norm_num) (by rw [← hz1]; exact hfix)

/-! ## The cut points lie in the arms of the tripod, and `b₂` in every level -/

/-- **The level-`n` cut points lie in the arms of the tripod** (the fields
`CertGeometry.cutA_mem`/`cutB_mem`/`cutC_mem`, derived). -/
theorem cut_mem_of (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    (∀ n : ℕ, (N.Za n).y ∈ Work.EL.Tripod.armA T) ∧
    (∀ n : ℕ, (N.Zb n).y ∈ Work.EL.Tripod.armB T) ∧
    (∀ n : ℕ, (N.Zc n).y ∈ Work.EL.Tripod.armC T) := by
  obtain ⟨hA, hB, hC, -⟩ := tripod_mem d.hN Work.TopJordan.jordanForm T
  obtain ⟨-, -, h3, -, h5, -, h7, -, -, -, -, -, -, -⟩ := armAngle_facts
  exact ⟨fun n => hA (N.Za n) (by rw [N.Zaa n]; exact h3 n) (Za_ne_tripod d N T n),
    fun n => hB (N.Zb n) (by rw [N.Zba n]; exact h5 n) (Zb_ne_tripod d N T n),
    fun n => hC (N.Zc n) (by rw [N.Zca n]; exact h7 n) (Zc_ne_tripod d N T n)⟩

/-- The landing points of the three arm pairs are pairwise distinct (the `inj` content of
`PolyAdmissible`), from the arm memberships and the disjointness of the arms. -/
theorem cut_ne_of (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    (∀ n : ℕ, (N.Za n).y ≠ (N.Zb n).y) ∧ (∀ n : ℕ, (N.Zb n).y ≠ (N.Zc n).y) ∧
      (∀ n : ℕ, (N.Zc n).y ≠ (N.Za n).y) := by
  obtain ⟨hA, hB, hC⟩ := cut_mem_of d N T
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact (tripod_cut_ne d.hN Work.TopJordan.jordanForm T (yA := (N.Za n).y)
      (yB := (N.Zb n).y) (yC := (N.Zc n).y) (hA n) (hB n) (hC n)).1
  · exact (tripod_cut_ne d.hN Work.TopJordan.jordanForm T (yA := (N.Za n).y)
      (yB := (N.Zb n).y) (yC := (N.Zc n).y) (hA n) (hB n) (hC n)).2.1
  · exact (tripod_cut_ne d.hN Work.TopJordan.jordanForm T (yA := (N.Za n).y)
      (yB := (N.Zb n).y) (yC := (N.Zc n).y) (hA n) (hB n) (hC n)).2.2

/-- **The three-pair lists are admissible**, from the derived cut memberships. -/
theorem D_adm_of' (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN) :
    ∀ n : ℕ, Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n] := by
  obtain ⟨hAB, hBC, hCA⟩ := cut_ne_of d N T
  exact fun n => D_adm_of d N hAB hBC hCA n

/-- The non-degeneracy of the three arm pairs at every level. -/
theorem arm_arcLen_ne (d : Work.EL.RootParabolic c) (N : NestPairs d) :
    (∀ n : ℕ, Work.EL.arcLen (N.Za n).a (N.Za n).b ≠ 0) ∧
    (∀ n : ℕ, Work.EL.arcLen (N.Zb n).a (N.Zb n).b ≠ 0) ∧
    (∀ n : ℕ, Work.EL.arcLen (N.Zc n).a (N.Zc n).b ≠ 0) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [N.Zaa n, N.Zab n]; exact (armChainInputs_of d).2.1 n
  · rw [N.Zba n, N.Zbb n]; exact (armChainInputs_of d).2.2.1 n
  · rw [N.Zca n, N.Zcb n,
      show Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1)
          = Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n) from by
        unfold Work.EL.arcLen
        rw [show Work.ELNest.armC2 n + 1 - Work.ELNest.armC1 n
            = (Work.ELNest.armC2 n - Work.ELNest.armC1 n) + (1 : ℤ) by push_cast; ring,
          Int.fract_add_intCast]]
    exact (armChainInputs_of d).2.2.2 n

/-- **`b₂` lies in every level of the nest at `b₂`** (the field `CertGeometry.b2_mem_D`,
derived): the tripod rays of angles `22/63`, `25/63`, `37/63` lie in the near arcs of the three
arm pairs, so their common landing point lies in the closure of each near side, and it is not on
any of the three pair curves. -/
theorem b2_mem_D_of (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN)
    {L : ℝ} (hL : 1 < L) :
    ∀ n : ℕ, T.y ∈ Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10, h11, -, -, -⟩ := armAngle_facts
  obtain ⟨-, -, -, hnear⟩ := tripod_mem d.hN Work.TopJordan.jordanForm T
  have hadm := D_adm_of' d N T
  obtain ⟨hndA, hndB, hndC⟩ := arm_arcLen_ne d N
  intro n
  rw [Dmem_of d N hL hadm hndA hndB hndC n]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hnear (22 / 63) (N.Za n) T.lands₁ (by rw [N.Zab n, N.Zaa n]; exact h9 n)
      (Za_ne_tripod d N T n)
  · exact hnear (25 / 63) (N.Zb n) T.lands₂ (by rw [N.Zbb n, N.Zba n]; exact h10 n)
      (Zb_ne_tripod d N T n)
  · exact hnear (37 / 63) (N.Zc n) T.lands₃ (by rw [N.Zcb n, N.Zca n]; exact h11 n)
      (Zc_ne_tripod d N T n)
  · have hp : Work.EL.pot d.hN T.y = 0 :=
      Work.EL.pot_of_mem d.hN (Work.ELTop.landsN_mem_K d.hN T.lands₁)
    show Work.EL.pot d.hN T.y < Real.log (Work.ELNest.Dlev L n)
    rw [hp]
    exact Real.log_pos (by rw [Work.ELNest.Dlev]; exact Real.one_lt_rpow hL (by positivity))

/-! ## The nest at `b₂` decreases -/

/-- The two `b₂`-angles of the middle arm are ordered: `armB1 n < armB2 n`. -/
theorem armB1_lt_armB2 (n : ℕ) : Work.ELNest.armB1 n < Work.ELNest.armB2 n := by
  rw [Work.ELNest.armB1_closed n, Work.ELNest.armB2_closed n]
  have hy : (0 : ℝ) < ((64 : ℝ) ^ n)⁻¹ := by positivity
  have hy1 : ((64 : ℝ) ^ n)⁻¹ ≤ 1 := inv_pow_64_le_one n
  nlinarith [hy, hy1]

/-- Two angles `x < y` in `(0,1)` are incongruent modulo `1`, in both directions. -/
theorem ne_add_int_of_lt' {x y : ℝ} (hx : 0 < x) (hy : y < 1) (hxy : x < y) :
    (∀ k : ℤ, y ≠ x + k) ∧ (∀ k : ℤ, x ≠ y + k) :=
  ne_add_int_of_sub (by linarith) (by linarith)

/-- The `b₂`-nest landing points of consecutive levels differ (arm `A`). -/
theorem Za_succ_y_ne (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    (N.Za (n + 1)).y ≠ (N.Za n).y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Za (m + 1)).y) = (N.Za m).y :=
    (armY_shift d N).1
  intro h
  have hfix : ((Tantibar c)^[6]) ((N.Za n).y) = (N.Za n).y := by rw [← h, hsh n, h]
  have hz : (N.Za 0).y = (N.Za n).y :=
    descent_of_fixed (Z := fun k => (N.Za k).y) hsh hfix rfl
  have hz1 : (N.Za n).y = d.z₁ := by rw [← Za_y_base d N]; exact hz.symm
  exact not_fixed_T6_of d 0 (by norm_num) (by rw [← hz1]; exact hfix)

/-- The `b₂`-nest landing points of consecutive levels differ (arm `B`). -/
theorem Zb_succ_y_ne (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    (N.Zb (n + 1)).y ≠ (N.Zb n).y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Zb (m + 1)).y) = (N.Zb m).y :=
    (armY_shift d N).2.1
  intro h
  have hfix : ((Tantibar c)^[6]) ((N.Zb n).y) = (N.Zb n).y := by rw [← h, hsh n, h]
  have hz : (N.Zb 0).y = (N.Zb n).y :=
    descent_of_fixed (Z := fun k => (N.Zb k).y) hsh hfix rfl
  have hz1 : (N.Zb n).y = ((Tantibar c)^[2]) d.z₁ := by rw [← Zb_y_base d N]; exact hz.symm
  exact not_fixed_T6_of d 2 (by norm_num) (by rw [← hz1]; exact hfix)

/-- The `b₂`-nest landing points of consecutive levels differ (arm `C`). -/
theorem Zc_succ_y_ne (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    (N.Zc (n + 1)).y ≠ (N.Zc n).y := by
  have hsh : ∀ m : ℕ, ((Tantibar c)^[6]) ((N.Zc (m + 1)).y) = (N.Zc m).y :=
    (armY_shift d N).2.2
  intro h
  have hfix : ((Tantibar c)^[6]) ((N.Zc n).y) = (N.Zc n).y := by rw [← h, hsh n, h]
  have hz : (N.Zc 0).y = (N.Zc n).y :=
    descent_of_fixed (Z := fun k => (N.Zc k).y) hsh hfix rfl
  have hz1 : (N.Zc n).y = ((Tantibar c)^[4]) d.z₁ := by rw [← Zc_y_base d N]; exact hz.symm
  exact not_fixed_T6_of d 4 (by norm_num) (by rw [← hz1]; exact hfix)

/-- The consecutive pair curves of the arm-`A` nest are disjoint. -/
theorem Za_succ_curve_disjoint (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Disjoint (Work.EL.pairCurve (N.Za (n + 1))) (Work.EL.pairCurve (N.Za n)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := armAngle_order
  have hα1 : Work.EL.alpha1 < 1 := by norm_num [Work.EL.alpha1]
  have hα2 : (0 : ℝ) < Work.EL.alpha2 := by norm_num [Work.EL.alpha2]
  have p1 : 0 < Work.ELNest.armA1 n := lt_of_lt_of_le (by norm_num) (h3 n)
  have p1' : 0 < Work.ELNest.armA1 (n + 1) := lt_of_lt_of_le (by norm_num) (h3 (n + 1))
  have q1 : Work.ELNest.armA1 n < 1 := lt_of_le_of_lt (h2 n) hα1
  have q1' : Work.ELNest.armA1 (n + 1) < 1 := lt_of_le_of_lt (h2 (n + 1)) hα1
  have p2 : 0 < Work.ELNest.armA2 n := lt_of_lt_of_le hα2 (h5 n)
  have q2 : Work.ELNest.armA2 n < 1 := lt_of_lt_of_le (h6 n) (by norm_num)
  have q2' : Work.ELNest.armA2 (n + 1) < 1 := lt_of_lt_of_le (h6 (n + 1)) (by norm_num)
  have c12 : Work.ELNest.armA1 (n + 1) < Work.ELNest.armA2 n :=
    lt_of_le_of_lt (h2 (n + 1))
      (lt_of_lt_of_le (Work.ELNest.alpha1_lt_alpha2) (h5 n))
  have c21 : Work.ELNest.armA1 n < Work.ELNest.armA2 (n + 1) :=
    lt_of_le_of_lt (h2 n) (lt_of_lt_of_le (Work.ELNest.alpha1_lt_alpha2) (h5 (n + 1)))
  have d1 : (0 : ℝ) < Work.ELNest.armA1 n - Work.ELNest.armA1 (n + 1) := by linarith [h1 n]
  have e1 : Work.ELNest.armA1 n - Work.ELNest.armA1 (n + 1) < 1 := by linarith [p1', q1]
  have d2 : (0 : ℝ) < Work.ELNest.armA2 n - Work.ELNest.armA1 (n + 1) := by linarith [c12]
  have e2 : Work.ELNest.armA2 n - Work.ELNest.armA1 (n + 1) < 1 := by linarith [p1', q2]
  have d3 : (0 : ℝ) < Work.ELNest.armA2 (n + 1) - Work.ELNest.armA1 n := by linarith [c21]
  have e3 : Work.ELNest.armA2 (n + 1) - Work.ELNest.armA1 n < 1 := by linarith [p1, q2']
  have d4 : (0 : ℝ) < Work.ELNest.armA2 (n + 1) - Work.ELNest.armA2 n := by linarith [h4 n]
  have e4 : Work.ELNest.armA2 (n + 1) - Work.ELNest.armA2 n < 1 := by linarith [p2, q2']
  refine pairCurve_disjoint_of d.hN (N.Za (n + 1)) (N.Za n) ?_ ?_ ?_ ?_ (Za_succ_y_ne d N n)
  · intro k
    rw [N.Zaa n, N.Zaa (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armA1 (n + 1)) (y := Work.ELNest.armA1 n)
      d1 e1).1 k
  · intro k
    rw [N.Zab n, N.Zaa (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armA1 (n + 1)) (y := Work.ELNest.armA2 n)
      d2 e2).1 k
  · intro k
    rw [N.Zaa n, N.Zab (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armA1 n) (y := Work.ELNest.armA2 (n + 1))
      d3 e3).2 k
  · intro k
    rw [N.Zab n, N.Zab (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armA2 n) (y := Work.ELNest.armA2 (n + 1))
      d4 e4).2 k

/-- The consecutive pair curves of the arm-`B` nest are disjoint. -/
theorem Zb_succ_curve_disjoint (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Disjoint (Work.EL.pairCurve (N.Zb (n + 1))) (Work.EL.pairCurve (N.Zb n)) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, h12, -⟩ := armAngle_order
  have p1 : 0 < Work.ELNest.armB1 n := lt_trans (by norm_num) (h8 n)
  have p1' : 0 < Work.ELNest.armB1 (n + 1) := lt_trans (by norm_num) (h8 (n + 1))
  have q1 : Work.ELNest.armB1 n < 1 := lt_of_lt_of_le (h9 n) (by norm_num)
  have p2 : 0 < Work.ELNest.armB2 n := lt_trans (by norm_num) (h11 n)
  have p2' : 0 < Work.ELNest.armB2 (n + 1) := lt_trans (by norm_num) (h11 (n + 1))
  have q2 : Work.ELNest.armB2 n < 1 := lt_of_lt_of_le (h12 n) (by norm_num)
  have q2' : Work.ELNest.armB2 (n + 1) < 1 := lt_of_lt_of_le (h12 (n + 1)) (by norm_num)
  have c12 : Work.ELNest.armB1 (n + 1) < Work.ELNest.armB2 n :=
    lt_trans (h7 n) (armB1_lt_armB2 n)
  have c21 : Work.ELNest.armB1 n < Work.ELNest.armB2 (n + 1) :=
    lt_trans (armB1_lt_armB2 n) (h10 n)
  have d1 : (0 : ℝ) < Work.ELNest.armB1 n - Work.ELNest.armB1 (n + 1) := by linarith [h7 n]
  have e1 : Work.ELNest.armB1 n - Work.ELNest.armB1 (n + 1) < 1 := by linarith [p1', q1]
  have d2 : (0 : ℝ) < Work.ELNest.armB2 n - Work.ELNest.armB1 (n + 1) := by linarith [c12]
  have e2 : Work.ELNest.armB2 n - Work.ELNest.armB1 (n + 1) < 1 := by linarith [p1', q2]
  have d3 : (0 : ℝ) < Work.ELNest.armB2 (n + 1) - Work.ELNest.armB1 n := by linarith [c21]
  have e3 : Work.ELNest.armB2 (n + 1) - Work.ELNest.armB1 n < 1 := by linarith [p1, q2']
  have d4 : (0 : ℝ) < Work.ELNest.armB2 (n + 1) - Work.ELNest.armB2 n := by linarith [h10 n]
  have e4 : Work.ELNest.armB2 (n + 1) - Work.ELNest.armB2 n < 1 := by linarith [p2, q2']
  refine pairCurve_disjoint_of d.hN (N.Zb (n + 1)) (N.Zb n) ?_ ?_ ?_ ?_ (Zb_succ_y_ne d N n)
  · intro k
    rw [N.Zba n, N.Zba (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armB1 (n + 1)) (y := Work.ELNest.armB1 n)
      d1 e1).1 k
  · intro k
    rw [N.Zbb n, N.Zba (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armB1 (n + 1)) (y := Work.ELNest.armB2 n)
      d2 e2).1 k
  · intro k
    rw [N.Zba n, N.Zbb (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armB1 n) (y := Work.ELNest.armB2 (n + 1))
      d3 e3).2 k
  · intro k
    rw [N.Zbb n, N.Zbb (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armB2 n) (y := Work.ELNest.armB2 (n + 1))
      d4 e4).2 k

/-- The consecutive pair curves of the arm-`C` nest are disjoint. -/
theorem Zc_succ_curve_disjoint (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Disjoint (Work.EL.pairCurve (N.Zc (n + 1))) (Work.EL.pairCurve (N.Zc n)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, h15, h16, h17, h18⟩ := armAngle_order
  have q1 : Work.ELNest.armC1 n < 1 := h15 n
  have q1' : Work.ELNest.armC1 (n + 1) < 1 := h15 (n + 1)
  have c1 : (0 : ℝ) < Work.ELNest.armC1 (n + 1) := lt_trans (by norm_num) (h14 (n + 1))
  have e1 : (0 : ℝ) < Work.ELNest.armC2 n + 1 := by linarith [h17 n]
  have e1' : (0 : ℝ) < Work.ELNest.armC2 (n + 1) + 1 := by linarith [h17 (n + 1)]
  have d1 : (0 : ℝ) < Work.ELNest.armC1 n - Work.ELNest.armC1 (n + 1) := by linarith [h13 n]
  have e1 : Work.ELNest.armC1 n - Work.ELNest.armC1 (n + 1) < 1 := by linarith [c1, q1]
  have d2 : (0 : ℝ) < Work.ELNest.armC2 n + 1 - Work.ELNest.armC1 (n + 1) := by
    linarith [q1', h17 n]
  have e2 : Work.ELNest.armC2 n + 1 - Work.ELNest.armC1 (n + 1) < 1 := by
    linarith [h18 n, h14 (n + 1)]
  have d3 : (0 : ℝ) < Work.ELNest.armC2 (n + 1) + 1 - Work.ELNest.armC1 n := by
    linarith [q1, h17 (n + 1)]
  have e3 : Work.ELNest.armC2 (n + 1) + 1 - Work.ELNest.armC1 n < 1 := by
    linarith [h18 (n + 1), h14 n]
  have d4 : (0 : ℝ) < Work.ELNest.armC2 (n + 1) + 1 - (Work.ELNest.armC2 n + 1) := by
    linarith [h16 n]
  have e4 : Work.ELNest.armC2 (n + 1) + 1 - (Work.ELNest.armC2 n + 1) < 1 := by
    linarith [h18 (n + 1), h17 n]
  refine pairCurve_disjoint_of d.hN (N.Zc (n + 1)) (N.Zc n) ?_ ?_ ?_ ?_ (Zc_succ_y_ne d N n)
  · intro k
    rw [N.Zca n, N.Zca (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armC1 (n + 1)) (y := Work.ELNest.armC1 n)
      d1 e1).1 k
  · intro k
    rw [N.Zcb n, N.Zca (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armC1 (n + 1))
      (y := Work.ELNest.armC2 n + 1) d2 e2).1 k
  · intro k
    rw [N.Zca n, N.Zcb (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armC1 n)
      (y := Work.ELNest.armC2 (n + 1) + 1) d3 e3).2 k
  · intro k
    rw [N.Zcb n, N.Zcb (n + 1)]
    exact (ne_add_int_of_sub (x := Work.ELNest.armC2 n + 1)
      (y := Work.ELNest.armC2 (n + 1) + 1) d4 e4).2 k

/-- **The nest at `b₂` is decreasing** (the field `CertGeometry.Dnest_sub`, derived). -/
theorem Dnest_sub_of' (d : Work.EL.RootParabolic c) (N : NestPairs d) (T : Work.EL.Tripod d.hN)
    {L : ℝ} (hL : 1 < L) :
    ∀ n : ℕ, Work.EL.polyRegion [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)]
        (Work.ELNest.Dlev L (n + 1))
      ⊆ Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13, h14⟩ := armAngle_facts
  have hadm := D_adm_of' d N T
  obtain ⟨hndA, hndB, hndC⟩ := arm_arcLen_ne d N
  have hD : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)
      = Work.EL.pairSideNear (N.Za n) ∩ Work.EL.pairSideNear (N.Zb n)
        ∩ Work.EL.pairSideNear (N.Zc n)
        ∩ {z : ℂ | Work.EL.pot d.hN z < Real.log (Work.ELNest.Dlev L n)} :=
    fun n => Dmem_of d N hL hadm hndA hndB hndC n
  have hsideA : ∀ n : ℕ, Work.EL.pairSideNear (N.Za (n + 1)) ⊆ Work.EL.pairSideNear (N.Za n) :=
    fun n => nest_side_of_nearArc d.hN Work.TopJordan.jordanForm (N.Za (n + 1)) (N.Za n)
      (fun θ hθ => by
        rw [N.Zab (n + 1), N.Zaa (n + 1)] at hθ
        rw [N.Zab n, N.Zaa n]
        exact h12 n θ hθ)
      (Za_succ_curve_disjoint d N n)
  have hsideB : ∀ n : ℕ, Work.EL.pairSideNear (N.Zb (n + 1)) ⊆ Work.EL.pairSideNear (N.Zb n) :=
    fun n => nest_side_of_nearArc d.hN Work.TopJordan.jordanForm (N.Zb (n + 1)) (N.Zb n)
      (fun θ hθ => by
        rw [N.Zbb (n + 1), N.Zba (n + 1)] at hθ
        rw [N.Zbb n, N.Zba n]
        exact h13 n θ hθ)
      (Zb_succ_curve_disjoint d N n)
  have hsideC : ∀ n : ℕ, Work.EL.pairSideNear (N.Zc (n + 1)) ⊆ Work.EL.pairSideNear (N.Zc n) :=
    fun n => nest_side_of_nearArc d.hN Work.TopJordan.jordanForm (N.Zc (n + 1)) (N.Zc n)
      (fun θ hθ => by
        rw [N.Zcb (n + 1), N.Zca (n + 1)] at hθ
        rw [N.Zcb n, N.Zca n]
        exact h14 n θ hθ)
      (Zc_succ_curve_disjoint d N n)
  exact fun n => Dnest_sub_of d N hL hD hsideA hsideB hsideC n

end Work.ELAssembly
