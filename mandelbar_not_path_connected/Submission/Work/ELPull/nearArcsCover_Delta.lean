/-
# `nearArcsCover_Delta`: the `NearArcsCover` instance of the level-1 region `Δ̂₁`

The angle map `θ ↦ 4³ θ mod 1` of `(Tsq c)^[3]` carries

* the level-1 arm pairs `Cert.levelPair1 Z` onto the level-0 arm pairs `Cert.farArc Z`
  (certificate C9, `Cert.angMul_levelPair1_*`), and
* the near arcs `Cert.delta1Near Z` of `Δ̂₁` onto the near arcs `Cert.delta0Near Z` of `Δ̂₀`
  (the `×64` scaling `Cert.delta1Near_scaling`).

Consequently `[Q' 0, Q' 1, Q' 2]` is a `NearArcsCover` of `[Q 0, Q 1, Q 2]` for `m = 3`, as soon
as the pairs `Q Z` and `Q' Z` carry the certificate angles (`Cert.farArc Z`, `Cert.levelPair1 Z`).
This is the `NearArcsCover` input of `polyPullback` for the arm region `Δ̂₁`.

The proof is pure angle arithmetic: `NearArcsCover` only sees the angles `.a`, `.b` of the pairs,
so the landing points and the `LandsN` fields of `Q`, `Q'` are irrelevant.
-/
import Mathlib
import Submission.Work.ELPull.Cert.Checks
import Submission.Work.ELPull.polyPullback

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

/-! ## 1. General angle lemmas -/

/-- `angMul 3` is `θ ↦ 64 θ mod 1`. -/
private lemma angMul_three (θ : ℝ) : angMul 3 θ = Int.fract (64 * θ) := by
  rw [angMul]; norm_num

/-- `Int.fract` of a rational in `[0,1)` is the rational itself. -/
private lemma fract_ratCast_of_mem {q : ℚ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Int.fract ((q : ℝ)) = (q : ℝ) := by
  rw [Int.fract_eq_self]
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

/-- **Scaling of arcs under `angMul 3`.**  If `x` lies in the counterclockwise arc `(a,b)` of
length `b - a ∈ [0,1)`, and the arc `(a,b)` is taken by `64 ·` onto the arc `(A,B)` (up to the
integer shift `k` on the endpoints and with the length scaled by `64`), then `angMul 3 x` lies in
`(A,B)`. -/
private lemma InArc_angMul64_scaled {x a b A B : ℝ} (k : ℤ)
    (hx : InArc x a b) (ha : 64 * a = A + k)
    (hl : 0 ≤ b - a) (hl1 : b - a < 1)
    (hBA : B - A = 64 * (b - a)) (hBA1 : B - A < 1) :
    InArc (angMul 3 x) A B := by
  have hx2 : Int.fract (x - a) < b - a := by
    have := hx.2
    rwa [arcLen, Int.fract_eq_self.mpr ⟨hl, hl1⟩] at this
  have hsplit : x = a + ⌊x - a⌋ + Int.fract (x - a) := by
    have := Int.floor_add_fract (x - a); linarith
  have hkey : Int.fract (64 * x - A) = 64 * Int.fract (x - a) := by
    refine Int.fract_eq_iff.mpr ⟨by linarith [hx.1], by linarith, ⟨k + 64 * ⌊x - a⌋, ?_⟩⟩
    push_cast
    linarith
  have hfr' : Int.fract (Int.fract (64 * x) - A) = Int.fract (64 * x - A) := by
    rw [Int.fract_eq_fract]
    refine ⟨-⌊64 * x⌋, ?_⟩
    have hh := Int.self_sub_fract (64 * x)
    push_cast
    linarith
  have hfr : Int.fract (angMul 3 x - A) = 64 * Int.fract (x - a) := by
    rw [show angMul 3 x = Int.fract (64 * x) from angMul_three x, hfr', hkey]
  have hBA0 : 0 ≤ B - A := by rw [hBA]; positivity
  refine ⟨?_, ?_⟩
  · rw [hfr]; linarith [hx.1]
  · rw [hfr, arcLen, Int.fract_eq_self.mpr ⟨hBA0, hBA1⟩, hBA]; linarith

/-! ## 2. The certificate values of the near arcs

`nearArc` unwraps the upper endpoint with `ccwLift`; these are the six evaluations of `ccwLift`
that turn the near arcs of the two polygons into the certificate arcs `Cert.delta1Near` (level 1)
and `Cert.delta0Near` (level 0). -/

private lemma ccwLift_lp_0 :
    ccwLift ((Cert.levelPair1 0).2 : ℝ) ((Cert.levelPair1 1).1 : ℝ)
      = ((Cert.levelPair1 1).1 : ℝ) := by
  simp only [Cert.levelPair1_val_0, Cert.levelPair1_val_1, qq, ccwLift]
  push_cast
  norm_num

private lemma ccwLift_lp_1 :
    ccwLift ((Cert.levelPair1 1).2 : ℝ) ((Cert.levelPair1 2).1 : ℝ)
      = ((Cert.levelPair1 2).1 : ℝ) := by
  simp only [Cert.levelPair1_val_1, Cert.levelPair1_val_2, qq, ccwLift]
  push_cast
  norm_num

private lemma ccwLift_lp_2 :
    ccwLift ((Cert.levelPair1 2).2 : ℝ) ((Cert.levelPair1 0).1 : ℝ)
      = ((Cert.levelPair1 0).1 : ℝ) + 1 := by
  simp only [Cert.levelPair1_val_0, Cert.levelPair1_val_2, qq, ccwLift]
  push_cast
  norm_num

private lemma ccwLift_fa_0 :
    ccwLift ((Cert.farArc 0).2 : ℝ) ((Cert.farArc 1).1 : ℝ)
      = ((Cert.farArc 1).1 : ℝ) := by
  simp only [Cert.farArc_val_0, Cert.farArc_val_1, qq, ccwLift]
  push_cast
  norm_num

private lemma ccwLift_fa_1 :
    ccwLift ((Cert.farArc 1).2 : ℝ) ((Cert.farArc 2).1 : ℝ)
      = ((Cert.farArc 2).1 : ℝ) := by
  simp only [Cert.farArc_val_1, Cert.farArc_val_2, qq, ccwLift]
  push_cast
  norm_num

private lemma ccwLift_fa_2 :
    ccwLift ((Cert.farArc 2).2 : ℝ) ((Cert.farArc 0).1 : ℝ)
      = ((Cert.farArc 0).1 : ℝ) + 1 := by
  simp only [Cert.farArc_val_0, Cert.farArc_val_2, qq, ccwLift]
  push_cast
  norm_num

/-- The far arc of the arm `C` is unwrapped past `1`: `Int.fract (1349/1023) = 326/1023`. -/
private lemma fract_farArc_2_2 :
    Int.fract ((Cert.farArc 2).2 : ℝ) = ((Cert.farArc 2).2 : ℝ) - 1 := by
  rw [Int.fract_eq_iff]
  refine ⟨by norm_num, by norm_num, ⟨1, ?_⟩⟩
  push_cast
  norm_num

/-! ## 3. The three scaled near-arc inclusions `Δ̂₁ → Δ̂₀` -/

private lemma arc_delta_0 {x : ℝ}
    (hx : InArc x ((Cert.levelPair1 0).2 : ℝ) ((Cert.levelPair1 1).1 : ℝ)) :
    InArc (angMul 3 x) ((Cert.farArc 0).2 : ℝ) ((Cert.farArc 1).1 : ℝ) := by
  refine InArc_angMul64_scaled (k := 25) hx ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Cert.levelPair1_val_0, Cert.levelPair1_val_1, Cert.farArc_val_0,
      Cert.farArc_val_1, qq] <;>
    push_cast <;> norm_num

private lemma arc_delta_1 {x : ℝ}
    (hx : InArc x ((Cert.levelPair1 1).2 : ℝ) ((Cert.levelPair1 2).1 : ℝ)) :
    InArc (angMul 3 x) ((Cert.farArc 1).2 : ℝ) ((Cert.farArc 2).1 : ℝ) := by
  refine InArc_angMul64_scaled (k := 37) hx ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Cert.levelPair1_val_1, Cert.levelPair1_val_2, Cert.farArc_val_1,
      Cert.farArc_val_2, qq] <;>
    push_cast <;> norm_num

private lemma arc_delta_2 {x : ℝ}
    (hx : InArc x ((Cert.levelPair1 2).2 : ℝ) (((Cert.levelPair1 0).1 : ℝ) + 1)) :
    InArc (angMul 3 x) ((Cert.farArc 2).2 : ℝ) (((Cert.farArc 0).1 : ℝ) + 1) := by
  refine InArc_angMul64_scaled (k := 85) hx ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Cert.levelPair1_val_0, Cert.levelPair1_val_2, Cert.farArc_val_0,
      Cert.farArc_val_2, qq] <;>
    push_cast <;> norm_num

/-! ## 4. The `NearArcsCover` instance -/

theorem nearArcsCover_Delta {c : ℂ} (hN : DynB c) (Q Q' : Fin 3 → CoPair hN)
    (hQ : ∀ Z : Fin 3, (Q Z).a = (Cert.farArc Z).1 ∧ (Q Z).b = (Cert.farArc Z).2)
    (hQ' : ∀ Z : Fin 3, (Q' Z).a = (Cert.levelPair1 Z).1 ∧ (Q' Z).b = (Cert.levelPair1 Z).2) :
    NearArcsCover hN [Q 0, Q 1, Q 2] [Q' 0, Q' 1, Q' 2] 3 := by
  refine ⟨?_, ?_⟩
  · -- the boundary pairs: `Cert.angMul_levelPair1_*` (C9)
    intro P' hP'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP'
    rcases hP' with rfl | rfl | rfl
    · refine ⟨Q 0, by simp, ?_, ?_⟩
      · rw [(hQ' 0).1, (hQ 0).1, Cert.angMul_levelPair1_0_0]
        exact (fract_ratCast_of_mem (q := (Cert.farArc 0).1) (by norm_num) (by norm_num)).symm
      · rw [(hQ' 0).2, (hQ 0).2, Cert.angMul_levelPair1_0_1]
        exact (fract_ratCast_of_mem (q := (Cert.farArc 0).2) (by norm_num) (by norm_num)).symm
    · refine ⟨Q 1, by simp, ?_, ?_⟩
      · rw [(hQ' 1).1, (hQ 1).1, Cert.angMul_levelPair1_1_0]
        exact (fract_ratCast_of_mem (q := (Cert.farArc 1).1) (by norm_num) (by norm_num)).symm
      · rw [(hQ' 1).2, (hQ 1).2, Cert.angMul_levelPair1_1_1]
        exact (fract_ratCast_of_mem (q := (Cert.farArc 1).2) (by norm_num) (by norm_num)).symm
    · refine ⟨Q 2, by simp, ?_, ?_⟩
      · rw [(hQ' 2).1, (hQ 2).1, Cert.angMul_levelPair1_2_0]
        exact (fract_ratCast_of_mem (q := (Cert.farArc 2).1) (by norm_num) (by norm_num)).symm
      · rw [(hQ' 2).2, (hQ 2).2, Cert.angMul_levelPair1_2_1]
        exact fract_farArc_2_2.symm
  · -- the near arcs: `Cert.delta1Near_scaling` (C4), one arc onto the corresponding arc
    intro i
    fin_cases i
    · refine ⟨(0 : Fin 3), fun x hx => ?_⟩
      simp [nearArc, nextIdx] at hx
      rw [(hQ' 0).2, (hQ' 1).1, ccwLift_lp_0] at hx
      simp [nearArc, nextIdx]
      rw [(hQ 0).2, (hQ 1).1, ccwLift_fa_0]
      exact arc_delta_0 hx
    · refine ⟨(1 : Fin 3), fun x hx => ?_⟩
      simp [nearArc, nextIdx] at hx
      rw [(hQ' 1).2, (hQ' 2).1, ccwLift_lp_1] at hx
      simp [nearArc, nextIdx]
      rw [(hQ 1).2, (hQ 2).1, ccwLift_fa_1]
      exact arc_delta_1 hx
    · refine ⟨(2 : Fin 3), fun x hx => ?_⟩
      simp [nearArc, nextIdx] at hx
      rw [(hQ' 2).2, (hQ' 0).1, ccwLift_lp_2] at hx
      simp [nearArc, nextIdx]
      rw [(hQ 2).2, (hQ 0).1, ccwLift_fa_2]
      exact arc_delta_2 hx

end Work.ELPull
