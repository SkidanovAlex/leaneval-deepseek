import Mathlib
import Submission.Work.ELAssembly.PbAvoid_cycle
import Submission.Work.ELTop.pairSide_subset_pairSide
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELNest.Nest_coLand
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qp_shift
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The arithmetic of the wake angles

For `j < 5` the two ends of the wake arc `W_j = (wakeLo j, wakeHi j)` are the two portrait angles
`T^j α₁`, `T^j α₂` of the `j`-th cycle point, up to integer translation.  We only need the
consequence on `Int.fract`: the fractional part of either end of `W_j` is one of the two portrait
angles `T^j αᵢ`. -/

/-- `Int.fract (wakeLo j)` is one of `T^j α₁`, `T^j α₂`. -/
private lemma fract_wakeLo (j : ℕ) (hj : j < 5) :
    Int.fract (Work.EL.wakeLo j) = Work.EL.T^[j] Work.EL.alpha1 ∨
      Int.fract (Work.EL.wakeLo j) = Work.EL.T^[j] Work.EL.alpha2 := by
  interval_cases j <;>
    (try (left; norm_num [Work.EL.wakeLo, Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]; done)) <;>
    (try (right; norm_num [Work.EL.wakeLo, Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]; done))

/-- `Int.fract (wakeHi j)` is one of `T^j α₁`, `T^j α₂`. -/
private lemma fract_wakeHi (j : ℕ) (hj : j < 5) :
    Int.fract (Work.EL.wakeHi j) = Work.EL.T^[j] Work.EL.alpha1 ∨
      Int.fract (Work.EL.wakeHi j) = Work.EL.T^[j] Work.EL.alpha2 := by
  interval_cases j <;>
    (try (left; norm_num [Work.EL.wakeHi, Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]; done)) <;>
    (try (right; norm_num [Work.EL.wakeHi, Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]; done))

/-- An angle whose fractional part avoids both portrait angles `T^j αᵢ` is not congruent to
`wakeLo j` modulo `1`. -/
private lemma ne_add_int_of_fract_wakeLo {j : ℕ} (hj : j < 5) {θ : ℝ}
    (h1 : Int.fract θ ≠ Work.EL.T^[j] Work.EL.alpha1)
    (h2 : Int.fract θ ≠ Work.EL.T^[j] Work.EL.alpha2) :
    ∀ k : ℤ, θ ≠ Work.EL.wakeLo j + k := by
  intro k hk
  have hf : Int.fract θ = Int.fract (Work.EL.wakeLo j) := by
    rw [hk, Int.fract_add_intCast]
  rcases fract_wakeLo j hj with h | h
  · exact h1 (hf.trans h)
  · exact h2 (hf.trans h)

/-- An angle whose fractional part avoids both portrait angles `T^j αᵢ` is not congruent to
`wakeHi j` modulo `1`. -/
private lemma ne_add_int_of_fract_wakeHi {j : ℕ} (hj : j < 5) {θ : ℝ}
    (h1 : Int.fract θ ≠ Work.EL.T^[j] Work.EL.alpha1)
    (h2 : Int.fract θ ≠ Work.EL.T^[j] Work.EL.alpha2) :
    ∀ k : ℤ, θ ≠ Work.EL.wakeHi j + k := by
  intro k hk
  have hf : Int.fract θ = Int.fract (Work.EL.wakeHi j) := by
    rw [hk, Int.fract_add_intCast]
  rcases fract_wakeHi j hj with h | h
  · exact h1 (hf.trans h)
  · exact h2 (hf.trans h)

/-- A ray which lands at `y` also lands at `y` when its angle is replaced by its fractional part:
`LandsN` only depends on the angle modulo `1`. -/
private lemma landsN_fract {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : Work.EL.LandsN hN (Int.fract θ) y := by
  have hfloor : θ = Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) := (Int.fract_add_floor θ).symm
  have h1 : Work.EL.LandsN hN (Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ)) y := hfloor ▸ h
  have h2 := Work.ELTop.LandsN_add_int hN h1 (-⌊θ⌋)
  have harg : Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) + ((((-⌊θ⌋) : ℤ)) : ℝ) = Int.fract θ := by
    push_cast
    ring
  rwa [harg] at h2

/-! ## The curve of the wake arc is the curve of the portrait pair

The two rays of the `j`-th portrait pair `P_j = alphaPairRaw c z₁ j` are those of angles
`min (T^j α₁) (T^j α₂)` and `max (T^j α₁) (T^j α₂)`; the two rays of the pair
`⟨wakeLo j, wakeHi j, ·⟩` are the same two *sets* (the difference is an integer translation for
`j = 3, 4`, and a swap for `j = 1`).  Since `RawPair.curve` is the union of the two rays and the
landing point, the two curves agree. -/

/-- The wake angles and the portrait angles define the same curve. -/
private lemma wake_curve_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ)
    (j : ℕ) (hj : j < 5) :
    Work.EL.RawPair.curve hN (Work.EL.alphaPairRaw c z₁ j) =
    Work.EL.RawPair.curve hN
      (⟨Work.EL.wakeLo j, Work.EL.wakeHi j, (Tantibar c)^[j] z₁⟩ : Work.EL.RawPair) := by
  interval_cases j
  · simp only [Work.EL.alphaPairRaw, Work.EL.RawPair.curve, Work.EL.wakeLo, Work.EL.wakeHi,
      Function.iterate_zero_apply, Work.EL.alpha1, Work.EL.alpha2]
    rw [min_eq_left (by norm_num : (371:ℝ)/1023 ≤ 404/1023),
      max_eq_right (by norm_num : (371:ℝ)/1023 ≤ 404/1023)]
  · simp only [Work.EL.alphaPairRaw, Work.EL.RawPair.curve, Work.EL.wakeLo, Work.EL.wakeHi]
    have hA : Work.EL.T^[1] Work.EL.alpha1 = 281/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have hB : Work.EL.T^[1] Work.EL.alpha2 = 215/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    rw [hA, hB, min_eq_right (by norm_num : (215:ℝ)/1023 ≤ 281/1023),
      max_eq_left (by norm_num : (215:ℝ)/1023 ≤ 281/1023)]
  · simp only [Work.EL.alphaPairRaw, Work.EL.RawPair.curve, Work.EL.wakeLo, Work.EL.wakeHi]
    have hA : Work.EL.T^[2] Work.EL.alpha1 = 461/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have hB : Work.EL.T^[2] Work.EL.alpha2 = 593/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    rw [hA, hB, min_eq_left (by norm_num : (461:ℝ)/1023 ≤ 593/1023),
      max_eq_right (by norm_num : (461:ℝ)/1023 ≤ 593/1023)]
  · simp only [Work.EL.alphaPairRaw, Work.EL.RawPair.curve, Work.EL.wakeLo, Work.EL.wakeHi]
    have hA : Work.EL.T^[3] Work.EL.alpha1 = 101/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have hB : Work.EL.T^[3] Work.EL.alpha2 = 860/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have h : Work.EL.paramRay hN (1124/1023) = Work.EL.paramRay hN (101/1023) := by
      have h' : (1124:ℝ)/1023 = 101/1023 + ((1:ℤ):ℝ) := by norm_num
      rw [h']
      exact Work.ELTop.paramRay_add_int hN (101/1023) 1
    rw [hA, hB, h, min_eq_left (by norm_num : (101:ℝ)/1023 ≤ 860/1023),
      max_eq_right (by norm_num : (101:ℝ)/1023 ≤ 860/1023)]
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  · simp only [Work.EL.alphaPairRaw, Work.EL.RawPair.curve, Work.EL.wakeLo, Work.EL.wakeHi]
    have hA : Work.EL.T^[4] Work.EL.alpha1 = 821/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have hB : Work.EL.T^[4] Work.EL.alpha2 = 326/1023 := by
      norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]
    have h : Work.EL.paramRay hN (1349/1023) = Work.EL.paramRay hN (326/1023) := by
      have h' : (1349:ℝ)/1023 = 326/1023 + ((1:ℤ):ℝ) := by norm_num
      rw [h']
      exact Work.ELTop.paramRay_add_int hN (326/1023) 1
    rw [hA, hB, h, min_eq_right (by norm_num : (326:ℝ)/1023 ≤ 821/1023),
      max_eq_left (by norm_num : (326:ℝ)/1023 ≤ 821/1023)]
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto

/-- The same statement with the explicit rational values of the wake angles of `j < 5`. -/
private lemma wake_curve_eq_target {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ)
    (j : ℕ) (hj : j < 5) (lo hi : ℝ) (hlo : lo = Work.EL.wakeLo j)
    (hhi : hi = Work.EL.wakeHi j) :
    Work.EL.RawPair.curve hN (Work.EL.alphaPairRaw c z₁ j) =
    Work.EL.RawPair.curve hN (⟨lo, hi, (Tantibar c)^[j] z₁⟩ : Work.EL.RawPair) := by
  rw [hlo, hhi]
  exact wake_curve_eq hN z₁ j hj

/-! ## The cycle pair of the wake arc -/

/-- **The wake arc is a co-landing pair.**  For `j < 5` there is a co-landing pair `wakeR` whose
angles are exactly `wakeLo j`, `wakeHi j` and whose landing point is the `j`-th cycle point
`(Tantibar c)^[j] z₁` (the angle identification `T^j αᵢ` of `PbAvoid_cycle`, with the integer
translation `+1` at `j = 3, 4` supplied by `LandsN_add_int`), and its far side is the wake side
`X_j`. -/
private lemma wakeSide_eq_pairSide_wakeR {c : ℂ} (d : Work.EL.RootParabolic c)
    (j : ℕ) (hj : j < 5) :
    ∃ wakeR : Work.EL.CoPair d.hN,
      wakeR.a = Work.EL.wakeLo j ∧ wakeR.b = Work.EL.wakeHi j ∧
      wakeR.y = (Tantibar c)^[j] d.z₁ ∧
      Work.EL.wakeSide d.hN d.z₁ j = Work.EL.pairSide wakeR := by
  have hland := (PbAvoid_cycle d).1
  interval_cases j
  · -- j = 0
    have hPa : Work.EL.LandsN d.hN (371/1023) d.z₁ := by
      simpa [Work.EL.alpha1] using (hland 0).1
    have hPb : Work.EL.LandsN d.hN (404/1023) d.z₁ := by
      simpa [Work.EL.alpha2] using (hland 0).2
    refine ⟨⟨⟨371/1023, 404/1023, d.z₁⟩, hPa, hPb⟩, rfl, rfl, rfl, ?_⟩
    have hc := wake_curve_eq_target d.hN d.z₁ 0 hj (371/1023) (404/1023) rfl rfl
    simp only [Work.EL.wakeSide, Work.EL.pairSide, Work.EL.pairSideThroughArc,
      Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
    rw [hc]
    rfl
  · -- j = 1
    have hPa : Work.EL.LandsN d.hN (215/1023) ((Tantibar c)^[1] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[1] Work.EL.alpha2 = 215/1023) ▸ (hland 1).2
    have hPb : Work.EL.LandsN d.hN (281/1023) ((Tantibar c)^[1] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[1] Work.EL.alpha1 = 281/1023) ▸ (hland 1).1
    refine ⟨⟨⟨215/1023, 281/1023, (Tantibar c)^[1] d.z₁⟩, hPa, hPb⟩, rfl, rfl, rfl, ?_⟩
    have hc := wake_curve_eq_target d.hN d.z₁ 1 hj (215/1023) (281/1023) rfl rfl
    simp only [Work.EL.wakeSide, Work.EL.pairSide, Work.EL.pairSideThroughArc,
      Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
    rw [hc]
    rfl
  · -- j = 2
    have hPa : Work.EL.LandsN d.hN (461/1023) ((Tantibar c)^[2] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[2] Work.EL.alpha1 = 461/1023) ▸ (hland 2).1
    have hPb : Work.EL.LandsN d.hN (593/1023) ((Tantibar c)^[2] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[2] Work.EL.alpha2 = 593/1023) ▸ (hland 2).2
    refine ⟨⟨⟨461/1023, 593/1023, (Tantibar c)^[2] d.z₁⟩, hPa, hPb⟩, rfl, rfl, rfl, ?_⟩
    have hc := wake_curve_eq_target d.hN d.z₁ 2 hj (461/1023) (593/1023) rfl rfl
    simp only [Work.EL.wakeSide, Work.EL.pairSide, Work.EL.pairSideThroughArc,
      Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
    rw [hc]
    rfl
  · -- j = 3
    have hPa : Work.EL.LandsN d.hN (860/1023) ((Tantibar c)^[3] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[3] Work.EL.alpha2 = 860/1023) ▸ (hland 3).2
    have hPb : Work.EL.LandsN d.hN (1124/1023) ((Tantibar c)^[3] d.z₁) := by
      have h := Work.ELTop.LandsN_add_int d.hN
        ((by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
          Work.EL.T^[3] Work.EL.alpha1 = 101/1023) ▸ (hland 3).1) (1:ℤ)
      have harg : (101:ℝ)/1023 + ((1:ℤ):ℝ) = 1124/1023 := by norm_num
      rwa [harg] at h
    refine ⟨⟨⟨860/1023, 1124/1023, (Tantibar c)^[3] d.z₁⟩, hPa, hPb⟩, rfl, rfl, rfl, ?_⟩
    have hc := wake_curve_eq_target d.hN d.z₁ 3 hj (860/1023) (1124/1023) rfl rfl
    simp only [Work.EL.wakeSide, Work.EL.pairSide, Work.EL.pairSideThroughArc,
      Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
    rw [hc]
    rfl
  · -- j = 4
    have hPa : Work.EL.LandsN d.hN (821/1023) ((Tantibar c)^[4] d.z₁) :=
      (by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
        Work.EL.T^[4] Work.EL.alpha1 = 821/1023) ▸ (hland 4).1
    have hPb : Work.EL.LandsN d.hN (1349/1023) ((Tantibar c)^[4] d.z₁) := by
      have h := Work.ELTop.LandsN_add_int d.hN
        ((by norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2] :
          Work.EL.T^[4] Work.EL.alpha2 = 326/1023) ▸ (hland 4).2) (1:ℤ)
      have harg : (326:ℝ)/1023 + ((1:ℤ):ℝ) = 1349/1023 := by norm_num
      rwa [harg] at h
    refine ⟨⟨⟨821/1023, 1349/1023, (Tantibar c)^[4] d.z₁⟩, hPa, hPb⟩, rfl, rfl, rfl, ?_⟩
    have hc := wake_curve_eq_target d.hN d.z₁ 4 hj (821/1023) (1349/1023) rfl rfl
    simp only [Work.EL.wakeSide, Work.EL.pairSide, Work.EL.pairSideThroughArc,
      Work.EL.RawPair.side, Work.EL.RawPair.sideThrough]
    rw [hc]
    rfl

/-! ## Disjointness of the curves -/

/-- **The curve of the wake pair is disjoint from the curve of a pair which shares no angle with
the portrait pair `P_j`.**  Rays against rays: the angles differ modulo `1` by the
non-degeneracy hypotheses.  Rays against points: a ray avoids `K c` while a landing point lies in
it.  Points against points: a common landing point would make `fract Q.a` a portrait angle of
`T^j z₁` by `hport`. -/
private lemma pairCurve_disjoint_wake {c : ℂ} (d : Work.EL.RootParabolic c) (j : ℕ) (hj : j < 5)
    (P Q : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.wakeLo j) (hPb : P.b = Work.EL.wakeHi j)
    (hPy : P.y = (Tantibar c)^[j] d.z₁)
    (hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((Tantibar c)^[j] d.z₁) ↔
        θ = Work.EL.T^[j] Work.EL.alpha1 ∨ θ = Work.EL.T^[j] Work.EL.alpha2))
    (hna : Int.fract Q.a ≠ Work.EL.T^[j] Work.EL.alpha1 ∧
      Int.fract Q.a ≠ Work.EL.T^[j] Work.EL.alpha2)
    (hnb : Int.fract Q.b ≠ Work.EL.T^[j] Work.EL.alpha1 ∧
      Int.fract Q.b ≠ Work.EL.T^[j] Work.EL.alpha2) :
    Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q) := by
  have hnaa : ∀ k : ℤ, Q.a ≠ Work.EL.wakeLo j + k :=
    ne_add_int_of_fract_wakeLo hj hna.1 hna.2
  have hnab : ∀ k : ℤ, Q.b ≠ Work.EL.wakeLo j + k :=
    ne_add_int_of_fract_wakeLo hj hnb.1 hnb.2
  have hnba : ∀ k : ℤ, Q.a ≠ Work.EL.wakeHi j + k :=
    ne_add_int_of_fract_wakeHi hj hna.1 hna.2
  have hnbb : ∀ k : ℤ, Q.b ≠ Work.EL.wakeHi j + k :=
    ne_add_int_of_fract_wakeHi hj hnb.1 hnb.2
  have hPy_ne : P.y ≠ Q.y := by
    intro hy
    have hQy : Q.y = (Tantibar c)^[j] d.z₁ := hy ▸ hPy
    have h1 : Work.EL.LandsN d.hN Q.a ((Tantibar c)^[j] d.z₁) := hQy ▸ Q.lands_a
    have h2 := landsN_fract h1
    rcases (hport (Int.fract Q.a) ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩).mp h2 with h | h
    · exact hna.1 h
    · exact hna.2 h
  have hK_P : ({P.y} : Set ℂ) ⊆ Work.EL.K c := by
    rintro z rfl
    exact Work.ELTop.landsN_mem_K d.hN P.lands_a
  have hK_Q : ({Q.y} : Set ℂ) ⊆ Work.EL.K c := by
    rintro z rfl
    exact Work.ELTop.landsN_mem_K d.hN Q.lands_a
  rw [Set.disjoint_left]
  intro z hzP hzQ
  rw [Work.EL.mem_pairCurve_iff] at hzP hzQ
  rw [hPa, hPy, hPb] at hzP
  rcases hzP with hzPa | hzPy | hzPb
  · rcases hzQ with hzQa | hzQy | hzQb
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hnaa) hzPa) hzQa
    · exact (Work.EL.paramRay_subset_compl d.hN (Work.EL.wakeLo j) (hzQy ▸ hzPa))
        (hK_Q (Set.mem_singleton Q.y))
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hnab) hzPa) hzQb
  · rcases hzQ with hzQa | hzQy | hzQb
    · exact (Work.EL.paramRay_subset_compl d.hN Q.a ((hPy.symm ▸ hzPy) ▸ hzQa))
        (hK_P (Set.mem_singleton P.y))
    · exact hPy_ne ((hPy.symm ▸ hzPy) ▸ hzQy)
    · exact (Work.EL.paramRay_subset_compl d.hN Q.b ((hPy.symm ▸ hzPy) ▸ hzQb))
        (hK_P (Set.mem_singleton P.y))
  · rcases hzQ with hzQa | hzQy | hzQb
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hnba) hzPb) hzQa
    · exact (Work.EL.paramRay_subset_compl d.hN (Work.EL.wakeHi j) (hzQy ▸ hzPb))
        (hK_Q (Set.mem_singleton Q.y))
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hnbb) hzPb) hzQb

/-! ## The core of the avoidance argument -/

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `import Submission.Work.ELAssembly.PbAvoid_cycle`.
/-- **The core of the avoidance argument** (`NOTES_LEAD_mandelbar_pbavoid.md` §3.3), for a fixed
cycle index `j < 5`:
(WS) if the wake arc `W_j = (wakeLo j, wakeHi j)` lies in the far arc `(Q.a, Q.b)` of a
co-landing pair `Q`, `Q` shares no angle (mod 1) with the portrait pair `P_j` — i.e.
`Int.fract Q.a`, `Int.fract Q.b` avoid `T^j α₁`, `T^j α₂` — and the portrait at the cycle point
`T^j z₁` is the two-ray portrait (hypothesis `hport`, from `PbAvoid_portrait`), then the wake side
`X_j = wakeSide d.hN d.z₁ j` is contained in the far side `pairSide Q`;
(WS=) if `Q` *is* the cycle pair (`Q.a = wakeLo j`, `Q.b = wakeHi j`), then `X_j = pairSide Q`.

Build the cycle pair `wakeR : CoPair d.hN` with `a = wakeLo j`, `b = wakeHi j`, `y = T^[j] z₁`
from `PbAvoid_cycle` (`LandsN_add_int` for the `+1023` lifts at `j = 3, 4`), and observe
`wakeSide d.hN d.z₁ j = pairSide wakeR` (same base point `rayPt (wakeLo j + arcLen/2) 2`, and the
curves agree because `{min, max}(T^j α₁, T^j α₂) ≡ {wakeLo j, wakeHi j}` mod `1` —
`interval_cases j`, `norm_num`, `paramRay_add_int`).  For (WS) the curves of `wakeR` and `Q` are
disjoint: rays against rays by `Work.ELTop.paramRay_disjoint` and the non-degeneracy hypotheses;
landing points against rays by `K` vs `Kᶜ`; and `Q.y ≠ T^j z₁` because otherwise `hport` applied
to `Q.lands_a` would force `fract Q.a ∈ {T^j α₁, T^j α₂}`.  Then
`Work.ELTop.pairSide_subset_pairSide d.hN Work.TopJordan.jordanForm wakeR Q hdisj hW`.  For (WS=),
`Q.y = T^j z₁` by landing uniqueness (`Work.ELNest.landsN_unique`). -/
theorem PbAvoid_core {c : ℂ} (d : Work.EL.RootParabolic c) (j : ℕ) (hj : j < 5) :
    (∀ (hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.EL.LandsN d.hN θ ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁) ↔
          θ = Work.EL.T^[j] Work.EL.alpha1 ∨ θ = Work.EL.T^[j] Work.EL.alpha2))
      (Q : Work.EL.CoPair d.hN),
      (∀ θ : ℝ, Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j) →
        Work.EL.InArc θ Q.a Q.b) →
      (Int.fract Q.a ≠ (Work.EL.T^[j] Work.EL.alpha1) ∧
        Int.fract Q.a ≠ (Work.EL.T^[j] Work.EL.alpha2)) →
      (Int.fract Q.b ≠ (Work.EL.T^[j] Work.EL.alpha1) ∧
        Int.fract Q.b ≠ (Work.EL.T^[j] Work.EL.alpha2)) →
      Work.EL.wakeSide d.hN d.z₁ j ⊆ Work.EL.pairSide Q) ∧
    (∀ Q : Work.EL.CoPair d.hN, Q.a = Work.EL.wakeLo j → Q.b = Work.EL.wakeHi j →
      Work.EL.wakeSide d.hN d.z₁ j = Work.EL.pairSide Q) := by
  constructor
  · intro hport Q hW hna hnb
    obtain ⟨wakeR, ha, hb, hy, hside⟩ := wakeSide_eq_pairSide_wakeR d j hj
    rw [hside]
    refine Work.ELTop.pairSide_subset_pairSide d.hN Work.TopJordan.jordanForm wakeR Q ?_ ?_
    · exact pairCurve_disjoint_wake d j hj wakeR Q ha hb hy hport hna hnb
    · intro θ hθ
      exact hW θ (by rwa [ha, hb] at hθ)
  · intro Q hQa hQb
    obtain ⟨wakeR, ha, hb, hy, hside⟩ := wakeSide_eq_pairSide_wakeR d j hj
    rw [hside]
    have hQy : Q.y = wakeR.y :=
      Work.ELNest.landsN_unique (hQa ▸ Q.lands_a) (ha ▸ wakeR.lands_a)
    have hraw : wakeR.toRawPair = Q.toRawPair := by
      rw [show wakeR.toRawPair = ({ a := wakeR.a, b := wakeR.b, y := wakeR.y } : Work.EL.RawPair)
            from rfl,
          show Q.toRawPair = ({ a := Q.a, b := Q.b, y := Q.y } : Work.EL.RawPair) from rfl,
          Work.EL.RawPair.mk.injEq]
      exact ⟨by rw [ha, hQa], by rw [hb, hQb], hQy.symm⟩
    rw [Work.EL.pairSide_eq, Work.EL.pairSide_eq, hraw]

end Work.ELAssembly
