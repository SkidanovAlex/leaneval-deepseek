import Mathlib
import Submission.Work.FIArea1.QboxDefs

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about the radii `KR`, `KZ` -/

/-- `KZ (2X) = KR X`. -/
lemma KZ_two_mul_eq_KR (X : ℝ) : KZ (2 * X) = KR X := by
  have h : (2 : ℝ) * (2 * X) = 4 * X := by ring
  rw [KZ, KR, h]

/-- **`KR`-box membership from a norm bound.**  If `|z|² ≤ 4X` then `|Re z|, |Im z| ≤ √(4X) ≤
KR X = ⌈√(4X)⌉`, hence `z ∈ gBox (KR X)`. -/
lemma mem_gBox_KR_of_gnorm_le {X : ℝ} {z : GaussianInt}
    (h : (Work.FIPlan.gnorm z : ℝ) ≤ 4 * X) : z ∈ Work.FIPlan.gBox (KR X) := by
  rw [← KZ_two_mul_eq_KR X]
  exact mem_gBox_KZ_of_gnorm_le (by linarith)

/-- `(KR M)² ≤ 16 M` for `M ≥ 1/4`: `KR M = ⌈2√M⌉ ≤ 4√M` because `√M ≥ 1/2`. -/
lemma natAbs_KR_sq_le (M : ℝ) (hM : (1 : ℝ) / 4 ≤ M) : ((KR M).natAbs : ℝ) ^ 2 ≤ 16 * M := by
  have h0 : (0 : ℝ) ≤ M := by linarith
  have hcoef : ((KR M).natAbs : ℝ) = ((⌈Real.sqrt (4 * M)⌉₊ : ℕ) : ℝ) := by simp [KR]
  rw [hcoef]
  have hceil := Nat.ceil_lt_add_one (a := Real.sqrt (4 * M)) (by positivity)
  have hsq : Real.sqrt (4 * M) = 2 * Real.sqrt M := by
    rw [show (4 : ℝ) * M = 2 ^ 2 * M by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt M := (Real.le_sqrt (by norm_num) h0).mpr (by linarith)
  have hle : ((⌈Real.sqrt (4 * M)⌉₊ : ℕ) : ℝ) ≤ 4 * Real.sqrt M := by linarith
  have h4 : (4 * Real.sqrt M) ^ 2 = 16 * M := by
    rw [mul_pow, Real.sq_sqrt h0]
    norm_num
  calc ((⌈Real.sqrt (4 * M)⌉₊ : ℕ) : ℝ) ^ 2 ≤ (4 * Real.sqrt M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hle 2
    _ = 16 * M := h4

/-- **The norm bound in the `KR`-box.**  For `w` in the box `gBox (KR M)` (`M ≥ 1/4`) one has
`|w|² ≤ 2 (KR M)² ≤ 32 M`. -/
lemma gnorm_le_of_mem_gBox_KR {M : ℝ} (hM : (1 : ℝ) / 4 ≤ M) {w : GaussianInt}
    (hw : w ∈ Work.FIPlan.gBox (KR M)) : (Work.FIPlan.gnorm w : ℝ) ≤ 32 * M := by
  have h1 := Work.FIArea2.gnorm_le_of_mem_gBox (KR_nonneg M) hw
  have h1r : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * ((KR M).natAbs : ℝ) ^ 2 := by
    have h1' : ((Work.FIPlan.gnorm w : ℕ) : ℝ) ≤ ((2 * (KR M).natAbs ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact h1'
  have h2 := natAbs_KR_sq_le M hM
  linarith

/-! ## The main grouping lemma -/

/-- **Grouping the `(π,w)`-sum by the product `W = πw`.**  Route: rewrite the double sum over
`PiSet q N × (gBox (KR M)).erase 0` as a sum over its image under `(π,w) ↦ πw` with the fibre
cardinalities as weights (`Finset.sum_fiberwise_of_maps_to`); each fibre over `W` injects into
`PiDvd q N W` (the map `(π,w) ↦ π` is injective on the fibre because `w = W/π` is determined), so
its cardinality is at most `((PiDvd q N W).card : ℝ) ≤ K`; finally bound the image by the whole box
`(gBox (KR (16*M*q))).erase 0` using `0 ≤ F` there.  The box hypothesis is the arithmetic
`π ∈ PiSet q N`, `w ∈ gBox (KR M)` ⟹ `|πw|² ≤ 2q·2(KR M)² ≤ 64Mq ≤ (KR (16Mq))²`. -/
theorem pi_w_group_le (q M N K : ℝ) (F : GaussianInt → ℝ)
    (hq : 1 ≤ q) (hN : 2 ≤ N) (hNM : N ≤ M) (hK : 0 ≤ K)
    (hcard : ∀ W ∈ (Work.FIPlan.gBox (Work.FIArea1.KR (16 * M * q))).erase 0,
      ((Work.FIArea1.PiDvd q N W).card : ℝ) ≤ K)
    (hF : ∀ W ∈ (Work.FIPlan.gBox (Work.FIArea1.KR (16 * M * q))).erase 0, 0 ≤ F W) :
    (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ (Work.FIPlan.gBox (Work.FIArea1.KR M)).erase 0,
        F (π * w))
      ≤ K * (∑ W ∈ (Work.FIPlan.gBox (Work.FIArea1.KR (16 * M * q))).erase 0, F W) := by
  classical
  set T : Finset GaussianInt := (Work.FIPlan.gBox (KR (16 * M * q))).erase 0 with hT
  set S : Finset (GaussianInt × GaussianInt) :=
    PiSet q N ×ˢ ((Work.FIPlan.gBox (KR M)).erase 0) with hS
  have hM1 : (1 : ℝ) / 4 ≤ M := by linarith
  -- The image of `S` under `(π,w) ↦ πw` lies in the big box.
  have hmap : ∀ p ∈ S, p.1 * p.2 ∈ T := by
    intro p hp
    rw [hS, Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hw0, hwbox⟩ := Finset.mem_erase.mp hp2
    rw [PiSet, Finset.mem_filter] at hp1
    obtain ⟨hπbox, hπprime, hπgt, hπle⟩ := hp1
    rw [hT, Finset.mem_erase]
    refine ⟨mul_ne_zero hπprime.ne_zero hw0, ?_⟩
    refine mem_gBox_KR_of_gnorm_le ?_
    have hgw : (Work.FIPlan.gnorm p.2 : ℝ) ≤ 32 * M := gnorm_le_of_mem_gBox_KR hM1 hwbox
    have hprod : (Work.FIPlan.gnorm (p.1 * p.2) : ℝ)
        = (Work.FIPlan.gnorm p.1 : ℝ) * (Work.FIPlan.gnorm p.2 : ℝ) := by
      rw [gnorm_mul]
      push_cast
      ring
    rw [hprod]
    have h1 : (Work.FIPlan.gnorm p.1 : ℝ) * (Work.FIPlan.gnorm p.2 : ℝ)
        ≤ (2 * q) * (32 * M) :=
      mul_le_mul hπle hgw (by positivity) (by linarith)
    have h2 : (2 * q) * (32 * M) ≤ 4 * (16 * M * q) := by
      have heq : (2 * q) * (32 * M) = 4 * (16 * M * q) := by ring
      linarith
    linarith
  -- Each fibre injects into `PiDvd q N W`.
  have hfib_le : ∀ W : GaussianInt,
      ((S.filter (fun p => p.1 * p.2 = W)).card : ℝ) ≤ ((PiDvd q N W).card : ℝ) := by
    intro W
    have hinj : Set.InjOn (fun p : GaussianInt × GaussianInt => p.1)
        ↑(S.filter (fun p => p.1 * p.2 = W)) := by
      intro p hp r hr hpr
      have hpr' : p.1 = r.1 := by simpa using hpr
      rw [Finset.mem_coe, Finset.mem_filter] at hp hr
      have hp1 : p.1 ∈ PiSet q N := by
        have h := hp.1
        rw [hS, Finset.mem_product] at h
        exact h.1
      have hne : p.1 ≠ 0 := (Finset.mem_filter.mp hp1).2.1.ne_zero
      have heq : p.1 * p.2 = p.1 * r.2 := by rw [hp.2, ← hr.2, hpr']
      have h2 : p.2 = r.2 := mul_left_cancel₀ hne heq
      exact Prod.ext hpr' h2
    have hmt : Set.MapsTo (fun p : GaussianInt × GaussianInt => p.1)
        ↑(S.filter (fun p => p.1 * p.2 = W)) ↑(PiDvd q N W) := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      have hp1 : p.1 ∈ PiSet q N := by
        have h := hp.1
        rw [hS, Finset.mem_product] at h
        exact h.1
      rw [PiSet, Finset.mem_filter] at hp1
      obtain ⟨hb, hpr, hgt, hle⟩ := hp1
      refine Finset.mem_filter.mpr ⟨hb, hpr, hgt, hle, ?_⟩
      rw [← hp.2]
      exact dvd_mul_right _ _
    exact_mod_cast Finset.card_le_card_of_injOn (fun p : GaussianInt × GaussianInt => p.1) hmt hinj
  -- Turn the double sum into the fibre sum over the box.
  have hprod : (∑ π ∈ PiSet q N, ∑ w ∈ (Work.FIPlan.gBox (KR M)).erase 0, F (π * w))
      = ∑ p ∈ S, F (p.1 * p.2) := by
    rw [hS, Finset.sum_product]
  have hexpand : (∑ p ∈ S, F (p.1 * p.2))
      = ∑ W ∈ T, ((S.filter (fun p => p.1 * p.2 = W)).card : ℝ) * F W := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun p : GaussianInt × GaussianInt => p.1 * p.2) hmap (fun p => F (p.1 * p.2))]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    trans ∑ p ∈ S.filter (fun p => p.1 * p.2 = W), F W
    · exact Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])
    · rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ π ∈ PiSet q N, ∑ w ∈ (Work.FIPlan.gBox (KR M)).erase 0, F (π * w))
      = ∑ p ∈ S, F (p.1 * p.2) := hprod
    _ = ∑ W ∈ T, ((S.filter (fun p => p.1 * p.2 = W)).card : ℝ) * F W := hexpand
    _ ≤ ∑ W ∈ T, K * F W := by
        refine Finset.sum_le_sum (fun W hW => ?_)
        exact mul_le_mul_of_nonneg_right (le_trans (hfib_le W) (hcard W hW)) (hF W hW)
    _ = K * ∑ W ∈ T, F W := by rw [Finset.mul_sum]

end

end Work.FIArea1
