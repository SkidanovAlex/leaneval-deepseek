/-
# `Submission.Work.FIArea1.PiRangeReduce` — the substitution `z = π y` of *FI* (5.22)

This module carries the **combinatorial reduction** of the per-dyadic-range bound of *FI* (5.22):
for a Gaussian prime `π` of norm `> q` and a point `z` of `Zbox N` (`|z|² ∈ (N, 2N]`, primitive)
divisible by `π`, the quotient `y = z/π` satisfies

  `|y|² = |z|²/|π|² ≤ 2N/q`,   and   `|y| ≤ √(2N/q) ≤ KZ (N/q)`,

i.e. `y ∈ Qbig (N/q)`.  Consequently the inner double sum over the pairs `(z₁,z₂)` divisible by `π`
is bounded by the corresponding double sum over the ball `Qbig (N/q)` with `w` replaced by `wπ`
(this is where `Re(w zᵢ) = Re((wπ) yᵢ)` and `Δ(πy₁,πy₂) = |π|²Δ(y₁,y₂)` are used).
-/
import Mathlib
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.QboxDefs
import Submission.Work.FIArea2.area2_r3

set_option maxHeartbeats 800000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The quotient `z/π` -/

/-- The quotient `z / π`, with the junk value `0` when `π ∤ z`. -/
noncomputable def zQuot (π z : GaussianInt) : GaussianInt :=
  if h : π ∣ z then Classical.choose h else 0

lemma mul_zQuot {π z : GaussianInt} (h : π ∣ z) : π * zQuot π z = z := by
  rw [zQuot, dif_pos h]
  exact (Classical.choose_spec h).symm

lemma zQuot_eq_iff {π : GaussianInt} {z1 z2 : GaussianInt}
    (h1 : π ∣ z1) (h2 : π ∣ z2) : zQuot π z1 = zQuot π z2 ↔ z1 = z2 := by
  constructor
  · intro h
    rw [← mul_zQuot h1, ← mul_zQuot h2, h]
  · intro h; rw [h]

lemma zQuot_ne_zero {π z : GaussianInt} (hz : z ≠ 0) (h : π ∣ z) : zQuot π z ≠ 0 := by
  intro h0
  exact hz (by rw [← mul_zQuot h, h0, mul_zero])

lemma star_intCast (n : ℤ) : star ((n : ℤ) : GaussianInt) = ((n : ℤ) : GaussianInt) := by
  ext <;> simp

/-! ## The two identities of the substitution -/

/-- `Re(w (π y)) = Re((wπ) y)`. -/
lemma cForm_mul_assoc (w π y : GaussianInt) :
    Work.FIPlan.cForm w (π * y) = Work.FIPlan.cForm (w * π) y := by
  simp [Work.FIPlan.cForm, mul_assoc]

/-- `Δ(πy₁, πy₂) = |π|² Δ(y₁,y₂)`. -/
lemma Delta_mul_mul (a b c : GaussianInt) :
    Work.FIPlan.Delta (a * b) (a * c)
      = ((Work.FIPlan.gnorm a : ℕ) : ℤ) * Work.FIPlan.Delta b c := by
  rw [Work.FIArea2.Delta_def, Work.FIArea2.Delta_def]
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [Work.FIArea1.gnorm_int]
  ring_nf

/-- `Δ(πy₁, πy₂)` vanishes exactly when `Δ(y₁,y₂)` does (for `π ≠ 0`). -/
lemma Delta_mul_mul_eq_zero_iff {a : GaussianInt} (ha : a ≠ 0) (b c : GaussianInt) :
    Work.FIPlan.Delta (a * b) (a * c) = 0 ↔ Work.FIPlan.Delta b c = 0 := by
  rw [Delta_mul_mul]
  have hane : ((Work.FIPlan.gnorm a : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Work.FIArea2.gnorm_pos ha).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hane
    · exact h1
  · intro h; rw [h, mul_zero]

/-! ## The norm bound for the quotient -/

lemma gnorm_zQuot_le {π z : GaussianInt} {q N : ℝ} (hq : 0 < q)
    (hπq : q ≤ (Work.FIPlan.gnorm π : ℝ)) (hz : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N)
    (h : π ∣ z) : (Work.FIPlan.gnorm (zQuot π z) : ℝ) ≤ 2 * N / q := by
  have hN0 : 0 ≤ N := by
    have := Nat.cast_nonneg (α := ℝ) (Work.FIPlan.gnorm z); linarith
  have hgn : Work.FIPlan.gnorm z
      = Work.FIPlan.gnorm π * Work.FIPlan.gnorm (zQuot π z) := by
    conv_lhs => rw [← mul_zQuot h]
    rw [Work.FIArea1.gnorm_mul]
  rw [hgn] at hz
  push_cast at hz
  have hπpos : (0:ℝ) < (Work.FIPlan.gnorm π : ℝ) := lt_of_lt_of_le hq hπq
  have h1 : (Work.FIPlan.gnorm (zQuot π z) : ℝ) ≤ 2 * N / (Work.FIPlan.gnorm π : ℝ) := by
    rw [le_div_iff₀ hπpos]; linarith
  have h2 : 2 * N / (Work.FIPlan.gnorm π : ℝ) ≤ 2 * N / q :=
    div_le_div_of_nonneg_left (by linarith) hq hπq
  linarith

/-- **The substituted point lies in the ball**: if `z ∈ Zbox N` and `π ∣ z` with
`0 < q ≤ |π|²`, then `z/π ∈ Qbig (N/q)`. -/
lemma zQuot_mem_Qbig {π z : GaussianInt} {q N : ℝ} (hq : 0 < q)
    (hπq : q ≤ (Work.FIPlan.gnorm π : ℝ)) (hz : z ∈ Zbox N) (h : π ∣ z) :
    zQuot π z ∈ Qbig (N / q) := by
  obtain ⟨-, -, hNlt, hNle⟩ := (mem_Zbox_iff).mp hz
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (Work.FIPlan.gnorm z : ℝ) = 0 := by rw [h0]; simp [Work.FIArea2.gnorm_zero]
    linarith
  refine mem_Qbig_of_gnorm_le (zQuot_ne_zero hz0 h) ?_
  have hb := gnorm_zQuot_le hq hπq hNle h
  rw [show 2 * (N / q) = 2 * N / q from by ring]
  exact hb

/-! ## A real substituted point is a unit -/

/-- **A real substituted point must be `±1`.**  If `z ∈ Zbox N` (in particular `z` is primitive),
`π ∣ z` and `y = z/π` is real, then `y = ±1`: writing `y = n` with `|n| ≥ 2`, a rational prime
`p ∣ n` would divide `z` and `z̄`, contradicting `(z,z̄) = 1`. -/
lemma zQuot_eq_unit_of_im_eq_zero {π z : GaussianInt} {N : ℝ} (hz : z ∈ Zbox N)
    (hd : π ∣ z) (him : (zQuot π z).im = 0) :
    zQuot π z = 1 ∨ zQuot π z = -1 := by
  set y := zQuot π z with hy
  have hyz : π * y = z := mul_zQuot hd
  have hprim : IsCoprime z (star z) := (mem_Zbox_iff.mp hz).2.1
  have hy_eq : y = ((y.re : ℤ) : GaussianInt) := by ext <;> simp [him]
  have hz_ne : z ≠ 0 := by
    intro h0
    obtain ⟨-, -, hNlt, hNle⟩ := (mem_Zbox_iff.mp hz)
    rw [h0] at hNlt hNle
    simp [Work.FIArea2.gnorm_zero] at hNlt hNle
    linarith
  have hy_ne : y ≠ 0 := fun h0 => hz_ne (by rw [← hyz, h0, mul_zero])
  have hle : y.re.natAbs ≤ 1 := by
    by_contra h
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : y.re.natAbs ≠ 1)
    have hpd' : (p : ℤ) ∣ y.re := by
      have h1 : ((p : ℤ) ∣ ((y.re.natAbs : ℕ) : ℤ)) := by exact_mod_cast hpd
      rwa [Int.dvd_natAbs] at h1
    obtain ⟨k, hk⟩ := hpd'
    have hpdy : (((p : ℤ)) : GaussianInt) ∣ y :=
      ⟨((k : ℤ) : GaussianInt), by rw [hy_eq, hk]; push_cast; ring⟩
    have hpdπ : (((p : ℤ)) : GaussianInt) ∣ z := by
      rw [← hyz]; exact dvd_mul_of_dvd_right hpdy π
    have hpdπ' : (((p : ℤ)) : GaussianInt) ∣ star z := by
      obtain ⟨c, hc⟩ := hpdπ
      refine ⟨star c, ?_⟩
      rw [hc, star_mul, star_intCast]
      ring
    have hunit : IsUnit (((p : ℤ)) : GaussianInt) := hprim.isUnit_of_dvd' hpdπ hpdπ'
    have hnorm0 : (((p : ℤ)) : GaussianInt).norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hunit
    have hnorm : Work.FIPlan.gnorm (((p : ℤ)) : GaussianInt) = 1 := hnorm0
    rw [Work.FIArea1.gnorm_intCast] at hnorm
    have hp1 : p = 1 := by
      have h2 : (p : ℤ).natAbs * (p : ℤ).natAbs = 1 := by rw [← pow_two]; exact hnorm
      have h3 : (p : ℤ).natAbs = 1 := Nat.dvd_one.mp ⟨_, h2.symm⟩
      have h4 : (((p : ℤ).natAbs : ℤ)) = (p : ℤ) := Int.natAbs_of_nonneg (by positivity)
      omega
    have := hp.two_le
    omega
  have hmem : y.re = -1 ∨ y.re = 0 ∨ y.re = 1 := by
    have habs : |y.re| ≤ 1 := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hle
    have h1 := (abs_le.mp habs).1
    have h2 := (abs_le.mp habs).2
    omega
  rcases hmem with h | h | h
  · right; rw [hy_eq, h]; norm_num
  · exact absurd (show y = 0 by rw [hy_eq, h]; rfl) hy_ne
  · left; rw [hy_eq, h]; norm_num

/-- **The substituted point lies in `Yset (N/q)`.** -/
lemma zQuot_mem_Yset {π z : GaussianInt} {q N : ℝ} (hq : 0 < q)
    (hπq : q ≤ (Work.FIPlan.gnorm π : ℝ)) (hz : z ∈ Zbox N) (hd : π ∣ z) :
    zQuot π z ∈ Yset (N / q) := by
  by_cases him : (zQuot π z).im = 0
  · rcases zQuot_eq_unit_of_im_eq_zero hz hd him with h | h
    · rw [h]; exact one_mem_Yset _
    · rw [h]; exact neg_one_mem_Yset _
  · exact mem_Yset_iff.mpr (Or.inl (Finset.mem_filter.mpr
      ⟨zQuot_mem_Qbig hq hπq hz hd, him⟩))

/-! ## A generic "injective image" sum bound -/

lemma sum_image_le {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → α} {g : α → ℝ}
    (hinj : Set.InjOn f ↑s) (hmap : ∀ a ∈ s, f a ∈ t) (hpos : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun i hi _ => hpos i hi)
  obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
  rw [← hax]
  exact hmap a ha

/-! ## The per-`(π,w)` substitution of the inner double sum -/

/-- **Substitution in the inner double sum.**  For a Gaussian prime `π` with `0 < q ≤ |π|²` and any
`w`, the double sum over the pairs of `Zbox N` divisible by `π` (restricted to `Δ ≠ 0`) is at most
the same double sum over the ball `Qbig (N/q)`, with `w` replaced by `wπ`. -/
lemma subst_pair_le {π w : GaussianInt} {q N : ℝ} (hq : 0 < q)
    (hπq : q ≤ (Work.FIPlan.gnorm π : ℝ)) :
    (∑ z1 ∈ (Zbox N).filter (fun z => π ∣ z),
       ∑ z2 ∈ (Zbox N).filter (fun z => π ∣ z),
         (if Work.FIPlan.Delta z1 z2 = 0 then 0
          else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
               * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
    ≤ (∑ y1 ∈ Yset (N/q), ∑ y2 ∈ Yset (N/q),
         (if Work.FIPlan.Delta y1 y2 = 0 then 0
          else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) y1) : ℝ)
               * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) y2) : ℝ))) := by
  classical
  have hπne : π ≠ 0 := by
    intro h0
    have : (Work.FIPlan.gnorm π : ℝ) = 0 := by rw [h0]; simp [Work.FIArea2.gnorm_zero]
    linarith
  set Z := (Zbox N).filter (fun z => π ∣ z) with hZ
  have hpt : ∀ p ∈ Z.product Z,
      (if Work.FIPlan.Delta p.1 p.2 = 0 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w p.1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w p.2) : ℝ))
      = (if Work.FIPlan.Delta (zQuot π p.1) (zQuot π p.2) = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) (zQuot π p.1)) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) (zQuot π p.2)) : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hd1 : π ∣ p.1 := (Finset.mem_filter.mp hp1).2
    have hd2 : π ∣ p.2 := (Finset.mem_filter.mp hp2).2
    have e1 : p.1 = π * zQuot π p.1 := (mul_zQuot hd1).symm
    have e2 : p.2 = π * zQuot π p.2 := (mul_zQuot hd2).symm
    have hΔ : Work.FIPlan.Delta p.1 p.2 = 0
        ↔ Work.FIPlan.Delta (zQuot π p.1) (zQuot π p.2) = 0 := by
      conv_lhs => rw [e1, e2]
      exact Delta_mul_mul_eq_zero_iff hπne _ _
    have hc1 : Work.FIPlan.cForm w p.1 = Work.FIPlan.cForm (w * π) (zQuot π p.1) := by
      conv_lhs => rw [e1]
      rw [cForm_mul_assoc]
    have hc2 : Work.FIPlan.cForm w p.2 = Work.FIPlan.cForm (w * π) (zQuot π p.2) := by
      conv_lhs => rw [e2]
      rw [cForm_mul_assoc]
    by_cases h0 : Work.FIPlan.Delta p.1 p.2 = 0
    · rw [if_pos h0, if_pos (hΔ.mp h0)]
    · rw [if_neg h0, if_neg (fun hc => h0 (hΔ.mpr hc)), hc1, hc2]
  have hstep : (∑ z1 ∈ Z, ∑ z2 ∈ Z,
        (if Work.FIPlan.Delta z1 z2 = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
      = ∑ p ∈ Z.product Z,
          (if Work.FIPlan.Delta (zQuot π p.1) (zQuot π p.2) = 0 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) (zQuot π p.1)) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) (zQuot π p.2)) : ℝ)) := by
    rw [← Finset.sum_product Z Z (fun p : GaussianInt × GaussianInt =>
      (if Work.FIPlan.Delta p.1 p.2 = 0 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w p.1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w p.2) : ℝ)))]
    exact Finset.sum_congr rfl hpt
  rw [hstep]
  rw [← Finset.sum_product (Yset (N/q)) (Yset (N/q))
    (fun r : GaussianInt × GaussianInt =>
      (if Work.FIPlan.Delta r.1 r.2 = 0 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) r.1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) r.2) : ℝ)))]
  refine sum_image_le (s := Z.product Z) (t := (Yset (N/q)).product (Yset (N/q)))
    (f := fun p : GaussianInt × GaussianInt => (zQuot π p.1, zQuot π p.2))
    (g := fun r : GaussianInt × GaussianInt =>
      (if Work.FIPlan.Delta r.1 r.2 = 0 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) r.1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) r.2) : ℝ))) ?_ ?_ ?_
  · intro p hp r hr hpr
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hr1, hr2⟩ := Finset.mem_product.mp hr
    have hd1 : π ∣ p.1 := (Finset.mem_filter.mp hp1).2
    have hd2 : π ∣ p.2 := (Finset.mem_filter.mp hp2).2
    have he1 : π ∣ r.1 := (Finset.mem_filter.mp hr1).2
    have he2 : π ∣ r.2 := (Finset.mem_filter.mp hr2).2
    exact Prod.ext ((zQuot_eq_iff hd1 he1).mp (congrArg Prod.fst hpr))
      ((zQuot_eq_iff hd2 he2).mp (congrArg Prod.snd hpr))
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr
      ⟨zQuot_mem_Yset hq hπq (Finset.mem_filter.mp hp1).1 (Finset.mem_filter.mp hp1).2,
       zQuot_mem_Yset hq hπq (Finset.mem_filter.mp hp2).1 (Finset.mem_filter.mp hp2).2⟩
  · intro r _
    split_ifs <;> positivity


/-! ## The indicator reduction of the target summand -/

/-- **Pointwise reduction.**  The summand of the target (which vanishes unless `Δ ≠ 0` and both
points are divisible by `π`) is at most the same expression with the two divisibility conditions
moved into nested indicators. -/
lemma term_le_indicator (w π z1 z2 : GaussianInt) :
    (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
     else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))
    ≤ (if π ∣ z1 then (if π ∣ z2 then
        (if Work.FIPlan.Delta z1 z2 = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)) else 0) else 0) := by
  by_cases h1 : π ∣ z1
  · by_cases h2 : π ∣ z2
    · by_cases hΔ : Work.FIPlan.Delta z1 z2 = 0
      · simp [hΔ]
      · simp only [h1, h2, hΔ, if_true, if_false]
        exact le_rfl
    · simp [h2]
  · simp [h1]

/-- Nested indicator sums are the sums over the filtered sets. -/
lemma sum_filter_nested (Z : Finset GaussianInt) (p : GaussianInt → Prop) [DecidablePred p]
    (f : GaussianInt → GaussianInt → ℝ) :
    (∑ a ∈ Z, ∑ b ∈ Z, (if p a then (if p b then f a b else 0) else 0))
      = ∑ a ∈ Z.filter p, ∑ b ∈ Z.filter p, f a b := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hpa : p a
  · simp only [hpa, if_true]
    rw [Finset.sum_filter]
  · simp only [hpa, if_false, Finset.sum_const_zero]

/-- **The reduction of the prime-substitution sum to the ball `Qbig (N/q)`.** -/
lemma pi_range_reduce {q M N : ℝ} (hq : 0 < q) :
    (∑ π ∈ PiSet q N, ∑ w ∈ (Work.FIPlan.gBox (KR M)).erase 0,
      ∑ z1 ∈ Zbox N, ∑ z2 ∈ Zbox N,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
    ≤ (∑ π ∈ PiSet q N, ∑ w ∈ (Work.FIPlan.gBox (KR M)).erase 0,
        ∑ y1 ∈ Yset (N/q), ∑ y2 ∈ Yset (N/q),
          (if Work.FIPlan.Delta y1 y2 = 0 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) y1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) y2) : ℝ))) := by
  refine Finset.sum_le_sum (fun π hπ => Finset.sum_le_sum (fun w _ => ?_))
  have hqπ : q ≤ (Work.FIPlan.gnorm π : ℝ) :=
    le_of_lt (Finset.mem_filter.mp hπ).2.2.1
  refine le_trans ?_ (subst_pair_le (π := π) (w := w) (q := q) (N := N) hq hqπ)
  refine le_trans (Finset.sum_le_sum (fun z1 _ =>
    Finset.sum_le_sum (fun z2 _ => term_le_indicator w π z1 z2))) ?_
  rw [sum_filter_nested (Zbox N) (fun z => π ∣ z)]

end

end Work.FIArea1
