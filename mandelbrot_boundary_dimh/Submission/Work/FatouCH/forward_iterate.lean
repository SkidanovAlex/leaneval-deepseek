import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Shishikura A.2.1(i): forward iteration crosses the line `Re = x₀` inside `𝒬`

For a near-translation `F` on `Qreg b₁ b₂` and a vertical line `Re = x₀` with
`Re b₁ + 1 < x₀` and `x₀ + 3 < Re b₂`, any point `z ∈ Qreg b₁ b₂` with `Re z < x₀` reaches
the line `Re = x₀` by forward iteration, without ever leaving `Qreg b₁ b₂`.

The proof is the standard one for Shishikura's `𝒬`:

* one step of `F` raises `Re` by between `31/32` and `33/32` (from `‖F u - (u+1)‖ ≤ 1/32`);
* consequently the left cone condition `-|Im (z-a)| < Re (z-a)` is preserved: the quantity
  `Re (z-a) + |Im (z-a)|` increases by at least `30/32` under `F`;
* once `Re` is to the left of every `b ∈ b₂` (in particular whenever `Re < x₀ + 3 < Re b₂`)
  the right cone condition holds automatically.

Hence a forward orbit either stays in `𝒬`, moving right by at least `31/32` per step, or has
already crossed `Re = x₀`; iteration cannot continue forever below `x₀`.
-/

namespace Work.FatouCH

open MandelDim

noncomputable section

/-- Component bounds for one step of a near-translation: `Re` moves by between `31/32`
and `33/32`. -/
lemma fi_re_step_bounds {F : ℂ → ℂ} {u : ℂ} (h : ‖F u - (u + 1)‖ ≤ 1 / 32) :
    u.re + 31 / 32 ≤ (F u).re ∧ (F u).re ≤ u.re + 33 / 32 := by
  have h1 : |(F u - (u + 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) h
  have h2 : (F u - (u + 1)).re = (F u).re - u.re - 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  rw [h2] at h1
  have h3 := abs_le.mp h1
  constructor <;> linarith

/-- The left cone condition `-|Im (z-a)| < Re (z-a)` is preserved by one step of a
near-translation: `Re (z-a) + |Im (z-a)|` increases by at least `30/32`. -/
lemma fi_left_cone_step {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {u : ℂ}
    (hu : u ∈ Qreg b₁ b₂) (hstep : ‖F u - (u + 1)‖ ≤ 1 / 32) :
    ∀ a ∈ b₁, 0 < (F u - a).re + |(F u - a).im| := by
  intro a ha
  have hpos : 0 < (u - a).re + |(u - a).im| := by
    have := hu.1 a ha; linarith
  have hδre : -(1 / 32 : ℝ) ≤ (F u - (u + 1)).re := by
    have := le_trans (Complex.abs_re_le_norm (F u - (u + 1))) hstep
    linarith [abs_le.mp this]
  have hδim : |(F u - (u + 1)).im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm _) hstep
  have hre : (F u - a).re = (u - a).re + 1 + (F u - (u + 1)).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F u - a).im = (u - a).im + (F u - (u + 1)).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  rw [hre, him]
  have habs := abs_sub_abs_le_abs_sub (u - a).im (-(F u - (u + 1)).im)
  simp only [abs_neg, sub_neg_eq_add] at habs
  linarith

/-- One step of a near-translation at a point of `𝒬` below the line `Re = x₀` still lies in
`𝒬` (the left cone is preserved, the right cone is automatic because `Re < x₀ + 3 < Re b₂`). -/
lemma fi_step_mem_Qreg {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {u : ℂ} (hu : u ∈ Qreg b₁ b₂) (hux : u.re < x₀)
    (hstep : ‖F u - (u + 1)‖ ≤ 1 / 32) :
    F u ∈ Qreg b₁ b₂ := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h := fi_left_cone_step hu hstep a ha
    have := abs_nonneg (F u - a).im
    show -|(F u - a).im| < (F u - a).re
    linarith
  · have hre : (F u).re ≤ u.re + 33 / 32 := (fi_re_step_bounds hstep).2
    have hb' := h₂ b hb
    show (F u - b).re < |(F u - b).im|
    have hsub : (F u - b).re = (F u).re - b.re := by simp only [Complex.sub_re]
    have := abs_nonneg (F u - b).im
    rw [hsub]; linarith

/-- Invariant of the forward orbit below the line: as long as `Re (F^[i] z) < x₀` for all
`i < j`, the iterate `F^[j] z` stays in `𝒬` and its real part is at least
`Re z + j · 31/32`. -/
lemma fi_iterates_stay {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : NearTranslationOn F (Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) :
    ∀ j : ℕ, (∀ i < j, (F^[i] z).re < x₀) →
      F^[j] z ∈ Qreg b₁ b₂ ∧ z.re + (j : ℝ) * (31 / 32) ≤ (F^[j] z).re := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨hz, ?_⟩
      simp
  | succ j ih =>
      intro hlt
      have hlt' : ∀ i < j, (F^[i] z).re < x₀ := fun i hi => hlt i (Nat.lt_succ_of_lt hi)
      obtain ⟨hmem, _hbound⟩ := ih hlt'
      have hjx : (F^[j] z).re < x₀ := hlt j (Nat.lt_succ_self j)
      have hstep : ‖F (F^[j] z) - (F^[j] z + 1)‖ ≤ 1 / 32 := (hF.2 (F^[j] z) hmem).1
      have hiter : F^[j + 1] z = F (F^[j] z) := Function.iterate_succ_apply' F j z
      refine ⟨?_, ?_⟩
      · rw [hiter]; exact fi_step_mem_Qreg h₂ hmem hjx hstep
      · rw [hiter]
        have h1 := (fi_re_step_bounds hstep).1
        have : z.re + (j : ℝ) * (31 / 32) + 31 / 32 ≤ (F (F^[j] z)).re := by linarith
        calc z.re + ((j + 1 : ℕ) : ℝ) * (31 / 32)
            = z.re + (j : ℝ) * (31 / 32) + 31 / 32 := by push_cast; ring
          _ ≤ (F (F^[j] z)).re := this

open MandelDim in
lemma forward_iterate {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : NearTranslationOn F (Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzx : z.re < x₀) :
    ∃ k : ℕ, 0 < k ∧ (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∧
      x₀ ≤ (F^[k] z).re ∧ ∀ j < k, (F^[j] z).re < x₀ := by
  classical
  -- The forward orbit cannot stay below the line `Re = x₀` forever.
  have hex : ∃ j, x₀ ≤ (F^[j] z).re := by
    by_contra hcon
    have hlt : ∀ j, (F^[j] z).re < x₀ := fun j => not_le.mp (not_exists.mp hcon j)
    obtain ⟨j, hj⟩ := exists_nat_gt ((x₀ - z.re) * 32 / 31)
    have hbound := (fi_iterates_stay h₂ hF hz j (fun i _ => hlt i)).2
    have h32 : (0 : ℝ) < 31 / 32 := by norm_num
    have hmul : x₀ - z.re < (j : ℝ) * (31 / 32) := by
      have h := mul_lt_mul_of_pos_right hj h32
      have he : (x₀ - z.re) * 32 / 31 * (31 / 32) = x₀ - z.re := by ring
      rw [he] at h
      exact h
    linarith [hlt j]
  -- `k` is the first crossing.
  let k := Nat.find hex
  have hk_spec : x₀ ≤ (F^[k] z).re := Nat.find_spec hex
  have hk_min : ∀ i < k, (F^[i] z).re < x₀ := fun i hi => not_le.mp (Nat.find_min hex hi)
  refine ⟨k, ?_, ?_, hk_spec, hk_min⟩
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      rw [hk] at hk_spec
      simp only [Function.iterate_zero, id] at hk_spec
      linarith
    · exact hk
  · intro j hj
    exact (fi_iterates_stay h₂ hF hz j (fun i hi => hk_min i (lt_of_lt_of_le hi hj))).1

end

end Work.FatouCH
