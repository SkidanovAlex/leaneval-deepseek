import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.mem_Dst_of_F_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

set_option maxHeartbeats 800000

open Work.PARIMPL (ParNormal Ft)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## `Work.FlowerGlue2.exists_back_entry`

The entry statement (S3) of `Submission/Work/NOTES_LEAD_mandelbar_gaps3.md` §1.2: along a
*backward* `Ft c₀`-orbit `z_n = Ψ (u - n)` which tends to `d.z₁` at the far left, the Stolz
petal `Dst P R₂` is entered after finitely many steps and is *upward closed* in `n`.

The proof is the one sketched in the design note:

* `Work.FlowerGlue2.w0_step` gives, at every point of a fixed small chart ball, the one-step
  estimate `w0 (Ft z) = w0 z + 1 + e` with `‖e‖ ≤ C ‖z - d.z₁‖ ≤ 1/4`; hence going backwards
  (`z_{k+1} ↦ z_k = Ft z_{k+1}`) the real part of `w0` drops by at least `3/4` per step and the
  imaginary part grows by at most `1/4` per step;
* `Work.FlowerGlue2.mem_Dst_of_F_mem` is the *upward closure*: inside the small ball, a point
  whose image lies in `Dst P R` is itself in `Dst P R`.

`hsmall` supplies a *uniform* radius (`ε := r`, independently of `u`), which is what makes the
threshold `N₀` uniform in `u`: for `Re u < -N₀` **every** backward iterate `Ψ (u - n)`,
`n : ℕ`, lies in the punctured chart ball of radius `r`.  The step count at which `Dst P R₂`
is entered then depends on `u` (through `‖w0 (Ψ u)‖`), but the threshold `N₀` does not. -/

/-- **The one-step backward estimate of the `c₀`-chart.**  In the small ball around the parabolic
point the backward chart step is a translation by `-1` up to an error of modulus `≤ 1/4`: the
real part of `w0` drops by at least `3/4` and the imaginary part grows by at most `1/4` in
absolute value. -/
private theorem back_step (P : ParNormal d) (hτ : P.h c₀ 0 = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < r →
      Ft c₀ z ≠ d.z₁ ∧
      (w0 P z).re ≤ (w0 P (Ft c₀ z)).re - 3 / 4 ∧
      |(w0 P z).im| ≤ |(w0 P (Ft c₀ z)).im| + 1 / 4 := by
  obtain ⟨r₁, hr₁, C, hC, hstep⟩ := w0_step P hτ
  refine ⟨min r₁ (1 / (4 * (C + 1))), lt_min hr₁ (by positivity), ?_⟩
  intro z hz hzd
  have hzd₁ : ‖z - d.z₁‖ < r₁ := lt_of_lt_of_le hzd (min_le_left _ _)
  have hzd₂ : ‖z - d.z₁‖ < 1 / (4 * (C + 1)) := lt_of_lt_of_le hzd (min_le_right _ _)
  obtain ⟨hFtne, herr⟩ := hstep z hz hzd₁
  have hnorm : C * ‖z - d.z₁‖ ≤ 1 / 4 := by
    calc C * ‖z - d.z₁‖ ≤ C * (1 / (4 * (C + 1))) :=
          mul_le_mul_of_nonneg_left (le_of_lt hzd₂) hC
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (C + 1))]
          linarith
  set e : ℂ := w0 P (Ft c₀ z) - w0 P z - 1 with hedef
  have henorm : ‖e‖ ≤ 1 / 4 := by rw [hedef]; exact le_trans herr hnorm
  have hmain : w0 P z = w0 P (Ft c₀ z) - 1 - e := by rw [hedef]; ring
  have hre : (w0 P z).re = (w0 P (Ft c₀ z)).re - 1 - e.re := by rw [hmain]; simp
  have him : (w0 P z).im = (w0 P (Ft c₀ z)).im - e.im := by rw [hmain]; simp
  have here : -(1 / 4) ≤ e.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm e)).1
    linarith
  have heim : |e.im| ≤ 1 / 4 := le_trans (Complex.abs_im_le_norm e) henorm
  refine ⟨hFtne, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [him]
    calc |(w0 P (Ft c₀ z)).im - e.im| ≤ |(w0 P (Ft c₀ z)).im| + |e.im| := abs_sub _ _
      _ ≤ |(w0 P (Ft c₀ z)).im| + 1 / 4 := by linarith

theorem exists_back_entry {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1) {Ψ : ℂ → ℂ}
    (hsh : ∀ w : ℂ, Ψ (w + 1) = Work.PARIMPL.Ft c₀ (Ψ w))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R →
      Ψ w ≠ d.z₁ ∧ ‖Ψ w - d.z₁‖ < ε) (R₂ : ℝ) :
    ∃ N₀ : ℝ, ∀ u : ℂ, u.re < -N₀ →
      (∃ n : ℕ, Ψ (u - (n : ℂ)) ∈ Work.FlowerGlue2.Dst P R₂) ∧
      ∀ n : ℕ, Ψ (u - (n : ℂ)) ∈ Work.FlowerGlue2.Dst P R₂ →
        Ψ (u - ((n : ℂ) + 1)) ∈ Work.FlowerGlue2.Dst P R₂ := by
  obtain ⟨r₂, hr₂, hbwd⟩ := mem_Dst_of_F_mem P hτ
  obtain ⟨r₁, hr₁, hstep₁⟩ := back_step P hτ
  set r : ℝ := min r₁ r₂ with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact lt_min hr₁ hr₂
  have hrr₁ : r ≤ r₁ := by rw [hrdef]; exact min_le_left _ _
  have hrr₂ : r ≤ r₂ := by rw [hrdef]; exact min_le_right _ _
  obtain ⟨R₀, hR₀⟩ := hsmall r hrpos
  refine ⟨R₀, ?_⟩
  intro u hu
  -- every backward iterate lies in the punctured ball of radius `r`
  have hfar : ∀ n : ℕ, (u - (n : ℂ)).re < -R₀ := by
    intro n
    rw [Complex.sub_re, Complex.natCast_re]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne : ∀ n : ℕ, Ψ (u - (n : ℂ)) ≠ d.z₁ := fun n => (hR₀ _ (hfar n)).1
  have hcl : ∀ n : ℕ, ‖Ψ (u - (n : ℂ)) - d.z₁‖ < r := fun n => (hR₀ _ (hfar n)).2
  have hshift_u : ∀ n : ℕ, Ft c₀ (Ψ (u - ((n : ℂ) + 1))) = Ψ (u - (n : ℂ)) := by
    intro n
    have h := hsh (u - ((n : ℂ) + 1))
    have h2 : u - ((n : ℂ) + 1) + 1 = u - (n : ℂ) := by ring
    rw [h2] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · -- (a) some backward iterate lands in the Stolz petal: the chart real part decreases
    -- linearly while the imaginary part grows at most sublinearly, so the Stolz ratio tends to 0
    have key : ∀ z : ℕ → ℂ, (∀ n : ℕ, z n ≠ d.z₁) → (∀ n : ℕ, ‖z n - d.z₁‖ < r) →
        (∀ n : ℕ, Ft c₀ (z (n + 1)) = z n) → ∃ n : ℕ, z n ∈ Dst P R₂ := by
      intro z hzne hzcl hshz
      have hstep_re : ∀ n : ℕ, (w0 P (z (n + 1))).re ≤ (w0 P (z n)).re - 3 / 4 := by
        intro n
        have h := (hstep₁ (z (n + 1)) (hzne (n + 1)) (lt_of_lt_of_le (hzcl (n + 1)) hrr₁)).2.1
        rw [hshz n] at h
        exact h
      have hstep_im : ∀ n : ℕ, |(w0 P (z (n + 1))).im| ≤ |(w0 P (z n)).im| + 1 / 4 := by
        intro n
        have h := (hstep₁ (z (n + 1)) (hzne (n + 1)) (lt_of_lt_of_le (hzcl (n + 1)) hrr₁)).2.2
        rw [hshz n] at h
        exact h
      have hRe : ∀ n : ℕ, (w0 P (z n)).re ≤ (w0 P (z 0)).re - 3 / 4 * (n : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ k ih =>
            have h1 := hstep_re k
            have h2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
            rw [h2]
            linarith
      have hIm : ∀ n : ℕ, |(w0 P (z n)).im| ≤ |(w0 P (z 0)).im| + 1 / 4 * (n : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ k ih =>
            have h1 := hstep_im k
            have h2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
            rw [h2]
            linarith
      obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, 4 * ‖w0 P (z 0)‖ + 4 * max R₂ 0 + 8 ≤ (n : ℝ) :=
        ⟨Nat.ceil (4 * ‖w0 P (z 0)‖ + 4 * max R₂ 0 + 8), Nat.le_ceil _⟩
      refine ⟨n₀, ?_⟩
      rw [mem_Dst]
      refine ⟨hzne n₀, ?_, ?_⟩
      · have h1 := hRe n₀
        have h2 : (w0 P (z 0)).re ≤ ‖w0 P (z 0)‖ := Complex.re_le_norm _
        have h3 : R₂ ≤ max R₂ 0 := le_max_left _ _
        have h4 : (0 : ℝ) ≤ max R₂ 0 := le_max_right _ _
        have h5 : (0 : ℝ) ≤ ‖w0 P (z 0)‖ := norm_nonneg _
        linarith
      · have h1 := hIm n₀
        have h2 : |(w0 P (z 0)).im| ≤ ‖w0 P (z 0)‖ := Complex.abs_im_le_norm _
        have h3 := hRe n₀
        have h4 : (w0 P (z 0)).re ≤ ‖w0 P (z 0)‖ := Complex.re_le_norm _
        have h5 : (0 : ℝ) ≤ ‖w0 P (z 0)‖ := norm_nonneg _
        have h6 : (0 : ℝ) ≤ max R₂ 0 := le_max_right _ _
        linarith
    refine key (fun n => Ψ (u - (n : ℂ))) hne hcl ?_
    intro n
    simpa only [Nat.cast_succ] using hshift_u n
  · -- (b) upward closure: `mem_Dst_of_F_mem` at the point `z_{n+1}`, whose image is `z_n`
    intro n hn
    have hz : Ψ (u - ((n : ℂ) + 1)) ≠ d.z₁ := by
      simpa only [Nat.cast_succ] using hne (n + 1)
    have hzd : ‖Ψ (u - ((n : ℂ) + 1)) - d.z₁‖ < r₂ :=
      lt_of_lt_of_le (by simpa only [Nat.cast_succ] using hcl (n + 1)) hrr₂
    exact (hbwd R₂ (Ψ (u - ((n : ℂ) + 1))) hz hzd (by rw [hshift_u n]; exact hn)).1

end Work.FlowerGlue2
