import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory
open intervalIntegral

namespace Submission
namespace Periodic

lemma abs_sin_integral_length_pi (s : ℝ) :
    (∫ u in s..(s + Real.pi), |Real.sin u|) = 2 := by
  have hper : Function.Periodic (fun u : ℝ => |Real.sin u|) Real.pi := by
    intro x
    change |Real.sin (x + Real.pi)| = |Real.sin x|
    rw [Real.sin_add_pi, abs_neg]
  calc
    (∫ u in s..(s + Real.pi), |Real.sin u|) = ∫ u in 0..Real.pi, |Real.sin u| := by
      simpa using (hper.intervalIntegral_add_eq s 0)
    _ = ∫ u in 0..Real.pi, Real.sin u := by
      apply integral_congr
      intro u hu
      have hmem : u ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa [Set.uIcc_of_le Real.pi_pos.le] using hu
      change |Real.sin u| = Real.sin u
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hmem.1 hmem.2)]
    _ = 2 := by
      rw [integral_sin]
      norm_num

lemma abs_cos_integral_length_pi (s : ℝ) :
    (∫ u in s..(s + Real.pi), |Real.cos u|) = 2 := by
  have hper : Function.Periodic (fun u : ℝ => |Real.cos u|) Real.pi := by
    intro x
    change |Real.cos (x + Real.pi)| = |Real.cos x|
    rw [Real.cos_add_pi, abs_neg]
  calc
    (∫ u in s..(s + Real.pi), |Real.cos u|) = ∫ u in 0..Real.pi, |Real.cos u| := by
      simpa using (hper.intervalIntegral_add_eq s 0)
    _ = 2 := by
      have hrew : (∫ u in 0..Real.pi, |Real.cos u|) =
            (∫ u in 0..Real.pi, |Real.sin (u + Real.pi / 2)|) := by
          apply integral_congr
          intro u hu
          change |Real.cos u| = |Real.sin (u + Real.pi / 2)|
          rw [(Real.sin_add_pi_div_two u).symm]
      rw [hrew]
      rw [integral_comp_add_right (fun v : ℝ => |Real.sin v|) (Real.pi / 2)]
      convert abs_sin_integral_length_pi (Real.pi / 2) using 1
      ring_nf

lemma sin_arg_shift (N : ℝ) (hN : 0 < N) (t : ℝ) :
    Real.sin (2 * N * (t + Real.pi / (2 * N))) = -Real.sin (2 * N * t) := by
  have h2N : 2 * N ≠ 0 := by nlinarith
  have hp : (2 * N) * (Real.pi / (2 * N)) = Real.pi := mul_div_cancel₀ _ h2N
  have harg : 2 * N * (t + Real.pi / (2 * N)) = 2 * N * t + Real.pi := by
    calc 2 * N * (t + Real.pi / (2 * N)) = 2 * N * t + (2 * N) * (Real.pi / (2 * N)) := by ring
    _ = 2 * N * t + Real.pi := by rw [hp]
  rw [harg, Real.sin_add_pi]

lemma cos_arg_shift (N : ℝ) (hN : 0 < N) (t : ℝ) :
    Real.cos (2 * N * (t + Real.pi / (2 * N))) = -Real.cos (2 * N * t) := by
  have h2N : 2 * N ≠ 0 := by nlinarith
  have hp : (2 * N) * (Real.pi / (2 * N)) = Real.pi := mul_div_cancel₀ _ h2N
  have harg : 2 * N * (t + Real.pi / (2 * N)) = 2 * N * t + Real.pi := by
    calc 2 * N * (t + Real.pi / (2 * N)) = 2 * N * t + (2 * N) * (Real.pi / (2 * N)) := by ring
    _ = 2 * N * t + Real.pi := by rw [hp]
  rw [harg, Real.cos_add_pi]

lemma abs_sin_integral_half_period (N : ℝ) (hN : 0 < N) (x : ℝ) :
    (∫ t in x..(x + Real.pi / (2 * N)), |Real.sin (2 * N * t)|) = 1 / N := by
  have h2N : 2 * N ≠ 0 := by nlinarith
  have hderiv : ∀ y ∈ Set.uIcc x (x + Real.pi / (2 * N)),
      HasDerivAt (fun t : ℝ => 2 * N * t) (2 * N) y := by
    intro y hy
    simpa [mul_assoc] using (hasDerivAt_id y).const_mul (2 * N)
  have hsub :
      (∫ t in x..(x + Real.pi / (2 * N)), |Real.sin (2 * N * t)| * (2 * N)) =
        ∫ u in (2 * N * x)..(2 * N * (x + Real.pi / (2 * N))), |Real.sin u| := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (integral_comp_mul_deriv (f := fun t : ℝ => 2 * N * t) (f' := fun _ : ℝ => 2 * N)
        (g := fun u : ℝ => |Real.sin u|) (a := x) (b := x + Real.pi / (2 * N)) hderiv
        (by fun_prop) (Continuous.abs Real.continuous_sin))
  have hp : (2 * N) * (Real.pi / (2 * N)) = Real.pi := mul_div_cancel₀ _ h2N
  have h2Nx : 2 * N * (x + Real.pi / (2 * N)) = 2 * N * x + Real.pi := by
    calc 2 * N * (x + Real.pi / (2 * N)) = 2 * N * x + (2 * N) * (Real.pi / (2 * N)) := by ring
    _ = 2 * N * x + Real.pi := by rw [hp]
  have hJ : (∫ t in x..(x + Real.pi / (2 * N)), |Real.sin (2 * N * t)|) * (2 * N) = 2 := by
    calc
      (∫ t in x..(x + Real.pi / (2 * N)), |Real.sin (2 * N * t)|) * (2 * N)
          = ∫ t in x..(x + Real.pi / (2 * N)), |Real.sin (2 * N * t)| * (2 * N) := by
              symm
              exact integral_mul_const (2 * N) (fun t : ℝ => |Real.sin (2 * N * t)|)
      _ = 2 := by
              rw [hsub, h2Nx]
              exact abs_sin_integral_length_pi (2 * N * x)
  rw [eq_div_iff (show N ≠ 0 from ne_of_gt hN)]
  nlinarith

lemma abs_cos_integral_half_period (N : ℝ) (hN : 0 < N) (x : ℝ) :
    (∫ t in x..(x + Real.pi / (2 * N)), |Real.cos (2 * N * t)|) = 1 / N := by
  have h2N : 2 * N ≠ 0 := by nlinarith
  have hderiv : ∀ y ∈ Set.uIcc x (x + Real.pi / (2 * N)),
      HasDerivAt (fun t : ℝ => 2 * N * t) (2 * N) y := by
    intro y hy
    simpa [mul_assoc] using (hasDerivAt_id y).const_mul (2 * N)
  have hsub :
      (∫ t in x..(x + Real.pi / (2 * N)), |Real.cos (2 * N * t)| * (2 * N)) =
        ∫ u in (2 * N * x)..(2 * N * (x + Real.pi / (2 * N))), |Real.cos u| := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (integral_comp_mul_deriv (f := fun t : ℝ => 2 * N * t) (f' := fun _ : ℝ => 2 * N)
        (g := fun u : ℝ => |Real.cos u|) (a := x) (b := x + Real.pi / (2 * N)) hderiv
        (by fun_prop) (Continuous.abs Real.continuous_cos))
  have hp : (2 * N) * (Real.pi / (2 * N)) = Real.pi := mul_div_cancel₀ _ h2N
  have h2Nx : 2 * N * (x + Real.pi / (2 * N)) = 2 * N * x + Real.pi := by
    calc 2 * N * (x + Real.pi / (2 * N)) = 2 * N * x + (2 * N) * (Real.pi / (2 * N)) := by ring
    _ = 2 * N * x + Real.pi := by rw [hp]
  have hJ : (∫ t in x..(x + Real.pi / (2 * N)), |Real.cos (2 * N * t)|) * (2 * N) = 2 := by
    calc
      (∫ t in x..(x + Real.pi / (2 * N)), |Real.cos (2 * N * t)|) * (2 * N)
          = ∫ t in x..(x + Real.pi / (2 * N)), |Real.cos (2 * N * t)| * (2 * N) := by
              symm
              exact integral_mul_const (2 * N) (fun t : ℝ => |Real.cos (2 * N * t)|)
      _ = 2 := by
              rw [hsub, h2Nx]
              exact abs_cos_integral_length_pi (2 * N * x)
  rw [eq_div_iff (show N ≠ 0 from ne_of_gt hN)]
  nlinarith


private lemma half_pi_pos (N : ℝ) (hN : 0 < N) : 0 < Real.pi / (2 * N) :=
  div_pos Real.pi_pos (mul_pos zero_lt_two hN)

private lemma full_pi_pos (N : ℝ) (hN : 0 < N) : 0 < Real.pi / N := div_pos Real.pi_pos hN

private lemma half_add_half (N : ℝ) (hN : 0 < N) :
    Real.pi / (2 * N) + Real.pi / (2 * N) = Real.pi / N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  field_simp [hN0]
  ring

private lemma half_le_full (N : ℝ) (hN : 0 < N) : Real.pi / (2 * N) ≤ Real.pi / N := by
  rw [← half_add_half N hN]
  exact le_add_of_nonneg_right (half_pi_pos N hN).le

private lemma add_half_add_half (N : ℝ) (hN : 0 < N) (x : ℝ) :
    x + Real.pi / (2 * N) + Real.pi / (2 * N) = x + Real.pi / N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  field_simp [hN0]
  ring

/-- continuity of the folded integrand (h t - h (t+M)) * g t -/
private lemma continuousOn_folded (N : ℝ) (hN : 0 < N) {x : ℝ} {g h : ℝ → ℝ}
    (hg : Continuous g) (hcont : ContinuousOn h (Set.Icc x (x + Real.pi / N))) :
    ContinuousOn (fun t : ℝ => (h t - h (t + Real.pi / (2 * N))) * g t)
      (Set.Icc x (x + Real.pi / (2 * N))) := by
  have hhalf : 0 < Real.pi / (2 * N) := half_pi_pos N hN
  have hle : Real.pi / (2 * N) ≤ Real.pi / N := half_le_full N hN
  have hc_h_on : ContinuousOn h (Set.Icc x (x + Real.pi / (2 * N))) := by
    refine hcont.mono ?_
    intro y hy
    exact ⟨hy.1, by linarith [hy.2, hle]⟩
  have hc_h_shift : ContinuousOn (fun t : ℝ => h (t + Real.pi / (2 * N)))
      (Set.Icc x (x + Real.pi / (2 * N))) := by
    refine ContinuousOn.comp' (t := Set.Icc (x + Real.pi / (2 * N)) (x + Real.pi / N))
      (hcont.mono ?_) ?_ ?_
    · intro y hy
      exact ⟨by linarith [hy.1, hhalf], hy.2⟩
    · fun_prop
    · intro t ht
      constructor
      · linarith [ht.1, hhalf]
      · have ht2 : t ≤ x + Real.pi / (2 * N) := ht.2
        have hx : x + Real.pi / (2 * N) + Real.pi / (2 * N) = x + Real.pi / N :=
          add_half_add_half N hN x
        linarith [ht2, hx]
  have hc_g_on : ContinuousOn g (Set.Icc x (x + Real.pi / (2 * N))) := by
    exact (hg.continuousOn : ContinuousOn g (Set.Icc x (x + Real.pi / (2 * N))))
  exact ((hc_h_on.sub hc_h_shift).mul hc_g_on)

private lemma continuousOn_folded_abs (N : ℝ) (hN : 0 < N) {x : ℝ} {g h : ℝ → ℝ}
    (hg : Continuous g) (hcont : ContinuousOn h (Set.Icc x (x + Real.pi / N))) :
    ContinuousOn (fun t : ℝ => |(h t - h (t + Real.pi / (2 * N))) * g t|)
      (Set.Icc x (x + Real.pi / (2 * N))) := by
  exact continuous_abs.comp_continuousOn (continuousOn_folded N hN hg hcont)

/-- Bound on a single piece of length π/N, for a generic sign-alternating oscillating weight
whose absolute value integrates to 1/N over a half piece. -/
lemma piece_bound_core (N : ℝ) (hN : 0 < N) {x : ℝ} {g : ℝ → ℝ} {h : ℝ → ℝ}
    (hg : Continuous g)
    (hcont : ContinuousOn h (Set.Icc x (x + Real.pi / N)))
    (hmono : MonotoneOn h (Set.Icc x (x + Real.pi / N)))
    (hshift : ∀ t : ℝ, g (t + Real.pi / (2 * N)) = -g t)
    (habshalf : ∀ y : ℝ, (∫ u in y..(y + Real.pi / (2 * N)), |g u|) = 1 / N) :
    |∫ θ in x..(x + Real.pi / N), h θ * g θ| ≤
      (h (x + Real.pi / N) - h x) / N := by
  let G : ℝ → ℝ := fun θ => h θ * g θ
  let D : ℝ := h (x + Real.pi / N) - h x
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hhalf : 0 < Real.pi / (2 * N) := half_pi_pos N hN
  have hle : Real.pi / (2 * N) ≤ Real.pi / N := half_le_full N hN
  have hxM : x ≤ x + Real.pi / (2 * N) := by linarith
  have hxL : x ≤ x + Real.pi / N := by linarith [full_pi_pos N hN]
  have hmem_x : x ∈ Set.Icc x (x + Real.pi / N) := ⟨le_rfl, hxL⟩
  have hmem_xL : x + Real.pi / N ∈ Set.Icc x (x + Real.pi / N) := ⟨hxL, le_rfl⟩
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact sub_nonneg.mpr (hmono hmem_x hmem_xL hxL)
  have hcG_full : ContinuousOn G (Set.Icc x (x + Real.pi / N)) := by
    dsimp [G]
    exact hcont.mul (hg.continuousOn : ContinuousOn g (Set.Icc x (x + Real.pi / N)))
  have hIint1 : IntervalIntegrable G volume x (x + Real.pi / (2 * N)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxM
    exact hcG_full.mono (by intro y hy; exact ⟨hy.1, by linarith [hy.2, hle]⟩)
  have hIint2 : IntervalIntegrable G volume (x + Real.pi / (2 * N)) (x + Real.pi / N) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    exact hcG_full.mono (by intro y hy; exact ⟨by linarith [hy.1, hhalf], hy.2⟩)
  have hIint_shift : IntervalIntegrable (fun t : ℝ => G (t + Real.pi / (2 * N))) volume x
      (x + Real.pi / (2 * N)) := by
    have hc := hIint2.comp_add_left (Real.pi / (2 * N))
    have hc' : IntervalIntegrable (fun y : ℝ => G (Real.pi / (2 * N) + y)) volume x
        (x + Real.pi / (2 * N)) := by
      convert hc using 1
      · ring
      · rw [← add_half_add_half N hN x]
        ring
    simpa [add_comm] using hc'
  have hshiftG : ∀ t : ℝ, G (t + Real.pi / (2 * N)) = -h (t + Real.pi / (2 * N)) * g t := by
    intro t
    dsimp [G]
    rw [hshift]
    ring
  have hI2 : (∫ θ in (x + Real.pi / (2 * N))..(x + Real.pi / N), G θ) =
      ∫ t in x..(x + Real.pi / (2 * N)), G (t + Real.pi / (2 * N)) := by
    have hb : (∫ t in x..(x + Real.pi / (2 * N)), G (t + Real.pi / (2 * N))) =
        ∫ u in (x + Real.pi / (2 * N))..(x + Real.pi / (2 * N) + Real.pi / (2 * N)), G u := by
      simpa using (integral_comp_add_right (f := G) (d := Real.pi / (2 * N))
        (a := x) (b := x + Real.pi / (2 * N)))
    calc
      (∫ θ in (x + Real.pi / (2 * N))..(x + Real.pi / N), G θ)
          = ∫ θ in (x + Real.pi / (2 * N))..(x + Real.pi / (2 * N) + Real.pi / (2 * N)), G θ := by
              rw [← add_half_add_half N hN x]
      _ = ∫ t in x..(x + Real.pi / (2 * N)), G (t + Real.pi / (2 * N)) := hb.symm
  have hfold : (∫ θ in x..(x + Real.pi / N), G θ) =
      ∫ t in x..(x + Real.pi / (2 * N)), (h t - h (t + Real.pi / (2 * N))) * g t := by
    calc
      (∫ θ in x..(x + Real.pi / N), G θ)
          = (∫ θ in x..(x + Real.pi / (2 * N)), G θ)
              + (∫ θ in (x + Real.pi / (2 * N))..(x + Real.pi / N), G θ) := by
              symm
              exact integral_add_adjacent_intervals hIint1 hIint2
      _ = (∫ θ in x..(x + Real.pi / (2 * N)), G θ)
              + (∫ t in x..(x + Real.pi / (2 * N)), G (t + Real.pi / (2 * N))) := by
              rw [hI2]
      _ = ∫ t in x..(x + Real.pi / (2 * N)), G t + G (t + Real.pi / (2 * N)) := by
              rw [← integral_add hIint1 hIint_shift]
      _ = ∫ t in x..(x + Real.pi / (2 * N)), (h t - h (t + Real.pi / (2 * N))) * g t := by
              apply integral_congr
              intro t ht
              dsimp [G]
              rw [hshift]
              ring
  have hmonoMid : ∀ t ∈ Set.Icc x (x + Real.pi / (2 * N)),
      |h t - h (t + Real.pi / (2 * N))| ≤ D := by
    intro t ht
    have ht1 : t ∈ Set.Icc x (x + Real.pi / N) := ⟨ht.1, by linarith [ht.2, hle]⟩
    have ht2 : t + Real.pi / (2 * N) ∈ Set.Icc x (x + Real.pi / N) := by
      refine ⟨by linarith [ht.1, hhalf], ?_⟩
      have hx : x + Real.pi / (2 * N) + Real.pi / (2 * N) = x + Real.pi / N :=
        add_half_add_half N hN x
      linarith [ht.2, hx]
    have h_le : h t ≤ h (t + Real.pi / (2 * N)) := hmono ht1 ht2 (by linarith [hhalf])
    have h_le2 : h (t + Real.pi / (2 * N)) - h t ≤ D := by
      dsimp [D]
      have h1 : h (t + Real.pi / (2 * N)) ≤ h (x + Real.pi / N) :=
        hmono ht2 hmem_xL ht2.2
      have h2 : h x ≤ h t := hmono hmem_x ht1 ht1.1
      exact sub_le_sub h1 h2
    rw [show h t - h (t + Real.pi / (2 * N)) = -(h (t + Real.pi / (2 * N)) - h t) by ring]
    rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr h_le)]
    exact h_le2
  have hpoint : ∀ t ∈ Set.Icc x (x + Real.pi / (2 * N)),
      |(h t - h (t + Real.pi / (2 * N))) * g t| ≤ D * |g t| := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hmonoMid t ht) (abs_nonneg (g t))
  have hI_W : IntervalIntegrable (fun t : ℝ =>
      |(h t - h (t + Real.pi / (2 * N))) * g t|) volume x (x + Real.pi / (2 * N)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxM
    exact continuousOn_folded_abs N hN hg hcont
  have hI_Dg : IntervalIntegrable (fun t : ℝ => D * |g t|) volume x (x + Real.pi / (2 * N)) := by
    exact (continuous_const.mul hg.abs).intervalIntegrable x (x + Real.pi / (2 * N))
  calc
    |∫ θ in x..(x + Real.pi / N), h θ * g θ|
        = |∫ θ in x..(x + Real.pi / N), G θ| := by simp [G]
    _ = |∫ t in x..(x + Real.pi / (2 * N)), (h t - h (t + Real.pi / (2 * N))) * g t| := by
        rw [hfold]
    _ ≤ ∫ t in x..(x + Real.pi / (2 * N)), |(h t - h (t + Real.pi / (2 * N))) * g t| :=
        abs_integral_le_integral_abs hxM
    _ ≤ ∫ t in x..(x + Real.pi / (2 * N)), D * |g t| := by
        exact integral_mono_on hxM hI_W hI_Dg hpoint
    _ = D * (∫ t in x..(x + Real.pi / (2 * N)), |g t|) := by
        rw [intervalIntegral.integral_const_mul D (fun t : ℝ => |g t|)]
    _ = D * (1 / N) := by rw [habshalf x]
    _ = (h (x + Real.pi / N) - h x) / N := by
        dsimp [D]
        field_simp [hN0]

private lemma cast_succ_mul (m : ℕ) (L : ℝ) : ((m + 1 : ℕ) : ℝ) * L = (m : ℝ) * L + L := by
  rw [Nat.cast_add, Nat.cast_one]
  ring

private lemma cast_nat_nonneg (m : ℕ) : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)

/-- Telescoping bound: if the interval has length `m * L` (L = π/N) then the total
integral is at most (h(end) - h(start))/N. -/
private lemma iterate_bound_core (N : ℝ) (hN : 0 < N) (L : ℝ) (hL : L = Real.pi / N)
    {g : ℝ → ℝ} {h : ℝ → ℝ} {A : ℝ} (hg : Continuous g)
    (hshift : ∀ t : ℝ, g (t + Real.pi / (2 * N)) = -g t)
    (habshalf : ∀ y : ℝ, (∫ u in y..(y + Real.pi / (2 * N)), |g u|) = 1 / N) :
    ∀ m : ℕ,
      ContinuousOn h (Set.Icc A (A + (m : ℝ) * L)) →
      MonotoneOn h (Set.Icc A (A + (m : ℝ) * L)) →
      |∫ θ in A..(A + (m : ℝ) * L), h θ * g θ| ≤ (h (A + (m : ℝ) * L) - h A) / N := by
  intro m
  induction m with
  | zero =>
      intro hcont hmono
      simp
  | succ m ih =>
      intro hcont hmono
      have hL0 : 0 ≤ L := by
        rw [hL]
        exact (full_pi_pos N hN).le
      have hmR : 0 ≤ (m : ℝ) := cast_nat_nonneg m
      let xm : ℝ := A + (m : ℝ) * L
      have hxm_end : A + ((m + 1 : ℕ) : ℝ) * L = xm + L := by
        dsimp [xm]
        rw [cast_succ_mul]
        ring
      have hxmle : xm ≤ A + ((m + 1 : ℕ) : ℝ) * L := by
        rw [hxm_end]
        linarith
      have hmL_nonneg : 0 ≤ (m : ℝ) * L := mul_nonneg hmR hL0
      have hA_xm : A ≤ xm := by
        dsimp [xm]
        linarith
      have hsub_m : Set.Icc A xm ⊆ Set.Icc A (A + ((m + 1 : ℕ) : ℝ) * L) := by
        intro y hy
        constructor
        · exact hy.1
        · linarith [hy.2, hxmle]
      have hsub_piece : Set.Icc xm (xm + Real.pi / N) ⊆ Set.Icc A (A + ((m + 1 : ℕ) : ℝ) * L) := by
        intro y hy
        constructor
        · linarith [hy.1, hA_xm]
        · rw [← hL] at hy
          rw [hxm_end]
          exact hy.2
      have hcont_m : ContinuousOn h (Set.Icc A xm) := hcont.mono hsub_m
      have hmono_m : MonotoneOn h (Set.Icc A xm) := hmono.mono hsub_m
      have hcont2 : ContinuousOn h (Set.Icc xm (xm + Real.pi / N)) := hcont.mono hsub_piece
      have hmono2 : MonotoneOn h (Set.Icc xm (xm + Real.pi / N)) := hmono.mono hsub_piece
      have hbd1 : |∫ θ in A..xm, h θ * g θ| ≤ (h xm - h A) / N := by
        simpa [xm] using (ih hcont_m hmono_m)
      have hpb_raw := piece_bound_core N hN (x := xm) (g := g) (h := h) hg hcont2 hmono2 hshift habshalf
      have hpb : |∫ θ in xm..(xm + L), h θ * g θ| ≤ (h (xm + L) - h xm) / N := by
        rw [← hL] at hpb_raw
        exact hpb_raw
      have hbd2 : |∫ θ in xm..(A + ((m + 1 : ℕ) : ℝ) * L), h θ * g θ| ≤
          (h (A + ((m + 1 : ℕ) : ℝ) * L) - h xm) / N := by
        rw [hxm_end]
        exact hpb
      have hGcont : ContinuousOn (fun θ : ℝ => h θ * g θ) (Set.Icc A (A + ((m + 1 : ℕ) : ℝ) * L)) := by
        exact hcont.mul (hg.continuousOn : ContinuousOn g (Set.Icc A (A + ((m + 1 : ℕ) : ℝ) * L)))
      have hInt1 : IntervalIntegrable (fun θ : ℝ => h θ * g θ) volume A xm := by
        apply ContinuousOn.intervalIntegrable_of_Icc hA_xm
        exact hGcont.mono hsub_m
      have hInt2 : IntervalIntegrable (fun θ : ℝ => h θ * g θ) volume xm (A + ((m + 1 : ℕ) : ℝ) * L) := by
        apply ContinuousOn.intervalIntegrable_of_Icc hxmle
        exact hGcont.mono (by intro y hy; exact ⟨by linarith [hy.1, hA_xm], hy.2⟩)
      have hsplit : (∫ θ in A..(A + ((m + 1 : ℕ) : ℝ) * L), h θ * g θ) =
          (∫ θ in A..xm, h θ * g θ) + (∫ θ in xm..(A + ((m + 1 : ℕ) : ℝ) * L), h θ * g θ) := by
        exact (integral_add_adjacent_intervals hInt1 hInt2).symm
      calc
        |∫ θ in A..(A + ((m + 1 : ℕ) : ℝ) * L), h θ * g θ|
            ≤ |∫ θ in A..xm, h θ * g θ| + |∫ θ in xm..(A + ((m + 1 : ℕ) : ℝ) * L), h θ * g θ| := by
                rw [hsplit]
                exact abs_add_le _ _
        _ ≤ (h xm - h A) / N + (h (A + ((m + 1 : ℕ) : ℝ) * L) - h xm) / N := by
                exact add_le_add hbd1 hbd2
        _ = (h (A + ((m + 1 : ℕ) : ℝ) * L) - h A) / N := by
                have hN0 : N ≠ 0 := ne_of_gt hN
                field_simp [hN0]
                ring

/-- Outer driver: monotone h, generic kernel g with shift and half-period abs facts. -/
private lemma kernel_bound_monotone (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hmono : MonotoneOn h (Set.Icc a b))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hshift : ∀ t : ℝ, g (t + Real.pi / (2 * (n : ℝ))) = -g t)
    (habshalf : ∀ y : ℝ, (∫ u in y..(y + Real.pi / (2 * (n : ℝ))), |g u|) = 1 / (n : ℝ))
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * g θ| ≤ |h b - h a| / n := by
  rcases hmul with ⟨m, hm⟩
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnnz : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hbL : b - a = (m : ℝ) * (Real.pi / N) := by
    dsimp [N]
    rw [hm]
    field_simp [hnnz]
  have hab_mL : a + (m : ℝ) * (Real.pi / N) = b := by
    linarith
  have hcont2 : ContinuousOn h (Set.Icc a (a + (m : ℝ) * (Real.pi / N))) := by
    rw [hab_mL]
    exact hcont
  have hmono2 : MonotoneOn h (Set.Icc a (a + (m : ℝ) * (Real.pi / N))) := by
    rw [hab_mL]
    exact hmono
  have hbd := iterate_bound_core N hN (Real.pi / N) rfl (g := g) (h := h) (A := a)
    hg hshift habshalf m hcont2 hmono2
  have hmon : h a ≤ h b := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have habs : |h b - h a| = h b - h a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmon)]
  rw [hab_mL] at hbd
  rw [← habs] at hbd
  simpa [N] using hbd

lemma monotone_sin_integral_bound (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hmono : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h x ≤ h y)
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * θ)| ≤ |h b - h a| / n := by
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact kernel_bound_monotone n hn hab h hcont (by
    intro x hx y hy hxy
    exact hmono hx hy hxy) (fun θ : ℝ => Real.sin (2 * N * θ))
    (by fun_prop)
    (fun t => sin_arg_shift N hN t)
    (fun y => abs_sin_integral_half_period N hN y)
    hmul

lemma monotone_cos_integral_bound (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hmono : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h x ≤ h y)
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * Real.cos (2 * (n : ℝ) * θ)| ≤ |h b - h a| / n := by
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact kernel_bound_monotone n hn hab h hcont (by
    intro x hx y hy hxy
    exact hmono hx hy hxy) (fun θ : ℝ => Real.cos (2 * N * θ))
    (by fun_prop)
    (fun t => cos_arg_shift N hN t)
    (fun y => abs_cos_integral_half_period N hN y)
    hmul



lemma antitone_sin_integral_bound (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hanti : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h y ≤ h x)
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * θ)| ≤ |h b - h a| / n := by
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcont_neg : ContinuousOn (fun θ : ℝ => -h θ) (Set.Icc a b) := hcont.neg
  have hmono_neg : MonotoneOn (fun θ : ℝ => -h θ) (Set.Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hanti (x := x) (y := y) hx hy hxy)
  have hbd := kernel_bound_monotone n hn hab (fun θ : ℝ => -h θ) hcont_neg hmono_neg
    (fun θ : ℝ => Real.sin (2 * N * θ)) (by fun_prop)
    (fun t => sin_arg_shift N hN t)
    (fun y => abs_sin_integral_half_period N hN y)
    hmul
  have hx : (∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * θ)) =
      - (∫ θ in a..b, (-h θ) * Real.sin (2 * (n : ℝ) * θ)) := by
    have hiv := intervalIntegral.integral_neg (μ := volume)
      (f := fun θ : ℝ => (-h θ) * Real.sin (2 * (n : ℝ) * θ)) (a := a) (b := b)
    rw [← hiv]
    apply integral_congr
    intro θ hθ
    ring
  rw [hx, abs_neg]
  have hmon : h b ≤ h a := hanti (x := a) (y := b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have h1 : (-h b) - (-h a) = -(h b - h a) := by ring
  calc
    |∫ θ in a..b, (-h θ) * Real.sin (2 * (n : ℝ) * θ)| ≤ |(-h b) - (-h a)| / n := hbd
    _ = |h b - h a| / n := by rw [h1, abs_neg]

lemma const_sin_integral_bound (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b)
    (c : ℝ) (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, c * Real.sin (2 * (n : ℝ) * θ)| ≤ 0 := by
  let N : ℝ := (n : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmono_c : MonotoneOn (fun _ : ℝ => c) (Set.Icc a b) := by
    intro x hx y hy hxy
    rfl
  have hbd := kernel_bound_monotone n hn hab (fun _ : ℝ => c) continuousOn_const hmono_c
    (fun θ : ℝ => Real.sin (2 * N * θ)) (by fun_prop)
    (fun t => sin_arg_shift N hN t)
    (fun y => abs_sin_integral_half_period N hN y)
    hmul
  simpa using hbd


end Periodic
end Submission
