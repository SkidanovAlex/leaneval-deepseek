import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- Membership in `symIcc` fails only above the radius (in `natAbs` form). -/
lemma lt_natAbs_of_notMem_symIcc' {L : ℕ} {x : ℤ} (hx : x ∉ Work.Peluse.symIcc L) :
    L < x.natAbs := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc, not_and_or, not_le, not_le] at hx
  have key : (L : ℤ) < |x| := by
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have h2 : ((x.natAbs : ℕ) : ℤ) = |x| := Int.natCast_natAbs x
  omega

/-- **Cauchy--Schwarz for the chirped autocorrelation.**  For a finitely supported `G` and any
shifts `a, b` and frequency `β`, the chirped correlation of the two shifts is at most the `ℓ²`-mass
of `G` to the fourth power (divided by `L⁴`, here kept outside). -/
theorem norm_tsum_shift_chirp_le {G : ℤ → ℂ} {N : ℕ} (hG : Work.Peluse.SupportIn G N)
    (a b : ℤ) (β : ℝ) :
    ‖∑' x : ℤ, G (x + a) * star (G (x + b)) *
        Complex.exp (2 * Real.pi * Complex.I * β * (x : ℂ))‖
      ≤ ∑' x : ℤ, ‖G x‖ ^ 2 := by
  classical
  set W : ℕ := N + max a.natAbs b.natAbs with hW
  have hshift : ∀ (c : ℤ) (x : ℤ), x.natAbs ≤ (x + c).natAbs + c.natAbs := by
    intro c x
    have h := Int.natAbs_add_le (x + c) (-c)
    rw [show x + c + -c = x by ring, Int.natAbs_neg] at h
    exact h
  have hvan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc W →
      G (x + a) * star (G (x + b)) * Complex.exp (2 * Real.pi * Complex.I * β * (x : ℂ)) = 0 := by
    intro x hx
    have hx' : W < x.natAbs := lt_natAbs_of_notMem_symIcc' hx
    have ha : N < (x + a).natAbs := by
      have h1 := hshift a x
      have h2 : a.natAbs ≤ max a.natAbs b.natAbs := le_max_left _ _
      have h3 : W = N + max a.natAbs b.natAbs := hW
      omega
    have : G (x + a) = 0 := hG (x + a) ha
    rw [this, zero_mul, zero_mul]
  rw [tsum_eq_sum hvan]
  have hmod : ∀ x : ℤ, ‖G (x + a) * star (G (x + b)) *
      Complex.exp (2 * Real.pi * Complex.I * β * (x : ℂ))‖ = ‖G (x+a)‖ * ‖G (x+b)‖ := by
    intro x
    rw [norm_mul, norm_mul, norm_star, Complex.norm_exp]
    simp
  have h1 : ‖∑ x ∈ Work.Peluse.symIcc W,
      G (x + a) * star (G (x + b)) * Complex.exp (2 * Real.pi * Complex.I * β * (x : ℂ))‖
      ≤ ∑ x ∈ Work.Peluse.symIcc W, ‖G (x+a)‖ * ‖G (x+b)‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
    rw [hmod]
  have hsumm : Summable (fun x : ℤ => ‖G x‖ ^ 2) :=
    summable_of_ne_finset_zero (s := Work.Peluse.symIcc N) (fun x hx => by
      rw [hG x (lt_natAbs_of_notMem_symIcc' hx)]; simp)
  have hsumma : Summable (fun x : ℤ => ‖G (x+a)‖ ^ 2) := (Equiv.addRight a).summable_iff.mpr hsumm
  have hsumb : Summable (fun x : ℤ => ‖G (x+b)‖ ^ 2) := (Equiv.addRight b).summable_iff.mpr hsumm
  have h3 : ∑ x ∈ Work.Peluse.symIcc W, ‖G (x+a)‖^2 ≤ ∑' x : ℤ, ‖G x‖^2 := by
    refine le_trans (hsumma.sum_le_tsum _ (fun i _ => by positivity)) ?_
    exact le_of_eq ((Equiv.addRight a).tsum_eq (fun y => ‖G y‖ ^ 2))
  have h4 : ∑ x ∈ Work.Peluse.symIcc W, ‖G (x+b)‖^2 ≤ ∑' x : ℤ, ‖G x‖^2 := by
    refine le_trans (hsumb.sum_le_tsum _ (fun i _ => by positivity)) ?_
    exact le_of_eq ((Equiv.addRight b).tsum_eq (fun y => ‖G y‖ ^ 2))
  have h2 : (∑ x ∈ Work.Peluse.symIcc W, ‖G (x+a)‖ * ‖G (x+b)‖)^2
      ≤ (∑' x : ℤ, ‖G x‖^2)^2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Work.Peluse.symIcc W)
      (fun x => ‖G (x+a)‖) (fun x => ‖G (x+b)‖)
    have hp : (0:ℝ) ≤ ∑' x : ℤ, ‖G x‖^2 := tsum_nonneg (fun x => by positivity)
    have hsa : (0:ℝ) ≤ ∑ x ∈ Work.Peluse.symIcc W, ‖G (x+a)‖^2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hsb : (0:ℝ) ≤ ∑ x ∈ Work.Peluse.symIcc W, ‖G (x+b)‖^2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hle := mul_le_mul h3 h4 hsb hp
    linarith [hcs, hle]
  have hfinal : ‖∑ x ∈ Work.Peluse.symIcc W,
      G (x + a) * star (G (x + b)) * Complex.exp (2 * Real.pi * Complex.I * β * (x : ℂ))‖^2
      ≤ (∑' x : ℤ, ‖G x‖^2)^2 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  have hp : (0:ℝ) ≤ ∑' x : ℤ, ‖G x‖^2 := tsum_nonneg (fun x => by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hp (by norm_num : (2:ℕ) ≠ 0)).mp hfinal

end

end Work.Peluse.Ulower
