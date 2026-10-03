import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Phi_dev_geom
import Submission.Work.Pert.pert2v2.fatou_proper_im

/-!
# `Work.Pert.pert2v2.GatePreimageReBound.walk_trace`

**The trace of the forward walk in the lower gate.**  Let `F` be a near-translation on the gate
`Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)`, i.e. `‖F w - (w + 1)‖ ≤ 1/32` on `Qm Ξ α`, and let `z ∈ Qm Ξ α`
satisfy the two "height" hypotheses

* `hC : -z.re < z.im + C`, i.e. `z.re > -z.im - C`;
* `hA : max (Ξ + 17/16) (11/8) ≤ (30/31) z.im - C/31`.

Then, as long as the orbit stays in the open left half plane `{re < 0}`, it stays inside the gate and
advances by at least `31/32` in the real part and at most `1/32` downward in the imaginary part
per step:

`∀ j, (∀ i < j, (F^[i] z).re < 0) → (∀ i ≤ j, F^[i] z ∈ Qm Ξ α) ∧
  z.re + (31/32) j ≤ (F^[j] z).re ∧ z.im - j/32 ≤ (F^[j] z).im`.

## The argument

Write `w_i = F^[i] z`, `re = z.re`, `im = z.im`, and `κ = (30/31) im - C/31 ≥ max (Ξ+17/16) (11/8)`.
The near-translation defect gives, at every visited point `w ∈ Qm Ξ α`,

`(F w).re ∈ [w.re + 31/32, w.re + 33/32]`,  `|(F w).im - w.im| ≤ 1/32`,

so by induction on `i ≤ j`

* `re_i ≥ re + (31/32) i` and `|im_i - im| ≤ i/32`.

The *lower* cone inequality `Ξ - Re(1/α) - |Im w + Im(1/α)| < Re w` is transported from `z` by the
Lipschitz estimate `|Im w_i + Im(1/α)| ≤ |Im z + Im(1/α)| + i/32` — the gain `31/32` of the real
part pays for the loss `1/32` of the imaginary part, and the inequality is strict at `i = 0`.

The *upper* cone inequality `Re w_i < |Im w_i| - Ξ` is the only place where the walk has to be
short: while `re_i < 0` the two estimates give `(31/32) i < -re < im + C`, whence `i ≤ j` and

`im_i ≥ im - i/32 > im - (im + C)/31 = κ - 1/32 ≥ Ξ + 33/32`.

So `im_i > 0` and `im_i - Ξ > 33/32 > re_{i+1} ≥ ...`; for the last index `j` (where `re_j < 0` is
no longer assumed) one uses instead `re_j ≤ re_{j-1} + 33/32 < 33/32`, so the same conclusion
`re_j < 33/32 < im_j - Ξ` holds.
-/

namespace Work.Pert.pert2v2.GatePreimageReBound

/-- **One step of a near-translation on the gate.**  At a point `w` of the gate the map moves the
real part by `[31/32, 33/32]` and the imaginary part by at most `1/32` (in absolute value). -/
theorem walk_trace_step_bounds {Ξ : ℝ} {α : ℂ} {F : ℂ → ℂ} {w : ℂ}
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α)) (hw : w ∈ Work.Pert.Qm Ξ α) :
    w.re + 31/32 ≤ (F w).re ∧ (F w).re ≤ w.re + 33/32 ∧ |(F w).im - w.im| ≤ 1/32 := by
  obtain ⟨-, h⟩ := hNT
  obtain ⟨h1, -⟩ := h w hw
  have hsplit : F w - w - 1 = F w - (w + 1) := by ring
  have hnorm : ‖F w - w - 1‖ ≤ (1:ℝ)/32 := by rw [hsplit]; exact h1
  have hre : |(F w - w - 1).re| ≤ (1:ℝ)/32 := le_trans (Complex.abs_re_le_norm _) hnorm
  have him : |(F w - w - 1).im| ≤ (1:ℝ)/32 := le_trans (Complex.abs_im_le_norm _) hnorm
  have hre' : (F w - w - 1).re = (F w).re - w.re - 1 := by
    simp only [Complex.sub_re, Complex.one_re]
  have him' : (F w - w - 1).im = (F w).im - w.im := by
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
  rw [hre'] at hre
  rw [him'] at him
  obtain ⟨a, b⟩ := abs_le.mp hre
  exact ⟨by linarith, by linarith, him⟩

/-- **Transport of the lower cone inequality.**  If `w` is `i` steps ahead of `z` in the sense of
the estimates `Re w ≥ Re z + (31/32) i`, `|Im w - Im z| ≤ i/32`, then the lower cone inequality at
`z` implies the one at `w`. -/
theorem walk_trace_lower_cone {Ξ : ℝ} {α : ℂ} {z w : ℂ} {n : ℕ}
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hre : z.re + (31/32 : ℝ) * (n : ℝ) ≤ w.re)
    (him : |w.im - z.im| ≤ (n : ℝ) / 32) :
    Ξ - (1/α).re - |w.im + (1/α).im| < w.re := by
  have hz1 : Ξ - (1/α).re - |z.im + (1/α).im| < z.re := Work.Pert.Qm_mem_iff.mp hz |>.1
  have h1 : |z.im + (1/α).im| ≤ |w.im + (1/α).im| + (n:ℝ)/32 := by
    have h2 : z.im + (1/α).im = (w.im + (1/α).im) + (z.im - w.im) := by ring
    calc |z.im + (1/α).im| = |(w.im + (1/α).im) + (z.im - w.im)| := by rw [h2]
      _ ≤ |w.im + (1/α).im| + |z.im - w.im| := abs_add_le _ _
      _ ≤ |w.im + (1/α).im| + (n:ℝ)/32 := by
          have h3 : |z.im - w.im| = |w.im - z.im| := abs_sub_comm _ _
          rw [h3]; linarith
  have h2 : (n:ℝ)/32 ≤ (31/32:ℝ) * (n:ℝ) := by
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith [hn]
  linarith

/-- **The upper cone inequality under a height bound.**  A point with `Re w < 33/32` and
`Im w > max (Ξ + 33/32) (43/32)` satisfies `Re w < |Im w| - Ξ`. -/
theorem walk_trace_upper_cone {Ξ : ℝ} {w : ℂ}
    (hre : w.re < 33/32) (him : max (Ξ + 33/32) (43/32) < w.im) :
    w.re < |w.im| - Ξ := by
  have h1 : Ξ + 33/32 < w.im := lt_of_le_of_lt (le_max_left _ _) him
  have h2 : (43/32:ℝ) < w.im := lt_of_le_of_lt (le_max_right _ _) him
  have h3 : 0 < w.im := by linarith
  rw [abs_of_pos h3]
  linarith

theorem walk_trace {Ξ : ℝ} {α : ℂ} {C : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (hz : z ∈ Work.Pert.Qm Ξ α) (hC : -z.re < z.im + C)
    (hA : max (Ξ + 17 / 16) (11 / 8) ≤ (30 / 31 : ℝ) * z.im - C / 31) :
    ∀ j : ℕ, (∀ i < j, (F^[i] z).re < 0) →
      (∀ i ≤ j, (F^[i] z) ∈ Work.Pert.Qm Ξ α) ∧
      z.re + (31 / 32 : ℝ) * (j : ℝ) ≤ (F^[j] z).re ∧
      z.im - (j : ℝ) / 32 ≤ (F^[j] z).im := by
  intro j hj
  have hC' : -z.im - C < z.re := by linarith
  have hA1 : Ξ + 17/16 ≤ (30/31:ℝ) * z.im - C/31 := le_trans (le_max_left _ _) hA
  have hA2 : (11/8:ℝ) ≤ (30/31:ℝ) * z.im - C/31 := le_trans (le_max_right _ _) hA
  -- the trace of the walk up to `j`, as a strong induction invariant
  have key : ∀ n : ℕ, (∀ i < n, (F^[i] z).re < 0) → ∀ i ≤ n,
      (F^[i] z) ∈ Work.Pert.Qm Ξ α ∧
      z.re + (31/32:ℝ) * (i:ℝ) ≤ (F^[i] z).re ∧
      |(F^[i] z).im - z.im| ≤ (i:ℝ)/32 := by
    intro n
    induction n with
    | zero =>
      intro _ i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact ⟨by simpa using hz, by simp, by simp⟩
    | succ n ih =>
      intro hn i hi
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact ih (fun k hk => hn k (by omega)) i (by omega)
      · subst heq
        obtain ⟨hmemN, hreN, himN⟩ := ih (fun k hk => hn k (by omega)) n le_rfl
        have hneg : (F^[n] z).re < 0 := hn n (by omega)
        obtain ⟨s1, s2, s3⟩ := walk_trace_step_bounds hNT hmemN
        have hsucc : F^[n+1] z = F (F^[n] z) := Function.iterate_succ_apply' F n z
        have s1' : (F^[n] z).re + 31/32 ≤ (F^[n+1] z).re := by rw [hsucc]; exact s1
        have s2' : (F^[n+1] z).re ≤ (F^[n] z).re + 33/32 := by rw [hsucc]; exact s2
        have hcast : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by push_cast; ring
        -- the two estimates at `n+1`
        have hreS : z.re + (31/32:ℝ) * ((n+1:ℕ):ℝ) ≤ (F^[n+1] z).re := by
          rw [hcast]; linarith
        have himS : |(F^[n+1] z).im - z.im| ≤ ((n+1:ℕ):ℝ)/32 := by
          have s3' : |(F^[n+1] z).im - (F^[n] z).im| ≤ (1:ℝ)/32 := by rw [hsucc]; exact s3
          calc |(F^[n+1] z).im - z.im|
              = |((F^[n+1] z).im - (F^[n] z).im) + ((F^[n] z).im - z.im)| := by ring_nf
            _ ≤ |(F^[n+1] z).im - (F^[n] z).im| + |(F^[n] z).im - z.im| := abs_add_le _ _
            _ ≤ (1:ℝ)/32 + (n:ℝ)/32 := by linarith
            _ = ((n+1:ℕ):ℝ)/32 := by rw [hcast]; ring
        -- the walk hypothesis bounds `n` against the initial height
        have hbound : (31/32:ℝ) * (n:ℝ) < z.im + C := by linarith
        have hgt : ((30/31:ℝ) * z.im - C/31) - 1/32 < (F^[n+1] z).im := by
          have h1 : z.im - ((n+1:ℕ):ℝ)/32 ≤ (F^[n+1] z).im := by
            have := (abs_le.mp himS).1; linarith
          have h2 : (n:ℝ)/32 < (z.im + C)/31 := by linarith
          have h4 : (30/31:ℝ) * z.im - C/31 = z.im - (z.im + C)/31 := by ring
          rw [h4]; linarith
        have hgt2 : max (Ξ + 33/32) (43/32) < (F^[n+1] z).im := by
          refine max_lt ?_ ?_
          · linarith [hA1]
          · linarith [hA2]
        have hreS' : (F^[n+1] z).re < 33/32 := by linarith
        -- membership at `n+1` is now the two cone inequalities
        exact ⟨Work.Pert.Qm_mem_iff.mpr
            ⟨walk_trace_lower_cone hz hreS himS, walk_trace_upper_cone hreS' hgt2⟩, hreS, himS⟩
  have hkey := key j hj
  refine ⟨fun i hi => (hkey i hi).1, (hkey j le_rfl).2.1, ?_⟩
  have := (abs_le.mp (hkey j le_rfl).2.2).1
  linarith

end Work.Pert.pert2v2.GatePreimageReBound
