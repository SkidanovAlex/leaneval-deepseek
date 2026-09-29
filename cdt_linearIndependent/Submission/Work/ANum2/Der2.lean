import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.slit_facts

/-!
# Second-derivative data for the slit map

With `Q r z = (1+r)² - 2(1-6r+r²) z + (1+r)² z²`, `S = √Q` (principal square root),
`P r z = (1+r)² - 2(r-1)² z + (1+r)² z²` and `N = P + (1+r)(z-1)S`, the slit map is
`slit r z = N(z)/(8rz)` (for `z ≠ 0`, and both sides vanish at `0`).  This module fixes the
notation and the closed forms of the first and second derivatives

  `N'  = -2(r-1)² + 2(1+r)²z + (1+r)S + (1+r)(z-1)Q'/(2S)`,
  `N'' = 2(1+r)² + (1+r)Q'/S + (1+r)(z-1)(2QQ'' - Q'²)/(4S³)`,
  `slit'' = (N''z² - 2N'z + 2N)/(8rz³)`,

so that the analytic identity `slit'' = (N''z² - 2N'z + 2N)/(8rz³)` and the magnitude bounds on
the disc can be stated and proved downstream.

All the functions below are built with *pointwise* operations on `ℂ → ℂ` (or as compositions),
so that the `HasDerivAt` combinators apply without any lambda bookkeeping.
-/

namespace Work.ANum2

open Submission.CDTPlan Complex

noncomputable section

/-- The constant function. -/
abbrev K (c : ℂ) : ℂ → ℂ := fun _ => c

/-- `Q r z = (1+r)² - 2(1-6r+r²) z + (1+r)² z²`. -/
def Qf (r : ℝ) : ℂ → ℂ :=
  K ((1 + (r : ℂ)) ^ 2) - K (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * id
    + K ((1 + (r : ℂ)) ^ 2) * (id * id)

/-- `Q'(z) = 2(1+r)² z - 2(1-6r+r²)`. -/
def Qd (r : ℝ) : ℂ → ℂ :=
  K (2 * (1 + (r : ℂ)) ^ 2) * id - K (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2))

/-- `Q''(z) = 2(1+r)²` (a constant). -/
def Qdd (r : ℝ) : ℂ → ℂ := K (2 * (1 + (r : ℂ)) ^ 2)

/-- `S r z = √(Q r z)`, the principal square root. -/
def Sf (r : ℝ) : ℂ → ℂ := (fun u : ℂ => u ^ (1 / 2 : ℂ)) ∘ Qf r

/-- `S'(z) = Q'(z)/(2 S z)`. -/
def Sd (r : ℝ) : ℂ → ℂ := Qd r / (K 2 * Sf r)

/-- `S''(z) = (2 Q Q'' - Q'²)/(4 S³)`. -/
def Sdd (r : ℝ) : ℂ → ℂ := (K 2 * Qf r * Qdd r - Qd r * Qd r) / (K 4 * Sf r ^ 3)

/-- `P r z = (1+r)² - 2(r-1)² z + (1+r)² z²`. -/
def Pf (r : ℝ) : ℂ → ℂ :=
  K ((1 + (r : ℂ)) ^ 2) - K (2 * ((r : ℂ) - 1) ^ 2) * id + K ((1 + (r : ℂ)) ^ 2) * (id * id)

/-- The numerator `N r z = P r z + (1+r)(z-1)S r z` of the slit map. -/
def Nf (r : ℝ) : ℂ → ℂ := Pf r + K (1 + (r : ℂ)) * (id - K 1) * Sf r

/-- `N'(z) = -2(r-1)² + 2(1+r)²z + (1+r)S + (1+r)(z-1)Q'/(2S)`. -/
def Nd (r : ℝ) : ℂ → ℂ :=
  K (-2 * ((r : ℂ) - 1) ^ 2) + K (2 * (1 + (r : ℂ)) ^ 2) * id + K (1 + (r : ℂ)) * Sf r
    + K (1 + (r : ℂ)) * (id - K 1) * Sd r

/-- `N''(z) = 2(1+r)² + (1+r)Q'/S + (1+r)(z-1)(2QQ'' - Q'²)/(4S³)`. -/
def Ndd (r : ℝ) : ℂ → ℂ :=
  K (2 * (1 + (r : ℂ)) ^ 2) + K (2 * (1 + (r : ℂ))) * Sd r
    + K (1 + (r : ℂ)) * (id - K 1) * Sdd r

/-- The slit map written as `N/(8rz)`, as a function built from pointwise operations. -/
def Gfun (r : ℝ) : ℂ → ℂ := Nf r / (K (8 * (r : ℂ)) * id)

/-- `(N/z)' = (N'z - N)/z²`, as a function built from pointwise operations. -/
def Hd (r : ℝ) : ℂ → ℂ := (Nd r * id - Nf r) / (K (8 * (r : ℂ)) * (id * id))

/-! ## Value forms -/

theorem Qf_apply (r : ℝ) (z : ℂ) :
    Qf r z = (1 + (r : ℂ)) ^ 2 - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2) * z
      + (1 + (r : ℂ)) ^ 2 * z ^ 2 := by
  simp only [Qf, K, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq] <;> ring

theorem Qd_apply (r : ℝ) (z : ℂ) :
    Qd r z = 2 * (1 + (r : ℂ)) ^ 2 * z - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2) := by
  simp only [Qd, K, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

theorem Qdd_apply (r : ℝ) (z : ℂ) : Qdd r z = 2 * (1 + (r : ℂ)) ^ 2 := rfl

theorem Sf_apply (r : ℝ) (z : ℂ) : Sf r z = (Qf r z) ^ (1 / 2 : ℂ) := rfl

theorem Pf_apply (r : ℝ) (z : ℂ) :
    Pf r z = (1 + (r : ℂ)) ^ 2 - 2 * ((r : ℂ) - 1) ^ 2 * z + (1 + (r : ℂ)) ^ 2 * z ^ 2 := by
  simp only [Pf, K, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq] <;> ring

theorem Nf_apply (r : ℝ) (z : ℂ) :
    Nf r z = (1 + (r : ℂ)) ^ 2 - 2 * ((r : ℂ) - 1) ^ 2 * z + (1 + (r : ℂ)) ^ 2 * z ^ 2
      + (1 + (r : ℂ)) * (z - 1) * (Qf r z) ^ (1 / 2 : ℂ) := by
  simp only [Nf, Pf, Sf, K, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    id_eq] <;> ring

theorem Sd_apply (r : ℝ) (z : ℂ) : Sd r z = Qd r z / (2 * Sf r z) := by
  simp only [Sd, K, Pi.div_apply, Pi.mul_apply]

theorem Sdd_apply (r : ℝ) (z : ℂ) :
    Sdd r z = (2 * Qf r z * Qdd r z - Qd r z * Qd r z) / (4 * (Sf r z) ^ 3) := by
  simp only [Sdd, K, Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]

theorem Nd_apply (r : ℝ) (z : ℂ) :
    Nd r z = -2 * ((r : ℂ) - 1) ^ 2 + 2 * (1 + (r : ℂ)) ^ 2 * z + (1 + (r : ℂ)) * Sf r z
      + (1 + (r : ℂ)) * (z - 1) * (Qd r z / (2 * Sf r z)) := by
  simp only [Nd, Sd_apply, K, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

theorem Ndd_apply (r : ℝ) (z : ℂ) :
    Ndd r z = 2 * (1 + (r : ℂ)) ^ 2 + (1 + (r : ℂ)) * (Qd r z / Sf r z)
      + (1 + (r : ℂ)) * (z - 1)
        * ((2 * Qf r z * Qdd r z - Qd r z * Qd r z) / (4 * (Sf r z) ^ 3)) := by
  simp only [Ndd, Sdd_apply, Sd_apply, K, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    id_eq] <;> ring_nf

theorem Gfun_apply (r : ℝ) (z : ℂ) : Gfun r z = Nf r z / (8 * (r : ℂ) * z) := by
  simp only [Gfun, K, Pi.div_apply, Pi.mul_apply, id_eq] <;> ring

theorem Hd_apply (r : ℝ) (z : ℂ) : Hd r z = (Nd r z * z - Nf r z) / (8 * (r : ℂ) * z ^ 2) := by
  simp only [Hd, K, Pi.div_apply, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

/-! ## Basic facts -/

/-- `S r z` is the principal square root of `Q r z`. -/
theorem Sf_sq (r : ℝ) (z : ℂ) : (Sf r z) ^ 2 = Qf r z := by
  rw [Sf_apply]
  exact Work.APsi.cpow_half_sq (Qf r z)

/-- `Q r z ≠ 0` on the open unit disc. -/
theorem Qf_ne_zero {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Qf r z ≠ 0 := by
  have hmem : Qf r z ∈ slitPlane := by
    rw [Qf_apply]
    exact (Work.APsi.slitQ_branch r hr0 hr1).1 z hz
  intro h
  rw [h] at hmem
  simp [Complex.mem_slitPlane_iff] at hmem

/-- `S r z ≠ 0` on the open unit disc. -/
theorem Sf_ne_zero {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Sf r z ≠ 0 := by
  intro h
  have hQ : Qf r z = 0 := by rw [← Sf_sq r z, h]; ring
  exact Qf_ne_zero hr0 hr1 hz hQ

/-- The slit map is the rational expression `N/(8rz)` everywhere (both sides vanish at `0`). -/
theorem slit_eq_Nf (r : ℝ) : (slit r) = fun z => Nf r z / (8 * (r : ℂ) * z) := by
  funext z
  rcases eq_or_ne z 0 with h0 | h0
  · subst h0; simp [Submission.CDTPlan.slit, Nf, Pf, Sf, K]
  · rw [Work.APsi.slit_eq_formula r z h0]
    have hN : Work.APsi.slitN r z = Nf r z := by
      simp only [Work.APsi.slitN, Work.APsi.slitR, Work.APsi.slitP, Work.APsi.slitQ, Nf_apply,
        Qf_apply] <;> ring
    rw [hN]

/-- The slit map is `Gfun r = Nf r/(8 r ·)`. -/
theorem slit_eq_Gfun (r : ℝ) : (slit r) = Gfun r := by
  rw [slit_eq_Nf r]
  funext z
  rw [Gfun_apply]

end

end Work.ANum2
