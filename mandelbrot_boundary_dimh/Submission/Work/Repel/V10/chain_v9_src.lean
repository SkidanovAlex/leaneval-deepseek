import Mathlib
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.chain_v9_geom
import Submission.Work.Repel.V10.chain_image_mem
import Submission.Work.L62.chain

/-!
# `Work.Repel.chain_v9_src` : the source region of a §6 cell, revisited

Shishikura §6, Step 3 cuts out, for each cell `(j, k, n)` (chain level `j`, integer `Re`-translate
`k`, level-0 box/period index `n`), a *topological disc* in the level-0 Fatou plane: the component
of the preimage under `π` of the level-1 fibre image `E = φ₁ '' (W j + k)`, in the `n`-th period.

`chain_v9_chase` used the *half-open* box `B n = {n ≤ Re w < n+1, ...}`, which makes the source
region non-open and can cut the source disc in two (`NOTES_chain_returns_v9_progress.md` §7).
Here the period is cut out by the **round box** `Metric.ball (w_c + n) (1/2)` instead: because the
level-1 fibre has diameter `< 1/2` and `φ₁` is locally invertible with `‖φ₁'‖ ≈ 1/η₁²` at height
`η₁`, each component of `Raw j k = {w : s·π w ∈ E}` is a disc of diameter `≪ 1`, the translates by
`ℤ` are `1` apart, and `Metric.ball (w_c + n) (1/2) ∩ Raw j k` is therefore exactly one component:
open and connected.

Everything is *explicit* through the normalisation at the reference point

  `w_c = log (φ₁ (u_c + k) / s) / (2πi)`,   `u_c ∈ W j` chosen in the chain,

which is the principal lift: `Re w_c ∈ (-1/2, 1/2]`, `Im w_c = -log‖φ₁(u_c+k)/s‖/(2π) ≈ η`.  The
map

  `lift u = w_c + n + log (φ₁ u / φ₁ (u_c + k)) / (2πi)`   (`u ∈ W j + k`)

satisfies `π (lift u) = φ₁ u / s` and `‖lift u - (w_c + n)‖ < 1/2`, and its image is the whole
source region, so no branch-of-log or connected-component bookkeeping is needed.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The level-1 fibre image `E = φ₁ '' (W j + k)` of the cell (a small disc in the `ζ`-plane). -/
def fibImg (j : ℕ) (k : ℤ) : Set ℂ :=
  V.P₁.φ '' ((fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j)

/-- The level-0 fibre preimage of the cell: the points whose level-1 image is in `E`. -/
def Raw (j : ℕ) (k : ℤ) : Set ℂ := {w : ℂ | V.s * MandelDim.piExp w ∈ V.fibImg j k}

/-- A chosen point of the chain level `W j` (the `L62.IsChain.close` witness). -/
def uc (j : ℕ) : ℂ := Classical.choose (V.hIsChain.close j)

theorem uc_mem (j : ℕ) : V.uc j ∈ V.W j := (Classical.choose_spec (V.hIsChain.close j)).1

/-- **The reference point of the cell.**  The principal lift of the fibre image: `π w_c` is the
principal lift of `φ₁ (u_c + k)/s`, so `Re w_c ∈ (-1/2, 1/2]` and
`Im w_c = -log‖φ₁ (u_c + k)/s‖/(2π)`. -/
def wc (j : ℕ) (k : ℤ) : ℂ :=
  Complex.log (V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) / V.s) / (2 * Real.pi * Complex.I)

/-- **The source region of the cell** `(j, k, n)`: the `n`-th period component of `Raw j k`,
cut out by the round box `Metric.ball (w_c + n) (1/2)`. -/
def SrcC (j : ℕ) (k : ℤ) (n : ℤ) : Set ℂ :=
  V.Raw j k ∩ Metric.ball (V.wc j k + ((n : ℤ) : ℂ)) (1 / 2)

/-- The explicit lift of a level-1 source `u ∈ W j + k` into the source region of the `n`-th
period. -/
def lift (j : ℕ) (k : ℤ) (n : ℤ) (u : ℂ) : ℂ :=
  V.wc j k + ((n : ℤ) : ℂ) +
    Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) / (2 * Real.pi * Complex.I)

/-- The fibre of the cell, translated to the chain level `j`. -/
def fib (j : ℕ) (k : ℤ) : Set ℂ := (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j

theorem uc_fib (j : ℕ) (k : ℤ) : V.uc j + ((k : ℤ) : ℂ) ∈ V.fib j k :=
  ⟨V.uc j, V.uc_mem j, rfl⟩

/-- `φ₁` does not vanish on the fibre `W j + k ⊆ Sm1`. -/
theorem phi_ne_zero_of_mem_fib {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {u : ℂ}
    (hu : u ∈ V.fib j k) : V.P₁.φ u ≠ 0 := by
  have h := (V.phi_bounds_of_mem_Sm1 (hSm hu)).1
  have hpos : 0 < 40 / (51 * V.η₁) :=
    div_pos (by norm_num) (mul_pos (by norm_num) V.hη₁pos)
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- `π (w_c)` is the image of the chosen fibre point. -/
theorem piExp_wc {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    MandelDim.piExp (V.wc j k) = V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) / V.s := by
  rw [V10.wc, Work.Horn.MandelDim.piExp_log_div _
    (div_ne_zero (phi_ne_zero_of_mem_fib V hSm (V.uc_fib j k)) V.hs)]

/-- The reference point is in the raw source set. -/
theorem wc_mem_Raw {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) : V.wc j k ∈ V.Raw j k := by
  show V.s * MandelDim.piExp (V.wc j k) ∈ V.fibImg j k
  rw [piExp_wc V hSm, mul_div_cancel₀ _ V.hs]
  exact ⟨V.uc j + ((k : ℤ) : ℂ), V.uc_fib j k, rfl⟩

/-- `π` is additive. -/
theorem piExp_add' (a b : ℂ) :
    MandelDim.piExp (a + b) = MandelDim.piExp a * MandelDim.piExp b := by
  rw [MandelDim.piExp, MandelDim.piExp, MandelDim.piExp, ← Complex.exp_add]
  congr 1
  ring

/-- The explicit lift has the prescribed `π`-image. -/
theorem lift_piExp {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {n : ℤ} {u : ℂ}
    (hu : u ∈ V.fib j k) :
    MandelDim.piExp (V.lift j k n u) = V.P₁.φ u / V.s := by
  have huc : V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ≠ 0 :=
    phi_ne_zero_of_mem_fib V hSm (V.uc_fib j k)
  have hne : V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ≠ 0 :=
    div_ne_zero (phi_ne_zero_of_mem_fib V hSm hu) huc
  rw [V10.lift, piExp_add', Work.Horn.MandelDim.piExp_add_intCast, piExp_wc V hSm,
    Work.Horn.MandelDim.piExp_log_div _ hne]
  field_simp

/-- The explicit lift lies in the raw source set. -/
theorem lift_mem_Raw {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {n : ℤ} {u : ℂ}
    (hu : u ∈ V.fib j k) : V.lift j k n u ∈ V.Raw j k := by
  show V.s * MandelDim.piExp (V.lift j k n u) ∈ V.fibImg j k
  rw [lift_piExp V hSm hu, mul_div_cancel₀ _ V.hs]
  exact ⟨u, hu, rfl⟩

end V10

end

end Work.Repel
