/-
# `phiAj_smooth2` — the regularity of the `𝒜`-iterates of the radial profile

`𝒜 = α z²∂_zz + (5+α) z∂_z` is the radial operator of the `Φ_*` decomposition, `φ = 2z/(1+z)²`
is the profile and `phiAj j α = 𝒜^j φ` (`StarDefs.phiAj`, with `phiAj 1 = phiA`).  The consumer
(`PhiStar/telescoping`, `PhiStar/Defs.bslOp_sep`) needs `𝒜φ` and `𝒜²φ` to be `C²` at every
`z > 0`, because the separable identity `bslOp α (A(z)·ψ(θ)) = A(z)·L₀ψ − (𝒜A)(z)·ψ(θ)`
is applied with `A = 𝒜φ` and `A = 𝒜²φ`.

Both are in fact `C^∞` on `(0,∞)`: `𝒜φ` is the *rational function*

`𝒜φ(z) = 4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³`

(`Basic.phiA_eq`), which is `C^n` at every `z ≠ −1` for every order `n` since the denominators
`(1+z)^k` do not vanish there.  The second iterate is then a sum of products of `z^2`, `z` with
the second and first derivatives of the `C^∞` function `𝒜φ`; a `C^∞` function has `C^∞` iterated
derivatives (`ContDiffAt.derivWithin`).

Everything is proved against the explicit form, so no unsimplified quotient is ever
differentiated by the junk-valued `deriv`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## General order bookkeeping -/

/-- The derivative of a `C^∞` function is `C^∞`. -/
theorem contDiffAt_infty_deriv {f : ℝ → ℝ} {z : ℝ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (deriv f) z :=
  h.derivWithin (m := ∞) (by simp)

/-- A `C^∞` function has `C^∞` iterated derivatives. -/
theorem contDiffAt_infty_iteratedDeriv {f : ℝ → ℝ} {z : ℝ} (k : ℕ)
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact contDiffAt_infty_deriv ih

/-! ## The first iterate `𝒜φ = phiA α` -/

/-- **`𝒜φ` is `C^n` at every `z > 0`, for every order `n`** (in particular `C^∞`).  Proof: the
explicit rational form `Basic.phiA_eq` is a sum of two quotients whose denominators `(1+z)^4`,
`(1+z)^3` are nonvanishing for `z > 0`. -/
theorem contDiffAt_phiA_of (α : ℝ) (n : ℕ∞ω) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ n (Work.FTS.VocabO.phiA α) z := by
  have hz1 : z ≠ -1 := by linarith
  have hF : ContDiffAt ℝ n (fun z : ℝ =>
      4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4
        + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3) z := by
    have hden : (1 + z) ^ 4 ≠ 0 := by
      have : 1 + z ≠ 0 := by linarith
      positivity
    have hden3 : (1 + z) ^ 3 ≠ 0 := by
      have : 1 + z ≠ 0 := by linarith
      positivity
    refine (ContDiffAt.div ?_ (((contDiffAt_const (c := (1 : ℝ))).add contDiffAt_id).pow 4)
      hden).add (ContDiffAt.div ?_ (((contDiffAt_const (c := (1 : ℝ))).add
        contDiffAt_id).pow 3) hden3)
    · exact (((contDiffAt_const (c := (4 * α))).mul (contDiffAt_id.pow 2)).mul
        (contDiffAt_id.sub contDiffAt_const))
    · exact (((contDiffAt_const (c := (2 * (5 + α)))).mul contDiffAt_id).mul
        (contDiffAt_const.sub contDiffAt_id))
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  have hy1 : y ≠ -1 := by
    simp only [Set.mem_Ioi] at hy
    linarith
  exact Work.FTS.PhiStar.phiA_eq α y hy1

/-- `𝒜φ` is `C^∞` at every `z > 0`. -/
theorem contDiffAt_phiA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Work.FTS.VocabO.phiA α) z :=
  contDiffAt_phiA_of α ∞ hz

/-! ## The second iterate `𝒜²φ = phiAj 2 α` -/

/-- **`𝒜²φ` is `C²` at every `z > 0`**: `𝒜(𝒜φ) = αz²(𝒜φ)'' + (5+α)z(𝒜φ)'` is a sum of
products of the smooth `z²`, `z` with the second and first derivatives of the `C^∞` function
`𝒜φ`. -/
theorem contDiffAt_phiAj_two (α : ℝ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.phiAj 2 α) z := by
  have h : ContDiffAt ℝ ∞ (Work.FTS.PhiStar.phiAj 1 α) z := contDiffAt_phiA α hz
  have hd1 : ContDiffAt ℝ ∞ (deriv (Work.FTS.PhiStar.phiAj 1 α)) z := contDiffAt_infty_deriv h
  have hd2 : ContDiffAt ℝ ∞ (iteratedDeriv 2 (Work.FTS.PhiStar.phiAj 1 α)) z :=
    contDiffAt_infty_iteratedDeriv 2 h
  have hd1' : ContDiffAt ℝ 2 (deriv (Work.FTS.PhiStar.phiAj 1 α)) z :=
    hd1.of_le (by simp)
  have hd2' : ContDiffAt ℝ 2 (iteratedDeriv 2 (Work.FTS.PhiStar.phiAj 1 α)) z :=
    hd2.of_le (by simp)
  show ContDiffAt ℝ 2 (fun z : ℝ =>
    α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.phiAj 1 α) z
      + (5 + α) * z * deriv (Work.FTS.PhiStar.phiAj 1 α) z) z
  exact (((contDiffAt_const (c := α)).mul (contDiffAt_id.pow 2)).mul hd2').add
    (((contDiffAt_const (c := (5 + α))).mul contDiffAt_id).mul hd1')

/-! ## The requested statement -/

theorem phiAj_smooth2 {α z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ 2 (Work.FTS.VocabO.phiA α) z ∧
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.phiAj 2 α) z :=
  ⟨(contDiffAt_phiA α hz).of_le (by simp), contDiffAt_phiAj_two α hz⟩

end Work.FTS.PhiStar
