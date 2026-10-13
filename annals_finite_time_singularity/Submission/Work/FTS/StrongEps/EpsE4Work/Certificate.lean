/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Work/Certificate.lean`

**Why `Work.FTS.StrongEps.EpsE4` is FALSE as stated.**

The target `EpsE4` (`Submission/Work/FTS/StrongEps/EpsE4.lean`) asks for

  `EpsUniformMem α ρ Φs E g₀ C₀ K`

from the datum hypotheses `hvan`, `hd : ∀ ε > 0, EpsDatum α ρ ε g₀`,
`h4 : Xn α g₀ ≤ α ^ 2`, `h6 : Xn₆ α g₀ ≤ K * α ^ 2` and the elliptic/modulation
hypotheses `hEll`, `hstar`, `hml` — for **every** `0 < C₀`.

The conclusion's clause at fake time `τ = 0` is, however,

  `Xn α (slice (JfamP ρ ε g) 0) ≤ C₀ * α ^ 2`,

and `slice (JfamP ρ ε g) 0 = Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀` (the `Pz`-projection is the
identity on the class-`C` profile `J_ε g₀`, which is exactly the `l12` field of `hd`).  Since
`Xn α (Jeps ρ ε g₀) → Xn α g₀` as `ε → 0⁺` (the workspace's mollifier-approximation estimate
`EpsApprox.HkNorm_Jeps_sub_le`), the conclusion **forces `Xn α g₀ ≤ C₀ α²`** for every datum
satisfying `hd` — while the hypotheses only require `Xn α g₀ ≤ α²`.  No hypothesis can supply the
missing factor: `MuLamOK` holds for *every* `C₀ > 0` (`FTS_MuLamOK.MuLamOK_proved`), so nothing
forces `C₀ ≥ 1`.

Hence the statement fails for every `C₀ < 1` (this file records the slightly weaker formal
threshold `C₀ < 1/√2`, the `√2` being the loss of the available triangle inequality
`EllipticEst.HkNorm_add_le`; the honest sharp threshold is `C₀ < 1`).  The three theorems below
make this machine-checked:

* `EpsUniformMem_false_of_size` — for a datum of `ℋ⁴`-size `> √2 C₀ α²` (and of the `hd`-class),
  **no** `Φs`, `E`, `K` make the conclusion of `EpsE4` hold;
* `exists_datum_Xn_eq` — there *is* a datum in the `hd`-class with `Xn α g₀ = α²` exactly, namely
  the project's own localised order-`6` datum `locG6 α L β` (with `L₁₂(locG6)(0) = 0`, produced by
  `LocData6.locG6_data`) rescaled by `α² / Xn α (locG6 α L β)`;
* `EpsE4_counterexample` — their combination.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Work.epsUniformMem_Jeps_bound
import Submission.Work.FTS.StrongEps.EpsE4Work.Xn_le_sqrt_two_mul_of_Jeps_bound
import Submission.Work.FTS.StrongEps.EpsE4Work.Jeps_smul
import Submission.Work.FTS.StrongEps.EpsE4Work.HkSq_pos_of_continuousOn_ne
import Submission.Work.FTS.StrongEps.EpsE4Work.locG6_apply_ne_zero
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS_RegExport.Supp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Small API: `SmoothOpen` is stable under scalar multiplication -/

theorem smoothOpen_smul {c : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) : Work.FTS.EllipticEst.SmoothOpen (c • f) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h ⊢
  intro n
  show ContDiffOn ℝ (n : ℕ) (fun y : ℝ × ℝ => c * Function.uncurry f y) Work.FTS.EllipticEst.Q0
  exact ContDiffOn.const_smul c (h n)

/-! ## The datum-side hypotheses of `EpsUniformMem` do not force the `C₀`-ball

The first theorem is the crux: from the conclusion of `EpsE4` (plus the datum's `hd`) one derives
`Xn α g₀ ≤ √2 C₀ α²`.  It is the composition of the two delegated lemmas
(`epsUniformMem_Jeps_bound`: the `τ = 0` clause reads `Xn α (Jeps ρ ε g₀) ≤ C₀ α²`;
`Xn_le_sqrt_two_mul_of_Jeps_bound`: the mollifier-approximation estimate upgrades this to the
bound on `Xn α g₀`). -/

theorem EpsUniformMem_false_of_size {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀)
    (hd : ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀)
    (hsize : Real.sqrt 2 * (C₀ * α ^ 2) < Work.FTS.Nonlin.Xn α g₀) :
    ∀ (Φs : Fn) (E : Fn → Fn) (K : ℝ), ¬ Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K := by
  -- the datum-side data of `hd`
  have hsm : Work.FTS.EllipticEst.SmoothOpen g₀ := (hd 1 one_pos).1
  have h5 : Work.Spaces.HkMem α 5 g₀ :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm (hd 1 one_pos).2.1
  have hsmJ : ∀ ε ∈ Set.Ioc 0 1, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g₀) :=
    fun ε hε => (hd ε hε.1).2.2.reg
  have hmem4 : ∀ ε ∈ Set.Ioc 0 1, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε g₀) :=
    fun ε hε =>
      Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num)
        (hd ε hε.1).2.2.reg (hd ε hε.1).2.2.mem
  intro Φs E K hU
  obtain ⟨ε₁, hε₁, hbd⟩ := epsUniformMem_Jeps_bound hU hd
  have hle := Xn_le_sqrt_two_mul_of_Jeps_bound (ρ := ρ) hρ hα hα1 hC₀.le hsm h5 hsmJ hmem4
    ⟨ε₁, hε₁, hbd⟩
  linarith [hsize, hle]

/-! ## An admissible datum of size exactly `α²`

The project's own datum `locG6 α L β` (with the `L₁₂`-condition produced by
`LocData6.locG6_data`) is admissible for every `ε > 0` (`FTS_LocDatum3a.locG6_epsDatum`) and has
positive `ℋ⁴`-size (its value at `(2L+1, π/4)` is `⁻(α/c)·Fstar(2L+1)·Gam(π/4) ≠ 0`, and the
`ℋ⁴`-integrand is continuous and positive there).  Rescaling it by
`c := α² / Xn α (locG6 α L β)` gives a datum of `ℋ⁴`-size exactly `α²`, admissible for every `ε`
(the class `EpsDatum` is scale-invariant) and vanishing on the angular boundary. -/

theorem Xn_locG6_pos {α L β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    0 < Work.FTS.Nonlin.Xn α (Work.FTS.LocData6.locG6 α L β) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.LocData6.locG6 α L β) :=
    Work.FTS_LocDatum3a.smoothOpen_locG6 α L β
  have h6 : Work.Spaces.HkMem α 6 (Work.FTS.LocData6.locG6 α L β) :=
    (Work.FTS.LocData6.regQ_locG6_uncond α L β hα hα1 hL).2.1
  have hmem : Work.Spaces.HkMem α 4 (Work.FTS.LocData6.locG6 α L β) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm h6
  have hcont : ContinuousOn (Function.uncurry (Work.FTS.LocData6.locG6 α L β))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h := hsm.continuousOn
    simpa only [Work.FTS.EllipticEst.Q0] using h
  have hz : (0 : ℝ) < 2 * L + 1 := by linarith
  have hθ : (π / 4 : ℝ) ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpos := HkSq_pos_of_continuousOn_ne (α := α) (k := 4) (f := Work.FTS.LocData6.locG6 α L β)
    (z₀ := 2 * L + 1) (θ₀ := π / 4) hα hmem hcont hz hθ (locG6_apply_ne_zero hα hα1 hL)
  rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  exact Real.sqrt_pos.2 hpos

/-- **There is a datum in the `hd`-class with `ℋ⁴`-size exactly `α²`**: the rescaled localised
order-`6` datum. -/
theorem exists_datum_Xn_eq {α : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ g₀ : Fn, (∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀) ∧
      Work.FTS.Nonlin.Xn α g₀ = α ^ 2 ∧
      (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) := by
  obtain ⟨L₀, _hL₀pos, hL₀⟩ := Work.FTS.LocData6.locG6_data α hα hα1 1 (by norm_num)
  obtain ⟨β, _hβ, _hAdm, _hregQ, _hgal, hL12, _hXn, _hXn6⟩ :=
    hL₀ (max L₀ 1) (le_max_left _ _)
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have hpos : 0 < Work.FTS.Nonlin.Xn α (Work.FTS.LocData6.locG6 α (max L₀ 1) β) :=
    Xn_locG6_pos hα hα1 hL1
  refine ⟨(α ^ 2 / Work.FTS.Nonlin.Xn α (Work.FTS.LocData6.locG6 α (max L₀ 1) β))
      • Work.FTS.LocData6.locG6 α (max L₀ 1) β, ?_, ?_, ?_⟩
  · -- admissibility for every `ε`, by scale-invariance of `EpsDatum`
    intro ε hε
    obtain ⟨hsm, h6, hC⟩ :=
      Work.FTS_LocDatum3a.locG6_epsDatum α (max L₀ 1) β hα hα1 hL1 hL12 hρ hε
    have hc : (α ^ 2 / Work.FTS.Nonlin.Xn α (Work.FTS.LocData6.locG6 α (max L₀ 1) β)) ≠ 0 := by
      exact div_ne_zero (pow_ne_zero 2 hα.ne') hpos.ne'
    exact ⟨smoothOpen_smul hsm, Work.FTS.EllipticEst.HkMem_smul hc α 6 h6,
      by rw [Jeps_smul]; exact Work.FTS.ClassC.classC_smul _ hC⟩
  · -- the size is exactly `α²`
    have hcpos : 0 < α ^ 2 / Work.FTS.Nonlin.Xn α (Work.FTS.LocData6.locG6 α (max L₀ 1) β) :=
      div_pos (pow_pos hα 2) hpos
    rw [Work.FTS.Nonlin.Xn, Work.FTS.EllipticEst.HkNorm_smul, abs_of_pos hcpos]
    field_simp
  · -- the angular-boundary vanishing
    intro z _
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul, Work.FTS.LocDataExt.locG_eq_locR_Gam α (max L₀ 1) β,
        Work.FTS_RegExport.Gam_zero_left hα, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, Work.FTS.LocDataExt.locG_eq_locR_Gam α (max L₀ 1) β,
        Work.FTS_RegExport.Gam_zero_pi hα, mul_zero]

/-- **`EpsE4` is false for every `0 < C₀ < 1/√2`**: there is a datum satisfying the theorem's
datum-side hypotheses (`hvan`, `hd`, and `h4`/`h6` at a suitable `K`) for which the conclusion
`EpsUniformMem α ρ Φs E g₀ C₀ K` fails for *every* `Φs`, `E`, `K`.

(The threshold `1/√2` is a formal artefact of `EllipticEst.HkNorm_add_le`; the honest one is `1`,
because `Xn α (Jeps ρ ε g₀) → Xn α g₀`.) -/
theorem EpsE4_counterexample {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀)
    (hC₀1 : C₀ < 1 / Real.sqrt 2) :
    ∃ g₀ : Fn, (∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀) ∧
      Work.FTS.Nonlin.Xn α g₀ = α ^ 2 ∧
      (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧
      ∀ (Φs : Fn) (E : Fn → Fn) (K : ℝ), 0 ≤ K →
        ¬ Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨g₀, hd, hsize, hvan⟩ := exists_datum_Xn_eq (α := α) hρ hα hα1
  refine ⟨g₀, hd, hsize, hvan, ?_⟩
  -- the size `α²` beats the threshold `√2 C₀ α²`
  have hαsq : 0 < α ^ 2 := pow_pos hα 2
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlt : Real.sqrt 2 * C₀ < 1 := by
    calc Real.sqrt 2 * C₀ < Real.sqrt 2 * (1 / Real.sqrt 2) :=
          mul_lt_mul_of_pos_left hC₀1 hsqrt2
      _ = 1 := by rw [mul_one_div, div_self hsqrt2.ne']
  have hthr : Real.sqrt 2 * (C₀ * α ^ 2) < Work.FTS.Nonlin.Xn α g₀ := by
    rw [hsize, ← mul_assoc]
    simpa using mul_lt_mul_of_pos_right hlt hαsq
  intro Φs E K _hK
  exact EpsUniformMem_false_of_size hρ hα hα1 hC₀ hd hthr Φs E K

end Work.FTS.StrongEps.EpsE4Work
