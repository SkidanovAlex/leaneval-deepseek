/-
# The constructive clauses of the induction step of the `ℋ^k` coercivity

Elgindi's §"Higher order derivatives and the inner product on `ℋ^k`" (tex 661–707)
constructs, by induction on `k`, the inner product `(·,·)_{ℋ^k}` via the recursion

  `(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c₁(D_θf,D_θg)_{ℋ^{k-1}} + c₂(D_zf,D_zg)_{ℋ^{k-1}}`

(`Work.Coercivity.HkIPStep`), together with its comparability with `|·|_{ℋ^k}`.

This file proves the **constructive half** of that step: from an admissible inner product
at level `n` (`IsHkIPCore_fts α n IP`) one obtains the constructive clauses
(`IsHkIPCore_fts α (n+1)`) for the pairing `HkIPStep 1 1 IP`.  No clause of
`IsHkIPCore_fts` mentions `𝓛_Γ^T`, so the step needs neither the regularity package
`StepReg` nor the commutator bounds `CommutBounds`: those enter only in the coercivity
half (`Step.HkIPStep_coercive`) and in the assembly (`Step.HkIPStep_isHkIP_fts`).

The mathematical content is that every clause is inherited from level `n`, using

* the descent `HkReg α (n+1) f → HkReg α n f` and `HkReg α (n+1) f → HkReg α n (D_θf)`,
  `HkReg α n (D_zf)` (`HkReg_mono`, `HkReg_dth`, `HkReg_dz`);
* the pointwise additivity/scaling of `D_θ` and `D_z` on the domain `[0,∞) × [0,π/2]`
  (`Dth_add_of_smoothNbhd`, `Dz_add_of_smoothNbhd`, `Dth_const_mul_of_smoothNbhd`,
  `Dz_const_mul_of_smoothNbhd`), which turns the pairings of the derivatives of a sum
  (resp. a scalar multiple) into pairings of sums (resp. multiples).  The class `HkReg` is
  *not* closed under addition a priori, so the transfer is made either through the
  `HkMem`-closure lemma `HkMem_smul` or, for the derivatives of a sum whose `HkReg`
  membership is known, through the congruence `HkMem_congr_Ioi` on `(0,∞) × I_θ`
  (`HkReg_dth_add`, `HkReg_dz_add`);
* the commutation of the derivative with the congruence on the open quadrant (`Qd`),
  which is the form in which `IsHkIPCore_fts.congr_qd` is stated (`Dth_congr_qd`,
  `Dz_congr_qd`);
* the comparability clauses at level `n` together with `HkSq_succ_le`,
  `HkSq_Dth_le`, `HkSq_Dz_le` and `HkSq_mono_le` for the norm clauses.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dz_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkAdm_mono
import Submission.Work.Coercivity.HkAdm_dth
import Submission.Work.Coercivity.HkSq_succ_le
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Step

set_option autoImplicit false

/-! ## Regularity bookkeeping

The regularity class `Work.FTS.CoercivityStep.HkReg α k f` (`SmoothNbhd f ∧ HkMem α k f`)
descends in the order, is preserved by `D_θ`, `D_z` (one order down), and is closed under
the pointwise operations used by the linearity clauses. -/

/-- `HkReg` descends: `HkReg α (n+1) f → HkReg α n f`. -/
theorem HkReg_mono {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n f :=
  ⟨h.1, Work.Coercivity.HkMem_mono α n h.1 h.2⟩

/-- `D_θ` lowers the order by one: `HkReg α (n+1) f → HkReg α n (D_θ f)`. -/
theorem HkReg_dth {α : ℝ} (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dth f) :=
  ⟨h.1.Dth, (Work.Coercivity.HkMem_dth α hα n h.1 h.2).1⟩

/-- `D_z` lowers the order by one: `HkReg α (n+1) f → HkReg α n (D_z f)`. -/
theorem HkReg_dz {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dz f) :=
  ⟨h.1.Dz, Work.Coercivity.HkMem_dz_free α n h.1 h.2⟩

/-- `SmoothNbhd` is closed under pointwise addition. -/
theorem SmoothNbhd_add {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) : Work.Spaces.SmoothNbhd (f + g) := by
  have h : Function.uncurry (f + g)
      = fun p => Function.uncurry f p + Function.uncurry g p := by
    funext p; rfl
  rw [Work.Spaces.SmoothNbhd, h]
  exact hf.add hg

/-- `SmoothNbhd` is closed under pointwise multiplication by a constant. -/
theorem SmoothNbhd_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p => c * Function.uncurry f p := by
    funext p; rfl
  rw [Work.Spaces.SmoothNbhd, h]
  simpa only [smul_eq_mul] using hf.const_smul c

/-! ## The open quadrant inside the domain -/

/-- Membership in the open quadrant `Qd`, unfolded. -/
theorem mem_Qd_iff {z θ : ℝ} :
    ((z, θ) ∈ Work.FTS.CoercivityStep.Qd)
      ↔ z ∈ Set.Ioi (0 : ℝ) ∧ θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [Work.FTS.CoercivityStep.Qd, Set.mem_prod]

/-- The first coordinate of a point of the open quadrant is positive. -/
theorem Qd_pos_fst {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.CoercivityStep.Qd) :
    z ∈ Set.Ioi (0 : ℝ) :=
  (mem_Qd_iff.mp h).1

/-- A positive real belongs to `Iz`. -/
theorem Iz_of_pos {z : ℝ} (hz : 0 < z) : z ∈ Work.Spaces.Iz := by
  simpa only [Work.Spaces.Iz, Set.mem_Ici] using le_of_lt hz

/-- The second coordinate of a point of the open quadrant lies in `Iθ`. -/
theorem Qd_mem_snd {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.CoercivityStep.Qd) :
    θ ∈ Work.Spaces.Iθ := by
  simpa only [Work.Spaces.Iθ, Set.mem_Icc] using
    (⟨le_of_lt (mem_Qd_iff.mp h).2.1, le_of_lt (mem_Qd_iff.mp h).2.2⟩ :
      (0 : ℝ) ≤ θ ∧ θ ≤ π / 2)

/-! ## Differentiability of the slices -/

/-- The `z`-slice of a `SmoothNbhd` function is differentiable at every point of `nbhU`. -/
theorem differentiableAt_slice_fst {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hy : (z, θ) ∈ Work.Spaces.nbhU) : DifferentiableAt ℝ (fun z' => f z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry f ∘ fun z' : ℝ => (z', θ)) z
  exact hd.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

/-- The `θ`-slice of a `SmoothNbhd` function is differentiable at every point of `nbhU`. -/
theorem differentiableAt_slice_snd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hy : (z, θ) ∈ Work.Spaces.nbhU) : DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry f ∘ fun θ' : ℝ => (z, θ')) θ
  exact hd.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-! ## The pointwise calculus of `D_θ`, `D_z` on `Iz × Iθ` -/

/-- `D_θ` is additive on the domain, for `SmoothNbhd` functions. -/
theorem Dth_add_of_smoothNbhd {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (f + g) z θ = Work.Spaces.Dth f z θ + Work.Spaces.Dth g z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU (Iz_of_pos hz) hθ
  have h1 := differentiableAt_slice_snd hf hy
  have h2 := differentiableAt_slice_snd hg hy
  have hd : deriv (fun θ' => (f + g) z θ') θ
      = deriv (fun θ' => f z θ') θ + deriv (fun θ' => g z θ') θ := by
    rw [show (fun θ' => (f + g) z θ') = (fun θ' => f z θ') + (fun θ' => g z θ') from rfl,
      deriv_add h1 h2]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]; ring

/-- `D_z` is additive on the domain, for `SmoothNbhd` functions. -/
theorem Dz_add_of_smoothNbhd {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dz (f + g) z θ = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU (Iz_of_pos hz) hθ
  have h1 := differentiableAt_slice_fst hf hy
  have h2 := differentiableAt_slice_fst hg hy
  have hd : deriv (fun z' => (f + g) z' θ) z
      = deriv (fun z' => f z' θ) z + deriv (fun z' => g z' θ) z := by
    rw [show (fun z' => (f + g) z' θ) = (fun z' => f z' θ) + (fun z' => g z' θ) from rfl,
      deriv_add h1 h2]
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]; ring

/-- `D_θ` is `ℝ`-homogeneous on the domain, for `SmoothNbhd` functions. -/
theorem Dth_const_mul_of_smoothNbhd (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) z θ = c * Work.Spaces.Dth f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU (Iz_of_pos hz) hθ
  have h1 := differentiableAt_slice_snd hf hy
  have hd : deriv (fun θ' => c * f z θ') θ = c * deriv (fun θ' => f z θ') θ :=
    deriv_const_mul c h1
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]; ring

/-- `D_z` is `ℝ`-homogeneous on the domain, for `SmoothNbhd` functions. -/
theorem Dz_const_mul_of_smoothNbhd (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) z θ = c * Work.Spaces.Dz f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU (Iz_of_pos hz) hθ
  have h1 := differentiableAt_slice_fst hf hy
  have hd : deriv (fun z' => c * f z' θ) z = c * deriv (fun z' => f z' θ) z :=
    deriv_const_mul c h1
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]; ring

/-! ## Congruence of the derivatives on the open quadrant -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there: the
derivative is local and `Qd` is open. -/
theorem Dth_congr_qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  obtain ⟨hz, hθ⟩ := mem_Qd_iff.mp hzθ
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' (mem_Qd_iff.mpr ⟨hz, hθ'⟩)
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
theorem Dz_congr_qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  obtain ⟨hz, hθ⟩ := mem_Qd_iff.mp hzθ
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ (mem_Qd_iff.mpr ⟨hz', hθ⟩)
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-! ## The Cauchy–Schwarz constant of the new pairing -/

/-- **The Cauchy–Schwarz bound of `HkIPStep 1 1 IP`, with explicit constant `9·CC`.**  Each
of the three pairings is bounded by `CC·|f|_{ℋ^{n+1}}|g|_{ℋ^{n+1}}`, because
`|h|_{ℋ^n} ≤ |h|_{ℋ^{n+1}}` for `h = f, D_θf, D_zf` (and likewise in `g`), and there are
three of them. -/
theorem HkIPStep_cs_fts (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {CC : ℝ} (hCC : 0 < CC)
    (hcs : ∀ f g : ℝ → ℝ → ℝ, Work.FTS.CoercivityStep.HkReg α n f →
      Work.FTS.CoercivityStep.HkReg α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) :
    ∀ f g : ℝ → ℝ → ℝ, Work.FTS.CoercivityStep.HkReg α (n + 1) f →
      Work.FTS.CoercivityStep.HkReg α (n + 1) g →
      |Work.Coercivity.HkIPStep 1 1 IP f g|
        ≤ (9 * CC) * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
  intro f g hf hg
  have hfm : Work.Spaces.HkMem α (n + 1) f := hf.2
  have hgm : Work.Spaces.HkMem α (n + 1) g := hg.2
  have hf0 : Work.FTS.CoercivityStep.HkReg α n f := HkReg_mono hf
  have hg0 : Work.FTS.CoercivityStep.HkReg α n g := HkReg_mono hg
  have hf1 : Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dth f) := HkReg_dth hα hf
  have hg1 : Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dth g) := HkReg_dth hα hg
  have hf2 : Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dz f) := HkReg_dz hf
  have hg2 : Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dz g) := HkReg_dz hg
  have hN0f : Work.Spaces.HkNorm α n f ≤ Work.Spaces.HkNorm α (n + 1) f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hfm)
  have hN0g : Work.Spaces.HkNorm α n g ≤ Work.Spaces.HkNorm α (n + 1) g := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hgm)
  have hN1f : Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkNorm α (n + 1) f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hfm)
  have hN1g : Work.Spaces.HkNorm α n (Work.Spaces.Dth g)
      ≤ Work.Spaces.HkNorm α (n + 1) g := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hgm)
  have hN2f : Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
      ≤ Work.Spaces.HkNorm α (n + 1) f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dz_le α n hf.1 hfm)
  have hN2g : Work.Spaces.HkNorm α n (Work.Spaces.Dz g)
      ≤ Work.Spaces.HkNorm α (n + 1) g := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dz_le α n hg.1 hgm)
  have hNf : 0 ≤ Work.Spaces.HkNorm α (n + 1) f := Work.Spaces.HkNorm_nonneg α (n + 1) f
  have hNg : 0 ≤ Work.Spaces.HkNorm α (n + 1) g := Work.Spaces.HkNorm_nonneg α (n + 1) g
  have hNf' : 0 ≤ Work.Spaces.HkNorm α n f := Work.Spaces.HkNorm_nonneg α n f
  have hNg' : 0 ≤ Work.Spaces.HkNorm α n g := Work.Spaces.HkNorm_nonneg α n g
  have e1 : CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN0f hCC.le) hN0g hNg'
      (mul_nonneg hCC.le hNf)
  have e2 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
      * Work.Spaces.HkNorm α n (Work.Spaces.Dth g)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN1f hCC.le) hN1g
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC.le hNf)
  have e3 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
      * Work.Spaces.HkNorm α n (Work.Spaces.Dz g)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN2f hCC.le) hN2g
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC.le hNf)
  have h1 := hcs f g hf0 hg0
  have h2 := hcs (Work.Spaces.Dth f) (Work.Spaces.Dth g) hf1 hg1
  have h3 := hcs (Work.Spaces.Dz f) (Work.Spaces.Dz g) hf2 hg2
  have habs : |Work.Coercivity.HkIPStep 1 1 IP f g|
      ≤ |IP f g| + |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
        + |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
    simp only [Work.Coercivity.HkIPStep, one_mul]
    have hA := abs_add_le (IP f g + IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
      (IP (Work.Spaces.Dz f) (Work.Spaces.Dz g))
    have hB := abs_add_le (IP f g) (IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
    linarith
  refine le_trans habs ?_
  have e4 : |IP f g| ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    le_trans h1 e1
  have e5 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    le_trans h2 e2
  have e6 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    le_trans h3 e3
  have hP : 0 ≤ Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g :=
    mul_nonneg hNf hNg
  nlinarith [e4, e5, e6, hCC, hP]

/-! ## Congruence of the pairing in its second argument -/

/-- The congruence clause of the pairing, transported to the second argument by
symmetry. -/
theorem congr_qd_snd {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : Work.FTS.CoercivityStep.IsHkIPCore_fts α k IP) {f g g' : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α k f)
    (hg : Work.FTS.CoercivityStep.HkReg α k g)
    (hg' : Work.FTS.CoercivityStep.HkReg α k g')
    (hgg' : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd → g z θ = g' z θ) :
    IP f g = IP f g' := by
  rw [h.symm f g, h.symm f g']
  exact h.congr_qd g g' f hg hg' hf hgg'

/-! ## Regularity of the derivative-sums of a sum

For `f, g ∈ HkReg α (n+1)` with `f + g ∈ HkReg α (n+1)`, the functions `D_θf + D_θg` and
`D_zf + D_zg` are again of class `HkReg α n`: they are smooth (closure of `SmoothNbhd`
under addition) and their `ℋ^n` integrand is honest, because on `(0,∞) × I_θ` they agree
with `D_θ(f+g)`, resp. `D_z(f+g)`, whose integrand is honest by `HkReg_dth`/`HkReg_dz`
applied to the *sum*. -/

theorem HkReg_dth_add {α : ℝ} (hα : 0 < α) {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f)
    (hg : Work.FTS.CoercivityStep.HkReg α (n + 1) g)
    (hfg : Work.FTS.CoercivityStep.HkReg α (n + 1) (f + g)) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dth f + Work.Spaces.Dth g) :=
  ⟨SmoothNbhd_add hf.1.Dth hg.1.Dth,
    Work.Coercivity.HkMem_congr_Ioi α n (HkReg_dth hα hfg).2
      (fun z hz θ hθ => Dth_add_of_smoothNbhd hf.1 hg.1 hz hθ)⟩

theorem HkReg_dz_add {α : ℝ} {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f)
    (hg : Work.FTS.CoercivityStep.HkReg α (n + 1) g)
    (hfg : Work.FTS.CoercivityStep.HkReg α (n + 1) (f + g)) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dz f + Work.Spaces.Dz g) :=
  ⟨SmoothNbhd_add hf.1.Dz hg.1.Dz,
    Work.Coercivity.HkMem_congr_Ioi α n (HkReg_dz hfg).2
      (fun z hz θ hθ => Dz_add_of_smoothNbhd hf.1 hg.1 hz hθ)⟩


/-! ## Closure of `HkMem` under scalar multiplication

The last ingredient is that the `ℋ^k`-integrand of a scalar multiple is the multiple of
the integrand: for smooth `f` the iterated operators `D_z^i`, `D_z^jD_θ^i` are
`ℝ`-homogeneous on the neighbourhood `nbhU` on which `SmoothNbhd` is stated (the
totalised `deriv` being homogeneous on a *differentiable* argument), whence

  `HkIntegrand α k (c·f) = c² · HkIntegrand α k f`  on `Iz × Iθ`,

and the honesty of the integrand transfers by `Integrable.congr`. -/

/-- `D_z^i(c·f) = c·D_z^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem DzIter_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (i : ℕ) :
    Set.EqOn (fun y : ℝ × ℝ => Work.Spaces.DzIter i (fun z θ => c * f z θ) y.1 y.2)
      (fun y : ℝ × ℝ => c * Work.Spaces.DzIter i f y.1 y.2) Work.Spaces.nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.Spaces.nbhU :=
        (Continuous.prodMk_left θ).continuousAt.eventually
          (Work.Spaces.isOpen_nbhU.mem_nhds hy)
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => c * Work.Spaces.DzIter n f z' θ) := by
        filter_upwards [hnb] with z' hz'
        exact ih hz'
      have h1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        differentiableAt_slice_fst (Work.Spaces.SmoothNbhd.DzIter hf n) hy
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) z
          = c * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z := by
        rw [heq.deriv_eq]
        exact deriv_const_mul c h1
      show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) z
          = c * (z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z)
      rw [hderiv]; ring

/-- `D_θ^i(c·f) = c·D_θ^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem DthIter_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (i : ℕ) :
    Set.EqOn (fun y : ℝ × ℝ => Work.Spaces.DthIter i (fun z θ => c * f z θ) y.1 y.2)
      (fun y : ℝ × ℝ => c * Work.Spaces.DthIter i f y.1 y.2) Work.Spaces.nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.Spaces.nbhU :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.Spaces.isOpen_nbhU.mem_nhds hy)
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => c * Work.Spaces.DthIter n f z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        differentiableAt_slice_snd (Work.Spaces.SmoothNbhd.DthIter hf n) hy
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') θ
          = c * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ := by
        rw [heq.deriv_eq]
        exact deriv_const_mul c h1
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') θ
          = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ)
      rw [hderiv]; ring

/-- `D_z^jD_θ^i(c·f) = c·D_z^jD_θ^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem mixed_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (j i : ℕ) {z θ : ℝ}
    (hy : (z, θ) ∈ Work.Spaces.nbhU) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ := by
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c * f z θ)))
      (Function.uncurry (fun z θ => c * Work.Spaces.DthIter i f z θ)) Work.Spaces.nbhU := by
    intro y hy'
    obtain ⟨z', θ'⟩ := y
    simpa only [Function.uncurry] using DthIter_const_mul_nbh c hf i hy'
  have e1 : Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c * f z θ)) z θ
      = Work.Spaces.DzIter j (fun z θ => c * Work.Spaces.DthIter i f z θ) z θ :=
    Work.Spaces.DzIter_congr hEq j hy
  have e2 : Work.Spaces.DzIter j (fun z θ => c * Work.Spaces.DthIter i f z θ) z θ
      = c * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ :=
    DzIter_const_mul_nbh c (Work.Spaces.SmoothNbhd.DthIter hf i) j hy
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c * f z θ)) z θ
      = c * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ
  rw [e1, e2]

/-- The `ℋ^k`-integrand of a scalar multiple, for smooth `f`: it is `c²` times the
integrand of `f`. -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hZ : ∀ i, Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter i f z θ := fun i => DzIter_const_mul_nbh c hf i hy
  have hM : ∀ j i, Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ := fun j i => mixed_const_mul_nbh c hf j i hy
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hZ i]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, hM j i]; ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  simp only [Work.Spaces.HkIntegrand]
  rw [h1, h2]; ring

/-- `Iz` is measurable. -/
theorem measurableSet_Iz_fts : MeasurableSet Work.Spaces.Iz := by
  simpa only [Work.Spaces.Iz] using measurableSet_Ici

/-- `Iθ` is measurable. -/
theorem measurableSet_Iθ_fts : MeasurableSet Work.Spaces.Iθ := by
  simpa only [Work.Spaces.Iθ] using measurableSet_Icc

/-- **`ℋ^k` is closed under multiplication by a scalar.** -/
theorem HkMem_smul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  have hae : ∀ z ∈ Work.Spaces.Iz,
      (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ) :=
    fun z hz => (ae_restrict_mem measurableSet_Iθ_fts).mono
      (fun θ hθ => HkIntegrand_const_mul α k c hf hz hθ)
  have hzeq : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    rw [integral_congr_ae (hae z hz), integral_const_mul]
  exact ⟨fun z hz => ((hm.1 z hz).const_mul (c ^ 2)).congr (hae z hz).symm,
    IntegrableOn.congr_fun (hm.2.const_mul (c ^ 2)) (fun z hz => (hzeq z hz).symm)
      measurableSet_Iz_fts⟩

/-! ## Regularity of the derivative of a scalar multiple

`D_θ(c·f)` and `c·D_θf` agree on `(0,∞) × I_θ`, so each is in `HkReg α n` as soon as one
of them is; the membership of `c·D_θf` is the `HkMem`-closure under scalar multiplication
(`HkMem_smul`). -/

theorem HkReg_const_mul_dth {α : ℝ} (hα : 0 < α) {n : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (fun z θ => c * Work.Spaces.Dth f z θ) :=
  ⟨SmoothNbhd_const_mul c hf.1.Dth,
    HkMem_smul α n c hf.1.Dth (HkReg_dth hα hf).2⟩

theorem HkReg_const_mul_dz {α : ℝ} {n : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (fun z θ => c * Work.Spaces.Dz f z θ) :=
  ⟨SmoothNbhd_const_mul c hf.1.Dz,
    HkMem_smul α n c hf.1.Dz (HkReg_dz hf).2⟩

theorem HkReg_dth_const_mul {α : ℝ} (hα : 0 < α) {n : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dth (fun z θ => c * f z θ)) :=
  ⟨Work.Spaces.SmoothNbhd.Dth (SmoothNbhd_const_mul c hf.1),
    Work.Coercivity.HkMem_congr_Ioi α n
      (HkMem_smul α n c hf.1.Dth (HkReg_dth hα hf).2)
      (fun z hz θ hθ => (Dth_const_mul_of_smoothNbhd c hf.1 hz hθ).symm)⟩

theorem HkReg_dz_const_mul {α : ℝ} {n : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α (n + 1) f) :
    Work.FTS.CoercivityStep.HkReg α n (Work.Spaces.Dz (fun z θ => c * f z θ)) :=
  ⟨Work.Spaces.SmoothNbhd.Dz (SmoothNbhd_const_mul c hf.1),
    Work.Coercivity.HkMem_congr_Ioi α n
      (HkMem_smul α n c hf.1.Dz (HkReg_dz hf).2)
      (fun z hz θ hθ => (Dz_const_mul_of_smoothNbhd c hf.1 hz hθ).symm)⟩

/-! ## The induction step -/

theorem HkIPStep_core (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : Work.FTS.CoercivityStep.IsHkIPCore_fts α n IP) :
    Work.FTS.CoercivityStep.IsHkIPCore_fts α (n + 1) (Work.Coercivity.HkIPStep 1 1 IP) := by
  refine { add_fst := ?add_fst, smul_fst := ?smul_fst, add_snd := ?add_snd,
           smul_snd := ?smul_snd, symm := ?symm, congr_qd := ?congr_qd,
           nonneg := ?nonneg, cs := ?cs, le_self := ?le_self, upper := ?upper }
  case add_fst =>
    intro f₁ f₂ g hf₁ hf₂ hg hf₁₂
    have e0 : IP (f₁ + f₂) g = IP f₁ g + IP f₂ g :=
      h.add_fst f₁ f₂ g (HkReg_mono hf₁) (HkReg_mono hf₂) (HkReg_mono hg) (HkReg_mono hf₁₂)
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [h.congr_qd (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (HkReg_dth hα hf₁₂) (HkReg_dth_add hα hf₁ hf₂ hf₁₂) (HkReg_dth hα hg)
        (fun z θ hq => Dth_add_of_smoothNbhd hf₁.1 hf₂.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.add_fst (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (HkReg_dth hα hf₁) (HkReg_dth hα hf₂) (HkReg_dth hα hg)
        (HkReg_dth_add hα hf₁ hf₂ hf₁₂)
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [h.congr_qd (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (HkReg_dz hf₁₂) (HkReg_dz_add hf₁ hf₂ hf₁₂) (HkReg_dz hg)
        (fun z θ hq => Dz_add_of_smoothNbhd hf₁.1 hf₂.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.add_fst (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (HkReg_dz hf₁) (HkReg_dz hf₂) (HkReg_dz hg) (HkReg_dz_add hf₁ hf₂ hf₁₂)
    simp only [Work.Coercivity.HkIPStep, one_mul]
    rw [e0, e1, e2]
    ring
  case smul_fst =>
    intro c f g hf hg
    have e0 : IP (fun z θ => c * f z θ) g = c * IP f g :=
      h.smul_fst c f g (HkReg_mono hf) (HkReg_mono hg)
    have e1 : IP (Work.Spaces.Dth (fun z θ => c * f z θ)) (Work.Spaces.Dth g)
        = c * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g) := by
      rw [h.congr_qd (Work.Spaces.Dth (fun z θ => c * f z θ))
        (fun z θ => c * Work.Spaces.Dth f z θ) (Work.Spaces.Dth g)
        (HkReg_dth_const_mul hα c hf) (HkReg_const_mul_dth hα c hf) (HkReg_dth hα hg)
        (fun z θ hq => Dth_const_mul_of_smoothNbhd c hf.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.smul_fst c (Work.Spaces.Dth f) (Work.Spaces.Dth g)
        (HkReg_dth hα hf) (HkReg_dth hα hg)
    have e2 : IP (Work.Spaces.Dz (fun z θ => c * f z θ)) (Work.Spaces.Dz g)
        = c * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := by
      rw [h.congr_qd (Work.Spaces.Dz (fun z θ => c * f z θ))
        (fun z θ => c * Work.Spaces.Dz f z θ) (Work.Spaces.Dz g)
        (HkReg_dz_const_mul c hf) (HkReg_const_mul_dz c hf) (HkReg_dz hg)
        (fun z θ hq => Dz_const_mul_of_smoothNbhd c hf.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.smul_fst c (Work.Spaces.Dz f) (Work.Spaces.Dz g)
        (HkReg_dz hf) (HkReg_dz hg)
    simp only [Work.Coercivity.HkIPStep, one_mul]
    rw [e0, e1, e2]
    ring
  case add_snd =>
    intro f g₁ g₂ hf hg₁ hg₂ hg₁₂
    have e0 : IP f (g₁ + g₂) = IP f g₁ + IP f g₂ :=
      h.add_snd f g₁ g₂ (HkReg_mono hf) (HkReg_mono hg₁) (HkReg_mono hg₂) (HkReg_mono hg₁₂)
    have e1 : IP (Work.Spaces.Dth f) (Work.Spaces.Dth (g₁ + g₂))
        = IP (Work.Spaces.Dth f) (Work.Spaces.Dth g₁)
          + IP (Work.Spaces.Dth f) (Work.Spaces.Dth g₂) := by
      rw [congr_qd_snd h (HkReg_dth hα hf) (HkReg_dth hα hg₁₂)
        (HkReg_dth_add hα hg₁ hg₂ hg₁₂)
        (fun z θ hq => Dth_add_of_smoothNbhd hg₁.1 hg₂.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.add_snd (Work.Spaces.Dth f) (Work.Spaces.Dth g₁) (Work.Spaces.Dth g₂)
        (HkReg_dth hα hf) (HkReg_dth hα hg₁) (HkReg_dth hα hg₂)
        (HkReg_dth_add hα hg₁ hg₂ hg₁₂)
    have e2 : IP (Work.Spaces.Dz f) (Work.Spaces.Dz (g₁ + g₂))
        = IP (Work.Spaces.Dz f) (Work.Spaces.Dz g₁)
          + IP (Work.Spaces.Dz f) (Work.Spaces.Dz g₂) := by
      rw [congr_qd_snd h (HkReg_dz hf) (HkReg_dz hg₁₂) (HkReg_dz_add hg₁ hg₂ hg₁₂)
        (fun z θ hq => Dz_add_of_smoothNbhd hg₁.1 hg₂.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.add_snd (Work.Spaces.Dz f) (Work.Spaces.Dz g₁) (Work.Spaces.Dz g₂)
        (HkReg_dz hf) (HkReg_dz hg₁) (HkReg_dz hg₂) (HkReg_dz_add hg₁ hg₂ hg₁₂)
    simp only [Work.Coercivity.HkIPStep, one_mul]
    rw [e0, e1, e2]
    ring
  case smul_snd =>
    intro c f g hf hg
    have e0 : IP f (fun z θ => c * g z θ) = c * IP f g :=
      h.smul_snd c f g (HkReg_mono hf) (HkReg_mono hg)
    have e1 : IP (Work.Spaces.Dth f) (Work.Spaces.Dth (fun z θ => c * g z θ))
        = c * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g) := by
      rw [congr_qd_snd h (HkReg_dth hα hf) (HkReg_dth_const_mul hα c hg)
          (HkReg_const_mul_dth hα c hg)
          (fun z θ hq => Dth_const_mul_of_smoothNbhd c hg.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.smul_snd c (Work.Spaces.Dth f) (Work.Spaces.Dth g)
        (HkReg_dth hα hf) (HkReg_dth hα hg)
    have e2 : IP (Work.Spaces.Dz f) (Work.Spaces.Dz (fun z θ => c * g z θ))
        = c * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := by
      rw [congr_qd_snd h (HkReg_dz hf) (HkReg_dz_const_mul c hg) (HkReg_const_mul_dz c hg)
          (fun z θ hq => Dz_const_mul_of_smoothNbhd c hg.1 (Qd_pos_fst hq) (Qd_mem_snd hq))]
      exact h.smul_snd c (Work.Spaces.Dz f) (Work.Spaces.Dz g)
        (HkReg_dz hf) (HkReg_dz hg)
    simp only [Work.Coercivity.HkIPStep, one_mul]
    rw [e0, e1, e2]
    ring
  case symm =>
    intro f g
    simp only [Work.Coercivity.HkIPStep, one_mul, h.symm f g,
      h.symm (Work.Spaces.Dth f) (Work.Spaces.Dth g),
      h.symm (Work.Spaces.Dz f) (Work.Spaces.Dz g)]
  case congr_qd =>
    intro f f' g hf hf' hg hfg
    have e0 : IP f g = IP f' g :=
      h.congr_qd f f' g (HkReg_mono hf) (HkReg_mono hf') (HkReg_mono hg) hfg
    have e1 : IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f') (Work.Spaces.Dth g) :=
      h.congr_qd (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
        (HkReg_dth hα hf) (HkReg_dth hα hf') (HkReg_dth hα hg) (Dth_congr_qd hfg)
    have e2 : IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f') (Work.Spaces.Dz g) :=
      h.congr_qd (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
        (HkReg_dz hf) (HkReg_dz hf') (HkReg_dz hg) (Dz_congr_qd hfg)
    simp only [Work.Coercivity.HkIPStep, one_mul, e0, e1, e2]
  case nonneg =>
    intro u
    simp only [Work.Coercivity.HkIPStep, one_mul]
    linarith [h.nonneg u, h.nonneg (Work.Spaces.Dth u), h.nonneg (Work.Spaces.Dz u)]
  case cs =>
    obtain ⟨C₀, hC₀, hcs₀⟩ := h.cs
    exact ⟨9 * C₀, by linarith, HkIPStep_cs_fts α hα n hC₀ hcs₀⟩
  case le_self =>
    intro f hf
    have hf0 : Work.Coercivity.HkAdm α n f :=
      Work.FTS.CoercivityStep.Norm.HkAdm_mono α (Nat.le_succ n) hf
    obtain ⟨hf1, hf2⟩ := Work.Coercivity.HkAdm_dth α n hf
    have hm : Work.Spaces.HkMem α (n + 1) f := by
      simpa using hf.2.1 0 0 (by omega)
    have hY : Work.Spaces.HkSq α (n + 1) f
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
          + Work.Spaces.HkSq α n (Work.Spaces.Dz f) :=
      Work.Coercivity.HkSq_succ_le α hα n hn hf.1 hm
    have h0 := h.le_self f hf0
    have h1 := h.le_self (Work.Spaces.Dth f) hf1
    have h2 := h.le_self (Work.Spaces.Dz f) hf2
    simp only [Work.Coercivity.HkIPStep, one_mul]
    linarith
  case upper =>
    obtain ⟨C₀, hC₀, hup⟩ := h.upper
    refine ⟨3 * C₀, by linarith, ?_⟩
    intro f hf
    have hf0 : Work.Coercivity.HkAdm α n f :=
      Work.FTS.CoercivityStep.Norm.HkAdm_mono α (Nat.le_succ n) hf
    obtain ⟨hf1, hf2⟩ := Work.Coercivity.HkAdm_dth α n hf
    have hm : Work.Spaces.HkMem α (n + 1) f := by
      simpa using hf.2.1 0 0 (by omega)
    have h0 := hup f hf0
    have h1 := hup (Work.Spaces.Dth f) hf1
    have h2 := hup (Work.Spaces.Dz f) hf2
    have m0 : Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hm
    have m1 : Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f :=
      Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hm
    have m2 : Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
      Work.FTS.CoercivityStep.Norm.HkSq_Dz_le α n hf.1 hm
    have hX : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
        + Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ 3 * Work.Spaces.HkSq α (n + 1) f := by
      linarith
    have h01 : IP f f + IP (Work.Spaces.Dth f) (Work.Spaces.Dth f)
        + IP (Work.Spaces.Dz f) (Work.Spaces.Dz f)
        ≤ C₀ * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
          + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) := by
      linarith
    simp only [Work.Coercivity.HkIPStep, one_mul]
    calc IP f f + IP (Work.Spaces.Dth f) (Work.Spaces.Dth f)
          + IP (Work.Spaces.Dz f) (Work.Spaces.Dz f)
        ≤ C₀ * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) := h01
      _ ≤ C₀ * (3 * Work.Spaces.HkSq α (n + 1) f) :=
          mul_le_mul_of_nonneg_left hX (le_of_lt hC₀)
      _ = 3 * C₀ * Work.Spaces.HkSq α (n + 1) f := by ring

end Work.FTS.CoercivityStep.Step
