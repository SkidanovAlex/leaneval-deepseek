import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The partial derivatives of a function on `ℝ × ℝ`, and the kernel-side iterates

The proof below only uses *plain* partial derivatives of the kernel (never the paper's
`D_z = z ∂_z`, `D_θ = sin 2θ ∂_θ`: those act on the profile `f`), so it is convenient to have
them as named operators on `ℝ × ℝ → ℝ`. -/

/-- `∂₁`: the derivative in the first variable. -/
def partFst (u : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun s : ℝ => u (s, p.2)) p.1

/-- `∂₂`: the derivative in the second variable. -/
def partSnd (u : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun t : ℝ => u (p.1, t)) p.2

/-- The kernel-side iterated partial derivative, built from the outside in:
`Kd K 0 b = ∂₂^b K` and `Kd K (a+1) b = ∂₁ (Kd K a b)`.  It is `∂₁^a ∂₂^b K`, but with the
`∂₁`-iterations on the outside, which is the form in which the two recursions needed below
are cheap. -/
def Kd (K : ℝ × ℝ → ℝ) : ℕ → ℕ → (ℝ × ℝ → ℝ)
  | 0, b => (partSnd^[b]) K
  | (a + 1), b => partFst (Kd K a b)

@[simp] theorem Kd_zero_eq (K : ℝ × ℝ → ℝ) (b : ℕ) : Kd K 0 b = (partSnd^[b]) K := rfl

@[simp] theorem Kd_succ_eq (K : ℝ × ℝ → ℝ) (a b : ℕ) :
    Kd K (a + 1) b = partFst (Kd K a b) := rfl

/-- The shifted profile: `p ↦ g (z e^{-p₁}) (arctan (tan θ · e^{-p₂}))`. -/
def shf (z θ : ℝ) (g : Fn) : ℝ × ℝ → ℝ := fun p => g (zShift z p.1) (thShift θ p.2)

theorem Kd_zero_zero (K : ℝ × ℝ → ℝ) : Kd K 0 0 = K := by
  simp only [Kd_zero_eq, Function.iterate_zero_apply]

theorem Kd_zero_succ (K : ℝ × ℝ → ℝ) (b : ℕ) :
    Kd K 0 (b + 1) = partSnd (Kd K 0 b) := by
  simp only [Kd_zero_eq, Function.iterate_succ_apply']

/-! ## Clairaut, and the two recursions of `Kd` -/

/-- **Clairaut** for the plain partial derivatives on `ℝ × ℝ`. -/
theorem partFst_partSnd_comm {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G) :
    partFst (partSnd G) = partSnd (partFst G) := by
  funext p
  obtain ⟨z, θ⟩ := p
  have h : ContDiffAt ℝ 2 G (z, θ) := hG.contDiffAt
  have h1 := Work.Spaces.deriv_deriv_fst_snd G z θ h
  have h2 := Work.Spaces.deriv_deriv_snd_fst G z θ h
  have hsym := (ContDiffAt.isSymmSndFDerivAt h (by simp : minSmoothness ℝ 2 ≤ 2)).eq (1, 0) (0, 1)
  show partFst (partSnd G) (z, θ) = partSnd (partFst G) (z, θ)
  simp only [partFst, partSnd]
  rw [h1, h2]
  exact hsym

/-- `Kd K a b` is `C^n` for every `n` as soon as `K` is. -/
theorem Kd_smooth (K : ℝ × ℝ → ℝ) (hK : ∀ n : ℕ, ContDiff ℝ n K) (a b : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (Kd K a b) := by
  induction a with
  | zero =>
    induction b with
    | zero => simpa only [Kd_zero_eq, Function.iterate_zero_apply] using hK
    | succ b ih =>
      rw [Kd_zero_succ]
      exact (Work.FTS.StrongEps.KernAux.contDiff_partFst_partSnd (Kd K 0 b) ih).2
  | succ a ih =>
    rw [Kd_succ_eq]
    exact (Work.FTS.StrongEps.KernAux.contDiff_partFst_partSnd (Kd K a b) ih).1

/-- `Kd K a b` has compact support as soon as `K` has. -/
theorem Kd_compact (K : ℝ × ℝ → ℝ) (hK : HasCompactSupport K) (a b : ℕ) :
    HasCompactSupport (Kd K a b) := by
  induction a with
  | zero =>
    induction b with
    | zero => simpa only [Kd_zero_eq, Function.iterate_zero_apply] using hK
    | succ b ih =>
      rw [Kd_zero_succ]
      exact (Work.FTS.StrongEps.KernAux.hasCompactSupport_partFst_partSnd (Kd K 0 b) ih).2
  | succ a ih =>
    rw [Kd_succ_eq]
    exact (Work.FTS.StrongEps.KernAux.hasCompactSupport_partFst_partSnd (Kd K a b) ih).1

/-- The `∂₂`-recursion of `Kd`, obtained from the `∂₁`-recursion by Clairaut. -/
theorem Kd_succ_snd (K : ℝ × ℝ → ℝ) (hK : ∀ n : ℕ, ContDiff ℝ n K) (a b : ℕ) :
    Kd K a (b + 1) = partSnd (Kd K a b) := by
  induction a with
  | zero => exact Kd_zero_succ K b
  | succ a ih =>
    have h1 : Kd K (a + 1) (b + 1) = partFst (partSnd (Kd K a b)) := by
      rw [Kd_succ_eq, ih]
    rw [h1, partFst_partSnd_comm (Kd_smooth K hK a b 2)]
    exact congrArg partSnd (Kd_succ_eq K a b).symm

/-- `Kd K a b` is `∂₁^a ∂₂^b K` in the `iteratedDeriv` nesting of the target statement. -/
theorem Kd_eq (K : ℝ × ℝ → ℝ) (a b : ℕ) :
    Kd K a b = fun p : ℝ × ℝ =>
      iteratedDeriv a (fun s : ℝ => iteratedDeriv b (fun t : ℝ => K (s, t)) p.2) p.1 := by
  induction a with
  | zero =>
    induction b with
    | zero =>
      funext p
      simp only [Kd_zero_eq, Function.iterate_zero_apply, iteratedDeriv_zero]
    | succ b ih =>
      rw [Kd_zero_succ, ih]
      funext p
      simp only [partSnd, iteratedDeriv_succ, iteratedDeriv_zero]
  | succ a ih =>
    rw [Kd_succ_eq, ih]
    funext p
    simp only [partFst, iteratedDeriv_succ]

/-! ## Smoothness of the mixed derivatives of `f`, and of their shifts -/

theorem mixed_forall {f : Fn} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (a b : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed a b f)) Quad :=
  contDiffOn_infty.mp
    (Work.FTS.LocData.contDiffOn_mixed isOpen_Quad (contDiffOn_infty.mpr hf) a b)

/-! ## The partial-routing integral -/

/-- The partially routed integral: `a` kernel-side `z`-derivatives and `b` kernel-side
`θ`-derivatives have been moved onto the kernel, the remaining ones staying on `f`. -/
def Xi (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) (z θ : ℝ) (j i : ℕ) (a b : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p * shf z θ (Work.Spaces.mixed (j - a) (i - b) f) p

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

/-- One `p₁`-integration by parts: the state is unchanged. -/
theorem Xi_z_step (hρ : IsSmoothKernel ρ) {hε : 0 < ε}
    {hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad}
    {z θ : ℝ} {hz : 0 < z} {hθ : θ ∈ Set.Ioo 0 (π / 2)}
    {j i a b : ℕ} (ha : a + 1 ≤ j) :
    Xi ρ ε f z θ j i a b = Xi ρ ε f z θ j i (a + 1) b := by
  have hgsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.mixed (j - (a + 1)) (i - b) f)) Quad :=
    mixed_forall hf (j - (a + 1)) (i - b)
  have hv : ContDiff ℝ 1 (shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f)) :=
    Work.FTS.StrongEps.KernAux.contDiff_shift _ hz hθ hgsm 1
  have hu : ContDiff ℝ 1 (Kd (Jker ρ ε) a b) :=
    Kd_smooth _ (fun n => Jker_smooth hρ ε) a b 1
  have hus : HasCompactSupport (Kd (Jker ρ ε) a b) :=
    Kd_compact _ (Jker_hasCompactSupport hρ.moll hε) a b
  have hIBP : (∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p
        * deriv (fun s : ℝ =>
            shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1)
      = - ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Kd (Jker ρ ε) a b (s, p.2)) p.1
        * shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) p :=
    Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg hu hus hv
  have hshift : ∀ p : ℝ × ℝ,
      deriv (fun s : ℝ =>
        shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1
      = - Work.Spaces.Dz (Work.Spaces.mixed (j - (a + 1)) (i - b) f)
          (zShift z p.1) (thShift θ p.2) := by
    intro p
    simpa only [shf] using
      Work.FTS.StrongEps.KernAux.deriv_shift_fst
        (Work.Spaces.mixed (j - (a + 1)) (i - b) f) hz hθ (hgsm 1) p
  have hDz : Work.Spaces.Dz (Work.Spaces.mixed (j - (a + 1)) (i - b) f)
      = Work.Spaces.mixed (j - a) (i - b) f := by
    have hidx : (j - (a + 1)) + 1 = j - a := by omega
    simp only [Work.Spaces.mixed, ← hidx, Work.Spaces.DzIter_succ]
  have hp : ∀ p : ℝ × ℝ, shf z θ (Work.Spaces.mixed (j - a) (i - b) f) p
      = - deriv (fun s : ℝ =>
          shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1 := by
    intro p
    rw [hshift p, hDz]
    simp only [shf]
    ring
  have hstep : (∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p
        * shf z θ (Work.Spaces.mixed (j - a) (i - b) f) p)
      = - ∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p
        * deriv (fun s : ℝ =>
            shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1 := by
    rw [show (fun p : ℝ × ℝ => Kd (Jker ρ ε) a b p
          * shf z θ (Work.Spaces.mixed (j - a) (i - b) f) p)
        = fun p : ℝ × ℝ => -(Kd (Jker ρ ε) a b p
          * deriv (fun s : ℝ =>
              shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1)
        from by funext p; rw [hp p]; ring,
      integral_neg]
  calc Xi ρ ε f z θ j i a b
      = ∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p
          * shf z θ (Work.Spaces.mixed (j - a) (i - b) f) p := by
        simp only [Xi]
    _ = - ∫ p : ℝ × ℝ, Kd (Jker ρ ε) a b p
          * deriv (fun s : ℝ =>
              shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) (s, p.2)) p.1 := hstep
    _ = - (- ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Kd (Jker ρ ε) a b (s, p.2)) p.1
          * shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) p) := by rw [hIBP]
    _ = ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Kd (Jker ρ ε) a b (s, p.2)) p.1
          * shf z θ (Work.Spaces.mixed (j - (a + 1)) (i - b) f) p := by rw [neg_neg]
    _ = Xi ρ ε f z θ j i (a + 1) b := by
        simp only [Xi, Kd_succ_eq, partFst]

/-- One `p₂`-integration by parts, at the fully routed `z`-index `a = j` (where the profile
carries no `D_z`-derivative, so no commutation of `D_z` and `D_θ` is needed): the routed
`θ`-derivative costs a factor `1/2`. -/
theorem Xi_th_step_j (hρ : IsSmoothKernel ρ) {hε : 0 < ε}
    {hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad}
    {z θ : ℝ} {hz : 0 < z} {hθ : θ ∈ Set.Ioo 0 (π / 2)} (j : ℕ)
    {i b : ℕ} (hb : b + 1 ≤ i) :
    Xi ρ ε f z θ j i j (b + 1) = (1 / 2) * Xi ρ ε f z θ j i j b := by
  have hgsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.mixed 0 (i - (b + 1)) f)) Quad :=
    mixed_forall hf 0 (i - (b + 1))
  have hv : ContDiff ℝ 1 (shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f)) :=
    Work.FTS.StrongEps.KernAux.contDiff_shift _ hz hθ hgsm 1
  have hu : ContDiff ℝ 1 (Kd (Jker ρ ε) j b) :=
    Kd_smooth _ (fun n => Jker_smooth hρ ε) j b 1
  have hus : HasCompactSupport (Kd (Jker ρ ε) j b) :=
    Kd_compact _ (Jker_hasCompactSupport hρ.moll hε) j b
  have hIBP : (∫ p : ℝ × ℝ, deriv (fun t : ℝ => Kd (Jker ρ ε) j b (p.1, t)) p.2
        * shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f) p)
      = - ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j b p
        * deriv (fun t : ℝ =>
            shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f) (p.1, t)) p.2 := by
    have h := Work.FTS.StrongEps.KernAux.integral_mul_partSnd_eq_neg hu hus hv
    rw [h]; ring
  have hshift : ∀ p : ℝ × ℝ,
      deriv (fun t : ℝ =>
        shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f) (p.1, t)) p.2
      = -(1 / 2) * Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
          (zShift z p.1) (thShift θ p.2) := by
    intro p
    simpa only [shf] using
      Work.FTS.StrongEps.KernAux.deriv_shift_snd
        (Work.Spaces.mixed 0 (i - (b + 1)) f) hz hθ (hgsm 1) p
  have hDth : Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
      = Work.Spaces.mixed 0 (i - b) f := by
    have hidx : (i - (b + 1)) + 1 = i - b := by omega
    simp only [Work.Spaces.mixed_zero_left, ← hidx, Work.Spaces.DthIter_succ]
  calc Xi ρ ε f z θ j i j (b + 1)
      = ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Kd (Jker ρ ε) j b (p.1, t)) p.2
          * shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f) p := by
        simp only [Xi, Kd_succ_snd _ (fun n => Jker_smooth hρ ε) j b, partSnd, Nat.sub_self]
    _ = - ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j b p
          * deriv (fun t : ℝ =>
              shf z θ (Work.Spaces.mixed 0 (i - (b + 1)) f) (p.1, t)) p.2 := hIBP
    _ = - ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j b p
          * (-(1 / 2) * Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
              (zShift z p.1) (thShift θ p.2)) := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun p => by simp only [hshift p])
    _ = (1 / 2) * ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j b p
          * Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
              (zShift z p.1) (thShift θ p.2) := by
        rw [show (fun p : ℝ × ℝ => Kd (Jker ρ ε) j b p
              * (-(1 / 2) * Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
                  (zShift z p.1) (thShift θ p.2)))
            = fun p : ℝ × ℝ => (-(1 / 2)) * (Kd (Jker ρ ε) j b p
              * Work.Spaces.Dth (Work.Spaces.mixed 0 (i - (b + 1)) f)
                  (zShift z p.1) (thShift θ p.2)) from by funext p; ring,
          integral_const_mul]
        ring
    _ = (1 / 2) * ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j b p
          * shf z θ (Work.Spaces.mixed 0 (i - b) f) p := by
        rw [hDth]
        simp only [shf]
    _ = (1 / 2) * Xi ρ ε f z θ j i j b := by simp only [Xi, Nat.sub_self]

/-! ## Consequences of the two steps: independence of `a`, and the powers of `2` -/

/-- The `z`-routing steps can be run at will: the value at kernel-index `a` equals the value
at kernel-index `0`. -/
theorem Xi_z_inv0 (hρ : IsSmoothKernel ρ) {hε : 0 < ε}
    {hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad}
    {z θ : ℝ} {hz : 0 < z} {hθ : θ ∈ Set.Ioo 0 (π / 2)}
    {i a b : ℕ} (j : ℕ) (ha : a ≤ j) :
    Xi ρ ε f z θ j i a b = Xi ρ ε f z θ j i 0 b := by
  revert ha
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro ha
    rw [← Xi_z_step (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ)
      (a := a) (b := b) (by omega)]
    exact ih (by omega)

/-- The `z`-index is irrelevant. -/
theorem Xi_z_inv (hρ : IsSmoothKernel ρ) {hε : 0 < ε}
    {hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad}
    {z θ : ℝ} {hz : 0 < z} {hθ : θ ∈ Set.Ioo 0 (π / 2)}
    {i a a' b : ℕ} (j : ℕ) (ha : a ≤ j) (ha' : a' ≤ j) :
    Xi ρ ε f z θ j i a b = Xi ρ ε f z θ j i a' b :=
  (Xi_z_inv0 (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ) j ha).trans
    (Xi_z_inv0 (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ) j ha').symm

/-- The `θ`-routing steps at `a = j` cost a factor `1/2` each: the state at `b = i - d`
is `2^d` times the fully routed state. -/
theorem Xi_th_pow_j (hρ : IsSmoothKernel ρ) {hε : 0 < ε}
    {hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad}
    {z θ : ℝ} {hz : 0 < z} {hθ : θ ∈ Set.Ioo 0 (π / 2)} (j : ℕ)
    {i d : ℕ} (hd : d ≤ i) :
    Xi ρ ε f z θ j i j (i - d) = (2 : ℝ) ^ d * Xi ρ ε f z θ j i j i := by
  revert hd
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have hd' : d ≤ i := by omega
    have hidx : (i - (d + 1)) + 1 = i - d := by omega
    have hstep := Xi_th_step_j (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ)
      (j := j) (i := i) (b := i - (d + 1)) (by omega)
    rw [hidx] at hstep
    calc Xi ρ ε f z θ j i j (i - (d + 1))
        = 2 * ((1 / 2) * Xi ρ ε f z θ j i j (i - (d + 1))) := by ring
      _ = 2 * Xi ρ ε f z θ j i j (i - d) := by rw [← hstep]
      _ = 2 * ((2 : ℝ) ^ d * Xi ρ ε f z θ j i j i) := by rw [ih hd']
      _ = (2 : ℝ) ^ (d + 1) * Xi ρ ε f z θ j i j i := by rw [pow_succ]; ring

/-! ## The target -/

/-- **The partial-routing kernel representation of the framed derivatives of `J_ε f`.**

Each framed derivative that is *not* left on `f` is moved onto the (smooth, compactly supported)
kernel by a partial integration in the shift parameter `p`: the shift is a translation in the log
coordinates `s = log z`, `ζ = log tan θ`, so `D_z (f ∘ shift) = -∂_{p₁}(f ∘ shift)` and
`D_θ (f ∘ shift) = -2 ∂_{p₂}(f ∘ shift)`; the `j-j'` `p₁`-integrations and the `i-i'`
`p₂`-integrations each contribute one `-1`, while the two `-2` of each routed `θ`-derivative cancel
one of them, leaving the coefficient `2 ^ (i - i')`.  (`mixed_Jeps` is the case `j' = j`, `i' = i`;
the all-routed case `j' = i' = 0` is the one used for the smoothing estimates, and the case
`j' = 0, i' = 1` is the one used for the mixed slots with a `Wt`-weight.) -/
theorem mixed_Jeps_kernel_partial (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Work.FTS.Galerkin.Fn} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i j' i' : ℕ) (hj : j' ≤ j)
    (hi : i' ≤ i) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = (2 : ℝ) ^ (i - i') * ∫ p : ℝ × ℝ,
          iteratedDeriv (j - j') (fun s : ℝ => iteratedDeriv (i - i')
            (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1
          * Work.Spaces.mixed j' i' f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  have hbase : Work.Spaces.mixed j i (Jeps ρ ε f) z θ = Xi ρ ε f z θ j i 0 0 := by
    rw [mixed_Jeps ρ hρ.moll hε hf hz hθ j i,
      Jeps_eq_integral ρ ε (Work.Spaces.mixed j i f) hz hθ]
    simp only [Xi, shf, Kd_zero_zero, Nat.sub_zero]
  have e1 : Xi ρ ε f z θ j i 0 0 = (2 : ℝ) ^ i * Xi ρ ε f z θ j i j i := by
    rw [Xi_z_inv (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ)
      (a := 0) (a' := j) (b := 0) j (by omega) (le_refl j)]
    simpa only [Nat.sub_self] using
      Xi_th_pow_j (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ) j (d := i) (le_refl i)
  have e2 : Xi ρ ε f z θ j i (j - j') (i - i') = (2 : ℝ) ^ i' * Xi ρ ε f z θ j i j i := by
    rw [Xi_z_inv (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ)
      (a := j - j') (a' := j) (b := i - i') j (Nat.sub_le j j') (le_refl j)]
    exact Xi_th_pow_j (hρ := hρ) (hε := hε) (hf := hf) (hz := hz) (hθ := hθ) j
      (d := i') hi
  have hpow : (2 : ℝ) ^ (i - i') * 2 ^ i' = 2 ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have hmain : Xi ρ ε f z θ j i 0 0
      = (2 : ℝ) ^ (i - i') * Xi ρ ε f z θ j i (j - j') (i - i') := by
    rw [e1, e2, ← mul_assoc, hpow]
  rw [hbase, hmain]
  congr 1
  simp only [Xi, shf, Kd_eq, Nat.sub_sub_self hj, Nat.sub_sub_self hi]

end

end Work.FTS.StrongEps
