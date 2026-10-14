import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_tail_weight
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBDefs` — the explicit pieces of the `S6` forcing decomposition

The forcing `Σ = VR·D_zF_* + Vθ7·∂_θF_* + cR·F_*` of `Work.FTS.RegExportIface.RXT.SigR`
reduces (`SysAux.SigR_eq_reduced`) to `(β/c)·Γ·Ẑ` with `β = pExp α`, `Γ = Gam β`,
`c = Spaces.c β` and

  `Ẑ = VR·A1 + bR·B1 + cR·F̂`,  `A1 = 2z(1-z)/(1+z)³`,  `F̂ = 2z/(1+z)²`,
  `B1 = (2β/3)·c2m θ·F̂`   (`c2m θ = cos 2θ - sin²θ`).

Choosing the *leading* parts `V0 = (1-μ) + c2m·2β/(1+z)`, `b0 = -3/(1+z) + βF̂/2`,
`C0 = (1+μ) - 2/(1+z) + β sin²θ F̂` of the three coefficients and the two correction brackets

  `α₁ = c2m·(A1 - F̂) - F̂/β`,   `α₂ = B1/2 + sin²θ·F̂`

one has (this is the content of `FBDecomp.forcing_decomp`)

  `Ẑ = E + Lg·α₁ + Kg·α₂ + (2β·Vop Φ̃)·A1 + (2·W)·B1 + (-2·Rop Φ̃)·F̂`,

with `E = V0·A1 + b0·B1 + C0·F̂`, `Lg = L₁₂(F) - 2β/(1+z)`, `Kg = 𝔽K(F) - βF̂` and
`W = Uop β Φ̃ / sin 2θ`.  All the symbols of `E`, `A1`, `B1`, `F̂`, `α₁`, `α₂` are separated
(products `A(z)·B(θ)` of a radial with an angular factor), which is what makes their `mixed`
jets computable; this file records the definitions and the `ContDiffOn` facts on the open
quadrant that the Leibniz bound `JetCalc.LeibBound.abs_mixed_mul_bound` asks for, together
with a finitely-summed version of the additivity of `mixed`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1  The definitions -/

/-- `A1 = z·∂_z F̂ = 2z(1-z)/(1+z)³` (radial). -/
def A1f : ℝ → ℝ → ℝ := fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3

/-- `F̂ = 2z/(1+z)²` (radial). -/
def Fhf : ℝ → ℝ → ℝ := fun z _ => 2 * z / (1 + z) ^ 2

/-- `B1 = (2β/3)·c2m θ·F̂` (separable). -/
def B1f (β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)

/-- `V0 = (1-μ) + c2m θ·2β/(1+z)` (sum of a constant and a separable product). -/
def V0f (μ β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 - μ) + Work.Construction.c2m θ * (2 * β / (1 + z))

/-- `C0 = (1+μ) - 2/(1+z) + β·sin²θ·F̂`. -/
def C0f (μ β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 + μ) - 2 / (1 + z) + β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)

/-- `b0 = -3/(1+z) + βF̂/2`. -/
def b0f (β : ℝ) : ℝ → ℝ → ℝ :=
  fun z _ => -(3 / (1 + z)) + β * (2 * z / (1 + z) ^ 2) / 2

/-- The *leading* part `E = V0·A1 + b0·B1 + C0·F̂` of `Ẑ`: it is `O(z²/(1+z)²)` (the order-`z`
terms cancel exactly). -/
def Ef (μ β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => V0f μ β z θ * A1f z θ + b0f β z θ * B1f β z θ + C0f μ β z θ * Fhf z θ

/-- The bracket `α₁ = c2m·(A1 - F̂) - F̂/β` multiplying `Lg = L₁₂(F) - 2β/(1+z)`. -/
def al1f (β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.c2m θ * (A1f z θ - Fhf z θ) - (1 / β) * Fhf z θ

/-- The bracket `α₂ = B1/2 + sin²θ·F̂` multiplying `Kg = 𝔽K(F) - βF̂`. -/
def al2f (β : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => B1f β z θ / 2 + Real.sin θ ^ 2 * Fhf z θ

/-! ## §2  The definitions unfold to the literal expressions of `SysAux.piece_bounds` -/







/-! ## §3  Smoothness on the open quadrant -/

theorem contDiffOn_uncurry_fst {n : ℕ} {A : ℝ → ℝ} (hA : ContDiffOn ℝ n A (Set.Ioi 0)) :
    ContDiffOn ℝ n (Function.uncurry (fun z _ : ℝ => A z)) Work.FTS.EllipticEst.Q0 :=
  hA.comp contDiffOn_fst (fun p hp => hp.1)

theorem contDiffOn_uncurry_snd {n : ℕ} {B : ℝ → ℝ} (hB : ContDiffOn ℝ n B Set.univ) :
    ContDiffOn ℝ n (Function.uncurry (fun _ θ : ℝ => B θ)) Work.FTS.EllipticEst.Q0 :=
  hB.comp contDiffOn_snd (fun p _ => trivial)

theorem contDiffOn_uncurry_sep {n : ℕ} {A B : ℝ → ℝ} (hA : ContDiffOn ℝ n A (Set.Ioi 0))
    (hB : ContDiffOn ℝ n B Set.univ) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => A z * B θ)) Work.FTS.EllipticEst.Q0 := by
  have h1 := (contDiffOn_uncurry_fst hA).mul (contDiffOn_uncurry_snd hB)
  exact h1.congr (fun p _ => rfl)

theorem contDiffOn_A1z {n : ℕ} : ContDiffOn ℝ n (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3)
    (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z * (1 - z)) (Set.Ioi 0) := by fun_prop
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) := by fun_prop
  refine hnum.div hden (fun z hz => ?_)
  have hz0 : (0:ℝ) < z := hz
  have h1 : (0:ℝ) < 1 + z := by linarith only [hz0]
  exact pow_ne_zero 3 (ne_of_gt h1)

theorem contDiffOn_Fhz {n : ℕ} : ContDiffOn ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2)
    (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z) (Set.Ioi 0) := by fun_prop
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) := by fun_prop
  refine hnum.div hden (fun z hz => ?_)
  have hz0 : (0:ℝ) < z := hz
  have h1 : (0:ℝ) < 1 + z := by linarith only [hz0]
  exact pow_ne_zero 2 (ne_of_gt h1)

theorem contDiffOn_c2m {n : ℕ} :
    ContDiffOn ℝ n (fun θ : ℝ => Work.Construction.c2m θ) Set.univ := by
  rw [show Work.Construction.c2m = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 from rfl]
  fun_prop

theorem contDiffOn_sinsq {n : ℕ} : ContDiffOn ℝ n (fun θ : ℝ => Real.sin θ ^ 2) Set.univ := by
  fun_prop

theorem contDiffOn_add_one {n : ℕ} : ContDiffOn ℝ n (fun z : ℝ => 1 + z) (Set.Ioi 0) := by
  fun_prop


theorem contDiffOn_two_div {n : ℕ} : ContDiffOn ℝ n (fun z : ℝ => 2 / (1 + z)) (Set.Ioi 0) :=
  (contDiffOn_const (c := (2:ℝ))).div contDiffOn_add_one (fun z hz => by
    have hz0 : (0:ℝ) < z := hz
    exact ne_of_gt (by linarith only [hz0] : (0:ℝ) < 1 + z))

theorem contDiffOn_three_div {n : ℕ} : ContDiffOn ℝ n (fun z : ℝ => 3 / (1 + z)) (Set.Ioi 0) :=
  (contDiffOn_const (c := (3:ℝ))).div contDiffOn_add_one (fun z hz => by
    have hz0 : (0:ℝ) < z := hz
    exact ne_of_gt (by linarith only [hz0] : (0:ℝ) < 1 + z))

theorem contDiffOn_A1f (n : ℕ) : ContDiffOn ℝ n (Function.uncurry A1f) Work.FTS.EllipticEst.Q0 :=
  contDiffOn_uncurry_fst contDiffOn_A1z

theorem contDiffOn_Fhf (n : ℕ) : ContDiffOn ℝ n (Function.uncurry Fhf) Work.FTS.EllipticEst.Q0 :=
  contDiffOn_uncurry_fst contDiffOn_Fhz

theorem contDiffOn_B1f (n : ℕ) (β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (B1f β)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi 0) := contDiffOn_Fhz
  have hB : ContDiffOn ℝ n (fun θ : ℝ => (2 * β / 3) * Work.Construction.c2m θ) Set.univ :=
    contDiffOn_const.mul contDiffOn_c2m
  refine (contDiffOn_uncurry_sep hA hB).congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, B1f]
  ring

theorem contDiffOn_V0f (n : ℕ) (μ β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (V0f μ β)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ n (fun z : ℝ => 2 * β / (1 + z)) (Set.Ioi 0) :=
    (contDiffOn_const (c := 2 * β)).div contDiffOn_add_one (fun z hz => by
      have hz0 : (0:ℝ) < z := hz
      exact ne_of_gt (by linarith only [hz0] : (0:ℝ) < 1 + z))
  have hB : ContDiffOn ℝ n (fun θ : ℝ => Work.Construction.c2m θ) Set.univ := contDiffOn_c2m
  have h1 : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ =>
      Work.Construction.c2m θ * (2 * β / (1 + z)))) Work.FTS.EllipticEst.Q0 := by
    refine (contDiffOn_uncurry_sep hA hB).congr (fun p _ => ?_)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry]
    ring
  refine (contDiffOn_const (c := 1 - μ) |>.add h1).congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, V0f, Pi.add_apply]

theorem contDiffOn_b0f (n : ℕ) (β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (b0f β)) Work.FTS.EllipticEst.Q0 := by
  have h4 : ContDiffOn ℝ n (fun z : ℝ => -(3 / (1 + z))) (Set.Ioi 0) :=
    contDiffOn_three_div.neg
  have h5 : ContDiffOn ℝ n (fun z : ℝ => β * (2 * z / (1 + z) ^ 2) / 2) (Set.Ioi 0) :=
    (contDiffOn_const.mul contDiffOn_Fhz).div_const 2
  refine ((contDiffOn_uncurry_fst h4).add (contDiffOn_uncurry_fst h5)).congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, b0f, Pi.add_apply]

theorem contDiffOn_C0f (n : ℕ) (μ β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (C0f μ β)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi 0) := contDiffOn_Fhz
  have hB : ContDiffOn ℝ n (fun θ : ℝ => β * Real.sin θ ^ 2) Set.univ :=
    contDiffOn_const.mul contDiffOn_sinsq
  have h1 : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ =>
      β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2))) Work.FTS.EllipticEst.Q0 := by
    refine (contDiffOn_uncurry_sep hA hB).congr (fun p _ => ?_)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry]
    ring
  have h3 : ContDiffOn ℝ n (fun z : ℝ => (1 + μ) - 2 / (1 + z)) (Set.Ioi 0) :=
    (contDiffOn_const (c := 1 + μ)).sub contDiffOn_two_div
  have h4 : ContDiffOn ℝ n (Function.uncurry (fun z _ : ℝ => (1 + μ) - 2 / (1 + z)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_fst h3
  refine (h4.add h1).congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, C0f, Pi.add_apply]

theorem contDiffOn_al1f (n : ℕ) (β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (al1f β)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ n (fun z : ℝ =>
      2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_A1z.sub contDiffOn_Fhz
  have hB : ContDiffOn ℝ n (fun θ : ℝ => Work.Construction.c2m θ) Set.univ := contDiffOn_c2m
  have h1 := contDiffOn_uncurry_sep hA hB
  have h2 : ContDiffOn ℝ n (Function.uncurry (fun z _ : ℝ => (1 / β) * (2 * z / (1 + z) ^ 2)))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_fst (contDiffOn_const.mul contDiffOn_Fhz)
  have h3 := h1.sub h2
  refine h3.congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, al1f, A1f, Fhf, Pi.sub_apply]
  ring

theorem contDiffOn_al2f (n : ℕ) (β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (al2f β)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi 0) := contDiffOn_Fhz
  have hB1 : ContDiffOn ℝ n (fun θ : ℝ => (2 * β / 3) * Work.Construction.c2m θ / 2)
      Set.univ := (contDiffOn_const.mul contDiffOn_c2m).div_const 2
  have hB2 : ContDiffOn ℝ n (fun θ : ℝ => Real.sin θ ^ 2) Set.univ := contDiffOn_sinsq
  have h1 := (contDiffOn_uncurry_sep hA hB1).add (contDiffOn_uncurry_sep hA hB2)
  refine h1.congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, al2f, B1f, Fhf, Pi.add_apply]
  ring

theorem contDiffOn_Ef (n : ℕ) (μ β : ℝ) :
    ContDiffOn ℝ n (Function.uncurry (Ef μ β)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => V0f μ β z θ * A1f z θ))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_V0f n μ β).mul (contDiffOn_A1f n) |>.congr (fun p _ => rfl)
  have h2 : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => b0f β z θ * B1f β z θ))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_b0f n β).mul (contDiffOn_B1f n β) |>.congr (fun p _ => rfl)
  have h3 : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => C0f μ β z θ * Fhf z θ))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_C0f n μ β).mul (contDiffOn_Fhf n) |>.congr (fun p _ => rfl)
  have h4 := (h1.add h2).add h3
  refine h4.congr (fun p _ => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, Ef, Pi.add_apply]

/-! ## §4  Additivity of `mixed` over a finite sum -/

/-- `D_θ^i` of the zero function is the zero function. -/
theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' : ℝ => (0 : ℝ)) θ = 0
      simp

/-- `D_z^j` of the zero function is the zero function. -/
theorem DzIter_zero_fun (j : ℕ) :
    Work.Spaces.DzIter j (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' : ℝ => (0 : ℝ)) z = 0
      simp


theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const_mul_field]
      ring

theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
      ring

theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, DthIter_const_mul c f i]
  exact DzIter_const_mul c (Work.Spaces.DthIter i f) j

/-- `D_θ` of a function of `z` alone is zero (the `θ`-slice is constant). -/
theorem Dth_z_only (h : ℝ → ℝ) :
    Work.Spaces.Dth (fun z _ : ℝ => h z) = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => (fun z _ : ℝ => h z) z θ') = (fun _ : ℝ => h z) from rfl, deriv_const]
  ring

/-- `D_θ` of the zero function is the zero function. -/
theorem Dth_zero_fun : Work.Spaces.Dth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => (fun _ _ : ℝ => (0 : ℝ)) z θ') = (fun _ : ℝ => (0 : ℝ)) from rfl,
    deriv_const]
  ring

/-- `D_θ^a` of a function of `z` alone vanishes for `a ≥ 1`. -/
theorem DthIter_z_only (h : ℝ → ℝ) (a : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.DthIter a (fun z _ : ℝ => h z) = fun _ _ => 0 := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        simpa using Dth_z_only h
      · rw [Work.Spaces.DthIter_succ, ih hapos, Dth_zero_fun]

/-- Every `θ`-derivative of a function of `z` alone vanishes. -/
theorem mixed_z_only_apply (h : ℝ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ => h z) z θ = 0 := by
  rw [Work.Spaces.mixed, DthIter_z_only h a ha, DzIter_zero_fun]

/-- With no `θ`-derivative, a function of `z` alone behaves as `D_z^b`. -/
theorem mixed_z_only_zero_apply (h : ℝ → ℝ) (b : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b 0 (fun z θ => h z) z θ = Work.Elliptic.DzdIter b h z := by
  rw [Work.Spaces.mixed, Work.Spaces.DthIter_zero]
  exact Work.Elliptic.DzIter_rad h b z θ


end Work.FTS_RegExport.RXT.Sys
