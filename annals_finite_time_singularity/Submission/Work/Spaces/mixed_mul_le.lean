/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz rule for the mixed operators `D_z^j D_θ^i`

The target of this file is `Work.Spaces.mixed_mul_le`: for `SmoothInt` functions `f`, `g` there is
a constant `C > 0` with

`|D_z^j D_θ^i (f g)(z,θ)| ≤ C * ∑_{a ≤ i} ∑_{b ≤ j} |D_z^b D_θ^a f(z,θ)| · |D_z^{j-b} D_θ^{i-a} g(z,θ)|`

for all `(z,θ) ∈ [0,∞) × [0,π/2]`.

The proof rests on the iterated Leibniz rule for two derivation-like operators
(`Work.Spaces.twoOp_iterate_mul_eqOn`), applied

* on the open strip `(-1,∞) × (0,π/2)`, where `SmoothInt` gives *joint* smoothness, to the two
  operators `Dz2`, `Dth2` (the `(z,θ)`-versions of `D_z`, `D_θ`), and
* on the open half-line `(-1,∞)`, to the one-variable operator `OpZ` for the boundary points
  `θ ∈ {0, π/2}` (where the `θ`-derivatives all vanish, so only the `z`-direction is needed).
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.twoOp_iterate_mul_eqOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The operators acting on functions of the pair `(z, θ)` -/

/-- `D_z` acting on functions of the pair `(z, θ)`: `D_z F (z,θ) = z ∂_z F (z,θ)`. -/
def Dz2 (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => p.1 * deriv (fun z => F (z, p.2)) p.1

/-- `D_θ` acting on functions of the pair `(z, θ)`: `D_θ F (z,θ) = sin(2θ) ∂_θ F (z,θ)`. -/
def Dth2 (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Real.sin (2 * p.2) * deriv (fun θ => F (p.1, θ)) p.2

/-- The one-variable operator `φ ↦ (x ↦ x φ'(x))`: the `z`-operator on a `θ`-slice. -/
def OpZ (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

/-- The one-variable operator `φ ↦ (θ ↦ sin(2θ) φ'(θ))`: the `θ`-operator on a `z`-slice. -/
def OpT (φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv φ θ

/-! ## Compatibility with the curried definitions of `Defs.lean` -/

theorem Dz2_uncurry (H : ℝ → ℝ → ℝ) :
    Dz2 (Function.uncurry H) = Function.uncurry (Dz H) := by
  funext p; rfl

theorem Dth2_uncurry (H : ℝ → ℝ → ℝ) :
    Dth2 (Function.uncurry H) = Function.uncurry (Dth H) := by
  funext p; rfl

theorem Dz2_iterate_uncurry (b : ℕ) (H : ℝ → ℝ → ℝ) :
    (Dz2^[b]) (Function.uncurry H) = Function.uncurry (DzIter b H) := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Dz2_uncurry]
      rfl

theorem Dth2_iterate_uncurry (a : ℕ) (H : ℝ → ℝ → ℝ) :
    (Dth2^[a]) (Function.uncurry H) = Function.uncurry (DthIter a H) := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Dth2_uncurry]
      rfl

theorem mixed_uncurry (j i : ℕ) (H : ℝ → ℝ → ℝ) :
    (Dz2^[j]) ((Dth2^[i]) (Function.uncurry H)) = Function.uncurry (mixed j i H) := by
  rw [Dth2_iterate_uncurry, Dz2_iterate_uncurry]
  rfl

private theorem uncurry_mul_le (f g : ℝ → ℝ → ℝ) :
    Function.uncurry (fun z θ => f z θ * g z θ) = Function.uncurry f * Function.uncurry g := rfl

/-! ## Slices of the operators -/

theorem sliceZ_DzIter (b : ℕ) (H : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => DzIter b H z θ) = (OpZ^[b]) (fun z => H z θ) := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show (fun z => z * deriv (fun z' => DzIter n H z' θ) z) = OpZ ((OpZ^[n]) fun z => H z θ)
      rw [ih]
      rfl

theorem sliceTh_DthIter (i : ℕ) (H : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => DthIter i H z θ) = (OpT^[i]) (fun θ => H z θ) := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show (fun θ => Real.sin (2 * θ) * deriv (fun θ' => DthIter n H z θ') θ) =
        OpT ((OpT^[n]) fun θ => H z θ)
      rw [ih]
      rfl

/-! ## Slices of functions: `HasFDerivAt` gives the one-variable derivatives -/

theorem hasDerivAt_slice_fst {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt F F' p) : HasDerivAt (fun z => F (z, p.2)) (F' (1, 0)) p.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)
  exact h.comp_hasDerivAt _ hc

theorem hasDerivAt_slice_snd {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt F F' p) : HasDerivAt (fun θ => F (p.1, θ)) (F' (0, 1)) p.2 := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    HasDerivAt.prodMk (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)
  exact h.comp_hasDerivAt _ hc

/-! ## Smoothness of the partial derivative maps (via `fderiv`) -/

theorem contDiffOn_deriv_fst {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => deriv (fun z => F (z, p.2)) p.1) U := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ F p) (1, 0)) U :=
    hfd.clm_apply contDiffOn_const
  refine h1.congr fun p hp => ?_
  have hd : DifferentiableAt ℝ F p :=
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact (hasDerivAt_slice_fst hd.hasFDerivAt).deriv

theorem contDiffOn_deriv_snd {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => deriv (fun θ => F (p.1, θ)) p.2) U := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) U :=
    hfd.clm_apply contDiffOn_const
  refine h1.congr fun p hp => ?_
  have hd : DifferentiableAt ℝ F p :=
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact (hasDerivAt_slice_snd hd.hasFDerivAt).deriv

theorem contDiffOn_Dz2 {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U) : ContDiffOn ℝ ⊤ (Dz2 F) U := by
  have h1 := contDiffOn_deriv_fst hU hF
  have h2 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1) U := contDiff_fst.contDiffOn
  exact h2.mul h1

theorem contDiffOn_Dth2 {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U) : ContDiffOn ℝ ⊤ (Dth2 F) U := by
  have h1 := contDiffOn_deriv_snd hU hF
  have h2 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) U :=
    (by fun_prop : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2))).contDiffOn
  exact h2.mul h1

theorem contDiffOn_OpZ {φ : ℝ → ℝ} (h : ContDiffOn ℝ ⊤ φ (Ioi (-1))) :
    ContDiffOn ℝ ⊤ (OpZ φ) (Ioi (-1)) := by
  have h1 : ContDiffOn ℝ ⊤ (deriv φ) (Ioi (-1)) := h.deriv_of_isOpen isOpen_Ioi (by simp)
  have h2 : ContDiffOn ℝ ⊤ (fun x : ℝ => x) (Ioi (-1)) := contDiff_id.contDiffOn
  exact h2.mul h1

/-! ## The operator identities on an open set -/

theorem Dz2_mul_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ⊤ A U) (hB : ContDiffOn ℝ ⊤ B U) :
    Set.EqOn (Dz2 (A * B)) (fun p => Dz2 A p * B p + A p * Dz2 B p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B p := (hB.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dz2]
  have hkey : deriv (fun z => (A * B) (z, p.2)) p.1
      = deriv (fun z => A (z, p.2)) p.1 * B p + A p * deriv (fun z => B (z, p.2)) p.1 := by
    rw [show (fun z => (A * B) (z, p.2)) = (fun z => A (z, p.2)) * (fun z => B (z, p.2))
      from rfl]
    exact deriv_mul (hasDerivAt_slice_fst hdA.hasFDerivAt).differentiableAt
      (hasDerivAt_slice_fst hdB.hasFDerivAt).differentiableAt
  rw [hkey]
  ring

theorem Dth2_mul_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ⊤ A U) (hB : ContDiffOn ℝ ⊤ B U) :
    Set.EqOn (Dth2 (A * B)) (fun p => Dth2 A p * B p + A p * Dth2 B p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B p := (hB.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dth2]
  have hkey : deriv (fun θ => (A * B) (p.1, θ)) p.2
      = deriv (fun θ => A (p.1, θ)) p.2 * B p + A p * deriv (fun θ => B (p.1, θ)) p.2 := by
    rw [show (fun θ => (A * B) (p.1, θ)) = (fun θ => A (p.1, θ)) * (fun θ => B (p.1, θ))
      from rfl]
    exact deriv_mul (hasDerivAt_slice_snd hdA.hasFDerivAt).differentiableAt
      (hasDerivAt_slice_snd hdB.hasFDerivAt).differentiableAt
  rw [hkey]
  ring

theorem Dz2_add_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ⊤ A U) (hB : ContDiffOn ℝ ⊤ B U) :
    Set.EqOn (Dz2 (A + B)) (fun p => Dz2 A p + Dz2 B p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B p := (hB.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dz2]
  have hkey : deriv (fun z => (A + B) (z, p.2)) p.1
      = deriv (fun z => A (z, p.2)) p.1 + deriv (fun z => B (z, p.2)) p.1 := by
    rw [show (fun z => (A + B) (z, p.2)) = (fun z => A (z, p.2)) + (fun z => B (z, p.2))
      from rfl]
    exact deriv_add (hasDerivAt_slice_fst hdA.hasFDerivAt).differentiableAt
      (hasDerivAt_slice_fst hdB.hasFDerivAt).differentiableAt
  rw [hkey]; ring

theorem Dth2_add_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ⊤ A U) (hB : ContDiffOn ℝ ⊤ B U) :
    Set.EqOn (Dth2 (A + B)) (fun p => Dth2 A p + Dth2 B p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B p := (hB.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dth2]
  have hkey : deriv (fun θ => (A + B) (p.1, θ)) p.2
      = deriv (fun θ => A (p.1, θ)) p.2 + deriv (fun θ => B (p.1, θ)) p.2 := by
    rw [show (fun θ => (A + B) (p.1, θ)) = (fun θ => A (p.1, θ)) + (fun θ => B (p.1, θ))
      from rfl]
    exact deriv_add (hasDerivAt_slice_snd hdA.hasFDerivAt).differentiableAt
      (hasDerivAt_slice_snd hdB.hasFDerivAt).differentiableAt
  rw [hkey]; ring

theorem Dz2_smul_eqOn {A : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (c : ℝ)
    (hA : ContDiffOn ℝ ⊤ A U) :
    Set.EqOn (Dz2 (fun p => c * A p)) (fun p => c * Dz2 A p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dz2]
  have hkey : deriv (fun z => c * A (z, p.2)) p.1 = c * deriv (fun z => A (z, p.2)) p.1 := by
    rw [show (fun z => c * A (z, p.2)) = (fun z => c * (fun z => A (z, p.2)) z) from rfl]
    exact deriv_const_mul c (hasDerivAt_slice_fst hdA.hasFDerivAt).differentiableAt
  rw [hkey]; ring

theorem Dth2_smul_eqOn {A : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (c : ℝ)
    (hA : ContDiffOn ℝ ⊤ A U) :
    Set.EqOn (Dth2 (fun p => c * A p)) (fun p => c * Dth2 A p) U := by
  intro p hp
  have hdA : DifferentiableAt ℝ A p := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Dth2]
  have hkey : deriv (fun θ => c * A (p.1, θ)) p.2 = c * deriv (fun θ => A (p.1, θ)) p.2 := by
    rw [show (fun θ => c * A (p.1, θ)) = (fun θ => c * (fun θ => A (p.1, θ)) θ) from rfl]
    exact deriv_const_mul c (hasDerivAt_slice_snd hdA.hasFDerivAt).differentiableAt
  rw [hkey]; ring

theorem Dz2_congr_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : Set.EqOn A B U) : Set.EqOn (Dz2 A) (Dz2 B) U := by
  intro p hp
  simp only [Dz2]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcont : Continuous (fun z : ℝ => (z, p.2)) := by fun_prop
  have hmem : {z : ℝ | (z, p.2) ∈ U} ∈ 𝓝 p.1 :=
    (hU.preimage hcont).mem_nhds (by simpa using hp)
  filter_upwards [hmem] with z hz
  exact h hz

theorem Dth2_congr_eqOn {A B : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : Set.EqOn A B U) : Set.EqOn (Dth2 A) (Dth2 B) U := by
  intro p hp
  simp only [Dth2]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcont : Continuous (fun θ : ℝ => (p.1, θ)) := by fun_prop
  have hmem : {θ : ℝ | (p.1, θ) ∈ U} ∈ 𝓝 p.2 :=
    (hU.preimage hcont).mem_nhds (by simpa using hp)
  filter_upwards [hmem] with θ hθ
  exact h hθ

theorem OpZ_mul_eqOn {A B : ℝ → ℝ} (hA : ContDiffOn ℝ ⊤ A (Ioi (-1)))
    (hB : ContDiffOn ℝ ⊤ B (Ioi (-1))) :
    Set.EqOn (OpZ (A * B)) (fun x => OpZ A x * B x + A x * OpZ B x) (Ioi (-1)) := by
  intro x hx
  have hdA : DifferentiableAt ℝ A x := (hA.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B x := (hB.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  simp only [OpZ]
  rw [deriv_mul hdA hdB]
  ring

theorem OpZ_add_eqOn {A B : ℝ → ℝ} (hA : ContDiffOn ℝ ⊤ A (Ioi (-1)))
    (hB : ContDiffOn ℝ ⊤ B (Ioi (-1))) :
    Set.EqOn (OpZ (A + B)) (fun x => OpZ A x + OpZ B x) (Ioi (-1)) := by
  intro x hx
  have hdA : DifferentiableAt ℝ A x := (hA.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B x := (hB.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  simp only [OpZ]
  rw [deriv_add hdA hdB]
  ring

theorem OpZ_smul_eqOn {A : ℝ → ℝ} (c : ℝ) (hA : ContDiffOn ℝ ⊤ A (Ioi (-1))) :
    Set.EqOn (OpZ (fun x => c * A x)) (fun x => c * OpZ A x) (Ioi (-1)) := by
  intro x hx
  have hdA : DifferentiableAt ℝ A x := (hA.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  simp only [OpZ]
  rw [deriv_const_mul c hdA]
  ring

theorem OpZ_congr_eqOn {A B : ℝ → ℝ} (h : Set.EqOn A B (Ioi (-1))) :
    Set.EqOn (OpZ A) (OpZ B) (Ioi (-1)) := by
  intro x hx
  simp only [OpZ]
  congr 1
  exact Filter.EventuallyEq.deriv_eq
    (by filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy; exact h hy)

/-! ## Iterated Leibniz rules, deduced from the abstract two-operator rule -/

theorem Dz2_Dth2_leibniz_eqOn {j i : ℕ} {F G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U) (hG : ContDiffOn ℝ ⊤ G U) :
    Set.EqOn ((Dz2^[j]) ((Dth2^[i]) (F * G)))
      (fun p => ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ)) *
          (((Dz2^[b]) ((Dth2^[a]) F)) p * ((Dz2^[j - b]) ((Dth2^[i - a]) G)) p)) U :=
  twoOp_iterate_mul_eqOn U (fun A => ContDiffOn ℝ ⊤ A U) Dz2 Dth2
    (fun A B hA hB => hA.add hB)
    (fun A B hA hB => hA.mul hB)
    (fun c A hA => by simpa only [Pi.smul_apply, smul_eq_mul] using hA.const_smul c)
    (fun A B hA hB => Dz2_add_eqOn hU hA hB)
    (fun A B hA hB => Dz2_mul_eqOn hU hA hB)
    (fun A B h => Dz2_congr_eqOn hU h)
    (fun A hA => contDiffOn_Dz2 hU hA)
    (fun c A hA => Dz2_smul_eqOn hU c hA)
    (fun A B hA hB => Dth2_add_eqOn hU hA hB)
    (fun A B hA hB => Dth2_mul_eqOn hU hA hB)
    (fun A B h => Dth2_congr_eqOn hU h)
    (fun A hA => contDiffOn_Dth2 hU hA)
    (fun c A hA => Dth2_smul_eqOn hU c hA)
    i j hF hG

theorem OpZ_leibniz_eqOn {j : ℕ} {A B : ℝ → ℝ}
    (hA : ContDiffOn ℝ ⊤ A (Ioi (-1))) (hB : ContDiffOn ℝ ⊤ B (Ioi (-1))) :
    Set.EqOn ((OpZ^[j]) (A * B))
      (fun x => ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * ((OpZ^[b] A) x * (OpZ^[j - b] B) x)) (Ioi (-1)) := by
  have h := twoOp_iterate_mul_eqOn (Ioi (-1))
    (fun A => ContDiffOn ℝ ⊤ A (Ioi (-1))) OpZ 0
    (fun A B hA hB => hA.add hB)
    (fun A B hA hB => hA.mul hB)
    (fun c A hA => by simpa only [Pi.smul_apply, smul_eq_mul] using hA.const_smul c)
    (fun A B hA hB => OpZ_add_eqOn hA hB)
    (fun A B hA hB => OpZ_mul_eqOn hA hB)
    (fun A B h => OpZ_congr_eqOn h)
    (fun A hA => contDiffOn_OpZ hA)
    (fun c A hA => OpZ_smul_eqOn c hA)
    (fun A B _ _ => by intro x _; simp)
    (fun A B _ _ => by intro x _; simp)
    (fun A B _ => by intro x _; simp)
    (fun A _ => contDiffOn_const)
    (fun c A _ => by intro x _; simp)
    0 j hA hB
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero_apply,
    Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero] using h

/-! ## Vanishing of the `θ`-derivatives at the angular boundary -/

theorem OpZ_apply_zero (x : ℝ) : OpZ (fun _ : ℝ => (0 : ℝ)) x = 0 := by simp [OpZ]

theorem OpZ_iterate_zero (j : ℕ) :
    (OpZ^[j]) (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; funext x; exact OpZ_apply_zero x

theorem OpT_apply_eq_zero {φ : ℝ → ℝ} {θ : ℝ} (hθ : Real.sin (2 * θ) = 0) :
    OpT φ θ = 0 := by
  simp only [OpT, hθ, zero_mul]

theorem OpT_iterate_apply_eq_zero {φ : ℝ → ℝ} {θ : ℝ} (hθ : Real.sin (2 * θ) = 0) :
    ∀ i : ℕ, 1 ≤ i → (OpT^[i] φ) θ = 0 := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Function.iterate_succ_apply']
  exact OpT_apply_eq_zero hθ

/-- At an angle `θ` with `sin(2θ) = 0`, all mixed derivatives of `θ`-order `≥ 1` vanish. -/
theorem mixed_eq_zero_of_sin_eq_zero {H : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) {j i : ℕ} (hi : 1 ≤ i) : mixed j i H z θ = 0 := by
  have h1 : (fun z' => DthIter i H z' θ) = fun _ => (0 : ℝ) := by
    funext z'
    rw [show DthIter i H z' θ = (OpT^[i]) (fun θ' => H z' θ') θ
      from congrFun (sliceTh_DthIter i H z') θ]
    exact OpT_iterate_apply_eq_zero hθ i hi
  have h2 : mixed j i H z θ = (OpZ^[j]) (fun z' => DthIter i H z' θ) z :=
    congrFun (sliceZ_DzIter j (DthIter i H) θ) z
  rw [h2, h1, OpZ_iterate_zero j]

/-! ## A summation bound -/

/-- If `L` expands as `∑_{a ≤ i} ∑_{b ≤ j} c a b * (X a b * Y a b)` with nonnegative
coefficients `c a b ≤ C`, then `|L|` is bounded by `C` times the corresponding sum of absolute
values. -/
theorem abs_le_sum_of_expansion {i j : ℕ} {C L : ℝ} (X Y : ℕ → ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (hc0 : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1), 0 ≤ c a b)
    (hcC : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1), c a b ≤ C)
    (hid : L = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      c a b * (X a b * Y a b)) :
    |L| ≤ C * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      |X a b| * |Y a b| := by
  rw [hid]
  calc |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), c a b * (X a b * Y a b)|
      ≤ ∑ a ∈ Finset.range (i + 1),
          |∑ b ∈ Finset.range (j + 1), c a b * (X a b * Y a b)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |c a b * (X a b * Y a b)| :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          c a b * (|X a b| * |Y a b|) := by
        refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
        rw [abs_mul, abs_mul, abs_of_nonneg (hc0 a ha b hb)]
    _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          C * (|X a b| * |Y a b|) := by
        refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => ?_))
        exact mul_le_mul_of_nonneg_right (hcC a ha b hb)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |X a b| * |Y a b| := by
        simp only [Finset.mul_sum]

/-! ## The main estimate -/

theorem mixed_mul_le (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ| ≤
        C * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a) g z θ| := by
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      ((i.choose a : ℝ) * (j.choose b : ℝ)) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hCpos : 0 < 1 + S := by linarith
  refine ⟨1 + S, hCpos, ?_⟩
  intro z hz θ hθ
  have hzIoi : z ∈ Ioi (-1 : ℝ) := by
    simp only [mem_Ioi]
    exact lt_of_lt_of_le (by norm_num) hz
  have hc0 : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) :=
    fun a _ b _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcC : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 1 + S := by
    intro a ha b hb
    have h1 : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ S := by
      rw [hSdef]
      have hinner : (i.choose a : ℝ) * (j.choose b : ℝ) ≤
          ∑ b' ∈ Finset.range (j + 1), (i.choose a : ℝ) * (j.choose b' : ℝ) :=
        Finset.single_le_sum (s := Finset.range (j + 1))
          (f := fun b' => (i.choose a : ℝ) * (j.choose b' : ℝ))
          (fun b' _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb
      have houter : ∑ b' ∈ Finset.range (j + 1), (i.choose a : ℝ) * (j.choose b' : ℝ) ≤
          ∑ a' ∈ Finset.range (i + 1), ∑ b' ∈ Finset.range (j + 1),
            (i.choose a' : ℝ) * (j.choose b' : ℝ) :=
        Finset.single_le_sum (s := Finset.range (i + 1))
          (f := fun a' => ∑ b' ∈ Finset.range (j + 1), (i.choose a' : ℝ) * (j.choose b' : ℝ))
          (fun a' _ => Finset.sum_nonneg (fun b' _ =>
            mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ha
      linarith
    linarith
  by_cases hθint : θ ∈ Ioo 0 (π/2)
  · -- interior point: `SmoothInt` gives joint smoothness on the open strip
    have hU : IsOpen (Ioi (-1 : ℝ) ×ˢ Ioo (0 : ℝ) (π/2)) := isOpen_Ioi.prod isOpen_Ioo
    have hp : (z, θ) ∈ Ioi (-1 : ℝ) ×ˢ Ioo (0 : ℝ) (π/2) := ⟨hzIoi, hθint⟩
    have hleib := Dz2_Dth2_leibniz_eqOn (j := j) (i := i)
      (F := Function.uncurry f) (G := Function.uncurry g) hU hf.1 hg.1
    have hconv : (Dz2^[j]) ((Dth2^[i]) (Function.uncurry f * Function.uncurry g)) (z, θ)
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ)) *
              (mixed b a f z θ * mixed (j - b) (i - a) g z θ) := by
      rw [hleib hp]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [mixed_uncurry, mixed_uncurry]
      rfl
    refine abs_le_sum_of_expansion (fun a b => mixed b a f z θ)
      (fun a b => mixed (j - b) (i - a) g z θ)
      (fun a b => (i.choose a : ℝ) * (j.choose b : ℝ)) hc0 hcC ?_
    rw [← hconv, ← uncurry_mul_le f g, mixed_uncurry]
    rfl
  · -- boundary point: `θ = 0` or `θ = π/2`, so `sin (2θ) = 0`
    have hθcase : θ = 0 ∨ θ = π/2 := by
      obtain ⟨h0, h1⟩ := hθ
      by_contra hcon
      push Not at hcon
      exact hθint ⟨lt_of_le_of_ne h0 (Ne.symm hcon.1), lt_of_le_of_ne h1 hcon.2⟩
    have hθsin : Real.sin (2 * θ) = 0 := by
      rcases hθcase with rfl | rfl
      · simp
      · rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- `i = 0`: only the `z`-direction is involved
      subst hi0
      have hA : ContDiffOn ℝ ⊤ (fun z' => f z' θ) (Ioi (-1)) := hf.2 θ hθ
      have hB : ContDiffOn ℝ ⊤ (fun z' => g z' θ) (Ioi (-1)) := hg.2 θ hθ
      have hmain : mixed j 0 (fun z θ => f z θ * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (mixed b 0 f z θ * mixed (j - b) 0 g z θ) := by
        have h1 : mixed j 0 (fun z θ => f z θ * g z θ) z θ
            = (OpZ^[j]) ((fun z' => f z' θ) * (fun z' => g z' θ)) z :=
          congrFun (sliceZ_DzIter j (fun z θ => f z θ * g z θ) θ) z
        rw [h1, OpZ_leibniz_eqOn (j := j) hA hB hzIoi]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [(congrFun (sliceZ_DzIter b f θ) z).symm,
          (congrFun (sliceZ_DzIter (j - b) g θ) z).symm]
        rfl
      refine abs_le_sum_of_expansion (fun a b => mixed b a f z θ)
        (fun a b => mixed (j - b) (0 - a) g z θ)
        (fun a b => ((0 : ℕ).choose a : ℝ) * (j.choose b : ℝ)) hc0 hcC ?_
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
        Nat.cast_one, one_mul, Nat.sub_zero] using hmain
    · -- `i ≥ 1`: all mixed derivatives occurring vanish
      rw [mixed_eq_zero_of_sin_eq_zero hθsin hipos, abs_zero]
      exact mul_nonneg (le_of_lt hCpos) (Finset.sum_nonneg (fun a _ =>
        Finset.sum_nonneg (fun b _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))

end Work.Spaces
