import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump_aux_independent_core
import Submission.Commons.Geometry.Ulam.exists_odd_section_solution
import Submission.Commons.Geometry.Ulam.odd_transition_volterra_fixed_point

/-!
# Odd-dimension transition slopes: the Volterra data

This file sets up the area `Work.OddVolterra` for the odd-dimensional case
`d = 2 n + 1` (`n ≥ 1`) of Ryabogin's theorem.  The paper's transition-slope
argument (`s ∈ [1 - 3τ, 1]`) differentiates the two moment equations

`(A)  ∫_{-x s}^{y s} (f t² - L(s,t)²)^{n+1/2} dt = C / √(1+s²)`,
`(B)  ∫_{-x s}^{y s} (f t² - L(s,t)²)^{n-1/2} ∂_s L(s,t) dt = 0`,

(`L(s,t) = s t + h s`, `f` the envelope of the curve `(x,y)`, so that `±x s`,
`y s` are the two intersections of the line `L(s,·)` with `±f`) and rewrites
the result, after the change of variables `t = -x(σ)`, `t = y(σ)`, as the
Abel-type system

`-∫_s^1 [K₁(s,σ,-x σ) x'(σ) + K₁(s,σ,y σ) y'(σ)] dσ/√(σ-s) = Q₁(s)`,
`-∫_s^1 [K₂(s,σ,-x σ) x'(σ) + K₂(s,σ,y σ) y'(σ)] dσ/√(σ-s) = Q₂(s)`,

which Abel-inverts (NRZ Lemma 8) to the pure integral system (the paper's
`(hah44)`)

`𝐆(s, Z(s)) = ∫_s^1 𝚯(s,σ,Z(σ)) dσ + 𝚵(s)`, `Z = (x, y, x', y')`.

All the objects below are the paper's: `K₁`, `K₂` are the Abel kernels built
from the iterated `s`-derivatives `J₁`, `J₂` of the two moment integrands, and
`𝐆`, `𝚯`, `𝚵` are the data of `(hah44)`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra

open Commons.Geometry.Ulam

noncomputable section

/-- The slope parameter window half-width used by the paper.  The perturbation
`h` is supported on the transition window `[1 - 2τ, 1 - τ]`. -/
def tau : ℝ := 1 / 10

/-- The state `(x, y, x', y')` of the transition-slope system. -/
abbrev St : Type := Fin 4 → ℝ

/-- The four-component state attached to a curve `(x, y)` and its derivative. -/
def stateOf (x y : ℝ → ℝ) (s : ℝ) : St := ![x s, y s, deriv x s, deriv y s]

/-- The unperturbed (ball) state `Z₀(s) = (x₀, x₀, x₀', x₀')`, `x₀ = profileX`. -/
def baseState (s : ℝ) : St :=
  ![profileX s, profileX s, deriv profileX s, deriv profileX s]

/-- The affine line `L(s,t) = s t + h s` cutting the body. -/
def line (h : ℝ → ℝ) (s t : ℝ) : ℝ := s * t + h s

/-- The slope derivative `∂L/∂s = t + h'(s)`. -/
def lineSlope (h : ℝ → ℝ) (s t : ℝ) : ℝ := t + deriv h s

/-- The divided difference `H(s,σ) = (h σ - h s)/(σ - s)`, in the paper's
integral form `∫_0^1 h'(s + τ(σ-s)) dτ`, which is smooth in `(s,σ)` whenever
`h` is `C¹`. -/
def hquot (h : ℝ → ℝ) (s σ : ℝ) : ℝ := ∫ τ in (0 : ℝ)..1, deriv h (s + τ * (σ - s))

/-- The radicand `ψ_s(t) = f(t)² - L(s,t)²` of the moment equations. -/
def psi (h f : ℝ → ℝ) (s t : ℝ) : ℝ := f t ^ 2 - line h s t ^ 2

/-- The first moment integrand `ψ^{n+1/2} = ψ^n √ψ`. -/
def momentIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  psi h f s t ^ n * Real.sqrt (psi h f s t)

/-- The second moment (centroid) integrand `ψ^{n-1/2} ∂_s L`. -/
def centroidIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  psi h f s t ^ (n - 1) * Real.sqrt (psi h f s t) * lineSlope h s t

/-- The first moment integral over the section `(-x s, y s)`. -/
def momentF (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), momentIntegrand n h f s t

/-- The second (centroid) moment integral over the section `(-x s, y s)`. -/
def momentH (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), centroidIntegrand n h f s t

/-- The right-hand side of the first moment equation: the ball's constant over
`√(1+s²)`. -/
def momentRHS (n : ℕ) (s : ℝ) : ℝ :=
  oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2)

/-! ## The envelope and the two moment equations -/

/-- `f` is the envelope of the curve `(x, y)` for the slope family `L`: the
line of slope `s` meets `f` at `t = y s` from below and at `t = -x s` from
above, with the parallel-body offset `h s`. -/
def IsEnvelope (h x y f : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → f (y s) ^ 2 = (s * y s + h s) ^ 2) ∧
  (∀ s : ℝ, 0 < s → f (-(x s)) ^ 2 = (s * (-(x s)) + h s) ^ 2)

/-- The two moment equations `(A)` and `(B)` on a set of slopes `S`. -/
def MomentEqsOn (n : ℕ) (C : ℝ) (h x y f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  (∀ s ∈ S, momentF n h x y f s = C / Real.sqrt (1 + s ^ 2)) ∧
  (∀ s ∈ S, momentH n h x y f s = 0)

/-- The section `(-x s, y s)` of the profile is non-degenerate at slope `s`:
the line really cuts the profile, so that the moment integrands are not
identically zero.  (Without this the equations hold trivially, because
`Real.sqrt` of a non-positive base is `0`.) -/
def NondegenerateAt (h x y f : ℝ → ℝ) (s : ℝ) : Prop :=
  ∃ t ∈ Set.Ioo (-(x s)) (y s), 0 < psi h f s t

/-- Anti-vacuity: some section is non-degenerate. -/
def Nondegenerate (h x y f : ℝ → ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ NondegenerateAt h x y f s

/-! ## The Abel kernels `K₁`, `K₂` -/

/-- The numerator `J₁` of the first Abel kernel: the `(n+1)`-st
`s`-derivative of the moment integrand, times the square-root denominator, so
that it stays finite at the root.  Off the diagonal it is the differentiated
numerator; on the diagonal it is the limit value
`(2n+1)!! (-L ∂_sL)^{n+1}`. -/
def J1 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  if σ = s then
    ((Nat.doubleFactorial (2 * n + 1) : ℝ)) *
      (- (line h s t * lineSlope h s t)) ^ (n + 1)
  else
    iteratedDeriv (n + 1)
      (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) s *
      Real.sqrt (psi h (fun t' => line h σ t') s t)

/-- The numerator `J₂` of the second Abel kernel. -/
def J2 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  if σ = s then
    ((Nat.doubleFactorial (2 * n - 1) : ℝ)) *
      (- (line h s t * lineSlope h s t)) ^ n * lineSlope h s t
  else
    iteratedDeriv n
      (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) s *
      Real.sqrt (psi h (fun t' => line h σ t') s t)

/-- The common denominator `√((t + H(s,σ)) (L(σ,t) + L(s,t)))` of the two Abel
kernels, i.e. the square root of `L(σ,t)² - L(s,t)²` divided by `√(σ-s)`. -/
def Kden (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  Real.sqrt ((t + hquot h s σ) * (line h σ t + line h s t))

/-- The first Abel kernel `K₁ = J₁ / √((t+H)(L_σ+L_s))`. -/
def K1 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J1 n h s σ t / Kden h s σ t

/-- The second Abel kernel `K₂ = J₂ / √((t+H)(L_σ+L_s))`. -/
def K2 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ := J2 n h s σ t / Kden h s σ t

/-- The two-component vector `K(s,σ,z,z')` of the paper. -/
def Kvec (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  ![- (K1 n h s σ (-x) * x' + K1 n h s σ y * y'),
    - (K2 n h s σ (-x) * x' + K2 n h s σ y * y')]

/-- The Abel-averaged kernel `G₂(s,σ,z,z') = ∫_0^1 K(s+τ(σ-s),σ,z,z')/√(τ(1-τ)) dτ`. -/
def G2 (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (x y x' y' : ℝ) : Fin 2 → ℝ :=
  fun i : Fin 2 =>
    ∫ τ in (0 : ℝ)..1, (Kvec n h (s + τ * (σ - s)) σ x y x' y') i /
      Real.sqrt (τ * ((1 : ℝ) - τ))

/-! ## The inhomogeneities `E₁`, `E₂` and the right-hand side `Q`, `Q̃`, `𝚵` -/

/-- The first inhomogeneity `E₁(s)`: the `(n+1)`-st derivative of the moment
integrand of the *ball* integrated over the fixed interval `(-x₀(1), x₀(1))`. -/
def E1 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-profileX 1)..(profileX 1),
    iteratedDeriv (n + 1) (fun u : ℝ => (psi h semicircle u t) ^ n *
      Real.sqrt (psi h semicircle u t)) s

/-- The second inhomogeneity `E₂(s)`. -/
def E2 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-profileX 1)..(profileX 1),
    iteratedDeriv n (fun u : ℝ => (psi h semicircle u t) ^ (n - 1) *
      Real.sqrt (psi h semicircle u t) * lineSlope h u t) s

/-- The right-hand side `Q` of the paper's Abel system `(arik)`. -/
def Q (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : Fin 2 → ℝ :=
  ![ - E1 n h s + iteratedDeriv (n + 1) (momentRHS n) s,
     - E2 n h s]

/-- The Abel transform `d/ds ∫_s^1 Q(s')/√(s'-s) ds'` appearing in `(dvi)`. -/
def Qtilde (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : Fin 2 → ℝ :=
  ![(deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 0 / Real.sqrt (v - u)) s),
    (deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 1 / Real.sqrt (v - u)) s)]

/-- The left-hand side `𝚵` of the paper's system `(hah44)`. -/
def Xi (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : St :=
  ![profileX 1, profileX 1, (Qtilde n h s) 0, (Qtilde n h s) 1]

/-- The left-hand side `𝐆` of the paper's system `(hah44)`:
the first two rows are the two auxiliary relations `z = -∫ z' + z₀(1)`, the
last two rows are `-G₂(s,s,z,z')`. -/
def Godd (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (Z : St) : St :=
  ![Z 0, Z 1,
    - (G2 n h s s (Z 0) (Z 1) (Z 2) (Z 3)) 0,
    - (G2 n h s s (Z 0) (Z 1) (Z 2) (Z 3)) 1]

/-- The kernel `𝚯` of the paper's system `(hah44)`:
`𝚯 = - (z', ∂_s G₂(s,σ,z,z'))`. -/
def Theta (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (Z : St) : St :=
  ![- Z 2, - Z 3,
    - (deriv (fun u : ℝ => (G2 n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 0) s),
    - (deriv (fun u : ℝ => (G2 n h u σ (Z 0) (Z 1) (Z 2) (Z 3)) 1) s)]

/-- The system `(hah44)` on a slope interval: the odd-case Volterra equation. -/
def VolterraEqOn (n : ℕ) (h : ℝ → ℝ) (x y : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, Godd n h s (stateOf x y s) =
    (∫ σ in s..(1 : ℝ), Theta n h s σ (stateOf x y σ)) + Xi n h s

/-! ## Elementary API -/

lemma line_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => line h p.1 p.2) := by
  unfold line; fun_prop

lemma lineSlope_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => lineSlope h p.1 p.2) := by
  unfold lineSlope; fun_prop

lemma hquot_self (h : ℝ → ℝ) (s : ℝ) : hquot h s s = deriv h s := by
  unfold hquot
  have hcongr : (fun τ : ℝ => deriv h (s + τ * (s - s))) = fun _ : ℝ => deriv h s := by
    funext τ; ring_nf
  rw [hcongr]
  simp

/-- The divided difference identity `h σ - h s = (σ - s) H(s,σ)`, with
`H(s,σ) = ∫_0^1 h'(s + τ (σ-s)) dτ` the paper's `H`. -/
lemma sub_mul_hquot {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (s σ : ℝ) :
    h σ - h s = (σ - s) * hquot h s σ := by
  have hcont : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hderiv : ∀ x ∈ Set.uIcc s σ, HasDerivAt h (deriv h x) x := by
    intro x _
    exact ((hh.differentiable_one).differentiableAt (x := x)).hasDerivAt
  have hint : IntervalIntegrable (deriv h) volume s σ := hcont.intervalIntegrable _ _
  have hFTC : ∫ u in s..σ, deriv h u = h σ - h s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hf_cont : ContinuousOn (fun τ : ℝ => s + τ * (σ - s)) (Set.uIcc (0:ℝ) 1) := by fun_prop
  have hf' : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun τ : ℝ => s + τ * (σ - s)) (σ - s) x := by
    intro x _
    have h1 : HasDerivAt (fun τ : ℝ => τ * (σ - s)) (σ - s) x := by
      simpa using (hasDerivAt_id x).mul_const (σ - s)
    simpa using h1.const_add s
  have hmul : (∫ τ in (0:ℝ)..1, deriv h (s + τ * (σ - s)) * (σ - s))
      = hquot h s σ * (σ - s) := by
    unfold hquot
    rw [intervalIntegral.integral_mul_const]
  rcases le_total s σ with hle | hge
  · have hc : 0 ≤ σ - s := by linarith
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun τ : ℝ => s + τ * (σ - s)) (f' := fun _ : ℝ => σ - s) (g := deriv h)
      (a := (0:ℝ)) (b := 1) hf_cont hf' (fun x _ => hc)
    have hsub' : (∫ τ in (0:ℝ)..1, deriv h (s + τ * (σ - s)) * (σ - s)) = ∫ u in s..σ, deriv h u := by
      simpa [Function.comp_def] using hsub
    calc h σ - h s = ∫ u in s..σ, deriv h u := hFTC.symm
      _ = ∫ τ in (0:ℝ)..1, deriv h (s + τ * (σ - s)) * (σ - s) := hsub'.symm
      _ = hquot h s σ * (σ - s) := hmul
      _ = (σ - s) * hquot h s σ := by ring
  · have hc : σ - s ≤ 0 := by linarith
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (f := fun τ : ℝ => s + τ * (σ - s)) (f' := fun _ : ℝ => σ - s) (g := deriv h)
      (a := (0:ℝ)) (b := 1) hf_cont hf' (fun x _ => hc)
    have hsub' : (∫ τ in (0:ℝ)..1, deriv h (s + τ * (σ - s)) * (σ - s)) = ∫ u in s..σ, deriv h u := by
      simpa [Function.comp_def] using hsub
    calc h σ - h s = ∫ u in s..σ, deriv h u := hFTC.symm
      _ = ∫ τ in (0:ℝ)..1, deriv h (s + τ * (σ - s)) * (σ - s) := hsub'.symm
      _ = hquot h s σ * (σ - s) := hmul
      _ = (σ - s) * hquot h s σ := by ring

lemma psi_self_right (h : ℝ → ℝ) (s t : ℝ) : psi h (fun t' => line h s t') s t = 0 := by
  unfold psi line; ring

lemma psi_self_right_pos (h : ℝ → ℝ) (s t : ℝ) :
    psi h (fun t' => line h s t') s t ≤ 0 := by
  rw [psi_self_right]

end

end Work.OddVolterra
