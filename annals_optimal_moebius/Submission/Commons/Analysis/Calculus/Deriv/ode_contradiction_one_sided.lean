import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
Pure real-analysis fact used by the flat-stop impossibility proof
(Submission/Work/NoFlatStop.lean): a real function `g`, twice continuously
differentiable on an open interval `(-ε, ε)` around 0, with `g 0 = 0`,
`g u ≠ 0` on the right half `(0, ε)`, CANNOT satisfy the one-variable ODE
`g·g'' = 2·(g')²` on `(0, ε)`.

Proof: on `(0,ε)`, `g ≠ 0`, so `h := fun u => (g u)⁻¹` is `C²` on `(0,ε)`;
pointwise `deriv h u = -deriv g u / (g u)^2`, and differentiating once more
and using the ODE gives `deriv (deriv h) u = 0` at every `u ∈ (0,ε)`.
Hence (zero second derivative on the connected open interval) `h` is affine:
`h u = c₁·u + c₀` there, so `g u · (c₁·u + c₀) = 1` on `(0,ε)`.  Now send
`uₙ = ε / (n+2) → 0⁺`: since `g` is continuous at `0` and `g 0 = 0`,
`g(uₙ) → 0`, while `c₁·uₙ + c₀ → c₀`, so the product tends to `0`; but it is
constantly `1`.  Contradiction.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Commons.Analysis.Calculus.Deriv

/-- `u ∈ (0, ε)` implies `u ∈ (-ε, ε)` (the interval is symmetric around 0). -/
lemma mem_Ioo_neg_of_pos {ε u : ℝ} (_hε : 0 < ε) (hu : u ∈ Set.Ioo (0 : ℝ) ε) :
    u ∈ Set.Ioo (-ε) ε := by
  rcases hu with ⟨hu0, huε⟩
  exact ⟨by linarith, huε⟩

/-- First derivative of `1 / g` at a point where `g` is differentiable and
nonzero. -/
lemma deriv_inv_of_nonzero {g : ℝ → ℝ} {u : ℝ} (hdg : DifferentiableAt ℝ g u)
    (hgu : g u ≠ 0) :
    deriv (fun x : ℝ => (g x)⁻¹) u = -(deriv g u) / (g u) ^ 2 := by
  exact (hdg.hasDerivAt.inv hgu).deriv

/-- `g` is `C²` at each point of the right half-interval. -/
lemma contDiffAt_two_of_contDiffOn_two {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε)) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) ε) :
    ContDiffAt ℝ 2 g u := by
  exact (((IsOpen.contDiffOn_iff (s := Set.Ioo (-ε) ε) (f := g) (n := 2) isOpen_Ioo).1 hg)
    (a := u)) (mem_Ioo_neg_of_pos hε hu)

/-- `g` is differentiable at each point of the right half-interval. -/
lemma differentiableAt_of_contDiffOn_two {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε)) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) ε) :
    DifferentiableAt ℝ g u := by
  exact (contDiffAt_two_of_contDiffOn_two hε hg hu).differentiableAt (by norm_num)

/-- `deriv g` is differentiable at each point of the right half-interval. -/
lemma differentiableAt_deriv_of_contDiffOn_two {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε)) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) ε) :
    DifferentiableAt ℝ (deriv g) u := by
  have h1 : ContDiffAt ℝ 1 (deriv g) u := by
    exact ContDiffAt.derivWithin (m := 1) (n := 2)
      (contDiffAt_two_of_contDiffOn_two hε hg hu) (by norm_num)
  exact h1.differentiableAt (by norm_num)

/-- Pointwise first derivative of `h := fun x => (g x)⁻¹` on the right
half-interval. -/
lemma deriv_inv_on {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε))
    (hgne : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u ≠ 0) :
    ∀ u ∈ Set.Ioo (0 : ℝ) ε,
      deriv (fun x : ℝ => (g x)⁻¹) u = -(deriv g u) / (g u) ^ 2 := by
  intro u hu
  exact deriv_inv_of_nonzero (differentiableAt_of_contDiffOn_two hε hg hu) (hgne u hu)

/-- On the right half-interval, `fun x => (g x)⁻¹` is `C²`. -/
lemma contDiffOn_two_inv {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε))
    (hgne : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u ≠ 0) :
    ContDiffOn ℝ 2 (fun x : ℝ => (g x)⁻¹) (Set.Ioo (0 : ℝ) ε) := by
  rw [IsOpen.contDiffOn_iff (s := Set.Ioo (0 : ℝ) ε) (f := fun x : ℝ => (g x)⁻¹)
    (n := 2) isOpen_Ioo]
  intro u hu
  exact ContDiffAt.inv (contDiffAt_two_of_contDiffOn_two hε hg hu) (hgne u hu)

/-- Local second-derivative computation: on the right half-interval the second
derivative of `1/g` vanishes, provided `g` satisfies the ODE
`g g'' = 2 (g')²`. -/
lemma second_deriv_inv_eq_zero {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε))
    (hgne : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u ≠ 0)
    (hode : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u * deriv (deriv g) u = 2 * (deriv g u) ^ 2) :
    ∀ u ∈ Set.Ioo (0 : ℝ) ε, deriv (deriv (fun x : ℝ => (g x)⁻¹)) u = 0 := by
  intro u hu
  have hgu2 : ContDiffAt ℝ 2 g u := contDiffAt_two_of_contDiffOn_two hε hg hu
  have hgd : DifferentiableAt ℝ g u := hgu2.differentiableAt (by norm_num)
  have hgd2 : DifferentiableAt ℝ (deriv g) u := by
    exact (ContDiffAt.derivWithin (m := 1) (n := 2) hgu2 (by norm_num)).differentiableAt
      (by norm_num)
  have hgu : g u ≠ 0 := hgne u hu
  have hgh : HasDerivAt g (deriv g u) u := hgd.hasDerivAt
  have hg2h : HasDerivAt (deriv g) (deriv (deriv g) u) u := hgd2.hasDerivAt
  have hnumA : HasDerivAt (fun x : ℝ => -(deriv g x)) (-(deriv (deriv g) u)) u := hg2h.neg
  have hm : HasDerivAt (fun x : ℝ => g x * g x)
      (deriv g u * g u + g u * deriv g u) u := hgh.mul hgh
  have hnumB : HasDerivAt (fun x : ℝ => (g x)^2) (2 * g u * (deriv g u)) u := by
    convert hm using 1
    · funext x
      rw [pow_two]
    · ring
  let N : ℝ := (-(deriv (deriv g) u) * (g u)^2 - (-(deriv g u)) * (2 * g u * (deriv g u)))
    / ((g u)^2)^2
  have hE : HasDerivAt (fun x : ℝ => -(deriv g x) / (g x)^2) N u := by
    dsimp [N]
    exact hnumA.div hnumB (pow_ne_zero 2 hgu)
  have hcomm : deriv (deriv g) u * g u = 2 * (deriv g u)^2 := by
    rw [mul_comm (deriv (deriv g) u) (g u)]
    exact hode u hu
  have hN0 : N = 0 := by
    dsimp [N]
    have hnum_zero : -(deriv (deriv g) u) * (g u)^2 - (-(deriv g u)) * (2 * g u * deriv g u) = 0 := by
      calc
        -(deriv (deriv g) u) * (g u)^2 - (-(deriv g u)) * (2 * g u * deriv g u)
            = -((deriv (deriv g) u * g u) * g u) + (2 * (deriv g u)^2) * g u := by ring
        _ = -(2 * (deriv g u)^2) * g u + (2 * (deriv g u)^2) * g u := by
              rw [hcomm]
              ring
        _ = 0 := by ring
    rw [hnum_zero]
    ring
  have hE0 : HasDerivAt (fun x : ℝ => -(deriv g x) / (g x)^2) 0 u := by
    simpa [hN0] using hE
  have hagr : (deriv (fun x : ℝ => (g x)⁻¹)) =ᶠ[𝓝 u]
      (fun x : ℝ => -(deriv g x) / (g x)^2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact deriv_inv_on hε hg hgne x hx
  have hD : HasDerivAt (deriv (fun x : ℝ => (g x)⁻¹)) 0 u := by
    exact HasDerivAt.congr_of_eventuallyEq hE0 hagr
  exact hD.deriv

/-- The two-step affine-lemma: if `f` is differentiable on the open
preconnected set `s` and its second derivative vanishes there, then `f` is
affine on `s`. -/
lemma eq_affine_of_second_deriv_eq_zero {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hconn : IsPreconnected s)
    (hf1 : DifferentiableOn ℝ f s)
    (hf2 : DifferentiableOn ℝ (deriv f) s)
    (hderiv2 : ∀ u ∈ s, deriv (deriv f) u = 0) :
    ∃ a b : ℝ, ∀ u ∈ s, f u = a * u + b := by
  rcases hs.exists_is_const_of_deriv_eq_zero hconn hf2 (fun u hu => hderiv2 u hu)
    with ⟨a, ha⟩
  let K : ℝ → ℝ := fun u => f u - a * u
  have hK1 : DifferentiableOn ℝ K s := by
    intro u hu
    have hdu : DifferentiableAt ℝ f u := hf1.differentiableAt (hs.mem_nhds hu)
    have haff : DifferentiableAt ℝ (fun v : ℝ => a * v) u := by
      simpa using (DifferentiableAt.const_mul (a := (id : ℝ → ℝ)) (b := a) differentiableAt_id)
    exact (hdu.sub haff).differentiableWithinAt
  have hderivK : ∀ u ∈ s, deriv K u = 0 := by
    intro u hu
    have hdu : DifferentiableAt ℝ f u := hf1.differentiableAt (hs.mem_nhds hu)
    have haff : DifferentiableAt ℝ (fun v : ℝ => a * v) u := by
      simpa using (DifferentiableAt.const_mul (a := (id : ℝ → ℝ)) (b := a) differentiableAt_id)
    dsimp [K]
    change deriv (f - (fun v : ℝ => a * v)) u = 0
    rw [deriv_sub hdu haff]
    rw [ha u hu]
    have haffd : deriv (fun v : ℝ => a * v) u = a := by
      have hidv : HasDerivAt (fun v : ℝ => a * v) (a * 1) u :=
        HasDerivAt.const_mul a (hasDerivAt_id u)
      rw [hidv.deriv]
      ring
    rw [haffd]
    ring
  rcases hs.exists_is_const_of_deriv_eq_zero hconn hK1 (fun u hu => hderivK u hu)
    with ⟨b, hb⟩
  refine ⟨a, b, ?_⟩
  intro u hu
  have hbK : K u = b := hb u hu
  dsimp [K] at hbK
  linarith

/-- A strictly positive real sequence `ε / (n + 2)` in the interval `(0, ε)`. -/
lemma seq_mem_Ioo {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ε / ((n : ℝ) + 2) ∈ Set.Ioo (0 : ℝ) ε := by
  constructor
  · positivity
  · have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ hd]
    have hgt : (1 : ℝ) < (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith
    simpa only [mul_one] using (mul_lt_mul_of_pos_left hgt hε)

/-- The sequence `ε / (n + 2)` tends to `0` as `n → ∞`. -/
lemma tendsto_seq {ε : ℝ} : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have hw : Tendsto (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsub : Tendsto (fun n : ℕ => (1 : ℝ) / ((↑(n + 1) : ℝ) + 1)) atTop (𝓝 0) := by
    exact hw.comp (tendsto_add_atTop_nat 1)
  have hw2 : Tendsto (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 2))) atTop (𝓝 0) := by
    convert hsub using 1
    · funext n
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
      ring
  have hc : Tendsto (fun n : ℕ => ε * ((1 : ℝ) / (((n : ℝ) + 2)))) atTop (𝓝 (ε * 0)) :=
    (tendsto_const_nhds (x := ε)).mul hw2
  have hc0 : Tendsto (fun n : ℕ => ε * ((1 : ℝ) / (((n : ℝ) + 2)))) atTop (𝓝 0) := by
    simpa using hc
  have hdiv : ∀ n : ℕ, ε / ((n : ℝ) + 2) = ε * ((1 : ℝ) / ((n : ℝ) + 2)) := by
    intro n
    rw [div_eq_mul_one_div]
  simpa [hdiv] using hc0

/-- The main one-variable contradiction: `g·g'' = 2·(g')²` on `(0,ε)` with
`g 0 = 0` and `g ≠ 0` on `(0,ε)` cannot hold for a `C²` function. -/
theorem ode_contradiction_one_sided {g : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo (-ε) ε))
    (hg0 : g 0 = 0)
    (hgne : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u ≠ 0)
    (hode : ∀ u ∈ Set.Ioo (0 : ℝ) ε, g u * deriv (deriv g) u = 2 * (deriv g u) ^ 2) :
    False := by
  let h : ℝ → ℝ := fun x : ℝ => (g x)⁻¹
  let s : Set ℝ := Set.Ioo (0 : ℝ) ε
  have hs_open : IsOpen s := isOpen_Ioo
  have hs_conn : IsPreconnected s := isPreconnected_Ioo
  -- h is C² on s, pointwise.
  have hhAt : ∀ u ∈ s, ContDiffAt ℝ 2 h u := by
    intro u hu
    have hgAtu : ContDiffAt ℝ 2 g u := by
      exact (((IsOpen.contDiffOn_iff (s := Set.Ioo (-ε) ε) (f := g) (n := 2) isOpen_Ioo).1 hg)
        (a := u)) (mem_Ioo_neg_of_pos hε (by simpa [s] using hu))
    exact ContDiffAt.inv (𝕜' := ℝ) hgAtu (hgne u (by simpa [s] using hu))
  -- h is differentiable on s, and so is deriv h.
  have hf1 : DifferentiableOn ℝ h s := by
    intro u hu
    exact ((hhAt u hu).differentiableAt (by norm_num)).differentiableWithinAt
  have hf2 : DifferentiableOn ℝ (deriv h) s := by
    intro u hu
    have h1c : ContDiffAt ℝ 1 (deriv h) u := by
      exact ContDiffAt.derivWithin (m := 1) (n := 2) (hhAt u hu) (by norm_num)
    exact (h1c.differentiableAt (by norm_num)).differentiableWithinAt
  -- second derivative of h vanishes pointwise on s.
  have hderiv2 : ∀ u ∈ s, deriv (deriv h) u = 0 := by
    intro u hu
    simpa [h] using second_deriv_inv_eq_zero hε hg hgne hode u (by simpa [s] using hu)
  -- h is affine on s.
  rcases eq_affine_of_second_deriv_eq_zero (f := h) (s := s) hs_open hs_conn hf1 hf2 hderiv2
    with ⟨c₁, c₀, haff⟩
  -- the product identity g u * (c₁ u + c₀) = 1 on s.
  have hid : ∀ u ∈ s, g u * (c₁ * u + c₀) = 1 := by
    intro u hu
    have hgu : g u ≠ 0 := hgne u (by simpa [s] using hu)
    have hmu : h u = c₁ * u + c₀ := haff u hu
    calc
      g u * (c₁ * u + c₀) = g u * h u := by rw [hmu]
      _ = 1 := by
        dsimp [h]
        exact mul_inv_cancel₀ hgu
  -- g is continuous at 0.
  have hgAt0 : ContDiffAt ℝ 2 g 0 := by
    exact (((IsOpen.contDiffOn_iff (s := Set.Ioo (-ε) ε) (f := g) (n := 2) isOpen_Ioo).1 hg)
      (a := 0)) (by constructor <;> linarith)
  have hgc : ContinuousAt g 0 := hgAt0.continuousAt
  -- sequence uₙ := ε / (n + 2).
  let u : ℕ → ℝ := fun n : ℕ => ε / ((n : ℝ) + 2)
  have hmemu : ∀ n : ℕ, u n ∈ s := by
    intro n
    simpa [u, s] using seq_mem_Ioo hε n
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    simpa [u] using tendsto_seq (ε := ε)
  have hgu0 : Tendsto (fun n : ℕ => g (u n)) atTop (𝓝 0) := by
    change Tendsto (g ∘ u) atTop (𝓝 0)
    simpa [hg0] using hgc.tendsto.comp hu_tendsto
  have hlin : Tendsto (fun n : ℕ => c₁ * u n + c₀) atTop (𝓝 (c₁ * 0 + c₀)) := by
    have hcu : Tendsto (fun n : ℕ => c₁ * u n) atTop (𝓝 (c₁ * 0)) :=
      (tendsto_const_nhds.mul hu_tendsto)
    exact hcu.add tendsto_const_nhds
  have hprod0 : Tendsto (fun n : ℕ => g (u n) * (c₁ * u n + c₀)) atTop
      (𝓝 (0 * (c₁ * 0 + c₀))) := hgu0.mul hlin
  have hprod1 : Tendsto (fun n : ℕ => g (u n) * (c₁ * u n + c₀)) atTop (𝓝 1) := by
    exact (tendsto_const_nhds (x := (1 : ℝ))).congr'
      (Eventually.of_forall (fun n => (hid (u n) (hmemu n)).symm))
  have hzero : (0 : ℝ) = 1 := by
    simpa using (tendsto_nhds_unique hprod0 hprod1)
  exact zero_ne_one hzero

end Commons.Analysis.Calculus.Deriv