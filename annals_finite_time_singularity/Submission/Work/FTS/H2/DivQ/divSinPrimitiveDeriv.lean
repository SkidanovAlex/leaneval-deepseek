import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.H2.DivQ

/-- A function which is `C^N` at `x` has an `n`-th iterated derivative (for `n < N`) whose
derivative is the `(n+1)`-st iterated derivative. -/
lemma hasDerivAt_iteratedDeriv_of_contDiffAt {f : ℝ → ℝ} {x : ℝ} {n : ℕ} {N : WithTop ℕ∞}
    (h : ContDiffAt ℝ N f x) (hn : (n : WithTop ℕ∞) < N) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv n f) x := by
    have h' := h.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := n) hn
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv n f) (deriv (iteratedDeriv n f) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

/-- The inductive core of `divSinPrimitiveDeriv`, stated for an abstract function `H` that agrees
with `f / ·` on `(0,x₁)` and is smooth there. -/
lemma divSinPrimitiveDeriv_aux (x₁ : ℝ) (f H : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hHs : ContDiffOn ℝ (⊤ : ℕ∞) H (Set.Ioo 0 x₁))
    (hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y) :
    ∀ j : ℕ,
      (∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j H t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ y ∈ Set.Ioo 0 x₁,
        y ^ (j + 2) * iteratedDeriv (j + 1) H y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j H y)) := by
  have hfI : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 x₁) := hf.mono Set.Ioo_subset_Ioc_self
  have hfAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ (⊤ : ℕ∞) f x :=
    fun x hx => hfI.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hHAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ (⊤ : ℕ∞) H x :=
    fun x hx => hHs.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hlt : ∀ n : ℕ, (n : WithTop ℕ∞) < (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)
  have hdf : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x :=
    fun n x hx => hasDerivAt_iteratedDeriv_of_contDiffAt (hfAt x hx) (hlt n)
  have hdH : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n H) (iteratedDeriv (n + 1) H x) x :=
    fun n x hx => hasDerivAt_iteratedDeriv_of_contDiffAt (hHAt x hx) (hlt n)
  intro j
  induction j with
  | zero =>
    have hbase : ∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t * H t) (iteratedDeriv 1 f x) x := by
      intro x hx
      have hfe : HasDerivAt f (iteratedDeriv 1 f x) x := by simpa using hdf 0 x hx
      have hcongr : (fun t : ℝ => t * H t) =ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        rw [hHv t ht]
        exact mul_div_cancel₀ (f t) (ne_of_gt ht.1)
      exact (hcongr.hasDerivAt_iff).mpr hfe
    constructor
    · intro x hx; simpa using hbase x hx
    · intro y hy
      have hA0 := hbase y hy
      have hHd : HasDerivAt H (iteratedDeriv 1 H y) y := by simpa using hdH 0 y hy
      have hmul : HasDerivAt (fun t : ℝ => t * H t) (1 * H y + y * iteratedDeriv 1 H y) y := by
        have := (hasDerivAt_id y).mul hHd
        exact this
      have heq : 1 * H y + y * iteratedDeriv 1 H y = iteratedDeriv 1 f y := hmul.unique hA0
      have hgoal : y ^ 2 * iteratedDeriv 1 H y = y * iteratedDeriv 1 f y - 1 * (y * H y) := by
        linear_combination (y : ℝ) * heq
      simpa using hgoal
  | succ j ih =>
    obtain ⟨hAj, hBj⟩ := ih
    have hA1 : ∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          (x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
      intro x hx
      have hp : HasDerivAt (fun t : ℝ => t ^ (j + 1)) (((j : ℝ) + 1) * x ^ j) x := by
        have h := hasDerivAt_pow (j + 1) x
        rw [show (j + 1) - 1 = j from by omega] at h
        push_cast at h
        exact h
      have hd : HasDerivAt (iteratedDeriv (j + 1) f) (iteratedDeriv ((j + 1) + 1) f x) x :=
        hdf (j + 1) x hx
      have h1 : HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
          (((j : ℝ) + 1) * x ^ j * iteratedDeriv (j + 1) f x
            + x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
        exact hp.mul hd
      have hVj : HasDerivAt (fun t : ℝ => ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t))
          (((j : ℝ) + 1) * (x ^ j * iteratedDeriv (j + 1) f x)) x :=
        (hAj x hx).const_mul ((j : ℝ) + 1)
      have hW : HasDerivAt
          (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t
            - ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t))
          (x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
        have hsub := h1.sub hVj
        convert hsub using 1
        ring
      have hev : (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          =ᶠ[𝓝 x]
          (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t
            - ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        simpa using hBj t ht
      exact hW.congr_of_eventuallyEq hev
    constructor
    · intro x hx; exact hA1 x hx
    · intro y hy
      have hAj1 := hA1 y hy
      have hDH1 : HasDerivAt (iteratedDeriv (j + 1) H) (iteratedDeriv ((j + 1) + 1) H y) y :=
        hdH (j + 1) y hy
      have hp1 : HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1)) (((j : ℝ) + 2) * y ^ (j + 1)) y := by
        have h := hasDerivAt_pow ((j + 1) + 1) y
        rw [show ((j + 1) + 1) - 1 = j + 1 from by omega] at h
        push_cast at h
        convert h using 1
        ring
      have hmul : HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          (((j : ℝ) + 2) * y ^ (j + 1) * iteratedDeriv (j + 1) H y
            + y ^ ((j + 1) + 1) * iteratedDeriv ((j + 1) + 1) H y) y := by
        exact hp1.mul hDH1
      have heq := hmul.unique hAj1
      push_cast
      linear_combination (y : ℝ) * heq

/-- Local calculus for the division `H = f / ·` on `(0,x₁]`: for `f` of class `C^∞` on `(0,x₁]` and
`H y = f y / y`, the function `V_j x = x^{j+1}·H^{(j)}(x)` has derivative `x^j·f^{(j+1)}(x)` on the
*open* interval `(0,x₁)`, together with the recursion that turns `H`-derivatives into `f`-derivatives:
`V_{j+1}(y) = y^{j+1} f^{(j+1)}(y) − (j+1) V_j(y)`.

Both are purely local identities on `(0,x₁)`.  Route: induction on `j`.  Base: `V_0 y = y·(f y / y) = f y`
near `y ≠ 0`, so `HasDerivAt (V 0) (deriv f x) x` by congruence, and `deriv f = iteratedDeriv 1 f`.  Step:
by `iteratedDeriv_succ`, `H^{(j+1)} = deriv (H^{(j)})`, and `H^{(j)}(u) = V_j(u)/u^{j+1}` for `u ≠ 0`; the
quotient rule plus the induction hypothesis gives the recursion, and then the product rule plus
`iteratedDeriv_succ` again gives `HasDerivAt (V_{j+1}) (x^{j+1} f^{(j+2)} x) x`. -/
theorem divSinPrimitiveDeriv (x₁ : ℝ) (hx₁ : 0 < x₁) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      (∀ (j : ℕ) (x : ℝ), x ∈ Set.Ioo 0 x₁ →
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ (j : ℕ) (y : ℝ), y ∈ Set.Ioo 0 x₁ →
        y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) y)) := by
  intro f hf
  set H : ℝ → ℝ := fun y : ℝ => f y / y with hHdef
  have hfm : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 x₁) := hf.mono Set.Ioo_subset_Ioc_self
  have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H (Set.Ioo 0 x₁) := by
    rw [hHdef]
    have hid : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) := contDiffOn_id
    have hdiv := hfm.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rw [hfun] at hdiv
    exact hdiv
  have hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y := by
    intro y hy; rw [hHdef]
  have hmain := divSinPrimitiveDeriv_aux x₁ f H hf hHs hHv
  constructor
  · intro j x hx; exact (hmain j).1 x hx
  · intro j y hy; exact (hmain j).2 y hy

end Work.FTS.H2.DivQ
