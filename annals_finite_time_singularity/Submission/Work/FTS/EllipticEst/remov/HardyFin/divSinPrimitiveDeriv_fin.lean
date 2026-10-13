import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.HardyFin.Basic
import Submission.Work.FTS.H2.DivQ.divSinPrimitiveDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.HardyFin

open scoped Topology

/-- The inductive core of `divSinPrimitiveDeriv_fin`, stated for an abstract function `H` that
agrees with `f / ·` on `(0,x₁)` and is `C^{N+2}` there.  Finite-order version of
`Work.FTS.H2.DivQ.divSinPrimitiveDeriv_aux`. -/
lemma divSinPrimitiveDeriv_aux_fin (x₁ : ℝ) (f H : ℝ → ℝ) (N : ℕ)
    (hf : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hHs : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H (Set.Ioo 0 x₁))
    (hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y) :
    ∀ j : ℕ, j ≤ N →
      (∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j H t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ y ∈ Set.Ioo 0 x₁,
        y ^ (j + 2) * iteratedDeriv (j + 1) H y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j H y)) := by
  have hfI : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
    hf.mono Set.Ioo_subset_Ioc_self
  have hfAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f x :=
    fun x hx => hfI.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hHAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H x :=
    fun x hx => hHs.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hlt : ∀ n : ℕ, n ≤ N → (n : WithTop ℕ∞) < ((N + 2 : ℕ) : WithTop ℕ∞) :=
    fun n hn => by exact_mod_cast (by omega : n < N + 2)
  have hdf : ∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x :=
    fun n x hn hx =>
      Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt (hfAt x hx) (hlt n hn)
  have hdH : ∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n H) (iteratedDeriv (n + 1) H x) x :=
    fun n x hn hx =>
      Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt (hHAt x hx) (hlt n hn)
  intro j
  induction j with
  | zero =>
    intro _
    have hbase : ∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t * H t) (iteratedDeriv 1 f x) x := by
      intro x hx
      have hfe : HasDerivAt f (iteratedDeriv 1 f x) x := by
        simpa using hdf 0 x (Nat.zero_le N) hx
      have hcongr : (fun t : ℝ => t * H t) =ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        rw [hHv t ht]
        exact mul_div_cancel₀ (f t) (ne_of_gt ht.1)
      exact (hcongr.hasDerivAt_iff).mpr hfe
    constructor
    · intro x hx; simpa using hbase x hx
    · intro y hy
      have hA0 := hbase y hy
      have hHd : HasDerivAt H (iteratedDeriv 1 H y) y := by
        simpa using hdH 0 y (Nat.zero_le N) hy
      have hmul : HasDerivAt (fun t : ℝ => t * H t) (1 * H y + y * iteratedDeriv 1 H y) y := by
        have := (hasDerivAt_id y).mul hHd
        exact this
      have heq : 1 * H y + y * iteratedDeriv 1 H y = iteratedDeriv 1 f y := hmul.unique hA0
      have hgoal : y ^ 2 * iteratedDeriv 1 H y = y * iteratedDeriv 1 f y - 1 * (y * H y) := by
        linear_combination (y : ℝ) * heq
      simpa using hgoal
  | succ j ih =>
    intro hj
    obtain ⟨hAj, hBj⟩ := ih (by omega)
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
        hdf (j + 1) x hj hx
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
        hdH (j + 1) y hj hy
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

/-- Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitiveDeriv`
(`Submission/Work/FTS/H2/DivQ/divSinPrimitiveDeriv.lean`), where the `C^∞` hypothesis
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` is replaced by `ContDiffOn ℝ ((N+2 : ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
for a *finite* order `N + 2`, and the two conclusions are asserted only for levels `j ≤ N`.

Adaptation instructions: copy `divSinPrimitiveDeriv_aux` and `divSinPrimitiveDeriv` from the
original file `Submission/Work/FTS/H2/DivQ/divSinPrimitiveDeriv.lean` (import it: it contains the
helper `Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt`, which is already stated for an
arbitrary order `N : WithTop ℕ∞` and is to be reused unchanged). Replace
`hfAt x hx : ContDiffAt ℝ (⊤ : ℕ∞) f x` by
`ContDiffAt ℝ (((N+2 : ℕ)) : WithTop ℕ∞) f x` (obtained from
`(hf.mono Set.Ioo_subset_Ioc_self).contDiffAt (isOpen_Ioo.mem_nhds hx)`) and the analogous `hHAt`
for `H = fun y => f y / y` (which is `C^{N+2}` on `Ioo 0 x₁` as a quotient of two such functions,
`ContDiffOn.div` with `contDiffOn_id`), and replace the proof
`hlt n : (n : WithTop ℕ∞) < (↑(⊤ : ℕ∞) : WithTop ℕ∞)` by
`hlt n (hn : n ≤ N) : (n : WithTop ℕ∞) < ((N+2 : ℕ) : WithTop ℕ∞)` proved by
`exact_mod_cast (by omega : n < N + 2)`. The induction on `j` becomes an induction with the extra
hypothesis `j ≤ N`, `ih : j ≤ N → P j`, and every use of `hdf`/`hdH` at level `n` must be
accompanied by `n ≤ N`. Formally, `P j` is the conjunction of

* `∀ x ∈ Set.Ioo 0 x₁, HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t) (x ^ j * iteratedDeriv (j + 1) f x) x`
* `∀ y ∈ Set.Ioo 0 x₁, y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y - (j + 1) * (y ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) y)`

and the step from `j` to `j+1` uses `hdf (j+1)` (needing `j + 1 ≤ N`) and `hdH (j+1)`
(needing `j + 1 ≤ N`). -/
theorem divSinPrimitiveDeriv_fin (x₁ : ℝ) (hx₁ : 0 < x₁) (N : ℕ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
      (∀ (j : ℕ) (x : ℝ), j ≤ N → x ∈ Set.Ioo 0 x₁ →
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ (j : ℕ) (y : ℝ), j ≤ N → y ∈ Set.Ioo 0 x₁ →
        y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) y)) := by
  intro f hf
  set H : ℝ → ℝ := fun y : ℝ => f y / y with hHdef
  have hfm : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
    hf.mono Set.Ioo_subset_Ioc_self
  have hHs : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H (Set.Ioo 0 x₁) := by
    rw [hHdef]
    have hid : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := hfm.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rw [hfun] at hdiv
    exact hdiv
  have hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y := by
    intro y hy; rw [hHdef]
  have hmain := divSinPrimitiveDeriv_aux_fin x₁ f H N hf hHs hHv
  constructor
  · intro j x hj hx; exact (hmain j hj).1 x hx
  · intro j y hj hy; exact (hmain j hj).2 y hy

end Work.FTS.EllipticEst.remov.HardyFin
