import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint
import Submission.Work.FTS.EllipticEst.remov.Baux.deriv_tan_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The recursion of `D_θ^k` applied to the operator `L`

The target `Work.FTS.EllipticEst.remov.Baux.DthIter_M_recursion` records that the angular
operator `D_θ = sin(2θ) ∂_θ` acts on the multiplier

`M Ψ = ∂_θ (tan θ · Ψ) - 6 Ψ - α(5+α) D_z Ψ`

through the twisted binomial expansion `D_θ^k (tan²θ · X) = tan²θ · (D_θ + 4)^k X + D_θ^k X`.

Everything is reduced to the one-dimensional operator `Work.Spaces.Lop u θ = sin(2θ) u'(θ)`
(the action of `D_θ` on `θ`-slices) and the *pointwise* finite-order calculus for it:
`LopLeibnizPoint` (the Leibniz rule at a point), the additivity `Lop_iter_add_at`, the
congruence `Lop_iter_congr_at` and the eigenvalue identity `Lop^k (tan²) = 4^k tan²`.
-/

namespace Work.FTS.EllipticEst.remov.Baux

open scoped Real Topology
open Filter Set

/-- `((N : ℕ) : ℕ∞ω)` for the finite order `N`. -/
abbrev DmrOrd (N : ℕ) : WithTop ℕ∞ := ((N : ℕ) : WithTop ℕ∞)

namespace Dmr

/-! ## Elementary facts about the angular operator `Lop` -/

/-- The `θ`-slice of a jointly `C^n` function is `C^n` at the corresponding point. -/
theorem contDiffAt_slice_snd_fin (N : ℕ) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ (DmrOrd N) (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ (DmrOrd N) (fun θ' => f z θ') θ := by
  have hlin : ContDiffAt ℝ (DmrOrd N) (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  have hcomp := h.comp θ hlin
  simpa [Function.comp_def, Function.uncurry] using hcomp

/-- Iterates of `Lop` commute with multiplication by a constant. -/
theorem Lop_iter_const_mul (c : ℝ) (u : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.Lop^[i] (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop^[i] u θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [deriv_const_mul_field (u := c) (v := Work.Spaces.Lop^[n] u) (x := θ)]
      ring

/-- `Lop`-iterates respect eventual equality: they only see the germ of the function. -/
theorem Lop_iter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (i : ℕ) :
    Work.Spaces.Lop^[i] u =ᶠ[𝓝 θ] Work.Spaces.Lop^[i] v := by
  induction i with
  | zero => simpa using h
  | succ n ih =>
      change ∀ᶠ x in 𝓝 θ, Work.Spaces.Lop^[n] u x = Work.Spaces.Lop^[n] v x at ih
      rw [Filter.eventually_iff_exists_mem] at ih
      obtain ⟨s, hs, hsEq⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ∀ᶠ x in 𝓝 θ, Real.sin (2 * x) * deriv (Work.Spaces.Lop^[n] u) x
          = Real.sin (2 * x) * deriv (Work.Spaces.Lop^[n] v) x
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨interior s, interior_mem_nhds.mpr hs, fun x hx => ?_⟩
      have hg : Work.Spaces.Lop^[n] u =ᶠ[𝓝 x] Work.Spaces.Lop^[n] v :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨interior s, isOpen_interior.mem_nhds hx, fun y hy => hsEq y (interior_subset hy)⟩
      congr 1
      exact Filter.EventuallyEq.deriv_eq hg

/-- `Lop`-iterates respect eventual equality, pointwise form. -/
theorem Lop_iter_congr_at {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (i : ℕ) :
    Work.Spaces.Lop^[i] u θ = Work.Spaces.Lop^[i] v θ :=
  (Lop_iter_eventuallyEq h i).eq_of_nhds

/-- `Lop^[i]` is additive at a point where both summands are `C^i`. -/
theorem Lop_iter_add_at (i : ℕ) :
    ∀ {u v : ℝ → ℝ} {θ : ℝ}, ContDiffAt ℝ (DmrOrd i) u θ →
      ContDiffAt ℝ (DmrOrd i) v θ →
      Work.Spaces.Lop^[i] (u + v) θ = Work.Spaces.Lop^[i] u θ + Work.Spaces.Lop^[i] v θ := by
  induction i with
  | zero => intro u v θ hu hv; rfl
  | succ n ih =>
      intro u v θ hu hv
      have hle : DmrOrd n ≤ DmrOrd (n + 1) := by
        simp only [DmrOrd]; exact_mod_cast Nat.le_succ n
      obtain ⟨s, hs, hscd⟩ := hu.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (ne_of_lt (Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopOrd_lt_omega (n + 1))))
      obtain ⟨t, ht, htcd⟩ := hv.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (ne_of_lt (Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopOrd_lt_omega (n + 1))))
      obtain ⟨W, hWst, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
      have hev : Work.Spaces.Lop^[n] (u + v)
          =ᶠ[𝓝 θ] (Work.Spaces.Lop^[n] u + Work.Spaces.Lop^[n] v) := by
        change ∀ᶠ x in 𝓝 θ, Work.Spaces.Lop^[n] (u + v) x
          = (Work.Spaces.Lop^[n] u + Work.Spaces.Lop^[n] v) x
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨W, hWopen.mem_nhds hθW, fun x hx => ?_⟩
        have h1 : ContDiffAt ℝ (DmrOrd (n + 1)) u x :=
          (hscd.mono (fun y hy => (hWst hy).1)).contDiffAt (hWopen.mem_nhds hx)
        have h2 : ContDiffAt ℝ (DmrOrd (n + 1)) v x :=
          (htcd.mono (fun y hy => (hWst hy).2)).contDiffAt (hWopen.mem_nhds hx)
        exact ih (h1.of_le hle) (h2.of_le hle)
      have hdu : DifferentiableAt ℝ (Work.Spaces.Lop^[n] u) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hu).differentiableAt (by simp [DmrOrd])
      have hdv : DifferentiableAt ℝ (Work.Spaces.Lop^[n] v) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hv).differentiableAt (by simp [DmrOrd])
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] (u + v)) θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] u) θ
            + Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] v) θ
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_add hdu hdv]
      ring

/-- `Lop^i (tan²)` is the eigenfunction `4^i tan²` of the twisted operator. -/
theorem Lop_iter_tan_sq : ∀ (i : ℕ) {θ : ℝ}, θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Work.Spaces.Lop^[i] (fun θ' => Real.tan θ' ^ 2) θ = 4 ^ i * Real.tan θ ^ 2 := by
  intro i
  induction i with
  | zero => intro θ _; simp
  | succ i ih =>
      intro θ hθ
      have hcosp : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hcos : Real.cos θ ≠ 0 := ne_of_gt hcosp
      have hev : (fun θ' => Work.Spaces.Lop^[i] (fun θ'' => Real.tan θ'' ^ 2) θ')
          =ᶠ[𝓝 θ] (fun θ' => 4 ^ i * Real.tan θ' ^ 2) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih hθ'
      rw [Function.iterate_succ_apply']
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.Lop^[i] (fun θ'' => Real.tan θ'' ^ 2) θ') θ
        = 4 ^ (i + 1) * Real.tan θ ^ 2
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => Real.tan θ' ^ 2) θ :=
        ((Real.hasDerivAt_tan hcos).pow 2).differentiableAt
      rw [deriv_const_mul (4 ^ i) hdiff]
      have hd : deriv (fun θ' : ℝ => Real.tan θ' ^ 2) θ
          = 2 * Real.tan θ ^ (2 - 1) * (1 / Real.cos θ ^ 2) :=
        ((Real.hasDerivAt_tan hcos).pow 2).deriv
      rw [hd]
      have h1 : Real.tan θ ^ (2 - 1) = Real.tan θ := by norm_num
      have hnum : Real.sin (2 * θ) * (2 * Real.tan θ * (1 / Real.cos θ ^ 2))
          = 4 * Real.tan θ ^ 2 := by
        rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
        field_simp
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [h1, show (4 : ℝ) ^ (i + 1) = 4 ^ i * 4 from pow_succ 4 i]
      calc Real.sin (2 * θ) * (4 ^ i * (2 * Real.tan θ * (1 / Real.cos θ ^ 2)))
          = 4 ^ i * (Real.sin (2 * θ) * (2 * Real.tan θ * (1 / Real.cos θ ^ 2))) := by ring
        _ = 4 ^ i * (4 * Real.tan θ ^ 2) := by rw [hnum]
        _ = 4 ^ i * 4 * Real.tan θ ^ 2 := by ring

/-! ## A finite-sum reindexing

`∑_{a ≤ k} C(k,a) 4^a X(k-a) = ∑_{j ≤ k} C(k,j) 4^{k-j} X j`: the reflection of the index
range `range (k+1)`, using `Nat.choose_symm`. -/

theorem sum_range_choose_reflect (k : ℕ) (X : ℕ → ℝ) :
    (∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * (4 ^ a * X (k - a)))
      = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * 4 ^ (k - j)) * X j := by
  rw [← Finset.sum_range_reflect (fun j => ((k.choose j : ℝ) * 4 ^ (k - j)) * X j) (k + 1)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self ha', ← Nat.choose_symm ha']
  ring

/-- `DmrOrd` is monotone in the natural number. -/
theorem DmrOrd_le {a b : ℕ} (h : a ≤ b) : DmrOrd a ≤ DmrOrd b := by
  simp only [DmrOrd]; exact_mod_cast h

/-- The order `n+1` is the successor of the order `n`. -/
theorem DmrOrd_succ (n : ℕ) : DmrOrd (n + 1) = DmrOrd n + 1 := by
  simp only [DmrOrd]; push_cast; ring

/-- A finite order is not the smooth order `∞`. -/
theorem DmrOrd_ne_infty (n : ℕ) : DmrOrd n ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ne_of_lt (Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopOrd_lt_omega n)

/-- `Lop^[i]` is subtractive at a point where both arguments are `C^i`. -/
theorem Lop_iter_sub_at (i : ℕ) :
    ∀ {u v : ℝ → ℝ} {θ : ℝ}, ContDiffAt ℝ (DmrOrd i) u θ →
      ContDiffAt ℝ (DmrOrd i) v θ →
      Work.Spaces.Lop^[i] (u - v) θ = Work.Spaces.Lop^[i] u θ - Work.Spaces.Lop^[i] v θ := by
  induction i with
  | zero => intro u v θ hu hv; rfl
  | succ n ih =>
      intro u v θ hu hv
      have hle : DmrOrd n ≤ DmrOrd (n + 1) := DmrOrd_le (Nat.le_succ n)
      obtain ⟨s, hs, hscd⟩ := hu.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (DmrOrd_ne_infty (n + 1)))
      obtain ⟨t, ht, htcd⟩ := hv.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (DmrOrd_ne_infty (n + 1)))
      obtain ⟨W, hWst, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
      have hev : Work.Spaces.Lop^[n] (u - v)
          =ᶠ[𝓝 θ] (Work.Spaces.Lop^[n] u - Work.Spaces.Lop^[n] v) := by
        change ∀ᶠ x in 𝓝 θ, Work.Spaces.Lop^[n] (u - v) x
          = (Work.Spaces.Lop^[n] u - Work.Spaces.Lop^[n] v) x
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨W, hWopen.mem_nhds hθW, fun x hx => ?_⟩
        have h1 : ContDiffAt ℝ (DmrOrd (n + 1)) u x :=
          (hscd.mono (fun y hy => (hWst hy).1)).contDiffAt (hWopen.mem_nhds hx)
        have h2 : ContDiffAt ℝ (DmrOrd (n + 1)) v x :=
          (htcd.mono (fun y hy => (hWst hy).2)).contDiffAt (hWopen.mem_nhds hx)
        exact ih (h1.of_le hle) (h2.of_le hle)
      have hdu : DifferentiableAt ℝ (Work.Spaces.Lop^[n] u) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hu).differentiableAt (by simp [DmrOrd])
      have hdv : DifferentiableAt ℝ (Work.Spaces.Lop^[n] v) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hv).differentiableAt (by simp [DmrOrd])
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] (u - v)) θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] u) θ
            - Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] v) θ
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_sub hdu hdv]
      ring

/-- The `tan²`-evaluation and reindexing of the Leibniz sum. -/
theorem tan_sq_Lop_sum (k : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (Y : ℕ → ℝ) :
    (∑ a ∈ Finset.range (k + 1),
        (k.choose a : ℝ) * (Work.Spaces.Lop^[a] (fun θ' => Real.tan θ' ^ 2) θ * Y (k - a)))
      = Real.tan θ ^ 2 * (∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℝ) * 4 ^ (k - j)) * Y j) := by
  have h1 : ∀ a ∈ Finset.range (k + 1),
      (k.choose a : ℝ) * (Work.Spaces.Lop^[a] (fun θ' => Real.tan θ' ^ 2) θ * Y (k - a))
        = Real.tan θ ^ 2 * ((k.choose a : ℝ) * (4 ^ a * Y (k - a))) := by
    intro a _
    rw [Lop_iter_tan_sq a hθ]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_range_choose_reflect k Y]

/-- Multiplication by a constant preserves pointwise `C^n`. -/
theorem const_mul_contDiffAt (c : ℝ) {f : ℝ → ℝ} {θ : ℝ} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f θ) : ContDiffAt ℝ n (fun θ' => c * f θ') θ :=
  (by fun_prop : ContDiffAt ℝ n (fun _ : ℝ => c) θ).mul hf

/-- The `θ`-slice of `D_z Ψ` is `C^N` at `θ`. -/
theorem contDiffAt_Dz_slice_fin (N : ℕ) {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ n : ℕ, ContDiffAt ℝ (DmrOrd n) (Function.uncurry Ψ) (z, θ)) :
    ContDiffAt ℝ (DmrOrd N) (fun θ' => Work.Spaces.Dz Ψ z θ') θ := by
  obtain ⟨s, hs, hscd⟩ := (h (N + 1)).contDiffOn (le_rfl : DmrOrd (N + 1) ≤ DmrOrd (N + 1))
    (fun h => absurd h (DmrOrd_ne_infty (N + 1)))
  obtain ⟨W, hWs, hWopen, hθW⟩ := mem_nhds_iff.mp hs
  have hfd : ContDiffOn ℝ (DmrOrd N) (fderiv ℝ (Function.uncurry Ψ)) W :=
    (hscd.mono hWs).fderiv_of_isOpen hWopen (le_of_eq (DmrOrd_succ N).symm)
  set V : Set ℝ := {θ' : ℝ | (z, θ') ∈ W} with hVdef
  have hVopen : IsOpen V := hWopen.preimage (by continuity : Continuous fun θ' : ℝ => (z, θ'))
  have hslice : ContDiffAt ℝ (DmrOrd N)
      (fun θ' => z * (fderiv ℝ (Function.uncurry Ψ) (z, θ')) (1, 0)) θ := by
    have h1 : ContDiffAt ℝ (DmrOrd N) (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p)
        (z, θ) := hfd.contDiffAt (hWopen.mem_nhds hθW)
    have h2 : ContDiffAt ℝ (DmrOrd N) (fun θ' : ℝ => (z, θ')) θ := by fun_prop
    have h3 := h1.comp θ h2
    have h4 : ContDiffAt ℝ (DmrOrd N)
        (fun θ' : ℝ => (fderiv ℝ (Function.uncurry Ψ) (z, θ')) (1, 0)) θ :=
      h3.clm_apply (by fun_prop : ContDiffAt ℝ (DmrOrd N) (fun _ : ℝ => ((1 : ℝ), (0 : ℝ))) θ)
    exact const_mul_contDiffAt z h4
  refine hslice.congr_of_eventuallyEq ?_
  refine Filter.eventually_iff_exists_mem.mpr ⟨V, hVopen.mem_nhds hθW, fun θ' hθ' => ?_⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ') :=
    ((hscd.mono hWs).contDiffAt (hWopen.mem_nhds hθ')).differentiableAt (by simp [DmrOrd])
  have hd : deriv (fun z' : ℝ => Function.uncurry Ψ (z', θ')) z
      = (fderiv ℝ (Function.uncurry Ψ) (z, θ')) (1, 0) :=
    Work.Spaces.deriv_slice_fst (Function.uncurry Ψ) z θ' hdiff
  show z * deriv (fun z' : ℝ => Ψ z' θ') z
      = z * (fderiv ℝ (Function.uncurry Ψ) (z, θ')) (1, 0)
  rw [show (fun z' : ℝ => Ψ z' θ') = (fun z' : ℝ => Function.uncurry Ψ (z', θ')) from rfl, hd]

/-- The iterate form of `DthIter` on a `θ`-slice. -/
theorem DthIter_apply_eq_Lop (i : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i F z θ = Work.Spaces.Lop^[i] (fun θ' => F z θ') θ :=
  congrFun (Work.Spaces.DthIter_eq_iterate_Lop i F z) θ

/-- **The one-dimensional recursion** underlying `DthIter_M_recursion`. -/
theorem Lop_M_recursion (k : ℕ) (c : ℝ) :
    ∀ {φ η : ℝ → ℝ} {θ : ℝ}, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      ContDiffAt ℝ (DmrOrd (k + 1)) φ θ → ContDiffAt ℝ (DmrOrd k) η θ →
      Work.Spaces.Lop^[k]
          (fun θ' => deriv (fun s => Real.tan s * φ s) θ' - 6 * φ θ' - c * η θ') θ
        = Real.tan θ ^ 2
            * (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * 4 ^ (k - j))
                * Work.Spaces.Lop^[j] (fun θ' => φ θ' + (1 / 2) * Work.Spaces.Lop φ θ') θ)
          + Work.Spaces.Lop^[k] (fun θ' => φ θ' + (1 / 2) * Work.Spaces.Lop φ θ') θ
          - 6 * Work.Spaces.Lop^[k] φ θ
          - c * Work.Spaces.Lop^[k] η θ := by
  intro φ η θ hθ hφ hη
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hφk : ContDiffAt ℝ (DmrOrd k) φ θ := hφ.of_le (DmrOrd_le (Nat.le_succ k))
  have hderivφ : ContDiffAt ℝ (DmrOrd k) (deriv φ) θ :=
    hφ.derivWithin (le_of_eq (DmrOrd_succ k).symm)
  have hLopφ : ContDiffAt ℝ (DmrOrd k) (Work.Spaces.Lop φ) θ := by
    have heq : Work.Spaces.Lop φ = (fun θ' : ℝ => Real.sin (2 * θ')) * deriv φ := rfl
    rw [heq]
    exact (by fun_prop : ContDiffAt ℝ (DmrOrd k) (fun θ' : ℝ => Real.sin (2 * θ')) θ).mul hderivφ
  have hU : ContDiffAt ℝ (DmrOrd k) (fun θ' => φ θ' + (1 / 2) * Work.Spaces.Lop φ θ') θ :=
    hφk.add (const_mul_contDiffAt (1 / 2) hLopφ)
  have htan2 : ContDiffAt ℝ (DmrOrd k) (fun θ' => Real.tan θ' ^ 2) θ :=
    (Real.contDiffAt_tan.mpr hcos).pow 2
  obtain ⟨s, hs, hscd⟩ := hφ.contDiffOn (DmrOrd_le (by omega : 1 ≤ k + 1))
    (fun h => absurd h (DmrOrd_ne_infty 1))
  obtain ⟨W, hWs, hWopen, hθW⟩ := mem_nhds_iff.mp hs
  set V : Set ℝ := W ∩ Set.Ioo 0 (Real.pi / 2) with hVdef
  have hVopen : IsOpen V := hWopen.inter isOpen_Ioo
  have hVsub : V ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx => hx.2
  have hθV : θ ∈ V := ⟨hθW, hθ⟩
  have hφV : ContDiffOn ℝ 1 φ V := hscd.mono (fun x hx => hWs hx.1)
  have harg : (fun θ' => deriv (fun s => Real.tan s * φ s) θ' - 6 * φ θ' - c * η θ')
      =ᶠ[𝓝 θ]
      (fun θ' => (Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')
            + (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ'))
          - (6 * φ θ' + c * η θ')) := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨V, hVopen.mem_nhds hθV, fun x hx => ?_⟩
    show deriv (fun s => Real.tan s * φ s) x - 6 * φ x - c * η x
      = (Real.tan x ^ 2 * (φ x + (1 / 2) * Work.Spaces.Lop φ x)
          + (φ x + (1 / 2) * Work.Spaces.Lop φ x)) - (6 * φ x + c * η x)
    rw [deriv_tan_mul_eq φ hVopen hVsub hφV x hx]
    ring
  rw [Lop_iter_congr_at harg k]
  have hX : ContDiffAt ℝ (DmrOrd k)
      (fun θ' => Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')
        + (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')) θ := (htan2.mul hU).add hU
  have hY : ContDiffAt ℝ (DmrOrd k) (fun θ' => 6 * φ θ' + c * η θ') θ :=
    (const_mul_contDiffAt 6 hφk).add (const_mul_contDiffAt c hη)
  have hsplit1 : (fun θ' => (Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')
            + (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')) - (6 * φ θ' + c * η θ'))
      = ((fun θ' => Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')
              + (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ'))
          - (fun θ' => 6 * φ θ' + c * η θ')) := rfl
  rw [hsplit1, Lop_iter_sub_at k hX hY]
  have hsplit2 : (fun θ' => Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')
              + (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ'))
      = ((fun θ' => Real.tan θ' ^ 2 * (φ θ' + (1 / 2) * Work.Spaces.Lop φ θ'))
          + (fun θ' => φ θ' + (1 / 2) * Work.Spaces.Lop φ θ')) := rfl
  have hsplit3 : (fun θ' => 6 * φ θ' + c * η θ')
      = ((fun θ' => 6 * φ θ') + (fun θ' => c * η θ')) := rfl
  rw [hsplit2, Lop_iter_add_at k (htan2.mul hU) hU]
  rw [hsplit3, Lop_iter_add_at k (const_mul_contDiffAt 6 hφk) (const_mul_contDiffAt c hη)]
  have hsplit4 : (fun x => Real.tan x ^ 2 * (φ x + (1 / 2) * Work.Spaces.Lop φ x))
      = ((fun x => Real.tan x ^ 2) * (fun x => φ x + (1 / 2) * Work.Spaces.Lop φ x)) := rfl
  rw [hsplit4, Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint k htan2 hU]
  rw [Lop_iter_const_mul 6 φ k, Lop_iter_const_mul c η k]
  rw [tan_sq_Lop_sum k hθ
    (fun j => Work.Spaces.Lop^[j] (fun θ' => φ θ' + (1 / 2) * Work.Spaces.Lop φ θ') θ)]
  ring

end Dmr

theorem DthIter_M_recursion (k : ℕ) :
    ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry Ψ) (z, θ)) →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DthIter k
          (fun z θ => Work.Spaces.pth (fun z' θ' => Real.tan θ' * Ψ z' θ') z θ
            - 6 * Ψ z θ - (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) z θ
        = Real.tan θ ^ 2
            * (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * 4 ^ (k - j))
                * Work.Spaces.DthIter j
                    (fun z θ => Ψ z θ + (1 / 2) * Work.Spaces.Dth Ψ z θ) z θ)
          + Work.Spaces.DthIter k
              (fun z θ => Ψ z θ + (1 / 2) * Work.Spaces.Dth Ψ z θ) z θ
          - 6 * Work.Spaces.DthIter k Ψ z θ
          - (α * (5 + α)) * Work.Spaces.DthIter k (Work.Spaces.Dz Ψ) z θ := by
  intro α Ψ z θ h hθ
  have hφ : ContDiffAt ℝ (DmrOrd (k + 1)) (fun θ' => Ψ z θ') θ :=
    Dmr.contDiffAt_slice_snd_fin (k + 1) (h (k + 1))
  have hη : ContDiffAt ℝ (DmrOrd k) (fun θ' => Work.Spaces.Dz Ψ z θ') θ :=
    Dmr.contDiffAt_Dz_slice_fin k h
  have key := Dmr.Lop_M_recursion k (α * (5 + α)) hθ hφ hη
  simp only [Dmr.DthIter_apply_eq_Lop]
  exact key

end Work.FTS.EllipticEst.remov.Baux
