import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.DivSinRec
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DerivLikeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# The recursion for the angular quotient, with only interior smoothness

`Work.Elliptic.DivSinRec` proves the recursion

`D_θ^i (h / sin 2θ) = D_θ^{i-1} h' - ∑_{l<i} C(i-1,l) · D_θ^{i-1-l}(2 cos 2θ) · D_θ^l (h/sin 2θ)`

for a slice `h` that is *analytic on an open neighbourhood* of `[0, π/2]` and vanishes at the two
endpoints.  That is more than the identity needs: it is a purely local consequence of the
first-order identity `D_θ (h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on the open interval
`(0, π/2)` together with the Leibniz rule for the derivation `D_θ = sin(2θ) ∂_θ`.

The Leibniz rule for iterates of a derivation is supplied by the abstract machinery
`Work.Spaces.DerivLike` / `Work.Spaces.FunClass`, but the instances shipped with it
(`Work.Spaces.Lop_iter_mul_eqOn`, `Work.Spaces.DthIter_mul`) ask for `ContDiffOn ℝ ⊤`, i.e.
*analyticity*.  Here we instantiate the same machinery with the honest `C^∞`-on-an-open-set class
(`SmoothOn`, phrased with the finite orders `n : ℕ`), which is what the hypothesis
`ContDiffOn ℝ (↑(⊤ : ℕ∞))` provides, and redo the short argument of `DivSinRec`.
-/

/-- The class of functions that are `C^∞` on the open set `U`, expressed with the finite orders
`n : ℕ` so that it can be consumed by `Work.Spaces.FunClass` / `Work.Spaces.DerivLike`. -/
private def SmoothOn (U : Set ℝ) : (ℝ → ℝ) → Prop :=
  fun u => ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) u U

/-- `SmoothOn U` is closed under `+`, `*` and scalar multiplication. -/
private lemma smoothOn_funClass (U : Set ℝ) : Work.Spaces.FunClass (SmoothOn U) where
  add := fun A B hA hB n => (hA n).add (hB n)
  mul := fun A B hA hB n => (hA n).mul (hB n)
  smul := fun c A hA n => by
    simpa only [Pi.smul_apply, smul_eq_mul] using (hA n).const_smul c

/-- `Work.Spaces.Lop = D_θ = sin(2θ) ∂_θ` is a derivation-like operator for the honest `C^∞`
class on an open set. -/
private lemma lop_derivLike_smooth (U : Set ℝ) (hU : IsOpen U) :
    Work.Spaces.DerivLike U (SmoothOn U) Work.Spaces.Lop where
  add := by
    intro A B hA hB θ hθ
    have dA : DifferentiableAt ℝ A θ :=
      ((hA 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
    have dB : DifferentiableAt ℝ B θ :=
      ((hB 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
    show Real.sin (2 * θ) * deriv (A + B) θ
        = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
    rw [show deriv (A + B) θ = deriv A θ + deriv B θ from by
      simpa only [Pi.add_apply] using deriv_add dA dB]
    ring
  mul := by
    intro A B hA hB θ hθ
    exact Work.Spaces.Lop_mul A B θ
      (((hA 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num))
      (((hB 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num))
  congr := by
    intro A B hAB θ hθ
    have hev : A =ᶠ[nhds θ] B := by
      filter_upwards [hU.mem_nhds hθ] with x hx
      exact hAB hx
    show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
    rw [hev.deriv_eq]
  preserve := by
    intro A hA n
    have h1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A U := hA (n + 1)
    have hcast : (n : WithTop ℕ∞) + 1 ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
    have hderiv := h1.deriv_of_isOpen hU hcast
    have hsin : ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
    exact hsin.mul hderiv
  smul := by
    intro c A hA θ hθ
    show Real.sin (2 * θ) * deriv (fun p => c * A p) θ = c * (Real.sin (2 * θ) * deriv A θ)
    rw [deriv_const_mul_field c]
    ring

/-- Linearity of the iterates of `D_θ` on `C^∞`-functions of an open set. -/
private lemma lop_iter_sub_smooth {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : SmoothOn U u) (hv : SmoothOn U v) (n : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[n] (u - v))
      (fun θ => Work.Spaces.Lop^[n] u θ - Work.Spaces.Lop^[n] v θ) U := by
  have hD := lop_derivLike_smooth U hU
  have hP := smoothOn_funClass U
  have hw : SmoothOn U (fun p => (-1 : ℝ) * v p) := hP.smul (-1) v hv
  have h1 := Work.Spaces.DerivLike.iterate_add hD n hu hw
  have h2 := Work.Spaces.DerivLike.iterate_smul hD n (-1) hv
  have hfun : (u - v) = (u + fun p => (-1 : ℝ) * v p) := by
    funext p; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, neg_one_mul]
  rw [hfun]
  refine h1.trans ?_
  intro θ hθ
  have h2θ := h2 hθ
  simp only [Pi.add_apply]
  rw [h2θ]
  ring

/-- The iterated Leibniz rule for `D_θ` on `C^∞`-functions of an open set. -/
private lemma Lop_iter_mul_smooth (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : SmoothOn U u) (hv : SmoothOn U v) (j : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U :=
  Work.Spaces.DerivLike.iterate_mul (lop_derivLike_smooth U hU) (smoothOn_funClass U) j hu hv

/-- `D_θ(h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on the open set `U`, for `h` merely `C^∞`
there (in particular no analyticity and no endpoint information is needed). -/
private lemma Lop_SinQ_eqOn_smooth {U : Set ℝ} (hU : IsOpen U) {h : ℝ → ℝ}
    (hh : SmoothOn U h) (hne : ∀ x ∈ U, Real.sin (2 * x) ≠ 0) :
    Set.EqOn (Work.Spaces.Lop (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * Work.Elliptic.SinQ h θ) U := by
  intro θ hθ
  have h1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) h U := hh 1
  have hsin1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun x : ℝ => Real.sin (2 * x)) U := by
    fun_prop
  have hg1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (Work.Elliptic.SinQ h) U := by
    show ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun x => h x / Real.sin (2 * x)) U
    exact h1.div hsin1 hne
  have hneθ : ∀ᶠ x in nhds θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) =ᶠ[nhds θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [Work.Elliptic.SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ = deriv h θ :=
    heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (Work.Elliptic.SinQ h) θ :=
    (hg1.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * Work.Elliptic.SinQ h θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ :=
    deriv_mul dsin dg
  rw [Work.Elliptic.deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ
      = deriv h θ - 2 * Real.cos (2 * θ) * Work.Elliptic.SinQ h θ
  rw [← hdeq, hprod]
  ring

theorem dthRecOpen (i : ℕ) (hi : 1 ≤ i) (h : ℝ → ℝ)
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ l ∈ Finset.range i, (Nat.choose (i - 1) l : ℝ) *
            (Work.Elliptic.Dth1Iter (i - 1 - l) (fun θ => 2 * Real.cos (2 * θ)) θ) *
            (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos]))
  have hsmU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) h := fun n =>
    hsm.of_le (by exact_mod_cast le_top)
  have hgU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (Work.Elliptic.SinQ h) := fun n => by
    show ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => h x / Real.sin (2 * x))
      (Set.Ioo (0 : ℝ) (Real.pi / 2))
    exact (hsmU n).div (by fun_prop) hne
  have hφU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun x : ℝ => 2 * Real.cos (2 * x)) :=
    fun n => by fun_prop
  have hderU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (deriv h) := fun n =>
    (hsmU (n + 1)).deriv_of_isOpen isOpen_Ioo (by rw [Nat.cast_add, Nat.cast_one])
  have hφgU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2))
      ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) := fun n =>
    (hφU n).mul (hgU n)
  have hD := lop_derivLike_smooth (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
  have hEq : Set.EqOn (Work.Spaces.Lop (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * Work.Elliptic.SinQ h θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := Lop_SinQ_eqOn_smooth hU hsmU hne
  have h1 : Work.Spaces.Lop^[j + 1] (Work.Elliptic.SinQ h) θ
      = Work.Spaces.Lop^[j]
          (fun x : ℝ => deriv h x - (fun x : ℝ => 2 * Real.cos (2 * x)) x * Work.Elliptic.SinQ h x)
          θ := by
    rw [Function.iterate_succ_apply]
    exact (Work.Spaces.DerivLike.iterate_congr hD j hEq) hθ
  have h2 : Work.Spaces.Lop^[j]
        (fun x : ℝ => deriv h x - (fun x : ℝ => 2 * Real.cos (2 * x)) x * Work.Elliptic.SinQ h x) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - Work.Spaces.Lop^[j]
            ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) θ :=
    (lop_iter_sub_smooth hU hderU hφgU j) hθ
  have h3 : Work.Spaces.Lop^[j]
        ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) θ
      = ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
          (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
           Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) :=
    (Lop_iter_mul_smooth (fun x : ℝ => 2 * Real.cos (2 * x)) (Work.Elliptic.SinQ h)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU hφU hgU j) hθ
  have hstep : Work.Spaces.Lop^[j + 1] (Work.Elliptic.SinQ h) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
            (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
             Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) := by
    rw [h1, h2, h3]
  have hsum : (∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ) *
        Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
        Work.Spaces.Lop^[l] (Work.Elliptic.SinQ h) θ)
      = ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
        (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
         Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) := by
    rw [← Finset.sum_range_reflect
      (fun a : ℕ => (Nat.choose j a : ℝ) *
        (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
         Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ)) (j + 1)]
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : (j + 1) - 1 - l = j - l := by omega
    rw [hsub, Nat.sub_sub_self hlj, Nat.choose_symm hlj]
    ring
  simp only [Work.Elliptic.Dth1Iter_eq_iterate_Lop]
  rw [hstep, hsum]

end

end Work.FTS.EllSol.PkgK5
