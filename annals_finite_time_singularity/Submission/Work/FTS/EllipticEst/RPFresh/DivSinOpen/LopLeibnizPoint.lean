/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise Leibniz rule for iterates of the angular operator `Lop`

`Work.Spaces.Lop u θ = sin(2θ) · u'(θ)` is the action of `D_θ = sin(2θ) ∂_θ` on functions of
`θ` alone; it is a derivation for the pointwise product.  This file proves the binomial
expansion for its iterates **at a point**, from *finite-order* regularity there:

  `Lop^[k] (u * v) θ = ∑_{a ≤ k} C(k,a) · (Lop^[a] u θ) · (Lop^[k-a] v θ)`,

for `u`, `v` of class `C^k` at `θ` (i.e. `ContDiffAt ℝ ((k : ℕ) : ℕ∞ω)` — the *finite* order
`k`, not the analytic order `⊤` for which the `Set.EqOn` version
`Work.Spaces.Lop_iter_mul_eqOn` is already available).

The proof spends exactly one order of regularity per iterate and proceeds through

* `Lop_contDiffAt` — iterating `Lop` costs one order of differentiability at a point;
* `Lop_iter_contDiffAt` — consequently `Lop^[a] u` is `C^{k-a}` at `θ` for `a ≤ k`;
* `Lop_iter_mul_eqOn_fin` — the finite-order Leibniz rule as a `Set.EqOn` on an open set,
  obtained by induction on the order: at level `j + 1` one differentiates the level-`j`
  identity (valid on the whole open set, hence on a neighbourhood of every point of it),
  differentiates the individual binomial summands (each of which is `C^{≥ 1}` there, as one
  order is left over in every slot) and recombines with the Pascal identity
  `Work.Spaces.leibniz_step`;
* `LopLeibnizPoint` — the pointwise statement, by first passing from `ContDiffAt` at `θ` to
  `ContDiffOn` on an open neighbourhood of `θ`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped ContDiff Real Topology
open Filter

namespace Work.FTS.EllipticEst.RPFresh.DivSinOpen

/-- The finite order `C^n` as an element of the differentiability order type `ℕ∞ω`. -/
abbrev LopOrd (n : ℕ) : ℕ∞ω := ((n : ℕ) : ℕ∞ω)

/-- The order `n + 1` is the successor of the order `n`. -/
lemma LopOrd_succ (n : ℕ) : LopOrd (n + 1) = LopOrd n + 1 := by
  simp only [LopOrd]; push_cast; ring

/-- The order `ℕ∞ω` is monotone in the natural number. -/
lemma LopOrd_le {a b : ℕ} (h : a ≤ b) : LopOrd a ≤ LopOrd b := by
  simp only [LopOrd]; exact_mod_cast h

/-- A positive finite order is a positive element of `ℕ∞ω`. -/
lemma LopOrd_pos {n : ℕ} (h : 0 < n) : 0 < LopOrd n := by
  simp only [LopOrd]; exact_mod_cast h

/-- A positive finite order is nonzero in `ℕ∞ω`. -/
lemma LopOrd_ne_zero_of_pos {n : ℕ} (h : 0 < n) : LopOrd n ≠ 0 :=
  ne_of_gt (LopOrd_pos h)

/-- Every finite order is strictly below the smooth order `∞` (`= ↑⊤ : ℕ∞`). -/
lemma LopOrd_lt_omega (n : ℕ) : LopOrd n < ∞ := by
  rw [show ∞ = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  simp only [LopOrd]
  exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)

/-- Applying `Lop = sin(2·) ∂` costs exactly one order of pointwise differentiability. -/
lemma Lop_contDiffAt (n : ℕ) {u : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ (LopOrd (n + 1)) u θ) :
    ContDiffAt ℝ (LopOrd n) (Work.Spaces.Lop u) θ := by
  have hd : ContDiffAt ℝ (LopOrd n) (deriv u) θ :=
    hu.derivWithin (le_of_eq (LopOrd_succ n).symm)
  have hsin : ContDiffAt ℝ (LopOrd n) (fun θ : ℝ => Real.sin (2 * θ)) θ := by
    have h : ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
    exact h.of_le le_top
  have heq : Work.Spaces.Lop u = (fun θ : ℝ => Real.sin (2 * θ)) * deriv u := rfl
  rw [heq]
  exact hsin.mul hd

/-- Iterating `Lop` costs one order of regularity per application: if `u` is `C^k` at `θ`
then `Lop^[a] u` is `C^{k-a}` at `θ` (for `a ≤ k`). -/
lemma Lop_iter_contDiffAt (a k : ℕ) (hak : a ≤ k) {u : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ (LopOrd k) u θ) :
    ContDiffAt ℝ (LopOrd (k - a)) (Work.Spaces.Lop^[a] u) θ := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
      have hak' : a ≤ k := le_trans (Nat.le_succ a) hak
      have hprev : ContDiffAt ℝ (LopOrd (k - a)) (Work.Spaces.Lop^[a] u) θ := ih hak'
      have hsucc : ContDiffAt ℝ (LopOrd (k - (a + 1) + 1)) (Work.Spaces.Lop^[a] u) θ := by
        have : k - (a + 1) + 1 = k - a := by omega
        rw [this]; exact hprev
      have hmain := Lop_contDiffAt (k - (a + 1)) hsucc
      rw [Function.iterate_succ_apply']
      exact hmain

/-- **Leibniz rule for iterates of `Lop`, finite order.**  On an open set `U` where `u` and
`v` are `C^j`, the `j`-th iterate of `Lop` applied to the pointwise product agrees on `U`
with the binomial convolution.  Unlike `Work.Spaces.Lop_iter_mul_eqOn` the regularity
hypothesis is of order `j`, not `⊤`: one order is spent at each induction step, exactly the
amount needed to differentiate the level-`(j-1)` identity and the individual summands. -/
theorem Lop_iter_mul_eqOn_fin : ∀ (j : ℕ) (k : ℕ) (u v : ℝ → ℝ) (U : Set ℝ), IsOpen U →
    ContDiffOn ℝ (LopOrd k) u U → ContDiffOn ℝ (LopOrd k) v U → j ≤ k →
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  intro j
  induction j with
  | zero =>
      intro k u v U hU hu hv hjk θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro k u v U hU hu hv hjk θ hθ
      have ihfun := ih k u v U hU hu hv (by omega)
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (ihfun.deriv hU) hθ
      have hdu : ∀ a ≤ j, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
        intro a haj
        exact (Lop_iter_contDiffAt a k (by omega)
          (hu.contDiffAt (hU.mem_nhds hθ))).differentiableAt
            (LopOrd_ne_zero_of_pos (by omega))
      have hdv : ∀ b ≤ j, DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := by
        intro b hbj
        exact (Lop_iter_contDiffAt b k (by omega)
          (hv.contDiffAt (hU.mem_nhds hθ))).differentiableAt
            (LopOrd_ne_zero_of_pos (by omega))
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact ((hdu a haj).mul (hdv (j - a) (by omega))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [Function.iterate_succ_apply', hkey]
      rw [Finset.sum_congr rfl
        (fun a ha => Work.Spaces.sin_deriv_term u v θ j a
          (hdu a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hdv (j - a) (by omega)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

theorem LopLeibnizPoint (k : ℕ) {u v : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) u θ)
    (hv : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) v θ) :
    Work.Spaces.Lop^[k] (u * v) θ
      = ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[k - a] v θ) := by
  -- pass to an open neighbourhood on which `u` and `v` are of class `C^k`
  obtain ⟨s, hs, hsu⟩ := hu.contDiffOn (le_refl (LopOrd k))
    (fun h => absurd h (ne_of_lt (LopOrd_lt_omega k)))
  obtain ⟨t, ht, htv⟩ := hv.contDiffOn (le_refl (LopOrd k))
    (fun h => absurd h (ne_of_lt (LopOrd_lt_omega k)))
  obtain ⟨W, hWst, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
  exact Lop_iter_mul_eqOn_fin k k u v W hWopen (hsu.mono (fun x hx => (hWst hx).1))
    (htv.mono (fun x hx => (hWst hx).2)) le_rfl hθW

end Work.FTS.EllipticEst.RPFresh.DivSinOpen
