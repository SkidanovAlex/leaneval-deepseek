import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.VopAux.dzIterSumConstMul
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Linearity of the radial operator `D_z^j` over a finite sum with `θ`-only coefficients

The operator `D_z = z ∂_z` commutes with a sum whose coefficients do not depend on `z`:
for `F k z θ = F k z θ` and `c k θ` an arbitrary `θ`-dependent coefficient,

  `D_z^j (∑_{k∈s} c k θ · F k z θ) = ∑_{k∈s} c k θ · D_z^j (F k) z θ`  on the open quadrant.

The only smoothness needed is the *finite* order `j + 1 ≤ n` at which the induction step
differentiates the summands (the sibling `Work.FTS.EllSol.VopAux.dzIterSumConstMul` needs `C^∞`,
which is more than the consumers of this file have available).

The proof is the induction on `j`: the induction hypothesis identifies the two level-`j`
functions on the (open) quadrant, `pz_congr_of_isOpen` transfers that identity through `∂_z`,
and `deriv_sum` / `deriv_const_mul_field` differentiate the sum term by term.  The
differentiability of the summand slices is the finite-order statement
`contDiffOn_uncurry_DzIter_fin` proved below: `D_z^a` lowers the differentiability order by `a`.
-/

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `Work.Spaces.DzIter a` lowers the differentiability order by `a` on an open set: if `G` is
`C^{N+a}` there, then `D_z^a G` is `C^N` there.  (Induction on `a`, the step being the one-order
statement `Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin`.) -/
private theorem contDiffOn_uncurry_DzIter_fin {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (a N : ℕ), ContDiffOn ℝ ((N + a : ℕ) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter a G)) V := by
  intro a
  induction a with
  | zero => intro N h; simpa using h
  | succ n ih =>
      intro N h
      have h' : ContDiffOn ℝ ((N + 1 + n : ℕ) : WithTop ℕ∞) (Function.uncurry G) V := by
        rw [show N + 1 + n = N + (n + 1) from by omega]; exact h
      have h2 : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter n G)) V := ih (N + 1) h'
      have h3 : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter n G))) V :=
        Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin hV h2
      simpa [Work.Spaces.DzIter_succ] using h3

theorem dzIter_sum_coef_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ) (j : ℕ)
    (hF : ∀ k ∈ s, ContDiffOn ℝ j (Function.uncurry (F k)) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ))
      Work.FTS.EllipticEst.Q0 := by
  revert hF
  induction j with
  | zero => intro hF p hp; rfl
  | succ j ih =>
      intro hF
      -- the induction hypothesis only needs order `j`, which follows from order `j + 1`
      have hFj : ∀ k ∈ s, ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞)
          (Function.uncurry (F k)) Work.FTS.EllipticEst.Q0 :=
        fun k hk => (hF k hk).of_le (by norm_num)
      have hEq := ih hFj
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hp
      -- the `z`-slices of the summands are differentiable (only order `j + 1` is used)
      have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j (F k) z' θ) z := by
        intro k hk
        have hsm : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
            (Function.uncurry (Work.Spaces.DzIter j (F k))) Work.FTS.EllipticEst.Q0 :=
          contDiffOn_uncurry_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 j 1 (by
            rw [show (1 + j : ℕ) = j + 1 from by omega]
            exact hF k hk)
        have h1 : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.DzIter j (F k))) (z, θ) :=
          (hsm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)).differentiableAt
            (by norm_num)
        have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
          (hasFDerivAt_prodMk_left z θ).differentiableAt
        have h3 : DifferentiableAt ℝ
            ((Function.uncurry (Work.Spaces.DzIter j (F k))) ∘ (fun e : ℝ => (e, θ))) z :=
          h1.comp z h2
        simpa [Function.comp_def, Function.uncurry] using h3
      -- the two level-`j` functions agree on the open quadrant, hence so do their `z`-derivatives
      have hpz1 : Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
          = Work.Spaces.pz (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hQ
      -- and the `z`-derivative of the sum is the sum of the `z`-derivatives
      have hpz2 : Work.Spaces.pz (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ
          = ∑ k ∈ s, c k θ * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ := by
        show deriv (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ) z = _
        rw [show (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ)
              = ∑ k ∈ s, (fun z' => c k θ * Work.Spaces.DzIter j (F k) z' θ) from by
            funext z'; rw [Finset.sum_apply]]
        rw [deriv_sum (fun k hk => (hdiff k hk).const_mul (c k θ))]
        exact Finset.sum_congr rfl fun k hk => deriv_const_mul_field (c k θ)
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
          = ∑ k ∈ s, c k θ * Work.Spaces.DzIter (j + 1) (F k) z θ
      rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
            from rfl,
        hpz1, hpz2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [show Work.Spaces.DzIter (j + 1) (F k) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ from rfl]
      ring

end Work.FTS_RegExport.RXT.Slots.JetCalc
