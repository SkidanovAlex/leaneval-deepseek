import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open MeasureTheory

-- `R` is part of the interface (it is the radius of the support hypothesis) but the argument
-- of this file only needs `0 < ℓ`; keep the binder, silence the linter.
set_option linter.unusedVariables false

/-! ## The lattice is locally finite

The only analytic input of `W1funPeriodSummable` is that a bounded set contains only finitely
many lattice points of `ℓℤ³`.  We prove it in the crudest possible way: if `‖lat ℓ n‖ ≤ S` then,
by `|(lat ℓ n) i| ≤ ‖lat ℓ n‖`, every coordinate of `n` satisfies `|(n i : ℝ)| ≤ S / ℓ`, so `n`
runs through the finite box `[-⌈S/ℓ⌉, ⌈S/ℓ⌉]³`. -/

/-- **A bounded set meets the lattice `ℓℤ³` (`ℓ > 0`) in finitely many points.** -/
lemma finite_lat_le {ℓ : ℝ} (hℓ : 0 < ℓ) (S : ℝ) :
    {n : Fin 3 → ℤ | ‖Work.BoseFixR.lat ℓ n‖ ≤ S}.Finite := by
  have hsub : {n : Fin 3 → ℤ | ‖Work.BoseFixR.lat ℓ n‖ ≤ S}
      ⊆ Set.univ.pi (fun _ : Fin 3 => (Set.Icc (-(⌈S / ℓ⌉)) (⌈S / ℓ⌉) : Set ℤ)) := by
    intro n hn
    rw [Set.mem_univ_pi]
    intro i
    have hn' : ‖Work.BoseFixR.lat ℓ n‖ ≤ S := hn
    -- the coordinate bound: `|ℓ * n i| ≤ ‖lat ℓ n‖`
    have h1 : |(n i : ℝ)| ≤ S / ℓ := by
      have h2 := PiLp.norm_apply_le (Work.BoseFixR.lat ℓ n) i
      rw [Work.BoseFixR.lat_apply] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hℓ, mul_comm] at h2
      exact (le_div_iff₀ hℓ).mpr (by linarith [h2, hn'])
    have h3 : |(n i : ℝ)| ≤ (⌈S / ℓ⌉ : ℝ) := le_trans h1 (Int.le_ceil _)
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have : ((-(⌈S / ℓ⌉) : ℤ) : ℝ) ≤ (n i : ℝ) := by
        push_cast
        exact (abs_le.mp h3).1
      exact_mod_cast this
    · exact_mod_cast (abs_le.mp h3).2
  exact (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).subset hsub

/-- **`W₁` vanishes off `B(0,R)`.**  `W₁ = wScaled ℓ (g₀)` is `g₀` divided by `(χ⋆χ)(·/ℓ)`, and
`g₀ = v(1−ω)` vanishes where `v` does, i.e. outside `B(0,R)` (`g0_zero_of_norm_ge`). -/
lemma W1fun_eq_zero_of_le_norm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : R ≤ ‖y‖) :
    Work.BoseFixR.W1fun v h ℓ y = 0 := by
  have hy0 : Submission.BoseGases.g0 v h y = 0 :=
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp hy h
  rw [show Work.BoseFixR.W1fun v h ℓ y
      = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) y from rfl]
  simp [Submission.BoseGases.wScaled, hy0]

/-- **The periodisation of `W₁` is summable at every point** — the `hper` hypothesis consumed by
`LatGreen.CellParseval` and `LatGreen.LatGreenParseval` for the intended charge `W = W1fun v h ℓ`.

Route: `W₁ = wScaled ℓ (g₀)` with `g₀ = v(1 − ω)` and `supp g₀ ⊆ B(0,R)`, hence `W₁ x = 0` for
`‖x‖ > R`; so for `ℓ ≠ 0` the family `n ↦ W₁(x − lat ℓ n)` is supported on
`{n : ‖lat ℓ n‖ ≤ R + ‖x‖}`, a finite set (`Work.BoseFixR.lat_injective` plus finiteness of the
lattice points in a bounded set), whence the `tsum` is a finite sum.  The hypothesis `0 < ℓ` is
**necessary**: at `ℓ = 0` one has `lat 0 n = 0` for all `n`, so the summand is the constant
`W1fun v h 0 x = g0 v h x / ∫χ²`, which is nonzero for the intended (nontrivial) `g₀`.  Both
consumers (`CellParseval`, `LatGreenParseval`) carry `hℓ : 0 < ℓ` already.  Obtain the vanishing of
`W₁` off `B(0,R)` directly from the support of `g₀` and `|wScaled ℓ h| ≤ 2|h|`; do not route through
`FarRowW1sqPH`, whose import cone is currently broken by an unrelated duplicate declaration in
another agent's `LatticeW1sq*` files. -/
theorem W1funPeriodSummable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => Work.BoseFixR.W1fun v h ℓ (x - Work.BoseFixR.lat ℓ n)) := by
  intro x
  -- the summand is supported where the translated lattice point stays in `B(0, R + ‖x‖)`
  have hsupp : Function.support
      (fun n : Fin 3 → ℤ => Work.BoseFixR.W1fun v h ℓ (x - Work.BoseFixR.lat ℓ n))
      ⊆ {n : Fin 3 → ℤ | ‖Work.BoseFixR.lat ℓ n‖ ≤ R + ‖x‖} := by
    intro n hn
    rw [Function.mem_support] at hn
    change ‖Work.BoseFixR.lat ℓ n‖ ≤ R + ‖x‖
    by_contra hc
    rw [not_le] at hc
    -- `‖lat ℓ n‖ ≤ ‖lat ℓ n − x‖ + ‖x‖ = ‖x − lat ℓ n‖ + ‖x‖`, so `R < ‖x − lat ℓ n‖`
    have hge : R ≤ ‖x - Work.BoseFixR.lat ℓ n‖ := by
      have h1 : ‖Work.BoseFixR.lat ℓ n‖ ≤ ‖Work.BoseFixR.lat ℓ n - x‖ + ‖x‖ := by
        have h := norm_add_le (Work.BoseFixR.lat ℓ n - x) x
        rwa [sub_add_cancel] at h
      have h2 : ‖Work.BoseFixR.lat ℓ n - x‖ = ‖x - Work.BoseFixR.lat ℓ n‖ := norm_sub_rev _ _
      linarith [h1, h2, hc]
    exact hn (W1fun_eq_zero_of_le_norm h hv_supp hge)
  exact summable_of_hasFiniteSupport ((finite_lat_le hℓ (R + ‖x‖)).subset hsupp)

end Work.BoseFixR.LatGreen
