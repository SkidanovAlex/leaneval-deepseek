import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs

/-!
# Comparing the monodromy of the conjugate covering along two paths

Let `p : Y × ℝ → Y` be the first projection, equipped with a topology `htop` on `Y × ℝ` making it a
covering map (the situation of `Submission.conjTopology`), and let `conjShift c` be the translation
`(y, t) ↦ (y, t + c)` of the étale space.

The *period* `Submission.conjPeriod u₀ e₀ cov δ` of a loop `δ` at `u₀` is the drift in the second
coordinate of the monodromy of the covering along `δ`, i.e.
`cov.monodromy δ e₀ = conjFiberShift (conjPeriod u₀ e₀ cov δ) e₀`
(`Submission.monodromy_eq_conjFiberShift`).  Consequently, if every period at `e₀` is a multiple of
`2π`, then for any two paths `γ, γ' : u₀ → x` the endpoints of their lifts differ by
`conjFiberShift (k · 2π)` for some `k : ℤ`.

The two structural facts behind this are

* the translation `conjShift c` commutes with the monodromy: the lift of a path starting at a
  translated point is the translate of the lift of that path (`liftPath_conjShift_apply'`), hence
  `cov.monodromy γ (conjFiberShift c e) = conjFiberShift c (cov.monodromy γ e)`; and

* the monodromy of the loop `γ' · γ⁻¹` at `u₀` is exactly the discrepancy between the endpoints of
  the lifts of `γ'` and of `γ` at `e₀`.

The lemmas below are stated for an arbitrary topological space `Y` and an arbitrary topology on
`Y × ℝ`: they never use a complex structure on `Y`, unlike the corresponding statements in
`Submission.Conjugate`, which are proved under charted-space hypotheses.
-/

open Path.Homotopic

namespace Work.Modulus

variable {Y : Type*} [TopologicalSpace Y] [htop : TopologicalSpace (Y × ℝ)]

/-- The value of the monodromy of a covering map along the class of a path is the endpoint of the
lift of that path.  This is `rfl`; it is recorded here because the version in
`Submission.Conjugate` carries charted-space hypotheses. -/
theorem monodromy_mk_val_eq_liftPath' (cov : IsCoveringMap (Prod.fst : Y × ℝ → Y))
    {a b : Y} (γ : Path a b) (e : ↥(Submission.conjFiber a)) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) e).1
      = cov.liftPath γ e.1 (γ.source.trans e.2.symm) 1 := rfl

/-- **Translation commutes with path lifting.**  If `γ` is a path in the base and `e` a lift of its
starting point, then the lift of `γ` starting at the translated point `conjShift c e` is the
translate of the lift starting at `e`. -/
theorem liftPath_conjShift_apply' (cov : IsCoveringMap (Prod.fst : Y × ℝ → Y)) (c : ℝ)
    (hσ : Continuous (Submission.conjShift (X := Y) c))
    {x y : Y} (γ : Path x y) (e : Y × ℝ) (he : γ 0 = Prod.fst e) :
    ∀ t : unitInterval,
      cov.liftPath γ (Submission.conjShift (X := Y) c e)
        (by rw [Submission.conjShift]; exact he) t
      = Submission.conjShift (X := Y) c (cov.liftPath γ e he t) := by
  intro t
  have h := (cov.eq_liftPath_iff' (γ := γ) (e := Submission.conjShift (X := Y) c e)
    (γ_0 := by rw [Submission.conjShift]; exact he)
    (Γ := ⟨fun s => Submission.conjShift (X := Y) c (cov.liftPath γ e he s),
      hσ.comp (cov.liftPath γ e he).continuous⟩)).mpr ?_
  · rw [← h]
    rfl
  · refine ⟨?_, ?_⟩
    · funext s
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [show Prod.fst (Submission.conjShift (X := Y) c (cov.liftPath γ e he s))
          = Prod.fst (cov.liftPath γ e he s) from rfl]
      exact congr_fun (cov.liftPath_lifts γ e he) s
    · simp only [ContinuousMap.coe_mk]
      rw [cov.liftPath_zero]

/-- **The monodromy commutes with the translation of the fibre.** -/
theorem monodromy_conjFiberShift' (cov : IsCoveringMap (Prod.fst : Y × ℝ → Y)) (c : ℝ)
    (hσ : Continuous (Submission.conjShift (X := Y) c))
    {x y : Y} (γ : Path.Homotopic.Quotient x y) (e : ↥(Submission.conjFiber x)) :
    cov.monodromy γ (Submission.conjFiberShift c e)
      = Submission.conjFiberShift c (cov.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  apply Subtype.ext
  apply Prod.ext
  · exact (cov.monodromy _ (Submission.conjFiberShift c e)).2.trans
      ((Submission.conjFiberShift c (cov.monodromy _ e)).2).symm
  · show (cov.monodromy (Path.Homotopic.Quotient.mk γ) (Submission.conjFiberShift c e)).1.2
      = (Submission.conjFiberShift c (cov.monodromy (Path.Homotopic.Quotient.mk γ) e)).1.2
    rw [show Submission.conjFiberShift c e
        = (⟨Submission.conjShift (X := Y) c e.1, e.2⟩ : ↥(Submission.conjFiber x)) from rfl]
    rw [monodromy_mk_val_eq_liftPath' cov γ ⟨Submission.conjShift (X := Y) c e.1, e.2⟩]
    rw [show Submission.conjFiberShift c (cov.monodromy (Path.Homotopic.Quotient.mk γ) e)
        = (⟨Submission.conjShift (X := Y) c
              (cov.liftPath γ e.1 (γ.source.trans e.2.symm) 1),
            (cov.monodromy (Path.Homotopic.Quotient.mk γ) e).2⟩ : ↥(Submission.conjFiber y)) from by
      refine Subtype.ext ?_
      exact congrArg (Submission.conjShift (X := Y) c) (monodromy_mk_val_eq_liftPath' cov γ e)]
    exact congrArg (fun z : Y × ℝ => z.2)
      (liftPath_conjShift_apply' cov c hσ γ e.1 (γ.source.trans e.2.symm) 1)

/-- **The monodromy of a loop is the shift by its period.** -/
theorem monodromy_eq_conjFiberShift' (cov : IsCoveringMap (Prod.fst : Y × ℝ → Y)) (x : Y)
    (e₀ : ↥(Submission.conjFiber x)) (γ : FundamentalGroup Y x) :
    cov.monodromy γ e₀
      = Submission.conjFiberShift (Submission.conjPeriod x e₀ cov γ) e₀ := by
  apply Subtype.ext
  apply Prod.ext
  · exact (cov.monodromy γ e₀).2.trans e₀.2.symm
  · simp only [Submission.conjFiberShift, Submission.conjPeriod]
    ring

/-- **Two paths with the same endpoints lift to points differing by an integral multiple of the
periods.**  If every period at `e₀` is an integral multiple of `2π`, then the lifts of `γ` and `γ'`
at `e₀` differ by `conjFiberShift (k · 2π)` for some `k : ℤ`. -/
theorem exists_int_monodromy_eq_conjFiberShift
    {Y : Type*} [TopologicalSpace Y] [htop : TopologicalSpace (Y × ℝ)]
    (cov : IsCoveringMap (Prod.fst : Y × ℝ → Y))
    (hσ : ∀ c : ℝ, Continuous (Submission.conjShift (X := Y) c))
    {u₀ x : Y} (e₀ : ↥(Submission.conjFiber u₀)) (γ γ' : Path u₀ x)
    (hper : ∀ δ : FundamentalGroup Y u₀,
      ∃ k : ℤ, Submission.conjPeriod u₀ e₀ cov δ = k * (2 * Real.pi)) :
    ∃ k : ℤ, cov.monodromy (Path.Homotopic.Quotient.mk γ') e₀
      = Submission.conjFiberShift (k * (2 * Real.pi)) (cov.monodromy (Path.Homotopic.Quotient.mk γ) e₀) := by
  set δ : FundamentalGroup Y u₀ :=
    (Path.Homotopic.Quotient.mk γ').trans (Path.Homotopic.Quotient.mk γ).symm with hδ
  obtain ⟨k, hk⟩ := hper δ
  refine ⟨k, ?_⟩
  have hcomp : δ.trans (Path.Homotopic.Quotient.mk γ) = Path.Homotopic.Quotient.mk γ' := by
    rw [hδ]
    simp
  rw [← hcomp, cov.monodromy_trans_apply δ (Path.Homotopic.Quotient.mk γ) e₀,
    monodromy_eq_conjFiberShift' cov u₀ e₀ δ, hk]
  exact monodromy_conjFiberShift' cov (k * (2 * Real.pi)) (hσ (k * (2 * Real.pi)))
    (Path.Homotopic.Quotient.mk γ) e₀

end Work.Modulus
