import Mathlib
import Submission.Work.HP.FM.RecDefs

/-!
# Injectivity of the projected presentation `D.step`

Given a `RecData` `D` (an injective presentation `Φ : ℚ^R → E` of a rank-`R` lattice, a
shortest primitive vector `u` and a family `v` completing `u` to a `ℤ`-basis of `ℤ^R`),
the peeled presentation `D.step` sends `t : Fin (R-1) → ℝ` to the orthogonal projection
of `Φ (∑ t_j v_j)` onto the orthogonal complement of `p = Φ u`:

`D.step t = projU D.p (D.Φ (∑ j, t j • v j))`.

Since the realifications of `u, v_0, …, v_{R-2}` are `ℝ`-linearly independent (`D.indep`)
and `Φ` is injective, this forces `D.step` to be injective: if `D.step t = 0`, then
`Φ (∑ t_j v_j)` is a multiple of `p = Φ u`, hence `∑ t_j v_j` is a real multiple of `u`,
and `D.indep` kills all the coefficients `t_j`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Work.HP.FM

/-- The peeled presentation evaluated at a real vector is the orthogonal projection
of `Φ (∑ j, t j • v j)` onto the orthogonal complement of `Φ u`. -/
lemma latStep_eq_projU {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (Φ : LatMap (ι := ι) R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (t : Fin (R - 1) → ℝ) :
    latStep Φ u v t
      = projU (Φ (fun k => (u k : ℝ)))
          (Φ (∑ j, t j • (fun k => (v j k : ℝ)))) := by
  rw [latStep_apply]
  have h1 : Φ (∑ j, t j • (fun k => (v j k : ℝ)))
      = ∑ j, t j • Φ (fun k => (v j k : ℝ)) := by
    rw [map_sum Φ]
    exact Finset.sum_congr rfl fun j _ => map_smul Φ (t j) _
  rw [h1, map_sum (projU (Φ (fun k => (u k : ℝ))))]
  exact Finset.sum_congr rfl fun j _ => (map_smul (projU (Φ (fun k => (u k : ℝ)))) (t j)
    (Φ (fun k => (v j k : ℝ)))).symm

/-- `D.step` is the orthogonal projection of `D.Φ (∑ j, t j • D.v j)` onto `D.p^⊥`. -/
lemma RecData.step_eq_projU {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (D : RecData R ι) (t : Fin (R - 1) → ℝ) :
    D.step t = projU D.p (D.Φ (∑ j, t j • (fun k => (D.v j k : ℝ)))) := by
  rw [RecData.step, RecData.p]
  exact latStep_eq_projU D.Φ D.u D.v t

/-- The shortest vector of a `RecData` is nonzero. -/
private lemma RecData.p_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (D : RecData R ι) : D.p ≠ 0 := by
  intro h0
  have h1 : (fun j => (D.u j : ℝ)) = 0 := by
    apply D.Φ_inj
    rw [map_zero]
    exact h0
  have h2 : D.u = 0 := funext fun j => Int.cast_eq_zero.mp (congr_fun h1 j)
  exact D.u_ne h2

theorem latStep_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (D : Work.HP.FM.RecData R ι) :
    Function.Injective D.step := by
  have hp : D.p ≠ 0 := D.p_ne_zero
  intro t t' h
  set s : Fin (R - 1) → ℝ := t - t' with hs
  set w : Fin R → ℝ := ∑ j, s j • (fun k => (D.v j k : ℝ)) with hw
  -- `D.step s = 0`
  have hs0 : D.step s = 0 := by rw [hs, map_sub, h, sub_self]
  -- rewrite it as a projection
  have hstep : D.step s = projU D.p (D.Φ w) := by
    rw [RecData.step_eq_projU D s, ← hw]
  have hproj : projU D.p (D.Φ w) = 0 := by rw [← hstep]; exact hs0
  -- hence `Φ w` is a real multiple of `p = Φ u`
  obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp
    ((projU_eq_zero_iff D.p hp (D.Φ w)).mp hproj)
  have hu : w = mu • (fun j => (D.u j : ℝ)) := by
    have h2 : w - mu • (fun j => (D.u j : ℝ)) = 0 := by
      apply D.Φ_inj
      rw [map_zero, map_sub, map_smul, ← RecData.p, hmu, sub_self]
    exact sub_eq_zero.mp h2
  -- `ℝ`-linear independence of the realifications of `u, v` forces `s = 0`
  have hdep : (-mu, s) = 0 := by
    apply D.indep
    show (-mu) • (fun j => (D.u j : ℝ)) + ∑ i, s i • (fun j => (D.v i j : ℝ)) = 0
    have hsum : ∑ i, s i • (fun j => (D.v i j : ℝ)) = mu • (fun j => (D.u j : ℝ)) := by
      rw [← hw]; exact hu
    rw [hsum, neg_smul, neg_add_cancel]
  have hsc : s = 0 := by
    have := congrArg Prod.snd hdep
    simpa using this
  exact sub_eq_zero.mp (by rw [← hs]; exact hsc)

end Work.HP.FM
