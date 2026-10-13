/-
# `Work.StabilityFar.St5` — the Beale–Kato–Majda divergence

`St5` converts the *a priori* lower bound on the vorticity at the maximal time into the last
clause of `theorem_1`, the divergence of `∫₀ᵗ ‖ω(·,s)‖_∞ ds` as `t → 1⁻`.

The input is the modulational bound of the construction: with `λ̄(t) = (T*-t)Λ(t)`, `Λ ≥ 1/2`,
the profile bound `|g|_{H⁴} ≤ Cα²` and the `L^∞ ⊂ H²` embedding
`Work.Spaces.Linf_H2` applied to `F = F_* + g` give

  `‖ω(·,t)‖_∞ ≥ c₀α/(4(T*-t))`   for `t ∈ [0,T*)`,

which is `VortLinfLower u T* (c₀α/4)` in the vocabulary of `Defs`.  The mathematical content of
`St5` itself is one-dimensional: `∫₀ᵗ ds/(T*-s) = log(T*/(T*-t)) → +∞`, and the comparison
`∫₀ᵗ ‖ω(·,s)‖_∞ ds ≥ ∫₀ᵗ c/(T*-s) ds` gives the divergence
(`Work.StabilityFar.BKM.bkm_tendsto_atTop_of_linf_lower`).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.StabilityFar.BKM.bkm_tendsto_atTop_of_linf_lower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- A pointwise lower bound for one slice of the vorticity gives a lower bound for the `L^∞`-norm
`vortLInf u t = ⨆ₓ ‖ω(x,t)‖`, provided the supremum is honest (`BddAbove`).  This is the form in
which the construction's data (a point where the profile `F_* + g` is large) is fed into `St5`. -/
theorem vortLInf_lower_of_exists {u : R3 → ℝ → R3} {t c : ℝ}
    (hbdd : BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => u y t) x‖)))
    (h : ∃ x : R3, c ≤ ‖vorticity (fun y => u y t) x‖) :
    c ≤ Work.LWP.vortLInf u t :=
  h.elim (fun x hx => le_trans hx (le_ciSup hbdd x))

/-- **`St5`.**  If the `L^∞`-norm of the vorticity dominates `c/(T*-t)` on `[0,T*)`, then the BKM
integral `bkm u t = ∫₀ᵗ ‖ω(·,s)‖_∞ ds` diverges as `t → T*⁻`. -/
theorem bkm_divergence_of_vortLinfLower {u : R3 → ℝ → R3} {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (h : VortLinfLower u T c)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (Work.LWP.bkm u) (𝓝[<] T) Filter.atTop :=
  BKM.bkm_tendsto_atTop_of_linf_lower hT hc h hint

/-- **`St5` at the physical blow-up time `1`**, in the exact shape of `theorem_1`'s last
clause. -/
theorem bkm_divergence_at_one {u : R3 → ℝ → R3} {c : ℝ} (hc : 0 < c)
    (h : VortLinfLower u 1 c)
    (hint : ∀ t ∈ Set.Ico 0 1, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖) (𝓝[<] 1)
      Filter.atTop := by
  have h1 := bkm_divergence_of_vortLinfLower (u := u) (T := (1 : ℝ)) (c := c) one_pos hc h hint
  have h2 : Work.LWP.bkm u = fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖ :=
    funext (fun t => rfl)
  rw [h2] at h1
  exact h1

/-! ## The `St5` lower bound from the self-similar ansatz

The paper's construction represents the vorticity by the self-similar ansatz
`ω(x,t) = λ̄(t)^{-1}·F(z,θ)` with `F = F_* + g`, `λ̄(t) = (T*-t)Λ(t)`.  Two ingredients then give
the `L^∞` lower bound consumed by `St5`:

* `Work.StabilityFar.Profile.exists_Fstar_add_ge`: the profile `F_* + g` is `≥ c₀α` somewhere in the
  domain as soon as `‖g‖_∞ ≤ c₀α/2` (with `Linf_H2`, `‖g‖_∞ ≤ 100√10·Cα^{3/2} ≤ c₀α/2`);
* the upper bound `Λ ≤ 2` of the bootstrap, i.e. `λ̄(t) ≤ 2(T*-t)`.

The lemma below packages the (elementary) step from those two to `VortLinfLower u T* (c₀α/2)`. -/

/-- **The `St5` lower bound from the ansatz.**  If at every time `t < T*` there is a point `x` with
`c₀α ≤ λ̄(t)·‖ω(x,t)‖` (the self-similar ansatz, read in the physical space, with the profile bound
`c₀α ≤ |F_* + g|` of `Profile.exists_Fstar_add_ge`), and if the modulation obeys
`0 < λ̄(t) ≤ 2(T*-t)`, then the vorticity sup-norm dominates `c₀α/(2(T*-t))`. -/
theorem vortLinfLower_of_ansatz {u : R3 → ℝ → R3} {T c₀ α : ℝ} {lam : ℝ → ℝ}
    (hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t)
    (hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hbdd : ∀ t ∈ Set.Ico 0 T,
      BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => u y t) x‖)))
    (hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * α ≤ lam t * ‖vorticity (fun y => u y t) x‖) :
    VortLinfLower u T (c₀ * α / 2) := by
  intro t ht
  obtain ⟨x, hx⟩ := hansatz t ht
  have h1 : c₀ * α / 2 / (T - t) ≤ ‖vorticity (fun y => u y t) x‖ := by
    have hTt : (0 : ℝ) < T - t := by linarith [ht.2]
    rw [div_le_iff₀ hTt]
    have h2 : c₀ * α ≤ lam t * ‖vorticity (fun y => u y t) x‖ := hx
    have h3 : lam t * ‖vorticity (fun y => u y t) x‖
        ≤ 2 * (T - t) * ‖vorticity (fun y => u y t) x‖ :=
      mul_le_mul_of_nonneg_right (hlam_le t ht) (norm_nonneg _)
    linarith
  exact vortLInf_lower_of_exists (u := u) (t := t) (c := c₀ * α / 2 / (T - t))
    (hbdd t ht) ⟨x, h1⟩

end Work.StabilityFar
