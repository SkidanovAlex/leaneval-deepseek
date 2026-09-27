import Mathlib
import Submission.Work.Mostow.periodicOrbitFix
import Submission.Work.Mostow.BaryBase

/-!
# `parabolicPow`: a positive power of a parabolic isometry is parabolic

If `g` is a parabolic isometry of `ℍⁿ` (no fixed point in `ℍⁿ`, infimal displacement `0`) then so is
`g ^ m` for every `m > 0`.

* *No fixed point.*  If `(g ^ m) • u = u` then `periodicOrbitFix` (a finite orbit sum in the
  hyperboloid model, which is future timelike and hence a point of `ℍⁿ`) produces a fixed point of
  `g`, contradicting parabolicity of `g`.
* *Infimal displacement `0`.*  The `m`-th power acts as the `m`-fold iterate of the action of `g`
  (`pow_smul_iterate`), so the triangle inequality together with the isometry property gives
  `hdist u ((g ^ m) • u) ≤ m * hdist u (g • u)` (`hdist_pow_le`).  Taking `u` with
  `hdist u (g • u) < ε / m` (which parabolicity of `g` provides) yields the claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## Iterates of the action -/

/-- The `m`-th power of `g` acts as the `m`-fold iterate of the action of `g`. -/
theorem pow_smul_iterate (hA : POActionProp n) (g : PO n 1) (m : ℕ) :
    ∀ u : E n, (g ^ m) • u = (fun x : E n => g • x)^[m] u := by
  induction m with
  | zero => intro u; rw [pow_zero, hA.2.2.2.1]; rfl
  | succ m ih =>
      intro u
      rw [pow_succ, hA.2.2.2.2.1 (g ^ m) g u, ih (g • u), Function.iterate_succ_apply]

/-! ## Distance estimates along an orbit -/

/-- Iterates of a distance-preserving map preserve distances. -/
theorem hdist_iterate_eq (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (j : ℕ) (a b : E n) :
    hdist (f^[j] a) (f^[j] b) = hdist a b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (f a) (f b), hf a b]

/-- Consecutive points of an orbit under a distance-preserving map are at constant distance. -/
theorem hdist_iterate_step (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (u : E n) (j : ℕ) :
    hdist (f^[j] u) (f^[j] (f u)) = hdist u (f u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      calc hdist (f^[j+1] u) (f^[j+1] (f u))
          = hdist (f^[j] (f u)) (f^[j] (f (f u))) := by
              rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        _ = hdist (f u) (f (f u)) := hdist_iterate_eq f hf j (f u) (f (f u))
        _ = hdist u (f u) := hf u (f u)

/-- Triangle-inequality bound for the displacement of an iterate of a distance-preserving map. -/
theorem hdist_iterate_le (hI : HypIsometryProp n) (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (u : E n) (m : ℕ) :
    hdist u (f^[m] u) ≤ (m : ℝ) * hdist u (f u) := by
  induction m with
  | zero => simp [hdist_self]
  | succ m ih =>
      calc hdist u (f^[m+1] u)
          = hdist u (f^[m] (f u)) := by rw [Function.iterate_succ_apply]
        _ ≤ hdist u (f^[m] u) + hdist (f^[m] u) (f^[m] (f u)) :=
              hI.2.2.2.1 u (f^[m] u) (f^[m] (f u))
        _ = hdist u (f^[m] u) + hdist u (f u) := by rw [hdist_iterate_step f hf u m]
        _ ≤ (m : ℝ) * hdist u (f u) + hdist u (f u) := by linarith
        _ = ((m + 1 : ℕ) : ℝ) * hdist u (f u) := by push_cast; ring

/-- The displacement of the `m`-th power is at most `m` times the displacement of `g`. -/
theorem hdist_pow_le (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1) (u : E n)
    (m : ℕ) : hdist u ((g ^ m) • u) ≤ (m : ℝ) * hdist u (g • u) := by
  rw [pow_smul_iterate hA g m u]
  exact hdist_iterate_le hI (fun x : E n => g • x) (fun a b => hI.2.2.2.2.2.2.1 g a b) u m

/-! ## The main statement -/

theorem parabolicPow (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {g : LeanEval.Geometry.MostowRigidity.PO n 1} (hg : Submission.Mostow.IsParabolic g)
    {m : ℕ} (hm : 0 < m) : Submission.Mostow.IsParabolic (g ^ m) := by
  constructor
  · intro u hu
    obtain ⟨b, hb⟩ := periodicOrbitFix n hA g m hm u hu
    exact hg.1 b hb
  · intro ε hε
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    obtain ⟨u, hu⟩ := hg.2 (ε / m) (by positivity)
    refine ⟨u, ?_⟩
    have hle := hdist_pow_le hA hI g u m
    have hlt : (m : ℝ) * hdist u (g • u) < (m : ℝ) * (ε / m) :=
      mul_lt_mul_of_pos_left hu hmR
    have hmul : (m : ℝ) * (ε / m) = ε := by field_simp
    linarith

end

end Work.Mostow
