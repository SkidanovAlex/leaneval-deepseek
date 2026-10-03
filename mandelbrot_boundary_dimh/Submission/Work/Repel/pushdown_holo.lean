import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# REPEL: holomorphy of the pushed-down horn map

`pushdown E ζ = π(E(log ζ/(2πi)))` for `ζ ≠ 0`, where `π = piExp` and `E` is `T`-equivariant
(`T w = w + 1`) on the `T`-invariant set `DR`.  We prove that `pushdown E` is complex
differentiable on `π '' DR`.

The principal branch of `log` is not holomorphic on the negative real axis, so we must not
differentiate `log ζ` itself.  Instead, for a base point `ζ₀ = π w₀` we use the *local* lift
`γ ζ = w₀ + log(ζ / π w₀)/(2πi)`, which is holomorphic at `ζ₀` (because `ζ₀/(π w₀) = 1` lies in
the slit plane), is a lift of `ζ` (`π (γ ζ) = ζ`), and differs from the principal lift `log ζ/(2πi)`
by an integer.  Since `DR` is `ℤ`-invariant, `γ` maps `π '' DR` into `DR`; and since `π` has period
`1`, `pushdown E = π ∘ E ∘ γ` on `π '' DR`.  The chain rule for `DifferentiableWithinAt` (applied
with the domain set `π '' DR` for the inner map `γ` and `DR` for `E`) then gives holomorphy.

The `ℤ`-bookkeeping (`π u = π v ↔ ∃ k, u = v + k`, iteration of equivariance) is taken from
`Submission/Work/Horn/basic.lean`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open Work.Horn.MandelDim

noncomputable section

namespace PushdownHolo

lemma differentiable_piExp : Differentiable ℂ piExp := by
  intro w
  unfold piExp
  fun_prop

/-- `π(a + b) = π a · π b`. -/
lemma piExp_mul (a b : ℂ) : piExp (a + b) = piExp a * piExp b := by
  rw [piExp, piExp, piExp, ← Complex.exp_add]
  congr 1
  ring

/-- The local lift `γ ζ = w₀ + log(ζ/π w₀)/(2πi)` really is a lift: `π (γ ζ) = ζ`. -/
lemma piExp_gamma_lift (w₀ ζ : ℂ) (hζ : ζ ≠ 0) :
    piExp (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I)) = ζ := by
  rw [piExp_mul, piExp_log_div (ζ / piExp w₀) (div_ne_zero hζ (piExp_ne_zero w₀))]
  exact mul_div_cancel₀ ζ (piExp_ne_zero w₀)

/-- `γ ζ` differs from the principal lift `log ζ/(2πi)` by an integer. -/
lemma gamma_lift_sub_int (w₀ ζ : ℂ) (hζ : ζ ≠ 0) :
    ∃ n : ℤ, w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I) =
      Complex.log ζ / (2 * Real.pi * I) + n := by
  have hpi : piExp (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))
      = piExp (Complex.log ζ / (2 * Real.pi * I)) := by
    rw [piExp_gamma_lift w₀ ζ hζ, piExp_log_div ζ hζ]
  exact piExp_eq_iff.mp hpi

/-- The principal lift of a point `ζ = π w` of `π '' DR` lies in `DR` (`DR` is `ℤ`-invariant). -/
lemma log_div_mem_of_piExp {DR : Set ℂ} (hD : IsTInvariant DR) {w ζ : ℂ} (hw : w ∈ DR)
    (hwζ : piExp w = ζ) : Complex.log ζ / (2 * Real.pi * I) ∈ DR := by
  have hζ : ζ ≠ 0 := by rw [← hwζ]; exact piExp_ne_zero w
  have hpi : piExp (Complex.log ζ / (2 * Real.pi * I)) = piExp w := by
    rw [piExp_log_div ζ hζ, hwζ]
  obtain ⟨k, hk⟩ := piExp_eq_iff.mp hpi
  rw [hk]
  exact IsTInvariant.add_int hD hw k

end PushdownHolo

open PushdownHolo

theorem pushdown_holo {E : ℂ → ℂ} {DR : Set ℂ}
    (heq : IsTEquivariantOn E DR) (hdiff : DifferentiableOn ℂ E DR) :
    DifferentiableOn ℂ (pushdown E) (piExp '' DR) := by
  intro ζ₀ hζ₀
  have hζ₀mem : ζ₀ ∈ piExp '' DR := hζ₀
  obtain ⟨w₀, hw₀, hζ₀w⟩ := hζ₀mem
  have hD : IsTInvariant DR := heq.1
  have hE : ∀ w ∈ DR, w + 1 ∈ DR → E (w + 1) = E w + 1 := fun w hw _ => heq.2 w hw
  have hζ₀ne : ζ₀ ≠ 0 := by rw [← hζ₀w]; exact piExp_ne_zero w₀
  -- the local lift is holomorphic at `ζ₀`
  have hγdiff : DifferentiableAt ℂ
      (fun ζ => w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I)) ζ₀ := by
    have hz : ζ₀ / piExp w₀ ∈ Complex.slitPlane := by
      rw [show ζ₀ / piExp w₀ = 1 by rw [← hζ₀w]; exact div_self (piExp_ne_zero w₀)]
      exact Complex.one_mem_slitPlane
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (ζ / piExp w₀)) ζ₀ :=
      (differentiableAt_id.div_const (piExp w₀)).clog hz
    exact (h1.div_const (2 * Real.pi * I)).const_add w₀
  -- the local lift maps `π '' DR` into `DR`
  have hmaps : MapsTo (fun ζ => w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))
      (piExp '' DR) DR := by
    intro ζ hζ
    obtain ⟨w, hw, hwζ⟩ := hζ
    have hζne : ζ ≠ 0 := by rw [← hwζ]; exact piExp_ne_zero w
    have hL : Complex.log ζ / (2 * Real.pi * I) ∈ DR := log_div_mem_of_piExp hD hw hwζ
    obtain ⟨n, hn⟩ := gamma_lift_sub_int w₀ ζ hζne
    have hmem : w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I) ∈ DR := by
      rw [hn]
      exact IsTInvariant.add_int hD hL n
    exact hmem
  -- `pushdown E = π ∘ E ∘ γ` on `π '' DR`
  have hpush : ∀ ζ ∈ piExp '' DR, pushdown E ζ
      = piExp (E (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))) := by
    intro ζ hζ
    obtain ⟨w, hw, hwζ⟩ := hζ
    have hζne : ζ ≠ 0 := by rw [← hwζ]; exact piExp_ne_zero w
    have hL : Complex.log ζ / (2 * Real.pi * I) ∈ DR := log_div_mem_of_piExp hD hw hwζ
    obtain ⟨n, hn⟩ := gamma_lift_sub_int w₀ ζ hζne
    rw [pushdown_of_ne E hζne]
    have hEn : E (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))
        = E (Complex.log ζ / (2 * Real.pi * I)) + n := by
      rw [hn, E_add_int hD hE hL n]
    rw [hEn, piExp_add_intCast]
  -- chain rule
  have hEL : DifferentiableWithinAt ℂ
      (fun ζ => E (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))) (piExp '' DR) ζ₀ :=
    DifferentiableWithinAt.comp ζ₀ (hdiff _ (hmaps hζ₀))
      hγdiff.differentiableWithinAt hmaps
  have hpi : DifferentiableWithinAt ℂ piExp Set.univ
      (E (w₀ + Complex.log (ζ₀ / piExp w₀) / (2 * Real.pi * I))) :=
    (differentiable_piExp _).differentiableWithinAt
  have hfin : DifferentiableWithinAt ℂ
      (fun ζ => piExp (E (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I))))
      (piExp '' DR) ζ₀ :=
    DifferentiableWithinAt.comp
      (f := fun ζ => E (w₀ + Complex.log (ζ / piExp w₀) / (2 * Real.pi * I)))
      (g := piExp) ζ₀ hpi hEL (Set.mapsTo_univ _ _)
  exact hfin.congr hpush (hpush ζ₀ hζ₀)

end

end Work.Repel
