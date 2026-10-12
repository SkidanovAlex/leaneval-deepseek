import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.slotExact_orth_gen` — the sector pairing identity for two different states

`slotExact_orth` (`fibre_decomposition.lean`) proves

`∫ x, star (slotExact e S Φ x) * slotExact e S' Φ x =
   if S = S' then ∫ x, star (Φ x) * slotExact e S Φ x else 0`

for a *continuous compactly supported* `Φ`.  The present file generalises the second argument to an
arbitrary **measurable bounded** state `Ψ`:

`∫ x, star (slotExact e S Φ x) * slotExact e S' Ψ x =
   if S = S' then ∫ x, star (Φ x) * slotExact e S Ψ x else 0`,

which is the form the box ↔ model bridge needs (the second factor is a model state, not an honest
box state).

The proof has two steps.

* **`slotExact_adjoint_meas`** — self-adjointness of the sector `slotExact e S` with a merely
  measurable bounded second argument.  The sector is the finite combination
  `∑_{T ⊇ S} (-1)^{|T|−|S|} slotProj e T`, and each slot projection is self-adjoint for a bounded
  measurable second factor (`slotProj_adjoint_meas`); the finite sum is pulled out of the integral
  with `integral_star_sum_mul` (the compact support of the *first* factor carries the
  integrability), and folded back with `integral_mul_sum`.
* the composition law `slotExact e S (slotExact e S' Ψ) = if S = S' then slotExact e S Ψ else 0`
  (`slotExact_comp`, available for a measurable bounded state) applied inside the integral.
-/

/-- **Self-adjointness of the `S`-sector for a measurable bounded second argument.**  The first
state `Φ` is continuous with compact support (that is what makes the integrals absolutely
convergent), the second only measurable and bounded. -/
theorem slotExact_adjoint_meas {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (Ψ : (Fin n → Ω) → ℂ) (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    ∫ x, star (slotExact e S Φ x) * Ψ x = ∫ x, star (Φ x) * slotExact e S Ψ x := by
  classical
  set sS : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T) with hsS
  set cP : Finset (Fin n) → ℂ := fun T => (-1 : ℂ) ^ (T.card - S.card) with hcP
  have hconj : ∀ k : ℕ, star ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
    intro k
    rw [Complex.star_def, map_pow]
    simp
  -- the sector `S` is the sum of the slot projections over the supersets of `S`
  have hE : ∀ Θ : (Fin n → Ω) → ℂ, ∀ x : Fin n → Ω,
      slotExact e S Θ x = ∑ T ∈ sS, cP T * slotProj e T Θ x := by
    intro Θ x
    simp only [slotExact, hsS, hcP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hPm : ∀ T : Finset (Fin n), Measurable (fun x => cP T * slotProj e T Φ x) := fun T =>
    (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).1.const_smul (cP T)
  have hPb : ∀ T : Finset (Fin n), ∃ C, ∀ x, ‖cP T * slotProj e T Φ x‖ ≤ C := fun T => by
    obtain ⟨C, hC⟩ := (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.1
    exact ⟨‖cP T‖ * C, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
  have hPc : ∀ T : Finset (Fin n), HasCompactSupport (fun x => cP T * slotProj e T Φ x) := fun T =>
    (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.2.smul_left
      (f := fun _ => cP T)
  have hQm : ∀ T : Finset (Fin n), Measurable (fun x => cP T * slotProj e T Ψ x) := fun T =>
    (sx_proj_mb e he hec T Ψ hΨm hΨb).1.const_smul (cP T)
  have hQb : ∀ T : Finset (Fin n), ∃ C, ∀ x, ‖cP T * slotProj e T Ψ x‖ ≤ C := fun T => by
    obtain ⟨C, hC⟩ := (sx_proj_mb e he hec T Ψ hΨm hΨb).2
    exact ⟨‖cP T‖ * C, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
  -- step 1: expand the left factor and pull out the coefficients
  have h1 : ∫ x, star (slotExact e S Φ x) * Ψ x
      = ∑ T ∈ sS, cP T * ∫ x, star (slotProj e T Φ x) * Ψ x := by
    have hpt : ∀ x : Fin n → Ω,
        star (slotExact e S Φ x) * Ψ x
          = star (∑ T ∈ sS, cP T * slotProj e T Φ x) * Ψ x := by
      intro x
      rw [hE Φ x, star_sum]
    rw [show (∫ x, star (slotExact e S Φ x) * Ψ x)
        = ∫ x, star (∑ T ∈ sS, cP T * slotProj e T Φ x) * Ψ x from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul sS (fun T x => cP T * slotProj e T Φ x) Ψ
      hPc hPm hPb hΨm hΨb]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [show (fun x => star (cP T * slotProj e T Φ x) * Ψ x)
        = fun x => cP T * (star (slotProj e T Φ x) * Ψ x) from by
      funext x
      rw [star_mul, hconj]
      ring]
    rw [integral_const_mul]
  -- step 2: self-adjointness of `slotProj` for the bounded measurable `Ψ`
  have h2 : ∑ T ∈ sS, cP T * ∫ x, star (slotProj e T Φ x) * Ψ x
      = ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * slotProj e T Ψ x) := by
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [slotProj_adjoint_meas e he hec horth T Φ Ψ hΦ hΦc hΨm hΨb]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- step 3: fold the sum back
  have h3 : ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * slotProj e T Ψ x)
      = ∫ x, star (Φ x) * slotExact e S Ψ x := by
    have hpt : ∀ x : Fin n → Ω, star (Φ x) * slotExact e S Ψ x
        = star (Φ x) * (∑ T ∈ sS, cP T * slotProj e T Ψ x) := by
      intro x
      rw [hE Ψ x]
    rw [show (∫ x, star (Φ x) * slotExact e S Ψ x)
        = ∫ x, star (Φ x) * (∑ T ∈ sS, cP T * slotProj e T Ψ x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [← integral_mul_sum sS (fun T x => cP T * slotProj e T Ψ x)
      (fun x => star (Φ x))
      (hΦc.comp_left (g := star) (by simp)) (measurable_star_comp hΦ.measurable)
      (hΦ.bounded_above_of_compact_support hΦc |>.imp (fun C hC x => by
        rw [norm_star]; exact hC x))
      hQm hQb]
  rw [h1, h2, h3]

theorem slotExact_orth_gen {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Work.BoseBoxFock.slotExact e S' Ψ x
      = if S = S' then ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x else 0 := by
  classical
  obtain ⟨hQm, hQb⟩ := sx_exact_mb e he hec S' Ψ hΨm hΨb
  have hA : ∫ x, star (slotExact e S Φ x) * slotExact e S' Ψ x
      = ∫ x, star (Φ x) * slotExact e S (slotExact e S' Ψ) x :=
    slotExact_adjoint_meas e he hec horth S Φ hΦ hΦc (slotExact e S' Ψ) hQm hQb
  have hcomp := slotExact_comp e he hec horth S S' Ψ hΨm hΨb
  rw [hA]
  by_cases h : S = S'
  · rw [if_pos h]
    have hfun :
        (fun x : Fin n → Ω => star (Φ x) * slotExact e S (slotExact e S' Ψ) x)
          = fun x : Fin n → Ω => star (Φ x) * slotExact e S Ψ x := by
      funext x
      simp only [congrFun hcomp x, if_pos h]
    rw [hfun]
  · rw [if_neg h]
    have hfun :
        (fun x : Fin n → Ω => star (Φ x) * slotExact e S (slotExact e S' Ψ) x)
          = fun x : Fin n → Ω => star (Φ x) * (0 : ℂ) := by
      funext x
      rw [congrFun hcomp x, if_neg h]
      simp
    rw [hfun]
    simp

end Work.BoseBoxFock
