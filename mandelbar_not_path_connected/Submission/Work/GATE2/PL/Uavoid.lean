/-
# `PL/Uavoid` — avoidance of the critical values on the cut-free domains

Companion of `Submission/Work/GATE2/PL/UCore.lean`.  Here we prove that a half-step lift on the
cut-free domain `U X k = {w | X - k/2 < Re w}` avoids the critical values of `G5 c₀`:

* `eq_v_of_eq_c0_U` : such a lift `ψ` takes the value `c₀` only at `w = v` (the analogue of
  `Work.GATE2.PL.eq_v_of_eq_c0` on the slit plane);
* `ne_iterate_crit_U` : it never takes the values `T_{c₀}^[j] c₀`, `1 ≤ j ≤ 4`;
* `notMem_critVals_U` : consequently `ψ` avoids the whole critical value set `critVals`, provided
  `ψ v ≠ c₀` (the assumption `hne` of `eq_c0_of_good`).

All three are stated for the *raw* hypotheses `hanti` (the intertwining relation with `sig`) and
`hfar` (the inverse Fatou coordinate far to the right) rather than for the bundled structure
`GoodU`, since that is the form in which they are consumed by the recursion.
-/
import Mathlib
import Submission.Work.GATE2.PL.UCore
import Submission.Work.GATE2.PL.eq_v_of_eq_c0
import Submission.Work.GATE2.PL.ne_iterate_crit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

section Avoid

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)

/-- The shift relation `ψ (w + n) = F^[n] (ψ w)` on `U X k`, from the intertwining relation with
`sig` alone. -/
theorem iterate_shift_of_anti {X : ℝ} {k : ℕ} {ψ : ℂ → ℂ}
    (hanti : ∀ w ∈ U X k, G5 c₀ (ψ w) = ψ (sig w)) :
    ∀ {w : ℂ}, w ∈ U X k → ∀ n : ℕ, ψ (w + (n : ℂ)) = (Work.EL.F c₀)^[n] (ψ w) := by
  intro w hw n
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : w + (n : ℂ) ∈ U X k := by
      rw [mem_U] at hw ⊢
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    have hshift : Work.EL.F c₀ (ψ (w + (n : ℂ))) = ψ ((w + (n : ℂ)) + 1) := by
      have h2 := hanti (w + (n : ℂ)) hmem
      have h3 := hanti (sig (w + (n : ℂ))) (sig_mem_U hmem)
      calc Work.EL.F c₀ (ψ (w + (n : ℂ))) = G5 c₀ (G5 c₀ (ψ (w + (n : ℂ)))) := by
            rw [F_eq_comp_G5]; rfl
        _ = G5 c₀ (ψ (sig (w + (n : ℂ)))) := by rw [h2]
        _ = ψ (sig (sig (w + (n : ℂ)))) := h3
        _ = ψ ((w + (n : ℂ)) + 1) := by rw [sig_sig]
    rw [h1, ← hshift, ih, Function.iterate_succ_apply']

/-- **A half-step lift on `U X k` takes the value `c₀` only at `w = v`.**  (The analogue of
`Work.GATE2.PL.eq_v_of_eq_c0` for the cut-free domains.) -/
theorem eq_v_of_eq_c0_U {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ}
    (hanti : ∀ w ∈ U X k, G5 c₀ (ψ w) = ψ (sig w))
    (hfar : ∀ w : ℂ, X < w.re → ψ w ∈ FF.Pg ∧ fl.φa (ψ w) = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    {w : ℂ} (hw : w ∈ U X k) (hval : ψ w = c₀) : w = (v : ℂ) := by
  obtain ⟨n0, hn0mem, hn0φa⟩ := hv
  obtain ⟨k', hk'⟩ := exists_nat_gt (X - w.re)
  set N := max k' n0 with hNdef
  have hNge : n0 ≤ N := le_max_right _ _
  have hk'N : k' ≤ N := le_max_left _ _
  have hXN : X < (w + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have : X - w.re < (N : ℝ) := lt_of_lt_of_le hk' (by exact_mod_cast hk'N)
    linarith
  obtain ⟨hPgwN, hφawN⟩ := hfar (w + (N : ℂ)) hXN
  have hiter := iterate_shift_of_anti hanti hw N
  rw [hval] at hiter
  have hwN : fl.φa ((Work.EL.F c₀)^[N] c₀) = w + (N : ℂ) := by
    rw [← hiter]; exact hφawN
  have hcast : ((v + (N : ℝ) : ℝ) : ℂ) =
      ((v + (n0 : ℝ) : ℝ) : ℂ) + ((N - n0 : ℕ) : ℂ) := by
    have h1 : (N : ℝ) = (n0 : ℝ) + ((N - n0 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hNge]; ring
    rw [h1]; push_cast; ring
  have hvN : fl.φa ((Work.EL.F c₀)^[N] c₀) = ((v + (N : ℝ) : ℝ) : ℂ) := by
    have hiterN : (Work.EL.F c₀)^[N] c₀ =
        (Work.EL.F c₀)^[N - n0] ((Work.EL.F c₀)^[n0] c₀) := by
      have h1 : N = (N - n0) + n0 := by omega
      conv_lhs => rw [h1]
      rw [Function.iterate_add_apply]
    rw [hiterN, fatou_iterate_of_shift fl.mapsTo_Pa FF.shift (N - n0) hn0mem, hn0φa]
    exact hcast.symm
  have hkey : w + (N : ℂ) = ((v + (N : ℝ) : ℝ) : ℂ) := hwN.symm.trans hvN
  have hcast2 : ((v + (N : ℝ) : ℝ) : ℂ) = (v : ℂ) + (N : ℂ) := by push_cast; ring
  rw [hcast2] at hkey
  exact add_right_cancel hkey

/-- **A half-step lift on `U X k` never takes the values `T^[j] c₀`, `1 ≤ j ≤ 4`.**  (The analogue
of `Work.GATE2.PL.ne_iterate_crit` for the cut-free domains.) -/
theorem ne_iterate_crit_U {X : ℝ} {k : ℕ} {ψ : ℂ → ℂ}
    (hanti : ∀ w ∈ U X k, G5 c₀ (ψ w) = ψ (sig w))
    (hfar : ∀ w : ℂ, X < w.re → ψ w ∈ FF.Pg ∧ fl.φa (ψ w) = w)
    {w : ℂ} (hw : w ∈ U X k) {j : ℕ} (hj : j ∈ Finset.Ioo 0 5) :
    ψ w ≠ (Tantibar c₀)^[j] c₀ := by
  have hT : Continuous (Tantibar c₀) := by
    rw [show Tantibar c₀ = fun z : ℂ => star z ^ 2 + c₀ from rfl]
    fun_prop
  let P : Set ℂ := {z : ℂ | ∃ n : ℕ, (Work.EL.F c₀)^[n] z ∈ fl.Pa}
  have hmemP : ψ w ∈ P := by
    obtain ⟨n, hn⟩ := exists_nat_gt (X - w.re)
    refine ⟨n, ?_⟩
    have hX : X < (w + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have hfar' : ψ (w + (n : ℂ)) ∈ FF.Pg := (hfar _ hX).1
    rw [iterate_shift_of_anti hanti hw n] at hfar'
    exact FF.Pg_sub hfar'
  have hP : ∀ z ∈ P, Tendsto (fun n : ℕ => (Work.EL.F c₀)^[n] z) atTop (nhds d.z₁) := by
    intro z hz
    obtain ⟨n₀, hn₀⟩ := hz
    have h1 : Tendsto (fun n : ℕ => (Work.EL.F c₀)^[n] ((Work.EL.F c₀)^[n₀] z))
        atTop (nhds d.z₁) := fl.tendsto_Pa _ hn₀
    rw [show (fun n : ℕ => (Work.EL.F c₀)^[n] ((Work.EL.F c₀)^[n₀] z))
        = fun n : ℕ => (Work.EL.F c₀)^[n + n₀] z from by
      funext n; exact (Function.iterate_add_apply _ n n₀ z).symm] at h1
    exact (Filter.tendsto_add_atTop_iff_nat n₀).1 h1
  have hmain := iterate_ten_not_mem_of_tendsto (T := Tantibar c₀)
    (F := Work.EL.F c₀) (Work.EL.F_eq_tantibar c₀) hT (d.ne_per j hj) P hP d.crit.1
  intro hval
  exact hmain (hval ▸ hmemP)

/-- **Every half-step lift on `U X k` avoids the critical values of `G5 c₀`**, provided it does
not take the value `c₀` at `w = v` (which is the assumption `hne : Ψs v ≠ c₀` of the target
theorem, transported to the lift through uniqueness of the lift, `Work.GATE2.PL.Good_eq`). -/
theorem notMem_critVals_U {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ}
    (hanti : ∀ w ∈ U X k, G5 c₀ (ψ w) = ψ (sig w))
    (hfar : ∀ w : ℂ, X < w.re → ψ w ∈ FF.Pg ∧ fl.φa (ψ w) = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hval : (v : ℂ) ∈ U X k → ψ (v : ℂ) ≠ c₀) :
    ∀ w ∈ U X k, ψ w ∉ critVals (c₀ := c₀) := by
  intro w hw
  rintro ⟨j, hj4, hjw⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    simp only [Function.iterate_zero, id_eq] at hjw
    have hwv : w = (v : ℂ) := eq_v_of_eq_c0_U fl FF hanti hfar hv hw hjw
    have hvU : (v : ℂ) ∈ U X k := hwv ▸ hw
    exact hval hvU (by rw [← hwv]; exact hjw)
  · exact ne_iterate_crit_U fl FF hanti hfar hw (Finset.mem_Ioo.mpr ⟨hpos, by omega⟩) hjw

end Avoid

end

end Work.GATE2.PL
