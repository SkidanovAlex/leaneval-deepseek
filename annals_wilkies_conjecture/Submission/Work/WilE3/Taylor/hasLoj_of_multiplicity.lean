import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.HasLoj.Reductions
import Submission.Work.WilE3.Taylor.HasLoj.Assembly
import Submission.Work.WilE3.Taylor.HasLoj.Elementary
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.Grad.hinge
import Submission.Work.WilE3.Taylor.Grad.CruxGap
import Submission.Work.WilE3.Taylor.CaseII.GenGrad
import Submission.Work.Taylor.Grad.polar_goodLevel_sharp
import Submission.Work.WilE3.eaEval_analytic

/-!
  annals_wilkies_conjecture, AREA E3: the target lemma `Work.WilE3.Taylor.hasLoj_of_multiplicity`.

  ## THE ARGUMENT IS COMPLETE (SESSION 17)

  The chain of implications is

  ```
  target `hasLoj_of_multiplicity`  <=  (SINGLE) `hasLoj_single`
     <=  (GRAD) `ea_grad_of_multiplicity`  <=  `Work.WilE3.Taylor.CaseII.ea_grad_of_multiplicity'`
         (node T5 of `sources/wilkiesE3caseII/wilkies_e3_caseII.md` §3, SESSION 17)
     <=  { `CaseII.Gen.squareSystem_deficit`   (node T2′, generalised Case A, proved),
           `CaseII.badArc_fixedBall`           (node T3, Step A/B with a fixed ball, proved),
           `CaseII.atomDeg_pertSys_le`, `CaseII.atomDeg_sphSys_le`   (node T2d, proved),
           `CaseII.pertSys_det_ne`, `CaseII.sphSys_det_ne`           (node T4, proved),
           `CaseII.exists_pos_of_ae_prod`      (the `d > 0` extraction, proved) },
  ```

  with the *mathematical core* `Work.WilE3.Taylor.CaseII.badArc_contradiction` (SESSION 17): a bad
  arc lying on one of the nondegenerate square systems `pertSys`/`sphSys` contradicts the
  generalised Case A count by the hinge's arithmetic `(K.eval (atomDeg Q) + 1)·n ≤ K.eval (atomDeg Q)·m`
  versus `(K.eval (atomDeg Φ) + 1)·m ≤ (K.eval (atomDeg Φ) + 2)·n` for a smaller `Q`.

  The **replacement route** of the project lead bypasses the earlier arc crux altogether: the legacy
  declarations kept in this file (`CaseA`, `ea_arcCrux_gap`, `ea_arcCrux`) and the hinge
  `Grad.ea_grad_of_arcCrux` are no longer used, and the former gap
  `Work.WilE3.Taylor.arcDeficitBound` (`Grad/CruxGap.lean`) is now *proved* from (GRAD) by
  `Work.WilE3.Taylor.Grad.arcCrux_of_grad` (the converse of the hinge).

  `#print axioms Work.WilE3.Taylor.hasLoj_of_multiplicity` = `propext, Classical.choice, Quot.sound`.

  See `NOTES_hasLoj_of_multiplicity.md` §17 for the full record of the final assembly, and §16 for
  the lead's design and the statement-level lessons of the earlier attempts.

  This file was split (SESSION 8) into `HasLoj/Elementary.lean`, `Grad/PolarDefs.lean` and
  `Grad/CruxGap.lean` to satisfy the workspace build guard (≤ 30 KB per module).
-/

namespace Work.WilE3.Taylor

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-- **The Case-A data** of the arc crux: the polar minors for the pivot `i₀` vanish along `γ` and
the Jacobian determinant of the polar system does *not* vanish identically along `γ`. -/
def CaseA (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ)
    (i₀ : Fin k) : Prop :=
  (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
      eaEval c (polarSys c Φ i₀ i) (γ t) = 0) ∧
    ¬ (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (Matrix.of fun i j =>
        eaEval c (eaD c j (polarSys c Φ i₀ i)) (γ t)).det = 0)

/-- **The arc crux for arcs to which Case A does not apply.**

For every format bound there is `K` such that every arc `γ` through `y` in the gradient-polar locus
`PolarLike`, with `m = ord₀ (Φ ∘ γ) > 0`, for which **no** pivot `i₀` exhibits the Case-A data
(i.e. either the polar minors for `i₀` do not vanish along `γ`, or the polar Jacobian determinant
vanishes identically along `γ`), has some partial `∂ᵢΦ` whose order `n` along `γ` satisfies
`n/m ≤ K.eval (atomDeg Φ)/(K.eval (atomDeg Φ) + 1)`.

This is *proved* here from the denominator bound `Work.WilE3.Taylor.ea_arcCrux_denomBound`
(together with the arithmetic `Work.WilE3.Taylor.arith_denom`): the gap lemma supplies the partial
`∂ᵢΦ` of finite order `n < m` whose reduced exponent denominator `m / gcd (2n) m` is at most
`Q.eval (atomDeg Φ)`, and the arithmetic converts that into `(2Q+1)·n ≤ 2Q·m`. -/
theorem ea_arcCrux_gap (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (m : ℕ),
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < m →
      analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 = m →
      Work.WilE3.Taylor.Grad.PolarLike c Φ y γ →
      (∀ i₀ : Fin k, ¬ CaseA c Φ y γ i₀) →
      ∃ (i : Fin k) (n : ℕ),
        analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Φ) (γ t)) 0 = n ∧
          (K.eval (atomDeg Φ) + 1) * n ≤ K.eval (atomDeg Φ) * m := by
  intro F
  obtain ⟨K, hK⟩ := arcDeficitBound hMB F
  refine ⟨K, ?_⟩
  intro k r c Φ y γ m hkr hγ hγ0 hm hord hPL _
  exact hK k r c Φ y γ m hkr hγ hγ0 hm hord hPL

/-- **The sharp arc crux `ArcCrux`, assembled from Case A (proved) and the gap `ea_arcCrux_gap`.**

The arc is either in Case A for some pivot `i₀` — and then
`Work.Taylor.Grad.polar_goodLevel_sharp` (the counting argument of
`Work.WilE3.Taylor.Grad.polarCount_goodLevel` together with `Work.WilE3.Taylor.Grad.gradOrderLe`)
gives the bound — or it is not for any pivot, and then the gap applies.  In the first case the
polynomials are combined by addition using `n ≤ m` (which the sharp Case-A bound itself gives). -/
theorem ea_arcCrux (hMB : Work.WilE3.MultiplicityBound) :
    Work.WilE3.Taylor.Grad.ArcCrux := by
  intro F
  obtain ⟨K₁, h₁⟩ := Work.Taylor.Grad.polar_goodLevel_sharp hMB F
  obtain ⟨K₂, h₂⟩ := ea_arcCrux_gap hMB F
  refine ⟨K₁ + K₂, ?_⟩
  intro k r c Φ y γ m hkr hγ hγ0 hm hord hPL
  by_cases hA : ∃ i₀ : Fin k, CaseA c Φ y γ i₀
  · obtain ⟨i₀, hminors, hdet⟩ := hA
    -- `Φ y = 0` and the ramification order of `γ`
    have hΦy : eaEval c Φ y = 0 := by
      have h1 : analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 ≠ 0 := by
        rw [hord]; exact_mod_cast hm.ne'
      have h2 := apply_eq_zero_of_analyticOrderAt_ne_zero h1
      simpa [hγ0] using h2
    have hne : ¬ (γ =ᶠ[𝓝 (0 : ℝ)] fun _ => y) := by
      intro hconst
      have htop : analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 = ⊤ := by
        rw [analyticOrderAt_eq_top]
        filter_upwards [hconst] with t ht
        rw [ht, hΦy]
      rw [hord] at htop
      exact absurd htop (ENat.natCast_ne_top m)
    have ha_exists : ∃ a : ℕ, 0 < a ∧ analyticOrderAt (fun t : ℝ => γ t - y) 0 = a := by
      have hsub : AnalyticAt ℝ (fun t : ℝ => γ t - y) 0 := hγ.sub analyticAt_const
      have hne_top : analyticOrderAt (fun t : ℝ => γ t - y) 0 ≠ ⊤ := by
        intro htop
        rw [analyticOrderAt_eq_top] at htop
        exact hne (by filter_upwards [htop] with t ht; exact sub_eq_zero.mp ht)
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne_top
      refine ⟨a, ?_, ha.symm⟩
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · exfalso
        have hz : analyticOrderAt (fun t : ℝ => γ t - y) 0 = 0 := by rw [← ha, h0]; rfl
        rw [analyticOrderAt_eq_zero] at hz
        rcases hz with h | h
        · exact h hsub
        · exact h (by simp [hγ0])
      · exact hpos
    obtain ⟨a, ha_pos, hram⟩ := ha_exists
    obtain ⟨i, n, hn, hb⟩ :=
      h₁ k r c Φ y γ m a i₀ hkr hγ hγ0 ha_pos hm hram hord hminors hdet
    refine ⟨i, n, hn, ?_⟩
    have hnm : n ≤ m := by
      have h2 : (K₁.eval (atomDeg Φ) + 1) * n ≤ (K₁.eval (atomDeg Φ) + 1) * m :=
        le_trans hb (Nat.mul_le_mul_right m (Nat.le_succ _))
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    rw [Polynomial.eval_add]
    have e1 : (K₁.eval (atomDeg Φ) + K₂.eval (atomDeg Φ) + 1) * n
        = (K₁.eval (atomDeg Φ) + 1) * n + K₂.eval (atomDeg Φ) * n := by ring
    have e2 : (K₁.eval (atomDeg Φ) + K₂.eval (atomDeg Φ)) * m
        = K₁.eval (atomDeg Φ) * m + K₂.eval (atomDeg Φ) * m := by ring
    rw [e1, e2]
    exact Nat.add_le_add hb (Nat.mul_le_mul_left _ hnm)
  · obtain ⟨i, n, hn, hb⟩ := h₂ k r c Φ y γ m hkr hγ hγ0 hm hord hPL
      (fun i₀ hi₀ => hA ⟨i₀, hi₀⟩)
    refine ⟨i, n, hn, ?_⟩
    have hnm : n ≤ m := by
      have h2 : (K₂.eval (atomDeg Φ) + 1) * n ≤ (K₂.eval (atomDeg Φ) + 1) * m :=
        le_trans hb (Nat.mul_le_mul_right m (Nat.le_succ _))
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    rw [Polynomial.eval_add]
    have e1 : (K₁.eval (atomDeg Φ) + K₂.eval (atomDeg Φ) + 1) * n
        = K₁.eval (atomDeg Φ) * n + (K₂.eval (atomDeg Φ) + 1) * n := by ring
    have e2 : (K₁.eval (atomDeg Φ) + K₂.eval (atomDeg Φ)) * m
        = K₁.eval (atomDeg Φ) * m + K₂.eval (atomDeg Φ) * m := by ring
    rw [e1, e2]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hnm) hb

/-- **The effective gradient inequality for EA functions** (Gabrielov 1995, Theorem 3.3), from
`MultiplicityBound`, deduced from the arc crux `ea_arcCrux` by the (proved) hinge
`Work.WilE3.Taylor.Grad.ea_grad_of_arcCrux`.

The hypothesis `eaEval c Φ y = 0` is *necessary*: for `Φ` with `Φ y ≠ 0` and `∇Φ y = 0`
(e.g. `Φ = 1 + x²`, `y = 0`) no `κ ∈ [0,1)`, `c > 0` can satisfy `c |Φ|^κ ≤ ‖∇Φ‖` near `y`.  In
`(SINGLE)` this case is handled separately by `Work.WilE3.Taylor.hasLoj_of_pos` (the zero set is
empty near `y`).

**(SESSION 17)** The proof is now the *replacement route* of
`sources/wilkiesE3caseII/wilkies_e3_caseII.md` §3 (`Work.WilE3.Taylor.CaseII.GenGrad`), which
bypasses the arc crux `ArcCrux`, the hinge and `CruxGap.arcDeficitBound` altogether: the bad arcs are
placed on the nondegenerate square systems `pertSys`/`sphSys` (perturbed squared gradient), where the
generalised Case A count `Work.WilE3.Taylor.CaseII.Gen.squareSystem_deficit` applies. -/
theorem ea_grad_of_multiplicity (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
        (y : Fin k → ℝ), k + r ≤ F → eaEval c Φ y = 0 →
        ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧
          1 / (1 - κ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) ∧
          (∀ᶠ x in 𝓝 y, cst * |eaEval c Φ x| ^ κ ≤
            ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x‖) :=
  CaseII.ea_grad_of_multiplicity' hMB

/-- **(SINGLE): the single-EA-polynomial Łojasiewicz inequality.**  For every format bound `F`
there is a polynomial `K` such that for every EA chain `c` and EA polynomial `Φ` of format `≤ F`,
every base point `y` and every exponent `q` above `K.eval (atomDeg Φ)`, the function `|eaEval c Φ|`
dominates `infDist (·, {Φ = 0})^q` near `y`.

This is Gabrielov 1995, Theorem 3.4 in the single-function form, and — by
`Work.WilE3.Taylor.hasLoj_of_single` and `hasLoj_sq` — it is the whole remaining content of the
target `hasLoj_of_multiplicity` (it is equivalent to the `Φ ≥ 0` statement with `Φ y = 0`). -/
theorem hasLoj_single (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval (atomDeg Φ) < q →
      Work.WilE3.HasLoj (fun x => |eaEval c Φ x|) {x | eaEval c Φ x = 0} y q := by
  intro F
  obtain ⟨K, hK⟩ := ea_grad_of_multiplicity hMB F
  refine ⟨K, ?_⟩
  intro k r c Φ y q hkr hKq
  by_cases hy : eaEval c Φ y = 0
  · obtain ⟨κ, cst, hκ0, hκ1, hcst, hKκ, hgr⟩ := hK k r c Φ y hkr hy
    have hC1 : ContDiff ℝ 1 (fun z : Fin k → ℝ => eaEval c Φ z) :=
      contDiff_iff_contDiffAt.mpr (fun x => (Work.WilE3.eaEval_analytic c Φ x).contDiffAt)
    have hQ : 1 / (1 - κ) ≤ (q : ℝ) := by
      have h1 : ((K.eval (atomDeg Φ) : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hKq
      linarith
    exact hasLoj_of_gradient_bound hC1 hy hcst hκ0 hκ1 hQ hgr
  · refine Work.WilE3.Taylor.hasLoj_of_pos ?_ ?_ q
    · exact (Work.WilE3.eaEval_analytic c Φ y).continuousAt.abs
    · simpa [abs_abs] using abs_pos.mpr hy

/-- **Gabrielov's effective Łojasiewicz inequality (1995, Cor. 4.4) from the multiplicity bound.**
This discharges the hypothesis `hL` of `Work.WilE3.Taylor.E3_taylor_closure_proved` from
`Work.WilE3.MultiplicityBound` (proved as `Work.WilE3.Realify.MultiplicityBound_of_ET` from the
separable-chain Khovanskii input).

For every basic EA set `B` (format `≤ F`), every point `y` and every exponent `q` above the format's
threshold the *system residual* `∑_{f ∈ B.eqs} |f|` is bounded below by a constant times
`infDist (·, Z) ^ q` near `y`, where `Z` is the common zero set of the equations — the residual form,
since the per-equation form against the common `Z` is false (`B.eqs = [X 0, X 0 - X 1]`).

Route (Gabrielov 1995, Cor. 4.4): if the inequality failed for the exponent `q`, one could build
points `x_n → y` with the residual decaying faster than `infDist ^ q`, deform the system by the
corresponding small perturbation `f + ε g` (padding with generic hyperplanes so that the system is
square), and obtain at least `q + 1` nondegenerate zeros in a ball of radius `ρ (ε) → 0`,
contradicting `MultiplicityBound` once `q` exceeds its polynomial bound. -/
theorem hasLoj_of_multiplicity (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval B.deg < q →
      Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
        {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y q := by
  exact hasLoj_of_single (hasLoj_single hMB)

end

end Work.WilE3.Taylor
