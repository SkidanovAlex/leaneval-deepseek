import Mathlib
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.HasLoj.polar_count_deformed
import Submission.Work.WilE3.Taylor.Grad.branchPointsAtLevel
import Submission.Work.WilE3.Taylor.Grad.polarPointsAtLevel
import Submission.Work.WilE3.Taylor.Grad.polarSys_eval_toC_eq_zero

/-!
  annals_wilkies_conjecture, AREA E3: the polar exponent bound along a *good* level of a polar
  branch (Gabrielov 1995, Theorem 3.1/3.3, the "Case A" of the polar-curve argument).

  ## The statement

  `Work.WilE3.Taylor.Grad.polarCount_goodLevel` is the third (and last) step of the route to
  Gabrielov's effective gradient inequality that is *not* delegated:

  > along a real analytic arc `γ` through `y = γ 0` which satisfies the gradient-polar system of
  > `Φ` with pivot `i₀` (the minors `gpolMinor c Φ i₀ i`, `i ≠ i₀`, vanish along `γ`) and along
  > which `Φ ∘ γ` vanishes to order `m > 0` while `γ - y` ramifies of order `a > 0`, the ratio
  > `m / a` is bounded by a polynomial `K.eval (atomDeg Φ)` in the atom degree of `Φ` alone —
  > *provided* the Jacobian determinant of the `k × k` polar system does not vanish identically
  > along `γ` (the "good level" hypothesis, which excludes the tangentially degenerate branch).

  ## The proof (this file assembles three proved inputs)

  Let `Q i := polarSys c Φ i₀ i` (row `i₀` is `Φ`, the other rows the gradient-polar minors) and
  let `P := Q`.  The complexification of the polar branch carries points of the level sets of the
  (deformed) polar system:

  1. `Work.WilE3.Taylor.Grad.polarPointsAtLevel` (delegated, proved): there are a level-point
     function `S : ℂ → Finset (Fin k → ℂ)` and a radius function `ρ ε → 0` such that for all small
     complex `ε ≠ 0` the set `S ε` consists of points of `{Φ = ε}` at which also the minors vanish
     and *at which the Jacobian of the polar system is invertible*, all within distance `ρ ε` of
     `toC y`, and with `m ≤ a * card (S ε)`.  (`m ≤ a * card` is the ramification bound: the
     complexified arc is `a`-to-one and the `m` simple solutions of `G = ε` on it distribute over
     its image; the nondegeneracy is where the "good level" hypothesis `hdet` enters, through the
     fact that the analytic germ `s ↦ det (∇Q) (σ s)` is not identically zero along the branch.)

  2. `Work.WilE3.Taylor.HasLoj.polar_count_deformed` (proved, from `MultiplicityBound`): for every
     radius function `ρ ε → 0` the number of *nondegenerate* zeros of the deformed polar system
     `Φ - ε`, `gpolMinor …` inside the `ρ ε`-ball around a zero `x` of the undeformed system is
     eventually bounded by `M.eval (atomDeg Φ)`, a polynomial in the atom degree of `Φ` alone.

  3. `Work.WilE3.Taylor.Grad.polarSys_eval_toC_eq_zero` (delegated, proved): the base point `toC y`
     is a zero of the undeformed polar system (the pivot row because `ord₀ (Φ ∘ γ) = m > 0` forces
     `Φ y = 0`, the other rows by continuity from `hminors`).

  Combining: the `S ε` are nondegenerate zeros of the deformed system inside the `ρ ε`-ball of the
  zero `toC y`, so `card (S ε) ≤ M.eval (atomDeg Φ)` for the fixed level `ε = min δ₁ δ₂ / 2` at
  which both "eventually" statements hold; hence `m ≤ a * M.eval (atomDeg Φ)`, and the polynomial
  `K := M` works.  -/

namespace Work.WilE3.Taylor.Grad

open Filter Topology
open scoped Topology

/-- **The polar exponent bound along a good level.**  Let `γ` be a real analytic arc with
`γ 0 = y`, `ord₀ (γ - y) = a > 0` and `ord₀ (Φ ∘ γ) = m > 0`; suppose that along `γ` (for small
positive `t`) all the gradient-polar minors of `Φ` with pivot `i₀` vanish, and that the Jacobian
determinant of the polar system `(Φ, gpolMinor c Φ i₀ i)` does *not* vanish identically along `γ`.
Then `m ≤ a * K.eval (atomDeg Φ)` for a polynomial `K` depending only on the format bound `F`.

See the module docstring for the route: the level sets of the deformed polar system carry
`m / a` nondegenerate points near `y` (`polarPointsAtLevel`), and their number is bounded by
`MultiplicityBound` (`polar_count_deformed`). -/
theorem polarCount_goodLevel (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ)
      (m a : ℕ) (i₀ : Fin k),
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
      analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t) = 0) →
      (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c
          (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (γ t)).det = 0) →
      m ≤ a * K.eval (WilkiesDesign.E.atomDeg Φ) := by
  obtain ⟨M, hM⟩ := Work.WilE3.Taylor.HasLoj.polar_count_deformed hMB F
  refine ⟨M, ?_⟩
  intro k r c Φ y γ m a i₀ hkr hγ hγ0 ha hm hram hord hminors hdet
  -- The arc is not eventually constant: `Φ ∘ γ` has finite nonzero order `m`, whereas an arc
  -- which is eventually constantly `y` would give `Φ ∘ γ =ᶠ 0` (as `ord₀ (Φ ∘ γ) = m > 0` forces
  -- `Φ y = 0`) and hence order `⊤`.
  have hne : ¬ (γ =ᶠ[nhds (0 : ℝ)] fun _ => y) := by
    intro hconst
    have hΦy : WilkiesDesign.E.eaEval c Φ y = 0 := by
      have h1 : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 ≠ 0 := by
        rw [hord]; exact_mod_cast hm.ne'
      have h2 := apply_eq_zero_of_analyticOrderAt_ne_zero
        (f := fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) (z₀ := (0 : ℝ)) h1
      simpa [hγ0] using h2
    have hev : (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hconst] with t ht
      rw [ht, hΦy]
    have htop : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = ⊤ :=
      analyticOrderAt_eq_top.mpr hev
    rw [hord] at htop
    exact ENat.natCast_ne_top m htop
  -- The level points of the polar branch together with their shrinking radius.
  obtain ⟨S, ρ, hρpos, hρtend, hS⟩ :=
    polarPointsAtLevel c Φ y γ i₀ hγ hγ0 ha hm hram hord hne hminors hdet
  -- The base point `toC y` is a zero of the (undeformed) polar system.
  have hPx : ∀ i : Fin k,
      Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i)
        (Work.WilE3.Frame.toC y) = 0 :=
    polarSys_eval_toC_eq_zero c Φ y γ i₀ hγ hγ0 hm hord hminors
  -- Degree bookkeeping: every row of the polar system has atom degree `≤ 3 * atomDeg Φ + 3`.
  have hdeg : ∀ i : Fin k, WilkiesDesign.E.atomDeg (Work.WilE3.Taylor.polarSys c Φ i₀ i)
      ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3 :=
    fun i => Work.WilE3.Taylor.atomDeg_polarSys_le c Φ i₀ i
  -- The multiplicity bound for the polar system, deformed by `-ε` in the pivot row.
  have hcount := hM k r c Φ (Work.WilE3.Taylor.polarSys c Φ i₀) i₀
    (Work.WilE3.Frame.toC y) hkr hPx hdeg ρ hρpos hρtend
  -- Both statements are "eventually in `ε ≠ 0`"; make the thresholds explicit.
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hcount hS
  obtain ⟨δ₁, hδ₁, hc₁⟩ := hcount
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hS
  -- A level at which both hold.
  set ε : ℂ := (((min δ₁ δ₂) / 2 : ℝ) : ℂ) with hεdef
  have hεnorm : ‖ε‖ = min δ₁ δ₂ / 2 := by
    rw [hεdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hεpos : 0 < ‖ε‖ := by rw [hεnorm]; positivity
  have hε0 : ε ≠ 0 := norm_pos_iff.mp hεpos
  have hεmem : ε ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hε0
  have hεδ₁ : dist ε 0 < δ₁ := by
    rw [dist_zero_right, hεnorm]; have := min_le_left δ₁ δ₂; linarith
  have hεδ₂ : dist ε 0 < δ₂ := by
    rw [dist_zero_right, hεnorm]; have := min_le_right δ₁ δ₂; linarith
  have hSε := hc₂ (y := ε) hεδ₂ hεmem
  have hcard : (S ε).card ≤ M.eval (WilkiesDesign.E.atomDeg Φ) :=
    hc₁ (y := ε) hεδ₁ hεmem (S ε) ?_ ?_
  · calc m ≤ a * (S ε).card := hSε.2.2.2.1
      _ ≤ a * M.eval (WilkiesDesign.E.atomDeg Φ) := Nat.mul_le_mul_left a hcard
  · -- The points of `S ε` are nondegenerate zeros of the deformed polar system.
    intro z hz
    refine ⟨fun i => ?_, hSε.2.2.1 z hz⟩
    by_cases hi : i = i₀
    · -- pivot row: `Φ z = ε`
      have hpol : Work.WilE3.Taylor.polarSys c Φ i₀ i = Φ := by
        simp [Work.WilE3.Taylor.polarSys, hi]
      have hzε := hSε.1 z hz
      rw [hpol, hzε, ite_eq_left hi]
      ring
    · -- other rows: the minors vanish
      rw [ite_eq_right hi, mul_zero, add_zero]
      exact hSε.2.1 z hz i hi
  · -- `S ε` lies in the `ρ ε`-ball around the base point.
    intro z hz
    exact hSε.2.2.2.2 z hz

end Work.WilE3.Taylor.Grad
