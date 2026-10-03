import Mathlib
import Submission.Work.KMTAreas.A5.Setup
import Submission.Work.KMTContract.kmtProj_tendsto_truncZ

/-!
# Pointwise convergence of the minor-arc parts along the truncations

The minor-arc parts `minorArc₁`, `minorArc₂` of the halved average at a fixed scale `N`
(`Work.KMTAreas.A5.Setup`) are finite bilinear combinations of the truncated functions
`truncZ K' u`, `truncZ K' v` and of their Ionescu--Wainger projections `kmtProj ρ L K`.

Each of the two ingredients converges as `K' → ∞`:

* `truncZ K' u → u` pointwise (`Work.KMTContract.tendsto_truncZ`);
* `kmtProj ρ l k (truncZ K' u) x → kmtProj ρ l k u x` for *bounded* `u`
  (`kmtProj_tendsto_truncZ_bounded` below).  For bounded `u` the family
  `j ↦ kern j * u (x - j)` is absolutely summable, and the projections against the truncations are
  exactly its partial sums over the intervals `Icc (x - K') (x + K')`; those intervals are cofinal
  among the finite subsets of `ℤ` (`Work.KMTContract.tendsto_sum_Icc_atTop`), so the partial sums
  converge to the full series.

The target `minorArc_tendsto_truncZ` then follows from the continuity of the *finite* sums defining
`Ablock`/`AhalfR` in their two function arguments (`AhalfR_TZ_tendsto`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

/-! ## Convergence of the Ionescu--Wainger projections along the truncations -/

/-- **Pointwise convergence of the truncated IW projections for bounded inputs.**
For bounded `u` the family `j ↦ kern j * u (n - j)` is absolutely summable, and the projections
against the truncations `truncZ K' u` are exactly its partial sums over the intervals
`Icc (n - K') (n + K')`, which are cofinal among the finite subsets of `ℤ`. -/
theorem kmtProj_tendsto_truncZ_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) {u : ℤ → ℂ}
    (hu : BoundedZ u) (n : ℤ) :
    Tendsto (fun K' : ℕ => kmtProj ρ l k (truncZ K' u) n) atTop
      (nhds (kmtProj ρ l k u n)) := by
  have hg : Summable (fun j : ℤ => kmtKern ρ l k j * u (n - j)) :=
    summable_kmtKern_mul ρ l k hu n
  have hsum := tendsto_sum_Icc_atTop hg n
  have h1 : (fun K' : ℕ => kmtProj ρ l k (truncZ K' u) n)
      = fun K' : ℕ => ∑ j ∈ Finset.Icc (n - (K' : ℤ)) (n + (K' : ℤ)),
          kmtKern ρ l k j * u (n - j) := by
    funext K'
    exact kmtProj_truncZ_eq_sumIcc ρ l k K' u n
  rw [h1, kmtProj_eq_conv]
  exact hsum

/-! ## Convergence through the halved average at a fixed scale -/

/-- Convergence through the (unnormalised) halved block sum `Ablock TZ`: it is a finite sum of
products of the two function arguments evaluated at the fixed points `TZ^{P₁.eval n} x`,
`TZ^{P₂.eval n} x`. -/
theorem Ablock_TZ_tendsto {F G : ℕ → ℤ → ℂ} {F₀ G₀ : ℤ → ℂ}
    (hF : ∀ y : ℤ, Tendsto (fun K' : ℕ => F K' y) atTop (nhds (F₀ y)))
    (hG : ∀ y : ℤ, Tendsto (fun K' : ℕ => G K' y) atTop (nhds (G₀ y)))
    (m : ℕ) (P₁ P₂ : Polynomial ℤ) (x : ℤ) :
    Tendsto (fun K' : ℕ => Ablock TZ m P₁ P₂ (F K') (G K') x) atTop
      (nhds (Ablock TZ m P₁ P₂ F₀ G₀ x)) := by
  simp only [Ablock]
  exact tendsto_finsetSum _ (fun n _ => (hF _).mul (hG _))

/-- Convergence through the halved average `Ã_N` at a fixed real scale `N`. -/
theorem AhalfR_TZ_tendsto {F G : ℕ → ℤ → ℂ} {F₀ G₀ : ℤ → ℂ}
    (hF : ∀ y : ℤ, Tendsto (fun K' : ℕ => F K' y) atTop (nhds (F₀ y)))
    (hG : ∀ y : ℤ, Tendsto (fun K' : ℕ => G K' y) atTop (nhds (G₀ y)))
    (N : ℝ≥0) (P₁ P₂ : Polynomial ℤ) (x : ℤ) :
    Tendsto (fun K' : ℕ => AhalfR TZ N P₁ P₂ (F K') (G K') x) atTop
      (nhds (AhalfR TZ N P₁ P₂ F₀ G₀ x)) := by
  simp only [AhalfR, Ahalf]
  exact (Ablock_TZ_tendsto hF hG (Nat.floor N) P₁ P₂ x).const_mul _

/-! ## The target -/

theorem minorArc_tendsto_truncZ (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : NNReal) (P : Polynomial ℤ) {u v : ℤ → ℂ}
    (hu : Work.KMTAreas.A5.BoundedZ u) (hv : Work.KMTAreas.A5.BoundedZ v) (x : ℤ) :
    (Filter.Tendsto (fun K' : ℕ => Work.KMTContract.kmtProj ρ L K (Work.KMTContract.truncZ K' u) x)
      Filter.atTop (nhds (Work.KMTContract.kmtProj ρ L K u x))) ∧
    (Filter.Tendsto (fun K' : ℕ => Work.KMTContract.kmtProj ρ L K₂ (Work.KMTContract.truncZ K' v) x)
      Filter.atTop (nhds (Work.KMTContract.kmtProj ρ L K₂ v x))) ∧
    (Filter.Tendsto (fun K' : ℕ => Work.KMTAreas.A5.minorArc₁ ρ L K N P
        (Work.KMTContract.truncZ K' u) (Work.KMTContract.truncZ K' v) x)
      Filter.atTop (nhds (Work.KMTAreas.A5.minorArc₁ ρ L K N P u v x))) ∧
    (Filter.Tendsto (fun K' : ℕ => Work.KMTAreas.A5.minorArc₂ ρ L K K₂ N P
        (Work.KMTContract.truncZ K' u) (Work.KMTContract.truncZ K' v) x)
      Filter.atTop (nhds (Work.KMTAreas.A5.minorArc₂ ρ L K K₂ N P u v x))) := by
  refine ⟨kmtProj_tendsto_truncZ_bounded ρ L K hu x,
    kmtProj_tendsto_truncZ_bounded ρ L K₂ hv x, ?_, ?_⟩
  · -- the first minor-arc part: `Ã_N(u - Π_{≤L,≤K} u, v)`
    have hF : ∀ y : ℤ, Tendsto
        (fun K' : ℕ => (truncZ K' u - kmtProj ρ L K (truncZ K' u)) y) atTop
        (nhds ((u - kmtProj ρ L K u) y)) :=
      fun y => (tendsto_truncZ u y).sub (kmtProj_tendsto_truncZ_bounded ρ L K hu y)
    have hG : ∀ y : ℤ, Tendsto (fun K' : ℕ => (truncZ K' v) y) atTop (nhds (v y)) :=
      fun y => tendsto_truncZ v y
    show Tendsto (fun K' : ℕ => AhalfR TZ N X P (truncZ K' u - kmtProj ρ L K (truncZ K' u))
        (truncZ K' v) x) atTop (nhds (AhalfR TZ N X P (u - kmtProj ρ L K u) v x))
    exact AhalfR_TZ_tendsto (F := fun K' : ℕ => truncZ K' u - kmtProj ρ L K (truncZ K' u))
      (G := fun K' : ℕ => truncZ K' v) (F₀ := u - kmtProj ρ L K u) (G₀ := v) hF hG N X P x
  · -- the second minor-arc part: `Ã_N(Π_{≤L,≤K} u, v - Π_{≤L,≤K₂} v)`
    have hF : ∀ y : ℤ, Tendsto (fun K' : ℕ => (kmtProj ρ L K (truncZ K' u)) y) atTop
        (nhds ((kmtProj ρ L K u) y)) :=
      fun y => kmtProj_tendsto_truncZ_bounded ρ L K hu y
    have hG : ∀ y : ℤ, Tendsto
        (fun K' : ℕ => (truncZ K' v - kmtProj ρ L K₂ (truncZ K' v)) y) atTop
        (nhds ((v - kmtProj ρ L K₂ v) y)) :=
      fun y => (tendsto_truncZ v y).sub (kmtProj_tendsto_truncZ_bounded ρ L K₂ hv y)
    show Tendsto (fun K' : ℕ => AhalfR TZ N X P (kmtProj ρ L K (truncZ K' u))
        (truncZ K' v - kmtProj ρ L K₂ (truncZ K' v)) x) atTop
      (nhds (AhalfR TZ N X P (kmtProj ρ L K u) (v - kmtProj ρ L K₂ v) x))
    exact AhalfR_TZ_tendsto (F := fun K' : ℕ => kmtProj ρ L K (truncZ K' u))
      (G := fun K' : ℕ => truncZ K' v - kmtProj ρ L K₂ (truncZ K' v))
      (F₀ := kmtProj ρ L K u) (G₀ := v - kmtProj ρ L K₂ v) hF hG N X P x

end

end Work.KMTAreas.A5
