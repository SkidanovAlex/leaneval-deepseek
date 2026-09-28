import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.HP2.good_classes_lower
import Submission.Work.HP.HP2.classPrimSet_sum_le
import Submission.Work.HP.bigW_le_pow

open Filter MeasureTheory

namespace Work.HP.HP2

/-- **Summing the per-class bound over the good residue classes (auxiliary form).**

Given the per-class lower bound `(1/8)·vol(coneRegion R)/W^{n+1} ≤ #classPrimSet b` for every `b`
in the box `[0,W)^{n+1}` that is primitive at every prime divisor of `W` and satisfies
`W ∣ f_a(b)`, conclude
`(1/8)·σ·vol(coneRegion R)/W ≤ #primConeSet`, where `σ = sigmaLoc d n a W` is the proportion of
unimodular residue classes mod `W` at which `f_a` vanishes and `primConeSet` is the index set of
`NVloc`.

Route.  `good_classes_lower` produces a `Finset G` with exactly the hypothesis shape of `hclass`
and `(G.card : ℝ) = sigmaLoc d n a W * W^n`; summing `hclass` over `b ∈ G` gives
`(G.card : ℝ) * ((1/8) vol/W^{n+1}) ≤ ∑_{b ∈ G} #classPrimSet b`, and
`∑_{b ∈ G} #classPrimSet b ≤ #primConeSet` is `classPrimSet_sum_le`.  Finally
`(G.card : ℝ) * ((1/8) vol/W^{n+1}) = (1/8)·σ·vol/W` using `W^n / W^{n+1} = 1/W`. -/
lemma sigma_lower_aux (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (W : ℕ) (hW : 0 < W) (α R : ℝ)
    (hclass : ∀ b : Fin (n + 1) → ℤ,
      (∀ i, 0 ≤ b i ∧ b i < W) →
      (∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i) →
      (W : ℤ) ∣ Work.HP.formEval d n a b →
      (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)
        ≤ ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ)) :
    (1 / 8) * Work.HP.sigmaLoc d n a W
        * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
      / (W : ℝ)
      ≤ ((Work.HP.primConeSet d n a α R W).ncard : ℝ) := by
  classical
  obtain ⟨G, hG, hcard⟩ := good_classes_lower d n W hW a
  -- Sum the per-class bound over the good classes.
  have hsum : ∑ b ∈ G, (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)
      ≤ ∑ b ∈ G, ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ) :=
    Finset.sum_le_sum (fun b hb => hclass b (hG b hb).1 (hG b hb).2.1 (hG b hb).2.2)
  have hsumL : ∑ b ∈ G, (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)
      = (G.card : ℝ) * ((1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbound := classPrimSet_sum_le d n a W α R G hG
  have hchain : (G.card : ℝ) * ((1 / 8)
          * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
        / (W : ℝ) ^ (n + 1)) ≤ ((Work.HP.primConeSet d n a α R W).ncard : ℝ) := by
    rw [← hsumL]
    exact le_trans hsum hbound
  -- Rewrite the left-hand side using `(G.card : ℝ) = σ * W^n` and `W^n / W^{n+1} = 1/W`.
  have harith : (1 / 8) * Work.HP.sigmaLoc d n a W
        * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ)
      = (Work.HP.sigmaLoc d n a W * (W : ℝ) ^ n)
        * ((1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
          / (W : ℝ) ^ (n + 1)) := by
    have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    rw [pow_succ]
    field_simp
  rw [harith, ← hcard]
  exact hchain

/-- **Summing the per-class bound over the `σ W^n` good residue classes.** Assume the per-class lower
bound `(1/8) vol(coneRegion R)/W^{n+1} ≤ #classPrimSet b` for every `b` in the box `[0,W)^{n+1}`
that is primitive at every prime divisor of `W` and satisfies `W ∣ f_a(b)`.  Then
`(1/8) · sigmaLoc d n a W · vol(coneRegion R)/W ≤ #primConeSet`, where `σ = sigmaLoc d n a W` is the
proportion of unimodular residue classes mod `W` at which `f_a` vanishes and `primConeSet` is the
index set of `NVloc`.

Route.  `Work.HP.HP2.good_classes_lower` (needs `W ≥ 1`, from `Work.HP.one_le_bigW`) produces a
`Finset G` with exactly the hypothesis shape of `hclass` and `(G.card : ℝ) = sigmaLoc d n a W * W^n`.
Sum `hclass` over `b ∈ G`:
`(G.card : ℝ) * ((1/8) vol/W^{n+1}) ≤ ∑_{b ∈ G} #classPrimSet b`.
Now `∑_{b ∈ G} #classPrimSet b ≤ #primConeSet`, because (i) each `classPrimSet b` is contained in
`primConeSet` — `v ≡ b (mod W)` and `W ∣ f_a(b)` give `W ∣ f_a(v)` via `Work.HP.formEval_congr_mod`,
the other three conjuncts being identical — and (ii) the `classPrimSet b`, `b ∈ G`, are pairwise
disjoint: `v` in two of them forces `W ∣ (b i − b' i)` for all `i` while `0 ≤ b i, b' i < W`, so
`b = b'` (and if `W = 0` the box is empty, so `G = ∅` and the claim is `0 ≤ 0`).  Finiteness of the
sets: `classPrimSet b ⊆ {v | eNorm v ≤ R}` and `primConeSet ⊆ Xi d n B`.
Finally `(G.card : ℝ) * ((1/8) vol/W^{n+1}) = (1/8) · σ · vol / W` using `W^n / W^{n+1} = 1/W`. -/
theorem primConeSet_sigma_lower (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∀ᶠ B in atTop, ∀ (a : Work.HP.Mon d n → ℤ),
      a ≠ 0 → Work.HP.RealSol d n a →
      (∀ (b : Fin (n + 1) → ℤ),
        (∀ i, 0 ≤ b i ∧ b i < Work.HP.bigW (Work.HP.wOf B)) →
        (∀ p : ℕ, p.Prime → p ∣ Work.HP.bigW (Work.HP.wOf B) → ∃ i, ¬ (p : ℤ) ∣ b i) →
        ((Work.HP.bigW (Work.HP.wOf B) : ℤ) ∣ Work.HP.formEval d n a b) →
        (1 / 8) * (MeasureTheory.volume (Work.HP.coneRegion d n a (Real.log B)
            (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
          / (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ (n + 1)
          ≤ ((Work.HP.classPrimSet d n a b (Work.HP.bigW (Work.HP.wOf B)) (Real.log B)
              (B ^ (1 / ((n : ℝ) + 1 - d)))).ncard : ℝ)) →
      (1 / 8) * Work.HP.sigmaLoc d n a (Work.HP.bigW (Work.HP.wOf B))
          * (MeasureTheory.volume (Work.HP.coneRegion d n a (Real.log B)
              (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
        / (Work.HP.bigW (Work.HP.wOf B) : ℝ)
        ≤ ((Work.HP.primConeSet d n a (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
            (Work.HP.bigW (Work.HP.wOf B))).ncard : ℝ) := by
  refine Filter.Eventually.of_forall (fun B => ?_)
  intro a _ha _hreal hclass
  have hW : 0 < Work.HP.bigW (Work.HP.wOf B) :=
    lt_of_lt_of_le Nat.zero_lt_one (Work.HP.one_le_bigW (Work.HP.wOf B))
  exact sigma_lower_aux d n a (Work.HP.bigW (Work.HP.wOf B)) hW (Real.log B)
    (B ^ (1 / ((n : ℝ) + 1 - d))) hclass

end Work.HP.HP2
