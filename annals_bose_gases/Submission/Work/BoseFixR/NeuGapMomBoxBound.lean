import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBox.q3kinMomFormLeGapBare
import Submission.Work.BoseBox.q3kinNeuFracLeGapBare
import Submission.Work.BoseFixR.fibre_sup_bound
import Submission.Work.BoseFixR.gapBare_zero_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.NeuGapMomBoxBound`

**The bounded part of the localised kinetic word is bounded on the box.**

`Work.BoseBox.neuGapMom ℓ d s eT b Φ i r` is the sum of the three *bounded* pieces of FS's
localised kinetic word `eq:DefT` along the slot-`i` fibre of an `(m+1)`-particle state `Φ`,

    `neuGapMom = neuWord + gapWord + momWord`
              `= ½ε_T(dℓ)⁻²·neuFrac(Q_0ψ) + bℓ⁻²·gapBare + bε_T(dℓ)⁻²·momForm`,

with `ψ = fun z => Φ (kcInsN m i (z, r))` (see `Work.BoseBox.fsWord_eq`, which splits `fsWord`
into `neuGapMom + mWord`).  The theorem states that for a merely **continuous** `Φ` this sum is
bounded above on the configuration box `abox m ℓ`, uniformly in `r` (the parameter `s` does not
occur in the three pieces).

## Route

Each of the three pieces is dominated by the *same* anchored bare mean-free box mass
`g := gapBare ℓ 0 ψ`:

* `neuFrac ℓ ((dℓ)⁻²) 0 (Q_0ψ) ≤ g` — `Work.BoseBox.q3kinNeuFracLeGapBare`, from the trial
  `g ≡ 0` in the Dirichlet principle (`A(A+a²)⁻¹ ≤ 1`);
* `momForm ℓ d 0 ψ ≤ g` — `Work.BoseBox.q3kinMomFormLeGapBare`, discarding the momentum
  cut-off and applying Plancherel;
* `gapWord = bℓ⁻²·g` is already a multiple of `g`.

All three coefficients `½ε_T(dℓ)⁻²`, `bℓ⁻²`, `bε_T(dℓ)⁻²` are nonnegative under
`0 < d`, `0 < ℓ`, `0 ≤ ε_T`, `0 ≤ b`, so

    `neuGapMom ≤ (½ε_T(dℓ)⁻² + bℓ⁻² + bε_T(dℓ)⁻²) · g`,

and it remains to bound `g` uniformly in `r`.  That is compactness plus the trivial mean bound:
for `r ∈ abox m ℓ` and `z ∈ acube ℓ` the insertion `kcInsN m i (z,r)` lies in the compact box
`abox (m+1) ℓ`, on which the continuous `Φ` is bounded by some `M ≥ 0`
(`Work.BoseFixR.fibre_sup_bound`); the box mean `m = |acube ℓ|⁻¹∫_{acube ℓ} ψ` is then also
bounded by `M`, so `|Q_0ψ| ≤ 2M` pointwise on the box and integrating over `acube ℓ`
(volume `ℓ³`) gives `g ≤ (2M)²ℓ³` (`Work.BoseFixR.gapBare_zero_le`).

The witness is therefore `K = (½ε_T(dℓ)⁻² + bℓ⁻² + bε_T(dℓ)⁻²)·(2M)²ℓ³ ≥ 0`.
-/

namespace Work.BoseFixR

set_option linter.unusedVariables false

/-- **Continuity of the slot insertion in the inserted coordinate.**  For fixed `r`, the map
`z ↦ kcInsN m i (z, r)` is continuous: by `continuous_pi` it suffices to control each coordinate,
and each coordinate of the insertion is either `z` itself (`kc_insN_apply_same`) or a coordinate
`r j'` of the frozen configuration (`kc_insN_apply_succ`). -/
private lemma continuous_kcInsN_snd {m : ℕ} (i : Fin (m + 1)) (r : Submission.BoseGases.X m) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kcInsN m i (z, r)) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = i
  · have hsame : ∀ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.kcInsN m i (z, r) j = z := by
      intro z
      rw [hj]
      exact Submission.BoseGases.kc_insN_apply_same m i z r
    exact continuous_id.congr (fun z => (hsame z).symm)
  · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hj
    have hsame : ∀ z : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kcInsN m i (z, r) j = r j' := by
      intro z
      rw [← hj']
      exact Submission.BoseGases.kc_insN_apply_succ m i z r j'
    exact continuous_const.congr (fun z => (hsame z).symm)

theorem NeuGapMomBoxBound {m : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseBox.neuGapMom ℓ d s eT b Φ i r ≤ K := by
  obtain ⟨M, hM0, hM⟩ := fibre_sup_bound hℓ hΦ i
  -- the three coefficients are nonnegative
  have hc1 : 0 ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) := by
    have hz1 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    positivity
  have hc2 : 0 ≤ b * ℓ ^ (-2 : ℤ) := by
    have hz2 : 0 ≤ ℓ ^ (-2 : ℤ) := zpow_nonneg hℓ.le _
    positivity
  have hc3 : 0 ≤ b * eT * (d * ℓ) ^ (-2 : ℤ) := by
    have hz1 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    positivity
  have hB0 : 0 ≤ (2 * M) ^ 2 * ℓ ^ 3 := by positivity
  refine ⟨((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
    + b * eT * (d * ℓ) ^ (-2 : ℤ)) * ((2 * M) ^ 2 * ℓ ^ 3), ?_, ?_⟩
  · exact mul_nonneg (by linarith) hB0
  · intro r hr
    -- the slot-`i` fibre is continuous as a function of the inserted coordinate
    have hψc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN m i (z, r))) :=
      hΦ.comp (continuous_kcInsN_snd i r)
    -- and the uniform bound on `Φ` restricts to it
    have hgap := gapBare_zero_le hℓ hM0 hψc (fun z hz => hM r hr z hz)
    -- the two domination lemmas of the corpus
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    have hneu := Work.BoseBox.q3kinNeuFracLeGapBare (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
      hℓ ha2 0 hψc
    have hmom := Work.BoseBox.q3kinMomFormLeGapBare (ℓ := ℓ) (d := d) hℓ 0 hψc
    have e1 : Work.BoseKinLoc.neuWord ℓ d eT 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
      rw [Work.BoseKinLoc.neuWord]
      exact mul_le_mul_of_nonneg_left hneu hc1
    have e2 : Work.BoseKinLoc.gapWord ℓ b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        = b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := rfl
    have e3 : Work.BoseKinLoc.momWord ℓ d eT b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ b * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
      rw [Work.BoseKinLoc.momWord]
      exact mul_le_mul_of_nonneg_left hmom hc3
    rw [Work.BoseBox.neuGapMom]
    calc Work.BoseKinLoc.neuWord ℓ d eT 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
            Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + Work.BoseKinLoc.gapWord ℓ b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + Work.BoseKinLoc.momWord ℓ d eT b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + b * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) :=
          add_le_add (add_le_add e1 (le_of_eq e2)) e3
      _ = ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
            + b * eT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
          ring
      _ ≤ ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
            + b * eT * (d * ℓ) ^ (-2 : ℤ)) * ((2 * M) ^ 2 * ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left hgap (by linarith)

end Work.BoseFixR
