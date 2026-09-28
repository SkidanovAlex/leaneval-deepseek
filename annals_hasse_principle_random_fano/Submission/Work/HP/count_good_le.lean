import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic

/-!
# `Work.HP.count_good_le` : the "good" part of the Archimedean count

This is the combinatorial/measure-theoretic core of N12 (`Work.HP.arch`), paper §5.3.

Let `S` be the set of primitive lattice points `a` of norm `≤ A` which are *good*: `a` has a real
zero (`IPt`), `τ(a;γ) < s`, `16γ ≤ ‖a‖`, and its whole unit neighbourhood consists of forms with a
real zero.  Two facts combine:

* **Packing.**  The `‖·‖ ≤ 1/2` balls around the points of `S` are pairwise disjoint, so by
  `hpack` the cardinality of `S` times the volume of the half-ball is at most the volume of the
  (slightly enlarged) set `Y` containing all of them.
* **Cone volume.**  Each ball around `a ∈ S` lies in
  `Y = {x : IPt x ∧ τ(x;2γ) < 2s} ∩ {‖x‖ ≤ A+1}`: membership in `IPt` is by the neighbourhood
  condition, and the bound on `τ` is the doubling property `hprop` applied at the scale `γ`.
  The set `X = {x : IPt x ∧ τ(x;2γ) < 2s}` is invariant under positive scalings
  (`hIscale`, `hscale`), so `hcone` computes `vol Y = (A+1)^N · vol(X ∩ B(1))`, and the inner
  volume is bounded by `hτvol`.  Since `2s ≤ 4s`, this gives the required `(4s)^{1/n}`.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP

/-- `eNorm` and `rNorm ∘ toR` are the same function (both are the Euclidean norm). -/
private lemma rNorm_toR_eq_eNorm' {d n : ℕ} (v : Mon d n → ℤ) : rNorm (toR v) = eNorm v := rfl

theorem count_good_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) {Kτ : ℝ} (hKτ : 0 < Kτ)
    (hτvol : ∀ (γ s : ℝ), 1 ≤ γ → 0 < s →
      volume {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1 ∧ tauArch d n a γ < s}
        ≤ ENNReal.ofReal (Kτ * s ^ (1 / (n : ℝ))))
    (hprop : ∀ (a y : Mon d n → ℝ) (γ : ℝ), 0 < γ → 8 * γ ≤ rNorm a → rNorm (y - a) ≤ 1 →
        tauArch d n y (2 * γ) ≤ 2 * tauArch d n a γ)
    (hscale : ∀ (a : Mon d n → ℝ) (γ t : ℝ), 0 < t → tauArch d n (t • a) γ = tauArch d n a γ)
    (hIscale : ∀ (a : Mon d n → ℝ) (t : ℝ), 0 < t → (IPt d n (t • a) ↔ IPt d n a))
    (hcone : ∀ (X : Set (Mon d n → ℝ)) (A : ℝ), 0 < A →
        (∀ (t : ℝ), 0 < t → ∀ a, a ∈ X ↔ t • a ∈ X) →
        volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ A})
          = ENNReal.ofReal (A ^ NN d n) * volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1}))
    (hpack : ∀ (s : Set (Mon d n → ℤ)) (Y : Set (Mon d n → ℝ)), s.Finite →
        (∀ a ∈ s, {w : Mon d n → ℝ | rNorm (w - toR a) ≤ (1 / 2 : ℝ)} ⊆ Y) →
        (s.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} ≤ volume Y)
    (hfin : ∀ R : ℝ, {a : Mon d n → ℤ | eNorm a ≤ R}.Finite)
    (γ s A : ℝ) (hγ : 1 ≤ γ) (hs : 0 < s) (hA : 1 ≤ A) :
    (({a : Mon d n → ℤ | eNorm a ≤ A ∧ IPt d n (toR a) ∧ tauArch d n (toR a) γ < s ∧
        16 * γ ≤ eNorm a ∧
        (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y)}.ncard : ℝ))
      * (volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}).toReal
      ≤ (A + 1) ^ NN d n * (Kτ * (4 * s) ^ (1 / (n : ℝ))) := by
  have hγpos : 0 < γ := by linarith
  have hA1 : 0 < A + 1 := by linarith
  -- The good lattice points.
  set S : Set (Mon d n → ℤ) :=
    {a | eNorm a ≤ A ∧ IPt d n (toR a) ∧ tauArch d n (toR a) γ < s ∧
      16 * γ ≤ eNorm a ∧ (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y)} with hS
  -- The cone of forms with a real zero and small `τ` at scale `2γ`.
  set X : Set (Mon d n → ℝ) := {x | IPt d n x ∧ tauArch d n x (2 * γ) < 2 * s} with hX
  set Y : Set (Mon d n → ℝ) := X ∩ {a : Mon d n → ℝ | rNorm a ≤ A + 1} with hY
  -- Every ball of radius `1/2` around a good point lies in `Y`.
  have hcont : ∀ a ∈ S, {w : Mon d n → ℝ | rNorm (w - toR a) ≤ (1 / 2 : ℝ)} ⊆ Y := by
    intro a ha w hw
    simp only [hS, Set.mem_ofPred_eq] at ha
    simp only [Set.mem_ofPred_eq] at hw
    obtain ⟨hAa, hIPa, hτa, h16, hN⟩ := ha
    have hwr : rNorm (w - toR a) ≤ 1 := by linarith
    have hNw : IPt d n w := hN w (by rw [rNorm_sub_comm]; exact hwr)
    have hτw : tauArch d n w (2 * γ) < 2 * s := by
      have hp := hprop (toR a) w γ hγpos (by rw [rNorm_toR_eq_eNorm']; linarith) hwr
      linarith
    refine ⟨⟨hNw, hτw⟩, ?_⟩
    have h := rNorm_le_add_sub w (toR a)
    rw [rNorm_toR_eq_eNorm'] at h
    change rNorm w ≤ A + 1
    linarith
  have hSfin : S.Finite := (hfin A).subset (fun a ha => by
    simp only [hS, Set.mem_ofPred_eq] at ha; exact ha.1)
  have hpack' := hpack S Y hSfin hcont
  -- `X` is invariant under positive scalings.
  have hsc : ∀ (t : ℝ), 0 < t → ∀ a, a ∈ X ↔ t • a ∈ X := by
    intro t ht a
    simp only [hX, Set.mem_ofPred_eq]
    rw [hIscale a t ht, hscale a (2 * γ) t ht]
  -- The cone measure of the unit slice.
  have hτvol' : volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1})
      ≤ ENNReal.ofReal (Kτ * (2 * s) ^ (1 / (n : ℝ))) := by
    have hset : X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1}
        = {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1 ∧ tauArch d n a (2 * γ) < 2 * s} := by
      ext x
      simp only [hX, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hset]
    exact hτvol (2 * γ) (2 * s) (by linarith) (by linarith)
  have hYvol : volume Y
      ≤ ENNReal.ofReal ((A + 1) ^ NN d n * (Kτ * (2 * s) ^ (1 / (n : ℝ)))) := by
    rw [hY, hcone X (A + 1) hA1 hsc]
    calc ENNReal.ofReal ((A + 1) ^ NN d n) * volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1})
        ≤ ENNReal.ofReal ((A + 1) ^ NN d n) * ENNReal.ofReal (Kτ * (2 * s) ^ (1 / (n : ℝ))) :=
          mul_le_mul' le_rfl hτvol'
      _ = ENNReal.ofReal ((A + 1) ^ NN d n * (Kτ * (2 * s) ^ (1 / (n : ℝ)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hmain : (S.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
      ≤ ENNReal.ofReal ((A + 1) ^ NN d n * (Kτ * (4 * s) ^ (1 / (n : ℝ)))) := by
    refine le_trans hpack' (le_trans hYvol (ENNReal.ofReal_le_ofReal ?_))
    have h2s : (2 * s) ^ (1 / (n : ℝ)) ≤ (4 * s) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have hmul : Kτ * (2 * s) ^ (1 / (n : ℝ)) ≤ Kτ * (4 * s) ^ (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h2s hKτ.le
    exact mul_le_mul_of_nonneg_left hmul (by positivity)
  -- Pass to `ℝ` on both sides.
  have h2 : ((S.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}).toReal
      ≤ (A + 1) ^ NN d n * (Kτ * (4 * s) ^ (1 / (n : ℝ))) := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
  exact h2

end Work.HP
