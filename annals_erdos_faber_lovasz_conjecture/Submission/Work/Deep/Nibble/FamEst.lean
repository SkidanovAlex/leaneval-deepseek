import Submission.Work.Deep.Nibble.FamDefs
import Submission.Work.Deep.Nibble.r2_own_b
import Submission.Work.Deep.Nibble.r2_own_h
import Submission.Work.Deep.Nibble.r2_Y_mean
import Submission.Work.Deep.Nibble.nibble_round_lemmas

/-!
# The per-set estimates of the family nibble

This module adds the per-set quantities of the "wasteful" Rödl nibble and their
first-moment estimates, in the form needed by the family round
(`nibble_round2_fam`).  The sets of the family are `Finset V`s, which is the
convenient form for the union bound over the family and for the per-set
cardinality estimates.

* `uncovFam 𝓖 ω S` — the vertices of `S` left uncovered by the round;
* `wasteFam 𝓖 ω S` — the vertices of `S` covered by a kept edge yet lying in no
  isolated kept edge: the vertices of `S` that the round's matching loses
  permanently;
* `badSum 𝓖 ω S = ∑_{e bad}|e ∩ S|` — the edge-charged upper bound for
  `wasteFam` (`wasteFam_le_badSum`), whose mean is computed by `r2_Wfam_mean`;
* `r2_exp_fam` — the exact mean of `uncovFam`;
* `r2_Yfam_mean` — `|E[uncovFam] - e^{-θ}|S|| ≤ δ|S|/2` under degree regularity.

The two per-set tail bounds (Bruhn--Joos certificates of size `|S|` and
`O(D²|S|)`) are `Work.Deep.Nibble.r2_Yfam_tail` and `Work.Deep.Nibble.r2_Wfam_tail`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The expectation of the indicator of an event is its probability. -/
lemma exp_indicator_set {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (A : Set Ω)
    [DecidablePred (· ∈ A)] :
    μ.exp (fun ω => if ω ∈ A then (1 : ℝ) else 0) = μ.prob A := by
  classical
  rw [FinProb.exp, FinProb.prob]
  exact Finset.sum_congr rfl fun ω _ => by
    by_cases h : ω ∈ A <;> simp [h]

/-- Expectation of a finite sum of real random variables. -/
lemma exp_sum_finset {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.exp (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.exp (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.exp_const]
  | insert a s ha ih =>
      have hpt : (fun ω => ∑ i ∈ insert a s, X i ω) = (fun ω => X a ω + ∑ i ∈ s, X i ω) :=
        funext fun ω => Finset.sum_insert ha
      rw [hpt, FinProb.exp_add, ih, Finset.sum_insert ha]

/-- The vertices of the finite set `S` left uncovered by the round. -/
noncomputable def uncovFam (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : ℕ := by
  classical
  exact (S.filter (fun v => v ∉ covX 𝓖 ω)).card

/-- The vertices of `S` covered by a kept edge of the round but lying in no
*isolated* kept edge: the vertices of `S` lost by the round. -/
noncomputable def wasteFam (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : ℕ := by
  classical
  exact (S.filter (fun v => v ∈ covX 𝓖 ω ∧ v ∉ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V))).card

/-- A kept edge is **bad** if some other kept edge meets it. -/
def badAt (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e : 𝓖) : Prop :=
  ω e = true ∧ ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ (f.1 ∩ e.1).Nonempty

/-- The edge-charged waste inside `S`: every bad kept edge contributes its
intersection with `S`.  It dominates `wasteFam` (`wasteFam_le_badSum`). -/
noncomputable def badSum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : ℕ := by
  classical
  exact ∑ e : 𝓖, if badAt 𝓖 ω e then (e.1 ∩ (S : Set V)).ncard else 0

/-- **The per-set clauses of one round of the family nibble**: for every `S` of
the family, the round leaves an `e^{-θ}`-fraction of `S` uncovered up to `δ|S|`,
and the vertices of `S` lost by the round (covered but not matched) are at most
`(1+δ)·2rθ²|S|`. -/
noncomputable def RoundGoodFamF (𝓖 : Set (Set V)) (r : ℕ) (θ δ : ℝ)
    (𝓕 : Finset (Finset V)) (ω : 𝓖 → Bool) : Prop :=
  (∀ S ∈ 𝓕, |((uncovFam 𝓖 ω S : ℝ)) - Real.exp (-θ) * (S.card : ℝ)| ≤ δ * (S.card : ℝ)) ∧
  (∀ S ∈ 𝓕, ((wasteFam 𝓖 ω S : ℝ)) ≤ (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ))

/-- **The exact mean of the per-set uncovered count**: `∑_{v ∈ S}(1-p)^{d(v)}`. -/
theorem r2_exp_fam (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset V) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))
      = ∑ v ∈ S, (1 - p) ^ (hd 𝓖 v) := by
  classical
  have hpt : ∀ ω : 𝓖 → Bool, ((uncovFam 𝓖 ω S : ℕ) : ℝ)
      = ∑ v ∈ S, (if v ∉ covX 𝓖 ω then (1 : ℝ) else 0) := by
    intro ω
    rw [uncovFam, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases h : x ∉ covX 𝓖 ω <;> simp [h]
  rw [show (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ))
      = (fun ω => ∑ v ∈ S, (if v ∉ covX 𝓖 ω then (1 : ℝ) else 0)) from funext hpt]
  rw [exp_sum_finset]
  exact Finset.sum_congr rfl fun v _ =>
    (exp_indicator_set (μ := edgeMeasure 𝓖 p hp0 hp1)
        (A := {ω : 𝓖 → Bool | v ∉ covX 𝓖 ω})).trans ((r2_exp_basic 𝓖 hp0 hp1).2.1 v)

/-- **The per-set mean bound of the round.**  If the degrees are `(1±ε)D`, `4ε ≤ δ`,
`8θ² ≤ δD`, and `p = θ/D`, then the expected number of uncovered vertices of `S` is
within `δ|S|/2` of `e^{-θ}|S|`. -/
theorem r2_Yfam_mean {𝓖 : Set (Set V)} {θ δ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hδ0 : 0 < δ) (hε0 : 0 < ε) (hεδ : 4 * ε ≤ δ)
    {D : ℕ} (hD : 8 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hθD : θ / (D : ℝ) ≤ 1 / 2) (hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ))
    (hdeg : ∀ v : V, |((hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) (S : Finset V) :
    |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))
        - Real.exp (-θ) * (S.card : ℝ)| ≤ δ * (S.card : ℝ) / 2 := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hpd : (θ / (D : ℝ)) * (D : ℝ) = θ := div_mul_cancel₀ θ hDne
  rw [r2_exp_fam 𝓖 hp0 hp1 S]
  have hsplit : (∑ v ∈ S, (1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ) * (S.card : ℝ))
      = ∑ v ∈ S, ((1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit]
  calc |∑ v ∈ S, ((1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ))|
      ≤ ∑ v ∈ S, |(1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, δ / 2 := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        exact r2Y_per_vertex hθ0 hθ1 hδ0 hε0 hεδ hD hp0 hp1 hpd hbig (hdeg v)
    _ = δ * (S.card : ℝ) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Work.Deep.Nibble
