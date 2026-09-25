import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmPotential_iter_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_top_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_holderNorm_le
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Final

open scoped NNReal ENNReal
open MeasureTheory Set
open Work.CR.Flat

noncomputable section

/-- Unfolding of `holderNorm` one step: private copy of the lemma of the same content in
`Submission/Work/CR/Flat/Cauchy/exists_dbar_solution_polydisc_Ck.lean`. -/
private lemma holderNorm_succ_local {n : ℕ} (k : ℕ) (α : ℝ) (g : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) :
    holderNorm (k + 1) α g Ω
      = holderNorm k α g Ω + (iterDerivNorm (k + 1) g Ω + holderSeminorm (k + 1) α g Ω) := by
  rw [holderNorm, holderNorm, Finset.sum_range_succ]

/-- **The Bochner–Martinelli row potential is an order-`-1` operator in the full `C^{k,α}` scale, for
compactly supported data.**  For `0 < α < 1`, a centre `c`, radii `ρ > 0` and every `k` there is
`C > 0` such that for every family `X : Fin n → Fin n → (ℂⁿ → ℂ)` of class `C^{k+1}` whose
components vanish at every point with `∃ i, ρ i ≤ ‖z i - c i‖` (i.e. outside the polydisc of radii
`ρ`), and for every `j`,

  `‖bmPot (X_{j·})‖_{C^{k+1,α}(polydisc c (ρ/2))} ≤ C · Σ_{l} ‖X_{j l}‖_{C^{k,α}(ℂⁿ)}`.

No closedness or antisymmetry is needed: this is the combination of the proved lower-order bound
`bmPotential_iter_bound` and the top-order bound `bmPotential_top_bound` (which both take the base
Calderón–Zygmund estimate as hypothesis), exactly as they are combined inside the proof of
`Work.NN.Core.flat_dbar_twoForm_Ck`.  The same statement, applied to the (0,3)-form
`X = ∂̄χ ∧ η`, is what turns the Bochner–Martinelli defect identity `Work.NN.Final.bmDefectTwo` into
an estimate for the residual. -/
theorem bmRow_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    {c : Fin n → ℂ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ j l, ContDiff ℝ (k + 1) (X j l)) →
      (∀ j l z, (∃ i, ρ i ≤ ‖z i - c i‖) → X j l z = 0) →
      ∀ j : Fin n,
        Work.CR.Flat.holderNorm (k + 1) α
            (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => X j l) y)
            (Work.CR.Flat.polydisc c (fun i => ρ i / 2))
          ≤ ENNReal.ofReal C *
              ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm k α (X j l) Set.univ := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: the conclusion is vacuous
    subst hn0
    refine ⟨1, one_pos, ?_⟩
    intro X _hX _hvan j
    exact Fin.elim0 j
  have hr2 : ∀ j, 0 < 2 * ρ j := fun j => by linarith [hρ j]
  have hr4 : ∀ j, 0 < 4 * ρ j := fun j => by linarith [hρ j]
  -- The order-zero (Calderón–Zygmund) estimate on the polydisc of radii `2ρ`: the data is
  -- supported in the polydisc of *half* that radius, `ρ`.  This is the `C^{1,α}` Schauder
  -- estimate on the polydisc of radii `4ρ` (whose half is `2ρ`), applied to data vanishing where
  -- `∃ i, (4ρ_i)/2 = 2ρ_i ≤ ‖z_i - c_i‖`.
  have hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, 2 * ρ i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) (polydisc c (fun i => 2 * ρ i))
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ := by
    obtain ⟨C₀, hC₀pos, hC₀⟩ :=
      Work.CR.Flat.Cauchy.bmPotential_holderNorm_le (n := n) hn (c := c)
        (r := fun j => 4 * ρ j) hα0 hα1 hr4
    refine ⟨C₀, hC₀pos, fun g hg hgs => ?_⟩
    have hvan4 : ∀ j z, (∃ i, (fun i => 4 * ρ i) i / 2 ≤ ‖z i - c i‖) → g j z = 0 := by
      intro j z hz
      obtain ⟨i, hi⟩ := hz
      exact hgs j z ⟨i, by rwa [show 4 * ρ i / 2 = 2 * ρ i from by ring] at hi⟩
    have h := hC₀ g hg hvan4
    rwa [show (fun j => (fun i => 4 * ρ i) j / 2) = (fun j => 2 * ρ j) from by
      funext j; show 4 * ρ j / 2 = 2 * ρ j; ring] at h
  -- the lower-order and top-order Schauder bounds, on the polydisc of radii `2ρ / 2 = ρ`,
  -- for data supported in the polydisc of radii `ρ`
  obtain ⟨C₁, hC₁pos, hiter⟩ :=
    Work.CR.Flat.Cauchy.bmPotential_iter_bound (n := n) hn (c := c) (r := fun j => 2 * ρ j)
      hα0 hα1 hr2 k hbase
  obtain ⟨C₂, hC₂pos, htop⟩ :=
    Work.CR.Flat.Cauchy.bmPotential_top_bound (n := n) hn (c := c) (r := fun j => 2 * ρ j)
      hα0 hα1 hr2 k hbase
  set K : ℝ := 2 * ((k : ℝ) + 1) * C₁ + 2 * C₂ with hK
  have hKpos : 0 < K := by
    rw [hK]; positivity
  refine ⟨K, hKpos, ?_⟩
  intro X hX hvan jrow
  set S : ℝ≥0∞ := ∑ l, holderNorm k α (X jrow l) Set.univ with hS
  -- the `jrow`-th row vanishes outside the polydisc of radii `ρ = (2ρ)/2`
  have hvan' : ∀ l z, (∃ i, (fun i => 2 * ρ i) i / 2 ≤ ‖z i - c i‖) → X jrow l z = 0 := by
    intro l z hz
    obtain ⟨i, hi⟩ := hz
    exact hvan jrow l z ⟨i, by rwa [show 2 * ρ i / 2 = ρ i from by ring] at hi⟩
  have hiterb : ∀ m, m ≤ k →
      (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
          (polydisc c (fun i => 2 * ρ i / 2)) ≤ ENNReal.ofReal C₁ * S) ∧
      (holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
          (polydisc c (fun i => 2 * ρ i / 2)) ≤ ENNReal.ofReal C₁ * S) := fun m hm =>
    hiter (fun l => X jrow l) (fun l => hX jrow l) hvan' m hm
  -- the lower-order part, summing over the `m ≤ k`
  have hlower : holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
      (polydisc c (fun i => 2 * ρ i / 2)) ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
    rw [holderNorm]
    calc ∑ m ∈ Finset.range (k + 1),
            (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
              (polydisc c (fun i => 2 * ρ i / 2))
              + holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
                (polydisc c (fun i => 2 * ρ i / 2)))
        ≤ ∑ _m ∈ Finset.range (k + 1), (ENNReal.ofReal (2 * C₁) * S) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          refine (add_le_add (hiterb m hmk).1 (hiterb m hmk).2).trans ?_
          rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₁pos) (le_of_lt hC₁pos),
            show C₁ + C₁ = 2 * C₁ from by ring]
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 * C₁) * S) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
          rw [← ENNReal.ofReal_natCast (k + 1), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          ring
  -- the top-order part
  have htop' : iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
        (polydisc c (fun i => 2 * ρ i / 2))
      + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
        (polydisc c (fun i => 2 * ρ i / 2)) ≤ ENNReal.ofReal (2 * C₂) * S := by
    have hh := htop (fun l => X jrow l) (fun l => hX jrow l) hvan'
    refine (add_le_add hh.1 hh.2).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₂pos) (le_of_lt hC₂pos),
      show C₂ + C₂ = 2 * C₂ from by ring]
  -- assembly of the two parts at order `k + 1`
  have hbound : holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
      (polydisc c (fun i => 2 * ρ i / 2)) ≤ ENNReal.ofReal K * S := by
    rw [holderNorm_succ_local k α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
      (polydisc c (fun i => 2 * ρ i / 2)), hK]
    calc holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
            (polydisc c (fun i => 2 * ρ i / 2))
          + (iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
              (polydisc c (fun i => 2 * ρ i / 2))
            + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
              (polydisc c (fun i => 2 * ρ i / 2)))
        ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S + ENNReal.ofReal (2 * C₂) * S :=
          add_le_add hlower htop'
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁ + 2 * C₂) * S := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hfun : (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => X jrow l) y)
      = (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l)) := by
    funext y
    exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (fun l => X jrow l) y).symm
  have hST : S ≤ ∑ j : Fin n, ∑ l : Fin n, holderNorm k α (X j l) Set.univ := by
    rw [hS]
    exact Finset.single_le_sum (f := fun j => ∑ l, holderNorm k α (X j l) Set.univ)
      (fun j _ => bot_le) (Finset.mem_univ jrow)
  -- restrict the estimate from the polydisc of radii `ρ` to the polydisc of radii `ρ/2`
  have hsub : polydisc c (fun i => ρ i / 2) ⊆ polydisc c (fun i => 2 * ρ i / 2) :=
    polydisc_mono (fun i => by linarith [hρ i])
  have hmono : holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
      (polydisc c (fun i => ρ i / 2))
      ≤ holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
        (polydisc c (fun i => 2 * ρ i / 2)) :=
    holderNorm_mono_set (isOpen_polydisc c (fun i => 2 * ρ i / 2))
      (isOpen_polydisc c (fun i => ρ i / 2)) hsub (k + 1) α _
  calc holderNorm (k + 1) α (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => X jrow l) y)
        (polydisc c (fun i => ρ i / 2))
      = holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
        (polydisc c (fun i => ρ i / 2)) := by rw [hfun]
    _ ≤ holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => X jrow l))
        (polydisc c (fun i => 2 * ρ i / 2)) := hmono
    _ ≤ ENNReal.ofReal K * S := hbound
    _ ≤ ENNReal.ofReal K *
          ∑ j : Fin n, ∑ l : Fin n, holderNorm k α (X j l) Set.univ :=
        mul_le_mul_right hST _

end

end Work.NN.Final
