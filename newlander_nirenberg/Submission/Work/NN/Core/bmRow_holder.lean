import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.flat_dbar_twoForm_Ck
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.CR.Flat.Cauchy.bmPotential_iter_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_top_bound

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set
open Work.CR.Flat

/-- **Bochner–Martinelli row potential in the `C^{k+1,α}` scale, for supported data.**

For `0 < α < 1`, a centre `c`, positive multi-radii `r` and `k : ℕ` there is `C > 0` such that for
every `η : Fin n → Fin n → ℂⁿ → ℂ` with components of class `C^{k+1}` supported in the half-size
polydisc (`η j l z = 0` whenever some `‖z i - c i‖ ≥ r i / 2`) one has, for every `j`,

  `‖bmRow η j‖_{C^{k+1,α}(polydisc c (r/2))} ≤ C · Σ_{l,m} ‖η_{l m}‖_{C^{k,α}(ℂⁿ)}`.

This is the estimate part of `Work.NN.Core.flat_dbar_twoForm_Ck`, whose proof produces
`ψ i = -γ⁻¹ bmPotential (η_{i·}) = bmRow η i` using `Work.NN.Core.bmPotential_holder` together with
`Work.CR.Flat.Cauchy.bmPotential_iter_bound` and `bmPotential_top_bound`; it should be extracted
from that proof, with the same `holderNorm_succ` / `holderNorm_smul` algebra. -/
theorem bmRow_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {c : Work.NN.Core.Cn n} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
      (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
      (∀ j l z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → η j l z = 0) →
      ∀ j, Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmRow η j)
            (Work.CR.Flat.polydisc c (fun j => r j / 2))
        ≤ ENNReal.ofReal C * ∑ l, ∑ m, Work.CR.Flat.holderNorm k α (η l m) Set.univ := by
  -- the order-zero potential estimate on the polydisc of twice the radii, obtained from the
  -- C^{1,α} Bochner–Martinelli Schauder estimate by doubling
  have hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ := by
    obtain ⟨C₀, hC₀, hC₀'⟩ := bmPotential_holder hn (c := c) (r := fun j => 2 * r j)
      hα hα1 (fun j => by linarith [hr j])
    refine ⟨C₀, hC₀, fun g hg hgs => ?_⟩
    have h := hC₀' g hg (fun j z hz => hgs j z (by
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩))
    rwa [show (fun j => 2 * r j / 2) = r from by funext j; ring] at h
  obtain ⟨C₁, hC₁, hiter⟩ := Work.CR.Flat.Cauchy.bmPotential_iter_bound hn hα hα1 hr k hbase
  obtain ⟨C₂, hC₂, htop⟩ := Work.CR.Flat.Cauchy.bmPotential_top_bound hn hα hα1 hr k hbase
  set K : ℝ := 2 * ((k : ℝ) + 1) * C₁ + 2 * C₂ with hK
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1, by positivity, ?_⟩
  intro η hη hsupp j
  set P : Set (Fin n → ℂ) := polydisc c (fun i => r i / 2) with hP
  set S : ℝ≥0∞ := ∑ l, holderNorm k α (η j l) Set.univ with hS
  have hsuppj : ∀ l z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → η j l z = 0 :=
    fun l z hz => hsupp j l z hz
  have hcs : ∀ l, HasCompactSupport (η j l) := fun l =>
    Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc hr (fun z hz => hsupp j l z hz)
  have hiterb : ∀ m, m ≤ k →
      (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
          (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal C₁ * S) ∧
      (holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
          (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal C₁ * S) := fun m hm =>
    hiter (fun l => η j l) (fun l => hη j l) hsuppj m hm
  have hlower : holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
      (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
    rw [holderNorm]
    calc ∑ m ∈ Finset.range (k + 1),
            (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
              (polydisc c (fun i => r i / 2))
              + holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
                (polydisc c (fun i => r i / 2)))
        ≤ ∑ _m ∈ Finset.range (k + 1), (ENNReal.ofReal (2 * C₁) * S) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          refine (add_le_add (hiterb m hmk).1 (hiterb m hmk).2).trans ?_
          rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₁) (le_of_lt hC₁),
            show C₁ + C₁ = 2 * C₁ from by ring]
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 * C₁) * S) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
          rw [← ENNReal.ofReal_natCast (k + 1), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          ring
  have htop' : iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
        (polydisc c (fun i => r i / 2))
      + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
        (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal (2 * C₂) * S := by
    have hh := htop (fun l => η j l) (fun l => hη j l) hsuppj
    refine (add_le_add hh.1 hh.2).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₂) (le_of_lt hC₂),
      show C₂ + C₂ = 2 * C₂ from by ring]
  have hbound : holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
      (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal K * S := by
    rw [Work.CR.Flat.Cauchy.holderNorm_succ k α
      (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l)) (polydisc c (fun i => r i / 2)), hK]
    calc holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
            (polydisc c (fun i => r i / 2))
          + (iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
              (polydisc c (fun i => r i / 2))
            + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
              (polydisc c (fun i => r i / 2)))
        ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S + ENNReal.ofReal (2 * C₂) * S :=
          add_le_add hlower htop'
      _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁ + 2 * C₂) * S := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hcd : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞)
      (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
      (polydisc c (fun i => r i / 2)) :=
    (Work.CR.Flat.Cauchy.contDiff_bmPotential_Ck hn k (fun l => hη j l) hcs).contDiffOn
  have hrow : bmRow η j = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
      • (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l)) := by
    funext z
    simp only [bmRow_apply, Pi.smul_apply, smul_eq_mul,
      Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  have hST : S ≤ ∑ l, ∑ m, holderNorm k α (η l m) Set.univ := by
    rw [hS]
    exact Finset.single_le_sum (f := fun l => ∑ m, holderNorm k α (η l m) Set.univ)
      (fun l _ => bot_le) (Finset.mem_univ j)
  rw [hrow, Work.CR.Flat.Holder.holderNorm_smul (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) hcd
    ((isOpen_polydisc c (fun i => r i / 2)).uniqueDiffOn), norm_neg]
  calc ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
        * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
          (polydisc c (fun i => r i / 2))
      ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (ENNReal.ofReal K * S) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K) * S := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1) * S :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) _
    _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1)
          * ∑ l, ∑ m, holderNorm k α (η l m) Set.univ :=
        mul_le_mul_right hST _

end Work.NN.Core
