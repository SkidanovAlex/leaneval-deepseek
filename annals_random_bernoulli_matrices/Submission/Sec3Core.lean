import Mathlib
import Submission.Threshold
import Submission.Helpers
import Submission.IntFun

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3 vocabulary: random averaging in ℓ₁(ℤ)

Tikhomirov 2020, Section 3.  The central objects:

- `wB ℓ p B := p^(B.card) · (1−p)^(ℓ−B.card)` — Bernoulli(p)-weight of the subset
  `B ⊆ {0..ℓ−1}` (probability that exactly the coordinates of `B` are hit);
- `subSum x B := Σ_{j ∈ B} xⱼ` — the weighted displacement;
- `avgF f p ℓ x t := Σ_{B ⊆ {0..ℓ−1}} wB · f(t + Σ_{j∈B} xⱼ)` — the averaged
  function `f_{A,p,ℓ}(t) := E_b f(t + Σ_{j≤ℓ} bⱼ xⱼ)` at the deterministic
  vector `x` (a realization of the `Xⱼ`'s).
-/

open scoped BigOperators

namespace Submission.Sec3

/-- Bernoulli-weight of the subset `B ⊆ {0..ℓ−1}`. -/
def wB (ℓ : ℕ) (p : unitInterval) (B : Finset (Fin ℓ)) : ℝ :=
  (p : ℝ) ^ B.card * (1 - (p : ℝ)) ^ (ℓ - B.card)

/-- Displacement of subset `B`. -/
def subSum {ℓ : ℕ} (x : Fin ℓ → ℤ) (B : Finset (Fin ℓ)) : ℤ := ∑ j ∈ B, x j

/-- The averaged function `f_{A,p,ℓ}` at the deterministic point `x`. -/
def avgF (f : ℤ → ℝ) (p : unitInterval) (ℓ : ℕ) (x : Fin ℓ → ℤ) : ℤ → ℝ :=
  fun t => ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * f (t + subSum x B)

/-- Weight sum over all subsets equals one (full probability). -/
lemma sum_wB_eq_one (ℓ : ℕ) (p : unitInterval) :
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) = 1 := by
  classical
  -- binomial identity: (p + (1−p))^ℓ = 1
  have hbin : (∑ j ∈ Finset.range (ℓ + 1),
      (ℓ.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (ℓ - j)) = 1 := by
    have h := add_pow (p : ℝ) (1 - (p : ℝ)) ℓ
    have h1 : (p : ℝ) + (1 - (p : ℝ)) = 1 := by ring
    calc
      (∑ j ∈ Finset.range (ℓ + 1),
          (ℓ.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (ℓ - j))
          = ∑ j ∈ Finset.range (ℓ + 1),
              (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (ℓ - j) * (ℓ.choose j : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (1 : ℝ) ^ ℓ := by
            rw [← h]
            rw [h1]
      _ = 1 := by simp
  -- partition into cardinality classes, evaluate each class
  calc
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B)
        = ∑ j ∈ Finset.range (ℓ + 1),
            (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard j, wB ℓ p B) := by
          simpa using (Finset.sum_powerset (Finset.univ : Finset (Fin ℓ)) (fun B => wB ℓ p B))
    _ = ∑ j ∈ Finset.range (ℓ + 1),
          (ℓ.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (ℓ - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simpa [wB, Finset.card_powersetCard, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
            using (Finset.sum_powersetCard j (Finset.univ : Finset (Fin ℓ))
              (fun c : ℕ => (p : ℝ) ^ c * (1 - (p : ℝ)) ^ (ℓ - c)))
    _ = 1 := hbin

/-- The weights are nonnegative. -/
lemma wB_nonneg (ℓ : ℕ) (p : unitInterval) (B : Finset (Fin ℓ)) : 0 ≤ wB ℓ p B := by
  unfold wB
  exact mul_nonneg (pow_nonneg p.property.1 _) (pow_nonneg (by linarith [p.property.2]) _)

/-- Mass of `avgF` over a finite window decomposes over subsets. -/
lemma avgF_window_mass {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (I : Finset ℤ) :
    (∑ t ∈ I, avgF f p ℓ x t) =
      ∑ t ∈ I, (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * f (t + subSum x B)) := by
  rfl

/-- For a single subset `B`, the translated window sum equals the sum of `f`
over the translated window (change of variables `s = t + d`). -/
lemma sum_translate_window {f : ℤ → ℝ} {ℓ : ℕ} {x : Fin ℓ → ℤ} (I : Finset ℤ)
    (B : Finset (Fin ℓ)) :
    (∑ t ∈ I, f (t + subSum x B)) = ∑ s ∈ I.image (fun t : ℤ => t + subSum x B), f s := by
  classical
  symm
  exact Finset.sum_image (f := f) (s := I) (g := fun t : ℤ => t + subSum x B) (by
    intro t₁ _ t₂ _ ht
    change t₁ + subSum x B = t₂ + subSum x B at ht
    omega)

/-- Mass of `avgF` over a window `I`, aggregated over the point `s = t + d`.
With `W` the (finite) union of all translates `J_B := I + d_B` and
`hit s := Σ_B wB·1[s ∈ J_B]`, we have `Σ_{t∈I} avgF(t) = Σ_{s∈W} f s · hit s`. -/
lemma avgF_aggregate {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    (I : Finset ℤ) :
    (∑ t ∈ I, avgF f p ℓ x t) =
      (∑ s ∈ (Finset.univ : Finset (Fin ℓ)).powerset.biUnion
          (fun B : Finset (Fin ℓ) => I.image (fun t : ℤ => t + subSum x B)),
        f s * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) := by
  classical
  let W : Finset ℤ := (Finset.univ : Finset (Fin ℓ)).powerset.biUnion
    (fun B : Finset (Fin ℓ) => I.image (fun t : ℤ => t + subSum x B))
  have hmemW : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      I.image (fun t : ℤ => t + subSum x B) ⊆ W := by
    intro B hB s hs
    dsimp [W]
    exact Finset.mem_biUnion.mpr ⟨B, hB, hs⟩
  -- per-subset identity: summing over W with the indicator equals the sum over the image
  have hind : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      (∑ s ∈ W, f s * (if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) =
        (∑ s ∈ I.image (fun t : ℤ => t + subSum x B), f s) := by
    intro B hB
    have hJW : I.image (fun t : ℤ => t + subSum x B) ⊆ W := hmemW B hB
    have hfilt : W.filter (fun s : ℤ => s ∈ I.image (fun t : ℤ => t + subSum x B)) =
        I.image (fun t : ℤ => t + subSum x B) := by
      ext s
      constructor
      · intro hs
        exact (Finset.mem_filter.mp hs).2
      · intro hs
        exact Finset.mem_filter.mpr ⟨hJW hs, hs⟩
    calc
      (∑ s ∈ W, f s * (if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0))
          = ∑ s ∈ W, (if s ∈ I.image (fun t : ℤ => t + subSum x B) then f s else 0) := by
            apply Finset.sum_congr rfl
            intro s hs
            by_cases hsJ : s ∈ I.image (fun t : ℤ => t + subSum x B) <;> simp [hsJ]
      _ = ∑ s ∈ W.filter (fun s : ℤ => s ∈ I.image (fun t : ℤ => t + subSum x B)), f s := by
            rw [Finset.sum_filter]
      _ = ∑ s ∈ I.image (fun t : ℤ => t + subSum x B), f s := by rw [hfilt]
  calc
    (∑ t ∈ I, avgF f p ℓ x t)
        = ∑ t ∈ I, ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * f (t + subSum x B) := by rfl
    _ = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, ∑ t ∈ I,
          wB ℓ p B * f (t + subSum x B) := by rw [Finset.sum_comm]
    _ = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * (∑ t ∈ I, f (t + subSum x B)) := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [Finset.mul_sum]
    _ = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * (∑ s ∈ W, f s * (if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [sum_translate_window I B, ← hind B hB]
    _ = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          ∑ s ∈ W, wB ℓ p B * (f s * (if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [Finset.mul_sum]
    _ = ∑ s ∈ W, ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * (f s * (if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ W, f s * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
          wB ℓ p B * if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          ring
    _ = (∑ s ∈ (Finset.univ : Finset (Fin ℓ)).powerset.biUnion
          (fun B : Finset (Fin ℓ) => I.image (fun t : ℤ => t + subSum x B)),
          f s * (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * if s ∈ I.image (fun t : ℤ => t + subSum x B) then 1 else 0)) := by
          dsimp [W]


/-- **Unpacking / lowering lemma for `avgF`**.  `avgF f p ℓ x t` is by
definition the subset-sum expectation `E_B wB(B)·f(t + Σ_{j∈B} xⱼ)`.  For a
nonnegative `f` that is `≥ a` on the "good" subsets (those whose displacement
`t + Σ_{j∈B} xⱼ` lies in `[-A, A]`), the averaged value at `t` is at least
`a` times the total Bernoulli weight of the good subsets. -/
lemma avgF_lower_subsetSum {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} {x : Fin ℓ → ℤ}
    {t : ℤ} {a A : ℝ}
    (hfpos : ∀ u : ℤ, 0 ≤ f u)
    (hgood : ∀ (B : Finset (Fin ℓ)),
        (|t + subSum x B| : ℝ) ≤ A → a ≤ f (t + subSum x B)) :
    a * (∑ B ∈ ((Finset.univ : Finset (Fin ℓ)).powerset.filter
          (fun B => (|t + subSum x B| : ℝ) ≤ A)), wB ℓ p B) ≤
      avgF f p ℓ x t := by
  classical
  let Good : Finset (Finset (Fin ℓ)) :=
    ((Finset.univ : Finset (Fin ℓ)).powerset).filter
      (fun B => (|t + subSum x B| : ℝ) ≤ A)
  have hsub : Good ⊆ (Finset.univ : Finset (Fin ℓ)).powerset := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hpos_tail : ∀ B : Finset (Fin ℓ), B ∈ (Finset.univ : Finset (Fin ℓ)).powerset →
      B ∉ Good → 0 ≤ wB ℓ p B * f (t + subSum x B) := by
    intro B hB hnot
    exact mul_nonneg (wB_nonneg ℓ p B) (hfpos (t + subSum x B))
  have hmain1 : (∑ B ∈ Good, wB ℓ p B * f (t + subSum x B)) ≤
      (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * f (t + subSum x B)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hpos_tail
  have hmain2 : a * (∑ B ∈ Good, wB ℓ p B) ≤ (∑ B ∈ Good, wB ℓ p B * f (t + subSum x B)) := by
    calc
      a * (∑ B ∈ Good, wB ℓ p B) = ∑ B ∈ Good, a * wB ℓ p B := by
            rw [Finset.mul_sum]
      _ = ∑ B ∈ Good, wB ℓ p B * a := by
            apply Finset.sum_congr rfl
            intro B hB
            ring
      _ ≤ ∑ B ∈ Good, wB ℓ p B * f (t + subSum x B) := by
            apply Finset.sum_le_sum
            intro B hB
            have hBgood : (|t + subSum x B| : ℝ) ≤ A := (Finset.mem_filter.mp hB).2
            have hfg : a ≤ f (t + subSum x B) := hgood B hBgood
            exact mul_le_mul_of_nonneg_left hfg (wB_nonneg ℓ p B)
  calc
    a * (∑ B ∈ Good, wB ℓ p B)
        ≤ (∑ B ∈ Good, wB ℓ p B * f (t + subSum x B)) := hmain2
    _ ≤ (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * f (t + subSum x B)) := hmain1
    _ = avgF f p ℓ x t := by rfl


/-- a nonnegative summable function is pointwise below its ℓ₁ mass. -/
lemma le_norm₁ {f : ℤ → ℝ} (hfpos : ∀ u : ℤ, 0 ≤ f u) (hf : Summable f) (u : ℤ) :
    f u ≤ IntFun.norm₁ f := by
  classical
  have hs := IntFun.Finset_sum_le_norm₁ hfpos hf ({u} : Finset ℤ)
  simpa using hs

/-- the averaged function is pointwise below the ℓ₁ mass of `f`
(averaging with nonnegative `f` cannot increase the sup above `‖f‖₁`). -/
lemma avgF_le_norm₁ {f : ℤ → ℝ} {p : unitInterval} (hfpos : ∀ u : ℤ, 0 ≤ f u)
    (hf : Summable f) (ℓ : ℕ) (x : Fin ℓ → ℤ) (t : ℤ) :
    avgF f p ℓ x t ≤ IntFun.norm₁ f := by
  have hpt : ∀ B : Finset (Fin ℓ),
      wB ℓ p B * f (t + subSum x B) ≤ wB ℓ p B * IntFun.norm₁ f := by
    intro B
    exact mul_le_mul_of_nonneg_left (le_norm₁ hfpos hf (t + subSum x B)) (wB_nonneg ℓ p B)
  calc
    avgF f p ℓ x t = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * f (t + subSum x B) := rfl
    _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * IntFun.norm₁ f := by
          exact Finset.sum_le_sum (fun B hB => hpt B)
    _ = IntFun.norm₁ f := by
          have hw : (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) = 1 := sum_wB_eq_one ℓ p
          calc
            (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B * IntFun.norm₁ f)
                = (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset, wB ℓ p B) * IntFun.norm₁ f := by
                  rw [Finset.sum_mul]
            _ = IntFun.norm₁ f := by rw [hw]; ring

end Submission.Sec3
