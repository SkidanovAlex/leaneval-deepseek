import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Prob

/-!
# Composition of independent Bernoulli rounds

`compose_union`: if `W` is Bernoulli-`a` (independent of `Y` which is Bernoulli-`s`),
then the law of `W ∪ Y` is Bernoulli with parameter `1 - (1-a)(1-s)`:

    (∑ W, Pmass a W · μ_s {Y | W ∪ Y ∈ A}) = μ_{1-(1-a)(1-s)} A.

This is the single-round composition identity needed for the layer identity
("union of Bernoulli rounds is Bernoulli") and for `Submission.PVIterP`.
-/

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.FET

attribute [local instance] Classical.propDecidable

namespace Submission
namespace OrMass

universe u
variable {X : Type u} [Fintype X]

lemma sum_indicator_ncard (A : Set (Set X)) :
    (∑ S : Set X, if S ∈ A then (1 : ℝ) else 0) = (A.ncard : ℝ) := by
  classical
  have hf : A.toFinset = (Finset.univ : Finset (Set X)).filter (fun S => S ∈ A) := by
    ext S
    by_cases hS : S ∈ A <;> simp [hS]
  calc
    (∑ S : Set X, if S ∈ A then (1 : ℝ) else 0)
        = ((Finset.univ : Finset (Set X)).filter (fun S => S ∈ A)).card := by
          rw [← Finset.sum_filter]
          simp
    _ = (A.ncard : ℝ) := by
          rw [← hf]
          rw [Set.ncard_eq_toFinset_card]
          simp

/-- the number of subsets of `s` with `ncard = j` is `s.ncard.choose j`. -/
lemma sum_slice_count (s : Set X) (j : ℕ) :
    (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0) = (s.ncard.choose j : ℝ) := by
  classical
  have hA : {T : Set X | T ⊆ s ∧ T.ncard = j}.ncard = (s.ncard.choose j : ℕ) := by
    simpa using (Set.ncard_powerset_ncard (s := s) (n := j) s.toFinite)
  calc
    (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0)
        = (({T : Set X | T ⊆ s ∧ T.ncard = j}).ncard : ℝ) := by
          rw [← sum_indicator_ncard]
          apply Finset.sum_congr rfl
          intro T hT
          by_cases h : T ⊆ s ∧ T.ncard = j <;> simp [h]
    _ = (s.ncard.choose j : ℝ) := by rw [hA]

/-- A sum over subsets of universe `U` that depends only on the size, sliced by size. -/
lemma subsetSum_eq (U : Set X) (w : ℕ → ℝ) :
    (∑ S : Set X, if S ⊆ U then w S.ncard else 0)
      = ∑ j ∈ Finset.range (U.ncard + 1), (U.ncard.choose j : ℝ) * w j := by
  classical
  have hsplit : ∀ S : Set X,
      (if S ⊆ U then w S.ncard else 0)
        = ∑ j ∈ Finset.range (U.ncard + 1), (if S ⊆ U ∧ S.ncard = j then w j else 0) := by
    intro S
    by_cases hSU : S ⊆ U
    · have hle : S.ncard ≤ U.ncard := Set.ncard_le_ncard hSU U.toFinite
      have hmem : S.ncard ∈ Finset.range (U.ncard + 1) := by
        simpa using (Nat.lt_succ_of_le hle)
      have hsum := Finset.sum_eq_single (s := Finset.range (U.ncard + 1)) (a := S.ncard)
        (f := fun j => (if S ⊆ U ∧ S.ncard = j then w j else 0))
        (by
          intro b hb hbne
          have hnot : ¬ S.ncard = b := fun h => hbne h.symm
          simp [hnot])
        (by simpa [hmem])
      simpa [hSU] using hsum.symm
    · simp [hSU]
  calc
    (∑ S : Set X, if S ⊆ U then w S.ncard else 0)
        = ∑ S : Set X, (∑ j ∈ Finset.range (U.ncard + 1),
            (if S ⊆ U ∧ S.ncard = j then w j else 0)) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hsplit S
    _ = ∑ j ∈ Finset.range (U.ncard + 1), (∑ S : Set X,
            (if S ⊆ U ∧ S.ncard = j then w j else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (U.ncard + 1), (U.ncard.choose j : ℝ) * w j := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (∑ S : Set X, (if S ⊆ U ∧ S.ncard = j then w j else 0))
                = (∑ S : Set X, w j * (if S ⊆ U ∧ S.ncard = j then (1 : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  by_cases h : S ⊆ U ∧ S.ncard = j <;> simp [h]
            _ = w j * (∑ S : Set X, if S ⊆ U ∧ S.ncard = j then (1 : ℝ) else 0) := by
                  rw [Finset.mul_sum]
            _ = w j * (U.ncard.choose j : ℝ) := by rw [sum_slice_count U j]
            _ = (U.ncard.choose j : ℝ) * w j := by ring

/-- Binomial theorem in the summed form. -/
lemma sum_binom (w : ℕ) (u v : ℝ) :
    ∑ m ∈ Finset.range (w + 1), (w.choose m : ℝ) * u ^ m * v ^ (w - m) = (u + v) ^ w := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- For `W ⊆ Z`, summing over `Y` with `W ∪ Y = Z` is the same as summing over `T ⊆ W`
of the set `(Z \ W) ∪ T`. -/
lemma sumY_eq_sumT (b : I) {Z W : Set X} (hWZ : W ⊆ Z) :
    (∑ Y : Set X, if W ∪ Y = Z then Pmass b Y else 0)
      = ∑ T : Set X, if T ⊆ W then Pmass b ((Z \ W) ∪ T) else 0 := by
  classical
  let s : Finset (Set X) := (Finset.univ : Finset (Set X)).filter (fun Y => W ∪ Y = Z)
  let t : Finset (Set X) := (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ W)
  have hbij : (∑ T ∈ t, Pmass b ((Z \ W) ∪ T)) = ∑ Y ∈ s, Pmass b Y := by
    unfold s t
    refine Finset.sum_bij (fun T hT => (Z \ W) ∪ T) ?_ ?_ ?_ ?_
    · intro T hT
      simp at hT ⊢
      have h1 : W ∪ (Z \ W) = Z := Set.union_sdiff_cancel hWZ
      rw [← Set.union_assoc, h1]
      exact Set.union_eq_self_of_subset_right (hT.trans hWZ)
    · intro T₁ hT₁ T₂ hT₂ h
      simp at hT₁ hT₂
      apply Set.Subset.antisymm
      · intro x hx
        have hxW : x ∈ W := hT₁ hx
        have hxZ : x ∈ (Z \ W) ∪ T₁ := by simpa using (Or.inr hx)
        have hx' : x ∈ (Z \ W) ∪ T₂ := by
          rw [h] at hxZ
          exact hxZ
        rcases hx' with hxZd | hxT2
        · exfalso
          exact hxZd.2 hxW
        · exact hxT2
      · intro x hx
        have hxW : x ∈ W := hT₂ hx
        have hxZ : x ∈ (Z \ W) ∪ T₂ := by simpa using (Or.inr hx)
        have hx' : x ∈ (Z \ W) ∪ T₁ := by
          rw [← h] at hxZ
          exact hxZ
        rcases hx' with hxZd | hxT1
        · exfalso
          exact hxZd.2 hxW
        · exact hxT1
    · intro Y hY
      simp at hY ⊢
      refine ⟨Y ∩ W, ?_, ?_⟩
      · intro x hx
        exact hx.2
      · -- (Z\W) ∪ (Y ∩ W) = Y, given hY : W ∪ Y = Z
        apply Set.Subset.antisymm
        · intro x hx
          rcases hx with hxd | hxy
          · have hxZ : x ∈ W ∪ Y := by simpa [hY] using hxd.1
            rcases hxZ with hxW | hxY
            · exfalso
              exact hxd.2 hxW
            · exact hxY
          · exact hxy.1
        · intro x hxY
          have hxZ : x ∈ W ∪ Y := Or.inr hxY
          have hxZW : x ∈ Z := by simpa [hY] using hxZ
          by_cases hxW : x ∈ W
          · exact Or.inr ⟨hxY, hxW⟩
          · exact Or.inl ⟨hxZW, hxW⟩
    · intro T hT
      rfl
  calc
    (∑ Y : Set X, if W ∪ Y = Z then Pmass b Y else 0)
        = ∑ Y ∈ s, Pmass b Y := by
          rw [Finset.sum_filter]
    _ = ∑ T ∈ t, Pmass b ((Z \ W) ∪ T) := hbij.symm
    _ = ∑ T : Set X, if T ⊆ W then Pmass b ((Z \ W) ∪ T) else 0 := by
          rw [Finset.sum_filter]

/-- Value of the inner T-sum (i.e. the Y-sum for a fixed `W ⊆ Z`). -/
lemma inner_sum_value (b : I) {Z W : Set X} (hWZ : W ⊆ Z) :
    (∑ T : Set X, if T ⊆ W then Pmass b ((Z \ W) ∪ T) else 0)
    = (b : ℝ) ^ (Z.ncard - W.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard) := by
  classical
  let n := Fintype.card X
  let m := (Z \ W).ncard
  let w := W.ncard
  have hz : Z.ncard = m + w := by
    unfold m w
    exact (Set.ncard_sdiff_add_ncard_of_subset hWZ).symm
  have hzle : Z.ncard ≤ n := by
    unfold n
    simpa using (Set.ncard_le_ncard (s := Z) (t := (univ : Set X))
        (by intro x hx; simp) (by simp))
  have hmw : m + w ≤ n := by omega
  let f : ℕ → ℝ := fun l => (b : ℝ) ^ (m + l) * (1 - (b : ℝ)) ^ ((n - m) - l)
  have hf (T : Set X) (hT : T ⊆ W) : Pmass b ((Z \ W) ∪ T) = f T.ncard := by
    unfold Pmass f
    have hd : Disjoint (Z \ W) T := by
      exact (disjoint_sdiff_left.mono_right hT)
    have hc : ((Z \ W) ∪ T).ncard = m + T.ncard := by
      unfold m
      exact Set.ncard_union_eq hd
    have hsub : (1 - (b : ℝ)) ^ (Fintype.card X - (m + T.ncard))
        = (1 - (b : ℝ)) ^ ((n - m) - T.ncard) := by
      congr 1
      unfold n
      omega
    rw [hc, hsub]
  calc
    (∑ T : Set X, if T ⊆ W then Pmass b ((Z \ W) ∪ T) else 0)
        = ∑ T : Set X, if T ⊆ W then f T.ncard else 0 := by
          apply Finset.sum_congr rfl
          intro T hT
          by_cases hTW : T ⊆ W
          · rw [if_pos hTW, if_pos hTW, hf T hTW]
          · simp [hTW]
    _ = ∑ l ∈ Finset.range (w + 1), (w.choose l : ℝ) * f l := by
          exact subsetSum_eq W f
    _ = (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard) := by
          have hterm : ∀ l ∈ Finset.range (w + 1), (w.choose l : ℝ) * f l
              = (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard)
                  * ((w.choose l : ℝ) * (b : ℝ) ^ l * (1 - (b : ℝ)) ^ (w - l)) := by
            intro l hl
            have hlw : l ≤ w := by
              have hlt : l < w + 1 := Finset.mem_range.mp (by simpa using hl)
              omega
            have he : (n - m) - l = (n - Z.ncard) + (w - l) := by
              rw [hz]
              omega
            unfold f
            rw [pow_add]
            rw [he]
            rw [pow_add]
            ring
          calc
            (∑ l ∈ Finset.range (w + 1), (w.choose l : ℝ) * f l)
                = ∑ l ∈ Finset.range (w + 1),
                    (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard)
                      * ((w.choose l : ℝ) * (b : ℝ) ^ l * (1 - (b : ℝ)) ^ (w - l)) := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  exact hterm l hl
            _ = (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard)
                  * (∑ l ∈ Finset.range (w + 1),
                      (w.choose l : ℝ) * (b : ℝ) ^ l * (1 - (b : ℝ)) ^ (w - l)) := by
                  rw [← Finset.mul_sum]
            _ = (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard) * (b + (1 - (b : ℝ))) ^ w := by
                  rw [sum_binom]
          have hb : (b : ℝ) + (1 - (b : ℝ)) = 1 := by ring
          rw [show (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard) * (b + (1 - (b : ℝ))) ^ w
              = (b : ℝ) ^ m * (1 - (b : ℝ)) ^ (n - Z.ncard) by
                rw [hb]
                simp]
    _ = (b : ℝ) ^ (Z.ncard - W.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard) := by
          have hm : m = Z.ncard - W.ncard := by
            change (Z \ W).ncard = Z.ncard - W.ncard
            exact Set.ncard_sdiff' hWZ Z.toFinite
          simpa [hm, n]

/-- If `W ⊄ Z` then no `Y` satisfies `W ∪ Y = Z`. -/
lemma innerY_zero_of_not_subset {Z W : Set X} (h : ¬ W ⊆ Z) (b : I) :
    (∑ Y : Set X, if W ∪ Y = Z then Pmass b Y else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro Y hY
  have hne : ¬ W ∪ Y = Z := by
    intro hEq
    apply h
    intro x hxW
    have : x ∈ W ∪ Y := by exact Or.inl hxW
    rwa [hEq] at this
  simp [hne]

/-- OR-composition of Bernoulli laws (point-mass closed form). -/
lemma or_mass_value (a b : I) (Z : Set X) :
    (∑ W : Set X, ∑ Y : Set X, if W ∪ Y = Z then Pmass a W * Pmass b Y else 0)
    = (1 - (a : ℝ)) ^ (Fintype.card X - Z.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard)
      * ((a : ℝ) + (1 - (a : ℝ)) * (b : ℝ)) ^ Z.ncard := by
  classical
  let n := Fintype.card X
  let z := Z.ncard
  have hzle : z ≤ n := by
    unfold n z
    simpa using (Set.ncard_le_ncard (s := Z) (t := (univ : Set X))
        (by intro x hx; simp) (by simp))
  let g : ℕ → ℝ := fun j => (a : ℝ) ^ j * (1 - (a : ℝ)) ^ (n - j) * (b : ℝ) ^ (z - j)
      * (1 - (b : ℝ)) ^ (n - z)
  have hg : ∀ W : Set X, W ⊆ Z →
      Pmass a W * ((b : ℝ) ^ (Z.ncard - W.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard))
        = g W.ncard := by
    intro W hWZ
    unfold Pmass
    dsimp [g, n, z]
    ring
  calc
    (∑ W : Set X, ∑ Y : Set X, if W ∪ Y = Z then Pmass a W * Pmass b Y else 0)
        = ∑ W : Set X, Pmass a W * (∑ Y : Set X, if W ∪ Y = Z then Pmass b Y else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Y hY
          by_cases h : W ∪ Y = Z <;> simp [h]
    _ = ∑ W : Set X, (if W ⊆ Z
          then Pmass a W * (∑ Y : Set X, if W ∪ Y = Z then Pmass b Y else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hWZ : W ⊆ Z
          · simp [hWZ]
          · rw [if_neg hWZ]
            rw [innerY_zero_of_not_subset hWZ b]
            ring
    _ = ∑ W : Set X, (if W ⊆ Z
          then Pmass a W * (∑ T : Set X, if T ⊆ W then Pmass b ((Z \ W) ∪ T) else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hWZ : W ⊆ Z
          · rw [if_pos hWZ, if_pos hWZ]
            rw [sumY_eq_sumT b hWZ]
          · simp [hWZ]
    _ = ∑ W : Set X, (if W ⊆ Z
          then Pmass a W * ((b : ℝ) ^ (Z.ncard - W.ncard)
            * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard)) else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hWZ : W ⊆ Z
          · rw [if_pos hWZ, if_pos hWZ]
            rw [inner_sum_value b hWZ]
          · simp [hWZ]
    _ = ∑ W : Set X, if W ⊆ Z then g W.ncard else 0 := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hWZ : W ⊆ Z
          · rw [if_pos hWZ, if_pos hWZ]
            exact hg W hWZ
          · simp [hWZ]
    _ = ∑ j ∈ Finset.range (z + 1), (z.choose j : ℝ) * g j := by
          exact subsetSum_eq Z g
    _ = (1 - (a : ℝ)) ^ (n - z) * (1 - (b : ℝ)) ^ (n - z)
        * ((a : ℝ) + (1 - (a : ℝ)) * (b : ℝ)) ^ z := by
          have hterm : ∀ j ∈ Finset.range (z + 1),
              (1 - (a : ℝ)) ^ (n - z) * (1 - (b : ℝ)) ^ (n - z)
                  * ((z.choose j : ℝ) * (a : ℝ) ^ j * ((1 - (a : ℝ)) * (b : ℝ)) ^ (z - j))
                = (z.choose j : ℝ) * g j := by
            intro j hj
            have hjl : j ≤ z := by
              have : j < z + 1 := Finset.mem_range.mp (by simpa using hj)
              omega
            have he : n - j = (n - z) + (z - j) := by omega
            unfold g
            rw [mul_pow]
            rw [he]
            rw [pow_add]
            ring
          calc
            (∑ j ∈ Finset.range (z + 1), (z.choose j : ℝ) * g j)
                = ∑ j ∈ Finset.range (z + 1),
                    (1 - (a : ℝ)) ^ (n - z) * (1 - (b : ℝ)) ^ (n - z)
                      * ((z.choose j : ℝ) * (a : ℝ) ^ j * ((1 - (a : ℝ)) * (b : ℝ)) ^ (z - j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact (hterm j hj).symm
            _ = (1 - (a : ℝ)) ^ (n - z) * (1 - (b : ℝ)) ^ (n - z)
                * (∑ j ∈ Finset.range (z + 1),
                    (z.choose j : ℝ) * (a : ℝ) ^ j * ((1 - (a : ℝ)) * (b : ℝ)) ^ (z - j)) := by
                  rw [← Finset.mul_sum]
            _ = (1 - (a : ℝ)) ^ (n - z) * (1 - (b : ℝ)) ^ (n - z)
                * ((a : ℝ) + (1 - (a : ℝ)) * (b : ℝ)) ^ z := by
                  rw [sum_binom]
    _ = (1 - (a : ℝ)) ^ (Fintype.card X - Z.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard)
        * ((a : ℝ) + (1 - (a : ℝ)) * (b : ℝ)) ^ Z.ncard := by
          dsimp [n, z]

/-- `mu` as an explicit sum over all subsets. -/
lemma mu_eq_sum_all (p : I) (A : Set (Set X)) :
    mu p A = ∑ S : Set X, if S ∈ A then Pmass p S else 0 := by
  classical
  rw [mu_eq_sum p A]
  have hset : A.toFinite.toFinset = (Finset.univ : Finset (Set X)).filter (fun S => S ∈ A) := by
    ext S
    by_cases hS : S ∈ A <;> simp [hS]
  rw [hset]
  rw [Finset.sum_filter]

/-- OR-composition of Bernoulli laws (point-mass form). -/
lemma or_mass (a b : I) (Z : Set X) :
    (∑ W : Set X, ∑ Y : Set X,
        if W ∪ Y = Z then Pmass a W * Pmass b Y else 0)
      = Pmass (⟨1 - (1 - (a : ℝ)) * (1 - (b : ℝ)), by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (b : ℝ) := sub_nonneg.mpr b.2.2
          have h1' : 1 - (a : ℝ) ≤ 1 := by linarith [a.2.1]
          have h2' : 1 - (b : ℝ) ≤ 1 := by linarith [b.2.1]
          have hp : (1 - (a : ℝ)) * (1 - (b : ℝ)) ≤ 1 := by
            nlinarith [mul_nonneg h1 h2]
          linarith, by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (b : ℝ) := sub_nonneg.mpr b.2.2
          linarith [mul_nonneg h1 h2]⟩ : I) Z := by
  classical
  rw [or_mass_value]
  change (1 - (a : ℝ)) ^ (Fintype.card X - Z.ncard) * (1 - (b : ℝ)) ^ (Fintype.card X - Z.ncard)
        * ((a : ℝ) + (1 - (a : ℝ)) * (b : ℝ)) ^ Z.ncard
      = (1 - (1 - (a : ℝ)) * (1 - (b : ℝ))) ^ Z.ncard *
          (1 - (1 - (1 - (a : ℝ)) * (1 - (b : ℝ)))) ^ (Fintype.card X - Z.ncard)
  let c : ℝ := 1 - (1 - (a : ℝ)) * (1 - (b : ℝ))
  rw [show 1 - (1 - (a : ℝ)) * (1 - (b : ℝ)) = c by rfl]
  have hc : (a : ℝ) + (1 - (a : ℝ)) * (b : ℝ) = c := by
    dsimp [c]
    ring
  have h1c : (1 - (a : ℝ)) * (1 - (b : ℝ)) = 1 - c := by
    dsimp [c]
    ring
  rw [← mul_pow]
  rw [h1c]
  rw [hc]
  ring

/-- reorder a triple sum over `Set X`. -/
lemma sum3_comm (f : Set X → Set X → Set X → ℝ) :
    (∑ W : Set X, ∑ Y : Set X, ∑ Z : Set X, f W Y Z)
      = ∑ Z : Set X, ∑ W : Set X, ∑ Y : Set X, f W Y Z := by
  classical
  calc
    (∑ W : Set X, ∑ Y : Set X, ∑ Z : Set X, f W Y Z)
        = ∑ p : Set X × Set X, ∑ Z : Set X, f p.1 p.2 Z := by
          rw [← Fintype.sum_prod_type' (f := fun W Y => (∑ Z : Set X, f W Y Z))]
    _ = ∑ Z : Set X, ∑ p : Set X × Set X, f p.1 p.2 Z := by
          rw [Finset.sum_comm]
    _ = ∑ Z : Set X, ∑ W : Set X, ∑ Y : Set X, f W Y Z := by
          apply Finset.sum_congr rfl
          intro Z hZ
          rw [Fintype.sum_prod_type (f := fun p : Set X × Set X => f p.1 p.2 Z)]

/-- `mu` of `{Y | W ∪ Y ∈ A}` as an explicit sum. -/
lemma mu_union_sum (p : I) (A : Set (Set X)) (W : Set X) :
    mu p {Y | W ∪ Y ∈ A} = ∑ Y : Set X, if W ∪ Y ∈ A then Pmass p Y else 0 := by
  classical
  rw [mu_eq_sum_all]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases h : W ∪ Y ∈ A <;> simp [h]

/-- OR-composition of Bernoulli laws (measure form):
    pushing a Bernoulli-`a` round through an independent Bernoulli-`s` rest. -/
lemma compose_union (a s : I) (A : Set (Set X)) :
    (∑ W : Set X, Pmass a W * mu s {Y | W ∪ Y ∈ A})
      = mu (⟨1 - (1 - (a : ℝ)) * (1 - (s : ℝ)), by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
          have h1' : 1 - (a : ℝ) ≤ 1 := by linarith [a.2.1]
          have h2' : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
          have hp : (1 - (a : ℝ)) * (1 - (s : ℝ)) ≤ 1 := by
            nlinarith [mul_nonneg h1 h2]
          linarith, by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
          linarith [mul_nonneg h1 h2]⟩ : I) A := by
  classical
  have hfix : ∀ W Y : Set X,
      (∑ Z : Set X, if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0)
        = if W ∪ Y ∈ A then Pmass a W * Pmass s Y else 0 := by
    intro W Y
    have hsum := Finset.sum_eq_single (s := (Finset.univ : Finset (Set X))) (a := W ∪ Y)
      (f := fun Z : Set X => if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0)
      (by
        intro b hb hbne
        simp [hbne])
      (by simp)
    simpa using hsum
  calc
    (∑ W : Set X, Pmass a W * mu s {Y | W ∪ Y ∈ A})
        = ∑ W : Set X, ∑ Y : Set X, if W ∪ Y ∈ A then Pmass a W * Pmass s Y else 0 := by
          apply Finset.sum_congr rfl
          intro W hW
          rw [mu_union_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Y hY
          by_cases h : W ∪ Y ∈ A <;> simp [h]
    _ = ∑ W : Set X, ∑ Y : Set X,
          (∑ Z : Set X, if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          apply Finset.sum_congr rfl
          intro Y hY
          rw [← hfix W Y]
    _ = ∑ Z : Set X, ∑ W : Set X, ∑ Y : Set X,
          if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0 := by
          rw [show (∑ W : Set X, ∑ Y : Set X, ∑ Z : Set X,
                  if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0)
                = ∑ Z : Set X, ∑ W : Set X, ∑ Y : Set X,
                  if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0 by
                exact sum3_comm (fun W Y Z : Set X =>
                  if Z ∈ A ∧ Z = W ∪ Y then Pmass a W * Pmass s Y else 0)]
    _ = ∑ Z : Set X, if Z ∈ A then
          (∑ W : Set X, ∑ Y : Set X, if W ∪ Y = Z then Pmass a W * Pmass s Y else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro Z hZ
          by_cases hZA : Z ∈ A
          · rw [if_pos hZA]
            apply Finset.sum_congr rfl
            intro W hW
            apply Finset.sum_congr rfl
            intro Y hY
            by_cases hEq : Z = W ∪ Y
            · rw [if_pos (by exact ⟨hZA, hEq⟩)]
              rw [if_pos hEq.symm]
            · rw [if_neg (by intro h; exact hEq h.2)]
              rw [if_neg (by intro h; exact hEq h.symm)]
          · rw [if_neg hZA]
            apply Finset.sum_eq_zero
            intro W hW
            apply Finset.sum_eq_zero
            intro Y hY
            rw [if_neg (by intro h; exact hZA h.1)]
    _ = ∑ Z : Set X, if Z ∈ A then Pmass
          (⟨1 - (1 - (a : ℝ)) * (1 - (s : ℝ)), by
            have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
            have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
            have h1' : 1 - (a : ℝ) ≤ 1 := by linarith [a.2.1]
            have h2' : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
            have hp : (1 - (a : ℝ)) * (1 - (s : ℝ)) ≤ 1 := by
              nlinarith [mul_nonneg h1 h2]
            linarith, by
            have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
            have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
            linarith [mul_nonneg h1 h2]⟩ : I) Z else 0 := by
          apply Finset.sum_congr rfl
          intro Z hZ
          by_cases hZA : Z ∈ A <;> simp [hZA, or_mass a s Z]
    _ = mu (⟨1 - (1 - (a : ℝ)) * (1 - (s : ℝ)), by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
          have h1' : 1 - (a : ℝ) ≤ 1 := by linarith [a.2.1]
          have h2' : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
          have hp : (1 - (a : ℝ)) * (1 - (s : ℝ)) ≤ 1 := by
            nlinarith [mul_nonneg h1 h2]
          linarith, by
          have h1 : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr a.2.2
          have h2 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
          linarith [mul_nonneg h1 h2]⟩ : I) A := by
          rw [mu_eq_sum_all]

end OrMass
end Submission


