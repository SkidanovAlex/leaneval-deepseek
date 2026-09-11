import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Chain12
import Submission.Binom
import Submission.Binom2

/-!
# Ratio: for sup-type processes the average over N-subsets dominates (N/w)·(average over w-subsets).

PROVE all declarations below (no unfinished proofs).  Add helpers as needed in this file.
Everything is classical finite combinatorics over a finite type `X`.

CONVENTIONS:
- `levelFs k` : the Finset of all `Finset X` of cardinal `k`.
- `fsum h k`, `favg h k` : sum / average of `h` over `levelFs k`.
- `sumW lam S W` and `supFW lam F W` are from `Submission.Chain12`:
    sumW lam S W  = Σ_{i ∈ (W∩S)} lam S i    (W is a Set X)
    supFW lam F W = famSup (fun S => sumW lam S W) F  (0 if F empty).
  For a Finset u, write `(↑u : Set X)` for its coercion; `sumW lam S (↑u) = (u.filter (· ∈ S)).sum (lam S)`.

GOAL of the file (`sizeAvg_ratio`): if the weights are nonnegative and N ≤ w ≤ n then
    (N : ℝ) * Binom.sizeAvg (supFW lam F) w ≤ (w : ℝ) * Binom.sizeAvg (supFW lam F) N.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Ratio

open Frame
open Sel
open Sel.Deep
open Sel.Deep.Sys
open Chain12

variable {X : Type*} [Fintype X]

noncomputable def levelFs (X : Type*) [Fintype X] (k : ℕ) : Finset (Finset X) :=
  (Finset.univ : Finset X).powersetCard k

lemma mem_levelFs (u : Finset X) (k : ℕ) : u ∈ levelFs X k ↔ u.card = k := by
  classical
  rw [levelFs, Finset.mem_powersetCard]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨(by intro x hx; exact Finset.mem_univ x), h⟩

lemma levelFs_card (k : ℕ) : (levelFs X k).card = (Fintype.card X).choose k := by
  classical
  rw [levelFs, Finset.card_powersetCard, Finset.card_univ]

lemma levelFs_nonempty (k : ℕ) (hk : k ≤ Fintype.card X) : (levelFs X k).Nonempty := by
  classical
  apply (Finset.card_pos).1
  rw [levelFs_card k]
  exact Nat.choose_pos hk

noncomputable def fsum (h : Finset X → ℝ) (k : ℕ) : ℝ := ∑ u ∈ levelFs X k, h u

noncomputable def favg (h : Finset X → ℝ) (k : ℕ) : ℝ :=
  fsum h k / ((levelFs X k).card : ℝ)

lemma sumW_eq_filter_sum (lam : Set X → X → ℝ) (S : Set X) (u : Finset X) :
    sumW lam S (↑u : Set X) = (u.filter (fun i : X => i ∈ S)).sum (fun i : X => lam S i) := by
  classical
  unfold sumW
  congr 1
  ext i
  simp

lemma sumW_erase_mem (lam : Set X → X → ℝ) (S : Set X) (u : Finset X) {i : X} (hi : i ∈ u) :
    sumW lam S (↑(u.erase i) : Set X) = (u.filter (fun j : X => j ∈ S ∧ j ≠ i)).sum (fun j : X => lam S j) := by
  classical
  rw [sumW_eq_filter_sum]
  congr 1
  ext j
  simp
  tauto

lemma count_ne_sum (u : Finset X) (j : X) (hj : j ∈ u) (c : ℝ) :
    (∑ i ∈ u, if i = j then 0 else c) = c * ((u.card : ℝ) - 1) := by
  calc
    (∑ i ∈ u, if i = j then 0 else c)
        = ∑ i ∈ u, (c - if i = j then c else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hij : i = j <;> simp [hij]
    _ = (∑ i ∈ u, c) - (∑ i ∈ u, if i = j then c else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = c * (u.card : ℝ) - c := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [Finset.sum_ite_eq' (s := u) (a := j) (b := fun _ => c)]
            simp [hj]
            ring
    _ = c * ((u.card : ℝ) - 1) := by ring

lemma erase_sum_linear (lam : Set X → X → ℝ) (S : Set X) (u : Finset X) :
    (∑ i ∈ u, sumW lam S (↑(u.erase i) : Set X)) =
      ((u.card : ℝ) - 1) * sumW lam S (↑u : Set X) := by
  classical
  let a : X → ℝ := fun j => lam S j
  let A : Finset X := u.filter (fun j : X => j ∈ S)
  have hA : A ⊆ u := by intro j hj; exact (Finset.mem_filter.mp hj).1
  have hR : sumW lam S (↑u : Set X) = A.sum a := by
    rw [sumW_eq_filter_sum]
  have hAf (i : X) : u.filter (fun j : X => j ∈ S ∧ j ≠ i) = A.filter (fun j : X => j ≠ i) := by
    simp [A, Finset.filter_filter]
  calc
    (∑ i ∈ u, sumW lam S (↑(u.erase i) : Set X))
        = ∑ i ∈ u, (u.filter (fun j : X => j ∈ S ∧ j ≠ i)).sum a := by
            apply Finset.sum_congr rfl
            intro i hi
            exact sumW_erase_mem lam S u hi
    _ = ∑ i ∈ u, (A.filter (fun j : X => j ≠ i)).sum a := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hAf i]
    _ = ∑ i ∈ u, ∑ j ∈ A, (if j ≠ i then a j else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_filter]
    _ = ∑ j ∈ A, ∑ i ∈ u, (if j ≠ i then a j else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ j ∈ A, a j * ((u.card : ℝ) - 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hcount : (∑ i ∈ u, if j ≠ i then a j else 0) = a j * ((u.card : ℝ) - 1) := by
              calc
                (∑ i ∈ u, if j ≠ i then a j else 0) = ∑ i ∈ u, if i = j then 0 else a j := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      by_cases hij : i = j
                      · simp [hij]
                      · have hji : j ≠ i := fun h => hij h.symm
                        simp [hij, hji]
                _ = a j * ((u.card : ℝ) - 1) := count_ne_sum u j (hA hj) (a j)
            exact hcount
    _ = ((u.card : ℝ) - 1) * A.sum a := by
            rw [← Finset.sum_mul]
            rw [mul_comm]
    _ = ((u.card : ℝ) - 1) * sumW lam S (↑u : Set X) := by
            rw [hR]

lemma supFW_ge_zero {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (W : Set X) : 0 ≤ supFW lam F W :=
  supFW_nonneg hnonneg W

lemma famSup_eq_of_mem {v : Set X → ℝ} {F : Set (Set X)}
    (hne : (F.toFinset.image v).Nonempty) : ∃ S ∈ F, v S = famSup v F := by
  classical
  unfold famSup
  rw [dif_pos hne]
  have hmem : (F.toFinset.image v).max' hne ∈ (F.toFinset.image v) := Finset.max'_mem _ _
  rcases (Finset.mem_image).1 hmem with ⟨S, hSF, hS⟩
  refine ⟨S, (Set.mem_toFinset).1 hSF, hS⟩

lemma supFW_erase_sum {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (W : Finset X) :
    ((W.card : ℝ) - 1) * supFW lam F (↑W : Set X) ≤
      ∑ i ∈ W, supFW lam F (↑(W.erase i) : Set X) := by
  classical
  by_cases hA : (F.toFinset.image (fun S : Set X => sumW lam S (↑W : Set X))).Nonempty
  · rcases famSup_eq_of_mem (v := fun S : Set X => sumW lam S (↑W : Set X)) (F := F) hA with ⟨S0, hS0F, hS0⟩
    calc
      ((W.card : ℝ) - 1) * supFW lam F (↑W : Set X)
          = ((W.card : ℝ) - 1) * sumW lam S0 (↑W : Set X) := by
              rw [supFW, ← hS0]
      _ = ∑ i ∈ W, sumW lam S0 (↑(W.erase i) : Set X) := by
              exact (erase_sum_linear lam S0 W).symm
      _ ≤ ∑ i ∈ W, supFW lam F (↑(W.erase i) : Set X) := by
              exact Finset.sum_le_sum (by
                intro i hi
                exact le_famSup (v := fun T : Set X => sumW lam T (↑(W.erase i) : Set X)) hS0F)
  · have hfam0 : supFW lam F (↑W : Set X) = 0 := by
      unfold supFW famSup
      simp [hA]
    rw [hfam0]
    have hsum0 : 0 ≤ ∑ i ∈ W, supFW lam F (↑(W.erase i) : Set X) := by
      exact Finset.sum_nonneg (fun i hi => supFW_nonneg hnonneg (↑(W.erase i) : Set X))
    simpa using hsum0

lemma sum_W_erase_eq (h : Finset X → ℝ) (k : ℕ) (hk0 : 0 < k) :
    (∑ W ∈ levelFs X k, ∑ i ∈ W, h (W.erase i)) =
      ((Fintype.card X : ℝ) - (k : ℝ) + 1) * fsum h (k - 1) := by
  classical
  let D : Finset (Σ _ : Finset X, X) := (levelFs X k).sigma (fun W : Finset X => W)
  let E : Finset (Σ _ : Finset X, X) := (levelFs X (k - 1)).sigma
    (fun T : Finset X => (Finset.univ : Finset X).filter (fun x : X => x ∉ T))
  have hsumD : (∑ W ∈ levelFs X k, ∑ i ∈ W, h (W.erase i)) = ∑ p ∈ D, h (p.1.erase p.2) := by
    dsimp [D]
    rw [Finset.sum_sigma]
  have hsumE : (∑ T ∈ levelFs X (k - 1), ∑ x ∈ (Finset.univ : Finset X).filter (fun x : X => x ∉ T), h T)
      = ∑ p ∈ E, h p.1 := by
    dsimp [E]
    rw [Finset.sum_sigma]
  calc
    (∑ W ∈ levelFs X k, ∑ i ∈ W, h (W.erase i)) = ∑ p ∈ D, h (p.1.erase p.2) := hsumD
    _ = ∑ p ∈ E, h p.1 := by
          let φ : (Σ _ : Finset X, X) → (Σ _ : Finset X, X) := fun p => ⟨p.1.erase p.2, p.2⟩
          let ψ : (Σ _ : Finset X, X) → (Σ _ : Finset X, X) := fun q => ⟨insert q.2 q.1, q.2⟩
          refine Finset.sum_bij (s := D) (t := E) (f := fun p => h (p.1.erase p.2))
            (g := fun q => h q.1) (fun p hp => φ p) ?_ ?_ ?_ ?_
          · intro p hp
            have hpD : p.1 ∈ levelFs X k ∧ p.2 ∈ p.1 := by
              simpa [D] using (Finset.mem_sigma.mp hp)
            have hcard : (p.1.erase p.2).card = k - 1 := by
              rw [Finset.card_erase_of_mem hpD.2, (mem_levelFs p.1 k).mp hpD.1]
            dsimp [φ, E]
            rw [Finset.mem_sigma]
            constructor
            · exact (mem_levelFs (p.1.erase p.2) (k - 1)).mpr hcard
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ p.2, Finset.notMem_erase p.2 p.1⟩
          · intro p₁ hp₁ p₂ hp₂ hEq
            rcases p₁ with ⟨W₁, i₁⟩
            rcases p₂ with ⟨W₂, i₂⟩
            dsimp [φ] at hEq
            simp at hEq
            rcases hEq with ⟨hW, hi⟩
            subst i₂
            have hi₁ : i₁ ∈ W₁ := by
              simpa [D] using (Finset.mem_sigma.mp hp₁) |>.2
            have hi₂ : i₁ ∈ W₂ := by
              simpa [D] using (Finset.mem_sigma.mp hp₂) |>.2
            congr 1
            calc
              W₁ = insert i₁ (W₁.erase i₁) := (Finset.insert_erase hi₁).symm
              _ = insert i₁ (W₂.erase i₁) := by rw [hW]
              _ = W₂ := Finset.insert_erase hi₂
          · intro q hq
            have hqE : q.1 ∈ levelFs X (k - 1) ∧ q.2 ∈ (Finset.univ : Finset X).filter (fun x : X => x ∉ q.1) := by
              simpa [E] using (Finset.mem_sigma.mp hq)
            have hqx : q.2 ∉ q.1 := (Finset.mem_filter.mp hqE.2).2
            have hcard : (insert q.2 q.1).card = k := by
              rw [Finset.card_insert_of_notMem hqx, (mem_levelFs q.1 (k - 1)).mp hqE.1]
              omega
            refine ⟨ψ q, ?_, ?_⟩
            · dsimp [ψ, D]
              rw [Finset.mem_sigma]
              constructor
              · exact (mem_levelFs (insert q.2 q.1) k).mpr hcard
              · exact Finset.mem_insert_self q.2 q.1
            · dsimp [φ, ψ]
              rw [Finset.erase_insert hqx]
          · intro p hp
            rfl
    _ = ∑ T ∈ levelFs X (k - 1), ∑ x ∈ (Finset.univ : Finset X).filter (fun x : X => x ∉ T), h T := hsumE.symm
    _ = ((Fintype.card X : ℝ) - (k : ℝ) + 1) * fsum h (k - 1) := by
          let cnt : Finset X → ℕ := fun T => ((Finset.univ : Finset X).filter (fun x : X => x ∉ T)).card
          have hcnt (T : Finset X) (hT : T ∈ levelFs X (k - 1)) :
              (cnt T : ℝ) = (Fintype.card X : ℝ) - (k : ℝ) + 1 := by
            have hTk : T.card = k - 1 := (mem_levelFs T (k - 1)).mp hT
            have hTsub : T ⊆ (Finset.univ : Finset X) := by intro x hx; exact Finset.mem_univ x
            have hcardf : ((Finset.univ : Finset X).filter (fun x : X => x ∉ T)).card = Fintype.card X - T.card := by
              rw [show (Finset.univ : Finset X).filter (fun x : X => x ∉ T) = (Finset.univ : Finset X) \ T by
                ext x
                simp]
              rw [Finset.card_sdiff_of_subset hTsub, Finset.card_univ]
            have hTsub2 : (k - 1 : ℕ) ≤ Fintype.card X := by
              calc
                (k - 1) = T.card := hTk.symm
                _ ≤ Fintype.card X := by
                    rw [← Finset.card_univ]
                    exact Finset.card_le_card hTsub
            have hk1 : 1 ≤ k := hk0
            dsimp [cnt]
            rw [hcardf, hTk, Nat.cast_sub hTsub2, Nat.cast_sub hk1]
            ring
          calc
            (∑ T ∈ levelFs X (k - 1), ∑ x ∈ (Finset.univ : Finset X).filter (fun x : X => x ∉ T), h T)
                = ∑ T ∈ levelFs X (k - 1), (cnt T : ℝ) * h T := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    rw [Finset.sum_const, nsmul_eq_mul]
            _ = ∑ T ∈ levelFs X (k - 1), ((Fintype.card X : ℝ) - (k : ℝ) + 1) * h T := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    rw [hcnt T hT]
            _ = ((Fintype.card X : ℝ) - (k : ℝ) + 1) * fsum h (k - 1) := by
                    rw [fsum]
                    rw [← Finset.mul_sum]


lemma favg_eq_sizeAvg (g : Set X → ℝ) (k : ℕ) (hk : k ≤ Fintype.card X) :
    favg (fun u : Finset X => g (↑u : Set X)) k = Binom.sizeAvg g k := by
  classical
  have hsum : (∑ u ∈ levelFs X k, g (↑u : Set X))
      = ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k), g T := by
    refine Finset.sum_bij (s := levelFs X k)
      (t := (Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k))
      (f := fun u => g (↑u : Set X)) (g := fun T => g T)
      (fun u hu => (↑u : Set X)) ?_ ?_ ?_ ?_
    · intro u hu
      simp [Binom.coe_ncard, (mem_levelFs u k).mp hu]
    · intro u hu v hv hEq
      ext x
      calc
        x ∈ u ↔ x ∈ (↑u : Set X) := by simp
        _ ↔ x ∈ (↑v : Set X) := by rw [hEq]
        _ ↔ x ∈ v := by simp
    · intro T hT
      have hTk : T.ncard = k := (Finset.mem_filter.mp hT).2
      refine ⟨T.toFinset, ?_, ?_⟩
      · rw [mem_levelFs]
        rw [Binom.toFinset_card_ncard]
        exact hTk
      · ext x
        simp
    · intro u hu
      rfl
  have hcard : ((levelFs X k).card : ℝ)
      = (((Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k)).card : ℝ) := by
    have h2 : ((Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k)).card
        = (Fintype.card X).choose k := by
      simpa [Binom.levelFinset] using (Binom.levelFinset_card k hk)
    rw [levelFs_card, h2]
  unfold favg fsum
  rw [show Binom.sizeAvg g k
      = if ((Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k)).Nonempty
        then (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k), g T)
             / (((Finset.univ : Finset (Set X)).filter (fun T : Set X => T.ncard = k)).card : ℝ)
        else 0 by
    rfl]
  rw [if_pos (by
    simpa [Binom.levelFinset] using (Binom.levelFinset_nonempty k hk))]
  rw [hsum, hcard]



lemma step_ratio {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (k : ℕ) (hk1 : 2 ≤ k)
    (hk : k ≤ Fintype.card X) :
    ((k : ℝ) - 1) * favg (fun u : Finset X => supFW lam F (↑u : Set X)) k ≤
      (k : ℝ) * favg (fun u : Finset X => supFW lam F (↑u : Set X)) (k - 1) := by
  classical
  let hT : Finset X → ℝ := fun u => supFW lam F (↑u : Set X)
  let a : ℝ := (k : ℝ) - 1
  let b : ℝ := (Fintype.card X : ℝ) - (k : ℝ) + 1
  let Ck : ℝ := ((levelFs X k).card : ℝ)
  let Cd : ℝ := ((levelFs X (k - 1)).card : ℝ)
  change a * favg hT k ≤ (k : ℝ) * favg hT (k - 1)
  have hsw (W : Finset X) (hW : W ∈ levelFs X k) :
      a * hT W ≤ (∑ i ∈ W, hT (W.erase i)) := by
    have hWk : W.card = k := (mem_levelFs W k).mp hW
    simpa [hT, a, hWk] using (supFW_erase_sum (lam := lam) (F := F) hnonneg W)
  have h1 : (∑ W ∈ levelFs X k, a * hT W) ≤ ∑ W ∈ levelFs X k, ∑ i ∈ W, hT (W.erase i) := by
    exact Finset.sum_le_sum (fun W hW => hsw W hW)
  have hL : (∑ W ∈ levelFs X k, a * hT W) = a * fsum hT k := by
    rw [fsum]
    exact (Finset.mul_sum (s := levelFs X k) (f := hT) (a := a)).symm
  have hk0 : 0 < k := by omega
  have hstepsum : a * fsum hT k ≤ b * fsum hT (k - 1) := by
    calc
      a * fsum hT k = (∑ W ∈ levelFs X k, a * hT W) := hL.symm
      _ ≤ ∑ W ∈ levelFs X k, ∑ i ∈ W, hT (W.erase i) := h1
      _ = ((Fintype.card X : ℝ) - (k : ℝ) + 1) * fsum hT (k - 1) := by
            simpa [b] using (sum_W_erase_eq hT k hk0)
  have hCkpos : 0 < Ck := by
    dsimp [Ck]
    exact_mod_cast (Finset.card_pos).2 (levelFs_nonempty k hk)
  have hCdpos : 0 < Cd := by
    dsimp [Cd]
    exact_mod_cast (Finset.card_pos).2 (levelFs_nonempty (k - 1) (by omega))
  have hid : (k : ℝ) * Ck = b * Cd := by
    have hk1n : 1 ≤ k := by omega
    have hcast_km1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1n]
      norm_num
    have hcast_nkm1 : (Fintype.card X : ℝ) - ((k - 1 : ℕ) : ℝ) = b := by
      dsimp [b]
      rw [Nat.cast_sub hk1n]
      ring
    have hch := Binom2.choose_succ_mul_real (k - 1) (by omega : (k - 1) + 1 ≤ Fintype.card X)
    have hksucc : (k - 1) + 1 = k := by omega
    rw [hksucc] at hch
    rw [hcast_nkm1] at hch
    rw [hcast_km1] at hch
    -- hch : ((Fintype.card X).choose k : ℝ) * (k : ℝ) = ((Fintype.card X).choose (k - 1) : ℝ) * b
    -- (after ring normalization of (k:ℝ)-1+1 → k)
    have hch' : ((Fintype.card X).choose k : ℝ) * (k : ℝ) = ((Fintype.card X).choose (k - 1) : ℝ) * b := by
      nlinarith [hch]
    have hck : ((Fintype.card X).choose k : ℝ) = Ck := by
      dsimp [Ck]
      rw [levelFs_card k]
    have hcd : ((Fintype.card X).choose (k - 1) : ℝ) = Cd := by
      dsimp [Cd]
      rw [levelFs_card (k - 1)]
    nlinarith [hch', hck, hcd]
  have hbpos : 0 < b := by
    dsimp [b]
    have hkR : (k : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hk
    nlinarith
  have hstep2 : a * fsum hT k * Cd ≤ (k : ℝ) * fsum hT (k - 1) * Ck := by
    calc
      a * fsum hT k * Cd ≤ b * fsum hT (k - 1) * Cd := by
        exact mul_le_mul_of_nonneg_right hstepsum (le_of_lt hCdpos)
      _ = (k : ℝ) * fsum hT (k - 1) * Ck := by
        calc
          b * fsum hT (k - 1) * Cd = b * Cd * fsum hT (k - 1) := by ring
          _ = (k : ℝ) * Ck * fsum hT (k - 1) := by rw [← hid]
          _ = (k : ℝ) * fsum hT (k - 1) * Ck := by ring
  unfold favg
  change a * (fsum hT k / Ck) ≤ (k : ℝ) * (fsum hT (k - 1) / Cd)
  have hfinal : a * (fsum hT k / Ck) ≤ (k : ℝ) * (fsum hT (k - 1) / Cd) := by
    field_simp [ne_of_gt hCkpos, ne_of_gt hCdpos]
    nlinarith [hstep2]
  exact hfinal

lemma favg_down_ratio {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (N w : ℕ)
    (hN0 : 0 < N) (hNw : N ≤ w) (hw : w ≤ Fintype.card X) :
    favg (fun u : Finset X => supFW lam F (↑u : Set X)) w ≤
      ((w : ℝ) / (N : ℝ)) * favg (fun u : Finset X => supFW lam F (↑u : Set X)) N := by
  classical
  let hT : Finset X → ℝ := fun u => supFW lam F (↑u : Set X)
  change favg hT w ≤ ((w : ℝ) / (N : ℝ)) * favg hT N
  induction w with
  | zero =>
      omega
  | succ w ih =>
      by_cases hNw' : N ≤ w
      · have hwpos0 : 0 < w := by omega
        have hwRpos : 0 < (w : ℝ) := by exact_mod_cast hwpos0
        have hwRne : (w : ℝ) ≠ 0 := ne_of_gt hwRpos
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN0)
        have hst := step_ratio (lam := lam) (F := F) hnonneg (w + 1) (by omega : 2 ≤ w + 1)
          (by omega : w + 1 ≤ Fintype.card X)
        have hst' : (w : ℝ) * favg hT (w + 1) ≤ ((w + 1 : ℕ) : ℝ) * favg hT w := by
          simpa [hT] using hst
        have hst2 : favg hT (w + 1) ≤ (((w + 1 : ℕ) : ℝ) / (w : ℝ)) * favg hT w := by
          rw [div_mul_eq_mul_div]
          rw [le_div_iff₀ hwRpos]
          simpa [mul_comm] using hst'
        have hih : favg hT w ≤ ((w : ℝ) / (N : ℝ)) * favg hT N := by
          exact ih hNw' (by omega : w ≤ Fintype.card X)
        calc
          favg hT (w + 1) ≤ (((w + 1 : ℕ) : ℝ) / (w : ℝ)) * favg hT w := hst2
          _ ≤ (((w + 1 : ℕ) : ℝ) / (w : ℝ)) * (((w : ℝ) / (N : ℝ)) * favg hT N) := by
                exact mul_le_mul_of_nonneg_left hih (by positivity)
          _ = (((w + 1 : ℕ) : ℝ) / (N : ℝ)) * favg hT N := by
                field_simp [hwRne, hNne]
      · have hN : N = w + 1 := by omega
        subst N
        have hNne2 : ((w + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : w + 1 ≠ 0)
        field_simp [hNne2]
        exact le_rfl

lemma sizeAvg_ratio {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (N w : ℕ)
    (hN0 : 0 < N) (hNw : N ≤ w) (hw : w ≤ Fintype.card X) :
    (N : ℝ) * Binom.sizeAvg (supFW lam F) w ≤
      (w : ℝ) * Binom.sizeAvg (supFW lam F) N := by
  classical
  have hdown := favg_down_ratio hnonneg N w hN0 hNw hw
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN0
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  calc
    (N : ℝ) * Binom.sizeAvg (supFW lam F) w
        = (N : ℝ) * favg (fun u : Finset X => supFW lam F (↑u : Set X)) w := by
            rw [favg_eq_sizeAvg (supFW lam F) w hw]
    _ ≤ (N : ℝ) * (((w : ℝ) / (N : ℝ)) *
          favg (fun u : Finset X => supFW lam F (↑u : Set X)) N) := by
            exact mul_le_mul_of_nonneg_left hdown (le_of_lt hNpos)
    _ = (w : ℝ) * favg (fun u : Finset X => supFW lam F (↑u : Set X)) N := by
            field_simp [hNne]
    _ = (w : ℝ) * Binom.sizeAvg (supFW lam F) N := by
            rw [favg_eq_sizeAvg (supFW lam F) N (by omega : N ≤ Fintype.card X)]


end Ratio
end Submission
