import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## The projection of a padded semi-Pfaffian set

`SemiPf.pad hm X` views `X ⊆ ℝ^k` as a semi-Pfaffian set in `ℝ^K` (`k ≤ K`) by zero-padding
the chain. Its coordinate projection to the first `n` coordinates does not see the padding:
projecting to `n + M` coordinates and then dropping the last `M` is the same as projecting to
`n + m` coordinates and dropping the last `m`, for `m ≤ M`.

The proof is an element chase, using the characterisation
`pad X = {y | y ∈ cubeC K ∧ takeZ hm y ∈ X}` of the padded set (which itself rests on the
fact that padding the chain does not change the values of the EA functions on the first `k`
coordinates).
-/

/-! ## Reindexing a sum over `Fin K` along `Fin.castLE` -/

/-- A sum over `Fin K` of a function vanishing above `k` equals the sum over `Fin k` of the
restriction along `Fin.castLE hm`. -/
theorem sum_padZ {k K : ℕ} (hm : k ≤ K) (f : Fin K → ℝ)
    (hf : ∀ i : Fin K, k ≤ i.val → f i = 0) :
    ∑ i : Fin K, f i = ∑ i : Fin k, f (Fin.castLE hm i) := by
  have h1 : (Finset.univ.image (Fin.castLE hm)) ⊆ (Finset.univ : Finset (Fin K)) :=
    Finset.subset_univ _
  have h2 : ∀ x ∈ (Finset.univ : Finset (Fin K)),
      x ∉ Finset.univ.image (Fin.castLE hm) → f x = 0 := by
    intro i _ hi
    apply hf i
    by_contra hlt
    push Not at hlt
    exact hi (Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _,
      Fin.ext (by rw [Fin.val_castLE])⟩)
  rw [← Finset.sum_subset h1 h2]
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Fin.castLE_injective hm hab

/-! ## The chain and its polynomials are unchanged by padding -/

/-- Padding the chain with zeros does not change the value of the affine forms on the
first `k` coordinates. -/
theorem ell_pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r) (y : Fin K → ℝ) :
    (EAChain.pad hm c).ell j y = c.ell j (takeZ hm y) := by
  unfold EAChain.ell
  have h : (∑ i : Fin K, (EAChain.pad hm c).a j i * y i)
      = ∑ i : Fin k, c.a j i * takeZ hm y i := by
    rw [sum_padZ hm (fun i => (EAChain.pad hm c).a j i * y i) ?_]
    · apply Finset.sum_congr rfl
      intro i _
      have hlt : (Fin.castLE hm i).val < k := by rw [Fin.val_castLE]; exact i.isLt
      have ha : (EAChain.pad hm c).a j (Fin.castLE hm i) = c.a j i := by
        change (if h : (Fin.castLE hm i).val < k then
            c.a j ⟨(Fin.castLE hm i).val, h⟩ else 0) = c.a j i
        rw [dif_pos hlt]
        congr 1
      rw [ha]
      rfl
    · intro i hi
      have hni : ¬ (i.val < k) := by omega
      have : (EAChain.pad hm c).a j i = 0 := by
        change (if h : i.val < k then c.a j ⟨i.val, h⟩ else 0) = 0
        rw [dif_neg hni]
      rw [this, zero_mul]
  rw [h]
  rfl

/-- Padding an EA polynomial does not change the value of the corresponding EA function on the
first `k` coordinates. -/
theorem eaEval_pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (Q : EAPoly k r)
    (y : Fin K → ℝ) :
    eaEval (EAChain.pad hm c) (EAPoly.pad hm Q) y = eaEval c Q (takeZ hm y) := by
  unfold eaEval EAPoly.pad
  rw [MvPolynomial.eval_rename]
  have huv : (Sum.elim y (fun j => Real.exp ((EAChain.pad hm c).ell j y)))
      ∘ (Sum.map (Fin.castLE hm) id)
      = Sum.elim (takeZ hm y) (fun j => Real.exp (c.ell j (takeZ hm y))) := by
    funext s
    cases s with
    | inl i => rfl
    | inr j => simpa only [Function.comp_apply, Sum.map_inr, Sum.elim_inr, id_eq]
                 using congrArg Real.exp (ell_pad hm c j y)
  rw [huv]

/-- Padding a basic set does not change when it holds. -/
theorem holds_pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (B : Basic k r)
    (y : Fin K → ℝ) :
    (Basic.pad hm B).holds (EAChain.pad hm c) y ↔ B.holds c (takeZ hm y) := by
  unfold Basic.holds Basic.pad
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro Q hQ
      have : EAPoly.pad hm Q ∈ B.eqs.map (EAPoly.pad hm) := List.mem_map.mpr ⟨Q, hQ, rfl⟩
      have := h.1 _ this
      rwa [eaEval_pad hm c Q y] at this
    · intro Q hQ
      have : EAPoly.pad hm Q ∈ B.pos.map (EAPoly.pad hm) := List.mem_map.mpr ⟨Q, hQ, rfl⟩
      have := h.2 _ this
      rwa [eaEval_pad hm c Q y] at this
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hf
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_pad hm c Q y]
      exact h.1 Q hQ
    · intro g hg
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_pad hm c Q y]
      exact h.2 Q hQ

/-! ## Elementary facts about `takeZ` and `padZ` -/

/-- Truncation of a point of the cube stays in the cube. -/
theorem takeZ_cube {k K : ℕ} (hm : k ≤ K) {y : Fin K → ℝ} (hy : y ∈ cubeC K) :
    takeZ hm y ∈ cubeC k := by
  intro i
  exact hy (Fin.castLE hm i)

/-- Zero-padding a point of the cube stays in the cube. -/
theorem padZ_cube {k K : ℕ} {x : Fin k → ℝ} (hx : x ∈ cubeC k) :
    padZ K x ∈ cubeC K := by
  intro i
  simp only [padZ]
  split_ifs with h
  · exact hx ⟨i.val, h⟩
  · simp

/-- Zero-padding and then truncating is the identity. -/
theorem takeZ_padZ {k K : ℕ} (hm : k ≤ K) (x : Fin k → ℝ) :
    takeZ hm (padZ K x) = x := by
  funext i
  have hlt : (Fin.castLE hm i).val < k := by rw [Fin.val_castLE]; exact i.isLt
  show padZ K x (Fin.castLE hm i) = x i
  simp only [padZ]
  rw [dif_pos hlt]
  congr 1

/-- The projection of a padded point to the first `n` coordinates does not depend on the
number of padding coordinates. -/
theorem projFirst_padZ {n m M : ℕ} (hm : m ≤ M) (x : Fin (n + m) → ℝ) :
    projFirst n M (padZ (n + M) x) = projFirst n m x := by
  funext i
  have hlt : (Fin.castAdd M i).val < n + m := by
    rw [Fin.val_castAdd]; omega
  show padZ (n + M) x (Fin.castAdd M i) = x (Fin.castAdd m i)
  simp only [padZ]
  rw [dif_pos hlt]
  congr 1

/-- `projFirst` is `takeZ`. -/
theorem projFirst_eq_takeZ {n M : ℕ} (y : Fin (n + M) → ℝ) :
    projFirst n M y = takeZ (Nat.le_add_right n M) y := by
  funext i
  exact congrArg y (Fin.ext rfl)

/-- Projecting to `n + M` coordinates and then taking the first `n` equals first truncating
the point to `n + m` coordinates (`m ≤ M`) and then projecting. -/
theorem projFirst_takeZ {n m M : ℕ} (hm : m ≤ M) (y : Fin (n + M) → ℝ) :
    projFirst n M y = projFirst n m (takeZ (Nat.add_le_add_left hm n) y) := by
  funext i
  show y (Fin.castAdd M i) = takeZ (Nat.add_le_add_left hm n) y (Fin.castAdd m i)
  show y (Fin.castAdd M i) = y (Fin.castLE (Nat.add_le_add_left hm n) (Fin.castAdd m i))
  exact congrArg y (Fin.ext (by rw [Fin.val_castLE, Fin.val_castAdd, Fin.val_castAdd]))

/-! ## The set of a padded semi-Pfaffian set -/

/-- **Set of a padded semi-Pfaffian set.** Padding is zero-padding of the extra coordinates. -/
theorem pad_set {k K : ℕ} (hm : k ≤ K) (X : SemiPf k) :
    (SemiPf.pad hm X).set = {y | y ∈ cubeC K ∧ takeZ hm y ∈ X.set} := by
  ext y
  rw [SemiPf.set]
  constructor
  · rintro ⟨hyc, B, hB, hBh⟩
    obtain ⟨B', hB', hBB'⟩ := List.mem_map.mp hB
    rw [← hBB'] at hBh
    exact ⟨hyc, ⟨takeZ_cube hm hyc, B', hB', (holds_pad hm X.c B' y).mp hBh⟩⟩
  · rintro ⟨hyc, hx⟩
    rw [SemiPf.set] at hx
    obtain ⟨_, B', hB', hBh⟩ := hx
    exact ⟨hyc, Basic.pad hm B', List.mem_map.mpr ⟨B', hB', rfl⟩,
      (holds_pad hm X.c B' y).mpr hBh⟩

/-! ## The main statement -/

/-- **Projection of a padded semi-Pfaffian set.** Padding a semi-Pfaffian set in `ℝ^{n+m}` to
`ℝ^{n+M}` (`m ≤ M`) and then projecting to the first `n` coordinates is the same as projecting
the original set to its first `n` coordinates. -/
theorem pad_proj {n m M : ℕ} (hm : m ≤ M) (X : WilkiesDesign.E.SemiPf (n + m)) :
    WilkiesDesign.E.projFirst n M '' (Work.WilE7.SemiPf.pad (Nat.add_le_add_left hm n) X).set =
      WilkiesDesign.E.projFirst n m '' X.set := by
  rw [pad_set (Nat.add_le_add_left hm n) X]
  ext z
  constructor
  · rintro ⟨y, ⟨hyc, hx⟩, rfl⟩
    exact ⟨takeZ _ y, hx, (projFirst_takeZ hm y).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨padZ (n + M) x, ⟨padZ_cube hx.1, ?_⟩, projFirst_padZ hm x⟩
    rw [takeZ_padZ]
    exact hx

end Work.WilE7
