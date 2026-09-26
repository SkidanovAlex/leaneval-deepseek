import Submission.Work.PTCert.LetterCore
import Submission.Work.PTCert.pairArith
import Submission.Work.PTCert.pairOfChar
import Submission.Work.PTCert.XtrInjective

/-!
# The letter library for `b1`

The letters `b1 r k`, `1 ≤ k < NB1 r`, enumerate `SAutGen r`: they are the Nielsen
transvections `Xtr i j hij ((k-1) % 4)` on the ordered pair `(i,j) = pairOf r ((k-1)/4)`.
This file collects the facts needed by the certificate pipeline:

* `b1_eq_ltr`, `ltr_unfold`, `ltr_eq_Xtr` — the unfolding of the letter;
* `b1_injOn` — injectivity on `Ico 1 (NB1 r)` (via `XtrInjective` and `pairOf_injOn`);
* `ltr_surj` — surjectivity onto `SAutGen r` (via `Xtr_eq_sAutAut` and `pairOfChar`);
* `SAutGen_eq_image`, `card_SAutGen`, `sum_SAutGen` — the resulting bijection;
* `deltaSub_eq_letters` — the expansion of `Δ_n` in the letters.
-/

set_option autoImplicit false

namespace Submission.PTCert

open Submission.FreeGroupAut

/-- Decomposition of a letter index into its pair index and kind. -/
theorem four_decomp (k : ℕ) (h1 : 1 ≤ k) : k = 1 + 4 * ((k - 1) / 4) + (k - 1) % 4 := by
  have h := Nat.div_add_mod (k - 1) 4
  omega

/-- The pair index `(k-1)/4` of a letter `k ∈ Ico 1 (NB1 r)` is in range. -/
theorem q_lt (r k : ℕ) (h1 : 1 ≤ k) (hk : k < NB1 r) : (k - 1) / 4 < r * (r - 1) := by
  have hd : 4 * ((k - 1) / 4) ≤ k - 1 := by
    have := Nat.div_mul_le_self (k - 1) 4
    omega
  have h4 : k - 1 < 4 * (r * (r - 1)) := by
    have hh : k - 1 < (4 * r) * (r - 1) := by simp only [NB1] at hk; omega
    simpa [mul_assoc] using hh
  have hlt : 4 * ((k - 1) / 4) < 4 * (r * (r - 1)) := lt_of_le_of_lt hd h4
  omega

/-- `pairOf` is injective on its range. -/
theorem pairOf_injOn (r : ℕ) {q1 q2 : ℕ} (h1 : q1 < r * (r - 1)) (h2 : q2 < r * (r - 1))
    (h : pairOf r q1 = pairOf r q2) : q1 = q2 := by
  have e1 := Work.PTCert.pairIdx_pairOf (r := r) (q := q1) h1
  have e2 := Work.PTCert.pairIdx_pairOf (r := r) (q := q2) h2
  rw [h] at e1
  exact e1.symm.trans e2

/-- Unfolding of the letter when the decoded pair is in range. -/
theorem ltr_unfold (r k : ℕ)
    (h : (pairOf r ((k - 1) / 4)).1 < r ∧ (pairOf r ((k - 1) / 4)).2 < r ∧
      (pairOf r ((k - 1) / 4)).1 ≠ (pairOf r ((k - 1) / 4)).2) :
    ltr r k = Xtr ⟨(pairOf r ((k - 1) / 4)).1, h.1⟩ ⟨(pairOf r ((k - 1) / 4)).2, h.2.1⟩
      (fun e => h.2.2 (congrArg Fin.val e)) ((k - 1) % 4) := by
  simp only [ltr, dif_pos h]

/-- The letter in terms of an explicitly given ordered pair. -/
theorem ltr_eq_Xtr (r k : ℕ)
    (h : (pairOf r ((k - 1) / 4)).1 < r ∧ (pairOf r ((k - 1) / 4)).2 < r ∧
      (pairOf r ((k - 1) / 4)).1 ≠ (pairOf r ((k - 1) / 4)).2)
    (i j : Fin r) (hij : i ≠ j) (hpair : ((i : ℕ), (j : ℕ)) = pairOf r ((k - 1) / 4)) :
    ltr r k = Xtr i j hij ((k - 1) % 4) := by
  rw [ltr_unfold r k h]
  have h1 : (⟨(pairOf r ((k - 1) / 4)).1, h.1⟩ : Fin r) = i :=
    Fin.ext (congrArg Prod.fst hpair).symm
  have h2 : (⟨(pairOf r ((k - 1) / 4)).2, h.2.1⟩ : Fin r) = j :=
    Fin.ext (congrArg Prod.snd hpair).symm
  subst h1
  subst h2
  rfl

/-- `b1` agrees with the decoded letter on its range. -/
theorem b1_eq_ltr (r k : ℕ) (hr : 2 ≤ r) (h1 : 1 ≤ k) (hk : k < NB1 r) :
    b1 r k = ltr r k := by
  have hk0 : ¬ (k = 0) := by omega
  have hP := Work.PTCert.pairOf_bounds (q_lt r k h1 hk)
  have hcond : (pairOf r ((k - 1) / 4)).1 < r ∧ (pairOf r ((k - 1) / 4)).2 < r ∧
      (pairOf r ((k - 1) / 4)).1 ≠ (pairOf r ((k - 1) / 4)).2 ∧ k < NB1 r :=
    ⟨hP.1, hP.2.1, hP.2.2, hk⟩
  simp only [b1, ltr, dif_neg hk0, dif_pos hcond, dif_pos hP, Xtr]

/-- The transvection `Xtr i j hij kind` is one of the Nielsen generators. -/
theorem Xtr_eq_sAutAut {r : ℕ} (i j : Fin r) (hij : i ≠ j) {kind : ℕ} (hk : kind < 4) :
    Xtr i j hij kind = sAutAut (⟨((i, j), (kind < 2, kind % 2 = 0)), hij⟩ : SAutIdx r) := by
  have h : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases h with h | h | h | h <;> subst h <;> simp [sAutAut, Xtr]

/-- Every letter in range is a Nielsen generator. -/
theorem b1_mem_SAutGen (r k : ℕ) (hr : 2 ≤ r) (h1 : 1 ≤ k) (hk : k < NB1 r) :
    b1 r k ∈ SAutGen r := by
  have hP := Work.PTCert.pairOf_bounds (q_lt r k h1 hk)
  have hk4 : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  set i : Fin r := ⟨(pairOf r ((k - 1) / 4)).1, hP.1⟩ with hi
  set j : Fin r := ⟨(pairOf r ((k - 1) / 4)).2, hP.2.1⟩ with hj
  have hij : i ≠ j := fun e => hP.2.2 (congrArg Fin.val e)
  rw [b1_eq_ltr r k hr h1 hk, ltr_eq_Xtr r k hP i j hij (by simp [hi, hj]),
    Xtr_eq_sAutAut i j hij hk4]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The letters of an index range are pairwise distinct. -/
theorem b1_injOn (r : ℕ) (hr : 2 ≤ r) :
    Set.InjOn (b1 r) ((Finset.Ico 1 (NB1 r) : Finset ℕ) : Set ℕ) := by
  intro k hk k' hk' h
  simp only [Finset.mem_coe, Finset.mem_Ico] at hk hk'
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hk1', hk2'⟩ := hk'
  have hq := q_lt r k hk1 hk2
  have hq' := q_lt r k' hk1' hk2'
  have hP := Work.PTCert.pairOf_bounds hq
  have hP' := Work.PTCert.pairOf_bounds hq'
  have hk4 : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hk4' : (k' - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hX : Xtr ⟨(pairOf r ((k - 1) / 4)).1, hP.1⟩ ⟨(pairOf r ((k - 1) / 4)).2, hP.2.1⟩
        (fun e => hP.2.2 (congrArg Fin.val e)) ((k - 1) % 4)
      = Xtr ⟨(pairOf r ((k' - 1) / 4)).1, hP'.1⟩ ⟨(pairOf r ((k' - 1) / 4)).2, hP'.2.1⟩
        (fun e => hP'.2.2 (congrArg Fin.val e)) ((k' - 1) % 4) := by
    rw [← ltr_unfold r k hP, ← ltr_unfold r k' hP', ← b1_eq_ltr r k hr hk1 hk2,
      ← b1_eq_ltr r k' hr hk1' hk2', h]
  obtain ⟨hi, hj, hkind⟩ := Work.PTCert.XtrInjective _ _ _ _ _ _ _ _ hk4 hk4' hX
  have hpair : pairOf r ((k - 1) / 4) = pairOf r ((k' - 1) / 4) :=
    Prod.ext (congrArg Fin.val hi) (congrArg Fin.val hj)
  have hqq : (k - 1) / 4 = (k' - 1) / 4 := pairOf_injOn r hq hq' hpair
  rw [four_decomp k hk1, four_decomp k' hk1', hqq, hkind]

/-- Every Nielsen generator is a letter in range. -/
theorem ltr_surj (r : ℕ) (hr : 2 ≤ r) (p : SAutIdx r) :
    ∃ k, 1 ≤ k ∧ k < NB1 r ∧ ltr r k = sAutAut p := by
  rcases p with ⟨⟨⟨i, j⟩, ⟨b, e⟩⟩, hij⟩
  obtain ⟨q, hq, hpq⟩ := (Work.PTCert.pairOfChar r hr).2 i.val j.val i.isLt j.isLt
    (fun h => hij (Fin.ext h))
  set kind : ℕ := if b then (if e then 0 else 1) else (if e then 2 else 3) with hkdef
  have hkind4 : kind < 4 := by rw [hkdef]; split <;> split <;> omega
  have hk1 : 1 ≤ 1 + 4 * q + kind := by omega
  have hk2 : 1 + 4 * q + kind < NB1 r := by
    have hqq : q + 1 ≤ r * (r - 1) := by omega
    have h4 : 4 * (q + 1) ≤ 4 * (r * (r - 1)) := Nat.mul_le_mul_left 4 hqq
    have hN : NB1 r = 1 + 4 * (r * (r - 1)) := by simp only [NB1, mul_assoc]
    rw [hN]
    omega
  have hkd : (1 + 4 * q + kind - 1) / 4 = q := by
    have h : 1 + 4 * q + kind - 1 = 4 * q + kind := by omega
    rw [h, Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt hkind4, Nat.add_zero]
  have hkm : (1 + 4 * q + kind - 1) % 4 = kind := by
    have h : 1 + 4 * q + kind - 1 = 4 * q + kind := by omega
    rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hkind4]
  refine ⟨1 + 4 * q + kind, hk1, hk2, ?_⟩
  have hP : (pairOf r ((1 + 4 * q + kind - 1) / 4)).1 < r ∧
      (pairOf r ((1 + 4 * q + kind - 1) / 4)).2 < r ∧
      (pairOf r ((1 + 4 * q + kind - 1) / 4)).1 ≠ (pairOf r ((1 + 4 * q + kind - 1) / 4)).2 := by
    rw [hkd]; exact Work.PTCert.pairOf_bounds hq
  have hpair : ((i : ℕ), (j : ℕ)) = pairOf r ((1 + 4 * q + kind - 1) / 4) := by
    rw [hkd, hpq]
  rw [ltr_eq_Xtr r _ hP i j hij hpair, hkm]
  cases b <;> cases e <;> simp [hkdef, Xtr, sAutAut]

/-- **The letters enumerate the Nielsen generating set.** -/
theorem SAutGen_eq_image (r : ℕ) (hr : 2 ≤ r) :
    SAutGen r = (Finset.Ico 1 (NB1 r)).image (b1 r) := by
  apply Finset.Subset.antisymm
  · intro g hg
    rw [SAutGen] at hg
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hg
    obtain ⟨k, hk1, hk2, hkeq⟩ := ltr_surj r hr p
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk1, hk2⟩,
      by rw [b1_eq_ltr r k hr hk1 hk2, hkeq, hp]⟩
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := Finset.mem_image.mp hg
    rw [← hkg]
    exact b1_mem_SAutGen r k hr (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2

/-- The Nielsen generating set has `NB1 r - 1 = 4 r (r-1)` elements. -/
theorem card_SAutGen (r : ℕ) (hr : 2 ≤ r) : (SAutGen r).card = NB1 r - 1 := by
  rw [SAutGen_eq_image r hr, Finset.card_image_of_injOn (b1_injOn r hr)]
  simp

/-- The sum over the Nielsen generating set, in the letters. -/
theorem sum_SAutGen (r : ℕ) (hr : 2 ≤ r) :
    (∑ g ∈ SAutGen r, MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) g)
      = ∑ a ∈ Finset.Ico 1 (NB1 r), MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r a) := by
  rw [SAutGen_eq_image r hr]
  exact Finset.sum_image (b1_injOn r hr)

end Submission.PTCert
