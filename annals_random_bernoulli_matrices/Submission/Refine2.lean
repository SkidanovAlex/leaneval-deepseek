import Mathlib
import Submission.Sec3Core
import Submission.Sec3Tower
import Submission.Refine

open Submission.Sec3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement, part 2: the avgF truncation identity

Tikhomirov 2020, Section 3 (`prop: refinement`).  This module proves the
associativity/truncation identity for the coordinate-averaging operator:

`avgF f p (j+m) (cat v w) = avgF (avgF f p j v) p m w`,

where `cat v w` is the concatenation of a vector of length `j` with one of
length `m`.  This is the hinge that identifies the level-`i` function
`g_i = avgF f p i (x₁..xᵢ)` with the `(i−j)`-fold average of the flat
level-`j` function `g_j` over the remaining coordinates, letting
`Refine.avgF_spike_shrink` apply from a flat level forward.

The proof expands both sides over subsets and matches them through the
bijection `Finset (Fin (j+m)) ≃ Finset (Fin j) × Finset (Fin m)` given by
splitting at `j`.  Weights depend only on cardinality, so they factor, and
subset sums split over the two halves.
-/

namespace Submission.Refine2

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-! ## 1. Splitting indices `Fin (j+m)` at `j` -/

/-- the tail index `j + r` inside `Fin (j+m)` (`j` explicit). -/
def tailIdx (j : ℕ) {m : ℕ} (r : Fin m) : Fin (j + m) :=
  ⟨j + r.val, by have h := r.isLt; omega⟩

/-- the embedding of `Fin j` into the head of `Fin (j+m)`. -/
def headIdx {j m : ℕ} (a : Fin j) : Fin (j + m) :=
  ⟨a.val, by have h := a.isLt; omega⟩

/-- concatenation of a head vector of length `j` with a tail vector of length `m`. -/
def cat {j m : ℕ} (v : Fin j → ℤ) (w : Fin m → ℤ) : Fin (j + m) → ℤ :=
  fun q => if hq : q.val < j then v ⟨q.val, hq⟩ else w ⟨q.val - j, by
    have h1 : j ≤ q.val := le_of_not_gt hq
    have h2 : q.val < j + m := q.isLt
    omega⟩

/-- `cat` agrees with `v` on the head indices. -/
lemma cat_head {j m : ℕ} {v : Fin j → ℤ} {w : Fin m → ℤ} (a : Fin j) :
    cat v w (headIdx a) = v a := by
  dsimp [cat, headIdx]
  rw [dif_pos (by have h := a.isLt; omega)]

/-- `cat` agrees with `w` on the tail indices. -/
lemma cat_tail {j m : ℕ} {v : Fin j → ℤ} {w : Fin m → ℤ} (r : Fin m) :
    cat v w (tailIdx j r) = w r := by
  dsimp [cat, tailIdx]
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- `headIdx` is injective. -/
lemma headIdx_inj {j m : ℕ} : Function.Injective (@headIdx j m) := by
  intro a b h
  apply Fin.ext
  simpa [headIdx] using (congrArg Fin.val h)

/-- `tailIdx j` is injective. -/
lemma tailIdx_inj (j : ℕ) {m : ℕ} : Function.Injective (@tailIdx j m) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [tailIdx] at hv
  omega

/-- images of `headIdx` and `tailIdx` are disjoint. -/
lemma head_tail_disjoint {j m : ℕ} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    Disjoint (A.image (headIdx : Fin j → Fin (j + m)))
      (R.image (tailIdx j : Fin m → Fin (j + m))) := by
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  rcases Finset.mem_image.mp hz₁ with ⟨a, ha, hz₁'⟩
  rcases Finset.mem_image.mp hz₂ with ⟨r, hr, hz₂'⟩
  have hval1 : (z : ℕ) < j := by
    rw [← hz₁']
    dsimp [headIdx]
    have h := a.isLt
    omega
  have hval2 : j ≤ (z : ℕ) := by
    rw [← hz₂']
    dsimp [tailIdx]
    have h := r.isLt
    omega
  omega

/-- reconstruct a subset of `Fin (j+m)` from its head part `A ⊆ Fin j` and its
tail part `R ⊆ Fin m`. -/
def reconstruct {j m : ℕ} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    Finset (Fin (j + m)) :=
  A.image (headIdx : Fin j → Fin (j + m)) ∪ R.image (tailIdx j : Fin m → Fin (j + m))

/-- membership in `reconstruct` (head/tail images). -/
lemma mem_reconstruct_iff {j m : ℕ} {A : Finset (Fin j)} {R : Finset (Fin m)}
    {q : Fin (j + m)} :
    q ∈ reconstruct A R ↔ (∃ a : Fin j, headIdx a = q ∧ a ∈ A) ∨
      (∃ r : Fin m, tailIdx j r = q ∧ r ∈ R) := by
  classical
  dsimp [reconstruct]
  rw [Finset.mem_union]
  constructor
  · intro h
    rcases h with h | h
    · left
      rw [Finset.mem_image] at h
      rcases h with ⟨a, ha, hq⟩
      exact ⟨a, hq, ha⟩
    · right
      rw [Finset.mem_image] at h
      rcases h with ⟨r, hr, hq⟩
      exact ⟨r, hq, hr⟩
  · intro h
    rcases h with h | h
    · left
      rcases h with ⟨a, hq, ha⟩
      rw [Finset.mem_image]
      exact ⟨a, ha, hq⟩
    · right
      rcases h with ⟨r, hq, hr⟩
      rw [Finset.mem_image]
      exact ⟨r, hr, hq⟩

/-- head part of a subset of `Fin (j+m)`: the elements with value `< j`. -/
def prePart {j m : ℕ} (S : Finset (Fin (j + m))) : Finset (Fin j) :=
  (S.filter (fun q : Fin (j + m) => q.val < j)).attach.image
    (fun a => (⟨a.1.val, (Finset.mem_filter.mp
      (a.property : a.1 ∈ (S.filter (fun q : Fin (j + m) => q.val < j)))).2⟩ : Fin j))

/-- tail part of a subset of `Fin (j+m)`: elements with value `≥ j`, shifted
back by `j`. -/
def tailPart {j m : ℕ} (S : Finset (Fin (j + m))) : Finset (Fin m) :=
  (S.filter (fun q : Fin (j + m) => j ≤ q.val)).attach.image
    (fun a => (⟨a.1.val - j, by
      have h1 : j ≤ a.1.val := (Finset.mem_filter.mp
        (a.property : a.1 ∈ (S.filter (fun q : Fin (j + m) => j ≤ q.val)))).2
      have h2 : a.1.val < j + m := a.1.isLt
      omega⟩ : Fin m))

/-- membership in `prePart`. -/
lemma mem_prePart {j m : ℕ} {S : Finset (Fin (j + m))} {a : Fin j} :
    a ∈ prePart S ↔ headIdx a ∈ S := by
  classical
  dsimp [prePart]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hxS : x.1 ∈ S := (Finset.mem_filter.mp
      (x.property : x.1 ∈ (S.filter (fun q : Fin (j + m) => q.val < j)))).1
    have hval : x.1.val = a.val := by
      have h := congrArg Fin.val hxa
      simpa using h
    have heq : x.1 = headIdx a := by
      apply Fin.ext
      dsimp [headIdx]
      exact hval
    simpa [heq] using hxS
  · intro hS
    refine ⟨⟨headIdx a, ?_⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hS, by dsimp [headIdx]; omega⟩
    · simp
    · simp [headIdx]

/-- membership in `tailPart`. -/
lemma mem_tailPart {j m : ℕ} {S : Finset (Fin (j + m))} {r : Fin m} :
    r ∈ tailPart S ↔ tailIdx j r ∈ S := by
  classical
  dsimp [tailPart]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxr⟩
    have hxS : x.1 ∈ S := (Finset.mem_filter.mp
      (x.property : x.1 ∈ (S.filter (fun q : Fin (j + m) => j ≤ q.val)))).1
    have hval : x.1.val - j = r.val := by
      have h := congrArg Fin.val hxr
      simpa using h
    have heq : x.1 = tailIdx j r := by
      apply Fin.ext
      have hle : j ≤ x.1.val := (Finset.mem_filter.mp
        (x.property : x.1 ∈ (S.filter (fun q : Fin (j + m) => j ≤ q.val)))).2
      calc
        x.1.val = (x.1.val - j) + j := (Nat.sub_add_cancel hle).symm
        _ = r.val + j := by rw [hval]
        _ = j + r.val := by omega
    simpa [heq] using hxS
  · intro hS
    refine ⟨⟨tailIdx j r, ?_⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hS, by dsimp [tailIdx]; omega⟩
    · simp
    · simp [tailIdx]

/-- cardinality of the head image. -/
lemma card_image_head {j m : ℕ} (A : Finset (Fin j)) :
    (A.image (headIdx : Fin j → Fin (j + m))).card = A.card := by
  exact Finset.card_image_of_injective A (@headIdx_inj j m)

/-- cardinality of the tail image. -/
lemma card_image_tail {j m : ℕ} (R : Finset (Fin m)) :
    (R.image (tailIdx j : Fin m → Fin (j + m))).card = R.card := by
  exact Finset.card_image_of_injective R (tailIdx_inj j)

/-- cardinality of a reconstructed set is the sum of the two parts. -/
lemma card_reconstruct {j m : ℕ} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    (reconstruct A R).card = A.card + R.card := by
  dsimp [reconstruct]
  rw [Finset.card_union_of_disjoint (head_tail_disjoint A R)]
  rw [card_image_head A, card_image_tail R]

/-- `reconstruct` recovers a set from its head and tail parts. -/
lemma reconstruct_eq {j m : ℕ} (S : Finset (Fin (j + m))) :
    reconstruct (prePart S) (tailPart S) = S := by
  ext q
  constructor
  · intro hq
    rw [mem_reconstruct_iff] at hq
    rcases hq with ⟨a, ha, hA⟩ | ⟨r, hr, hR⟩
    · have hS : headIdx a ∈ S := (mem_prePart.mp hA)
      rwa [← ha]
    · have hS : tailIdx j r ∈ S := (mem_tailPart.mp hR)
      rwa [← hr]
  · intro hq
    by_cases hlt : q.val < j
    · rw [mem_reconstruct_iff]
      left
      have hred : headIdx (⟨q.val, hlt⟩ : Fin j) = q := by
        apply Fin.ext
        rfl
      refine ⟨⟨q.val, hlt⟩, hred, ?_⟩
      rw [mem_prePart]
      rw [hred]
      exact hq
    · have hge : j ≤ q.val := le_of_not_gt hlt
      rw [mem_reconstruct_iff]
      right
      have hred : tailIdx j (⟨q.val - j, by
          have h2 : q.val < j + m := q.isLt
          omega⟩ : Fin m) = q := by
        apply Fin.ext
        simp [tailIdx]
        omega
      refine ⟨⟨q.val - j, by
        have h2 : q.val < j + m := q.isLt
        omega⟩, hred, ?_⟩
      rw [mem_tailPart]
      rw [hred]
      exact hq

/-- the head part of a reconstructed set is the head set. -/
lemma prePart_reconstruct {j m : ℕ} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    prePart (reconstruct A R) = A := by
  ext a
  rw [mem_prePart]
  constructor
  · intro h
    rw [mem_reconstruct_iff] at h
    rcases h with ⟨b, hb, hB⟩ | ⟨r, hr, hR⟩
    · have hb' := congrArg Fin.val hb
      have ha : a = b := by
        apply Fin.ext
        dsimp [headIdx] at hb'
        simpa using hb'.symm
      rwa [← ha] at hB
    · exfalso
      have hav := congrArg Fin.val hr
      have h1 : j ≤ (tailIdx j r).val := by
        dsimp [tailIdx]
        omega
      have h2 : ((headIdx (m := m) a) : Fin (j + m)).val < j := by
        dsimp [headIdx]
        have ha2 := a.isLt
        omega
      rw [hav] at h1
      omega
  · intro hA
    rw [mem_reconstruct_iff]
    left
    refine ⟨a, ?_, hA⟩
    apply Fin.ext
    rfl

/-- the tail part of a reconstructed set is the tail set. -/
lemma tailPart_reconstruct {j m : ℕ} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    tailPart (reconstruct A R) = R := by
  ext r
  rw [mem_tailPart]
  constructor
  · intro h
    rw [mem_reconstruct_iff] at h
    rcases h with ⟨a, ha, hA⟩ | ⟨s, hs, hS⟩
    · exfalso
      have hav := congrArg Fin.val ha
      have h1 : ((headIdx (m := m) a) : Fin (j + m)).val < j := by
        dsimp [headIdx]
        omega
      have h2 : j ≤ (tailIdx j r).val := by
        dsimp [tailIdx]
        omega
      rw [← hav] at h2
      omega
    · have hs' := congrArg Fin.val hs
      have hrr : r = s := by
        apply Fin.ext
        dsimp [tailIdx] at hs'
        omega
      rwa [← hrr] at hS
  · intro hR
    rw [mem_reconstruct_iff]
    right
    refine ⟨r, ?_, hR⟩
    apply Fin.ext
    rfl

/-! ## 2. subset sums and weights split over the two halves -/

/-- the subset sum of a concatenated vector over a reconstructed set splits. -/
lemma subSum_reconstruct {j m : ℕ} {v : Fin j → ℤ} {w : Fin m → ℤ}
    (A : Finset (Fin j)) (R : Finset (Fin m)) :
    subSum (cat v w) (reconstruct A R) = subSum v A + subSum w R := by
  classical
  dsimp [subSum]
  have hd := head_tail_disjoint A R
  calc
    (∑ q ∈ A.image (headIdx : Fin j → Fin (j + m)) ∪
        R.image (tailIdx j : Fin m → Fin (j + m)), cat v w q)
        = (∑ q ∈ A.image (headIdx : Fin j → Fin (j + m)), cat v w q) +
          (∑ q ∈ R.image (tailIdx j : Fin m → Fin (j + m)), cat v w q) := by
          rw [Finset.sum_union hd]
    _ = (∑ a ∈ A, cat v w (headIdx a)) +
        (∑ r ∈ R, cat v w (tailIdx j r)) := by
          rw [Finset.sum_image (g := (headIdx : Fin j → Fin (j + m))) (f := fun q => cat v w q) (@headIdx_inj j m).injOn]
          rw [Finset.sum_image (g := (tailIdx j : Fin m → Fin (j + m))) (f := fun q => cat v w q) (tailIdx_inj j).injOn]
    _ = (∑ a ∈ A, v a) + (∑ r ∈ R, w r) := by
          apply congrArg₂ HAdd.hAdd
          · apply Finset.sum_congr rfl
            intro a ha
            exact cat_head a
          · apply Finset.sum_congr rfl
            intro r hr
            exact cat_tail r

/-- powers split over the two subset sizes. -/
lemma pow_split_add {p : ℝ} (a b c d : ℕ) : p ^ (a + b) * (1 - p) ^ (c + d) =
    p ^ a * (1 - p) ^ c * (p ^ b * (1 - p) ^ d) := by
  rw [pow_add (a := p), pow_add (a := 1 - p)]
  ring

/-- the weight of a reconstructed set factors. -/
lemma wB_reconstruct {j m : ℕ} {p : unitInterval} (A : Finset (Fin j)) (R : Finset (Fin m)) :
    wB (j + m) p (reconstruct A R) = wB j p A * wB m p R := by
  classical
  dsimp [wB]
  rw [card_reconstruct]
  have hcA : A.card ≤ j := by simpa using (Finset.card_le_univ A)
  have hcR : R.card ≤ m := by simpa using (Finset.card_le_univ R)
  have hsub : j + m - (A.card + R.card) = (j - A.card) + (m - R.card) := by omega
  rw [hsub, pow_add (a := (p : ℝ)), pow_add (a := (1 - (p : ℝ)))]
  ring


/-! ## 3. the truncation identity -/

/-- `avgF` is associative: averaging `f` over `j+m` concatenated coordinates
equals averaging the `j`-coordinate average over the remaining `m`
coordinates. -/
theorem avgF_cat {f : ℤ → ℝ} {p : unitInterval} {j m : ℕ}
    (v : Fin j → ℤ) (w : Fin m → ℤ) :
    avgF (avgF f p j v) p m w = avgF f p (j + m) (cat v w) := by
  funext t
  let P1 : Finset (Finset (Fin (j + m))) :=
    (Finset.univ : Finset (Fin (j + m))).powerset
  let Pj : Finset (Finset (Fin j)) :=
    (Finset.univ : Finset (Fin j)).powerset
  let Pm : Finset (Finset (Fin m)) :=
    (Finset.univ : Finset (Fin m)).powerset
  -- bijection between full subsets and pairs of parts
  have hbij : (∑ S ∈ P1, wB (j + m) p S * f (t + subSum (cat v w) S)) =
      ∑ pr ∈ Pj.product Pm,
        wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2) := by
    classical
    let i : (S : Finset (Fin (j + m))) → S ∈ P1 → Finset (Fin j) × Finset (Fin m) :=
      fun S _ => (prePart S, tailPart S)
    refine Finset.sum_bij (s := P1) (t := Pj.product Pm)
      (f := fun S => wB (j + m) p S * f (t + subSum (cat v w) S))
      (g := fun pr => wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2))
      i ?_ ?_ ?_ ?_
    · intro S hS
      simp [Pj, Pm]
    · intro S₁ hS₁ S₂ hS₂ h
      have hpre : prePart S₁ = prePart S₂ := congrArg Prod.fst h
      have htail : tailPart S₁ = tailPart S₂ := congrArg Prod.snd h
      calc
        S₁ = reconstruct (prePart S₁) (tailPart S₁) := (reconstruct_eq S₁).symm
        _ = reconstruct (prePart S₂) (tailPart S₂) := by rw [hpre, htail]
        _ = S₂ := reconstruct_eq S₂
    · intro pr hpr
      refine ⟨reconstruct pr.1 pr.2, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        simp
      · apply Prod.ext
        · exact prePart_reconstruct pr.1 pr.2
        · exact tailPart_reconstruct pr.1 pr.2
    · intro S hS
      dsimp [i]
      have hl : wB (j + m) p S * f (t + subSum (cat v w) S) =
          wB j p (prePart S) * wB m p (tailPart S) *
            f (t + subSum v (prePart S) + subSum w (tailPart S)) := by
        conv_lhs =>
          rw [← reconstruct_eq S]
          rw [wB_reconstruct]
          rw [subSum_reconstruct]
        have harg : t + (subSum v (prePart S) + subSum w (tailPart S)) =
            t + subSum v (prePart S) + subSum w (tailPart S) := by
          ring
        rw [harg]
      exact hl
  -- expand the left side into the double product sum
  have hmain : avgF (avgF f p j v) p m w t =
      ∑ pr ∈ Pj.product Pm,
        wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2) := by
    calc
      avgF (avgF f p j v) p m w t
          = ∑ R ∈ Pm, ∑ B ∈ Pj,
              wB m p R * (wB j p B * f (t + subSum w R + subSum v B)) := by
            dsimp [avgF]
            apply Finset.sum_congr rfl
            intro R hR
            rw [Finset.mul_sum]
      _ = ∑ B ∈ Pj, ∑ R ∈ Pm,
              wB j p B * wB m p R * f (t + subSum v B + subSum w R) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro B hB
            apply Finset.sum_congr rfl
            intro R hR
            have harg : t + subSum w R + subSum v B = t + subSum v B + subSum w R := by
              ring
            rw [harg]
            ring
      _ = ∑ pr ∈ Pj.product Pm,
            wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2) := by
            exact (Finset.sum_product (s := Pj) (t := Pm)
              (f := fun pr : Finset (Fin j) × Finset (Fin m) =>
                wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2))).symm
  calc
    avgF (avgF f p j v) p m w t
        = ∑ pr ∈ Pj.product Pm,
            wB j p pr.1 * wB m p pr.2 * f (t + subSum v pr.1 + subSum w pr.2) := hmain
    _ = ∑ S ∈ P1, wB (j + m) p S * f (t + subSum (cat v w) S) := hbij.symm
    _ = avgF f p (j + m) (cat v w) t := by
          rfl


/-! ## 4. level 0 and level 1 averages -/

/-- the length-0 average is the identity. -/
lemma avgF_zero {g : ℤ → ℝ} {p : unitInterval} (t : ℤ) :
    avgF g p 0 (fun _ : Fin 0 => (0 : ℤ)) t = g t := by
  dsimp [avgF, wB, subSum]
  simp

/-- the length-1 average with a single shift `c` is the basic two-point mix. -/
lemma avgF_one {g : ℤ → ℝ} {p : unitInterval} (c : ℤ) (t : ℤ) :
    avgF g p 1 (fun _ : Fin 1 => c) t = (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + c) := by
  classical
  let x : Fin 1 → ℤ := fun _ => c
  have hrec := Sec3Tower.avgF_rec (f := g) (p := p) 0 x t
  have hpre : Sec3Tower.pre x 0 (Nat.le_succ 0) = (fun _ : Fin 0 => (0 : ℤ)) := by
    funext j
    exact Fin.elim0 j
  have hzero1 : avgF g p 0 (Sec3Tower.pre x 0 (Nat.le_succ 0)) t = g t := by
    rw [hpre]
    exact avgF_zero t
  have hx : x Sec3Tower.last = c := by
    dsimp [x]
  have hzero2 : avgF g p 0 (Sec3Tower.pre x 0 (Nat.le_succ 0)) (t + x Sec3Tower.last) = g (t + c) := by
    calc
      avgF g p 0 (Sec3Tower.pre x 0 (Nat.le_succ 0)) (t + x Sec3Tower.last)
          = g (t + x Sec3Tower.last) := by
            rw [hpre]
            exact avgF_zero (t + x Sec3Tower.last)
      _ = g (t + c) := by
            rw [hx]
  rw [hrec]
  rw [hzero1, hzero2]

end Submission.Refine2
