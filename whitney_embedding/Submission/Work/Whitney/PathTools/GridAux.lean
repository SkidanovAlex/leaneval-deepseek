import Mathlib
import Submission.Work.Whitney.PathTools.JaniszewskiTwo
import Submission.Work.Whitney.PathTools.Snap

/-!
# Subdivision of the grid chain complex and the locus of a chain

This module contains the combinatorial tools used to prove the planar Janiszewski theorem
for two compacta meeting in a single point (`Grid.janis_singleton_general`), following
McCleary's "Alexander Theorem" (Chapter 9 of *A First Course in Topology*):

* `sub2`, `sub1`, `sub0` subdivide a `2`-chain, a `1`-chain and a `0`-chain at the mesh `h/n`;
* `bdry2_sub2` and `bdry1_sub1` are the chain-map properties;
* `locus`/`elocus` are the loci of a `2`-chain/`1`-chain (unions of cells/segments);
* the geometric inclusions `gseg_sub1_subset` and `gsq_sub2_subset` compare a fine edge/cell
  with the coarse edge/cell it tiles.
-/

namespace Work.Whitney.PathTools
namespace Grid

noncomputable section

open Set Metric
open scoped BigOperators Topology

/-! ## Subdivision -/

/-- Subdivision of a `2`-chain: the fine cell `(i, j)` inherits the value of the coarse cell
`(i / n, j / n)`. -/
def sub2 (n : ℕ) (W : C2) : C2 := fun c => W (c.1 / (n : ℤ), c.2 / (n : ℤ))

/-- Subdivision of a `1`-chain: the fine edges lying on a coarse grid line inherit the value of
the coarse edge they tile. -/
def sub1 (n : ℕ) (l : Edge → ZMod 2) : Edge → ZMod 2
  | (false, i, j) => if (n : ℤ) ∣ i then l (false, i / (n : ℤ), j / (n : ℤ)) else 0
  | (true, i, j) => if (n : ℤ) ∣ j then l (true, i / (n : ℤ), j / (n : ℤ)) else 0

/-- Subdivision of a `0`-chain. -/
def sub0 (n : ℕ) (σ : Chain0) : Chain0 :=
  fun p => if (n : ℤ) ∣ p.1 ∧ (n : ℤ) ∣ p.2 then σ (p.1 / (n : ℤ), p.2 / (n : ℤ)) else 0

lemma ediv_pred_of_dvd {n i : ℤ} (hn : 0 < n) (h : n ∣ i) : (i - 1) / n = i / n - 1 := by
  obtain ⟨q, rfl⟩ := h
  rw [Int.mul_ediv_cancel_left _ (ne_of_gt hn)]
  have key : (n - 1) + n * (q - 1) = n * q - 1 := by ring
  have h3 : 0 ≤ n - 1 := by omega
  have h4 : n - 1 < n := by omega
  exact ((Int.ediv_emod_unique (a := n * q - 1) (b := n) (q := q - 1) (r := n - 1) hn).mpr
    ⟨key, h3, h4⟩).1

lemma ediv_pred_of_not_dvd {n i : ℤ} (hn : 0 < n) (h : ¬ n ∣ i) : (i - 1) / n = i / n := by
  have hr : 0 < i % n := by
    rcases lt_trichotomy (i % n) 0 with hlt | heq | hgt
    · exact absurd (Int.emod_nonneg i (ne_of_gt hn)) (not_le.mpr hlt)
    · exact absurd (Int.dvd_of_emod_eq_zero heq) h
    · exact hgt
  have hlt : i % n < n := Int.emod_lt_of_pos i hn
  have key : (i % n - 1) + n * (i / n) = i - 1 := by
    have := Int.mul_ediv_add_emod i n
    omega
  have h3 : 0 ≤ i % n - 1 := by omega
  have h4 : i % n - 1 < n := by omega
  exact ((Int.ediv_emod_unique (a := i - 1) (b := n) (q := i / n) (r := i % n - 1) hn).mpr
    ⟨key, h3, h4⟩).1

/-- **The subdivision is a chain map** (in degree `2`). -/
lemma bdry2_sub2 {n : ℕ} (hn : 0 < n) (W : C2) : bdry2 (sub2 n W) = sub1 n (bdry2 W) := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  funext e
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [bdry2, sub2, sub1]
    by_cases hdvd : (n : ℤ) ∣ i
    · rw [if_pos hdvd, ediv_pred_of_dvd hn' hdvd]
    · rw [if_neg hdvd, ediv_pred_of_not_dvd hn' hdvd]
      exact CharTwo.add_self_eq_zero _
  · simp only [bdry2, sub2, sub1]
    by_cases hdvd : (n : ℤ) ∣ j
    · rw [if_pos hdvd, ediv_pred_of_dvd hn' hdvd]
    · rw [if_neg hdvd, ediv_pred_of_not_dvd hn' hdvd]
      exact CharTwo.add_self_eq_zero _

/-- `sub1` is additive. -/
lemma sub1_add (n : ℕ) (a b : Edge → ZMod 2) : sub1 n (a + b) = sub1 n a + sub1 n b := by
  funext e
  obtain ⟨c, i, j⟩ := e
  cases c <;> (simp only [sub1, Pi.add_apply]; split <;> simp)

lemma sub1_zero (n : ℕ) : sub1 n (0 : Edge → ZMod 2) = 0 := by
  funext e
  obtain ⟨c, i, j⟩ := e
  cases c <;> simp [sub1]

/-- **The subdivision is a chain map** (in degree `1`). -/
lemma bdry1_sub1 {n : ℕ} (hn : 0 < n) (l : Edge → ZMod 2) :
    bdry1 (sub1 n l) = sub0 n (bdry1 l) := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  funext p
  obtain ⟨i, j⟩ := p
  by_cases hi : (n : ℤ) ∣ i
  · by_cases hj : (n : ℤ) ∣ j
    · rw [sub0, if_pos ⟨hi, hj⟩]
      simp only [bdry1, sub1, if_pos hi, if_pos hj, ediv_pred_of_dvd hn' hi,
        ediv_pred_of_dvd hn' hj]
    · rw [sub0, if_neg (by tauto)]
      simp only [bdry1, sub1, if_pos hi, if_neg hj, ediv_pred_of_not_dvd hn' hj,
        CharTwo.add_self_eq_zero, zero_add, add_zero, CharP.cast_eq_zero]
  · by_cases hj : (n : ℤ) ∣ j
    · rw [sub0, if_neg (by tauto)]
      simp only [bdry1, sub1, if_neg hi, if_pos hj, ediv_pred_of_not_dvd hn' hi,
        CharTwo.add_self_eq_zero, zero_add, add_zero, CharP.cast_eq_zero]
    · rw [sub0, if_neg (by tauto)]
      simp only [bdry1, sub1, if_neg hi, if_neg hj, zero_add, add_zero]

/-- After subdivision the two-point `0`-chain at `p, q` becomes the two-point `0`-chain at the
scaled vertices `n • p`, `n • q`. -/
lemma sub0_pair {n : ℕ} (hn : 0 < n) (p q : ℤ × ℤ) :
    sub0 n (fun v => (if v = p then (1 : ZMod 2) else 0) + (if v = q then 1 else 0)) =
      fun v => (if v = (n * p.1, n * p.2) then (1 : ZMod 2) else 0)
        + (if v = (n * q.1, n * q.2) then 1 else 0) := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnne : (n : ℤ) ≠ 0 := ne_of_gt hn'
  have hdivl : ∀ a : ℤ, (n : ℤ) ∣ n * a := fun a => ⟨a, by ring⟩
  funext v
  rw [sub0]
  by_cases hv : (n : ℤ) ∣ v.1 ∧ (n : ℤ) ∣ v.2
  · rw [if_pos hv]
    have hv1 : (n : ℤ) * (v.1 / (n : ℤ)) = v.1 := Int.mul_ediv_cancel' hv.1
    have hv2 : (n : ℤ) * (v.2 / (n : ℤ)) = v.2 := Int.mul_ediv_cancel' hv.2
    have hkey : ∀ r : ℤ × ℤ, (v.1 / (n : ℤ), v.2 / (n : ℤ)) = r ↔
        v = (n * r.1, n * r.2) := by
      intro r
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := Prod.mk.injEq (v.1 / (n : ℤ)) (v.2 / (n : ℤ)) r.1 r.2 |>.mp h
        have : v = (n * (v.1 / (n : ℤ)), n * (v.2 / (n : ℤ))) := by rw [hv1, hv2]
        rw [this, h1, h2]
      · intro h
        rw [h, Int.mul_ediv_cancel_left r.1 hnne, Int.mul_ediv_cancel_left r.2 hnne]
    by_cases hp : (v.1 / (n : ℤ), v.2 / (n : ℤ)) = p
    · rw [if_pos hp, if_pos ((hkey p).mp hp)]
      by_cases hq : (v.1 / (n : ℤ), v.2 / (n : ℤ)) = q
      · rw [if_pos hq, if_pos ((hkey q).mp hq)]
      · rw [if_neg hq, if_neg fun h => hq ((hkey q).mpr h)]
    · rw [if_neg hp, if_neg fun h => hp ((hkey p).mpr h)]
      by_cases hq : (v.1 / (n : ℤ), v.2 / (n : ℤ)) = q
      · rw [if_pos hq, if_pos ((hkey q).mp hq)]
      · rw [if_neg hq, if_neg fun h => hq ((hkey q).mpr h)]
  · rw [if_neg hv]
    have hp : v ≠ (n * p.1, n * p.2) := by
      intro h
      refine hv ⟨?_, ?_⟩
      · rw [congrArg Prod.fst h]; exact hdivl p.1
      · rw [congrArg Prod.snd h]; exact hdivl p.2
    have hq : v ≠ (n * q.1, n * q.2) := by
      intro h
      refine hv ⟨?_, ?_⟩
      · rw [congrArg Prod.fst h]; exact hdivl q.1
      · rw [congrArg Prod.snd h]; exact hdivl q.2
    rw [if_neg hp, if_neg hq, add_zero]

/-! ## The constant `2`-chain -/

/-- The constant `2`-chain (all cells). -/
def Theta2 : C2 := fun _ => 1

lemma bdry2_Theta2 : bdry2 Theta2 = 0 := by
  funext e
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [bdry2, Theta2, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · simp only [bdry2, Theta2, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

lemma add_Theta2_apply (w : C2) (c : Cell) : (w + Theta2) c = w c + 1 := rfl

/-! ## Loci of chains -/

/-- The locus of a `2`-chain: the union of the closed cells in its support. -/
def locus (h : ℝ) (w : C2) : Set Pt := {z | ∃ c, w c ≠ 0 ∧ z ∈ gsq h c}

/-- The locus of a `1`-chain: the union of the closed segments in its support. -/
def elocus (h : ℝ) (l : Edge → ZMod 2) : Set Pt := {z | ∃ e, l e ≠ 0 ∧ z ∈ gseg h e}

lemma mem_locus {h : ℝ} {w : C2} {z : Pt} : z ∈ locus h w ↔ ∃ c, w c ≠ 0 ∧ z ∈ gsq h c :=
  Iff.rfl

lemma mem_elocus {h : ℝ} {l : Edge → ZMod 2} {z : Pt} :
    z ∈ elocus h l ↔ ∃ e, l e ≠ 0 ∧ z ∈ gseg h e := Iff.rfl

lemma elocus_add_subset {h : ℝ} {l l' : Edge → ZMod 2} :
    elocus h (l + l') ⊆ elocus h l ∪ elocus h l' := by
  rintro z ⟨e, he, hz⟩
  rw [Pi.add_apply] at he
  rcases eq_or_ne (l e) 0 with h0 | h0
  · exact Or.inr ⟨e, by rw [h0, zero_add] at he; exact he, hz⟩
  · exact Or.inl ⟨e, h0, hz⟩

/-! ## Segments and cells -/

lemma mem_gseg_false {h : ℝ} (hh : 0 < h) {i j : ℤ} {z : Pt} :
    z ∈ gseg h (false,i,j) ↔ z 0 = h * i ∧ h * j ≤ z 1 ∧ z 1 ≤ h * (j+1) := by
  constructor
  · intro hz
    rw [gseg, segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [gptH, gpt, eTail_false, eHead_false]; push_cast; simp)
    · ring
    · nlinarith [ht.1, ht.2, hh]
    · nlinarith [ht.1, ht.2, hh]
  · rintro ⟨h0, h1, h2⟩
    rw [gseg, segment_eq_image]
    refine ⟨(z 1 - h * j) / h, ⟨?_, ?_⟩, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one hh]; linarith
    · ext k
      fin_cases k
      · simp only [gptH, gpt, eTail_false, eHead_false]
        simp
        field_simp
        linarith
      · simp only [gptH, gpt, eTail_false, eHead_false]
        push_cast
        simp
        field_simp
        ring

lemma mem_gseg_true {h : ℝ} (hh : 0 < h) {i j : ℤ} {z : Pt} :
    z ∈ gseg h (true,i,j) ↔ z 1 = h * j ∧ h * i ≤ z 0 ∧ z 0 ≤ h * (i+1) := by
  constructor
  · intro hz
    rw [gseg, segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [gptH, gpt, eTail_true, eHead_true]; push_cast; simp)
    · ring
    · nlinarith [ht.1, ht.2, hh]
    · nlinarith [ht.1, ht.2, hh]
  · rintro ⟨h0, h1, h2⟩
    rw [gseg, segment_eq_image]
    refine ⟨(z 0 - h * i) / h, ⟨?_, ?_⟩, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one hh]; linarith
    · ext k
      fin_cases k
      · simp only [gptH, gpt, eTail_true, eHead_true]
        push_cast
        simp
        field_simp
        ring
      · simp only [gptH, gpt, eTail_true, eHead_true]
        simp
        field_simp
        linarith


/-! ## Edge and cell comparisons between the coarse and the fine mesh -/

lemma intCast_ediv_of_dvd {n i : ℤ} (hn : 0 < n) (h : n ∣ i) :
    (((i / n : ℤ)) : ℝ) = (i : ℝ) / (n : ℝ) := by
  have h1 : n * (i / n) = i := Int.mul_ediv_cancel' h
  have h2 : ((n : ℝ)) * (((i / n : ℤ)) : ℝ) = (i : ℝ) := by exact_mod_cast h1
  rw [eq_div_iff (by exact_mod_cast (ne_of_gt hn) : (n : ℝ) ≠ 0)]
  linarith

lemma intCast_ediv_le {n j : ℤ} (hn : 0 < n) : (((j / n : ℤ)) : ℝ) ≤ (j : ℝ) / (n : ℝ) := by
  have h1 : n * (j / n) ≤ j := by
    have h2 := Int.mul_ediv_add_emod j n
    have h3 : 0 ≤ j % n := Int.emod_nonneg j (ne_of_gt hn)
    omega
  have h4 : ((n : ℝ)) * (((j / n : ℤ)) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
  rw [le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]
  linarith

lemma real_ediv_succ_le {n j : ℤ} (hn : 0 < n) :
    ((j : ℝ) + 1) / (n : ℝ) ≤ (((j / n : ℤ)) : ℝ) + 1 := by
  have h1 : j + 1 ≤ n * (j / n) + n := by
    have h2 := Int.mul_ediv_add_emod j n
    have h3 : j % n < n := Int.emod_lt_of_pos j hn
    omega
  have h4 : (j : ℝ) + 1 ≤ ((n : ℝ)) * (((j / n : ℤ)) : ℝ) + (n : ℝ) := by exact_mod_cast h1
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]
  have h5 : (((j / n : ℤ)) : ℝ) * (n : ℝ) = ((n : ℝ)) * (((j / n : ℤ)) : ℝ) := by ring
  linarith [h4, h5]

lemma div_mul_eq' {h n a : ℝ} : (h / n) * a = h * (a / n) := by ring

/-- A fine vertical grid edge lies in the coarse vertical edge that tiles it. -/
lemma gseg_sub1_false {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) {l : Edge → ZMod 2}
    {i j : ℤ} (hdvd : (n : ℤ) ∣ i) (hl : l (false, i / (n : ℤ), j / (n : ℤ)) ≠ 0) :
    ∃ e : Edge, l e ≠ 0 ∧ gseg (h / n) (false, i, j) ⊆ gseg h e := by
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh' : 0 < h / n := div_pos hh hnR
  refine ⟨(false, i / (n : ℤ), j / (n : ℤ)), hl, ?_⟩
  intro z hz
  rw [mem_gseg_false hh'] at hz
  rw [mem_gseg_false hh]
  have hx : (h / n) * (i : ℝ) = h * (((i / (n : ℤ) : ℤ)) : ℝ) := by
    rw [intCast_ediv_of_dvd hnZ hdvd]
    rw [show (((n : ℤ) : ℝ)) = (n : ℝ) from Int.cast_natCast n]
    field_simp
  have hlow : h * (((j / (n : ℤ) : ℤ)) : ℝ) ≤ (h / n) * (j : ℝ) := by
    calc h * (((j / (n : ℤ) : ℤ)) : ℝ) ≤ h * ((j : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (intCast_ediv_le hnZ (j := j)) hh.le
      _ = (h / n) * (j : ℝ) := (div_mul_eq' (h := h) (n := (n : ℝ)) (a := (j : ℝ))).symm
  have hhigh : (h / n) * ((j : ℝ) + 1) ≤ h * ((((j / (n : ℤ) : ℤ)) : ℝ) + 1) := by
    calc (h / n) * ((j : ℝ) + 1) = h * (((j : ℝ) + 1) / (n : ℝ)) :=
          div_mul_eq' (h := h) (n := (n : ℝ)) (a := (j : ℝ) + 1)
      _ ≤ h * ((((j / (n : ℤ) : ℤ)) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (real_ediv_succ_le hnZ (j := j)) hh.le
  exact ⟨by rw [hz.1, hx], by linarith [hz.2.1, hlow], by linarith [hz.2.2, hhigh]⟩

/-- A fine horizontal grid edge lies in the coarse horizontal edge that tiles it. -/
lemma gseg_sub1_true {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) {l : Edge → ZMod 2}
    {i j : ℤ} (hdvd : (n : ℤ) ∣ j) (hl : l (true, i / (n : ℤ), j / (n : ℤ)) ≠ 0) :
    ∃ e : Edge, l e ≠ 0 ∧ gseg (h / n) (true, i, j) ⊆ gseg h e := by
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh' : 0 < h / n := div_pos hh hnR
  refine ⟨(true, i / (n : ℤ), j / (n : ℤ)), hl, ?_⟩
  intro z hz
  rw [mem_gseg_true hh'] at hz
  rw [mem_gseg_true hh]
  have hx : (h / n) * (j : ℝ) = h * (((j / (n : ℤ) : ℤ)) : ℝ) := by
    rw [intCast_ediv_of_dvd hnZ hdvd]
    rw [show (((n : ℤ) : ℝ)) = (n : ℝ) from Int.cast_natCast n]
    field_simp
  have hlow : h * (((i / (n : ℤ) : ℤ)) : ℝ) ≤ (h / n) * (i : ℝ) := by
    calc h * (((i / (n : ℤ) : ℤ)) : ℝ) ≤ h * ((i : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (intCast_ediv_le hnZ (j := i)) hh.le
      _ = (h / n) * (i : ℝ) := (div_mul_eq' (h := h) (n := (n : ℝ)) (a := (i : ℝ))).symm
  have hhigh : (h / n) * ((i : ℝ) + 1) ≤ h * ((((i / (n : ℤ) : ℤ)) : ℝ) + 1) := by
    calc (h / n) * ((i : ℝ) + 1) = h * (((i : ℝ) + 1) / (n : ℝ)) :=
          div_mul_eq' (h := h) (n := (n : ℝ)) (a := (i : ℝ) + 1)
      _ ≤ h * ((((i / (n : ℤ) : ℤ)) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (real_ediv_succ_le hnZ (j := i)) hh.le
  exact ⟨by rw [hz.1, hx], by linarith [hz.2.1, hlow], by linarith [hz.2.2, hhigh]⟩

/-- A fine edge of the subdivision lies in the coarse edge it tiles. -/
lemma gseg_sub1_subset {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) {l : Edge → ZMod 2}
    {e' : Edge} (he' : sub1 n l e' ≠ 0) :
    ∃ e : Edge, l e ≠ 0 ∧ gseg (h / n) e' ⊆ gseg h e := by
  obtain ⟨b, i, j⟩ := e'
  cases b
  · simp only [sub1] at he'
    by_cases hdvd : (n : ℤ) ∣ i
    · rw [if_pos hdvd] at he'
      exact gseg_sub1_false hn hh hdvd he'
    · rw [if_neg hdvd] at he'
      exact absurd he' (by simp)
  · simp only [sub1] at he'
    by_cases hdvd : (n : ℤ) ∣ j
    · rw [if_pos hdvd] at he'
      exact gseg_sub1_true hn hh hdvd he'
    · rw [if_neg hdvd] at he'
      exact absurd he' (by simp)

/-- The locus of a subdivided chain is contained in the locus of the chain. -/
lemma elocus_sub1_subset {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) {l : Edge → ZMod 2} :
    elocus (h / n) (sub1 n l) ⊆ elocus h l := by
  rintro z ⟨e', he', hz⟩
  obtain ⟨e, hle, hsub⟩ := gseg_sub1_subset hn hh he'
  exact ⟨e, hle, hsub hz⟩

/-- A fine cell of the subdivision lies in the coarse cell it tiles. -/
lemma gsq_sub2_subset {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (c : Cell) :
    gsq (h / n) c ⊆ gsq h (c.1 / (n : ℤ), c.2 / (n : ℤ)) := by
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  rintro z ⟨h1, h2, h3, h4⟩
  have hlow : ∀ a : ℤ, h * (((a / (n : ℤ) : ℤ)) : ℝ) ≤ (h / n) * (a : ℝ) := by
    intro a
    calc h * (((a / (n : ℤ) : ℤ)) : ℝ) ≤ h * ((a : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (intCast_ediv_le hnZ (j := a)) hh.le
      _ = (h / n) * (a : ℝ) := (div_mul_eq' (h := h) (n := (n : ℝ)) (a := (a : ℝ))).symm
  have hhigh : ∀ a : ℤ, (h / n) * ((a : ℝ) + 1) ≤ h * ((((a / (n : ℤ) : ℤ)) : ℝ) + 1) := by
    intro a
    calc (h / n) * ((a : ℝ) + 1) = h * (((a : ℝ) + 1) / (n : ℝ)) :=
          div_mul_eq' (h := h) (n := (n : ℝ)) (a := (a : ℝ) + 1)
      _ ≤ h * ((((a / (n : ℤ) : ℤ)) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (real_ediv_succ_le hnZ (j := a)) hh.le
  exact ⟨by linarith [hlow c.1, h1], by linarith [hhigh c.1, h2],
    by linarith [hlow c.2, h3], by linarith [hhigh c.2, h4]⟩

/-- A vertical grid edge also lies in the cell to its left. -/
lemma gseg_false_subset_gsq_left {h : ℝ} (hh : 0 < h) (i j : ℤ) :
    gseg h (false,i,j) ⊆ gsq h (i-1, j) := by
  intro z hz
  rw [mem_gseg_false hh] at hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith [hz.1, hz.2.1, hz.2.2, hh]

/-- A horizontal grid edge also lies in the cell below it. -/
lemma gseg_true_subset_gsq_below {h : ℝ} (hh : 0 < h) (i j : ℤ) :
    gseg h (true,i,j) ⊆ gsq h (i, j-1) := by
  intro z hz
  rw [mem_gseg_true hh] at hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith [hz.1, hz.2.1, hz.2.2, hh]

/-- The locus of a `2`-chain contains the locus of its boundary. -/
lemma elocus_bdry2_subset_locus {h : ℝ} (hh : 0 < h) (w : C2) :
    elocus h (bdry2 w) ⊆ locus h w := by
  rintro z ⟨e, he, hz⟩
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [bdry2] at he
    by_cases h1 : w (i,j) = 0
    · refine ⟨(i-1,j), ?_, gseg_false_subset_gsq_left hh i j hz⟩
      intro h0
      exact he (by rw [h1, h0, add_zero])
    · exact ⟨(i,j), h1, gseg_subset_gsq hh _ hz⟩
  · simp only [bdry2] at he
    by_cases h1 : w (i,j) = 0
    · refine ⟨(i,j-1), ?_, gseg_true_subset_gsq_below hh i j hz⟩
      intro h0
      exact he (by rw [h1, h0, add_zero])
    · exact ⟨(i,j), h1, gseg_subset_gsq hh _ hz⟩

/-- The scaled grid vertex `n • p` at the fine mesh `h/n` is the grid vertex `p` at the mesh
`h`. -/
lemma gptH_scaled {n : ℕ} (hn : 0 < n) {h : ℝ} (p : ℤ × ℤ) :
    gptH (h / n) (n * p.1, n * p.2) = gptH h p := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : (h / (n : ℝ)) * (((n : ℤ) : ℝ) * (p.1 : ℝ)) = h * (p.1 : ℝ) := by
    rw [show (((n : ℤ) : ℝ)) = (n : ℝ) from Int.cast_natCast n]
    field_simp
  have hy : (h / (n : ℝ)) * (((n : ℤ) : ℝ) * (p.2 : ℝ)) = h * (p.2 : ℝ) := by
    rw [show (((n : ℤ) : ℝ)) = (n : ℝ) from Int.cast_natCast n]
    field_simp
  ext k
  fin_cases k
  · simp only [gptH, gpt, Prod.fst_mul]
    push_cast
    simp
    exact hx
  · simp only [gptH, gpt, Prod.snd_mul]
    push_cast
    simp
    exact hy

/-- Joining two nearby points by a segment, when both are far from `S`. -/
lemma joinedIn_seg {S : Set Pt} {x y : Pt} {r : ℝ} (hr : 0 < r) (hxy : dist x y ≤ r)
    (hx : ∀ s ∈ S, 20 * r ≤ dist x s) : JoinedIn (Sᶜ) x y := by
  refine ⟨segPath x y, fun t => ?_⟩
  rw [Set.mem_compl_iff]
  intro hs
  have h1 : 20 * r ≤ dist x (segPath x y t) := hx (segPath x y t) hs
  have h2 : dist x (segPath x y t) ≤ r := by
    have hmem := segPath_mem x y t
    rw [segment_eq_image] at hmem
    obtain ⟨u, hu, huv⟩ := hmem
    have hval : segPath x y t = (1 - (u : ℝ)) • x + (u : ℝ) • y := huv.symm
    calc dist x (segPath x y t)
        = dist x ((1 - (u : ℝ)) • x + (u : ℝ) • y) := by rw [hval]
      _ = ‖x - ((1 - (u : ℝ)) • x + (u : ℝ) • y)‖ := by rw [dist_eq_norm]
      _ = ‖(u : ℝ) • (x - y)‖ := by
        rw [show x - ((1 - (u : ℝ)) • x + (u : ℝ) • y) = (u : ℝ) • (x - y) from by module]
      _ = |(u : ℝ)| * ‖x - y‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = u * dist x y := by rw [abs_of_nonneg hu.1, dist_eq_norm]
      _ ≤ dist x y := mul_le_of_le_one_left dist_nonneg hu.2
      _ ≤ r := hxy
  linarith [h1, h2, hr]

/-- Translating the whole plane transports `JoinedIn` (in the complement of the translated
set). -/
lemma joinedIn_compl_sub_iff {S : Set Pt} {x y : Pt} (w : Pt) :
    JoinedIn (((fun z => z - w) '' S)ᶜ) (x - w) (y - w) ↔ JoinedIn (Sᶜ) x y := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨⟨⟨fun t => γ t + w, γ.continuous.add continuous_const⟩, ?_, ?_⟩, ?_⟩
    · dsimp only
      rw [Path.source]
      abel
    · dsimp only
      rw [Path.target]
      abel
    · intro t
      rw [Set.mem_compl_iff]
      rintro hs
      have h1 : γ t ∈ ((fun z => z - w) '' S)ᶜ := hγ t
      rw [Set.mem_compl_iff] at h1
      refine h1 ⟨γ t + w, hs, ?_⟩
      simp
  · rintro ⟨γ, hγ⟩
    refine ⟨⟨⟨fun t => γ t - w, γ.continuous.sub continuous_const⟩, ?_, ?_⟩, ?_⟩
    · dsimp only
      rw [Path.source]
    · dsimp only
      rw [Path.target]
    · intro t
      rw [Set.mem_compl_iff]
      rintro ⟨s, hs, hsv⟩
      have h1 : γ t ∈ Sᶜ := hγ t
      rw [Set.mem_compl_iff] at h1
      refine h1 ?_
      have h3 : γ t = s := by
        simpa using (congrArg (fun z : Pt => z + w) hsv).symm
      rw [h3]
      exact hs

/-- The fine edge of index `k ∈ [0,n)` lying on the coarse edge `e`. -/
def sub1Inv (n : ℕ) (e : Edge) (k : ℕ) : Edge :=
  match e with
  | (false,I,J) => (false, (n:ℤ)*I, (n:ℤ)*J + (k:ℤ))
  | (true,I,J) => (true, (n:ℤ)*I + (k:ℤ), (n:ℤ)*J)

/-- The subdivision of a finitely supported `1`-chain at a positive subdivision factor is
finitely supported. -/
lemma support_sub1_finite {n : ℕ} (hn : 0 < n) {l : Edge → ZMod 2}
    (hl : (Function.support l).Finite) : (Function.support (sub1 n l)).Finite := by
  classical
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hsub : Function.support (sub1 n l) ⊆
      ⋃ e ∈ Function.support l, ⋃ k ∈ Finset.range n, ({sub1Inv n e k} : Set Edge) := by
    intro e' he'
    obtain ⟨b,i,j⟩ := e'
    cases b
    · simp only [sub1, Function.mem_support] at he'
      by_cases hd : (n:ℤ) ∣ i
      · rw [if_pos hd] at he'
        have hI : i = (n:ℤ) * (i / (n:ℤ)) := (Int.mul_ediv_cancel' hd).symm
        have hj : j = (n:ℤ) * (j / (n:ℤ)) + (j % (n:ℤ)) :=
          (Int.mul_ediv_add_emod j (n:ℤ)).symm
        have hjn : 0 ≤ j % (n:ℤ) := Int.emod_nonneg j hnZ
        have hjl : j % (n:ℤ) < (n:ℤ) := Int.emod_lt_of_pos j (by exact_mod_cast hn)
        have hk : (j % (n:ℤ)).toNat ∈ Finset.range n := by
          rw [Finset.mem_range]
          omega
        refine Set.mem_iUnion.mpr ⟨(false, i / (n:ℤ), j / (n:ℤ)), ?_⟩
        refine Set.mem_iUnion.mpr ⟨he', ?_⟩
        refine Set.mem_iUnion.mpr ⟨(j % (n:ℤ)).toNat, ?_⟩
        refine Set.mem_iUnion.mpr ⟨hk, ?_⟩
        simp only [Set.mem_singleton_iff, sub1Inv]
        rw [Int.toNat_of_nonneg hjn]
        exact Prod.ext rfl (Prod.ext hI hj)
      · rw [if_neg hd] at he'
        exact absurd he' (by simp)
    · simp only [sub1, Function.mem_support] at he'
      by_cases hd : (n:ℤ) ∣ j
      · rw [if_pos hd] at he'
        have hJ : j = (n:ℤ) * (j / (n:ℤ)) := (Int.mul_ediv_cancel' hd).symm
        have hi : i = (n:ℤ) * (i / (n:ℤ)) + (i % (n:ℤ)) :=
          (Int.mul_ediv_add_emod i (n:ℤ)).symm
        have hin : 0 ≤ i % (n:ℤ) := Int.emod_nonneg i hnZ
        have hil : i % (n:ℤ) < (n:ℤ) := Int.emod_lt_of_pos i (by exact_mod_cast hn)
        have hk : (i % (n:ℤ)).toNat ∈ Finset.range n := by
          rw [Finset.mem_range]
          omega
        refine Set.mem_iUnion.mpr ⟨(true, i / (n:ℤ), j / (n:ℤ)), ?_⟩
        refine Set.mem_iUnion.mpr ⟨he', ?_⟩
        refine Set.mem_iUnion.mpr ⟨(i % (n:ℤ)).toNat, ?_⟩
        refine Set.mem_iUnion.mpr ⟨hk, ?_⟩
        simp only [Set.mem_singleton_iff, sub1Inv]
        rw [Int.toNat_of_nonneg hin]
        exact Prod.ext rfl (Prod.ext hi hJ)
      · rw [if_neg hd] at he'
        exact absurd he' (by simp)
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion hl (fun e _ => ?_)
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun k _ => ?_)
  exact Set.finite_singleton _

lemma bdry2_add (a b : C2) : bdry2 (a + b) = bdry2 a + bdry2 b := by
  funext e
  obtain ⟨bb, i, j⟩ := e
  cases bb <;> simp only [bdry2, Pi.add_apply] <;> abel

lemma isClosed_gsq (h : ℝ) (c : Cell) : IsClosed (gsq h c) := by
  have h1 : IsClosed {x : Pt | h * (c.1 : ℝ) ≤ x 0} :=
    isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {x : Pt | x 0 ≤ h * ((c.1 : ℝ) + 1)} :=
    isClosed_le (by fun_prop) continuous_const
  have h3 : IsClosed {x : Pt | h * (c.2 : ℝ) ≤ x 1} :=
    isClosed_le continuous_const (by fun_prop)
  have h4 : IsClosed {x : Pt | x 1 ≤ h * ((c.2 : ℝ) + 1)} :=
    isClosed_le (by fun_prop) continuous_const
  have heq : gsq h c = {x : Pt | h * (c.1 : ℝ) ≤ x 0}
      ∩ {x : Pt | x 0 ≤ h * ((c.1 : ℝ) + 1)}
      ∩ {x : Pt | h * (c.2 : ℝ) ≤ x 1}
      ∩ {x : Pt | x 1 ≤ h * ((c.2 : ℝ) + 1)} := by
    ext x
    simp only [gsq, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact ((h1.inter h2).inter h3).inter h4

/-- A finite union of compact sets is compact. -/
lemma isCompact_biUnion_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Set Pt}
    (hf : ∀ i ∈ s, IsCompact (f i)) : IsCompact (⋃ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have hstep : (⋃ cc ∈ insert a s, f cc) = (f a ∪ ⋃ cc ∈ s, f cc) := by
      ext z
      simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨cc, (rfl | hcc), hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨cc, hcc, hz⟩
      · rintro (hz | ⟨cc, hcc, hz⟩)
        · exact ⟨a, Or.inl rfl, hz⟩
        · exact ⟨cc, Or.inr hcc, hz⟩
    rw [hstep]
    exact (hf a (Finset.mem_insert_self a s)).union
      (ih (fun cc hc => hf cc (Finset.mem_insert_of_mem hc)))

end

end Grid

end Work.Whitney.PathTools
