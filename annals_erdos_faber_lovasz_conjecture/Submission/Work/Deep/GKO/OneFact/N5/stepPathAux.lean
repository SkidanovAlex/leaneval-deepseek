import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.StepTools
import Submission.Work.Deep.GKO.OneFactDefs

/-!
# A single step path (backup proof of `exists_stepPath`)

This module proves the one-step path existence input of
`Work.Deep.GKO.OneFact.N5.completeInsideMatching` **with the additional hypothesis `Disjoint A B`**
(which the consumer has): given `u ∈ A ∩ U'` and `w ∈ B ∩ U'`, the lower regularity of the cross
graph `K` and the degree bound `degIn K v (univ \ F) ≥ D` produce an alternating path
`u -K- a -N- b -K- c -N- d -K- w` whose interior avoids `F`, `U'` and the "used" set `W`.

The two candidate sets are

* `cand N K U' F W u` — the `N`-mates of the "good" `K`-neighbours of `u`,
* `cand N K U' F W w` — the same for `w`,

which live on the two sides of the bipartition and both have at least
`D - (2b + 2|W| + |F|) > εn` elements.  `BipLowerReg` then supplies a `K`-edge between them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO.OneFact.N5

open Classical

noncomputable section

variable {n : ℕ}

/-- `nmate` is injective on the covered vertices. -/
theorem nmate_injOn {N : SimpleGraph (Fin n)} (hN : Work.Deep.GKO.IsMatching' N) {x y : Fin n}
    (hx : ∃ z, N.Adj x z) (hy : ∃ z, N.Adj y z) (h : nmate N x = nmate N y) : x = y := by
  have h1 : N.Adj x (nmate N x) := nmate_spec hx
  have h2 : N.Adj y (nmate N y) := nmate_spec hy
  rw [h] at h1
  exact hN (nmate N y) x y ((N.adj_comm x _).mp h1) ((N.adj_comm y _).mp h2)

/-- The candidate set for one end of a step path: the `N`-mates of the `K`-neighbours of `u`
outside `F` whose mate avoids `F`, `U'` and `W`. -/
def cand (N K : SimpleGraph (Fin n)) (U' F W : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  ((Work.Deep.GKO.nbrFinset K u (Finset.univ \ F)).filter
    (fun x => x ∉ U' ∧ x ∉ W ∧ ∃ y, N.Adj x y ∧ y ∉ F ∧ y ∉ U' ∧ y ∉ W)).image (nmate N)

theorem cand_mem {N K : SimpleGraph (Fin n)} {U' F W : Finset (Fin n)} {u : Fin n}
    (hN : Work.Deep.GKO.IsMatching' N) {y : Fin n} (hy : y ∈ cand N K U' F W u) :
    ∃ x, K.Adj u x ∧ x ∉ F ∧ x ∉ U' ∧ x ∉ W ∧ N.Adj x y ∧
      y ∉ F ∧ y ∉ U' ∧ y ∉ W := by
  rw [cand, Finset.mem_image] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [Finset.mem_filter] at hx
  obtain ⟨hxKu, hxU, hxW, hxmate⟩ := hx
  have hxadj : K.Adj u x := (Work.Deep.GKO.mem_nbrFinset.mp hxKu).2
  have hxF : x ∉ F := (Finset.mem_sdiff.mp (Work.Deep.GKO.mem_nbrFinset.mp hxKu).1).2
  obtain ⟨z, hxz, hzF, hzU, hzW⟩ := hxmate
  have hzy : z = y := by rw [← hxy]; exact (nmate_eq_of hN hxz).symm
  subst hzy
  exact ⟨x, hxadj, hxF, hxU, hxW, hxz, hzF, hzU, hzW⟩

/-- The cardinality bound for a candidate set. -/
theorem cand_card {N K : SimpleGraph (Fin n)} {U' F W S : Finset (Fin n)} {u : Fin n} {D b : ℕ}
    (hN : Work.Deep.GKO.IsMatching' N)
    (hdeg : D ≤ Work.Deep.GKO.degIn K u (Finset.univ \ F))
    (hsub : Work.Deep.GKO.nbrFinset K u (Finset.univ \ F) ⊆ S)
    (hclosed : ∀ x y, N.Adj x y → (x ∈ U' ↔ y ∈ U'))
    (hcover : ∀ x, x ∈ S → x ∉ U' → ∃ y, N.Adj x y)
    (hb : (U' ∩ S).card ≤ b) :
    D - (2 * b + 2 * W.card + F.card) ≤ (cand N K U' F W u).card := by
  classical
  set Ku : Finset (Fin n) := Work.Deep.GKO.nbrFinset K u (Finset.univ \ F) with hKu
  set Sel : Finset (Fin n) := Ku.filter (fun x => x ∉ U' ∧ x ∉ W ∧
    ∃ y, N.Adj x y ∧ y ∉ F ∧ y ∉ U' ∧ y ∉ W) with hSel
  have hcand : cand N K U' F W u = Sel.image (nmate N) := by rw [cand, hSel, hKu]
  have hinjOn : Set.InjOn (nmate N) ↑Sel := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    rw [hSel, Finset.mem_filter] at hx hy
    obtain ⟨-, -, -, ⟨zx, hxz, -⟩⟩ := hx
    obtain ⟨-, -, -, ⟨zy, hzy, -⟩⟩ := hy
    exact nmate_injOn hN ⟨zx, hxz⟩ ⟨zy, hzy⟩ hxy
  have hSelcard : Sel.card = (cand N K U' F W u).card := by
    rw [hcand, Finset.card_image_of_injOn hinjOn]
  set P1 : Finset (Fin n) := U' ∩ Ku with hP1
  set P2 : Finset (Fin n) := W ∩ Ku with hP2
  set P3 : Finset (Fin n) := Ku.filter (fun x => (∃ y, N.Adj x y) ∧ nmate N x ∈ F) with hP3
  set P4 : Finset (Fin n) := Ku.filter (fun x => (∃ y, N.Adj x y) ∧ nmate N x ∈ U') with hP4
  set P5 : Finset (Fin n) := Ku.filter (fun x => (∃ y, N.Adj x y) ∧ nmate N x ∈ W) with hP5
  have hsub' : Ku \ Sel ⊆ P1 ∪ P2 ∪ P3 ∪ P4 ∪ P5 := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxKu, hxSel⟩ := hx
    have hUn : x ∈ P1 ∪ P2 ∪ P3 ∪ P4 ∪ P5 := by
      simp only [Finset.mem_union]
      by_cases hxU : x ∈ U'
      · have hP1mem : x ∈ P1 := by
          rw [hP1]; exact Finset.mem_inter.mpr ⟨hxU, hxKu⟩
        exact Or.inl (Or.inl (Or.inl (Or.inl hP1mem)))
      by_cases hxW : x ∈ W
      · have hP2mem : x ∈ P2 := by
          rw [hP2]; exact Finset.mem_inter.mpr ⟨hxW, hxKu⟩
        exact Or.inl (Or.inl (Or.inl (Or.inr hP2mem)))
      obtain ⟨y, hxy⟩ := hcover x (hsub hxKu) hxU
      have hymate : y = nmate N x := (nmate_eq_of hN hxy).symm
      by_cases hyF : nmate N x ∈ F
      · have hP3mem : x ∈ P3 := by
          rw [hP3]; exact Finset.mem_filter.mpr ⟨hxKu, ⟨y, hxy⟩, hyF⟩
        exact Or.inl (Or.inl (Or.inr hP3mem))
      by_cases hyU : nmate N x ∈ U'
      · have hP4mem : x ∈ P4 := by
          rw [hP4]; exact Finset.mem_filter.mpr ⟨hxKu, ⟨y, hxy⟩, hyU⟩
        exact Or.inl (Or.inr hP4mem)
      by_cases hyW : nmate N x ∈ W
      · have hP5mem : x ∈ P5 := by
          rw [hP5]; exact Finset.mem_filter.mpr ⟨hxKu, ⟨y, hxy⟩, hyW⟩
        exact Or.inr hP5mem
      · exact absurd (Finset.mem_filter.mpr
          ⟨hxKu, hxU, hxW, ⟨y, hxy, hymate ▸ hyF, hymate ▸ hyU, hymate ▸ hyW⟩⟩) hxSel
    exact hUn
  have hP1c : P1.card ≤ b := by
    rw [hP1]
    exact le_trans (Finset.card_le_card (fun x hx => by
      rw [Finset.mem_inter] at hx
      exact Finset.mem_inter.mpr ⟨hx.1, hsub hx.2⟩)) hb
  have hP2c : P2.card ≤ W.card := by
    rw [hP2]; exact Finset.card_le_card Finset.inter_subset_left
  have hP3c : P3.card ≤ F.card := by
    rw [hP3]
    refine Finset.card_le_card_of_injOn (nmate N) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2.2
    · rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact nmate_injOn hN hx.2.1 hy.2.1 hxy
  have hP4c : P4.card ≤ b := by
    rw [hP4]
    refine le_trans (Finset.card_le_card (fun x hx => ?_)) hb
    rw [Finset.mem_filter] at hx
    exact Finset.mem_inter.mpr
      ⟨(hclosed x (nmate N x) (nmate_spec hx.2.1)).mpr hx.2.2, hsub hx.1⟩
  have hP5c : P5.card ≤ W.card := by
    rw [hP5]
    refine Finset.card_le_card_of_injOn (nmate N) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2.2
    · rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact nmate_injOn hN hx.2.1 hy.2.1 hxy
  have hbig : Ku.card ≤ Sel.card + (b + (W.card + (F.card + (b + W.card)))) := by
    have h1 : (Ku \ Sel).card = Ku.card - (Sel ∩ Ku).card := Finset.card_sdiff
    have h2 : (Sel ∩ Ku).card ≤ Sel.card := Finset.card_le_card Finset.inter_subset_left
    have h3 : (Ku \ Sel).card ≤ (P1 ∪ P2 ∪ P3 ∪ P4 ∪ P5).card := Finset.card_le_card hsub'
    have h4 : (P1 ∪ P2 ∪ P3 ∪ P4 ∪ P5).card
        ≤ P1.card + (P2.card + (P3.card + (P4.card + P5.card))) := by
      have a1 := Finset.card_union_le (P1 ∪ P2 ∪ P3 ∪ P4) P5
      have a2 := Finset.card_union_le (P1 ∪ P2 ∪ P3) P4
      have a3 := Finset.card_union_le (P1 ∪ P2) P3
      have a4 := Finset.card_union_le P1 P2
      omega
    omega
  have hKu : D ≤ Ku.card := hdeg
  have : Sel.card ≥ D - (2 * b + 2 * W.card + F.card) := by omega
  omega

/-- The candidate set of `u ∉ B` lies in `B`. -/
theorem cand_subset_B {N K : SimpleGraph (Fin n)} {U' F W A B : Finset (Fin n)} {u : Fin n}
    (hN : Work.Deep.GKO.IsMatching' N) (hAB : Disjoint A B) (huB : u ∉ B)
    (hKbip : ∀ u v, K.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    cand N K U' F W u ⊆ B := by
  intro y hy
  rw [cand, Finset.mem_image] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [Finset.mem_filter] at hx
  obtain ⟨hxKu, -, -, hxmate⟩ := hx
  rw [Work.Deep.GKO.mem_nbrFinset] at hxKu
  have hxB : x ∈ B := by
    rcases hKbip u x hxKu.2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h huB
  obtain ⟨z, hxz, -⟩ := hxmate
  have hzmate : nmate N x = z := nmate_eq_of hN hxz
  have hzB : z ∈ B := by
    rcases hNin x z hxz with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (Finset.disjoint_left.mp hAB.symm hxB)
    · exact h2
  rw [← hxy, hzmate]
  exact hzB

/-- The candidate set of `u ∉ A` lies in `A`. -/
theorem cand_subset_A {N K : SimpleGraph (Fin n)} {U' F W A B : Finset (Fin n)} {u : Fin n}
    (hN : Work.Deep.GKO.IsMatching' N) (hAB : Disjoint A B) (huA : u ∉ A)
    (hKbip : ∀ u v, K.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    cand N K U' F W u ⊆ A := by
  intro y hy
  rw [cand, Finset.mem_image] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [Finset.mem_filter] at hx
  obtain ⟨hxKu, -, -, hxmate⟩ := hx
  rw [Work.Deep.GKO.mem_nbrFinset] at hxKu
  have hxA : x ∈ A := by
    rcases hKbip u x hxKu.2 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h huA
    · exact h
  obtain ⟨z, hxz, -⟩ := hxmate
  have hzmate : nmate N x = z := nmate_eq_of hN hxz
  have hzA : z ∈ A := by
    rcases hNin x z hxz with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 (Finset.disjoint_left.mp hAB hxA)
  rw [← hxy, hzmate]
  exact hzA

/-- **The step path.**  Under the additional hypothesis `Disjoint A B` (which the consumer
`completeInsideMatching` has) the path always exists. -/
theorem exists_stepPath_aux {n : ℕ} (A B U' F W : Finset (Fin n)) (N K : SimpleGraph (Fin n))
    (hAB : Disjoint A B)
    (hN : Work.Deep.GKO.IsMatching' N)
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hKbip : ∀ u v, K.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hclosed : ∀ u v, N.Adj u v → (u ∈ U' ↔ v ∈ U'))
    (hcover : ∀ x, x ∉ U' → ∃ y, N.Adj x y)
    {u w : Fin n} (huA : u ∈ A) (hwB : w ∈ B) (huU' : u ∈ U') (hwU' : w ∈ U')
    (hne : u ≠ w)
    {q ε : ℝ} {D b : ℕ} (hq : 0 < q) (hε : 0 < ε)
    (hlr : Work.Deep.GKO.BipLowerReg K A B q ε)
    (hdeg : ∀ v, D ≤ Work.Deep.GKO.degIn K v (Finset.univ \ F))
    (hbA : (U' ∩ A).card ≤ b) (hbB : (U' ∩ B).card ≤ b)
    (hroom : ε * (n : ℝ) + ((2 * b + 2 * W.card + F.card : ℕ) : ℝ) < (D : ℝ)) :
    ∃ v : Fin 6 → Fin n, Function.Injective v ∧ v 0 = u ∧ v 5 = w ∧
      K.Adj (v 0) (v 1) ∧ N.Adj (v 1) (v 2) ∧ K.Adj (v 2) (v 3) ∧ N.Adj (v 3) (v 4) ∧
      K.Adj (v 4) (v 5) ∧
      (v 1 ∉ F ∧ v 1 ∉ U' ∧ v 1 ∉ W) ∧ (v 2 ∉ F ∧ v 2 ∉ U' ∧ v 2 ∉ W) ∧
      (v 3 ∉ F ∧ v 3 ∉ U' ∧ v 3 ∉ W) ∧ (v 4 ∉ F ∧ v 4 ∉ U' ∧ v 4 ∉ W) := by
  classical
  have hnpos : 0 < n := by omega
  have hYsub : cand N K U' F W u ⊆ B :=
    cand_subset_B (N := N) (K := K) hN hAB (huB := fun h => Finset.disjoint_left.mp hAB huA h)
      hKbip hNin
  have hZsub : cand N K U' F W w ⊆ A :=
    cand_subset_A (N := N) (K := K) hN hAB (huA := fun h => Finset.disjoint_left.mp hAB.symm hwB h)
      hKbip hNin
  have hKuB : Work.Deep.GKO.nbrFinset K u (Finset.univ \ F) ⊆ B := by
    intro x hx
    rw [Work.Deep.GKO.mem_nbrFinset] at hx
    rcases hKbip u x hx.2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (Finset.disjoint_left.mp hAB huA)
  have hKwA : Work.Deep.GKO.nbrFinset K w (Finset.univ \ F) ⊆ A := by
    intro x hx
    rw [Work.Deep.GKO.mem_nbrFinset] at hx
    rcases hKbip w x hx.2 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (Finset.disjoint_left.mp hAB.symm hwB)
    · exact h
  have hYcard : D - (2 * b + 2 * W.card + F.card) ≤ (cand N K U' F W u).card :=
    cand_card (N := N) (K := K) hN (hdeg u) hKuB hclosed (fun x _ hxU => hcover x hxU) hbB
  have hZcard : D - (2 * b + 2 * W.card + F.card) ≤ (cand N K U' F W w).card :=
    cand_card (N := N) (K := K) hN (hdeg w) hKwA hclosed (fun x _ hxU => hcover x hxU) hbA
  have hDgap : ((2 * b + 2 * W.card + F.card : ℕ) : ℝ) < (D : ℝ) := by
    have hprod : (0 : ℝ) ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg n)
    have hr := hroom
    push_cast at hr ⊢
    linarith
  have hle : 2 * b + 2 * W.card + F.card ≤ D := by exact_mod_cast hDgap.le
  have hYbig : ε * (n : ℝ) < ((cand N K U' F W u).card : ℝ) := by
    have h1 : ((D - (2 * b + 2 * W.card + F.card) : ℕ) : ℝ)
        ≤ ((cand N K U' F W u).card : ℝ) := by exact_mod_cast hYcard
    rw [Nat.cast_sub hle] at h1
    linarith
  have hZbig : ε * (n : ℝ) < ((cand N K U' F W w).card : ℝ) := by
    have h1 : ((D - (2 * b + 2 * W.card + F.card) : ℕ) : ℝ)
        ≤ ((cand N K U' F W w).card : ℝ) := by exact_mod_cast hZcard
    rw [Nat.cast_sub hle] at h1
    linarith
  -- the cross edge supplied by lower regularity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hcross : 0 < crossEdges K (cand N K U' F W w) (cand N K U' F W u) := by
    have h := hlr (cand N K U' F W w) hZsub (cand N K U' F W u) hYsub hZbig.le hYbig.le
    have h1 : (0 : ℝ) < ((cand N K U' F W w).card : ℝ) := lt_trans (mul_pos hε hnR) hZbig
    have h2 : (0 : ℝ) < ((cand N K U' F W u).card : ℝ) := lt_trans (mul_pos hε hnR) hYbig
    have h3 : (0 : ℝ) < q * ((cand N K U' F W w).card : ℝ)
        * ((cand N K U' F W u).card : ℝ) := mul_pos (mul_pos hq h1) h2
    have h4 : (0 : ℝ) < (crossEdges K (cand N K U' F W w) (cand N K U' F W u) : ℝ) :=
      lt_of_lt_of_le h3 h
    exact_mod_cast h4
  obtain ⟨c, hcZ, b', hbY, hcb⟩ : ∃ c ∈ cand N K U' F W w, ∃ b' ∈ cand N K U' F W u,
      K.Adj c b' := by
    rw [crossEdges] at hcross
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcross
    rw [Finset.mem_filter] at hp
    obtain ⟨hpZ, hpY⟩ := Finset.mem_product.mp hp.1
    exact ⟨p.1, hpZ, p.2, hpY, hp.2⟩
  obtain ⟨a', hua', ha'F, ha'U, ha'W, hab, hb'F, hb'U, hb'W⟩ := cand_mem hN hbY
  obtain ⟨d', hwd', hd'F, hd'U, hd'W, hdc, hcF, hcU, hcW⟩ := cand_mem hN hcZ
  have ha'B : a' ∈ B := by
    rcases hKbip u a' hua' with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (Finset.disjoint_left.mp hAB huA)
  have hb'B : b' ∈ B := by
    rcases hNin a' b' hab with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd ha'B (Finset.disjoint_left.mp hAB h1)
    · exact h2
  have hd'A : d' ∈ A := by
    rcases hKbip w d' hwd' with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (Finset.disjoint_left.mp hAB.symm hwB)
    · exact h
  have hcA : c ∈ A := hZsub hcZ
  refine ⟨![u, a', b', c, d', w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity
    have h1 : u ≠ a' := fun h => ha'U (by rw [← h]; exact huU')
    have h2 : u ≠ b' := fun h => hb'U (by rw [← h]; exact huU')
    have h3 : u ≠ c := fun h => hcU (by rw [← h]; exact huU')
    have h4 : u ≠ d' := fun h => hd'U (by rw [← h]; exact huU')
    have h6 : w ≠ a' := fun h => ha'U (by rw [← h]; exact hwU')
    have h7 : w ≠ b' := fun h => hb'U (by rw [← h]; exact hwU')
    have h8 : w ≠ c := fun h => hcU (by rw [← h]; exact hwU')
    have h9 : w ≠ d' := fun h => hd'U (by rw [← h]; exact hwU')
    have h10 : a' ≠ b' := fun h => N.loopless.1 a' (by rw [← h] at hab; exact hab)
    have h11 : a' ≠ c := fun h => Finset.disjoint_left.mp hAB (h ▸ hcA) ha'B
    have h12 : a' ≠ d' := fun h => Finset.disjoint_left.mp hAB (h ▸ hd'A) ha'B
    have h13 : b' ≠ c := fun h => Finset.disjoint_left.mp hAB (h ▸ hcA) hb'B
    have h14 : b' ≠ d' := fun h => Finset.disjoint_left.mp hAB (h ▸ hd'A) hb'B
    have h15 : c ≠ d' := fun h => N.loopless.1 c (by rw [← h] at hdc; exact hdc)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_succ]
  · simp
  · simp
  · simpa using hua'
  · simpa using hab
  · simpa using (K.adj_comm c b').mp hcb
  · simpa using (N.adj_comm d' c).mp hdc
  · simpa using (K.adj_comm w d').mp hwd'
  · simpa using (show a' ∉ F ∧ a' ∉ U' ∧ a' ∉ W from ⟨ha'F, ha'U, ha'W⟩)
  · simpa using (show b' ∉ F ∧ b' ∉ U' ∧ b' ∉ W from ⟨hb'F, hb'U, hb'W⟩)
  · simpa using (show c ∉ F ∧ c ∉ U' ∧ c ∉ W from ⟨hcF, hcU, hcW⟩)
  · simpa using (show d' ∉ F ∧ d' ∉ U' ∧ d' ∉ W from ⟨hd'F, hd'U, hd'W⟩)

end

end Work.Deep.GKO.OneFact.N5
