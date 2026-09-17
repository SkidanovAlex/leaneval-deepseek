import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_posRoots_fixes_rho
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_descent
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_eq
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_bound
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_Nroot_cons_card
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_rho_sub_wact_rho_eq_sum

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The negative roots: `y ∈ E8negRoots ↔ -y ∈ E8posRoots.P`. -/
noncomputable def E8negRoots : Finset (Fin 8 → ℤ) := E8posRoots.P.image (fun v => -v)

/-- The positive roots sent to negative roots by `wact L`. -/
noncomputable def E8Nroot (L : List (Fin 8)) : Finset (Fin 8 → ℤ) :=
  E8posRoots.P.filter (fun y => -(wact L y) ∈ E8posRoots.P)

lemma mem_E8Nroot {L : List (Fin 8)} {y : Fin 8 → ℤ} :
    y ∈ E8Nroot L ↔ y ∈ E8posRoots.P ∧ -(wact L y) ∈ E8posRoots.P := by
  simp [E8Nroot]

/-- The `coords` of the `E8posRoots` development agree with the top-level `coords`. -/
lemma E8posRoots_coords_eq (v : Fin 8 → ℤ) : E8posRoots.coords v = coords v := rfl

/-- The `wact` of the `E8posRoots` development agrees with the top-level `wact`. -/
lemma E8posRoots_wact_eq (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    E8posRoots.wact L v = wact L v := rfl

/-! ## Basic facts about the Weyl action -/

/-- The squared length is invariant under the Weyl action. -/
lemma qZ_wact (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    E8NormTwo.qZ (wact L v) = E8NormTwo.qZ v := by
  rw [qZ_eq_bil, qZ_eq_bil, bil_wact]

/-- The Weyl action is injective. -/
lemma wact_inj (L : List (Fin 8)) : Function.Injective (wact L) := by
  intro a b hab
  have h := congrArg (wact L.reverse) hab
  rwa [wact_reverse, wact_reverse] at h

/-- The simple root `alpha i` is a positive root. -/
lemma alpha_mem_P (i : Fin 8) : alpha i ∈ E8posRoots.P := by
  rw [E8posRoots.memP]
  refine ⟨?_, ?_, ?_⟩
  · rw [qZ_eq_bil, bil_apply, E8m_diag]
  · intro h
    have h2 : alpha i i = 2 := by rw [alpha_apply, E8m_diag]
    rw [h] at h2; exact absurd h2 (by norm_num)
  · intro j
    rw [E8posRoots_coords_eq, coords_alpha, Pi.single_apply]
    split <;> norm_num

/-- The `α`-coordinates commute with negation. -/
lemma coords_neg' (a : Fin 8 → ℤ) : coords (-a) = - coords a := by
  simp only [coords, Matrix.mulVec_neg]

/-! ## The height of `ρ - wρ` -/

/-- The height is the sum of the `α`-coordinates. -/
lemma e8ht_eq_sum_coords (v : Fin 8 → ℤ) : E8NormTwo.e8ht v = ∑ i, coords v i := by
  simp only [E8NormTwo.e8ht, coords, Matrix.mulVec_apply_eq_sum]

lemma e8ht_rhoZ : E8NormTwo.e8ht rhoZ = 620 := by
  rw [e8ht_eq_sum_coords]
  simp only [coords_apply, rhoZ, mul_one]
  decide

lemma e8ht_sub (a b : Fin 8 → ℤ) :
    E8NormTwo.e8ht (a - b) = E8NormTwo.e8ht a - E8NormTwo.e8ht b := by
  simp only [e8ht_eq_sum_coords, coords, Matrix.mulVec_sub, Pi.sub_apply,
    Finset.sum_sub_distrib]

lemma e8ht_sum (s : Finset (Fin 8 → ℤ)) :
    E8NormTwo.e8ht (∑ y ∈ s, y) = ∑ y ∈ s, E8NormTwo.e8ht y := by
  simp only [e8ht_eq_sum_coords]
  have hcoords : coords (∑ y ∈ s, y) = ∑ y ∈ s, coords y := by
    simp only [coords, Matrix.mulVec_sum]
  rw [hcoords]
  simp only [Finset.sum_apply]
  exact Finset.sum_comm

/-- Height of a difference against `ρ`. -/
lemma e8ht_rhoZ_sub (v : Fin 8 → ℤ) :
    E8NormTwo.e8ht (rhoZ - v) = 620 - E8NormTwo.e8ht v := by
  rw [e8ht_sub, e8ht_rhoZ]

/-! ## Elements of `N(w)` and the trivial element -/

lemma E8wact_ne_id_of_Nroot (L : List (Fin 8)) (h : E8Nroot L ≠ ∅) :
    ∃ v : Fin 8 → ℤ, wact L v ≠ v := by
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨hyP, hyN⟩ := mem_E8Nroot.mp hy
  refine ⟨y, ?_⟩
  intro hfix
  rw [hfix] at hyN
  exact E8_neg_not_memP hyP hyN

lemma wact_rhoZ_ne_rhoZ_of_Nroot (L : List (Fin 8)) (h : E8Nroot L ≠ ∅) :
    wact L rhoZ ≠ rhoZ := by
  intro hfix
  obtain ⟨v, hv⟩ := E8wact_ne_id_of_Nroot L h
  exact hv (E8_weyl_stab_rho_trivial L hfix v)

/-- **The descent expressed with `E8Nroot`.**  If `wact L` does not fix `ρ`, then some *simple* root
is sent to a negative root. -/
lemma exists_alpha_mem_E8Nroot_of_rhoZ (L : List (Fin 8)) (h : wact L rhoZ ≠ rhoZ) :
    ∃ i : Fin 8, alpha i ∈ E8Nroot L := by
  obtain ⟨i, hi⟩ := E8_weyl_descent L h
  have hal : alpha i = fun k => CartanMatrix.E₈ i k := funext fun k => alpha_apply i k
  have hw : (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
      (fun k => CartanMatrix.E₈ i k)) = wact L (alpha i) := by
    rw [← hal]; rfl
  refine ⟨i, mem_E8Nroot.mpr ⟨alpha_mem_P i, ?_⟩⟩
  rw [E8posRoots.memP]
  refine ⟨?_, ?_, ?_⟩
  · have h2 : E8NormTwo.qZ (alpha i) = 2 := by
      rw [qZ_eq_bil, bil_apply, E8m_diag]
    rw [E8_qZ_neg, qZ_wact]; exact h2
  · intro h0
    have hz : wact L (alpha i) = 0 := by simpa using neg_eq_zero.mp h0
    have h1 : alpha i = 0 := wact_inj L (by rw [hz, wact_zero])
    have h2 : alpha i i = 2 := by rw [alpha_apply, E8m_diag]
    rw [h1] at h2; exact absurd h2 (by norm_num)
  · intro j
    have hcj : coords (wact L (alpha i)) j ≤ 0 := by
      have hh := hi j
      rw [hw] at hh
      simpa only [coords_apply] using hh
    rw [E8posRoots_coords_eq, coords_neg', Pi.neg_apply]
    simpa using hcj

lemma exists_alpha_mem_E8Nroot (L : List (Fin 8)) (h : E8Nroot L ≠ ∅) :
    ∃ i : Fin 8, alpha i ∈ E8Nroot L :=
  exists_alpha_mem_E8Nroot_of_rhoZ L (wact_rhoZ_ne_rhoZ_of_Nroot L h)

lemma E8Nroot_ne_empty_of_rhoZ (L : List (Fin 8)) (h : wact L rhoZ ≠ rhoZ) :
    E8Nroot L ≠ ∅ := by
  obtain ⟨i, hi⟩ := exists_alpha_mem_E8Nroot_of_rhoZ L h
  intro he
  rw [he] at hi
  exact absurd hi (show alpha i ∉ (∅ : Finset (Fin 8 → ℤ)) from Finset.notMem_empty _)

lemma wact_eq_id_of_Nroot_empty (L : List (Fin 8)) (h : E8Nroot L = ∅) :
    ∀ v : Fin 8 → ℤ, wact L v = v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hcon
  exact E8Nroot_ne_empty_of_rhoZ L (fun hfix => hv (E8_weyl_stab_rho_trivial L hfix v)) h

/-! ## A word of length at most `|N(w)|` -/

/-- **A word of length at most `|N(w)|`.**  If the number of positive roots sent to negative roots by
`w = wact L` is at most `n`, then `w` is represented by a word of length at most `n`.

The construction is the classical descent peeling: if `N(w) ≠ ∅` then by `E8_weyl_descent` some
simple root `αᵢ` is sent to a negative root, and `w = (w ∘ sᵢ) ∘ sᵢ`; prepending the letter `i` to a
word for `w ∘ sᵢ` (which is `i :: L`) gives a word for `w`. -/
theorem exists_word_of_Nroot_card_le : ∀ (n : ℕ) (L : List (Fin 8)),
    (E8Nroot L).card ≤ n →
    ∃ L' : List (Fin 8), L'.length ≤ n ∧ ∀ v : Fin 8 → ℤ, wact L' v = wact L v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L h
    rcases eq_or_ne (E8Nroot L).card 0 with h0 | h0
    · -- `N(w) = ∅`: `w` is the identity
      refine ⟨[], by simp, ?_⟩
      intro v
      simpa using (wact_eq_id_of_Nroot_empty L (Finset.card_eq_zero.mp h0) v).symm
    · -- descent step
      have hne : E8Nroot L ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp (Finset.card_ne_zero.mp h0)
      obtain ⟨i, hi⟩ := exists_alpha_mem_E8Nroot L hne
      have hdec : (E8Nroot (i :: L)).card + 1 = (E8Nroot L).card := E8_Nroot_cons_card L i hi
      have hle : (E8Nroot (i :: L)).card ≤ n - 1 := by omega
      have hlt : n - 1 < n := by omega
      obtain ⟨M, hMlen, hMw⟩ := ih (n - 1) hlt (i :: L) hle
      refine ⟨i :: M, by simp only [List.length_cons]; omega, ?_⟩
      intro v
      have h1 : wact (i :: M) v = wact M (sref i v) := wact_cons i M v
      have h2 : wact M (sref i v) = wact (i :: L) (sref i v) := hMw (sref i v)
      have h3 : wact (i :: L) (sref i v) = wact L (sref i (sref i v)) := wact_cons i L (sref i v)
      rw [h1, h2, h3, sref_invol]


/-! ## The bijection `N(w) → N(w⁻¹)`, `y ↦ -wy` -/

lemma E8Nroot_card_le_reverse (L : List (Fin 8)) :
    (E8Nroot L).card ≤ (E8Nroot L.reverse).card := by
  have hinj : Function.Injective (fun y : Fin 8 → ℤ => -(wact L y)) := by
    intro a b hab
    exact wact_inj L (neg_injective hab)
  have hsub : (E8Nroot L).image (fun y : Fin 8 → ℤ => -(wact L y)) ⊆ E8Nroot L.reverse := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hyP, hyN⟩ := mem_E8Nroot.mp hy
    refine mem_E8Nroot.mpr ⟨hyN, ?_⟩
    rw [E8_wact_neg, wact_reverse, neg_neg]
    exact hyP
  calc (E8Nroot L).card
      = ((E8Nroot L).image (fun y : Fin 8 → ℤ => -(wact L y))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (E8Nroot L.reverse).card := Finset.card_le_card hsub


/-! ## Bilinearity of the form -/

lemma bil_neg_left (a c : Fin 8 → ℤ) : bil (-a) c = - bil a c := by
  have h0 : bil (0 : Fin 8 → ℤ) c = 0 := by
    have h := bil_sub_left a a c
    rw [sub_self] at h
    simpa using h
  have h2 := bil_sub_left 0 a c
  rw [zero_sub] at h2
  rw [h2, h0]; ring

lemma bil_neg_right (a c : Fin 8 → ℤ) : bil a (-c) = - bil a c := by
  have h0 : bil a (0 : Fin 8 → ℤ) = 0 := by
    have h := bil_sub_right a c c
    rw [sub_self] at h
    simpa using h
  have h2 := bil_sub_right a 0 c
  rw [zero_sub] at h2
  rw [h2, h0]; ring

lemma bil_neg_neg (a c : Fin 8 → ℤ) : bil (-a) (-c) = bil a c := by
  rw [bil_neg_left, bil_neg_right]; ring

lemma bil_add_left (a b c : Fin 8 → ℤ) : bil (a + b) c = bil a c + bil b c := by
  have h := bil_sub_left a (-b) c
  rw [sub_neg_eq_add, bil_neg_left] at h
  rw [h]; ring

lemma bil_add_right (a b c : Fin 8 → ℤ) : bil a (b + c) = bil a b + bil a c := by
  have h := bil_sub_right a b (-c)
  rw [sub_neg_eq_add, bil_neg_right] at h
  rw [h]; ring

lemma qZ_neg (v : Fin 8 → ℤ) : E8NormTwo.qZ (-v) = E8NormTwo.qZ v := by
  rw [qZ_eq_bil, qZ_eq_bil, bil_neg_neg]

lemma qZ_add (a b : Fin 8 → ℤ) :
    E8NormTwo.qZ (a + b) = E8NormTwo.qZ a + bil a b + bil b a + E8NormTwo.qZ b := by
  rw [qZ_eq_bil, qZ_eq_bil, qZ_eq_bil, bil_add_left, bil_add_right, bil_add_right]
  ring

/-! ## Height-one roots are simple -/

/-- The height is additive. -/
lemma e8ht_add (a b : Fin 8 → ℤ) :
    E8NormTwo.e8ht (a + b) = E8NormTwo.e8ht a + E8NormTwo.e8ht b := by
  simp only [e8ht_eq_sum_coords, coords, Matrix.mulVec_add, Pi.add_apply,
    Finset.sum_add_distrib]

/-- The height of a simple root is one. -/
lemma e8ht_alpha (i : Fin 8) : E8NormTwo.e8ht (alpha i) = 1 := by
  rw [e8ht_eq_sum_coords, coords_alpha,
    Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => by simp at h)]
  simp

/-- A positive root has positive height. -/
lemma one_le_e8ht_of_mem_P {y : Fin 8 → ℤ} (hy : y ∈ E8posRoots.P) :
    1 ≤ E8NormTwo.e8ht y := by
  have h := (E8posRoots.memP y).mp hy
  have hnn : ∀ i, 0 ≤ coords y i := fun i => by
    simpa only [E8posRoots_coords_eq] using h.2.2 i
  have hne : (∑ i, coords y i) ≠ 0 := by
    intro h0
    have hall : ∀ i, coords y i = 0 := fun i =>
      le_antisymm (le_trans (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))
        (le_of_eq h0)) (hnn i)
    have hzero : coords y = 0 := funext hall
    have hy0 : y = 0 := by
      conv_lhs => rw [← mulVec_coords y]
      rw [hzero, Matrix.mulVec_zero]
    exact h.2.1 hy0
  have hex : ∃ i, 1 ≤ coords y i := by
    by_contra hc
    push Not at hc
    exact hne (Finset.sum_eq_zero (fun i _ => le_antisymm (by have h1 := hc i; omega) (hnn i)))
  obtain ⟨i, hi⟩ := hex
  rw [e8ht_eq_sum_coords]
  exact le_trans hi (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))

/-- A positive root of height one is a simple root. -/
lemma eq_alpha_of_e8ht_eq_one {y : Fin 8 → ℤ} (hy : y ∈ E8posRoots.P)
    (h : E8NormTwo.e8ht y = 1) : ∃ i : Fin 8, y = alpha i := by
  have hm := (E8posRoots.memP y).mp hy
  have hnn : ∀ i, 0 ≤ coords y i := fun i => by
    simpa only [E8posRoots_coords_eq] using hm.2.2 i
  have hsum : ∑ i, coords y i = 1 := by
    rw [← e8ht_eq_sum_coords, h]
  obtain ⟨k, hk⟩ := eq_single_of_sum_eq_one (coords y) hnn hsum
  refine ⟨k, ?_⟩
  conv_lhs => rw [← mulVec_coords y]
  rw [hk]
  rfl

/-- The sum of two adjacent simple roots is a positive root. -/
lemma alpha_add_mem_P {i j : Fin 8} (hij : CartanMatrix.E₈ i j = -1) :
    alpha i + alpha j ∈ E8posRoots.P := by
  have hijm : E8m i j = -1 := hij
  have hijm' : E8m j i = -1 := by rw [← E8m_symm]; exact hij
  rw [E8posRoots.memP]
  refine ⟨?_, ?_, ?_⟩
  · rw [qZ_add, qZ_eq_bil, qZ_eq_bil, bil_apply, bil_apply, bil_apply, bil_apply,
      E8m_diag, E8m_diag, hijm, hijm']
    ring
  · intro h0
    have h1 : (alpha i + alpha j) i = 2 + E8m j i := by
      simp only [Pi.add_apply, alpha_apply, E8m_diag]
    have h2 : (alpha i + alpha j) i = 0 := by rw [h0]; rfl
    rw [h2, hijm'] at h1
    omega
  · intro k
    rw [E8posRoots_coords_eq, coords_add, coords_alpha, coords_alpha, Pi.add_apply]
    have h1 : (0 : ℤ) ≤ (Pi.single i (1 : ℤ) : Fin 8 → ℤ) k := by
      by_cases h : k = i <;> simp [h]
    have h2 : (0 : ℤ) ≤ (Pi.single j (1 : ℤ) : Fin 8 → ℤ) k := by
      by_cases h : k = j <;> simp [h]
    linarith

/-- **Closure of `N(w)` under adding adjacent simple roots.** -/
lemma E8Nroot_add_mem {L : List (Fin 8)} {i j : Fin 8} (hi : alpha i ∈ E8Nroot L)
    (hj : alpha j ∈ E8Nroot L) (hij : CartanMatrix.E₈ i j = -1) :
    alpha i + alpha j ∈ E8Nroot L := by
  obtain ⟨-, hibi⟩ := mem_E8Nroot.mp hi
  obtain ⟨-, hjbj⟩ := mem_E8Nroot.mp hj
  have hijm : E8m i j = -1 := hij
  have hijm' : E8m j i = -1 := by rw [← E8m_symm]; exact hij
  have hbP : (-(wact L (alpha i)) + -(wact L (alpha j))) ∈ E8posRoots.P := by
    have hm1 := (E8posRoots.memP (-(wact L (alpha i)))).mp hibi
    have hm2 := (E8posRoots.memP (-(wact L (alpha j)))).mp hjbj
    rw [E8posRoots.memP]
    refine ⟨?_, ?_, ?_⟩
    · rw [qZ_add, qZ_neg, qZ_neg, qZ_wact, qZ_wact, qZ_eq_bil, qZ_eq_bil, bil_neg_neg,
        bil_neg_neg, bil_wact, bil_wact, bil_apply, bil_apply, bil_apply, bil_apply,
        E8m_diag, E8m_diag, hijm, hijm']
      ring
    · intro h0
      have hweq : -(wact L (alpha i)) = wact L (alpha j) := by
        rw [add_eq_zero_iff_eq_neg] at h0
        simpa using h0
      have hnotP : wact L (alpha j) ∉ E8posRoots.P := by
        have h := E8_neg_not_memP hjbj
        rwa [neg_neg] at h
      exact hnotP (hweq ▸ hibi)
    · intro k
      rw [E8posRoots_coords_eq, coords_add, Pi.add_apply]
      exact add_nonneg (hm1.2.2 k) (hm2.2.2 k)
  refine mem_E8Nroot.mpr ⟨alpha_add_mem_P hij, ?_⟩
  have hneg : -(wact L (alpha i + alpha j))
      = -(wact L (alpha i)) + -(wact L (alpha j)) := by
    rw [wact_add]; abel
  rw [hneg]
  exact hbP

/-! ## The independence number of the `E₈` diagram is at most four -/

/-- Grouping the eight nodes into the four adjacent pairs `{0,2}`, `{1,3}`, `{4,5}`, `{6,7}`. -/
def E8pairIdx (i : Fin 8) : Fin 4 :=
  if i = 0 ∨ i = 2 then 0 else if i = 1 ∨ i = 3 then 1 else if i = 4 ∨ i = 5 then 2 else 3

lemma E8_adj_of_pairIdx_eq {i j : Fin 8} (h : E8pairIdx i = E8pairIdx j) (hij : i ≠ j) :
    CartanMatrix.E₈ i j = -1 := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact absurd h (by decide)
      | decide

/-- **An independent set of the `E₈` diagram has at most four elements.** -/
lemma E8_independent_card_le_four (S : Finset (Fin 8))
    (hind : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → CartanMatrix.E₈ i j ≠ -1) : S.card ≤ 4 := by
  have hinj : Set.InjOn E8pairIdx (↑S : Set (Fin 8)) := by
    intro i hi j hj hij
    by_contra hne
    exact hind i hi j hj hne (E8_adj_of_pairIdx_eq hij hne)
  have hcard := Finset.card_image_of_injOn hinj
  calc S.card = (S.image E8pairIdx).card := hcard.symm
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by simp

/-- **`N(w)` contains a root of height at least two when it has five elements.** -/
lemma E8Nroot_exists_ht_two (L : List (Fin 8)) (h : 5 ≤ (E8Nroot L).card) :
    ∃ y ∈ E8Nroot L, 2 ≤ E8NormTwo.e8ht y := by
  classical
  by_contra hcon
  push Not at hcon
  set T := E8Nroot L with hT
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => alpha i ∈ T) with hS
  have hTsub : ∀ y ∈ T, E8NormTwo.e8ht y = 1 := by
    intro y hy
    have h1 : 1 ≤ E8NormTwo.e8ht y := one_le_e8ht_of_mem_P (mem_E8Nroot.mp (hT ▸ hy)).1
    have h2 : E8NormTwo.e8ht y < 2 := hcon y (hT ▸ hy)
    omega
  have hTsub_image : T ⊆ S.image alpha := by
    intro y hy
    obtain ⟨i, hi⟩ := eq_alpha_of_e8ht_eq_one (mem_E8Nroot.mp (hT ▸ hy)).1 (hTsub y hy)
    rw [hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by rw [← hi]; exact hy⟩, rfl⟩
  have hinj : Function.Injective (fun i : Fin 8 => alpha i) := by
    intro i j hij
    have hij' : alpha i = alpha j := hij
    by_cases h : i = j
    · exact h
    · have h1 : coords (alpha i) = coords (alpha j) := by rw [hij']
      have h5 : coords (alpha i) i = 1 := by rw [coords_alpha]; simp
      have h6 : coords (alpha j) i = 1 := by rw [← h1]; exact h5
      rw [coords_alpha, Pi.single_apply, if_neg h] at h6
      norm_num at h6
  have hcard_le : T.card ≤ S.card := by
    calc T.card ≤ (S.image alpha).card := Finset.card_le_card hTsub_image
      _ = S.card := Finset.card_image_of_injective _ hinj
  have hS5 : 5 ≤ S.card := le_trans h hcard_le
  -- `S` cannot be independent
  by_cases hdep : ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ CartanMatrix.E₈ i j = -1
  · obtain ⟨i, hiS, j, hjS, hij, hadj⟩ := hdep
    have hiT : alpha i ∈ T := (Finset.mem_filter.mp hiS).2
    have hjT : alpha j ∈ T := (Finset.mem_filter.mp hjS).2
    have hsum := E8Nroot_add_mem (hT ▸ hiT) (hT ▸ hjT) hadj
    have h2 : E8NormTwo.e8ht (alpha i + alpha j) = 2 := by
      rw [e8ht_add, e8ht_alpha, e8ht_alpha]; norm_num
    have h1 := hTsub (alpha i + alpha j) (hT ▸ hsum)
    rw [h2] at h1
    norm_num at h1
  · push Not at hdep
    have hle := E8_independent_card_le_four S hdep
    omega

/-- **The independence bound: five elements of `N(w)` force height sum at least six.** -/
lemma E8Nroot_sum_ht_ge_six (L : List (Fin 8)) (h : 5 ≤ (E8Nroot L).card) :
    6 ≤ ∑ y ∈ E8Nroot L, E8NormTwo.e8ht y := by
  classical
  obtain ⟨y₀, hy₀, h2⟩ := E8Nroot_exists_ht_two L h
  have hsplit : ∑ y ∈ E8Nroot L, E8NormTwo.e8ht y
      = E8NormTwo.e8ht y₀ + ∑ y ∈ (E8Nroot L).erase y₀, E8NormTwo.e8ht y := by
    rw [(Finset.sum_erase_add _ _ hy₀).symm]
    ring
  have hge : ((E8Nroot L).erase y₀).card ≤ ∑ y ∈ (E8Nroot L).erase y₀, E8NormTwo.e8ht y := by
    have hdecomp : ∑ y ∈ (E8Nroot L).erase y₀, E8NormTwo.e8ht y
        = (∑ y ∈ (E8Nroot L).erase y₀, (E8NormTwo.e8ht y - 1))
          + (((E8Nroot L).erase y₀).card : ℤ) := by
      rw [Finset.sum_sub_distrib]
      simp
    have hnn : 0 ≤ ∑ y ∈ (E8Nroot L).erase y₀, (E8NormTwo.e8ht y - 1) :=
      Finset.sum_nonneg (fun y hy => by
        have h1 : 1 ≤ E8NormTwo.e8ht y :=
          one_le_e8ht_of_mem_P (mem_E8Nroot.mp (Finset.mem_of_mem_erase hy)).1
        omega)
    omega
  have hcard : ((E8Nroot L).erase y₀).card = (E8Nroot L).card - 1 :=
    Finset.card_erase_of_mem hy₀
  rw [hsplit]
  omega

/-! ## At most four positive roots are sent negative by a small Weyl element -/

/-- **The sum of the heights over `N(w⁻¹)` is the height of `ρ - wρ`.** -/
lemma sum_ht_E8Nroot_reverse (L : List (Fin 8)) :
    ∑ y ∈ E8Nroot L.reverse, E8NormTwo.e8ht y
      = E8NormTwo.e8ht (rhoZ - wact L rhoZ) := by
  rw [← e8ht_sum]
  congr 1
  exact (E8_rho_sub_wact_rho_eq_sum L).symm

/-- **At most four positive roots are sent to negative roots by a small-height Weyl element.**
If `w = wact L` maps the Weyl vector to a weight of height at least `615` (so that `ρ - wρ` has
height at most `5`), then `|N(w)| ≤ 4`. -/
theorem E8Nroot_card_le_four (L : List (Fin 8))
    (h : 615 ≤ E8NormTwo.e8ht (wact L rhoZ)) : (E8Nroot L).card ≤ 4 := by
  have hht : E8NormTwo.e8ht (rhoZ - wact L rhoZ) ≤ 5 := by
    rw [e8ht_rhoZ_sub]
    omega
  have h4 : (E8Nroot L.reverse).card ≤ 4 := by
    by_contra hc
    push Not at hc
    have h6 := E8Nroot_sum_ht_ge_six L.reverse hc
    have hsum := sum_ht_E8Nroot_reverse L
    omega
  exact le_trans (E8Nroot_card_le_reverse L) h4


/-- **Length bound for small elements of the Weyl group of `E₈`.**  If the image `wact L ρ` of the
Weyl vector `ρ = ω₀ + ⋯ + ω₇` has height `e8ht ≥ 615` (equivalently, the height of `ρ - wρ` is at
most `5`), then the element has a representative word of length at most `4`; in particular it lies in
the certified ball of radius `4` of `E8_weyl_ball4`.

(The mathematical content: the height `620 - e8ht (wρ)` equals the sum of the heights of the positive
roots sent negative by `w`, which is at least the number `ℓ(w)` of such roots; if `ℓ(w) ≥ 5` then one
of those roots is not simple — the independence number of the `E₈` Dynkin diagram is `4` — so that
sum is at least `6`.) -/
theorem E8_wact_small_height_length (L : List (Fin 8))
    (hL : 615 ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht
      (Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ)) :
    ∃ L' : List (Fin 8), L'.length ≤ 4 ∧
      (∀ v : Fin 8 → ℤ, Commons.LinearAlgebra.Matrix.Cartan.wact L' v =
        Commons.LinearAlgebra.Matrix.Cartan.wact L v) :=
  exists_word_of_Nroot_card_le 4 L (E8Nroot_card_le_four L hL)

end Commons.LinearAlgebra.Matrix.Cartan
