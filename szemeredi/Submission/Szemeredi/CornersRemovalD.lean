import Mathlib
import Submission.Szemeredi.Corners

/-!
# Simplex removal in every dimension ⇒ the multidimensional corners theorem

This generalises `Submission.Szemeredi.CornersRemoval` (the `d = 3` case) to
arbitrary dimension `d`: it derives the finite corners theorem
`CornersFiniteD d ε` — equivalently Szemerédi's theorem for `(d+1)`-term
arithmetic progressions — from a quantitative *simplex removal lemma* for
`(d+1)`-partite, `d`-uniform hypergraphs.

Coordinate conventions.  A point is `p : Fin d → G`; a simplex is
`w : Fin (d+1) → G`.  The encoding of a point is
`encD p = Fin.snoc p (∑ i, p i)`, i.e. the last coordinate is the sum; the
`j`-th face of `w` is `fun k => w (j.succAbove k)` (deleting the `j`-th
coordinate).  The witness `witnessD j w : Fin d → G` is the point whose face
`j` agrees with that of `w`.
-/

open scoped BigOperators
open Finset

namespace Szemeredi

section FinLayer

variable {G : Type*} [AddCommGroup G]

/-- Encoding of a point of `G^d` as the explicit simplex `(p, Σ p)`. -/
def encD {d : ℕ} (p : Fin d → G) : Fin (d+1) → G :=
  fun i => if h : (i : ℕ) < d then p ⟨(i : ℕ), h⟩ else ∑ k, p k

/-- The `j`-th face of a simplex `w`: the `d` coordinates other than `j`. -/
def faceD {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) : Fin d → G :=
  fun k => w (Fin.succAbove j k)

/-- The witness point of the `j`-th face of `w`. -/
def witnessD {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) : Fin d → G :=
  fun k => if (k : ℕ) = (j : ℕ) then
      w (Fin.last d) - ∑ l : Fin d, (if l = k then 0 else w (Fin.castSucc l))
    else w (Fin.castSucc k)

@[simp] lemma encD_castSucc {d : ℕ} (p : Fin d → G) (k : Fin d) :
    encD p (Fin.castSucc k) = p k := by
  simp only [encD, Fin.val_castSucc, dif_pos k.isLt]

lemma encD_last {d : ℕ} (p : Fin d → G) : encD p (Fin.last d) = ∑ k, p k := by
  simp only [encD, Fin.val_last, dif_neg (lt_irrefl d)]

lemma faceD_encD_apply {d : ℕ} (j : Fin (d+1)) (p : Fin d → G) (k : Fin d) :
    faceD j (encD p) k = encD p (Fin.succAbove j k) := rfl

lemma encD_succ {d : ℕ} (p : Fin d → G) (k : Fin d) :
    encD p k.succ = if h : (k : ℕ) + 1 < d then p ⟨(k : ℕ) + 1, h⟩ else ∑ l, p l := by
  simp only [encD, Fin.val_succ]

lemma encD_succAbove_of_lt {d : ℕ} (j : Fin (d+1)) (p : Fin d → G) (k : Fin d)
    (h : Fin.castSucc k < j) : encD p (Fin.succAbove j k) = p k := by
  rw [Fin.succAbove_of_castSucc_lt j k h, encD_castSucc]

lemma encD_succAbove_of_le {d : ℕ} (j : Fin (d+1)) (p : Fin d → G) (k : Fin d)
    (h : j ≤ Fin.castSucc k) : encD p (Fin.succAbove j k) = encD p k.succ := by
  rw [Fin.succAbove_of_le_castSucc j k h]

lemma witnessD_eq_of_ne {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) (k : Fin d)
    (h : (k : ℕ) ≠ (j : ℕ)) : witnessD j w k = w (Fin.castSucc k) := by
  simp only [witnessD]
  exact dif_neg h

lemma witnessD_self {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) (k : Fin d)
    (h : (k : ℕ) = (j : ℕ)) :
    witnessD j w k = w (Fin.last d) - ∑ l : Fin d, (if l = k then 0 else w (Fin.castSucc l)) := by
  simp only [witnessD]
  exact dif_pos h

lemma sum_witnessD {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) (h : (j : ℕ) < d) :
    ∑ l : Fin d, witnessD j w l = w (Fin.last d) := by
  classical
  set k0 : Fin d := ⟨(j : ℕ), h⟩ with hk0
  have hmem : k0 ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k0
  have hrest : ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k0, witnessD j w l
      = ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k0, w (Fin.castSucc l) := by
    refine Finset.sum_congr rfl ?_
    intro l hl
    rw [Finset.mem_erase] at hl
    refine witnessD_eq_of_ne j w l ?_
    intro hc
    exact hl.1 (Fin.ext (by show (l : ℕ) = (k0 : ℕ); rw [hk0]; exact hc))
  have hk0self : witnessD j w k0
      = w (Fin.last d) - ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k0, w (Fin.castSucc l) := by
    rw [witnessD_self j w k0 (by rw [hk0])]
    congr 1
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := k0) _ hmem]
    have : (if k0 = k0 then (0 : G) else w (Fin.castSucc k0)) = 0 := if_pos rfl
    rw [this, add_zero]
    refine Finset.sum_congr rfl ?_
    intro l hl
    rw [Finset.mem_erase] at hl
    exact if_neg hl.1
  rw [← Finset.sum_erase_add (s := Finset.univ) (a := k0) _ hmem, hrest, hk0self]
  abel

lemma faceD_encD_witnessD {d : ℕ} (j : Fin (d+1)) (w : Fin (d+1) → G) :
    faceD j (encD (witnessD j w)) = faceD j w := by
  classical
  funext k
  show encD (witnessD j w) (Fin.succAbove j k) = w (Fin.succAbove j k)
  rcases lt_or_ge (Fin.castSucc k) j with hlt | hge
  · rw [Fin.succAbove_of_castSucc_lt j k hlt, encD_castSucc]
    refine witnessD_eq_of_ne j w k ?_
    intro hc
    exact absurd hc (ne_of_lt hlt)
  · rw [Fin.succAbove_of_le_castSucc j k hge]
    rw [encD_succ]
    by_cases hd : (k : ℕ) + 1 < d
    · rw [dif_pos hd]
      refine (witnessD_eq_of_ne j w ⟨(k : ℕ) + 1, hd⟩ ?_).trans ?_
      · intro hc; have hge' : (j : ℕ) ≤ (k : ℕ) := hge; simp only [Fin.val_mk] at hc; omega
      · rfl
    · rw [dif_neg hd]
      have hjk : (j : ℕ) < d := lt_of_le_of_lt (show (j : ℕ) ≤ (k : ℕ) from hge) k.isLt
      rw [sum_witnessD j w hjk]
      have hsucc : k.succ = Fin.last d := by
        ext; simp only [Fin.val_succ, Fin.val_last]; omega
      rw [hsucc]

lemma succAbove_last_eq {d : ℕ} (j : Fin (d+1)) (h : (j : ℕ) < d) :
    Fin.succAbove j (⟨d - 1, by omega⟩ : Fin d) = Fin.last d := by
  have hge : j ≤ Fin.castSucc (⟨d - 1, by omega⟩ : Fin d) := by
    show (j : ℕ) ≤ ((d - 1 : ℕ)); omega
  rw [Fin.succAbove_of_le_castSucc j _ hge]
  ext; simp only [Fin.val_succ, Fin.val_mk, Fin.val_last]; omega

lemma faceD_encD_injective {d : ℕ} (j : Fin (d+1)) :
    Function.Injective (fun p : Fin d → G => faceD j (encD p)) := by
  classical
  intro p q hp
  have h := fun k => congrFun hp k
  have hother : ∀ l : Fin d, (l : ℕ) ≠ (j : ℕ) → p l = q l := by
    intro l hlj
    have key : encD p (Fin.castSucc l) = encD q (Fin.castSucc l) := by
      rcases lt_or_gt_of_ne hlj with hc | hc
      · have h1 := h l
        change encD p (Fin.succAbove j l) = encD q (Fin.succAbove j l) at h1
        rwa [Fin.succAbove_of_castSucc_lt j l hc] at h1
      · have hlt : (l : ℕ) - 1 < d := by have := l.isLt; omega
        have h1 := h (⟨(l : ℕ) - 1, hlt⟩ : Fin d)
        change encD p (Fin.succAbove j ⟨(l : ℕ) - 1, hlt⟩)
          = encD q (Fin.succAbove j ⟨(l : ℕ) - 1, hlt⟩) at h1
        have hs : Fin.succAbove j ⟨(l : ℕ) - 1, hlt⟩ = Fin.castSucc l := by
          rw [Fin.succAbove_of_le_castSucc j _ (by
            show (j : ℕ) ≤ (l : ℕ) - 1
            exact Nat.le_sub_one_of_lt hc)]
          ext; simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc]; omega
        rwa [hs] at h1
    rwa [encD_castSucc, encD_castSucc] at key
  by_cases hj : (j : ℕ) < d
  · have hsum : ∑ l : Fin d, p l = ∑ l : Fin d, q l := by
      have h1 := h (⟨d - 1, by omega⟩ : Fin d)
      change encD p (Fin.succAbove j ⟨d - 1, by omega⟩)
        = encD q (Fin.succAbove j ⟨d - 1, by omega⟩) at h1
      rw [succAbove_last_eq j hj, encD_last, encD_last] at h1
      exact h1
    set k0 : Fin d := ⟨(j : ℕ), hj⟩ with hk0
    have hmem : k0 ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k0
    have hcongr : ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k0, p l
        = ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k0, q l := by
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [Finset.mem_erase] at hl
      exact hother l (fun hc => hl.1 (Fin.ext (by show (l : ℕ) = (k0 : ℕ); rw [hk0]; exact hc)))
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := k0) _ hmem,
        ← Finset.sum_erase_add (s := Finset.univ) (a := k0) _ hmem] at hsum
    rw [hcongr] at hsum
    funext l
    by_cases hl : l = k0
    · subst hl
      exact add_left_cancel hsum
    · exact hother l (fun hc => hl (Fin.ext (by show (l : ℕ) = (k0 : ℕ); rw [hk0]; exact hc)))
  · have hjl : (j : ℕ) = d := by have := j.isLt; omega
    have hjlast : j = Fin.last d := Fin.ext (by simp [hjl])
    funext l
    have h1 := h l
    change encD p (Fin.succAbove j l) = encD q (Fin.succAbove j l) at h1
    have hs : Fin.succAbove j l = Fin.castSucc l := by rw [hjlast, Fin.succAbove_last_apply]
    rw [hs, encD_castSucc, encD_castSucc] at h1
    exact h1

lemma faceD_encD_eq_iff {d : ℕ} (j : Fin (d+1)) (p : Fin d → G) (w : Fin (d+1) → G) :
    faceD j (encD p) = faceD j w ↔ p = witnessD j w := by
  constructor
  · intro h
    have h2 : faceD j (encD p) = faceD j (encD (witnessD j w)) := by
      rw [h, faceD_encD_witnessD]
    exact faceD_encD_injective j h2
  · intro h
    rw [h, faceD_encD_witnessD]

lemma witnessD_last {d : ℕ} (w : Fin (d+1) → G) :
    witnessD (Fin.last d) w = fun k => w (Fin.castSucc k) := by
  funext k
  refine witnessD_eq_of_ne _ _ k ?_
  simp only [Fin.val_last]; exact (k.isLt).ne

lemma witnessD_castSucc {d : ℕ} (w : Fin (d+1) → G) (k : Fin d) :
    witnessD (Fin.castSucc k) w =
      fun l => w (Fin.castSucc l)
        + (if l = k then w (Fin.last d) - ∑ k' : Fin d, w (Fin.castSucc k') else (0 : G)) := by
  classical
  funext l
  by_cases hlk : l = k
  · subst hlk
    rw [witnessD_self _ _ l (by simp), if_pos rfl]
    have h2 : ∑ l' : Fin d, (if l' = l then (0 : G) else w (Fin.castSucc l'))
        = ∑ l' ∈ (Finset.univ : Finset (Fin d)).erase l, w (Fin.castSucc l') := by
      rw [← Finset.sum_erase_add (s := Finset.univ) (a := l) _ (Finset.mem_univ l)]
      have h1 : (if l = l then (0 : G) else w (Fin.castSucc l)) = 0 := if_pos rfl
      rw [h1, add_zero]
      refine Finset.sum_congr rfl ?_
      intro l' hl'
      rw [Finset.mem_erase] at hl'
      exact if_neg hl'.1
    have hS : (∑ l' ∈ (Finset.univ : Finset (Fin d)).erase l, w (Fin.castSucc l'))
        = ∑ l' : Fin d, w (Fin.castSucc l') - w (Fin.castSucc l) := by
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_erase_add (s := Finset.univ) (a := l) _ (Finset.mem_univ l)
    rw [h2, hS]
    abel
  · rw [witnessD_eq_of_ne _ _ l (by intro hc; exact hlk (Fin.ext hc)), if_neg hlk]
    abel

theorem corner_of_all_witnesses {d : ℕ} {B : Finset (Fin d → G)} {w : Fin (d+1) → G}
    (hw : ∀ j : Fin (d+1), witnessD j w ∈ B) :
    w = encD (witnessD (Fin.last d) w)
      ∨ ∃ x t, IsCornerD (B : Set (Fin d → G)) x t := by
  classical
  set t : G := w (Fin.last d) - ∑ k : Fin d, w (Fin.castSucc k) with ht
  by_cases h0 : t = 0
  · left
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, hk⟩ | hlast
    · subst hk
      rw [encD_castSucc]
      exact (congrFun (witnessD_last w) k).symm
    · subst hlast
      rw [encD_last]
      have htr : w (Fin.last d) - ∑ k : Fin d, w (Fin.castSucc k) = 0 := by rw [← ht, h0]
      rw [sub_eq_zero.mp htr]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact (congrFun (witnessD_last w) k).symm
  · right
    refine ⟨fun k => w (Fin.castSucc k), t, h0, ?_, ?_⟩
    · have := hw (Fin.last d)
      rwa [witnessD_last] at this
    · intro k
      have hwit := hw (Fin.castSucc k)
      rw [witnessD_castSucc] at hwit
      have hfun : (fun j : Fin d => w (Fin.castSucc j) + (if j = k then t else (0 : G)))
          = (fun l : Fin d => w (Fin.castSucc l)
              + (if l = k then w (Fin.last d) - ∑ k' : Fin d, w (Fin.castSucc k') else 0)) := by
        funext l
        by_cases hlk : l = k
        · subst hlk; rfl
        · rfl
      rwa [hfun]

end FinLayer

section Hypergraph

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- A simplex of a `(d+1)`-partite `d`-uniform hypergraph `E`: a tuple `w` all of whose
`(d+1)` faces are edges. -/
def IsSimplexD {d : ℕ} (E : Fin (d+1) → Finset (Fin d → G)) (w : Fin (d+1) → G) : Prop :=
  ∀ j : Fin (d+1), faceD j w ∈ E j

/-- The finset of all simplexes of `E`. -/
noncomputable def simplexFinsetD {d : ℕ} (E : Fin (d+1) → Finset (Fin d → G)) :
    Finset (Fin (d+1) → G) := by
  classical
  exact Finset.univ.filter (IsSimplexD E)

/-- `E` is simplex-free. -/
def SimplexFreeD {d : ℕ} (E : Fin (d+1) → Finset (Fin d → G)) : Prop :=
  ∀ w : Fin (d+1) → G, ¬ IsSimplexD E w

/-- The encoded hypergraph of `B ⊆ G^d`. -/
def encED {d : ℕ} (B : Finset (Fin d → G)) : Fin (d+1) → Finset (Fin d → G) :=
  fun j => B.image (fun p => faceD j (encD p))

/-- `E` is far from simplex-free at level `ε`. -/
def FarFromSimplexFreeD {d : ℕ} (E : Fin (d+1) → Finset (Fin d → G)) (ε : ℝ) : Prop :=
  ¬ ∃ E' : Fin (d+1) → Finset (Fin d → G),
    (∀ j : Fin (d+1), E' j ⊆ E j) ∧ SimplexFreeD E' ∧
      (∑ j : Fin (d+1), (((E j).card : ℝ) - ((E' j).card : ℝ))) <
        ε * (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d

lemma witnessD_encD {d : ℕ} (j : Fin (d+1)) (p : Fin d → G) :
    witnessD j (encD p) = p := by
  classical
  funext k
  by_cases hk : (k : ℕ) = (j : ℕ)
  · rw [witnessD_self _ _ k hk]
    have h2 : ∑ l : Fin d, (if l = k then (0 : G) else encD p (Fin.castSucc l))
        = ∑ l ∈ (Finset.univ : Finset (Fin d)).erase k, p l := by
      rw [← Finset.sum_erase_add (s := Finset.univ) (a := k) _ (Finset.mem_univ k)]
      have h1 : (if k = k then (0 : G) else encD p (Fin.castSucc k)) = 0 := if_pos rfl
      rw [h1, add_zero]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [Finset.mem_erase] at hl
      rw [if_neg hl.1, encD_castSucc]
    have hS : (∑ l ∈ (Finset.univ : Finset (Fin d)).erase k, p l)
        = ∑ l : Fin d, p l - p k := by
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_erase_add (s := Finset.univ) (a := k) _ (Finset.mem_univ k)
    rw [encD_last, h2, hS]
    abel
  · rw [witnessD_eq_of_ne _ _ k hk, encD_castSucc]

lemma face_mem_encED_iff_witness {d : ℕ} (B : Finset (Fin d → G)) (j : Fin (d+1))
    (w : Fin (d+1) → G) : faceD j w ∈ encED B j ↔ witnessD j w ∈ B := by
  classical
  simp only [encED]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpf⟩
    have h1 : p = witnessD j w := (faceD_encD_eq_iff j p w).mp hpf
    rwa [← h1]
  · intro hw
    exact ⟨witnessD j w, hw, (faceD_encD_eq_iff j (witnessD j w) w).mpr rfl⟩

lemma simplex_encED_iff_witness {d : ℕ} (B : Finset (Fin d → G)) (w : Fin (d+1) → G) :
    IsSimplexD (encED B) w ↔ ∀ j : Fin (d+1), witnessD j w ∈ B := by
  classical
  simp [IsSimplexD, face_mem_encED_iff_witness]

lemma explicit_isSimplexD {d : ℕ} (B : Finset (Fin d → G)) (p : Fin d → G) (hp : p ∈ B) :
    IsSimplexD (encED B) (encD p) := by
  classical
  rw [simplex_encED_iff_witness]
  intro j
  rwa [witnessD_encD]

lemma noAccidentalSimplexD {d : ℕ} {B : Finset (Fin d → G)}
    (hB : IsCornerFreeD (B : Set (Fin d → G))) {w : Fin (d+1) → G}
    (hw : ∀ j : Fin (d+1), witnessD j w ∈ B) :
    w = encD (witnessD (Fin.last d) w) ∧ witnessD (Fin.last d) w ∈ B := by
  rcases corner_of_all_witnesses (B := B) hw with henc | ⟨x, t, hcor⟩
  · exact ⟨henc, hw (Fin.last d)⟩
  · exact False.elim (hB ⟨x, t, hcor⟩)

lemma faceD_encD_injOn {d : ℕ} (B : Finset (Fin d → G)) (j : Fin (d+1)) :
    Set.InjOn (fun p : Fin d → G => faceD j (encD p)) (B : Set (Fin d → G)) :=
  fun p _ q _ hpq => faceD_encD_injective j hpq

lemma cornerFree_simplexFinsetD_eq_image {d : ℕ} (B : Finset (Fin d → G))
    (hB : IsCornerFreeD (B : Set (Fin d → G))) :
    simplexFinsetD (encED B) = B.image encD := by
  classical
  apply Finset.Subset.antisymm
  · intro w hw
    have hw' : ∀ j : Fin (d+1), witnessD j w ∈ B :=
      (simplex_encED_iff_witness B w).mp (Finset.mem_filter.mp hw).2
    obtain ⟨hwenc, hwl⟩ := noAccidentalSimplexD hB hw'
    rw [hwenc]
    exact Finset.mem_image.mpr ⟨witnessD (Fin.last d) w, hwl, rfl⟩
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, explicit_isSimplexD B p hp⟩

lemma cornerFree_card_simplexD {d : ℕ} (B : Finset (Fin d → G))
    (hB : IsCornerFreeD (B : Set (Fin d → G))) :
    (simplexFinsetD (encED B)).card = B.card := by
  classical
  rw [cornerFree_simplexFinsetD_eq_image B hB]
  refine Finset.card_image_of_injOn ?_
  intro p _ q _ hpq
  funext k
  have := congrFun hpq (Fin.castSucc k)
  simpa only [encD_castSucc] using this

lemma farFromSimplexFree_of_dense_D {d : ℕ} (B : Finset (Fin d → G)) {ε : ℝ} (hε : 0 < ε)
    (hBd : ε * ((Fintype.card G : ℕ) : ℝ) ^ d ≤ (B.card : ℝ)) :
    FarFromSimplexFreeD (encED B) (ε / (((d + 1) ^ d : ℕ) : ℝ)) := by
  classical
  rw [FarFromSimplexFreeD]
  rintro ⟨E', hsub, hfree, hdel⟩
  let D : Fin (d+1) → Finset (Fin d → G) := fun j => (encED B) j \ E' j
  have hDcard : ∀ j : Fin (d+1), (D j).card = ((encED B) j).card - (E' j).card := by
    intro j
    dsimp [D]
    rw [Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr (hsub j)]
  have hkill : ∀ p : Fin d → G, p ∈ B → ∃ j : Fin (d+1), faceD j (encD p) ∈ D j := by
    intro p hp
    have hnot : ¬ IsSimplexD E' (encD p) := hfree (encD p)
    rw [IsSimplexD] at hnot
    push_neg at hnot
    rcases hnot with ⟨j, hj⟩
    exact ⟨j, Finset.mem_sdiff.mpr ⟨explicit_isSimplexD B p hp j, hj⟩⟩
  let P : Finset (Σ j : Fin (d+1), Fin d → G) := (Finset.univ : Finset (Fin (d+1))).sigma D
  let β : {r : Fin d → G // r ∈ B} → Σ j : Fin (d+1), Fin d → G := fun r =>
    ⟨Classical.choose (hkill r.1 r.2), faceD (Classical.choose (hkill r.1 r.2)) (encD r.1)⟩
  have hβinj : Function.Injective β := by
    intro r s hpq
    have hjel : (Classical.choose (hkill r.1 r.2) : Fin (d+1)) =
        Classical.choose (hkill s.1 s.2) :=
      congrArg (fun z : Σ j : Fin (d+1), Fin d → G => z.1) hpq
    have hface : faceD (Classical.choose (hkill r.1 r.2)) (encD r.1) =
        faceD (Classical.choose (hkill s.1 s.2)) (encD s.1) :=
      congrArg (fun z : Σ j : Fin (d+1), Fin d → G => z.2) hpq
    have hface' : faceD (Classical.choose (hkill r.1 r.2)) (encD r.1) =
        faceD (Classical.choose (hkill r.1 r.2)) (encD s.1) := by simpa [hjel] using hface
    refine Subtype.ext ?_
    exact faceD_encD_injective _ hface'
  have hβim : B.attach.image β ⊆ P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    dsimp [P]
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ _, Classical.choose_spec (hkill r.1 r.2)⟩
  have hBle : (B.card : ℝ) ≤ (∑ j : Fin (d+1), ((D j).card : ℝ)) := by
    have hcardP : P.card = ∑ j : Fin (d+1), (D j).card := by
      dsimp [P]
      simpa using (Finset.card_sigma (Finset.univ : Finset (Fin (d+1))) D)
    have h1 : B.card ≤ P.card := by
      calc B.card = B.attach.card := (Finset.card_attach (s := B)).symm
        _ = (B.attach.image β).card := by
            exact (Finset.card_image_of_injOn (s := B.attach) (f := β) (by
              intro x _ y _ hxy; exact hβinj hxy)).symm
        _ ≤ P.card := Finset.card_le_card hβim
    rw [hcardP] at h1
    exact_mod_cast h1
  have hsumD : (∑ j : Fin (d+1), ((D j).card : ℝ)) =
      (∑ k : Fin (d+1), ((((encED B) k).card : ℝ) - ((E' k).card : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hDcard k, Nat.cast_sub (Finset.card_le_card (hsub k))]
  have hdelR : (∑ j : Fin (d+1), ((((encED B) j).card : ℝ) - ((E' j).card : ℝ))) <
      (ε / (((d + 1) ^ d : ℕ) : ℝ)) * (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d := by
    simpa using hdel
  have hbig : (ε / (((d + 1) ^ d : ℕ) : ℝ)) * (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d
      ≤ (B.card : ℝ) := by
    have hcast : (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d
        = (((d + 1) ^ d : ℕ) : ℝ) * ((Fintype.card G : ℕ) : ℝ) ^ d := by
      rw [Nat.cast_mul, Nat.cast_pow, mul_pow]
    rw [hcast]
    have hpos : (0 : ℝ) < (((d + 1) ^ d : ℕ) : ℝ) := by
      have : 0 < (d + 1) ^ d := pow_pos (by omega) d
      exact_mod_cast this
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [hBd]
  nlinarith [hBle, hsumD, hdelR, hbig]

end Hypergraph

/-- A quantitative **simplex removal lemma** in dimension `d` (for `(d+1)`-partite,
`d`-uniform hypergraphs with all parts of size `M`): if the hypergraph is far from
simplex-free at level `ε` then it has `≥ c(ε) · ((d+1)M)^{d+1}` simplexes. -/
def SimplexRemovalProgrammeD (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℕ,
    ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G],
      M₀ ≤ Fintype.card G →
      ∀ E : Fin (d+1) → Finset (Fin d → G),
        FarFromSimplexFreeD E ε →
          c * ((((d+1) * Fintype.card G : ℕ)) : ℝ) ^ (d+1) ≤ ((simplexFinsetD E).card : ℝ)

theorem cornersFinite_generic_d {d : ℕ} (hrem : SimplexRemovalProgrammeD d) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G],
      N₀ ≤ Fintype.card G → ∀ B : Finset (Fin d → G),
        ε * ((Fintype.card G : ℕ) : ℝ) ^ d ≤ (B.card : ℝ) →
          ¬ IsCornerFreeD (B : Set (Fin d → G)) := by
  have hden : (0 : ℝ) < (((d+1) ^ d : ℕ) : ℝ) := by
    have : (0 : ℕ) < (d + 1) ^ d := pow_pos (by omega) d
    exact_mod_cast this
  rcases hrem (ε / (((d+1) ^ d : ℕ) : ℝ)) (by positivity) with ⟨c, hc, M₀, hM₀⟩
  let x : ℝ := 1 / ((((d+1) ^ (d+1) : ℕ) : ℝ) * c)
  refine ⟨max M₀ (Nat.ceil x + 1), ?_⟩
  intro G _ _ _ hN B hBd hBf
  let M : ℕ := Fintype.card G
  have hM₀le : M₀ ≤ M := le_trans (le_max_left _ _) hN
  have hNbig : Nat.ceil x + 1 ≤ M := le_trans (le_max_right _ _) hN
  have hMge1 : 1 ≤ M := by omega
  have hxceil : x < (Nat.ceil x : ℝ) + 1 := by
    have hle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    linarith
  have hNb : (Nat.ceil x : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hNbig
  have hApos : (0 : ℝ) < (((d+1) ^ (d+1) : ℕ) : ℝ) := by
    have : (0 : ℕ) < (d + 1) ^ (d+1) := pow_pos (by omega) (d+1)
    exact_mod_cast this
  have hMbig : (1 : ℝ) < (((d+1) ^ (d+1) : ℕ) : ℝ) * c * (M : ℝ) := by
    have hcpos : 0 < (((d+1) ^ (d+1) : ℕ) : ℝ) * c := by positivity
    have hx : x < (M : ℝ) := by linarith
    have h0 : 1 / ((((d+1) ^ (d+1) : ℕ) : ℝ) * c) < (M : ℝ) := by simpa [x] using hx
    have h1 := (div_lt_iff₀ hcpos).mp h0
    linarith [h1]
  have hremG : ∀ E : Fin (d+1) → Finset (Fin d → G),
      FarFromSimplexFreeD E (ε / (((d+1) ^ d : ℕ) : ℝ)) →
      c * ((((d+1) * M : ℕ)) : ℝ) ^ (d+1) ≤ ((simplexFinsetD E).card : ℝ) := by
    intro E hE
    have h0 := hM₀ (G := G) hM₀le E hE
    simpa [M] using h0
  have hfar : FarFromSimplexFreeD (encED B) (ε / (((d+1) ^ d : ℕ) : ℝ)) :=
    farFromSimplexFree_of_dense_D B hε hBd
  have hcnt : (simplexFinsetD (encED B)).card = B.card := cornerFree_card_simplexD B hBf
  have hrem2 : c * ((((d+1) * M : ℕ)) : ℝ) ^ (d+1) ≤ (B.card : ℝ) := by
    have h0 := hremG (encED B) hfar
    simpa [hcnt] using h0
  have hle : (B.card : ℝ) ≤ (M : ℝ) ^ d := by
    have h0 : B.card ≤ Fintype.card (Fin d → G) := Finset.card_le_univ B
    have h1 : (Fintype.card (Fin d → G) : ℝ) = (M : ℝ) ^ d := by simp [M]
    calc (B.card : ℝ) ≤ (Fintype.card (Fin d → G) : ℝ) := by exact_mod_cast h0
      _ = (M : ℝ) ^ d := h1
  have h4 : ((((d+1) * M : ℕ)) : ℝ) ^ (d+1)
      = (((d+1) ^ (d+1) : ℕ) : ℝ) * (M : ℝ) ^ (d+1) := by
    rw [Nat.cast_mul, Nat.cast_pow, mul_pow]
  have hMpow : (M : ℝ) ^ (d+1) = (M : ℝ) ^ d * (M : ℝ) := pow_succ _ _
  have hrem2' : ((((d+1) ^ (d+1) : ℕ) : ℝ) * c * (M : ℝ)) * (M : ℝ) ^ d ≤ (M : ℝ) ^ d := by
    rw [h4, hMpow] at hrem2
    nlinarith [hrem2, hle]
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hMge1)
  have hMdpos : 0 < (M : ℝ) ^ d := pow_pos hMpos d
  nlinarith [hrem2', hMbig, hMdpos]

/-- **The multidimensional corners theorem from simplex removal.** -/
theorem cornersFiniteD_d {d : ℕ} (hrem : SimplexRemovalProgrammeD d) :
    ∀ ε : ℝ, 0 < ε → CornersFiniteD d ε := by
  intro ε hε
  rcases cornersFinite_generic_d hrem ε hε with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro M hM1 hN B hB
  haveI : NeZero M := ⟨by omega⟩
  by_contra hnc
  refine hN₀ (G := ZMod M) ?_ B ?_ hnc
  · simpa using hN
  · simpa using hB


end Szemeredi
