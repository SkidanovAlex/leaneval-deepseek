import Mathlib

/-!
# Counting `Fin (r+r) → Fin H` functions with no singleton fibre

A function `w : Fin (r+r) → Fin H` has *no singleton value* when for every index
`i` there is another index `j ≠ i` with `w j = w i`; equivalently every nonempty
fibre of `w` has at least two elements.  The goal is the crude but useful bound

  `#{w | w has no singleton value} ≤ (2r)^(2r) * H^r`.

Since every fibre has size `≥ 2` and the `2r` indices fall into the fibres, there
are at most `r` (nonempty) fibres, i.e. `|image w| ≤ r`.  We encode such a `w` by
the pair `(g, h)` where `g i` is the rank of `w i` among the (sorted) values in
the image of `w`, and `h t` is the `t`-th smallest value of the image; then
`w = h ∘ g`.  There are `r^(2r)` choices for `g` and `H^r` for `h`, and
`r^(2r) ≤ (2r)^(2r)`, giving the claim.
-/

namespace Work.LinnikAreas

namespace NoSingletonAux

open Finset

/-- Rank of `v` among the members of `S` smaller than `v`; for `v ∈ S` this is the
position of `v` in the increasing enumeration of `S`. -/
noncomputable def rankOf {H : ℕ} (S : Finset (Fin H)) (v : Fin H) : ℕ :=
  (S.filter (fun u => u < v)).card

lemma rankOf_lt_card {H : ℕ} (S : Finset (Fin H)) {v : Fin H} (hv : v ∈ S) :
    rankOf S v < S.card := by
  unfold rankOf
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨v, hv, lt_irrefl v⟩)

lemma rankOf_lt_of_lt {H : ℕ} (S : Finset (Fin H)) {v v' : Fin H} (hv : v ∈ S) (h : v < v') :
    rankOf S v < rankOf S v' := by
  unfold rankOf
  apply Finset.card_lt_card
  have hsub : S.filter (fun u => u < v) ⊆ S.filter (fun u => u < v') := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨v, ?_, ?_⟩
  · rw [Finset.mem_filter]; exact ⟨hv, h⟩
  · rw [Finset.mem_filter]; exact fun hc => lt_irrefl v hc.2

/-- The rank is strictly increasing on a finite set of `Fin H`, hence injective. -/
lemma rankOf_injOn {H : ℕ} (S : Finset (Fin H)) {v v' : Fin H} (hv : v ∈ S) (hv' : v' ∈ S)
    (h : rankOf S v = rankOf S v') : v = v' := by
  rcases lt_trichotomy v v' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (rankOf_lt_of_lt S hv hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (rankOf_lt_of_lt S hv' hgt))

/-- The first component of the encoding: the rank of each value in `image w`. -/
noncomputable def encG {n H r : ℕ} (w : Fin n → Fin H)
    (hbound : (Finset.univ.image w).card ≤ r) : Fin n → Fin r :=
  fun i => ⟨rankOf (Finset.univ.image w) (w i), by
    have hmem : w i ∈ Finset.univ.image w := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have := rankOf_lt_card (Finset.univ.image w) hmem
    omega⟩

/-- The second component of the encoding: the value of rank `t` in `image w`, with an
arbitrary default `d` for the (at most `r - |image w|`) unused ranks. -/
noncomputable def encH {n H r : ℕ} (d : Fin H) (w : Fin n → Fin H) : Fin r → Fin H :=
  fun t => if ht : ∃ v ∈ Finset.univ.image w, rankOf (Finset.univ.image w) v = (t : ℕ)
           then Classical.choose ht else d

/-- Decoding property: `w = h ∘ g`. -/
lemma encG_encH {n H r : ℕ} (d : Fin H) (w : Fin n → Fin H)
    (hbound : (Finset.univ.image w).card ≤ r) (i : Fin n) :
    encH d w (encG w hbound i) = w i := by
  have hcoe : ((encG w hbound i : Fin r) : ℕ) = rankOf (Finset.univ.image w) (w i) := by
    simp [encG]
  have hex : ∃ v ∈ Finset.univ.image w,
      rankOf (Finset.univ.image w) v = ((encG w hbound i : Fin r) : ℕ) :=
    ⟨w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hcoe.symm⟩
  have hchoose : Classical.choose hex = w i :=
    rankOf_injOn (Finset.univ.image w)
      (Classical.choose_spec hex).1
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      ((Classical.choose_spec hex).2.trans hcoe)
  simp only [encH]
  rw [dif_pos hex]
  exact hchoose

/-- If every index has a distinct partner with the same value, then the image has at
most `n/2` elements. -/
lemma two_mul_card_image_le {n H : ℕ} (w : Fin n → Fin H)
    (hw : ∀ i, ∃ j, j ≠ i ∧ w j = w i) :
    2 * (Finset.univ.image w).card ≤ n := by
  set t := Finset.univ.image w with ht
  have hmap : Set.MapsTo w (↑(Finset.univ : Finset (Fin n))) (↑t) := by
    intro x _
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hpart := Finset.card_eq_sum_card_fiberwise hmap
  have h2 : ∀ b ∈ t, 2 ≤ (Finset.univ.filter (fun i => w i = b)).card := by
    intro b hb
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hji, hwij⟩ := hw i
    have hi_mem : i ∈ Finset.univ.filter (fun x => w x = b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
    have hj_mem : j ∈ Finset.univ.filter (fun x => w x = b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hwij, hi]
    have hlt : 1 < (Finset.univ.filter (fun x => w x = b)).card :=
      Finset.one_lt_card.mpr ⟨i, hi_mem, j, hj_mem, Ne.symm hji⟩
    omega
  have hsum : ∑ b ∈ t, (Finset.univ.filter (fun i => w i = b)).card = n := by
    rw [← hpart]; simp
  have hle := Finset.card_nsmul_le_sum t
    (fun b => (Finset.univ.filter (fun i => w i = b)).card) 2 h2
  have hle' : t.card * 2 ≤ n := by simpa only [hsum, nsmul_eq_mul, Nat.cast_id] using hle
  omega

/-- The main counting bound, for functions `Fin (r+r) → Fin H` all of whose fibres have
size `≥ 2`. -/
lemma card_p_le (r H : ℕ) (hH : 1 ≤ H) :
    (Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
        ∀ i, ∃ j, j ≠ i ∧ w j = w i)).card ≤ (r + r) ^ (r + r) * H ^ r := by
  classical
  rw [← Fintype.card_subtype (p := fun w : Fin (r + r) → Fin H =>
        ∀ i, ∃ j, j ≠ i ∧ w j = w i)]
  let d : Fin H := ⟨0, by omega⟩
  let hcard : ∀ u : {w : Fin (r + r) → Fin H // (∀ i, ∃ j, j ≠ i ∧ w j = w i)},
      (Finset.univ.image u.1).card ≤ r :=
    fun u => by have := two_mul_card_image_le u.1 u.2; omega
  let mapFn : {w : Fin (r + r) → Fin H // (∀ i, ∃ j, j ≠ i ∧ w j = w i)} →
      (Fin (r + r) → Fin r) × (Fin r → Fin H) :=
    fun u => (encG u.1 (hcard u), encH d u.1)
  have hkey : ∀ (u : {w : Fin (r + r) → Fin H // (∀ i, ∃ j, j ≠ i ∧ w j = w i)})
      (i : Fin (r + r)),
      encH d u.1 (encG u.1 (hcard u) i) = u.1 i := fun u i => encG_encH d u.1 (hcard u) i
  have hinj : Function.Injective mapFn := by
    intro u u' h
    apply Subtype.ext
    funext i
    have h1 : encG u.1 (hcard u) = encG u'.1 (hcard u') := congrArg Prod.fst h
    have h2 : encH d u.1 = encH d u'.1 := congrArg Prod.snd h
    calc u.1 i = encH d u.1 (encG u.1 (hcard u) i) := (hkey u i).symm
      _ = encH d u'.1 (encG u'.1 (hcard u') i) := by rw [h1, h2]
      _ = u'.1 i := hkey u' i
  calc Fintype.card {w : Fin (r + r) → Fin H // (∀ i, ∃ j, j ≠ i ∧ w j = w i)}
      ≤ Fintype.card ((Fin (r + r) → Fin r) × (Fin r → Fin H)) :=
        Fintype.card_le_of_injective mapFn hinj
    _ = r ^ (r + r) * H ^ r := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, Fintype.card_fin]
    _ ≤ (r + r) ^ (r + r) * H ^ r := by
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_left (by omega) (r + r)

end NoSingletonAux

open NoSingletonAux

/-- Functions `Fin (r+r) → Fin H` with no singleton value number at most
`(2r)^(2r) * H^r`. -/
theorem nosingleton_value_count (r : ℕ) (hr : 1 ≤ r) (H : ℕ) :
    (Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
        ¬ ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → w j ≠ w i)).card
      ≤ (2 * r) ^ (2 * r) * H ^ r := by
  have hP : ∀ w : Fin (r + r) → Fin H,
      (¬ ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → w j ≠ w i) ↔
      (∀ i : Fin (r + r), ∃ j : Fin (r + r), j ≠ i ∧ w j = w i) := by
    intro w
    constructor
    · intro h i
      by_contra hc
      apply h
      refine ⟨i, ?_⟩
      intro j hj hw
      exact hc ⟨j, hj, hw⟩
    · rintro h ⟨i, hi⟩
      obtain ⟨j, hj, hw⟩ := h i
      exact hi j hj hw
  have hfilter : (Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
        ¬ ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → w j ≠ w i))
      = (Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
        ∀ i : Fin (r + r), ∃ j : Fin (r + r), j ≠ i ∧ w j = w i)) := by
    apply Finset.filter_congr
    intro w _
    exact hP w
  rw [hfilter]
  cases H with
  | zero =>
    have hempty : (Finset.univ.filter (fun w : Fin (r + r) → Fin 0 =>
        ∀ i : Fin (r + r), ∃ j : Fin (r + r), j ≠ i ∧ w j = w i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _
      exact fun _ => Fin.elim0 (w ⟨0, by omega⟩)
    rw [hempty, Finset.card_empty, Nat.zero_pow (by omega : 0 < r)]
    simp
  | succ k =>
    have h := card_p_le r (k + 1) (by omega)
    rw [show (2 : ℕ) * r = r + r from by omega]
    exact h

end Work.LinnikAreas
