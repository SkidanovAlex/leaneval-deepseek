import Mathlib
import Submission.Commons.Combinatorics.Composition.bounded_card_rec

open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Combinatorics.TupleCount

private abbrev S (q t : ℕ) : Type :=
  {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
    (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
    (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
    (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = t}

private def GoodF (q t : ℕ) (l : List (Fin (2 * q))) : Prop :=
  (∀ b ∈ l, 1 ≤ ((b : Fin (2 * q)) : ℕ)) ∧
  (∀ b ∈ l, ¬ (q ∣ ((b : Fin (2 * q)) : ℕ))) ∧
  (l.map (fun b : Fin (2 * q) => ((b : Fin (2 * q)) : ℕ))).sum = t

private noncomputable def e2 (N : ℕ) :
    (Σ r : Fin N, Fin r → Fin N) ≃ {s : Σ n : ℕ, Fin n → Fin N // s.1 < N} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv x := by rcases x with ⟨⟨r, hr⟩, f⟩; rfl
  right_inv y := by rcases y with ⟨⟨n, f⟩, hn⟩; rfl

private noncomputable def e3 (N : ℕ) :
    {l : List (Fin N) // l.length < N} ≃ {s : Σ n : ℕ, Fin n → Fin N // s.1 < N} :=
  Equiv.subtypeEquiv (List.equivSigmaTuple (α := Fin N)) (fun l => by
    simp [List.equivSigmaTuple])

private noncomputable def eS (N : ℕ) :
    (Σ r : Fin N, Fin r → Fin N) ≃ {l : List (Fin N) // l.length < N} :=
  (e2 N).trans (e3 N).symm

@[simp] private lemma eS_val (N : ℕ) (x : Σ r : Fin N, Fin r → Fin N) :
    (eS N x).1 = List.ofFn x.2 := rfl

private abbrev Bnd (B t : ℕ) : Type := {c : Composition t // ∀ b ∈ c.blocks, b ≤ B}

private noncomputable def nemb (q : ℕ) (hq : 2 ≤ q) (y : ℕ) : Fin (2 * q) :=
  if h : y < 2 * q then ⟨y, h⟩ else ⟨0, by omega⟩

private lemma nemb_lt (q : ℕ) (hq : 2 ≤ q) {y : ℕ} (h : y < 2 * q) :
    nemb q hq y = ⟨y, h⟩ := dif_pos h

private lemma nemb_val (q : ℕ) (hq : 2 ≤ q) {y : ℕ} (h : y < 2 * q) :
    ((nemb q hq y : Fin (2 * q)) : ℕ) = y := by rw [nemb_lt q hq h]

private lemma nemb_fin (q : ℕ) (hq : 2 ≤ q) (x : Fin (2 * q)) : nemb q hq (x : ℕ) = x := by
  rw [nemb_lt q hq x.2]

private noncomputable def S'toBnd (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q)
    (b : {b : {l : List (Fin (2 * q)) // l.length < 2 * q} // GoodF q t b.1}) :
    Bnd (q - 1) t :=
  ⟨⟨b.1.1.map (fun x : Fin (2*q) => ((x : Fin (2*q)) : ℕ)),
    (by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      have := b.2.1 x hx
      omega),
    b.2.2.2⟩,
   (by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      have hmem : ((x : Fin (2*q)) : ℕ) ∈ b.1.1.map (fun x : Fin (2*q) => ((x : Fin (2*q)) : ℕ)) :=
        List.mem_map.mpr ⟨x, hx, rfl⟩
      have hle : ((x : Fin (2*q)) : ℕ) ≤ t := by
        have := List.le_sum_of_mem hmem
        rwa [b.2.2.2] at this
      have hne : ((x : Fin (2*q)) : ℕ) ≠ q := by
        intro hh; exact b.2.2.1 x hx (by rw [hh])
      omega)⟩

@[simp] private lemma S'toBnd_blocks (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q)
    (b : {b : {l : List (Fin (2 * q)) // l.length < 2 * q} // GoodF q t b.1}) :
    (S'toBnd q t hq ht b).1.blocks
      = b.1.1.map (fun x : Fin (2*q) => ((x : Fin (2*q)) : ℕ)) := rfl

private noncomputable def S'ofBnd (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q)
    (c : Bnd (q - 1) t) :
    {b : {l : List (Fin (2 * q)) // l.length < 2 * q} // GoodF q t b.1} :=
  ⟨⟨c.1.blocks.map (nemb q hq),
    (by
      rw [List.length_map]
      have h := Composition.length_le c.1
      have : c.1.length = c.1.blocks.length := rfl
      omega)⟩,
   ⟨(by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      have hxq : x ≤ q - 1 := c.2 x hx
      have hxlt : x < 2*q := by omega
      rw [nemb_val q hq hxlt]
      have := c.1.blocks_pos hx
      omega),
    (by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      have hxq : x ≤ q - 1 := c.2 x hx
      have hxlt : x < 2*q := by omega
      rw [nemb_val q hq hxlt]
      intro hdvd
      have : q ≤ x := Nat.le_of_dvd (c.1.blocks_pos hx) hdvd
      omega),
    (by
      rw [List.map_map]
      have hmap : c.1.blocks.map (((fun b : Fin (2*q) => (b:ℕ))) ∘ nemb q hq)
          = c.1.blocks.map (fun a => a) :=
        List.map_congr_left (fun x hx => by
          simp only [Function.comp_apply]
          exact nemb_val q hq (by have := c.2 x hx; omega))
      rw [hmap, List.map_id', c.1.blocks_sum])⟩⟩

@[simp] private lemma S'ofBnd_val (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q) (c : Bnd (q - 1) t) :
    (S'ofBnd q t hq ht c).1.1 = c.1.blocks.map (nemb q hq) := rfl

private noncomputable def S'_equiv_Bnd (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q) :
    {b : {l : List (Fin (2 * q)) // l.length < 2 * q} // GoodF q t b.1} ≃ Bnd (q - 1) t where
  toFun := S'toBnd q t hq ht
  invFun := S'ofBnd q t hq ht
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [S'ofBnd_val, S'toBnd_blocks]
    rw [List.map_map]
    exact List.map_id'' (fun x => nemb_fin q hq x) _
  right_inv c := by
    apply Subtype.ext
    apply Composition.ext
    simp only [S'ofBnd_val, S'toBnd_blocks]
    rw [List.map_map]
    have hmap : c.1.blocks.map (((fun b : Fin (2*q) => (b:ℕ))) ∘ nemb q hq)
        = c.1.blocks.map (fun a => a) :=
      List.map_congr_left (fun x hx => by
        simp only [Function.comp_apply]
        exact nemb_val q hq (by have := c.2 x hx; omega))
    rw [hmap, List.map_id']

private noncomputable def S_equiv_Bnd (q t : ℕ) (hq : 2 ≤ q) (ht : t ≤ q) :
    S q t ≃ Bnd (q - 1) t :=
  (Equiv.subtypeEquiv (eS (2*q)) (fun x => by
    simp only [eS_val, GoodF, List.forall_mem_ofFn_iff, List.map_ofFn, Function.comp_apply,
      List.sum_ofFn])).trans (S'_equiv_Bnd q t hq ht)

theorem tpW_rec_small (q w : ℕ) (hq : 2 ≤ q) (hw : 1 ≤ w) (hwq : w ≤ q) :
    Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
        (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
        (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
        (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w}
      = ∑ i ∈ Finset.range (min w (q - 1)),
        Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
          (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
          (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
          (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w - (i + 1)} := by
  have hB : 1 ≤ q - 1 := by omega
  change Nat.card (S q w)
      = ∑ i ∈ Finset.range (min w (q - 1)), Nat.card (S q (w - (i + 1)))
  rw [Nat.card_congr (S_equiv_Bnd q w hq hwq)]
  rw [Commons.Combinatorics.Composition.bounded_card_rec (q - 1) w hB hw]
  rw [Nat.min_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Nat.card_congr (S_equiv_Bnd q (w - (i + 1)) hq (le_trans (Nat.sub_le w (i+1)) hwq))]

end Commons.Combinatorics.TupleCount
