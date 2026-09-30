import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

open Finset

/-- **Linnik's linear counting lemma.**

Let `p` be a prime, `k < p`, `1 ≤ m` and `m + 1 ≤ k`, and let `a : Fin k → Fin p` be
injective.  Then for any `C : ℕ → ℤ` the number of `w : Fin k → Fin p` such that for every
`j` with `m + 1 ≤ j ≤ k` one has
`p ∣ C j + j * (∑ i, (a i)^(j-1) * (w i))`
is at most `p ^ m`.

The point is that the `k - m` congruences are linear conditions in the `k` unknowns
`w i`, with coefficient matrix the (transposed) Vandermonde matrix `(a i)^(j-1)` restricted
to the exponents `m, …, k-1`.  Since `a` is injective this matrix has rank `k - m`, so every
fibre of the associated affine map has at most `p ^ m` elements. -/
theorem linnik_lin (p k m : ℕ) (hp : p.Prime) (hk : k < p) (hm1 : 1 ≤ m) (hmk : m + 1 ≤ k)
    (a : Fin k → Fin p) (ha : Function.Injective a) (C : ℕ → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin p)).filter (fun w =>
      ∀ j, m + 1 ≤ j → j ≤ k →
        (p : ℤ) ∣ C j + (j : ℤ) * (∑ i, ((a i).val : ℤ) ^ (j - 1) * ((w i).val : ℤ)))).card
    ≤ p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Work over the field `F = ZMod p`.
  let afun : Fin k → ZMod p := fun i => ((a i).val : ℕ)
  -- The embedding of the constrained indices `m, …, k-1` into `Fin k`.
  let emb : Fin (k - m) → Fin k := fun t => ⟨m + t.val, by omega⟩
  -- The transposed Vandermonde ("moment") map.
  let V : (Fin k → ZMod p) → (Fin k → ZMod p) := fun x e => ∑ i, afun i ^ (e:ℕ) * x i
  -- The reduction `Fin p → ZMod p`.
  let iota : (Fin k → Fin p) → (Fin k → ZMod p) := fun w i => ((w i).val : ℕ)
  have hemb_val : ∀ t : Fin (k - m), (emb t).val = m + t.val := fun _ => rfl
  -- `afun` is injective because `a` is and `ℕ → ZMod p` is injective on `[0, p)`.
  have haf : Function.Injective afun := by
    intro i j hij
    have h1 : (afun i).val = (afun j).val := congrArg ZMod.val hij
    simp only [afun] at h1
    rw [ZMod.val_cast_of_lt (a i).isLt, ZMod.val_cast_of_lt (a j).isLt] at h1
    exact ha (Fin.ext h1)
  -- The moment map is injective (Vandermonde / Lagrange interpolation).
  have hV_inj : Function.Injective V := by
    intro x y hxy
    have hz : x - y = 0 :=
      Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ZMod p) haf (v := x - y) (fun e => by
        have h := congrFun hxy e
        simp only [V] at h
        have key : ∀ j : Fin k, (x - y) j * afun j ^ (e:ℕ)
            = x j * afun j ^ (e:ℕ) - y j * afun j ^ (e:ℕ) := by
          intro j; simp only [Pi.sub_apply]; ring
        simp only [key]
        rw [Finset.sum_sub_distrib]
        rw [show (∑ j, x j * afun j ^ (e:ℕ)) = ∑ j, afun j ^ (e:ℕ) * x j from
            Finset.sum_congr rfl (fun j _ => mul_comm _ _),
            show (∑ j, y j * afun j ^ (e:ℕ)) = ∑ j, afun j ^ (e:ℕ) * y j from
            Finset.sum_congr rfl (fun j _ => mul_comm _ _)]
        rw [h, sub_self])
    funext i
    have := congrFun hz i
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  -- The translated counting problem over `ZMod p`.
  let Good : Finset (Fin k → ZMod p) := Finset.univ.filter (fun x => ∀ t : Fin (k - m),
      (C ((emb t).val + 1) : ZMod p) + (((emb t).val + 1 : ℕ) : ZMod p) * V x (emb t) = 0)
  -- The `Fin p`-valued solutions inject into the `ZMod p`-valued ones.
  have hS_le : ((Finset.univ : Finset (Fin k → Fin p)).filter (fun w =>
      ∀ j, m + 1 ≤ j → j ≤ k →
        (p : ℤ) ∣ C j + (j : ℤ) * (∑ i, ((a i).val : ℤ) ^ (j - 1) * ((w i).val : ℤ)))).card
      ≤ Good.card := by
    have hiota : Function.Injective iota := by
      intro w w' h
      funext i
      have h1 : (iota w i).val = (iota w' i).val := congrArg ZMod.val (congrFun h i)
      simp only [iota] at h1
      rw [ZMod.val_cast_of_lt (w i).isLt, ZMod.val_cast_of_lt (w' i).isLt] at h1
      exact Fin.ext h1
    rw [← Finset.card_image_of_injective _ hiota]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [Finset.mem_filter] at hw
    obtain ⟨-, hw⟩ := hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun t => ?_⟩
    -- the `t`-th congruence of `w`, transported to `ZMod p`
    have hcond := hw ((emb t).val + 1) (by rw [hemb_val t]; omega) (by rw [hemb_val t]; omega)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hcond
    have had : (((C ((emb t).val + 1) + (((emb t).val + 1 : ℕ) : ℤ) *
        (∑ i, ((a i).val : ℤ) ^ (((emb t).val + 1) - 1) * ((w i).val : ℤ)) : ℤ) : ZMod p))
        = (C ((emb t).val + 1) : ZMod p)
          + (((emb t).val + 1 : ℕ) : ZMod p) * V (iota w) (emb t) := by
      simp only [V, iota]
      push_cast
      ring
    rw [← had]
    exact hcond
  -- Each fibre of the affine constraint map has at most `p ^ m` elements: two solutions agree
  -- on the constrained moments and then, if they agree on the `m` free ones, on all of them.
  have hGood_bound : Good.card ≤ p ^ m := by
    have hjne : ∀ t : Fin (k - m), (((emb t).val + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro t hzero
      have hlt : (emb t).val + 1 < p := by
        rw [hemb_val t]; have h := (emb t).isLt; rw [hemb_val t] at h; omega
      have h1 : (((emb t).val + 1 : ℕ) : ZMod p).val = ((0 : ZMod p)).val := by rw [hzero]
      rw [ZMod.val_cast_of_lt (n := p) hlt, ZMod.val_zero] at h1
      omega
    have hκ : Set.InjOn (fun x : Fin k → ZMod p => fun s : Fin m => V x ⟨s.val, by omega⟩) ↑Good := by
      intro x hx x' hx' hκeq
      have hxm : ∀ s : Fin m, V x ⟨s.val, by omega⟩ = V x' ⟨s.val, by omega⟩ :=
        fun s => congrFun hκeq s
      have hxg := (Finset.mem_filter.mp hx).2
      have hx'g := (Finset.mem_filter.mp hx').2
      -- both solutions realise the prescribed moments, so they agree on `m, …, k-1`
      have hconstr : ∀ t : Fin (k - m), V x (emb t) = V x' (emb t) := by
        intro t
        have h1 := hxg t
        have h2 := hx'g t
        have e1 : (((emb t).val + 1 : ℕ) : ZMod p) * V x (emb t) = -(C ((emb t).val + 1) : ZMod p) :=
          eq_neg_of_add_eq_zero_right h1
        have e2 : (((emb t).val + 1 : ℕ) : ZMod p) * V x' (emb t) = -(C ((emb t).val + 1) : ZMod p) :=
          eq_neg_of_add_eq_zero_right h2
        have hmul : (((emb t).val + 1 : ℕ) : ZMod p) * (V x (emb t) - V x' (emb t)) = 0 := by
          rw [mul_sub, e1, e2, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (hjne t))
      apply hV_inj
      funext i
      by_cases hi : i.val < m
      · have h1 := hxm ⟨i.val, hi⟩
        simpa only [Fin.val_mk] using h1
      · have h1 := hconstr ⟨i.val - m, by omega⟩
        have h2 : (emb ⟨i.val - m, by omega⟩ : Fin k) = i := by
          apply Fin.ext
          simp only [emb]
          omega
        rw [h2] at h1
        exact h1
    have hcard' : Good.card ≤ (Finset.univ : Finset (Fin m → ZMod p)).card := by
      rw [← Finset.card_image_of_injOn hκ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard'
    exact hcard'
  calc _ ≤ Good.card := hS_le
    _ ≤ p ^ m := hGood_bound

end Work.BMF.N4chain
