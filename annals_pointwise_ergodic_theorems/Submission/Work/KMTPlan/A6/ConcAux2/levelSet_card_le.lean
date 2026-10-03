import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.fibre_card_le_of_cover

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The level set of a polynomial at a general `p`-adic depth

If the *full* level set `{x : ℤ/p^Kℤ // p^K ∣ G x}` is bounded by
`C * p^{K (1 - 1/deg G)}` (uniformly in `p` and `K`), then the level set at a *shallower* depth
`L ≤ k`,
`{x : ℤ/p^kℤ // p^L ∣ G x}`,
is bounded by `C * p^{k - L/deg G}`.

The reason is that the reduction map `ℤ/p^kℤ → ℤ/p^Lℤ` (well defined because `L ≤ k`) has all its
fibres of size `p^{k - L}` and maps the shallow level set onto the shallow level set at level `L`:
if `x ≡ y (mod p^L)` then `G x ≡ G y (mod p^L)` because `G` has integer coefficients.  Counting
the fibres gives `p^{k-L} · C p^{L(1 - 1/deg G)} = C p^{k - L/deg G}`.
-/

namespace Work.KMTPlan.A6.ConcAux2

theorem levelSet_card_le (G : Polynomial ℤ) (hG : 1 ≤ G.natDegree) (C : ℝ) (hC : 0 < C) (hb : ∀ (p : ℕ) [Fact p.Prime] (K : ℕ), 1 ≤ K → ((Finset.univ.filter (fun x : ZMod (p ^ K) => (p : ℤ) ^ K ∣ G.eval (x.val : ℤ))).card : ℝ) ≤ C * (p : ℝ) ^ ((K : ℝ) * (1 - 1 / (G.natDegree : ℝ)))) (p k L : ℕ) [Fact p.Prime] (hL : 1 ≤ L) (hLk : L ≤ k) : ((Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ L ∣ G.eval (x.val : ℤ))).card : ℝ) ≤ C * (p : ℝ) ^ ((k : ℝ) - (L : ℝ) / (G.natDegree : ℝ)) := by
  classical
  have _hCpos : (0 : ℝ) < C := hC
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hdvd : p ^ L ∣ p ^ k := pow_dvd_pow p hLk
  -- the shallow level set inside `ZMod (p ^ k)` and the one inside `ZMod (p ^ L)`
  set S : Finset (ZMod (p ^ k)) :=
    Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ L ∣ G.eval (x.val : ℤ)) with hS
  set T : Finset (ZMod (p ^ L)) :=
    Finset.univ.filter (fun y : ZMod (p ^ L) => (p : ℤ) ^ L ∣ G.eval (y.val : ℤ)) with hT
  -- the value of the reduction map
  have hφval : ∀ x : ZMod (p ^ k), (ZMod.castHom hdvd (ZMod (p ^ L)) x).val = x.val % p ^ L := by
    intro x
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  -- the coordinate in the fibre
  have hgt : ∀ x : ZMod (p ^ k), x.val / p ^ L < p ^ (k - L) := by
    intro x
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 L), mul_comm, ← pow_add, Nat.add_sub_of_le hLk]
    exact x.val_lt
  -- the injection `x ↦ (x mod p^L, x / p^L)`
  have hfmem : Set.MapsTo (fun x : ZMod (p ^ k) =>
        (ZMod.castHom hdvd (ZMod (p ^ L)) x, (⟨x.val / p ^ L, hgt x⟩ : Fin (p ^ (k - L)))))
      ↑S ↑(T ×ˢ (Finset.univ : Finset (Fin (p ^ (k - L))))) := by
    intro x hx
    simp only [hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (p : ℤ) ^ L ∣ G.eval (((ZMod.castHom hdvd (ZMod (p ^ L)) x).val : ℕ) : ℤ)
    rw [hφval x]
    -- `x ≡ x % p^L (mod p^L)`, hence `G x ≡ G (x % p^L) (mod p^L)`
    have hsub : (p : ℤ) ^ L ∣ (x.val : ℤ) - ((x.val % p ^ L : ℕ) : ℤ) := by
      refine ⟨(x.val / p ^ L : ℕ), ?_⟩
      have hcast : ((x.val : ℕ) : ℤ) =
          ((x.val % p ^ L : ℕ) : ℤ) + ((p ^ L * (x.val / p ^ L) : ℕ) : ℤ) := by
        have h := Nat.mod_add_div x.val (p ^ L)
        omega
      rw [hcast]
      push_cast
      ring
    have hcong : (p : ℤ) ^ L ∣ G.eval (x.val : ℤ) - G.eval (((x.val % p ^ L : ℕ)) : ℤ) :=
      dvd_trans hsub (Polynomial.sub_dvd_eval_sub (x.val : ℤ) ((x.val % p ^ L : ℕ) : ℤ) G)
    have h := dvd_sub hx hcong
    simpa using h
  have hfinj : Set.InjOn (fun x : ZMod (p ^ k) =>
        (ZMod.castHom hdvd (ZMod (p ^ L)) x, (⟨x.val / p ^ L, hgt x⟩ : Fin (p ^ (k - L))))) ↑S := by
    intro x _ y _ hxy
    have h1 : ZMod.castHom hdvd (ZMod (p ^ L)) x = ZMod.castHom hdvd (ZMod (p ^ L)) y :=
      congrArg Prod.fst hxy
    have h2 : x.val / p ^ L = y.val / p ^ L := by
      have h := congrArg (fun t : ZMod (p ^ L) × Fin (p ^ (k - L)) => (t.2 : ℕ)) hxy
      simpa using h
    have h3 : x.val % p ^ L = y.val % p ^ L := by
      have h := congrArg (fun t : ZMod (p ^ L) => t.val) h1
      rw [hφval x, hφval y] at h
      exact h
    have h4 : x.val = y.val := by
      have hx' := Nat.mod_add_div x.val (p ^ L)
      have hy' := Nat.mod_add_div y.val (p ^ L)
      rw [h3, h2] at hx'
      omega
    exact ZMod.val_injective (p ^ k) h4
  have hcard := Finset.card_le_card_of_injOn (fun x : ZMod (p ^ k) =>
        (ZMod.castHom hdvd (ZMod (p ^ L)) x, (⟨x.val / p ^ L, hgt x⟩ : Fin (p ^ (k - L)))))
      hfmem hfinj
  have hTcard : (T ×ˢ (Finset.univ : Finset (Fin (p ^ (k - L))))).card = T.card * p ^ (k - L) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hTb : (T.card : ℝ) ≤ C * (p : ℝ) ^ ((L : ℝ) * (1 - 1 / (G.natDegree : ℝ))) := by
    rw [hT]
    exact hb p L hL
  have hpow : (p : ℝ) ^ ((L : ℝ) * (1 - 1 / (G.natDegree : ℝ))) * (p : ℝ) ^ (k - L)
      = (p : ℝ) ^ ((k : ℝ) - (L : ℝ) / (G.natDegree : ℝ)) := by
    rw [← Real.rpow_natCast (p : ℝ) (k - L), ← Real.rpow_add (by positivity : (0 : ℝ) < p)]
    congr 1
    rw [Nat.cast_sub hLk]
    field_simp
    ring
  calc (S.card : ℝ)
      ≤ ((T ×ˢ (Finset.univ : Finset (Fin (p ^ (k - L))))).card : ℝ) := by
        exact_mod_cast hcard
    _ = (T.card : ℝ) * (p : ℝ) ^ (k - L) := by
        rw [hTcard]; push_cast; ring
    _ ≤ (C * (p : ℝ) ^ ((L : ℝ) * (1 - 1 / (G.natDegree : ℝ)))) * (p : ℝ) ^ (k - L) :=
        mul_le_mul_of_nonneg_right hTb (by positivity)
    _ = C * (p : ℝ) ^ ((k : ℝ) - (L : ℝ) / (G.natDegree : ℝ)) := by
        rw [mul_assoc, hpow]

end Work.KMTPlan.A6.ConcAux2
