import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

open Classical

namespace Work.LinnikBurgess

open Polynomial

/-- **Number of roots mod `p` is at most the degree, assuming only that the reduction is nonzero.**

If the reduction `G.map (Int.castRingHom (ZMod p))` of `G ∈ ℤ[X]` modulo the prime `p` is not the
zero polynomial, then the number of residues `r ∈ {0, …, p-1}` with `G(r) ≡ 0 (mod p)` is at most
`G.natDegree`.

Proof (the standard roots-bound over the domain `ZMod p`): put `g = G.map (Int.castRingHom (ZMod p))`,
nonzero by hypothesis. For `r ∈ [0, p)` we have `Polynomial.eval (r : ZMod p) g = ((G.eval (r : ℤ) : ℤ)
: ZMod p)` (`eval_map` together with `eval₂_at_apply`), so `p ∣ G.eval (r : ℤ)` iff `(r : ZMod p)`
is a root of `g`.  Thus the residues in question map injectively (`r ↦ (r : ZMod p)` is injective on
`[0, p)`) into the finite set of distinct roots of `g`, whose cardinality is at most
`g.roots.card ≤ g.natDegree ≤ G.natDegree`. -/
lemma roots_modp_card_le_of_map_ne_zero (p : ℕ) [Fact p.Prime] (G : Polynomial ℤ)
    (hmod : G.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ Polynomial.eval (r : ℤ) G)).card
      ≤ G.natDegree := by
  classical
  -- The reduction of `G` modulo `p`, nonzero by hypothesis.
  set g : Polynomial (ZMod p) := G.map (Int.castRingHom (ZMod p)) with hg
  have hg0 : g ≠ 0 := by rw [hg]; exact hmod
  -- The set of residues `r ∈ [0, p)` that are roots of `G` mod `p`.
  set S := (Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ Polynomial.eval (r : ℤ) G) with hS
  -- The (finset of) distinct roots of the reduction of `G`.
  set T : Finset (ZMod p) := g.roots.toFinset with hT
  -- Their number is bounded by the degree of `G`.
  have hTcard : T.card ≤ G.natDegree := by
    calc T.card ≤ g.roots.card := by rw [hT]; exact Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
      _ ≤ G.natDegree := by rw [hg]; exact Polynomial.natDegree_map_le
  -- Evaluation of the reduction is the reduction of the evaluation.
  have heval : ∀ r : ℕ,
      Polynomial.eval (r : ZMod p) g = ((Polynomial.eval (r : ℤ) G : ℤ) : ZMod p) := by
    intro r
    rw [hg]
    simp [Polynomial.eval_map]
  -- Each residue in `S` becomes a root of `g`.
  have hmaps : Set.MapsTo (fun r : ℕ => (r : ZMod p)) (↑S) (↑T) := by
    intro r hr
    have hdvd : (p : ℤ) ∣ Polynomial.eval (r : ℤ) G := by
      rw [hS] at hr
      exact (Finset.mem_filter.mp hr).2
    have hev : Polynomial.eval (r : ZMod p) g = 0 := by
      rw [heval r]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.eval (r : ℤ) G) p).mpr hdvd
    have hroot : g.IsRoot (r : ZMod p) := by rw [Polynomial.IsRoot.def]; exact hev
    simp only [hT, Finset.mem_coe]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots' (p := g)).mpr ⟨hg0, hroot⟩)
  -- Distinct residues in `[0, p)` stay distinct modulo `p`.
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) (↑S) := by
    intro a ha b hb hab
    rw [hS] at ha hb
    have ha' : a < p := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' : b < p := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have h2 := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
    exact h2
  exact (Finset.card_le_card_of_injOn (fun r : ℕ => (r : ZMod p)) hmaps hinj).trans hTcard

/-- For `e ≤ 3` (so `m = cubeLevel p e = 1`, `y < p`) and `p ∤ contAB a b`, the capped part of the
support has at most `4` elements — no hypothesis on the double-critical level is needed.

`capSet p e a b` is the set of support points `y < p^m` with `T ≤ nval y`, `T = capLevel p e`.

Hints: on `capSet`, `SuppTransfer` gives `p^(m+T) ∣ N(y)` with `m + T ≥ 1`, hence `p ∣ N(y)`, i.e.
`(N mod p)` vanishes at `y`; `hmod` says `(N mod p) ≠ 0`, so `y` is a root of a nonzero polynomial of
degree `≤ natDegree N ≤ 4` over the field `ZMod p`, whence `(capSet p e a b).card ≤ natDegree N ≤ 4`
(`Polynomial.card_roots'`; note `y < p^cubeLevel = p` makes `y ↦ (y : ZMod p)` injective). -/
theorem card_capSet_le_small {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e) (he3 : e ≤ 3)
    (a b : Fin 3 → ℕ) (hdeg : (critN a b).natDegree ≤ 4)
    (hmod : (critN a b).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hbt : SuppTransfer p e a b) :
    (capSet p e a b).card ≤ 4 := by
  -- For `e ≤ 3` the cube level is `1`, so `p ^ cubeLevel p e = p`.
  have hm : cubeLevel p e = 1 := by
    rw [cubeLevel_eq hp5]; omega
  have hm1 : p ^ cubeLevel p e = p := by rw [hm, pow_one]
  -- Every point of `capSet` is a root of `N = critN a b` modulo `p`.
  have hsub : capSet p e a b ⊆
      (Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ (critN a b).eval (r : ℤ)) := by
    intro y hy
    rw [Finset.mem_filter]
    rw [capSet, Finset.mem_filter] at hy
    obtain ⟨hysup, hge⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysup
    obtain ⟨hyr, hpred⟩ := hysup
    have hyr' : y < p := by
      have := Finset.mem_range.mp hyr
      rwa [hm1] at this
    refine ⟨Finset.mem_range.mpr hyr', ?_⟩
    -- `SuppTransfer` gives `b_y = T = min (nval y) T` and `p^(m+T) ∣ N(y)`; as `m ≥ 1` this yields
    -- `p ∣ N(y)`.
    obtain ⟨hbval, hdivN⟩ := hbt y hpred
    have hmin : bval p e a b y = capLevel p e := by rw [hbval]; exact min_eq_right hge
    rw [hmin, hm] at hdivN
    have hp_dvd : (p : ℤ) ∣ ((p ^ (1 + capLevel p e) : ℕ) : ℤ) := by
      rw [Nat.cast_pow]
      exact dvd_pow_self _ (by omega)
    exact dvd_trans hp_dvd hdivN
  calc (capSet p e a b).card
      ≤ ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ (critN a b).eval (r : ℤ))).card :=
        Finset.card_le_card hsub
    _ ≤ (critN a b).natDegree := roots_modp_card_le_of_map_ne_zero p (critN a b) hmod
    _ ≤ 4 := hdeg

end Work.LinnikBurgess
