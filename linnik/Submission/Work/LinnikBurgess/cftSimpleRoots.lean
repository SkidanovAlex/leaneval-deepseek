import Mathlib

set_option linter.style.haveILetI false

namespace Work.LinnikBurgess

/-- Over the prime field `ZMod p`, a polynomial has at most `natDegree` simple roots:
the simple roots form a subset of the (distinct) roots, whose number is at most
`g.roots.card ≤ g.natDegree`. -/
lemma zmod_simpleRoots_card_le_natDegree (p : ℕ) [Fact p.Prime] (g : Polynomial (ZMod p)) :
    ((Finset.univ : Finset (ZMod p)).filter
      (fun x => g.eval x = 0 ∧ g.derivative.eval x ≠ 0)).card ≤ g.natDegree := by
  classical
  by_cases hg : g = 0
  · subst hg; simp
  · calc ((Finset.univ : Finset (ZMod p)).filter
            (fun x => g.eval x = 0 ∧ g.derivative.eval x ≠ 0)).card
        ≤ g.roots.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact Multiset.mem_toFinset.mpr
            ((Polynomial.mem_roots' (p := g)).mpr
              ⟨hg, by rw [Polynomial.IsRoot.def]; exact hx.1⟩)
      _ ≤ g.roots.card := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g

/-- **Count of simple roots modulo `p` of a degree `≤ 4` polynomial.**

If `Q ∈ ℤ[X]` has degree at most `4`, then fewer than four residues `r` modulo `p`
satisfy `Q'(r) ≡ 0 (mod p)` while `Q''(r) ≢ 0 (mod p)`.  Indeed, the reduction of `Q'`
modulo `p` is a polynomial over the field `ZMod p` of degree at most `3`, and the residues
in question are exactly its simple roots; a polynomial of degree `d` has at most `d`
(distinct) roots. -/
lemma cftSimpleRoots {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ) (hdeg : Q.natDegree ≤ 4) :
    ((Finset.range p).filter (fun r : ℕ =>
        (p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ)
        ∧ ¬ (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ))).card
      ≤ 3 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Reduce the polynomial modulo `p`.
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hf
  set H : Polynomial (ZMod p) := Polynomial.map f (Polynomial.derivative Q) with hH
  -- Evaluation of the reductions is the reduction of the evaluations.
  have heval1 : ∀ r : ℕ,
      H.eval (r : ZMod p) = ((Polynomial.derivative Q).eval (r : ℤ) : ℤ) := by
    intro r
    rw [hH]; simp [Polynomial.eval_map]
  have hHd : H.derivative = Polynomial.map f (Polynomial.derivative (Polynomial.derivative Q)) := by
    rw [hH, Polynomial.derivative_map]
  have heval2 : ∀ r : ℕ, H.derivative.eval (r : ZMod p) =
      ((Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ) : ℤ) := by
    intro r
    rw [hHd]; simp [Polynomial.eval_map]
  -- The two counting problems agree.
  have hmain : ((Finset.range p).filter (fun r : ℕ =>
        (p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ)
        ∧ ¬ (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ))).card
      = ((Finset.univ : Finset (ZMod p)).filter (fun x : ZMod p =>
          H.eval x = 0 ∧ H.derivative.eval x ≠ 0)).card := by
    refine Finset.card_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨hrange, hd1, hd2⟩ := hr
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [heval1 r, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hd1
      · rw [heval2 r]
        intro h
        exact hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      have ha' : a < p := Finset.mem_range.mp ha.1
      have hb' : b < p := Finset.mem_range.mp hb.1
      have h2 := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨-, hx1, hx2⟩ := hx
      have hx1' : H.eval ((x.val : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_zmod_val x]; exact hx1
      have hx2' : H.derivative.eval ((x.val : ℕ) : ZMod p) ≠ 0 := by
        rw [ZMod.natCast_zmod_val x]; exact hx2
      refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_, ?_⟩
      · rw [heval1 x.val] at hx1'
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx1'
      · intro h
        exact hx2' (by rw [heval2 x.val]
                       exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)
  rw [hmain]
  refine (zmod_simpleRoots_card_le_natDegree p H).trans ?_
  have h1 : H.natDegree ≤ (Polynomial.derivative Q).natDegree := by
    rw [hH]; exact Polynomial.natDegree_map_le
  have h2 : (Polynomial.derivative Q).natDegree ≤ Q.natDegree - 1 :=
    Polynomial.natDegree_derivative_le Q
  omega

end Work.LinnikBurgess
