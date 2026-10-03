import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Cover
import Submission.Work.KMTPlan.A6.ConcAux.rescale_bound
import Submission.Work.KMTPlan.A6.ConcAux.sum_rootMultiplicity_le_natDegree
import Submission.Work.KMTPlan.A6.ConcAux.taylor_dvd_iff_rootMultiplicity
import Submission.Work.KMTPlan.A6.ConcAux.exists_content_decomp

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fibre of a polynomial modulo `p ^ k` is covered by at most `deg G` balls

This is Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages* (Annals 195 (2022)), Appendix C, Proposition `prop:zero`(i) in the sharp form needed
here: the zero set of `G` in `ℤ/p^kℤ` is a union of at most `max 1 G.natDegree` residue classes
mod `p^m`, each of which is *contained* in the zero set.

The proof (in `Cover.lean`) is the recursive digit expansion: writing a zero `x` of `G` mod `p^k`
as `x = r + p t` with `r = x mod p` a root of `G` mod `p`, the condition `p^k ∣ G(x)` is
equivalent to `p^{k-1} ∣ (G(r + pX)/p)(t)`; the rescaled polynomial is decomposed by its
`p`-content, reducing to the induction hypothesis.  The number of balls produced above the root
`r` is bounded by the multiplicity of `r` in the reduction of `G` mod `p`, and the multiplicities
of the distinct roots sum to at most `deg(G mod p) ≤ deg G`.
-/

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Finset

noncomputable section

/-- **The fibre of `G` mod `p^k` is a union of at most `max 1 G.natDegree` balls contained in it.**
-/
theorem fibre_ballCover (G : Polynomial ℤ) (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) :
    ∃ N : ℕ, N ≤ max 1 G.natDegree ∧ ∃ a : Fin N → ZMod (p ^ k), ∃ m : Fin N → ℕ,
      (∀ l : Fin N, m l ≤ k) ∧
      (∀ (l : Fin N) (x : ZMod (p ^ k)), (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ)) →
          (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)) ∧
      (∀ x : ZMod (p ^ k), (p : ℤ) ^ k ∣ G.eval (x.val : ℤ) →
          ∃ l : Fin N, (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ))) := by
  classical
  obtain ⟨C, h1, h2, h3⟩ := exists_cover_general p
    (fun H r s hs hr h1 h2 => rescale_bound p H r s hs hr h1 h2)
    (fun H r hH => taylor_dvd_iff_rootMultiplicity p H hH)
    (fun H hH => sum_rootMultiplicity_le_natDegree p H hH)
    (fun H => exists_content_decomp p H)
    k hk G
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Nat.Prime.ne_zero (Fact.out (p := p.Prime)))⟩
  refine ⟨C.card, h3, ?_⟩
  set e : Fin C.card ≃ ↥C := (Finset.equivFin C).symm with he
  refine ⟨fun l => (((((e l).1).1 : ℕ)) : ZMod (p ^ k)), fun l => ((e l).1).2, ?_, ?_, ?_⟩
  · intro l
    exact (h1 (e l).1 (e l).2).1
  · intro l x hx
    have hlev : ((e l).1).2 ≤ k := (h1 (e l).1 (e l).2).1
    have hval : ((((e l).1).1 : ℕ) : ZMod (p ^ k)).val = ((e l).1).1 % p ^ k :=
      ZMod.val_natCast (p ^ k) ((e l).1).1
    have hx' : (p : ℤ) ^ ((e l).1).2 ∣ (x.val : ℤ) - (((e l).1).1 : ℤ) := by
      rw [hval] at hx
      have hd : (p : ℤ) ^ ((e l).1).2 ∣ (((e l).1).1 : ℤ) -
          (((((e l).1).1 % p ^ k : ℕ)) : ℤ) :=
        dvd_trans (pow_dvd_pow (p : ℤ) hlev) (dvd_sub_mod (p := p) k ((e l).1).1)
      have heq : (x.val : ℤ) - (((e l).1).1 : ℤ) =
          ((x.val : ℤ) - (((((e l).1).1 % p ^ k : ℕ)) : ℤ)) -
            ((((e l).1).1 : ℤ) - (((((e l).1).1 % p ^ k : ℕ)) : ℤ)) := by ring
      rw [heq]
      exact dvd_sub hx hd
    have hmem : x.val ∈ fibre p k G := (h1 (e l).1 (e l).2).2 (by
      rw [mem_ball]
      exact ⟨ZMod.val_lt x, hx'⟩)
    rw [mem_fibre] at hmem
    exact hmem.2
  · intro x hx
    have hxfib : x.val ∈ fibre p k G := by
      rw [mem_fibre]
      exact ⟨ZMod.val_lt x, hx⟩
    obtain ⟨am, hamC, hball⟩ := h2 x.val hxfib
    rw [mem_ball] at hball
    let amC : ↥C := ⟨am, hamC⟩
    refine ⟨e.symm amC, ?_⟩
    have hesel : e (e.symm amC) = amC := e.apply_symm_apply amC
    have hleveq : ((e (e.symm amC)).1).2 = am.2 := congrArg (fun z : ↥C => z.1.2) hesel
    have hceq : ((e (e.symm amC)).1).1 = am.1 := congrArg (fun z : ↥C => z.1.1) hesel
    change (p : ℤ) ^ ((e (e.symm amC)).1).2 ∣
      (x.val : ℤ) - ((((e (e.symm amC)).1).1 : ℕ) : ZMod (p ^ k)).val
    rw [hleveq, hceq]
    have hlev : am.2 ≤ k := (h1 am hamC).1
    have hval : (((am.1 : ℕ)) : ZMod (p ^ k)).val = am.1 % p ^ k :=
      ZMod.val_natCast (p ^ k) am.1
    rw [hval]
    have hd : (p : ℤ) ^ am.2 ∣ (am.1 : ℤ) - ((((am.1 % p ^ k : ℕ))) : ℤ) :=
      dvd_trans (pow_dvd_pow (p : ℤ) hlev) (dvd_sub_mod (p := p) k am.1)
    have heq : (x.val : ℤ) - (((am.1 % p ^ k : ℕ)) : ℤ) =
        ((x.val : ℤ) - (am.1 : ℤ)) + ((am.1 : ℤ) - (((am.1 % p ^ k : ℕ)) : ℤ)) := by ring
    rw [heq]
    exact dvd_add hball.2 hd

end

end Work.KMTPlan.A6.ConcAux
