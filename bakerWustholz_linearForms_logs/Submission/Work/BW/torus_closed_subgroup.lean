import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.closedSubAux
import Submission.Work.BW.torus_coset_cover
import Submission.Work.BW.char_sum_at_of_vanishing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Closed subgroups of `0 × G_m^N` are kernels of their character lattice

`torus_closed_subgroup` is statement B2b of the Baker–Wüstholz multiplicity block: if `H` is a
Zariski-closed subgroup of `G = G_a × G_m^N` all of whose elements have vanishing `G_a`-coordinate,
then any point `y` of `0 × G_m^N` at which all characters trivial on `H` are trivial already lies
in `H`.

The proof evaluates a defining polynomial `f` at `(0,t)` for `t` in the torus part `K` of `H`,
rewrites the result as a character sum `∑ c, coeff c · χ_{c'} (t)` and applies the
character-independence lemma `char_sum_at_of_vanishing`.
-/

namespace Work.BW

open MvPolynomial

/-- Evaluation at a point of `0 × G_m^N`, expanded along the support of `f`. -/
lemma eval_cons_zero {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) (t : Fin N → ℂ) :
    MvPolynomial.eval (Fin.cons (0 : ℂ) t) f =
      ∑ c ∈ f.support, f.coeff c *
        ((0 : ℂ) ^ (c 0) * torChar (fun i : Fin N => (c i.succ : ℤ)) t) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  rw [torChar, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zpow_natCast]

/-- **B2b.** A Zariski-closed subgroup of `0 × G_m^N` is the kernel of its character lattice. -/
theorem torus_closed_subgroup {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) (hH : IsClosedSubG H)
    (hH0 : ∀ h ∈ H, h 0 = 0) (y : Fin (N + 1) → ℂ) (hy : InG y) (hy0 : y 0 = 0)
    (hchar : ∀ m : Fin N → ℤ, (∀ h ∈ H, ∏ i, h i.succ ^ m i = 1) → ∏ i, y i.succ ^ m i = 1) :
    y ∈ H := by
  classical
  obtain ⟨hInG, hgone, hmul, hinv, S, hS⟩ := hH
  rw [hS]
  refine ⟨hy, fun f hf => ?_⟩
  -- the torus part `K` of `H`
  set K : Set (Fin N → ℂ) := {t | Fin.cons (0 : ℂ) t ∈ H} with hKdef
  have hKtor : K ⊆ Tor N := by
    intro t ht i
    rw [hKdef] at ht
    have h := (hInG (Fin.cons (0 : ℂ) t) ht) i
    simpa using h
  have hKm : ∀ x ∈ K, ∀ z ∈ K, tmul x z ∈ K := by
    intro x hx z hz
    rw [hKdef] at hx hz ⊢
    show Fin.cons (0 : ℂ) (tmul x z) ∈ H
    have heq : gmul (Fin.cons (0 : ℂ) x) (Fin.cons (0 : ℂ) z)
        = Fin.cons (0 : ℂ) (tmul x z) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp [gmul, tmul]
    rw [← heq]
    exact hmul _ hx _ hz
  have hKone : tOne N ∈ K := by
    rw [hKdef]
    show Fin.cons (0 : ℂ) (fun _ : Fin N => (1 : ℂ)) ∈ H
    simpa [gone] using hgone
  -- the defining polynomial vanishes on the torus part
  have hvan : ∀ t ∈ K, MvPolynomial.eval (Fin.cons (0 : ℂ) t) f = 0 := by
    intro t ht
    rw [hKdef] at ht
    rw [hS] at ht
    exact ht.2 f hf
  -- the character sum relation
  have hrel : ∀ t ∈ K, ∑ c ∈ f.support,
      (f.coeff c * (0 : ℂ) ^ (c 0)) * torChar (fun i : Fin N => (c i.succ : ℤ)) t = 0 := by
    intro t ht
    have h1 := hvan t ht
    rw [eval_cons_zero] at h1
    simpa only [mul_assoc] using h1
  -- compatibility at `y`
  have hcompat : ∀ i ∈ f.support, ∀ j ∈ f.support,
      (∀ k ∈ K, torChar (fun a : Fin N => (i a.succ : ℤ)) k
        = torChar (fun a : Fin N => (j a.succ : ℤ)) k) →
      torChar (fun a : Fin N => (i a.succ : ℤ)) (fun a : Fin N => y a.succ)
        = torChar (fun a : Fin N => (j a.succ : ℤ)) (fun a : Fin N => y a.succ) := by
    intro i hi j hj hij
    set m : Fin N → ℤ := fun a => (i a.succ : ℤ) - (j a.succ : ℤ) with hmdef
    have hmK : m ∈ charLat K := by
      rw [mem_charLat_iff]
      intro k hk hkne
      have heq : (fun a : Fin N => (j a.succ : ℤ)) + m
          = (fun a : Fin N => (i a.succ : ℤ)) := by
        funext a; simp [hmdef]
      have h3 : torChar m k * torChar (fun a : Fin N => (j a.succ : ℤ)) k
          = torChar (fun a : Fin N => (i a.succ : ℤ)) k := by
        rw [mul_comm, ← torChar_add _ _ hkne, heq]
      have h5 : torChar m k * torChar (fun a : Fin N => (j a.succ : ℤ)) k
          = torChar (fun a : Fin N => (j a.succ : ℤ)) k := h3.trans (hij k hk)
      have h6 : torChar m k = 1 := by
        apply mul_right_cancel₀
          (torChar_ne_zero_of_ne (fun a : Fin N => (j a.succ : ℤ)) hkne)
        rw [one_mul]
        exact h5
      exact h6
    have hmchar : torChar m (fun a : Fin N => y a.succ) = 1 := by
      have h := hchar m ?_
      · simpa [torChar] using h
      · intro h hh
        have hhK : (fun a : Fin N => h a.succ) ∈ K := by
          rw [hKdef]
          show Fin.cons (0 : ℂ) (fun a : Fin N => h a.succ) ∈ H
          have heq : h = Fin.cons (0 : ℂ) (fun a : Fin N => h a.succ) := by
            funext a
            refine Fin.cases ?_ ?_ a
            · simpa using hH0 h hh
            · intro b; simp
          rwa [← heq]
        have hhne : ∀ a : Fin N, h a.succ ≠ 0 := fun a => (hInG h hh) a
        simpa [torChar] using (mem_charLat_iff.mp hmK) _ hhK hhne
    have : torChar (fun a : Fin N => (i a.succ : ℤ)) (fun a : Fin N => y a.succ)
        = torChar (fun a : Fin N => (j a.succ : ℤ)) (fun a : Fin N => y a.succ) := by
      have heq : (fun a : Fin N => (j a.succ : ℤ)) + m
          = (fun a : Fin N => (i a.succ : ℤ)) := by
        funext a; simp [hmdef]
      have hyne : ∀ a : Fin N, y a.succ ≠ 0 := fun a => hy a
      rw [← heq, torChar_add _ _ hyne, hmchar, mul_one]
    exact this
  -- the character-independence lemma
  have hmain := char_sum_at_of_vanishing hKm hKone hKtor f.support
    (fun c => f.coeff c * (0 : ℂ) ^ (c 0)) (fun c a => (c a.succ : ℤ))
    (fun a : Fin N => y a.succ) hrel hcompat
  have hyeq : y = Fin.cons (0 : ℂ) (fun a : Fin N => y a.succ) := by
    funext a
    refine Fin.cases ?_ ?_ a
    · simpa using hy0
    · intro b; simp
  rw [hyeq, eval_cons_zero]
  simpa only [mul_assoc] using hmain

end Work.BW
