/-
  `critRes_card_le_three`

  A non-zero polynomial of degree at most `3` over a field has at most `3` roots.
  Here the relevant polynomial is `Q.derivative` reduced modulo `p`: its degree over
  `ℤ` is at most `Q.natDegree - 1 ≤ 3`, and reducing coefficients modulo the prime `p`
  cannot raise the degree.  The hypothesis `hg` says this reduction is non-zero.

  The integers `r ∈ {0, …, p-1}` with `p ∣ Q.derivative.eval r` biject (via `r ↦ r mod p`)
  onto a subset of the roots of the reduced polynomial, whence the bound `3`.
-/
import Mathlib

namespace Work.LinnikBurgess

open Polynomial

theorem critRes_card_le_three {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ) (hdeg : Q.natDegree ≤ 4)
    (hg : Q.derivative.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ Q.derivative.eval (r : ℤ))).card ≤ 3 := by
  -- The reduced derivative, a non-zero polynomial over `ZMod p`.
  set P : Polynomial (ZMod p) := Q.derivative.map (Int.castRingHom (ZMod p)) with hP
  have hPne : P ≠ 0 := hg
  -- Its degree is at most `3`.
  have hPdeg : P.natDegree ≤ 3 := by
    have h1 : P.natDegree ≤ Q.derivative.natDegree := by rw [hP]; exact natDegree_map_le
    have h2 : Q.derivative.natDegree ≤ Q.natDegree - 1 := natDegree_derivative_le Q
    have h3 : Q.natDegree - 1 ≤ 3 := by omega
    omega
  -- The finset of roots of `P`.
  set S : Finset (ZMod p) := P.roots.toFinset with hS
  have hScard : S.card ≤ 3 := by
    have h1 : S.card ≤ P.roots.card := Multiset.toFinset_card_le _
    have h2 : P.roots.card ≤ P.natDegree := card_roots' P
    omega
  -- Evaluation of the reduced polynomial at a natural number cast.
  have hval : ∀ r : ℕ, P.eval (r : ZMod p) = ((Q.derivative.eval (r : ℤ) : ℤ) : ZMod p) := by
    intro r
    have hcast : (r : ZMod p) = (Int.castRingHom (ZMod p)) (r : ℤ) := by simp
    rw [hcast, hP, eval_map, eval₂_at_apply]
    rfl
  -- `r` lies in the filter precisely when `r mod p` is a root of `P`.
  have hmem : ∀ r : ℕ, r < p → ((p : ℤ) ∣ Q.derivative.eval (r : ℤ) → (r : ZMod p) ∈ S) := by
    intro r _hr hdiv
    rw [hS, Multiset.mem_toFinset, mem_roots hPne, IsRoot.def, hval r,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  set T : Finset ℕ := (Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ Q.derivative.eval (r : ℤ)) with hT
  -- The map `r ↦ r mod p` sends `T` into the root set `S` ...
  have hmaps : Set.MapsTo (fun r : ℕ => (r : ZMod p)) (↑T) (↑S) := by
    intro r hr
    rw [Finset.mem_coe] at hr ⊢
    rw [hT, Finset.mem_filter, Finset.mem_range] at hr
    exact hmem r hr.1 hr.2
  -- ... and is injective on `T` (which consists of integers `< p`).
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) (↑T) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    rw [hT, Finset.mem_filter, Finset.mem_range] at ha hb
    simp only at hab
    have hv : ((a : ZMod p)).val = ((b : ZMod p)).val := by rw [hab]
    rwa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] at hv
  calc T.card ≤ S.card := Finset.card_le_card_of_injOn (fun r : ℕ => (r : ZMod p)) hmaps hinj
    _ ≤ 3 := hScard

end Work.LinnikBurgess
