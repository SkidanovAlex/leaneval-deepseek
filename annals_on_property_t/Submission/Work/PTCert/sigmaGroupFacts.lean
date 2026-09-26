import Mathlib
import Submission.Work.PTCert.Interfaces

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`sigAut p s = signAut s * permAut p`
(`permAut`: Submission/Work/RouteB/PermAction.lean, `a_k ↦ a_{p k}`; `sigma k`:
Submission/FreeGroupAut.lean, `a_k ↦ a_k⁻¹`, other generators fixed).

This file proves `SigmaGroupFacts r` for every `r`: `SigmaSet r` (the signed permutations) and
`SignSet r` (the sign flips) are finite subgroups of `Aut(F_r)`, and `SignSet r ⊆ SigmaSet r`.

The engine is the value of `signAut`/`sigAut` on a free generator:
`signAut s (of k) = if s k then (of k)⁻¹ else of k`,
`sigAut p s (of k) = if s (p k) then (of (p k))⁻¹ else of (p k)`,
together with the multiplication/inversion formulas derived from it by checking on generators
(`Submission.RouteB.mulAut_eq_iff`).
-/

namespace Work.PTCert

open Submission.PTCert

namespace SigmaFacts

variable {r : ℕ}

/-- `sigma i` sends the generator `of k` either to itself or to its inverse. -/
lemma sigma_of (i k : Fin r) :
    Submission.FreeGroupAut.sigma i (FreeGroup.of k)
      = if k = i then (FreeGroup.of k)⁻¹ else FreeGroup.of k := by
  by_cases h : k = i
  · subst h
    rw [if_pos rfl, Submission.FreeGroupAut.sigma_apply_self]
  · rw [if_neg h, Submission.FreeGroupAut.sigma_apply_other h]

/-- A product of single-generator inversions, applied to a generator: the generators inverted
in the list `L` are sent to their inverses, the others are fixed. -/
lemma prod_map_sigma_of (L : List (Fin r)) (hL : L.Nodup) (k : Fin r) :
    (L.map (fun i => Submission.FreeGroupAut.sigma i)).prod (FreeGroup.of k)
      = if k ∈ L then (FreeGroup.of k)⁻¹ else FreeGroup.of k := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hiL, hLnodup⟩ := hL
    rw [List.map_cons, List.prod_cons]
    show Submission.FreeGroupAut.sigma i
        ((L.map (fun i => Submission.FreeGroupAut.sigma i)).prod (FreeGroup.of k)) = _
    rw [ih hLnodup]
    by_cases hmem : k ∈ L
    · have hne : k ≠ i := fun h => hiL (h ▸ hmem)
      rw [if_pos hmem, if_pos (List.mem_cons_of_mem i hmem)]
      rw [show Submission.FreeGroupAut.sigma i ((FreeGroup.of k)⁻¹) = (FreeGroup.of k)⁻¹ by
        rw [map_inv, sigma_of i k, if_neg hne]]
    · rw [if_neg hmem, sigma_of i k]
      by_cases h2 : k = i
      · subst h2; simp
      · rw [if_neg h2, if_neg (by simp [h2, hmem])]

/-- **Value of a sign flip on a generator.** -/
lemma signAut_apply (s : Fin r → Bool) (k : Fin r) :
    signAut s (FreeGroup.of k) = if s k then (FreeGroup.of k)⁻¹ else FreeGroup.of k := by
  rw [signAut]
  rw [prod_map_sigma_of _ ((List.nodup_finRange r).filter (fun k => s k)) k]
  have hmem : k ∈ (List.finRange r).filter (fun k => s k) ↔ s k = true := by
    rw [List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange k, h⟩⟩
  by_cases hs : s k
  · rw [if_pos (hmem.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hmem.mp h)), if_neg hs]

/-- Sign flips multiply by pointwise `xor` of the sign functions. -/
lemma signAut_mul (s s' : Fin r → Bool) :
    signAut s * signAut s' = signAut (fun k => s k ^^ s' k) := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  rw [show (signAut s * signAut s') (FreeGroup.of k)
      = signAut s (signAut s' (FreeGroup.of k)) from rfl]
  rw [show (signAut (fun k => s k ^^ s' k)) (FreeGroup.of k)
        = if (s k ^^ s' k) then (FreeGroup.of k)⁻¹ else FreeGroup.of k from
      signAut_apply (fun k => s k ^^ s' k) k]
  rw [signAut_apply s' k]
  by_cases h : s' k = true
  · rw [if_pos h, map_inv, signAut_apply s k]
    by_cases h2 : s k = true
    · rw [if_pos h2, if_neg (by simp [h, h2])]; simp
    · rw [if_neg h2, if_pos (by simp [h, h2])]
  · rw [if_neg h, signAut_apply s k]
    by_cases h2 : s k = true
    · rw [if_pos h2, if_pos (by simp [h, h2])]
    · rw [if_neg h2, if_neg (by simp [h, h2])]

/-- The trivial sign flip is the identity. -/
lemma signAut_one : signAut (fun _ : Fin r => false) = 1 := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  rw [show (1 : MulAut (FreeGroup (Fin r))) (FreeGroup.of k) = FreeGroup.of k from rfl]
  rw [signAut_apply]; simp

/-- Every sign flip is an involution. -/
lemma signAut_inv (s : Fin r → Bool) : (signAut s)⁻¹ = signAut s := by
  have h : signAut s * signAut s = 1 := by
    rw [signAut_mul,
      show (fun k => s k ^^ s k) = (fun _ : Fin r => false) from by funext k; simp,
      signAut_one]
  exact inv_eq_of_mul_eq_one_right h

/-- **Value of a signed permutation on a generator.** -/
lemma sigAut_apply (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) (k : Fin r) :
    sigAut p s (FreeGroup.of k)
      = if s (p k) then (FreeGroup.of (p k))⁻¹ else FreeGroup.of (p k) := by
  rw [sigAut]
  show signAut s (Submission.RouteB.permAut p (FreeGroup.of k)) = _
  rw [Submission.RouteB.permAut_apply, signAut_apply]

/-- The trivial signed permutation is the identity. -/
lemma sigAut_one : sigAut (1 : Equiv.Perm (Fin r)) (fun _ : Fin r => false) = 1 := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  rw [show (1 : MulAut (FreeGroup (Fin r))) (FreeGroup.of k) = FreeGroup.of k from rfl]
  rw [sigAut_apply]; simp

/-- Signed permutations multiply by multiplication of the permutations and `xor` of the sign
functions (the second sign function being pulled back along `p`). -/
lemma sigAut_mul (p : Equiv.Perm (Fin r)) (s : Fin r → Bool)
    (p' : Equiv.Perm (Fin r)) (s' : Fin r → Bool) :
    sigAut p s * sigAut p' s' = sigAut (p * p') (fun k => s k ^^ s' (p.symm k)) := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  rw [show (sigAut p s * sigAut p' s') (FreeGroup.of k)
      = sigAut p s (sigAut p' s' (FreeGroup.of k)) from rfl]
  rw [sigAut_apply p' s' k,
      sigAut_apply (p * p') (fun k => s k ^^ s' (p.symm k)) k,
      Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  by_cases h : s' (p' k) = true
  · rw [if_pos h, map_inv, sigAut_apply p s (p' k)]
    by_cases ha : s (p (p' k)) = true
    · rw [if_pos ha, if_neg (by simp [h, ha])]; simp
    · rw [if_neg ha, if_pos (by simp [h, ha])]
  · rw [if_neg h, sigAut_apply p s (p' k)]
    by_cases ha : s (p (p' k)) = true
    · rw [if_pos ha, if_pos (by simp [h, ha])]
    · rw [if_neg ha, if_neg (by simp [h, ha])]

/-- Inversion of a signed permutation. -/
lemma sigAut_inv (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) :
    (sigAut p s)⁻¹ = sigAut p.symm (fun q => s (p q)) := by
  have h : sigAut p s * sigAut p.symm (fun q => s (p q)) = 1 := by
    rw [sigAut_mul,
      show (p * p.symm) = 1 from by ext k; simp,
      show (fun k => s k ^^ (fun q => s (p q)) (p.symm k)) = (fun _ : Fin r => false) from by
        funext k; simp [Equiv.apply_symm_apply],
      sigAut_one]
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- Membership in `SignSet r`, unfolded. -/
lemma mem_SignSet_iff {g : MulAut (FreeGroup (Fin r))} :
    g ∈ SignSet r ↔ ∃ s : Fin r → Bool, signAut s = g := by
  classical
  rw [SignSet, Finset.mem_image]
  exact ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, Finset.mem_univ s, h⟩⟩

/-- Membership in `SigmaSet r`, unfolded. -/
lemma mem_SigmaSet_iff {g : MulAut (FreeGroup (Fin r))} :
    g ∈ SigmaSet r ↔ ∃ (p : Equiv.Perm (Fin r)) (s : Fin r → Bool), sigAut p s = g := by
  classical
  rw [SigmaSet, Finset.mem_image]
  exact ⟨fun ⟨⟨p, s⟩, _, h⟩ => ⟨p, s, h⟩, fun ⟨p, s, h⟩ => ⟨(p, s), Finset.mem_univ _, h⟩⟩

end SigmaFacts

open SigmaFacts

/-- **(S1)** `SigmaSet r` and `SignSet r` are finite subgroups of `Aut(F_r)`, and
`SignSet r ⊆ SigmaSet r`. -/
theorem sigmaGroupFacts (r : ℕ) : SigmaGroupFacts r := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mem_SigmaSet_iff]; exact ⟨1, fun _ => false, sigAut_one⟩
  · intro g hg h hh
    rw [mem_SigmaSet_iff] at hg hh
    obtain ⟨p, s, rfl⟩ := hg
    obtain ⟨p', s', rfl⟩ := hh
    rw [mem_SigmaSet_iff]
    exact ⟨p * p', fun k => s k ^^ s' (p.symm k), (sigAut_mul p s p' s').symm⟩
  · intro g hg
    rw [mem_SigmaSet_iff] at hg
    obtain ⟨p, s, rfl⟩ := hg
    rw [mem_SigmaSet_iff]
    exact ⟨p.symm, fun q => s (p q), (sigAut_inv p s).symm⟩
  · rw [mem_SignSet_iff]; exact ⟨fun _ => false, signAut_one⟩
  · intro g hg h hh
    rw [mem_SignSet_iff] at hg hh
    obtain ⟨s, rfl⟩ := hg
    obtain ⟨s', rfl⟩ := hh
    rw [mem_SignSet_iff]
    exact ⟨fun k => s k ^^ s' k, (signAut_mul s s').symm⟩
  · intro g hg
    rw [mem_SignSet_iff] at hg
    obtain ⟨s, rfl⟩ := hg
    rw [mem_SignSet_iff]
    exact ⟨s, (signAut_inv s).symm⟩
  · intro g hg
    rw [mem_SignSet_iff] at hg
    obtain ⟨s, rfl⟩ := hg
    rw [mem_SigmaSet_iff]
    exact ⟨1, s, by rw [sigAut, Submission.RouteB.permAut_one, mul_one]⟩

end Work.PTCert
