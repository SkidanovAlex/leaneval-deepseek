/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Small toolbox for the root-tracked Karrass--Magnus--Solitar induction

This module collects the elementary transfers that the assembly of
`Work.OROneRel.kmsRoot_all` needs and that are *not* provided by
`Submission/Work/OROneRel/KMSDefs.lean` (the corresponding copies live in
`Submission/Work/OROneRel/magnus_step_root.lean`, which is not importable while the
`mem_tlHk_iff` clash between `tlBandDescent` and `band_hnnConjMap_injective` is unresolved).

Contents:

* `MagData u l R` -- the raw HNN data of a Magnus step for the root `u`, with the shorter root
  bounded by `R`; together with `kmsRoot_of_magData`, the wrapper that turns it into `KMSRoot u l`
  using the induction hypothesis (`Work.OROneRel.kmsRoot_of_hnn`).
* `kmsRoot_of_conj` -- `KMSRoot` is invariant under conjugating the root.
* `isProperPower_conj_iff`, `not_isProperPower_cyclicReduction` -- proper powers and cyclic
  reduction.
* `eps_conj'` -- the exponent sum is invariant under conjugation.
* `relatorNorm_cyclicReduction_lt` -- the cyclic reduction strictly decreases the relator norm of a
  relator that is not already cyclically reduced.
* `nonTLetters_eq_relatorNorm_of_not_mem` -- if `t` does not occur in `u`, the number of non-`t`
  letters of `u` is the whole length of `u`.
-/
import Mathlib
import Submission.Work.OROneRel.KMSDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_eq_toAdd_sigma
import Submission.Work.OROneRel.presentedGroup_pow_conj_iso
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.nonTLetters_Psi_le

namespace Work.OROneRel.kmsAux.Core

universe u

/-- **Raw HNN data of a Magnus step.**  The one-relator group `⟨α | u ^ l⟩` is an HNN extension of
a one-relator group `⟨β | v ^ l⟩` with the *same* exponent `l`, a root `v` which is not a proper
power and has relator norm `< R`, and the class of `u` is conjugate to the class of `v`.  This is
`Work.OROneRel.HasMagnusDataAt`, copied here so that the assembly does not depend on
`Submission/Work/OROneRel/magnus_step_root.lean`. -/
def MagData {α : Type u} (u : FreeGroup α) (l : ℕ) (R : ℕ) : Prop :=
  ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
    Work.OROneRel.relatorNorm v < R ∧
    ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
      ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
        e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹

/-- **From a Magnus step to the torsion statement.**  If `MagData u l R` holds and every root of
norm `< R` satisfies `KMSRoot · l`, then so does `u`. -/
theorem kmsRoot_of_magData {α : Type u} {u : FreeGroup α} {l R : ℕ} (h : MagData u l R)
    (IH : ∀ {β : Type u} (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v →
      Work.OROneRel.relatorNorm v < R → Work.OROneRel.KMSRoot v l) :
    Work.OROneRel.KMSRoot u l := by
  obtain ⟨β, v, hpp, hlt, A, B, φ, e, c, hc⟩ := h
  exact Work.OROneRel.kmsRoot_of_hnn hc (IH v hpp hlt)

/-- Being a proper power is invariant under conjugation. -/
theorem isProperPower_conj_iff {α : Type u} (c w : FreeGroup α) :
    Work.OROneRel.IsProperPower (c * w * c⁻¹) ↔ Work.OROneRel.IsProperPower w := by
  constructor
  · rintro ⟨z, k, hk, hz⟩
    refine ⟨c⁻¹ * z * c, k, hk, ?_⟩
    have h2 : (c⁻¹ * z * c) ^ k = c⁻¹ * z ^ k * c := by
      simpa using Work.OROneRel.pow_conj_eq c⁻¹ z k
    rw [h2, ← hz]
    group
  · rintro ⟨z, k, hk, hz⟩
    exact ⟨c * z * c⁻¹, k, hk, by rw [hz, Work.OROneRel.pow_conj_eq]⟩

/-- The cyclic reduction of an element that is not a proper power is not a proper power. -/
theorem not_isProperPower_cyclicReduction {α : Type u} {u : FreeGroup α}
    (hu : ¬ Work.OROneRel.IsProperPower u) :
    ¬ Work.OROneRel.IsProperPower (Work.OROneRel.cyclicReduction u) := by
  intro h
  refine hu ?_
  rw [← Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv u]
  exact (isProperPower_conj_iff (Work.OROneRel.cyclicConjugator u)
    (Work.OROneRel.cyclicReduction u)).mpr h

/-- The exponent sum in a letter is invariant under conjugation. -/
theorem eps_conj' {α : Type u} (t : α) (r w : FreeGroup α) :
    Work.OROneRel.eps t (r * w * r⁻¹) = Work.OROneRel.eps t w := by
  have h : (Work.OROneRel.sigma t) (r * w * r⁻¹) = (Work.OROneRel.sigma t) w := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm ((Work.OROneRel.sigma t) r) ((Work.OROneRel.sigma t) w), mul_assoc,
      mul_inv_cancel, mul_one]
  rw [Work.OROneRel.eps_eq_toAdd_sigma, Work.OROneRel.eps_eq_toAdd_sigma, h]

/-- **`KMSRoot` is invariant under conjugating the root.**  If `u` is conjugate to `w` and
`KMSRoot w l` holds, then `KMSRoot u l` holds. -/
theorem kmsRoot_of_conj {α : Type u} {u w : FreeGroup α} {l : ℕ}
    (hc : ∃ c : FreeGroup α, c * w * c⁻¹ = u) (h : Work.OROneRel.KMSRoot w l) :
    Work.OROneRel.KMSRoot u l := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e, he⟩ := Work.OROneRel.presentedGroup_pow_conj_iso u w c l hc
  have hYu : (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u)
      = (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c)
        * (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w)
        * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv]
  have hW : (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w)
      = ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹
        * (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u)
        * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c)) := by
    rw [hYu]
    group
  refine ⟨?_, ?_⟩
  · have h1 : orderOf (e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u))
        = orderOf (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) :=
      Work.OROneRel.orderOf_mulEquiv e _
    rw [← h1, he, hYu, Work.OROneRel.orderOf_conj]
    exact h.1
  · intro g hg
    have hge : IsOfFinOrder (e g) := (Work.OROneRel.isOfFinOrder_mulEquiv_iff e g).mpr hg
    obtain ⟨k, c', hc'⟩ := h.2 (e g) hge
    refine ⟨k, e.symm (c' * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹), ?_⟩
    have hWk : (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w) ^ k
        = ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹
          * (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u) ^ k
          * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c)) := by
      rw [hW]
      simpa using Work.OROneRel.pow_conj_eq
        ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹
        (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u) k
    have key : e g
        = (c' * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹)
          * (e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)) ^ k
          * ((c' * ((PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c))⁻¹))⁻¹ := by
      rw [hc', he, hWk]
      group
    apply e.injective
    simpa [map_mul, map_pow, map_inv] using key

/-- **The cyclic reduction strictly decreases the relator norm** of a relator that is not already
cyclically reduced. -/
theorem relatorNorm_cyclicReduction_lt {α : Type u} {u : FreeGroup α}
    (hcyc : ¬ Work.OROneRel.IsCyclicallyReducedRelator u) :
    Work.OROneRel.relatorNorm (Work.OROneRel.cyclicReduction u) <
      Work.OROneRel.relatorNorm u := by
  classical
  have hconj : FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord u) ≠ [] := by
    intro h
    have h1 := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically (FreeGroup.toWord u)
    rw [h] at h1
    have h1' : FreeGroup.reduceCyclically (FreeGroup.toWord u) = FreeGroup.toWord u := by
      simpa [FreeGroup.invRev_empty] using h1
    have h2 : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
      rw [← h1']
      exact FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
    exact hcyc h2
  have hlen : (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length
      < (FreeGroup.toWord u).length := by
    have h1 := congrArg List.length
      (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically (FreeGroup.toWord u))
    simp only [List.length_append, FreeGroup.invRev_length] at h1
    have h2 : 0 < (FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord u)).length :=
      List.length_pos_of_ne_nil hconj
    omega
  refine lt_of_le_of_lt ?_ hlen
  show FreeGroup.norm (Work.OROneRel.cyclicReduction u) ≤
    (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length
  rw [show Work.OROneRel.cyclicReduction u
      = FreeGroup.mk (FreeGroup.reduceCyclically (FreeGroup.toWord u)) from rfl]
  exact FreeGroup.norm_mk_le

/-- If `t` does not occur in `u`, then every letter of `u` is different from `t`, so the number of
non-`t` letters of `u` is its whole length. -/
theorem nonTLetters_eq_relatorNorm_of_not_mem {α : Type u} {t : α} {u : FreeGroup α}
    (ht : t ∉ Work.OROneRel.relatorLetters u) :
    Work.OROneRel.nonTLetters t u = Work.OROneRel.relatorNorm u := by
  classical
  have h : ∀ p ∈ FreeGroup.toWord u, p.1 ≠ t := by
    rintro ⟨a, b⟩ hp rfl
    exact ht ⟨b, hp⟩
  rw [Work.OROneRel.nonTLetters_eq_nt, Work.OROneRel.nt, Work.OROneRel.relatorNorm,
    FreeGroup.norm, List.length_filter_eq_length_iff]
  intro p hp
  exact decide_eq_true (h p hp)

end Work.OROneRel.kmsAux.Core
