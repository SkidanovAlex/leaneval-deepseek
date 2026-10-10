import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.extH_classesK_two_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open CategoryTheory

/-- **A finite additive group has no element of order `p` when `p` does not divide its order.**
(Lagrange: the order of an element divides the order of the group.)  This is the abstract content
of the case distinction `p ∤ [K:k]` of the `G5` assembly. -/
lemma eq_zero_of_nsmul_eq_zero_of_not_dvd_natCard (p : ℕ) [Fact p.Prime]
    (A : Type) [AddCommGroup A] (h : ¬ p ∣ Nat.card A) :
    ∀ v : A, p • v = 0 → v = 0 := by
  intro v hv
  have hdvd : addOrderOf v ∣ p := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hv
  have hdvd2 : addOrderOf v ∣ Nat.card A := addOrderOf_dvd_natCard v
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (addOrderOf v) hdvd with h1 | hp
  · exact AddMonoid.addOrderOf_eq_one_iff.mp h1
  · exact absurd (hp ▸ hdvd2) h

/-- **`H²(Gal(K/k), C_K)` is `p`-torsion-free when `p ∤ [K:k]`.**  The class formation computes the
order of `H²(Gal(K/k), C_K) = SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k K) 2` as `[K:k]` (via
the order computation already carried out inside the proved `Work.SSGRoute.pt_char_pTorsion`), so
when `p ∤ [K:k]` it has no element of order `p`, hence no nonzero `p`-torsion.  This is the case
distinction of the `G5` assembly: the Poitou–Tate pairing values are `p`-torsion, so they are
automatically zero in this case. -/
lemma no_pTorsion_extH_classesK_two (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (hp : ¬ p ∣ Module.finrank k K) :
    ∀ v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k K) 2, p • v = 0 → v = 0 := by
  -- the order of `H²(Gal(K/k), C_K)` is `|Gal(K/k)| = [K:k]`.
  have hcardA : Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k K) 2)
      = Nat.card (K ≃ₐ[k] K) := Work.SSGRoute.extH_classesK_two_card k K
  have hfr : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have hnot : ¬ p ∣ Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k K) 2) := by
    rw [hcardA, hfr]
    exact hp
  exact eq_zero_of_nsmul_eq_zero_of_not_dvd_natCard p _ hnot

end Work.SSGRoute.PTembedding
