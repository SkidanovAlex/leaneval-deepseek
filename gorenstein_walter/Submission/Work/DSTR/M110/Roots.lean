/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The root subgroups of `PSL(2,q)` on the projective line

This file sets up the vocabulary for the spatiality statement (A6): every automorphism of
`PSL(2,q)` (`q = p^k`, `p` odd, `q ≥ 5`) is conjugation by an element of `PΓL(2,q)`.

The proof runs through the *root subgroups*: the Sylow `p`-subgroups of `PSL(2,q)`, which are
exactly the stabilizers of the points of `ℙ¹(q)` acting sharply transitively on the complement
of that point.  An automorphism `α` permutes the root subgroups, hence induces a permutation
`φ` of `ℙ¹(q)`, and `φ g φ⁻¹ = α g`.

Vocabulary:
* `Pl p k`      : the projective line `ℙ¹(𝔽_{p^k})`;
* `PG p k`      : `PSL(2,p^k)` as the permutation group `↥(pslImage 𝔽_{p^k})`;
* `U0 p k`      : the Sylow `p`-subgroup `U_∞ = {x ↦ x + b}` of translations (fixing `∞`);
* `Stab p k x`  : the stabilizer in `PG p k` of the point `x`;
* `Root p k`    : the type of subgroups of `PG p k` of order `p^k` (the root subgroups),
  with the conjugation and automorphism actions `Root.conj`, `Root.aut`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Conj
import Submission.Work.DSTR.M110.Normalizer.le_pgammaL
import Submission.Work.DSTR.M110.Aut.centralizer
import Submission.Work.DSTR.M110.Aut.pglHomInjective
import Submission.Work.PSL2.Card

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-- The projective line `ℙ¹(𝔽_{p^k})`. -/
abbrev Pl : Type := Work.AUTL2.P1 (GaloisField p k)

/-- `PSL(2,p^k)` as the permutation group `↥(pslImage 𝔽_{p^k})` on `ℙ¹`. -/
abbrev PG : Type := ↥(Work.AUTL2.pslImage (GaloisField p k))

/-- The group `U_∞ = {x ↦ x + b}` of translations, as a subgroup of `PG p k`. -/
noncomputable def U0 : Subgroup (PG p k) :=
  Subgroup.subgroupOf (Work.AUTL2.Normalizer.translSub (GaloisField p k))
    (Work.AUTL2.pslImage (GaloisField p k))

/-- The stabilizer of a point of the projective line in `PG p k`. -/
noncomputable def Stab (x : Pl p k) : Subgroup (PG p k) := MulAction.stabilizer (PG p k) x

/-- The type of root subgroups: the subgroups of `PG p k` of order `p ^ k`. -/
def Root : Type := { H : Subgroup (PG p k) // Nat.card H = p ^ k }

/-- Conjugation of a root subgroup by an element of `PG p k`. -/
noncomputable def Root.conj (g : PG p k) (H : Root p k) : Root p k :=
  ⟨H.1.map (MulAut.conj g).toMonoidHom, by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, H.2]⟩

/-- The image of a root subgroup under an automorphism of `PG p k`. -/
noncomputable def Root.aut (α : MulAut (PG p k)) (H : Root p k) : Root p k :=
  ⟨H.1.map α.toMonoidHom, by
    rw [Subgroup.card_map_of_injective α.injective, H.2]⟩

@[simp] lemma Root.conj_val (g : PG p k) (H : Root p k) :
    (Root.conj p k g H).1 = H.1.map (MulAut.conj g).toMonoidHom := rfl

@[simp] lemma Root.aut_val (α : MulAut (PG p k)) (H : Root p k) :
    (Root.aut p k α H).1 = H.1.map α.toMonoidHom := rfl

lemma mem_U0_iff {g : PG p k} :
    g ∈ U0 p k ↔ (g : Equiv.Perm (Pl p k)) ∈
      Work.AUTL2.Normalizer.translSub (GaloisField p k) :=
  Subgroup.mem_subgroupOf

/-- `U_∞` fixes `∞`. -/
lemma U0_le_stab : U0 p k ≤ Stab p k (∞ : Pl p k) := by
  intro g hg
  rw [Stab, MulAction.mem_stabilizer_iff]
  rw [mem_U0_iff] at hg
  exact Work.AUTL2.Normalizer.mem_translSub_fixes_infty (GaloisField p k) hg

/-- The only point of `ℙ¹` fixed by *every* element of `U_∞` is `∞`. -/
lemma eq_infty_of_U0_fixes (x : Pl p k) (h : ∀ u ∈ U0 p k, u • x = x) : x = ∞ := by
  rcases x with _ | y
  · rfl
  · exfalso
    have hu : (⟨Work.AUTL2.transl (GaloisField p k) 1,
        Work.AUTL2.transl_mem (GaloisField p k) 1⟩ : PG p k) ∈ U0 p k := by
      rw [mem_U0_iff]
      exact Work.AUTL2.Normalizer.transl_mem_translSub (GaloisField p k) 1
    have hfix : Work.AUTL2.transl (GaloisField p k) 1
        ((y : GaloisField p k) : Pl p k) = ((y : GaloisField p k) : Pl p k) := h _ hu
    exact OnePoint.coe_ne_infty y
      (Work.AUTL2.transl_fixed (GaloisField p k) 1 one_ne_zero _ hfix)

/-- `PG p k` acts transitively on `ℙ¹`. -/
lemma exists_smul_eq (x y : Pl p k) : ∃ g : PG p k, g • x = y := by
  obtain ⟨g, hg, hgx⟩ := Work.AUTL2.exists_pslImage_map_to_infty (GaloisField p k) x
  obtain ⟨h, hh, hhy⟩ := Work.AUTL2.exists_pslImage_map_to_infty (GaloisField p k) y
  refine ⟨⟨h, hh⟩⁻¹ * ⟨g, hg⟩, ?_⟩
  have hgx' : (⟨g, hg⟩ : PG p k) • x = ∞ := hgx
  have h2 : (⟨h, hh⟩ : PG p k) • y = ∞ := hhy
  rw [mul_smul, hgx']
  calc (⟨h, hh⟩ : PG p k)⁻¹ • (∞ : Pl p k)
      = (⟨h, hh⟩ : PG p k)⁻¹ • ((⟨h, hh⟩ : PG p k) • y) := by rw [h2]
    _ = y := inv_smul_smul _ y

/-- The orbit of any point of `ℙ¹` under `PG p k` is everything. -/
lemma orbit_eq_univ (x : Pl p k) : MulAction.orbit (PG p k) x = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  rw [MulAction.mem_orbit_iff]
  exact exists_smul_eq p k x y

/-- `|ℙ¹(𝔽_{p^k})| = p^k + 1`. -/
lemma card_Pl (hk : k ≠ 0) : Nat.card (Pl p k) = p ^ k + 1 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Option (GaloisField p k)) = p ^ k + 1
  rw [Fintype.card_option, ← Nat.card_eq_fintype_card, GaloisField.card p k hk]

/-- The order of `U_∞` is `p^k`. -/
theorem card_U0 (hk : k ≠ 0) : Nat.card (U0 p k) = p ^ k := by
  have hinj : Function.Injective (Work.AUTL2.Normalizer.translHom (GaloisField p k)) := by
    intro a b hab
    have h : Work.AUTL2.transl (GaloisField p k) (Multiplicative.toAdd a) =
        Work.AUTL2.transl (GaloisField p k) (Multiplicative.toAdd b) := hab
    exact Multiplicative.toAdd.injective
      (Work.AUTL2.Normalizer.transl_injective (GaloisField p k) h)
  have h1 : Nat.card (U0 p k) =
      Nat.card (Work.AUTL2.Normalizer.translSub (GaloisField p k)) :=
    Nat.card_congr
      { toFun := fun g => ⟨(g.1 : Equiv.Perm (Pl p k)), (mem_U0_iff p k).mp g.2⟩
        invFun := fun u =>
          ⟨⟨u.1, Work.AUTL2.Normalizer.translSub_le_pslImage (GaloisField p k) u.2⟩,
            (mem_U0_iff p k).mpr u.2⟩
        left_inv := fun g => by rfl
        right_inv := fun u => by rfl }
  have h2 : Nat.card (Work.AUTL2.Normalizer.translSub (GaloisField p k)) =
      Nat.card (Multiplicative (GaloisField p k)) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have h3 : Nat.card (Multiplicative (GaloisField p k)) = Nat.card (GaloisField p k) :=
    Nat.card_congr (Multiplicative.toAdd)
  rw [h1, h2, h3, GaloisField.card p k hk]

/-- `2 * |PSL(2,p^k)| = p^k (p^{2k} - 1)`. -/
theorem card_PG (hp : Odd p) (hk : k ≠ 0) :
    2 * Nat.card (PG p k) = p ^ k * (p ^ (2 * k) - 1) := by
  have hpsl : Function.Injective (Work.AUTL2.pslHom (GaloisField p k)) := by
    intro a b h
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (Work.AUTL2.Aut.pglHomInjective (GaloisField p k) h)
  have he : Nat.card (PSL(2, GaloisField p k)) = Nat.card (PG p k) :=
    Nat.card_congr (MonoidHom.ofInjective hpsl).toEquiv
  have h := Work.PSL2.card_PSL2_galoisField p k hp hk
  rw [← he]
  exact h

/-- A subgroup of `Equiv.Perm X` of cardinality `p ^ k` has a fixed point on a finite set `X`
whose cardinality is not divisible by `p`. -/
theorem exists_fixed_point_of_card_prime_pow {X : Type*} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (p k : ℕ) (hp : p.Prime) (hcard : Nat.card H = p ^ k)
    (hdvd : ¬ p ∣ Nat.card X) : ∃ x : X, ∀ g ∈ H, g x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := (IsPGroup.of_card hcard).nonempty_fixed_point_of_prime_not_dvd_card X hdvd
  exact ⟨x, fun g hg => (MulAction.mem_fixedPoints.mp hx) ⟨g, hg⟩⟩

/-- A subgroup of `PSL(2,p^k)` of order `p^k` fixes a point of `ℙ¹`. -/
theorem exists_fixed_point_of_card (hk : k ≠ 0) (H : Subgroup (PG p k))
    (hH : Nat.card H = p ^ k) : ∃ x : Pl p k, ∀ h ∈ H, h • x = x := by
  haveI hHp : IsPGroup p ↥H := IsPGroup.of_card hH
  have hdvd : ¬ p ∣ Nat.card (Pl p k) := by
    rw [card_Pl p k hk]
    intro h
    have hpk : p ∣ p ^ k := dvd_pow_self p hk
    have hsub : p ∣ (p ^ k + 1) - p ^ k := Nat.dvd_sub h hpk
    rw [Nat.add_sub_cancel_left] at hsub
    have h2 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hsub
    have h3 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨x, hx⟩ := hHp.nonempty_fixed_point_of_prime_not_dvd_card (Pl p k) hdvd
  exact ⟨x, fun h hh => (MulAction.mem_fixedPoints.mp hx) ⟨h, hh⟩⟩

end Work.DSTR.M110
