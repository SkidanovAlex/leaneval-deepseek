/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.L2F.L2NormalizesTwoSylowProp`, proved without `Work.AUTL2`

The main declaration of this file is `Work.L2F.Props.L2NormalizesTwoSylowFree`, a fresh proof of
`Work.L2F.L2NormalizesTwoSylowProp` whose entire import closure avoids `Work.AUTL2` (and hence the
`Work.GW2.IsFourGroup` that clashes with the core areas' copies); the only ingredients are the
`AUTL2`-free part of the `L2F` area plus Mathlib.

Implementation note: the `ℙ¹`-model used here is Mathlib's projectivisation `ℙ F (Fin 2 → F)` with
its (Mathlib) action of `PSL(2,F)`, not `Work.AUTL2.P1`.  The route is the one described in
`Props/L2Free/Defs.lean`:

* `Work.L2F.Props.L2Free.exists_conj_eq_pslUnipotent`: every subgroup of order `q = p ^ k` is a
  conjugate of the unipotent subgroup (Sylow conjugacy);
* `Work.L2F.Props.L2Free.pslStab_inf_eq_normalizer` / `normalizer_conj_pslUnipotent`: the normalizer
  of a conjugate of the unipotent subgroup is the stabilizer of the corresponding point;
* `Work.L2F.Props.L2Free.ncard_fixSet_le_two`: a non-identity element of `PSL(2,F)` fixes at most
  two points;
* the assembly (`Work.L2F.Props.ncard_normalizes_le_two_free`, then specialization to
  `GF(p,k)`): `Q ↦ (fixed point of Q)` is injective on the set of subgroups normalized by `Y` and
  lands in the fixed points of any non-identity element of `Y`. -/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Main
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.L2F.PSL.pslSplitTorus_card
import Submission.Work.L2F.PSL.pslHypTorus_card
import Submission.Work.L2F.PSL.normalizer_pslSplitTorus_dihedral
import Submission.Work.L2F.PSL.normalizer_pslHypTorus_dihedral
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.PSL.sylow_psl_dihedral
import Submission.Work.L2F.Semisimple.primeOrderCentralizer
import Submission.Work.L2F.Involution.lift_sq_neg_one
import Submission.Work.L2F.Props.L2Free.Defs
import Submission.Work.L2F.Props.L2Free.pslStab_card
import Submission.Work.L2F.Props.L2Free.ncard_fixSet_le_two
import Submission.Work.L2F.Props.L2Free.exists_conj_eq_pslUnipotent

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

namespace Work.L2F.Props.L2Free

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## The coordinate form of the `SL(2,F)`-action on `F²`

Auxiliary lemmas for the `ℙ¹`-model, kept in their own namespace so that they cannot clash with the
helper lemmas of the sibling files. -/
namespace Aux

/-- The `i`-th coordinate of `A • v` for `A ∈ SL(2,F)`. -/
theorem smul_apply (A : SL(2, F)) (v : Fin 2 → F) (i : Fin 2) :
    (A • v) i = (A : Matrix (Fin 2) (Fin 2) F) i 0 * v 0
      + (A : Matrix (Fin 2) (Fin 2) F) i 1 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The upper unipotent matrix `!![1,b;0,1]` acts on the first coordinate by `v ↦ v + b * w`. -/
theorem unipotent_smul_zero (b : F) (v : Fin 2 → F) :
    (Work.PSL2.unipotent F b • v) 0 = v 0 + b * v 1 := by
  rw [smul_apply F _ v 0, Work.PSL2.coe_unipotent]; simp

/-- The upper unipotent matrix `!![1,b;0,1]` fixes the second coordinate. -/
theorem unipotent_smul_one (b : F) (v : Fin 2 → F) :
    (Work.PSL2.unipotent F b • v) 1 = v 1 := by
  rw [smul_apply F _ v 1, Work.PSL2.coe_unipotent]; simp

/-- `A ∈ SL(2,F)` acts on the basis vector `![1,0]` by its first column. -/
theorem smul_e0 (A : SL(2, F)) :
    A • (![1,0] : Fin 2 → F) = (fun i => (A : Matrix (Fin 2) (Fin 2) F) i 0) := by
  ext i
  rw [smul_apply F A _ i]
  fin_cases i <;> simp

/-- The base point `inf F` is `Projectivization.mk F ![1,0]`. -/
theorem inf_eq : inf F = Projectivization.mk F (![1,0] : Fin 2 → F)
    (by simp [Fin.forall_fin_two]) := rfl

/-! ## Fixed points -/

/-- The only point of `ℙ¹(F)` fixed by every element of the upper unipotent subgroup is `[1:0]`.
The element `π(unipotent 1)` already forces the second coordinate of a representative to vanish. -/
theorem common_fixSet_pslUnipotent (h2 : (2 : F) ≠ 0) :
    {x : P1 F | ∀ q ∈ Work.L2F.pslUnipotent F, q • x = x} = {inf F} := by
  have hle : Work.L2F.pslUnipotent F ≤ pslStab F (inf F) := by
    rw [pslStab_inf_eq_normalizer F h2]; exact Subgroup.le_normalizer
  ext x
  constructor
  · intro hx
    induction x using Projectivization.ind with
    | _ v hv =>
      have hq : Work.PSL2.pslUnipotent F 1 ∈ Work.L2F.pslUnipotent F := by
        rw [Work.L2F.pslUnipotent, Subgroup.mem_map]
        exact ⟨Work.PSL2.unipotent F 1, ⟨Multiplicative.ofAdd (1 : F), rfl⟩, rfl⟩
      have h1 := hx _ hq
      rw [show Work.PSL2.pslUnipotent F 1 = (Work.PSL2.unipotent F 1 : PSL(2, F)) from rfl,
        smul_mk_apply F (Work.PSL2.unipotent F 1) v hv, Projectivization.mk_eq_mk_iff] at h1
      obtain ⟨a, ha⟩ := h1
      have hc1 : ((a : F) - 1) * v 1 = 0 := by
        have h := congrFun ha 1
        rw [unipotent_smul_one F 1 v] at h
        have h' : (a : F) * v 1 = v 1 := by simpa [Units.smul_def, smul_eq_mul] using h
        linear_combination h'
      have hv1 : v 1 = 0 := by
        rcases mul_eq_zero.mp hc1 with h | h
        · have ha1 : (a : F) = 1 := sub_eq_zero.mp h
          have h0 := congrFun ha 0
          rw [unipotent_smul_zero F 1 v] at h0
          have h0' : (a : F) * v 0 = v 0 + 1 * v 1 := by
            simpa [Units.smul_def, smul_eq_mul] using h0
          rw [ha1, one_mul] at h0'
          have hz : v 0 + 0 = v 0 + 1 * v 1 := by rw [add_zero]; exact h0'
          have hv1' : (1 : F) * v 1 = 0 := (add_left_cancel hz).symm
          simpa using hv1'
        · exact h
      have hv0 : v 0 ≠ 0 := by
        intro h0
        exact hv (by ext i; fin_cases i <;> simp [h0, hv1])
      rw [Set.mem_singleton_iff, inf_eq F, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (v 0) hv0, ?_⟩
      ext i
      fin_cases i <;> simp [hv1]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    intro q hq
    exact (mem_pslStab_iff (x := inf F) (g := q)).mp (hle hq)

/-- The fixed points of a conjugate: `x` is fixed by every element of `h Q h⁻¹` exactly when
`h⁻¹ • x` is fixed by every element of `Q`. -/
theorem mem_fix_conj (h : PSL(2, F)) (Q : Subgroup (PSL(2, F))) (x : P1 F) :
    (∀ q ∈ Q.map (MulAut.conj h).toMonoidHom, q • x = x) ↔
      (∀ q ∈ Q, q • (h⁻¹ • x) = h⁻¹ • x) := by
  constructor
  · intro hx q hq
    exact (smul_mem_conj_iff F h q x).mp (hx _ (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro hx q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    exact (smul_mem_conj_iff F h y x).mpr (hx y hy)

/-- The common fixed points of a conjugate of the unipotent subgroup consist only of the image of
`[1:0]`. -/
theorem fix_conj_pslUnipotent (h : PSL(2, F)) (h2 : (2 : F) ≠ 0) :
    {x : P1 F | ∀ q ∈ (Work.L2F.pslUnipotent F).map (MulAut.conj h).toMonoidHom, q • x = x}
      = {h • inf F} := by
  have key : ∀ y : P1 F, (∀ q ∈ Work.L2F.pslUnipotent F, q • y = y) ↔ y = inf F := by
    intro y
    have hc := common_fixSet_pslUnipotent F h2
    rw [Set.ext_iff] at hc
    exact (hc y).trans Set.mem_singleton_iff
  ext x
  rw [Set.mem_ofPred_eq, mem_fix_conj F h (Work.L2F.pslUnipotent F) x,
    key (h⁻¹ • x), Set.mem_singleton_iff]
  constructor
  · intro hx
    calc x = h • (h⁻¹ • x) := by rw [smul_smul, mul_inv_cancel, one_smul]
      _ = h • inf F := by rw [hx]
  · intro hx
    rw [hx, smul_smul, inv_mul_cancel, one_smul]

/-- The normalizer of a conjugate of the unipotent subgroup is the stabilizer of the conjugate
point. -/
theorem normalizer_conj_pslUnipotent (h2 : (2 : F) ≠ 0) (h : PSL(2, F)) :
    Subgroup.normalizer (((Work.L2F.pslUnipotent F).map (MulAut.conj h).toMonoidHom :
        Subgroup (PSL(2, F))) : Set (PSL(2, F))) = pslStab F (h • inf F) := by
  rw [normalizer_map_mulAut, ← pslStab_inf_eq_normalizer F h2, ← pslStab_smul_conj F h (inf F)]

end Aux

end Work.L2F.Props.L2Free

namespace Work.L2F.Props

open Work.L2F.Props.L2Free
open Work.L2F.Props.L2Free.Aux

/-- The general-field form of `L2NormalizesTwoSylowProp`: for a finite field `F` with
`Nat.card F = p ^ k` (`p` an odd prime) and a subgroup `Y` of `PSL(2,F)` of prime order `r ≠ 2`,
`r ≠ p`, the number of subgroups of order `p ^ k` normalized by `Y` is at most `2`.

The subgroups of order `p ^ k` are exactly the conjugates of the unipotent subgroup; each of them
has a unique fixed point on `ℙ¹(F)` (the common fixed points of `Q` are those of the unipotent
subgroup, transported by conjugation), and its normalizer is the stabilizer of that point, of order
`p ^ k (p ^ k - 1) / 2`.  Hence `Q ↦ fixed point` is injective on the set of normalized subgroups
and takes values in the fixed points of any non-identity element of `Y`, of which there are at most
two. -/
theorem ncard_normalizes_le_two_free (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) {p k r : ℕ} [Fact p.Prime] (hp : Odd p)
    (hcardF : Nat.card F = p ^ k) (hrp : r.Prime) (hr2 : r ≠ 2) (hrnp : r ≠ p)
    (Y : Subgroup (PSL(2, F))) (hY : Nat.card Y = r) :
    {Q : Subgroup (PSL(2, F)) | Nat.card Q = p ^ k ∧
        Y ≤ Subgroup.normalizer (Q : Set (PSL(2, F)))}.ncard ≤ 2 := by
  classical
  -- a non-identity element of `Y`
  have hne : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hrp.ne_one hY.symm
  obtain ⟨⟨g, hgY⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  -- arithmetic side conditions
  have hk : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk0', pow_zero, Nat.card_eq_fintype_card] at hcardF
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have h2dvd : 2 ∣ p ^ k - 1 := by
    obtain ⟨m, hm⟩ := hp.pow
    exact ⟨m, by rw [hm, Nat.add_sub_cancel]⟩
  have hpndvd : ¬ p ∣ p ^ k - 1 := by
    intro hdvd
    have hpdvd : p ∣ p ^ k := dvd_pow_self p hk.ne'
    have hsub : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub hpdvd hdvd
    have h1 : p ^ k - (p ^ k - 1) = 1 := by have := pow_pos (Fact.out : p.Prime).pos k; omega
    rw [h1] at hsub
    exact (Fact.out : p.Prime).not_dvd_one hsub
  have hnotdvd : ¬ p ∣ (p ^ k - 1) / 2 := by
    intro hdvd
    apply hpndvd
    rw [← Nat.mul_div_cancel' h2dvd]
    exact dvd_mul_of_dvd_right hdvd 2
  -- the conjugating element and the fixed point attached to a subgroup of order `p ^ k`
  let cnj : (Q : Subgroup (PSL(2, F))) → Nat.card Q = p ^ k → PSL(2, F) := fun Q hQ =>
    Classical.choose (exists_conj_eq_pslUnipotent F h2 p k hp hcardF Q hQ)
  have hcnj : ∀ (Q : Subgroup (PSL(2, F))) (hQ : Nat.card Q = p ^ k),
      Q = (Work.L2F.pslUnipotent F).map (MulAut.conj (cnj Q hQ)).toMonoidHom := fun Q hQ =>
    Classical.choose_spec (exists_conj_eq_pslUnipotent F h2 p k hp hcardF Q hQ)
  let pt : Subgroup (PSL(2, F)) → P1 F := fun Q =>
    if hQ : Nat.card Q = p ^ k then cnj Q hQ • inf F else inf F
  have hpt : ∀ (Q : Subgroup (PSL(2, F))) (hQ : Nat.card Q = p ^ k),
      pt Q = cnj Q hQ • inf F := by
    intro Q hQ
    simp only [pt, dif_pos hQ]
  have hN : ∀ (Q : Subgroup (PSL(2, F))) (hQ : Nat.card Q = p ^ k),
      Subgroup.normalizer (Q : Set (PSL(2, F))) = pslStab F (pt Q) := by
    intro Q hQ
    have hA : Subgroup.normalizer (Q : Set (PSL(2, F))) =
        Subgroup.normalizer (((Work.L2F.pslUnipotent F).map (MulAut.conj (cnj Q hQ)).toMonoidHom :
          Subgroup (PSL(2, F))) : Set (PSL(2, F))) :=
      congrArg (fun H : Subgroup (PSL(2, F)) => Subgroup.normalizer (H : Set (PSL(2, F))))
        (hcnj Q hQ)
    rw [hA, normalizer_conj_pslUnipotent F h2 (cnj Q hQ), hpt Q hQ]
  have hfix : ∀ (Q : Subgroup (PSL(2, F))) (hQ : Nat.card Q = p ^ k),
      {x : P1 F | ∀ q ∈ Q, q • x = x} = {pt Q} := by
    intro Q hQ
    conv_lhs => rw [hcnj Q hQ]
    rw [fix_conj_pslUnipotent F (cnj Q hQ) h2, hpt Q hQ]
  have hmem_fix : ∀ (Q : Subgroup (PSL(2, F))) (hQ : Nat.card Q = p ^ k) (q : PSL(2, F)),
      q ∈ Q → q • pt Q = pt Q := by
    intro Q hQ q hq
    have h1 : pt Q ∈ {x : P1 F | ∀ q ∈ Q, q • x = x} := by
      rw [hfix Q hQ]
      exact Set.mem_singleton _
    exact h1 q hq
  -- the cardinality of a point stabilizer, in the form needed below
  have hNcard : ∀ x : P1 F, Nat.card (pslStab F x) = p ^ k * ((p ^ k - 1) / 2) := by
    intro x
    have h := pslStab_card F h2 x
    rw [hcardF] at h
    have hX : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := Nat.mul_div_cancel' h2dvd
    have h4 : p ^ k * (p ^ k - 1) = 2 * (p ^ k * ((p ^ k - 1) / 2)) := by
      calc p ^ k * (p ^ k - 1) = p ^ k * (2 * ((p ^ k - 1) / 2)) := by rw [hX]
        _ = 2 * (p ^ k * ((p ^ k - 1) / 2)) := by ring
    have hmain : 2 * Nat.card (pslStab F x) = 2 * (p ^ k * ((p ^ k - 1) / 2)) := by rw [h, h4]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmain
  -- the map on the set of normalized subgroups, and its injectivity
  have hinj : Set.InjOn pt {Q : Subgroup (PSL(2, F)) | Nat.card Q = p ^ k ∧
      Y ≤ Subgroup.normalizer (Q : Set (PSL(2, F)))} := by
    intro Q hQ Q' hQ' hpq
    have hleQ : Q ≤ pslStab F (pt Q) := by
      intro q hq
      rw [mem_pslStab_iff]
      exact hmem_fix Q hQ.1 q hq
    have hleQ' : Q' ≤ pslStab F (pt Q) := by
      intro q hq
      rw [mem_pslStab_iff, hpq]
      exact hmem_fix Q' hQ'.1 q hq
    have hnorm : pslStab F (pt Q) ≤ Subgroup.normalizer (Q : Set (PSL(2, F))) :=
      le_of_eq (hN Q hQ.1).symm
    exact (eq_of_normal_card_eq (G := PSL(2, F)) (p := p) (m := k) (c := (p ^ k - 1) / 2)
      (P := Q) (Q := Q') (N := pslStab F (pt Q)) hleQ hleQ' hnorm hQ.1 hQ'.1
      (hNcard (pt Q)) hnotdvd).symm
  have hf : ∀ Q ∈ {Q : Subgroup (PSL(2, F)) | Nat.card Q = p ^ k ∧
      Y ≤ Subgroup.normalizer (Q : Set (PSL(2, F)))}, pt Q ∈ fixSet F g := by
    intro Q hQ
    rw [mem_fixSet_iff]
    have hgN : g ∈ Subgroup.normalizer (Q : Set (PSL(2, F))) := hQ.2 hgY
    have : g ∈ pslStab F (pt Q) := by rw [← hN Q hQ.1]; exact hgN
    exact (mem_pslStab_iff (x := pt Q) (g := g)).mp this
  exact le_trans (Set.ncard_le_ncard_of_injOn (s := {Q : Subgroup (PSL(2, F)) |
      Nat.card Q = p ^ k ∧ Y ≤ Subgroup.normalizer (Q : Set (PSL(2, F)))})
      (t := fixSet F g) pt hf hinj)
    (ncard_fixSet_le_two F h2 g hg1')

/-- A fresh, `Work.AUTL2`-free proof of `Work.L2F.L2NormalizesTwoSylowProp` (an odd prime `r ≠ p`
subgroup `Y` normalizes at most two subgroups of order `q` in `L₂(q)`), so that the result can be
imported next to `Work.CORE4.Defs` (the existing proof goes through `Props/TwoSylow/Defs`, which
imports `Work.AUTL2`, whose `Work.GW2.IsFourGroup` clashes with the core areas' copies).
Plan (no `ℙ¹` needed; every step below has a module in the dependency list):
* a subgroup `Q` of order `q` is a Sylow `p`-subgroup of `L₂(q)` (`q` is the full `p`-part of
  `q(q²-1)/2`), so by Sylow conjugacy `Q = pslUnipotentᵍ` for some `g`, hence
  `N(Q) = pslBorelᵍ` has order `q(q-1)/2` and its `p`-part is `Q`
  (`PSL.normalizer_pslUnipotent_card`, and the map `Q ↦ N(Q)` is injective on order-`q` subgroups
  because `Q` is the `p`-part of its own normalizer);
* `Y ≤ N(Q)` with `|Y| = r` prime and `r ∤ q` (from `r ≠ p`) gives `Y ∩ O_p(N(Q)) = 1`, so `Y` lies
  in the torus part of the Borel; hence the Borels containing `Y` are exactly the Borels containing
  the torus `C(Y)` (cyclic of order `(q±1)/2`, `Semisimple.primeOrderCentralizer`);
* a maximal torus lies in exactly two Borels (`N(T)/T ≅ C₂`; the split case is
  `PSL.normalizer_pslSplitTorus_dihedral`/`PSL.centralizer_psl_dihedral`), so at most two such `Q`. -/
theorem L2NormalizesTwoSylowFree : Work.L2F.L2NormalizesTwoSylowProp := by
  intro p k hpFact hp hk r hrprime hr2 hrp Y hYcard
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p k) := Classical.decEq _
  exact ncard_normalizes_le_two_free (GaloisField p k) (Work.L2F.two_ne_zero_galois hp) hp
    (Work.L2F.card_galois hk) hrprime hr2 hrp Y hYcard

end Work.L2F.Props
