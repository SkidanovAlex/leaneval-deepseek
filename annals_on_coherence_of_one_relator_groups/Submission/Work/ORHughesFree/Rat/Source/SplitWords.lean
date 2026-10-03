import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.Structural
import Submission.Work.ORHughesFree.Rat.Weak.Attain
import Submission.Work.ORHughesFree.Rat.Weak.Assembly
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.OrbitF
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_list
import Submission.Work.ORHughesFree.Rat.listProd_Xgen_eq_mk
import Submission.Work.ORHughesFree.Rat.A_ratOp
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff
import Submission.Work.ORHughesFree.Rat.mem_A_mul_ofGroup_iff
import Submission.Work.ORHughesFree.Rat.Psi_mem_A_iff

/-!
# `Splitting` of products (a private copy of the Src-free part of `Rat/Src/exists_Asource.lean`)

This module contains the splitting lemma `split_NU` and the `⋃`-decomposition
`Source.SW.hsplit_words` of the `Rat.A`-family of a product of two words, copied from
`Rat/Src/exists_Asource.lean` but *without* the import of `Rat/Src/exists_inP_mul_ofGroup` (which
imports `Rat/source_subgroup_exists`, whence an import cycle) and without the target statement
`exists_Asource` of that file (its proof is irrelevant here).  The mathematics is unchanged.
-/
/-!
# The source subgroup of an element of `Rat(U)` for the one-sided family `Rat.A`

[JZLA20, Proposition 4.4] / [DHS04, Theorem 5.7] attach to each `α ∈ Rat(U)` the *least* subgroup
`V ≤ U` with `α ∈ Rat(V)·U`.  This file proves the corresponding statement for the *one-sided*
family `Rat.A`: for every `y : RatU U` the family

  `Rat.Weak.FA y = {V ≤ U | y ∈ Rat.A V}`

has a least element.

## Structure of the proof

`Rat.Weak.FA y` is determined by the words in the support of `Psi y` (`Rat.Weak.mem_FA_iff_words`),
and the family of a word `w ∈ U ♮ X` is computed by a first-letter recursion
(`Rat.Xgen_mem_closure_iff`) along the *split* of `w` at a group letter:

  `u * v ∈ NUV V  →  ∃ w : U, u * Ugen w ∈ NUV V ∧ Ugen w⁻¹ * v ∈ NUV V`

(`split_NU` below, an induction on the number of `X`-letters of `u`).  This is the key input of the
`⋃`-decomposition of `Rat.A`-families of products (`Rat.Weak.FA_mul_splitting` is the easy half)
and hence of the induction on `Rat.treeOfRat` that proves the theorem.

-/

namespace Work.ORHughesFree.Rat.Source.SW

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-! ## The number of `X`-letters and the first-letter decomposition -/

/-- The number of `X`-letters of an element of `U ♮ X`. -/
noncomputable def xlen : NU U → ℕ
  | Sum.inl _ => 0
  | Sum.inr L =>
      Quotient.lift (fun l : NEL (U := U) => l.1.length)
        (fun _ _ h => FreeProduct.relNE_len h) L

theorem xlen_mk (L : NEL (U := U)) : xlen (Sum.inr (Quotient.mk _ L) : NU U) = L.1.length := rfl

@[simp] theorem xlen_ugen (t : U) : xlen (NU.Ugen t) = 0 := rfl

theorem xlen_Ugen_mul (t : U) (q : NU U) : xlen (NU.Ugen t * q) = xlen q := by
  rcases q with u | L
  · rfl
  · refine Quotient.inductionOn L ?_
    intro l
    rw [NU.Ugen_mul_mk, xlen_mk, xlen_mk]
    exact mulFirst_length t l.1

theorem xlen_Xgen_mul (a : RatU U) (q : NU U) : xlen (NU.Xgen a * q) = xlen q + 1 := by
  rcases q with u | L
  · rw [NU.Xgen_mul_Ugen]
    show xlen (NU.Xgen (actR u a)) = 0 + 1
    rw [show xlen (NU.Xgen (actR u a)) = 1 from xlen_mk (⟨[actR u a], by simp⟩ : NEL (U := U))]
  · refine Quotient.inductionOn L ?_
    intro l
    rw [NU.Xgen_mul_mk, xlen_mk, xlen_mk]
    simp

theorem one_le_xlen_of_xpart (L : XPart U) : 1 ≤ xlen (Sum.inr L) := by
  refine Quotient.inductionOn L ?_
  intro l
  rw [xlen_mk]
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil l.2
  rw [ht]
  simp

/-- Every element of `U ♮ X` with at least one `X`-letter can be written as `Xgen a * q`. -/
theorem exists_xgen_decomp (u : NU U) (h : 1 ≤ xlen u) :
    ∃ (a : RatU U) (q : NU U), u = NU.Xgen a * q := by
  rcases u with t | L
  · simp [xlen] at h
  · refine Quotient.inductionOn L ?_
    intro l
    obtain ⟨a, rest, hl⟩ := List.exists_cons_of_ne_nil l.2
    refine ⟨a, (rest.map NU.Xgen).prod, ?_⟩
    have h1 : (Sum.inr (Quotient.mk _ l) : NU U) = (l.1.map NU.Xgen).prod :=
      (listProd_Xgen_eq_mk l.1 l.2).symm
    rw [h1, hl, List.map_cons, List.prod_cons]

/-! ## The splitting lemma -/

/-- **The splitting lemma.**  If a product of two elements of `U ♮ X` lies in the `V`-part, then
the first factor can be completed by a single group letter `Ugen w` and simultaneously the second
factor can be *prefixed* by `Ugen w⁻¹`. -/
theorem split_NU (V : Subgroup U) (u v : NU U) (hv : u * v ∈ Orbit.NUV V) :
    ∃ w : U, u * NU.Ugen w ∈ Orbit.NUV V ∧ NU.Ugen w⁻¹ * v ∈ Orbit.NUV V := by
  suffices H : ∀ n, ∀ (u : NU U), xlen u ≤ n → ∀ v : NU U, u * v ∈ Orbit.NUV V →
      ∃ w : U, u * NU.Ugen w ∈ Orbit.NUV V ∧ NU.Ugen w⁻¹ * v ∈ Orbit.NUV V by
    exact H (xlen u) u le_rfl v hv
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u hn v hv
    by_cases h0 : xlen u = 0
    · -- `u` is a group letter
      obtain ⟨t, rfl⟩ : ∃ t : U, u = NU.Ugen t := by
        rcases u with t | L
        · exact ⟨t, rfl⟩
        · exact absurd h0 (by have := one_le_xlen_of_xpart L; omega)
      refine ⟨t⁻¹, ?_, ?_⟩
      · rw [NU.Ugen_mul, mul_inv_cancel]
        exact (Orbit.NUV V).one_mem
      · rw [inv_inv]
        exact hv
    · -- `u = Xgen a * q` with a shorter `q`
      obtain ⟨a, q, rfl⟩ := exists_xgen_decomp u (by omega)
      rw [mul_assoc] at hv
      obtain ⟨y, hy1, hy2⟩ := (Xgen_mem_closure_iff V a (q * v)).mp hv
      rw [← mul_assoc] at hy2
      have hlt : xlen (NU.Ugen y⁻¹ * q) < n := by
        rw [xlen_Ugen_mul]
        have := xlen_Xgen_mul a q
        omega
      obtain ⟨w, hw1, hw2⟩ := ih (xlen (NU.Ugen y⁻¹ * q)) hlt (NU.Ugen y⁻¹ * q) le_rfl v hy2
      refine ⟨w, ?_, hw2⟩
      rw [mul_assoc]
      exact (Xgen_mem_closure_iff V a (q * NU.Ugen w)).mpr
        ⟨y, hy1, by rw [← mul_assoc]; exact hw1⟩

/-! ## The `⋃`-decomposition of the `Rat.A`-family of a product of words -/

theorem supp_single_one (p : NU U) :
    (MonoidAlgebra.single p (1 : ℕ) : S2 U).coeff.support = {p} := by
  ext r
  constructor
  · intro hr
    exact Finsupp.support_single_subset hr
  · intro hr
    rw [Finset.mem_singleton] at hr
    subst hr
    rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_single]
    simp

/-- A word of `Rat(U)` is the value of a word of the word model. -/
theorem IsWord.exists_mval_sw {x : RatU U} (hx : RatU.IsWord x) :
    ∃ m : WordModel.Mword U, WordModel.Mval m = x := by
  induction hx with
  | ofGroup u => exact ⟨WordModel.Mu u, WordModel.Mval_Mu u⟩
  | mul hx hy ihx ihy =>
      obtain ⟨m, hm⟩ := ihx
      obtain ⟨m', hm'⟩ := ihy
      exact ⟨m * m', by rw [WordModel.Mval_mul, hm, hm']⟩
  | rat x hx =>
      refine ⟨WordModel.letterOf (WordModel.rho x), ?_⟩
      rw [WordModel.letterOf_val, WordModel.sumVal_toList, ← WordModel.sigma_apply,
        WordModel.sigma_rho]
      exact Rat.ratOp_eq_rational x

/-- The `Psi`-image of a word of `Rat(U)` is a single monomial. -/
theorem IsWord.exists_mval_sw_supp_sw {x : RatU U} (hx : RatU.IsWord x) :
    ∃ m : WordModel.Mword U, WordModel.Mval m = x ∧
      FreeProduct.Psi x = MonoidAlgebra.single (FreeProduct.nrm m) 1 := by
  obtain ⟨m, hm⟩ := IsWord.exists_mval_sw hx
  refine ⟨m, hm, ?_⟩
  rw [← hm]
  exact FreeProduct.Psi_Mval (by rw [hm]; exact RatU.isWord_ne_zero' hx)

/-- **The `⋃`-decomposition of the `Rat.A`-family of a product of two words.** -/
theorem hsplit_words {a b : RatU U} (ha : RatU.IsWord a) (hb : RatU.IsWord b) :
    Weak.FA (a * b) =
      ⋃ x : U, (Weak.FA (a * RatU.ofGroup x) ∩ Weak.FA (RatU.ofGroup x⁻¹ * b)) := by
  obtain ⟨m, hm, hPsia⟩ := IsWord.exists_mval_sw_supp_sw ha
  obtain ⟨m', hm', hPsib⟩ := IsWord.exists_mval_sw_supp_sw hb
  have hm0 : WordModel.Mval m ≠ 0 := by rw [hm]; exact RatU.isWord_ne_zero' ha
  have hm0' : WordModel.Mval m' ≠ 0 := by rw [hm']; exact RatU.isWord_ne_zero' hb
  have hnrm : FreeProduct.nrm (m * m') = FreeProduct.nrm m * FreeProduct.nrm m' :=
    FreeProduct.nrm_mul hm0 hm0'
  ext V
  rw [Weak.FA, Set.mem_iUnion]
  constructor
  · intro hV
    have hmemA : WordModel.Mval (m * m') ∈ Rat.A V := by
      rw [WordModel.Mval_mul, hm, hm']; exact hV
    have hne : WordModel.Mval (m * m') ≠ 0 := by
      rw [WordModel.Mval_mul, hm, hm']
      exact RatU.isWord_ne_zero' (RatU.IsWord.mul ha hb)
    have hsupp : ∀ p ∈ (FreeProduct.Psi (WordModel.Mval (m * m'))).coeff.support,
        p ∈ Orbit.NUV V :=
      (Psi_mem_A_iff V _).mp ((Rat.mem_A_iff_exists V _).mp hmemA)
    have hkey : FreeProduct.nrm m * FreeProduct.nrm m' ∈ Orbit.NUV V := by
      have h := hsupp (FreeProduct.nrm (m * m'))
        (by rw [FreeProduct.Psi_Mval hne, supp_single_one]; exact Finset.mem_singleton_self _)
      rwa [hnrm] at h
    obtain ⟨w, hw1, hw2⟩ := split_NU V (FreeProduct.nrm m) (FreeProduct.nrm m') hkey
    refine ⟨w, ?_, ?_⟩
    · show a * RatU.ofGroup w ∈ Rat.A V
      rw [mem_A_mul_ofGroup_iff]
      intro p hp
      have hp' : p = FreeProduct.nrm m := by
        rw [hPsia, supp_single_one] at hp
        exact Finset.mem_singleton.mp hp
      rw [hp']; exact hw1
    · show RatU.ofGroup w⁻¹ * b ∈ Rat.A V
      rw [mem_ofGroup_mul_A_iff]
      intro p hp
      have hp' : p = FreeProduct.nrm m' := by
        rw [hPsib, supp_single_one] at hp
        exact Finset.mem_singleton.mp hp
      rw [hp']; exact hw2
  · rintro ⟨x, hx1, hx2⟩
    have h1 : a * RatU.ofGroup x ∈ Rat.A V := hx1
    have h2 : RatU.ofGroup x⁻¹ * b ∈ Rat.A V := hx2
    have h3 : (a * RatU.ofGroup x) * (RatU.ofGroup x⁻¹ * b) ∈ Rat.A V :=
      Rat.A_mul h1 h2
    have heq : (a * RatU.ofGroup x) * (RatU.ofGroup x⁻¹ * b) = a * b := by
      rw [mul_assoc, ← mul_assoc (RatU.ofGroup x) (RatU.ofGroup x⁻¹) b, ← RatU.ofGroup_mul,
        mul_inv_cancel, RatU.ofGroup_one, one_mul]
    rwa [heq] at h3

end Work.ORHughesFree.Rat.Source.SW
