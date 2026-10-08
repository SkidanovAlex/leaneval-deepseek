import Mathlib
import Submission.Work.Frobenius.Main
import Submission.Work.Frobenius.Induced.ConjChar
import Submission.Work.Frobenius.VCharInd
import Submission.Work.Frobenius.ThetaIrr
import Submission.Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun
import Submission.Work.Frobenius.Induced.resFun_indFun_eq_sum_conjChar
import Submission.Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Characters of a Frobenius group not trivial on the kernel are induced from the kernel

Feit--Thompson (3.16)(iii): an irreducible character `χ` of a Frobenius group `G` with kernel `K`
which does not have `K` in its kernel is induced from an irreducible character of `K`.

The proof is the standard one (Isaacs, *Character Theory of Finite Groups*, Theorem 6.34):

* the restriction `χ|_K` is a class function of `K` which is not constant, so some non-principal
  `θ ∈ Irr K` occurs in it; by Frobenius reciprocity `charPair χ (Ind_K^G θ) ≠ 0`;
* `⟨Ind_K^G θ, Ind_K^G θ⟩ = ⟨θ, (Ind_K^G θ)|_K⟩ = ∑_{h ∈ H} ⟨θ, θ^h⟩ = 1`, because
  `(Ind_K^G θ)|_K = ∑_{h ∈ H} θ^h` (`resFun_indFun_eq_sum_conjChar`) and no non-trivial `h ∈ H`
  fixes a non-principal `θ` (`conjChar_ne_self_of_frobenius`, a consequence of Brauer's
  permutation lemma for the fixed-point-free action of `H` on `K`);
* hence `Ind_K^G θ` is a virtual character of norm one, so `±` an irreducible character
  (`vchar_norm_one`), and pairing with `χ` forces `Ind_K^G θ = χ` (the sign is excluded because
  `Ind_K^G θ` has positive degree `[G : K] θ(1)`).
-/

@[expose] public section

noncomputable section

open Classical

set_option linter.style.haveILetI false

namespace Work.Frobenius.Induced

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- The restriction of a class function to a subgroup is a class function. -/
theorem isClassFun_resFun {K : Subgroup G} {f : G → ℂ} (hf : IsClassFun f) :
    IsClassFun (resFun K f) := by
  intro a b
  simp only [resFun, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hf (a : G) (b : G)

/-- A class function on a finite group which is not constant has a non-principal irreducible
character with non-zero pairing with it. -/
theorem exists_mem_Irr_ne_one_charPair_ne_zero {L : Type*} [Group L] [Fintype L] {f : L → ℂ}
    (hf : IsClassFun f) (hne : f ≠ fun _ => f 1) :
    ∃ θ ∈ Irr L, θ ≠ 1 ∧ charPair f θ ≠ 0 := by
  classical
  by_cases hex : ∃ θ ∈ Irr L, θ ≠ 1 ∧ charPair f θ ≠ 0
  · exact hex
  · exfalso
    have hcon : ∀ θ ∈ Irr L, θ ≠ 1 → charPair f θ = 0 := by
      intro θ hθ hθ1
      by_contra hne'
      exact hex ⟨θ, hθ, hθ1, hne'⟩
    obtain ⟨c, t, hts, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp
      (CharZero.mem_span_Irr_of_isClassFun hf)
    have hcoeff : ∀ a ∈ t, a ≠ 1 → c a = 0 := by
      intro a ha ha1
      have hca : charPair f a = c a := by
        rw [← hsum, charPair_sum_smul_left]
        have hsingle : (∑ b ∈ t, c b * charPair b a) = c a * charPair a a := by
          refine Finset.sum_eq_single a ?_ ?_
          · intro b hb hba
            rw [Irr.charPair_irr_eq_ite (hts hb) (hts ha), ite_eq_right hba, mul_zero]
          · intro hnot; exact absurd ha hnot
        rw [hsingle, Irr.charPair_irr_eq_ite (hts ha) (hts ha), ite_eq_left rfl, mul_one]
      rw [← hca, hcon a (hts ha) ha1]
    refine hne ?_
    funext x
    have hfx : f x = ∑ a ∈ t, c a * a x := by
      rw [← hsum]; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hf1 : f 1 = ∑ a ∈ t, c a * a 1 := by
      rw [← hsum]; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show f x = f 1
    rw [hfx, hf1]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases ha1 : a = 1
    · subst ha1; simp
    · rw [hcoeff a ha ha1]; ring

/-- The degree of an induced class function: `Ind_K^G θ 1 = [G : K] * θ 1`. -/
theorem indFun_apply_one_eq (K : Subgroup G) (θ : K → ℂ) :
    indFun K θ 1 = (K.index : ℂ) * θ 1 := by
  classical
  have h1 : ∀ x : G, (if hx : x * 1 * x⁻¹ ∈ K then θ ⟨x * 1 * x⁻¹, hx⟩ else 0) = θ 1 := by
    intro x
    have hx : x * 1 * x⁻¹ ∈ K := by simp
    rw [dite_eq_left hx]
    congr 1
    exact Subtype.ext (by simp)
  simp only [indFun, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  have hcard : (Nat.card K : ℂ) ≠ 0 := by simp [Nat.card_eq_fintype_card]
  have hidx : (Nat.card G : ℂ) = (Nat.card K : ℂ) * (K.index : ℂ) := by
    rw [← Subgroup.card_mul_index K, Nat.cast_mul]
  rw [hidx, mul_assoc, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

section Inertia

variable {H K : Subgroup G} [K.Normal]

/-- **The inertia group of a non-principal character of the Frobenius kernel is the kernel.**
A non-trivial irreducible character `θ` of the Frobenius kernel `K` is fixed by no non-trivial
element of the complement `H`: `conjChar K h θ ≠ θ` for `1 ≠ h ∈ H`.

This is Feit--Thompson (3.16)(iii) / Isaacs, Theorem 6.34, and the classical proof is via
Brauer's permutation lemma (`Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses`): the
automorphism of `K` given by conjugation with `h` fixes as many conjugacy classes as irreducible
characters, and the only conjugacy class it fixes is that of `1`.  The latter is where the
Frobenius structure enters: if `h k h⁻¹ = c k c⁻¹` with `c, k ∈ K`, then `c * h ∉ K` commutes
with `k`, so (as `c * h ∉ frobeniusKernel H`) it is conjugate to some `1 ≠ h' ∈ H`; conjugating
the relation `h k h⁻¹ = k` by that element exhibits `k ≠ 1` as a fixed point of `h'`, which the
fixed-point-freeness of the action of `H` on `K` forbids. -/
theorem conjChar_ne_self_of_frobenius (hH : IsFrobeniusComplement H)
    (hK : (K : Set G) = frobeniusKernel H) {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθ1 : θ ≠ 1)
    {h : H} (hh : h ≠ 1) : conjChar K (h : G) θ ≠ θ := by
  classical
  intro hfix
  set α : K ≃* K := MulAut.conjNormal (h : G) with hαdef
  have hfpf : IsFixedPointFreeOn K H :=
    (frobenius_fpf_iff (frobenius_normal hH hK) (frobenius_inf_eq_bot hH hK)
      (frobenius_sup_eq_top hH hK) hH.ne_bot (kernel_ne_bot hH hK)).mp hH
  -- the only conjugacy class of `K` fixed by `α` is the class of `1`
  have hclass : ∀ C : ConjClasses K, Work.Clifford.IsFixedClass α C → C = ConjClasses.mk 1 := by
    intro C hC
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
    rw [Work.Clifford.IsFixedClass, Work.Clifford.conjClasses_map_mk] at hC
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hC)
    by_cases hx1 : x = 1
    · rw [hx1]
    · exfalso
      -- `c * h` conjugates `x` to itself
      have h1 : (c : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (c : G)⁻¹ = (x : G) := by
        have h2 : (c : G) * ((α x : K) : G) * (c : G)⁻¹ = (x : G) := by
          have h2' := congrArg (fun z : K => (z : G)) hc
          simpa using h2'
        rw [hαdef, MulAut.conjNormal_apply] at h2
        exact h2
      have hgconj : ((c : G) * (h : G)) * (x : G) * ((c : G) * (h : G))⁻¹ = (x : G) := by
        calc ((c : G) * (h : G)) * (x : G) * ((c : G) * (h : G))⁻¹
            = (c : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (c : G)⁻¹ := by group
          _ = (x : G) := h1
      have hgK : ((c : G) * (h : G)) ∉ (K : Set G) := by
        intro hgmem
        have hhK : (h : G) ∈ K := by
          have : (c : G)⁻¹ * ((c : G) * (h : G)) ∈ K := K.mul_mem (K.inv_mem c.2) hgmem
          simpa using this
        have hinf : (h : G) ∈ K ⊓ H := ⟨hhK, h.2⟩
        rw [frobenius_inf_eq_bot hH hK] at hinf
        exact hh (Subtype.ext (Subgroup.mem_bot.mp hinf))
      have hgnf : ((c : G) * (h : G)) ∉ frobeniusKernel H :=
        fun hm => hgK (show ((c : G) * (h : G)) ∈ (K : Set G) from hK ▸ hm)
      have hg1 : ((c : G) * (h : G)) ≠ 1 := by
        intro hgc
        exact hgnf (by rw [hgc]; exact one_mem_frobeniusKernel)
      have hnot : ¬ ∀ y : G, y⁻¹ * ((c : G) * (h : G)) * y ∉ H := by
        intro hcon
        exact hgnf (mem_frobeniusKernel_iff.mpr (Or.inr hcon))
      push Not at hnot
      obtain ⟨y, hy⟩ := hnot
      have hy1 : y⁻¹ * ((c : G) * (h : G)) * y ≠ 1 := by
        intro hcon
        apply hg1
        calc (c : G) * (h : G) = y * (y⁻¹ * ((c : G) * (h : G)) * y) * y⁻¹ := by group
          _ = 1 := by rw [hcon]; group
      have hxk : y⁻¹ * (x : G) * y ∈ K := (inferInstance : K.Normal).conj_mem' (x : G) x.2 y
      have hxk1 : y⁻¹ * (x : G) * y ≠ 1 := by
        intro hcon
        apply hx1
        exact Subtype.ext (by
          calc (x : G) = y * (y⁻¹ * (x : G) * y) * y⁻¹ := by group
            _ = 1 := by rw [hcon]; group)
      have hcomm : (y⁻¹ * ((c : G) * (h : G)) * y) * (y⁻¹ * (x : G) * y) *
          (y⁻¹ * ((c : G) * (h : G)) * y)⁻¹ = y⁻¹ * (x : G) * y := by
        have hconj := congrArg (fun z : G => y⁻¹ * z * y) hgconj
        calc (y⁻¹ * ((c : G) * (h : G)) * y) * (y⁻¹ * (x : G) * y) *
              (y⁻¹ * ((c : G) * (h : G)) * y)⁻¹
            = y⁻¹ * (((c : G) * (h : G)) * (x : G) * ((c : G) * (h : G))⁻¹) * y := by group
          _ = y⁻¹ * (x : G) * y := by rw [hconj]
      exact hxk1 (hfpf hy hy1 hxk hcomm)
  have hfix1 : Work.Clifford.IsFixedClass α (ConjClasses.mk 1) := by
    rw [Work.Clifford.IsFixedClass, Work.Clifford.conjClasses_map_mk]
    congr 1
    rw [hαdef]
    simp
  have hcardClass : Nat.card {C : ConjClasses K // Work.Clifford.IsFixedClass α C} = 1 := by
    refine Nat.card_eq_one_iff_exists.mpr ⟨⟨ConjClasses.mk 1, hfix1⟩, fun b => Subtype.ext ?_⟩
    exact (hclass b.1 b.2).trans (hclass (ConjClasses.mk 1) hfix1).symm
  -- Brauer's permutation lemma: as many fixed characters as fixed classes
  have hcardIrr :
      Nat.card {χ : K → ℂ // χ ∈ Work.Clifford.Irr K ∧ Work.Clifford.IsFixedIrr α χ} = 1 := by
    rw [Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses α, hcardClass]
  obtain ⟨a, ha⟩ := Nat.card_eq_one_iff_exists.mp hcardIrr
  -- both `θ` and the principal character are fixed, hence equal
  have hθC : θ ∈ Work.Clifford.Irr K :=
    (Work.Clifford.mem_Irr_iff_coherence (G := K)).mpr
      ((Work.Frobenius.Bridge.mem_Irr_iff_coherence (G := K)).mp hθ)
  have honeC : (1 : K → ℂ) ∈ Work.Clifford.Irr K :=
    (Work.Clifford.mem_Irr_iff_coherence (G := K)).mpr
      ((Work.Frobenius.Bridge.mem_Irr_iff_coherence (G := K)).mp
        (Work.Frobenius.Irr.isIrr_one (G := K)))
  have hθFix : Work.Clifford.IsFixedIrr α θ := by
    rw [Work.Clifford.IsFixedIrr]
    funext k
    show θ (α.symm k) = θ k
    have hk := congrFun hfix (α.symm k)
    rw [conjChar_apply] at hk
    have hcoe : ((α.symm k : K) : G) = (h : G)⁻¹ * (k : G) * (h : G) := by
      rw [hαdef, MulAut.conjNormal_symm_apply]
    have heq : (⟨(h : G) * ((α.symm k : K) : G) * (h : G)⁻¹,
        (inferInstance : K.Normal).conj_mem ((α.symm k : K) : G) (α.symm k).2 (h : G)⟩ : K) = k := by
      ext
      show (h : G) * ((α.symm k : K) : G) * (h : G)⁻¹ = (k : G)
      rw [hcoe]; group
    rw [heq] at hk
    exact hk.symm
  have honeFix : Work.Clifford.IsFixedIrr α (1 : K → ℂ) := by
    rw [Work.Clifford.IsFixedIrr]
    funext k
    show (1 : K → ℂ) (α.symm k) = (1 : K → ℂ) k
    simp
  have heq : (⟨θ, ⟨hθC, hθFix⟩⟩ :
        {χ : K → ℂ // χ ∈ Work.Clifford.Irr K ∧ Work.Clifford.IsFixedIrr α χ}) =
      ⟨1, ⟨honeC, honeFix⟩⟩ := (ha _).trans (ha _).symm
  exact hθ1 (congrArg Subtype.val heq)

end Inertia

theorem frobenius_irr_isInduced_of_not_trivial_on_kernel {G : Type*} [Group G] [Fintype G] {H K : Subgroup G} (hH : IsFrobeniusComplement H) (hK : (K : Set G) = frobeniusKernel H) {χ : G → ℂ} (hχ : χ ∈ Irr G) (hker : ∃ k ∈ K, χ k ≠ χ 1) : ∃ θ ∈ Irr K, χ = indFun K θ := by
  classical
  haveI hKn : K.Normal := frobenius_normal hH hK
  have hKf : Fintype K := Fintype.ofFinite K
  have hHf : Fintype H := Fintype.ofFinite H
  have hcomp : Subgroup.IsComplement' K H :=
    (isComplement'_iff K H).mp (frobenius_isComplement' hH hK)
  -- `χ|_K` is a class function which is not constant
  have hfcf : IsClassFun (resFun K χ) := isClassFun_resFun (irr_isClassFun hχ)
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := hker
  have hfne : resFun K χ ≠ fun _ => resFun K χ 1 := by
    intro hc
    exact hk₀ne (congrFun hc ⟨k₀, hk₀K⟩)
  obtain ⟨θ, hθ, hθ1, hpair⟩ := exists_mem_Irr_ne_one_charPair_ne_zero hfcf hfne
  refine ⟨θ, hθ, ?_⟩
  -- Frobenius reciprocity: `χ` pairs non-trivially with `Ind_K^G θ`
  have hrec : charPair χ (indFun K θ) = charPair θ (resFun K χ) := by
    rw [charPair_comm, Induction.charPair_indFun_resFun (φ := θ) (ψ := χ) (irr_isClassFun hχ)]
  have hpairχ : charPair χ (indFun K θ) ≠ 0 := by
    rw [hrec, charPair_comm (G := K)]; exact hpair
  -- `Ind_K^G θ` has norm one
  have hnorm : charPair (indFun K θ) (indFun K θ) = 1 := by
    rw [Induction.charPair_indFun_resFun (φ := θ) (ψ := indFun K θ)
      (Induction.isClassFun_indFun θ)]
    rw [resFun_indFun_eq_sum_conjChar hcomp (irr_isClassFun hθ)]
    rw [charPair_sum_right]
    trans ∑ h : H, (if θ = conjChar K (h : G) θ then 1 else 0)
    · exact Finset.sum_congr rfl fun h _ =>
        Irr.charPair_irr_eq_ite hθ (conjChar_mem_Irr (h : G) hθ)
    · rw [Finset.sum_eq_single (1 : H)]
      · simp
      · intro h _ hh1
        exact ite_eq_right fun hcontra =>
          conjChar_ne_self_of_frobenius hH hK hθ hθ1 hh1 hcontra.symm
      · intro hnot; exact absurd (Finset.mem_univ (1 : H)) hnot
  -- hence `Ind_K^G θ = ± χ'` for some irreducible `χ'`
  have hV : IsVChar (indFun K θ) := isVChar_indFun (AddSubgroup.subset_closure hθ)
  obtain ⟨χ', hχ', hcase⟩ := VChar.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · -- `Ind_K^G θ = χ'`, and the non-zero pairing with `χ` forces `χ = χ'`
    rw [h] at hpairχ
    have hχχ' : χ = χ' := by
      by_contra hne
      rw [Irr.charPair_irr_eq_ite hχ hχ', ite_eq_right hne] at hpairχ
      exact hpairχ rfl
    exact hχχ'.trans h.symm
  · -- the negative case is excluded by positivity of the degree
    exfalso
    obtain ⟨m, hmpos, hm⟩ := character_one_eq_natCast hχ'
    obtain ⟨n, hnpos, hn⟩ := character_one_eq_natCast hθ
    have h1 := congrFun h 1
    rw [indFun_apply_one_eq K θ, hn, Pi.neg_apply, hm] at h1
    have h2 : ((K.index * n + m : ℕ) : ℂ) = 0 := by
      push_cast
      rw [h1]; ring
    have h3 : K.index * n + m = 0 := by exact_mod_cast h2
    omega

end Work.Frobenius.Induced
