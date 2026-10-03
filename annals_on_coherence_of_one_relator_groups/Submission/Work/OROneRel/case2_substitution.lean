import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.injective_presentedGroupMap_of_isConj
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewrite_length_lt

/-!
# Case 2 of the Freiheitssatz: the assembly of the substitution step

This file proves `Work.OROneRel.case2_substitution`: the assembly of the Case-2 ("no letter has
exponent sum zero") step of the Freiheitssatz, given

* the exponent-sum-zero engine `hzero : ∀ N, ZeroExpsumEngine t x N`,
* the type-universal induction hypothesis `IH : FreiheitssatzBelow (relatorNorm r)`,
* transport of injectivity along conjugation `hconj`,
* the shortening of the Magnus rewriting of a cyclically reduced conjugate of the substituted
  relator `hlen`,
* injectivity of the Nielsen substitution `t ↦ t ^ p` in the form `hsubst`.

The mathematical content is exactly the argument of `freiheitssatz_case2_corrected`; the two inputs
that are *not* hypotheses (`relatorNorm_magRewRel_eq_of_notMem` and `substDropped_injective`) are
proved here from scratch, so that this file -- and hence its conclusion -- rests on no unproved
input beyond its hypotheses.
-/
namespace Work.OROneRel

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

variable {α : Type u}

/-! ## Word combinatorics of the Magnus rewriting -/

/-- The Magnus rewriting with respect to a letter that does not occur in the word keeps every
letter (with decorations), hence preserves the length. -/
theorem c2s_rewriteAux_length_of_notMem (t : α) (L : List (α × Bool)) :
    (∀ p ∈ L, p.1 ≠ t) → ∀ i : ℤ, (rewriteAux t i L).length = L.length := by
  induction L with
  | nil => intro _ i; rw [rewriteAux_nil]; simp
  | cons p L ih =>
    intro h i
    rw [rewriteAux_cons_of_ne t i L (h p (by simp))]
    simp only [List.length_cons]
    rw [ih (fun q hq => h q (by simp [hq])) i]

/-- If `t` does not occur in a relator `v`, then the Magnus rewriting of `v` with respect to `t`
has the same norm as `v`. -/
theorem c2s_relatorNorm_magRewRel_eq_of_notMem (t : α) {v : FreeGroup α}
    (h : t ∉ relatorLetters v) :
    relatorNorm (magRewRel t v) = relatorNorm v := by
  classical
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  have hred : FreeGroup.IsReduced (rewrite t v.toWord) :=
    rewrite_isReduced t FreeGroup.isReduced_toWord
  have h1 : relatorNorm (magRewRel t v) = (FreeGroup.toWord (magRewRel t v)).length := rfl
  have h2 : FreeGroup.toWord (magRewRel t v) = rewrite t v.toWord := by
    rw [show magRewRel t v = FreeGroup.mk (rewrite t v.toWord) from rfl,
      FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hred]
  have hl : (rewrite t v.toWord).length = v.toWord.length := by
    show (rewriteAux t 0 v.toWord).length = v.toWord.length
    refine c2s_rewriteAux_length_of_notMem t v.toWord ?_ 0
    rintro ⟨q, b⟩ hq hqt
    exact h ⟨b, by rw [← hqt]; exact hq⟩
  rw [h1, h2, hl]
  rfl

/-! ## Elementary properties of the exponent sum -/

theorem c2s_sigma_of_ne {s a : α} (h : a ≠ s) : sigma s (FreeGroup.of a) = 1 := by
  rw [sigma, FreeGroup.lift_apply_of]; simp [h]

theorem c2s_sigma_of_eq (s : α) : sigma s (FreeGroup.of s) = Multiplicative.ofAdd 1 := by
  rw [sigma, FreeGroup.lift_apply_of]; simp

theorem c2s_sigma_eq_one_of_mem_closure_notMem {s : α} {w : FreeGroup α}
    (h : w ∈ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ s})) : sigma s w = 1 := by
  have hle : Subgroup.closure (FreeGroup.of '' {a : α | a ≠ s}) ≤ (sigma s).ker := by
    apply (Subgroup.closure_le (sigma s).ker).mpr
    rintro y ⟨a, ha, rfl⟩
    exact c2s_sigma_of_ne ha
  exact hle h

theorem c2s_notMem_closure_of_sigma_ne_one {s : α} {w : FreeGroup α} (h : sigma s w ≠ 1) :
    w ∉ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ s}) :=
  fun hc => h (c2s_sigma_eq_one_of_mem_closure_notMem hc)

theorem c2s_mem_relatorLetters_of_sigma_ne_one {s : α} {w : FreeGroup α}
    (h : sigma s w ≠ 1) : s ∈ relatorLetters w := by
  by_contra hs
  apply h
  apply c2s_sigma_eq_one_of_mem_closure_notMem
  rw [letters_closure_iff]
  intro a ha has
  exact hs (has ▸ ha)

theorem c2s_sigma_conj_eq {s : α} (c w : FreeGroup α) : sigma s (c * w * c⁻¹) = sigma s w := by
  rw [map_mul, map_mul, map_inv, mul_comm (sigma s c), mul_assoc, mul_inv_cancel, mul_one]

/-! ## The Case-2 substitution `subst` -/

theorem c2s_subst_apply_of_t (t x : α) (p q : ℤ) :
    subst t x p q (FreeGroup.of t) = (FreeGroup.of t) ^ p := by
  rw [subst, FreeGroup.lift_apply_of, substFun]; simp

theorem c2s_subst_apply_of_x {t x : α} (hxt : x ≠ t) (p q : ℤ) :
    subst t x p q (FreeGroup.of x) = FreeGroup.of x * (FreeGroup.of t) ^ (-q) := by
  rw [subst, FreeGroup.lift_apply_of, substFun]; simp [hxt]

theorem c2s_subst_apply_of_ne {t x a : α} (hat : a ≠ t) (hax : a ≠ x) (p q : ℤ) :
    subst t x p q (FreeGroup.of a) = FreeGroup.of a := by
  rw [subst, FreeGroup.lift_apply_of, substFun]; simp [hat, hax]

theorem c2s_ofAdd_zpow_mul_zpow (p q : ℤ) :
    ((Multiplicative.ofAdd q) ^ p * (Multiplicative.ofAdd p) ^ (-q) : Multiplicative ℤ) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_zpow, toAdd_zpow]
  simp
  ring

theorem c2s_sigma_t_subst {t x : α} (hxt : x ≠ t) (p q : ℤ) (w : FreeGroup α) :
    sigma t (subst t x p q w) = (sigma t w) ^ p * (sigma x w) ^ (-q) := by
  have htx' : t ≠ x := fun h => hxt h.symm
  have h : (sigma t).comp (subst t x p q) =
      ((zpowGroupHom p).comp (sigma t)) * ((zpowGroupHom (-q)).comp (sigma x)) := by
    apply FreeGroup.ext_hom
    intro a
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, zpowGroupHom_apply]
    by_cases hat : a = t
    · rw [hat, c2s_subst_apply_of_t, map_zpow, c2s_sigma_of_eq t,
        c2s_sigma_of_ne (s := x) (a := t) htx', one_zpow, mul_one]
    · by_cases hax : a = x
      · rw [hax, c2s_subst_apply_of_x hxt, map_mul, map_zpow, c2s_sigma_of_eq t,
          c2s_sigma_of_ne (s := t) (a := x) hxt, c2s_sigma_of_eq x]
        simp
      · rw [c2s_subst_apply_of_ne hat hax, c2s_sigma_of_ne (s := t) hat,
          c2s_sigma_of_ne (s := x) hax]
        simp
  simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, zpowGroupHom_apply] using
    DFunLike.congr_fun h w

theorem c2s_sigma_x_subst {t x : α} (hxt : x ≠ t) (p q : ℤ) (w : FreeGroup α) :
    sigma x (subst t x p q w) = sigma x w := by
  have htx' : t ≠ x := fun h => hxt h.symm
  have h : (sigma x).comp (subst t x p q) = sigma x := by
    apply FreeGroup.ext_hom
    intro a
    simp only [MonoidHom.comp_apply]
    by_cases hat : a = t
    · rw [hat, c2s_subst_apply_of_t, map_zpow, c2s_sigma_of_ne (s := x) (a := t) htx']
      simp
    · by_cases hax : a = x
      · rw [hax, c2s_subst_apply_of_x hxt, map_mul, map_zpow,
          c2s_sigma_of_ne (s := x) (a := t) htx', c2s_sigma_of_eq x]
        simp
      · rw [c2s_subst_apply_of_ne hat hax]
  simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun h w

theorem c2s_map_normalClosure_le' {G H : Type*} [Group G] [Group H] (ρ : G →* H) (g : G) :
    Subgroup.normalClosure ({g} : Set G) ≤ (Subgroup.normalClosure ({ρ g} : Set H)).comap ρ := by
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Subgroup.subset_normalClosure (by simp)

/-! ## Injectivity of the "dropped" substitution on `F(α \ {x})` -/

section SubstInj
open Classical

/-- The Nielsen substitution `t ↦ t ^ p` on the free group `F(α \ {x})` (all generators different
from `t` fixed) is injective, given injectivity of the analogous substitution on the index type
where `t` has been split off as an extra generator.

The proof uses that `F(α \ {x})` and `F((α \ {x,t}) ⊕ Unit)` are the same free group: the map
`Einv : F(α \ {x}) →* F((α \ {x,t}) ⊕ Unit)` that sends the `t`-generator to the extra generator and
every other generator to itself has a left inverse `E`, hence is injective, and the substitution in
question factors as `Einv` followed by the substitution of the hypothesis. -/
theorem c2s_subst_map_injective {α : Type u} (x t : α) (hxt : x ≠ t) (p : ℤ) (hp : p ≠ 0)
    (hinj : Function.Injective (FreeGroup.lift (Sum.elim
      (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of (a.1 : α))
      (fun _ : Unit => (FreeGroup.of t) ^ p)))) :
    Function.Injective (FreeGroup.lift (fun a : {a : α // a ≠ x} =>
      if (a : α) = t then (FreeGroup.of t) ^ p else FreeGroup.of (a : α))) := by
  classical
  have htx' : t ≠ x := fun h => hxt h.symm
  set Einv : FreeGroup {a : α // a ≠ x} →* FreeGroup ({a : α // a ≠ x ∧ a ≠ t} ⊕ Unit) :=
    FreeGroup.lift (fun a : {a : α // a ≠ x} =>
      if h : (a : α) = t then FreeGroup.of (Sum.inr ())
      else FreeGroup.of (Sum.inl ⟨(a : α), a.2, h⟩)) with hEinvdef
  set E : FreeGroup ({a : α // a ≠ x ∧ a ≠ t} ⊕ Unit) →* FreeGroup {a : α // a ≠ x} :=
    FreeGroup.lift (Sum.elim
      (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of ⟨(a : α), a.2.1⟩)
      (fun _ : Unit => FreeGroup.of ⟨t, htx'⟩)) with hEdef
  have hE : E.comp Einv = MonoidHom.id (FreeGroup {a : α // a ≠ x}) := by
    apply FreeGroup.ext_hom
    intro a
    show E (Einv (FreeGroup.of a)) = FreeGroup.of a
    rw [hEinvdef, FreeGroup.lift_apply_of]
    by_cases ha : (a : α) = t
    · rw [dif_pos ha, hEdef, FreeGroup.lift_apply_of, Sum.elim_inr]
      exact congrArg FreeGroup.of (Subtype.ext ha.symm)
    · rw [dif_neg ha, hEdef, FreeGroup.lift_apply_of, Sum.elim_inl]
  have hEinv_inj : Function.Injective Einv := by
    intro u w huw
    have h1 := congrArg E huw
    rwa [show E (Einv u) = u from DFunLike.congr_fun hE u,
      show E (Einv w) = w from DFunLike.congr_fun hE w] at h1
  set F : FreeGroup ({a : α // a ≠ x ∧ a ≠ t} ⊕ Unit) →* FreeGroup α :=
    FreeGroup.lift (Sum.elim (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of (a.1 : α))
      (fun _ : Unit => (FreeGroup.of t) ^ p)) with hFdef
  have hinjF : Function.Injective F := hinj
  have hσF : FreeGroup.lift (fun a : {a : α // a ≠ x} =>
        if (a : α) = t then (FreeGroup.of t) ^ p else FreeGroup.of (a : α)) = F.comp Einv := by
    apply FreeGroup.ext_hom
    intro a
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, hEinvdef, FreeGroup.lift_apply_of]
    by_cases ha : (a : α) = t
    · rw [if_pos ha, dif_pos ha, hFdef, FreeGroup.lift_apply_of, Sum.elim_inr]
    · rw [if_neg ha, dif_neg ha, hFdef, FreeGroup.lift_apply_of, Sum.elim_inl]
  rw [hσF]
  exact hinjF.comp hEinv_inj

end SubstInj

/-! ## The Case-2 substitution step -/

theorem case2_substitution {α : Type u} (r : FreeGroup α) (t x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (hT : r ∉ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ x}))
    (hall : ∀ s ∈ Work.OROneRel.relatorLetters r, Work.OROneRel.sigma s r ≠ 1)
    (IH : ∀ (β : Type u) (s : FreeGroup β),
      Work.OROneRel.relatorNorm s < Work.OROneRel.relatorNorm r →
      Work.OROneRel.FreiheitssatzAt s)
    (hzero : ∀ N : ℕ, Work.OROneRel.ZeroExpsumEngine t x N)
    (hconj : ∀ (u s : FreeGroup α) (U : Set α), IsConj u s →
        Function.Injective (Work.OROneRel.presentedGroupMap u U) →
        Function.Injective (Work.OROneRel.presentedGroupMap s U))
    (hlen : ∀ v : FreeGroup α, Work.OROneRel.IsCyclicallyReducedRelator v →
        IsConj v (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
          (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r) →
        Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t v) < Work.OROneRel.relatorNorm r)
    (hsubst : ∀ (p : ℤ), p ≠ 0 → Function.Injective (FreeGroup.lift (Sum.elim
        (fun a : {a : α // a ≠ x ∧ a ≠ t} => FreeGroup.of (a.1 : α))
        (fun _ : Unit => (FreeGroup.of t) ^ p)))) :
    Function.Injective (Work.OROneRel.presentedGroupMap r {a : α | a ≠ x}) := by
  classical
  have htx' : t ≠ x := fun h => htx h.symm
  have hsigx_ne : sigma x r ≠ 1 := hall x hx
  have hsigt_ofAdd : sigma t r = Multiplicative.ofAdd (Multiplicative.toAdd (sigma t r)) := by
    simp
  have hsigx_ofAdd : sigma x r = Multiplicative.ofAdd (Multiplicative.toAdd (sigma x r)) := by
    simp
  set r' : FreeGroup α := subst t x (Multiplicative.toAdd (sigma x r))
      (Multiplicative.toAdd (sigma t r)) r with hr'
  have hP_ne : Multiplicative.toAdd (sigma x r) ≠ 0 := by
    intro h0
    exact hsigx_ne (by rw [hsigx_ofAdd, h0]; rfl)
  have hsigt_subst : sigma t r' = 1 := by
    rw [hr', c2s_sigma_t_subst htx (Multiplicative.toAdd (sigma x r))
        (Multiplicative.toAdd (sigma t r)) r, hsigt_ofAdd, hsigx_ofAdd]
    exact c2s_ofAdd_zpow_mul_zpow _ _
  have hsigx_subst : sigma x r' = sigma x r := by
    rw [hr', c2s_sigma_x_subst htx (Multiplicative.toAdd (sigma x r))
        (Multiplicative.toAdd (sigma t r)) r]
  obtain ⟨v, hcyc_v, hconj_v⟩ : ∃ v : FreeGroup α, IsCyclicallyReducedRelator v ∧
      IsConj v (subst t x (Multiplicative.toAdd (sigma x r))
        (Multiplicative.toAdd (sigma t r)) r) :=
    ⟨cyclicReduction r', isCyclicallyReducedRelator_cyclicReduction r',
      isConj_iff.mpr ⟨cyclicConjugator r', cyclicConjugator_mul_cyclicReduction_mul_inv r'⟩⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj_v
  have hsigt_v : sigma t v = 1 := by
    rw [← c2s_sigma_conj_eq c v, hc, hsigt_subst]
  have hsigx_v : sigma x v = sigma x r := by
    rw [← c2s_sigma_conj_eq c v, hc, hsigx_subst]
  have hsigx_v_ne : sigma x v ≠ 1 := by rw [hsigx_v]; exact hsigx_ne
  have hxmem_v : x ∈ relatorLetters v := c2s_mem_relatorLetters_of_sigma_ne_one hsigx_v_ne
  have hv_notmem : v ∉ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ x}) :=
    c2s_notMem_closure_of_sigma_ne_one hsigx_v_ne
  have hconj_vr' : IsConj v r' := by rw [hr']; exact hconj_v
  have hxT0 : x ∉ ({a : α | a ≠ x} : Set α) := fun h => h rfl
  have hinj_r' : Function.Injective (presentedGroupMap r' {a : α | a ≠ x}) := by
    by_cases htv : t ∈ relatorLetters v
    · have hinj_v : Function.Injective (presentedGroupMap v {a : α | a ≠ x}) := by
        exact hzero (relatorNorm r) v {a : α | a ≠ x} hcyc_v htv hxmem_v hsigt_v
          (Or.inl hxT0) hv_notmem (hlen v hcyc_v hconj_v) IH
      exact hconj v r' {a : α | a ≠ x} hconj_vr' hinj_v
    · have hnorm : relatorNorm v < relatorNorm r := by
        rw [← c2s_relatorNorm_magRewRel_eq_of_notMem t htv]
        exact hlen v hcyc_v hconj_v
      have hinj_v : Function.Injective (presentedGroupMap v {a : α | a ≠ x}) :=
        IH α v hnorm hcyc_v {a : α | a ≠ x} hv_notmem
      exact hconj v r' {a : α | a ≠ x} hconj_vr' hinj_v
  let L : FreeGroup {a : α | a ≠ x} →* FreeGroup α :=
    FreeGroup.lift (fun a : {a : α | a ≠ x} => FreeGroup.of (a : α))
  let σ : FreeGroup {a : α | a ≠ x} →* FreeGroup α :=
    FreeGroup.lift (fun a : {a : α | a ≠ x} =>
      if (a : α) = t then (FreeGroup.of t) ^ (Multiplicative.toAdd (sigma x r))
      else FreeGroup.of (a : α))
  let σ' : FreeGroup {a : α | a ≠ x} →* FreeGroup {a : α | a ≠ x} :=
    FreeGroup.lift (fun a : {a : α | a ≠ x} =>
      if (a : α) = t then (FreeGroup.of ⟨t, htx'⟩) ^ (Multiplicative.toAdd (sigma x r))
      else FreeGroup.of a)
  have hinj_σ : Function.Injective σ :=
    c2s_subst_map_injective x t htx (Multiplicative.toAdd (sigma x r)) hP_ne
      (hsubst (Multiplicative.toAdd (sigma x r)) hP_ne)
  have hσ_eq : σ = (subst t x (Multiplicative.toAdd (sigma x r))
      (Multiplicative.toAdd (sigma t r))).comp L := by
    apply FreeGroup.ext_hom
    intro a
    simp only [σ, L, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    by_cases hat : (a : α) = t
    · rw [if_pos hat, hat, c2s_subst_apply_of_t]
    · rw [if_neg hat, c2s_subst_apply_of_ne hat a.2]
  have hLσ' : L.comp σ' = σ := by
    apply FreeGroup.ext_hom
    intro a
    simp only [σ, σ', L, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    by_cases hat : (a : α) = t
    · rw [if_pos hat, if_pos hat, map_zpow, FreeGroup.lift_apply_of]
    · rw [if_neg hat, if_neg hat, FreeGroup.lift_apply_of]
  have hσ' : σ = L.comp σ' := hLσ'.symm
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  have hu' : (PresentedGroup.mk ({r} : Set (FreeGroup α))) (L u) = 1 := hu
  have hLu : L u ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) :=
    (PresentedGroup.mk_eq_one_iff).mp hu'
  have hφ : (subst t x (Multiplicative.toAdd (sigma x r)) (Multiplicative.toAdd (sigma t r)))
      (L u) ∈ Subgroup.normalClosure ({r'} : Set (FreeGroup α)) := by
    have h1 : (subst t x (Multiplicative.toAdd (sigma x r)) (Multiplicative.toAdd (sigma t r)))
        (L u) ∈ Subgroup.normalClosure
          ({(subst t x (Multiplicative.toAdd (sigma x r))
              (Multiplicative.toAdd (sigma t r))) r} : Set (FreeGroup α)) :=
      Subgroup.mem_comap.mp (c2s_map_normalClosure_le' _ r hLu)
    rwa [← hr'] at h1
  have hσu_mem : σ u ∈ Subgroup.normalClosure ({r'} : Set (FreeGroup α)) := by
    rw [hσ_eq]
    exact hφ
  have hLσ'u : L (σ' u) = σ u := DFunLike.congr_fun hLσ' u
  have h1 : presentedGroupMap r' {a : α | a ≠ x} (σ' u) = 1 := by
    show (PresentedGroup.mk ({r'} : Set (FreeGroup α))) (L (σ' u)) = 1
    rw [hLσ'u]
    exact (PresentedGroup.mk_eq_one_iff).mpr hσu_mem
  have h2 : σ' u = 1 := hinj_r' (by rw [h1, map_one])
  have h3 : σ u = 1 := by rw [← hLσ'u, h2, map_one]
  exact hinj_σ (h3.trans (map_one σ).symm)

end Work.OROneRel
