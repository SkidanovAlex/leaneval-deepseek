import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.rewrite_mem_letter
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewrite_isCyclicallyReduced_of_expsum_zero
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.injective_presentedGroupMap_of_disjoint
import Submission.Work.OROneRel.presentedGroupMap_injective_mono
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.rho_magRew
import Submission.Work.OROneRel.sigma_mk

/-!
# The `x ∉ T` case of the exponent-sum-zero step of the Freiheitssatz

Let `r` be a cyclically reduced relator whose exponent sum in the letter `t` is zero
(`sigma t r = 1`), and let `x ≠ t` be a letter of `r` which is *outside* the generating set `T`
(`x ∉ T`), with `r ∉ ⟨T⟩`.  This file proves that the canonical map `F(T) →* ⟨α | r⟩` is injective.

The HNN step `HNNStepCore r t x i j` exhibits `⟨α | r⟩` as an HNN extension of the one-relator
group `G' = ⟨(α \ {t}) × ℤ | r'⟩`, `r' = magRewRel t r`, with stable letter `t`, and with the
rewriting identity `hrewrite` for words of exponent sum zero avoiding the letter `x`.

The argument is a short kernel computation.  Let `u ∈ F(T)` with `presentedGroupMap r T u = 1`,
and put `w = FreeGroup.map Subtype.val u ∈ F(α)`.  Then

* the exponent sum in `t` of `w` is zero, because the exponent-sum homomorphism `sigma t` kills
  `r` (as `sigma t r = 1`) and therefore factors through `⟨α | r⟩`;
* `x ∉ relatorLetters w`, since the letters of `w` lie in `T` and `x ∉ T`;
* the rewriting identity gives `hnnOf r t (presentedGroupMap r' Sx (magRewRel t w)) = 1` (the image
  of `w` in `⟨α | r⟩` is trivial);
* the letters of `magRewRel t w` avoid `x`, so `magRewRel t w ∈ ⟨Sx⟩` with `Sx` the set of
  decorations avoiding `x`, while `magRewRel t r` contains an `x`-decoration and hence is *not* in
  `⟨Sx⟩`; the Freiheitssatz at the shorter relator `r'` (the induction hypothesis) therefore forces
  `magRewRel t w = 1`;
* `rho t (magRewRel t w) = w` because the exponent sum of `t` in `w` is zero, so `w = 1`, and hence
  `u = 1` by injectivity of `FreeGroup.map Subtype.val`.
-/

namespace Work.OROneRel

universe u

/-! ### Word combinatorics of the Magnus rewriting -/

/-- Every letter of a Magnus rewriting comes from a letter of the input word (with the same first
coordinate). -/
private lemma rewriteAux_source {α : Type u} (t : α) (i : ℤ) {L : List (α × Bool)}
    {p : ({a : α // a ≠ t} × ℤ) × Bool} (hp : p ∈ rewriteAux t i L) :
    ∃ b : Bool, ((p.1.1 : α), b) ∈ L := by
  induction L generalizing i with
  | nil => rw [rewriteAux_nil] at hp; exact absurd hp (List.not_mem_nil)
  | cons q L' ih =>
    by_cases hq : q.1 = t
    · rw [rewriteAux_cons_of_eq t i L' hq] at hp
      obtain ⟨b, hb⟩ := ih (i + (if q.2 then 1 else -1)) hp
      exact ⟨b, List.mem_cons_of_mem _ hb⟩
    · rw [rewriteAux_cons_of_ne t i L' hq] at hp
      rw [List.mem_cons] at hp
      rcases hp with hp | hp
      · refine ⟨q.2, ?_⟩
        subst hp
        simp
      · obtain ⟨b, hb⟩ := ih i hp
        exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- The Magnus rewriting of `w` only involves decorations whose letter is a letter of `w`. -/
private lemma relatorLetters_magRewRel_subset {α : Type u} (t x : α) {w : FreeGroup α}
    (hw : x ∉ relatorLetters w) :
    relatorLetters (magRewRel t w) ⊆ {p : ({a : α // a ≠ t} × ℤ) | (p.1 : α) ≠ x} := by
  classical
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  intro p hp
  obtain ⟨b, hb⟩ := hp
  have hto : (magRewRel t w).toWord = rewrite t w.toWord := by
    show (FreeGroup.mk (rewrite t w.toWord)).toWord = rewrite t w.toWord
    rw [FreeGroup.toWord_mk]
    exact FreeGroup.IsReduced.reduce_eq (rewrite_isReduced t FreeGroup.isReduced_toWord)
  rw [hto] at hb
  obtain ⟨b', hb'⟩ := rewriteAux_source t 0 hb
  intro hpx
  exact hw ⟨b', by rw [← hpx]; exact hb'⟩

/-- The Magnus rewriting of a cyclically reduced relator of exponent sum zero is cyclically
reduced. -/
private lemma isCyclicallyReducedRelator_magRewRel {α : Type u} (t : α) (r : FreeGroup α)
    (hcyc : IsCyclicallyReducedRelator r) (h : eps t r = 0) :
    IsCyclicallyReducedRelator (magRewRel t r) := by
  classical
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  have hcw : FreeGroup.IsCyclicallyReduced (rewrite t r.toWord) :=
    isCyclicallyReducedRelator_rewrite_toWord t hcyc h
  rw [IsCyclicallyReducedRelator, magRewRel, FreeGroup.toWord_mk, hcw.isReduced.reduce_eq]
  exact hcw

/-- If `x ≠ t` is a letter of `r`, then the Magnus rewriting `magRewRel t r` contains a letter whose
first coordinate is `x`. -/
private lemma exists_relatorLetters_magRewRel {α : Type u} (r : FreeGroup α) (t x : α)
    (htx : x ≠ t) (hx : x ∈ relatorLetters r) :
    ∃ p : ({a : α // a ≠ t} × ℤ), p ∈ relatorLetters (magRewRel t r) ∧ (p.1 : α) = x := by
  classical
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  obtain ⟨b, hb⟩ := hx
  obtain ⟨q, hq1, hq2⟩ := rewrite_mem_letter t x htx b hb
  refine ⟨q.1, ?_, ?_⟩
  · refine ⟨q.2, ?_⟩
    have hto : (magRewRel t r).toWord = rewrite t r.toWord := by
      show (FreeGroup.mk (rewrite t r.toWord)).toWord = rewrite t r.toWord
      rw [FreeGroup.toWord_mk]
      exact FreeGroup.IsReduced.reduce_eq (rewrite_isReduced t FreeGroup.isReduced_toWord)
    rw [hto]
    exact hq2
  · rw [hq1]

/-- `rho t` sends the Magnus rewriting of a word of exponent sum zero back to the word. -/
private lemma rho_magRewRel {α : Type u} (t : α) (w : FreeGroup α) (h : eps t w = 0) :
    rho t (magRewRel t w) = w := by
  classical
  have hw : wordEps t w.toWord = 0 := h
  have hmain := rho_magRew t 0 w.toWord
  rw [hw, add_zero, neg_zero, zpow_zero, mul_one, one_mul] at hmain
  rw [magRewRel, ← magRew_zero_eq_rewrite, hmain, FreeGroup.mk_toWord]

/-! ### Two general purpose reductions -/

/-- The exponent sum in `t` of a word vanishes whenever its image in `⟨α | r⟩` is trivial and
`sigma t r = 1` (so that the exponent sum descends to `⟨α | r⟩`). -/
private lemma sigma_eq_one_of_mk_eq_one {α : Type u} (r : FreeGroup α) (t : α)
    (ht0 : sigma t r = 1) {w : FreeGroup α}
    (hw : (PresentedGroup.mk ({r} : Set (FreeGroup α))) w = 1) : sigma t w = 1 := by
  classical
  let f : α → Multiplicative ℤ := fun a => if a = t then Multiplicative.ofAdd (1 : ℤ) else 1
  have hfs : FreeGroup.lift f = sigma t := by rw [sigma]
  let σb : PresentedGroup ({r} : Set (FreeGroup α)) →* Multiplicative ℤ :=
    PresentedGroup.toGroup (f := f) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [hfs]
      exact ht0)
  have hcomp : σb.comp (PresentedGroup.mk ({r} : Set (FreeGroup α))) = sigma t := by
    apply FreeGroup.ext_hom
    intro a
    show σb ((PresentedGroup.mk ({r} : Set (FreeGroup α))) (FreeGroup.of a))
      = sigma t (FreeGroup.of a)
    rw [show (PresentedGroup.mk ({r} : Set (FreeGroup α))) (FreeGroup.of a) = PresentedGroup.of a
      from rfl]
    rw [PresentedGroup.toGroup.of]
    rw [← hfs]
    rw [FreeGroup.lift_apply_of]
  have h := DFunLike.congr_fun hcomp w
  simp only [MonoidHom.comp_apply] at h
  rw [← h, hw, map_one]

/-- `sigma t w = 1` implies `eps t w = 0` (the two notations for exponent sum zero). -/
private lemma eps_eq_zero_of_sigma_eq_one {α : Type u} (t : α) (w : FreeGroup α)
    (h : sigma t w = 1) : eps t w = 0 := by
  classical
  have hh := sigma_mk t w.toWord
  rw [FreeGroup.mk_toWord] at hh
  rw [h] at hh
  have h0 : sigmaList t w.toWord = 0 := by
    apply Multiplicative.ofAdd.injective
    simpa using hh.symm
  show wordEps t w.toWord = 0
  rw [← sigmaList_eq_wordEps]
  exact h0

/-- The two ways of viewing `F(S)` inside `PresentedGroup {r}` agree. -/
private lemma map_mk_eq_presentedGroupMap {β : Type u} (r : FreeGroup β) (S : Set β)
    (v : FreeGroup S) :
    (PresentedGroup.mk ({r} : Set (FreeGroup β))) (FreeGroup.map (Subtype.val : S → β) v)
      = presentedGroupMap r S v := by
  rw [presentedGroupMap, FreeGroup.map_eq_lift]
  rfl

/-- If `presentedGroupMap r S` is injective, then any element of `F(β)` in the subgroup generated by
`S` whose image in `⟨β | r⟩` is trivial is itself trivial. -/
private lemma eq_one_of_mem_closure {β : Type u} {r : FreeGroup β} {S : Set β}
    (hinj : Function.Injective (presentedGroupMap r S)) {y : FreeGroup β}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' S))
    (hy1 : (PresentedGroup.mk ({r} : Set (FreeGroup β))) y = 1) : y = 1 := by
  have hy' : y ∈ (FreeGroup.map (Subtype.val : S → β)).range := by
    rw [FreeGroup.range_map, Subtype.range_coe]
    exact hy
  obtain ⟨v, hv⟩ := hy'
  have hv1 : v = 1 := hinj (by
    show presentedGroupMap r S v = presentedGroupMap r S 1
    rw [map_one (presentedGroupMap r S), ← map_mk_eq_presentedGroupMap r S v, hv]
    exact hy1)
  rw [← hv, hv1, map_one]

/-! ### The main theorem -/

section
variable {α : Type u}

theorem zero_expsum_x_not_mem (r : FreeGroup α) (T : Set α) (t x : α) (i j : ℤ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (ht0 : Work.OROneRel.sigma t r = 1) (hxT : x ∉ T)
    (hT : r ∉ Subgroup.closure (FreeGroup.of '' T))
    (d : Work.OROneRel.HNNStepCore r t x i j)
    (hrewrite : ∀ w : FreeGroup α, Work.OROneRel.sigma t w = 1 →
      x ∉ Work.OROneRel.relatorLetters w →
      d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) w) =
        Work.OROneRel.hnnOf r t (PresentedGroup.mk
          ({Work.OROneRel.magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))
          (Work.OROneRel.magRewRel t w)))
    (IH : ∀ (β : Type u) (s : FreeGroup β),
      Work.OROneRel.relatorNorm s < Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t r) + 1 →
      Work.OROneRel.FreiheitssatzAt s) :
    Function.Injective (Work.OROneRel.presentedGroupMap r T) := by
  classical
  have heps : eps t r = 0 := eps_eq_zero_of_sigma_eq_one t r ht0
  have hcyc' : IsCyclicallyReducedRelator (magRewRel t r) :=
    isCyclicallyReducedRelator_magRewRel t r hcyc heps
  obtain ⟨px, hpxmem, hpxval⟩ := exists_relatorLetters_magRewRel r t x htx hx
  let Sx : Set ({a : α // a ≠ t} × ℤ) := {p | (p.1 : α) ≠ x}
  have hr'Sx : magRewRel t r ∉ Subgroup.closure (FreeGroup.of '' Sx) := by
    intro hcon
    have hsub := (letters_closure_iff (magRewRel t r) Sx).mp hcon
    exact (hsub hpxmem) hpxval
  have hFA : FreiheitssatzAt (magRewRel t r) :=
    IH ({a : α // a ≠ t} × ℤ) (magRewRel t r) (Nat.lt_succ_self _)
  have hinjSx : Function.Injective (presentedGroupMap (magRewRel t r) Sx) :=
    hFA hcyc' Sx hr'Sx
  have key : ∀ u : FreeGroup T, presentedGroupMap r T u = 1 → u = 1 := by
    intro u hu
    let incl : FreeGroup T →* FreeGroup α := FreeGroup.map (Subtype.val : T → α)
    let w : FreeGroup α := incl u
    have hwq : (PresentedGroup.mk ({r} : Set (FreeGroup α))) w = presentedGroupMap r T u := by
      rw [show w = FreeGroup.map (Subtype.val : T → α) u from rfl, presentedGroupMap,
        FreeGroup.map_eq_lift]
      rfl
    have hq1 : (PresentedGroup.mk ({r} : Set (FreeGroup α))) w = 1 := by rw [hwq, hu]
    have hσw : sigma t w = 1 := sigma_eq_one_of_mk_eq_one r t ht0 hq1
    have hwmem : w ∈ Subgroup.closure (FreeGroup.of '' T) := by
      have hwr : w ∈ (FreeGroup.map (Subtype.val : T → α)).range := ⟨u, rfl⟩
      rwa [FreeGroup.range_map, Subtype.range_coe] at hwr
    have hsup : relatorLetters w ⊆ T := (letters_closure_iff w T).mp hwmem
    have hxw : x ∉ relatorLetters w := fun h => hxT (hsup h)
    have hrw := hrewrite w hσw hxw
    have hq'2 : (PresentedGroup.mk
        ({magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))) (magRewRel t w) = 1 := by
      apply HNNExtension.of_injective (d.phi)
      show hnnOf r t ((PresentedGroup.mk
          ({magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ))))
          (magRewRel t w)) = hnnOf r t (1 : HNNBase r t)
      rw [← hrw, hq1]
      simp
    have hsubset : relatorLetters (magRewRel t w) ⊆ Sx :=
      relatorLetters_magRewRel_subset t x hxw
    have hmrw : magRewRel t w = 1 :=
      eq_one_of_mem_closure hinjSx ((letters_closure_iff (magRewRel t w) Sx).mpr hsubset) hq'2
    have heps0 : eps t w = 0 := eps_eq_zero_of_sigma_eq_one t w hσw
    have hw1 : w = 1 := by
      rw [← rho_magRewRel t w heps0, hmrw, map_one]
    have hincl : incl u = incl 1 := by
      rw [map_one incl]
      exact hw1
    exact FreeGroup.map_injective (Subtype.val_injective) hincl
  intro a b hab
  have h : a * b⁻¹ = 1 := key (a * b⁻¹) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
  exact (mul_inv_eq_one.mp h)

end

end Work.OROneRel
