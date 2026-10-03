/-
# The star graph of a pushout of groups is a tree

This file proves `Work.ORBassSerre.IsTree (Vtx φ)` for the star graph `Vtx φ` of
`Submission.Work.ORLocInd.FKSKernel.PushoutStarTree`, for an arbitrary family of group
homomorphisms `φ : (i : ι) → H →* G i` (no injectivity is assumed).

## The argument

* A path of `Vtx φ` starting at a centre alternates between centres and leaves.  Following such a
  path records a sequence of "steps" from one centre to the next, each step carrying an element of
  `ofSub φ i` for some `i` (`clets`); reducedness forces consecutive steps to have distinct indices
  and each step to be non-trivial modulo the base subgroup.  The product of the steps is then a
  reduced word in the amalgam whose product lies in the base subgroup, which is impossible
  (`reduced_prod_notMem_baseSub`), so a reduced closed path starting at a centre has length zero.
* A reduced closed path starting at a leaf is turned into a reduced closed path starting at a
  centre of the same length (`cons_isReduced_of_comp_isReduced`), giving the result for all
  vertices.
* Finally `Vtx φ` is connected: every vertex is reachable from the base centre, because the images
  `ofSub φ i` generate the pushout and each of them can be traversed by a path of length two.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTreeTree
import Submission.Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff
import Submission.Work.ORLocInd.FKSKernel.clets_notMem_baseSub_of_isReduced
import Submission.Work.ORLocInd.FKSKernel.clets_isChain_fst_of_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.FKSKernel

open Quiver

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]

/-! ## The reduced word in an amalgam

The facts `clets_notMem_baseSub_of_isReduced` and `clets_isChain_fst_of_isReduced` are proved in
the sibling modules of the same directory and imported below. -/

/-! ## The reduced word in an amalgam

The following two facts are the algebraic core of the proof: a reduced word of positive length in
an amalgamated product never has product in the amalgamated subgroup.

The injective case is a direct consequence of Mathlib's
`Monoid.PushoutI.Reduced.eq_empty_of_mem_range`; the general case is reduced to it by replacing the
edge maps `φ i` by the inclusions `baseSub φ ↪ ofSub φ i`, which has the same pushout (this is the
standard "amalgam structure" of a pushout of groups and is proved below by the universal
property). -/

/-- The `PushoutI`-image of the product of a `CoprodI`-word is the product of the images of its
letters. -/
theorem ofCoprodI_word_prod {φ : ∀ i, H →* G i} (w : Monoid.CoprodI.Word G) :
    Monoid.PushoutI.ofCoprodI (φ := φ) w.prod
      = (w.toList.map (fun x => Monoid.PushoutI.of (φ := φ) x.1 x.2)).prod := by
  have h : ∀ x : Sigma G, Monoid.PushoutI.ofCoprodI (φ := φ) (Monoid.CoprodI.of x.2)
      = Monoid.PushoutI.of (φ := φ) x.1 x.2 := fun x => Monoid.PushoutI.ofCoprodI_of x.1 x.2
  simp only [Monoid.CoprodI.Word.prod, MonoidHom.map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun x _ => h x)

/-- **The injective case.** If all the edge maps are injective, then a reduced word whose product
lies in the base subgroup is empty. -/
theorem reduced_prod_notMem_baseSub_of_injective {φ : ∀ i, H →* G i}
    (hφ : ∀ i, Function.Injective (φ i)) (l : List (ι × Psh φ))
    (hchain : (l.map Prod.fst).IsChain (· ≠ ·))
    (hmem : ∀ x ∈ l, x.2 ∈ ofSub φ x.1)
    (hnot : ∀ x ∈ l, x.2 ∉ baseSub φ)
    (hne : l ≠ []) :
    (l.map Prod.snd).prod ∉ baseSub φ := by
  have key : ∀ (l : List (ι × Psh φ)), (l.map Prod.fst).IsChain (· ≠ ·) →
      (∀ x ∈ l, x.2 ∈ ofSub φ x.1) → (∀ x ∈ l, x.2 ∉ baseSub φ) →
      ∃ (w : Monoid.CoprodI.Word G),
        w.toList.map (fun x => x.1) = l.map Prod.fst ∧
        (w.toList.map (fun x => Monoid.PushoutI.of x.1 x.2)).prod = (l.map Prod.snd).prod ∧
        Monoid.PushoutI.Reduced φ w := by
    intro l
    induction l with
    | nil =>
      intro _ _ _
      refine ⟨Monoid.CoprodI.Word.empty, by simp, by simp, ?_⟩
      intro x hx
      simp only [Monoid.CoprodI.Word.empty, List.not_mem_nil] at hx
    | cons x l' ih =>
      intro hchain hmem hnot
      obtain ⟨i, u⟩ := x
      obtain ⟨g0, hg0⟩ := hmem (i, u) List.mem_cons_self
      rw [List.map_cons] at hchain
      obtain ⟨hhead, hchain'⟩ := List.isChain_cons.mp hchain
      obtain ⟨w', hw'list, hw'prod, hw'red⟩ := ih hchain'
        (fun y hy => hmem y (List.mem_cons_of_mem _ hy))
        (fun y hy => hnot y (List.mem_cons_of_mem _ hy))
      have hg0' : Monoid.PushoutI.of (φ := φ) i g0 = u := hg0
      have hg0one : g0 ≠ 1 := by
        intro h1
        exact hnot (i, u) List.mem_cons_self (show u ∈ baseSub φ from by
          rw [← hg0', h1, map_one]
          exact Subgroup.one_mem (baseSub φ))
      have hchainW : (⟨i, g0⟩ :: w'.toList).IsChain (fun a b => a.1 ≠ b.1) := by
        rw [List.isChain_cons]
        refine ⟨?_, w'.chain_ne⟩
        intro y hy
        have hy' : y.1 ∈ (l'.map Prod.fst).head? := by
          rw [← hw'list, List.head?_map, Option.mem_def.mp hy]
          exact Option.mem_def.mpr rfl
        exact hhead y.1 hy'
      refine ⟨⟨⟨i, g0⟩ :: w'.toList, ?_, hchainW⟩, ?_, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hg0one
        · exact fun h1 => hw'red y hy (h1.symm ▸ Subgroup.one_mem _)
      · show i :: (w'.toList.map (fun x => x.1)) = i :: l'.map Prod.fst
        rw [hw'list]
      · show Monoid.PushoutI.of (φ := φ) i g0
              * (w'.toList.map (fun x => Monoid.PushoutI.of x.1 x.2)).prod
            = u * (l'.map Prod.snd).prod
        rw [hg0', hw'prod]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · rintro ⟨h, hh⟩
          have hh' : φ i h = g0 := hh
          exact hnot (i, u) List.mem_cons_self (show u ∈ baseSub φ from by
            rw [← hg0', ← hh', Monoid.PushoutI.of_apply_eq_base]
            exact ⟨h, rfl⟩)
        · exact hw'red y hy
  obtain ⟨w, hwlist, hwprod, hred⟩ := key l hchain hmem hnot
  intro hmemB
  have hemp : w = Monoid.CoprodI.Word.empty :=
    Monoid.PushoutI.Reduced.eq_empty_of_mem_range hφ hred (by
      rw [ofCoprodI_word_prod, hwprod]
      exact hmemB)
  exact hne (List.map_eq_nil_iff.mp (by rw [← hwlist, hemp]; rfl))

/-- The ``amalgam structure'' of a pushout of groups: the pushout is the amalgamated product of
the images `ofSub φ i` over the image `baseSub φ` of `H`.  Consequently the two amalgams have the
same reduced words. -/
theorem reduced_prod_notMem_baseSub {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (l : List (ι × Psh φ))
    (hchain : (l.map Prod.fst).IsChain (· ≠ ·))
    (hmem : ∀ x ∈ l, x.2 ∈ ofSub φ x.1)
    (hnot : ∀ x ∈ l, x.2 ∉ baseSub φ)
    (hne : l ≠ []) :
    (l.map Prod.snd).prod ∉ baseSub φ := by
  let ψ : ∀ i, ↥(baseSub φ) →* ↥(ofSub φ i) := fun i => Subgroup.inclusion (baseSub_le_ofSub φ i)
  have hψ : ∀ i, Function.Injective (ψ i) := fun i => Subgroup.inclusion_injective _
  -- the two maps between `Psh φ` and the amalgam of the `ofSub φ i` over `baseSub φ`
  let f : Monoid.PushoutI ψ →* Psh φ :=
    Monoid.PushoutI.lift (fun i => (ofSub φ i).subtype) (baseSub φ).subtype (by
      intro i
      ext b
      exact Subgroup.coe_inclusion (baseSub_le_ofSub φ i) b)
  let g : Psh φ →* Monoid.PushoutI ψ :=
    Monoid.PushoutI.lift
      (fun i => (Monoid.PushoutI.of (φ := ψ) i).comp
        ((Monoid.PushoutI.of (φ := φ) i).rangeRestrict))
      ((Monoid.PushoutI.base ψ).comp ((Monoid.PushoutI.base φ).rangeRestrict))
      (by
        intro i
        ext h
        have h1 : (Monoid.PushoutI.of (φ := φ) i).rangeRestrict (φ i h)
            = ψ i ((Monoid.PushoutI.base φ).rangeRestrict h) := by
          have h1' : (Monoid.PushoutI.of (φ := φ) i).rangeRestrict (φ i h)
              = Subgroup.inclusion (baseSub_le_ofSub φ i)
                  ((Monoid.PushoutI.base φ).rangeRestrict h) := by
            apply Subtype.ext
            simp only [MonoidHom.coe_rangeRestrict, Subgroup.coe_inclusion,
              Monoid.PushoutI.of_apply_eq_base]
          exact h1'
        simp only [MonoidHom.comp_apply]
        conv_lhs => rw [h1]
        exact Monoid.PushoutI.of_apply_eq_base ψ i ((Monoid.PushoutI.base φ).rangeRestrict h))
  have g_of : ∀ i (x : G i), g (Monoid.PushoutI.of (φ := φ) i x)
      = Monoid.PushoutI.of (φ := ψ) i ((Monoid.PushoutI.of (φ := φ) i).rangeRestrict x) := by
    intro i x
    dsimp only [g]
    exact Monoid.PushoutI.lift_of _ _ _ _
  have g_base : ∀ h : H, g (Monoid.PushoutI.base φ h)
      = Monoid.PushoutI.base ψ ((Monoid.PushoutI.base φ).rangeRestrict h) := by
    intro h
    dsimp only [g]
    exact Monoid.PushoutI.lift_base _ _ _ _
  have f_of : ∀ i (s : ↥(ofSub φ i)), f (Monoid.PushoutI.of (φ := ψ) i s)
      = (ofSub φ i).subtype s := by
    intro i s
    dsimp only [f]
    exact Monoid.PushoutI.lift_of _ _ _ _
  have f_base : ∀ y : ↥(baseSub φ), f (Monoid.PushoutI.base ψ y) = (baseSub φ).subtype y := by
    intro y
    dsimp only [f]
    exact Monoid.PushoutI.lift_base _ _ _ _
  have hfg : f.comp g = MonoidHom.id (Psh φ) := by
    refine Monoid.PushoutI.hom_ext (φ := φ) (f := f.comp g) (g := MonoidHom.id (Psh φ)) ?_ ?_
    · intro i
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, g_of, f_of]
      exact MonoidHom.coe_rangeRestrict _ _
    · ext h
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, g_base, f_base]
      exact MonoidHom.coe_rangeRestrict _ _
  have hg_baseSub : ∀ y : ↥(baseSub φ), g ((baseSub φ).subtype y) = Monoid.PushoutI.base ψ y := by
    intro y
    obtain ⟨h, hh⟩ := y.2
    have hy : (baseSub φ).subtype y = Monoid.PushoutI.base φ h := hh.symm
    rw [hy, g_base]
    congr 1
    exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict]; exact hh)
  have hg_ofSub : ∀ i (s : ↥(ofSub φ i)), g ((ofSub φ i).subtype s)
      = Monoid.PushoutI.of (φ := ψ) i s := by
    intro i s
    obtain ⟨g0, hg0⟩ := s.2
    have hs : (ofSub φ i).subtype s = Monoid.PushoutI.of (φ := φ) i g0 := hg0.symm
    rw [hs, g_of]
    congr 1
    exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict]; exact hg0)
  -- transport the list
  let l' : List (ι × Monoid.PushoutI ψ) := l.map (fun x => (x.1, g x.2))
  have hl'chain : (l'.map Prod.fst).IsChain (· ≠ ·) := by
    rw [show l'.map Prod.fst = l.map Prod.fst from by
      rw [show l' = l.map (fun x => (x.1, g x.2)) from rfl, List.map_map]
      exact List.map_congr_left (fun x _ => rfl)]
    exact hchain
  have hl'mem : ∀ x ∈ l', x.2 ∈ ofSub ψ x.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨y.2, hmem y hy⟩, (hg_ofSub y.1 ⟨y.2, hmem y hy⟩).symm⟩
  have hl'not : ∀ x ∈ l', x.2 ∉ baseSub ψ := by
    intro x hx hmem'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz⟩ := hmem'
    have h1 : y.2 ∈ baseSub φ := by
      have h2 : f (g y.2) = f (Monoid.PushoutI.base ψ z) := by rw [hz]
      have h4 : f (g y.2) = y.2 := DFunLike.congr_fun hfg y.2
      rw [h4, f_base] at h2
      exact h2.symm ▸ z.2
    exact hnot y hy h1
  have hl'ne : l' ≠ [] := by
    intro h
    exact hne (List.map_eq_nil_iff.mp h)
  intro hprod
  refine reduced_prod_notMem_baseSub_of_injective (φ := ψ) hψ l' hl'chain hl'mem hl'not hl'ne ?_
  have hmap : (l'.map Prod.snd).prod = g ((l.map Prod.snd).prod) := by
    have e1 : l'.map Prod.snd = l.map (fun x => g x.2) := by
      rw [show l' = l.map (fun x => (x.1, g x.2)) from rfl, List.map_map]
      exact List.map_congr_left (fun x _ => rfl)
    have e2 : (l.map Prod.snd).map g = l.map (fun x => g x.2) := by
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => rfl)
    rw [e1, ← e2]
    exact (MonoidHom.map_list_prod g _).symm
  rw [hmap]
  obtain ⟨z, hz⟩ := hprod
  rw [← hz]
  have h3 : (Monoid.PushoutI.base φ z)
      = (baseSub φ).subtype ⟨Monoid.PushoutI.base φ z, ⟨z, rfl⟩⟩ := rfl
  rw [h3, hg_baseSub]
  exact ⟨⟨Monoid.PushoutI.base φ z, ⟨z, rfl⟩⟩, rfl⟩

/-! ## Elementary graph facts -/

/-- The canonical arrow from a centre to a leaf. -/
def arrowCtrLf (φ : ∀ i, H →* G i) (i : ι) (c : Psh φ ⧸ baseSub φ) :
    ctr φ c ⟶ lf φ i c :=
  ⟨(i, c), Or.inl ⟨rfl, rfl⟩⟩

@[simp]
theorem arrowCtrLf_idx (φ : ∀ i, H →* G i) (i : ι) (c : Psh φ ⧸ baseSub φ) :
    (arrowCtrLf φ i c).idx = i := rfl

@[simp]
theorem arrowCtrLf_lbl (φ : ∀ i, H →* G i) (i : ι) (c : Psh φ ⧸ baseSub φ) :
    (arrowCtrLf φ i c).lbl = c := rfl

/-- There are no loops. -/
theorem no_loop (φ : ∀ i, H →* G i) (x : Vtx φ) : IsEmpty (x ⟶ x) :=
  ⟨fun e => by
    rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ctr_ne_lf φ _ _ _ (h1.symm.trans h2)
    · exact lf_ne_ctr φ _ _ _ (h1.symm.trans h2)⟩

/-- The second factor of a reduced composite path is reduced. -/
theorem path_isReduced_of_comp {V : Type u} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c} (h : (u.comp v).IsReduced) : v.IsReduced :=
  fun q hq => h (u.comp q) (hq.comp_left u)

/-- Every vertex is a centre or a leaf. -/
theorem eq_ctr_or_eq_lf (φ : ∀ i, H →* G i) (a : Vtx φ) :
    (∃ c, a = ctr φ c) ∨ (∃ (i : ι) (c : Psh φ ⧸ baseSub φ), a = lf φ i c) := by
  rcases a with c | ⟨i, q⟩
  · exact Or.inl ⟨c, rfl⟩
  · obtain ⟨x, hx⟩ := Quotient.exists_rep q
    refine Or.inr ⟨i, Quotient.mk'' x, ?_⟩
    rw [← hx]
    rfl

/-- A path of length zero is `nil`. -/
theorem nil_cons_eq_toPath {V : Type u} [Quiver V] {a b : V} (e : a ⟶ b) :
    (Quiver.Path.nil.cons e : Quiver.Path a b) = e.toPath :=
  (Quiver.Path.comp_toPath_eq_cons Quiver.Path.nil e).symm.trans (Quiver.Path.nil_comp e.toPath)

/-! ## Cosets and representatives -/

/-- If two base cosets have the same image in `P ⧸ ofSub φ i` then the ratio of their chosen
representatives lies in `ofSub φ i`. -/
theorem mem_ofSub_of_cosetMap_eq (φ : ∀ i, H →* G i) {i : ι} {c c' : Psh φ ⧸ baseSub φ}
    (h : cosetMap φ i c = cosetMap φ i c') :
    (repC φ c)⁻¹ * repC φ c' ∈ ofSub φ i := by
  have h3 : (Quotient.mk'' (repC φ c) : Psh φ ⧸ ofSub φ i) = Quotient.mk'' (repC φ c') := by
    rw [← cosetMap_mk, ← cosetMap_mk, repC_mk φ c, repC_mk φ c', h]
  rw [QuotientGroup.eq] at h3
  simpa using h3

/-- Two base cosets whose representative ratio lies in the base subgroup coincide. -/
theorem eq_of_mul_mem_baseSub (φ : ∀ i, H →* G i) {c c' : Psh φ ⧸ baseSub φ}
    (h : (repC φ c)⁻¹ * repC φ c' ∈ baseSub φ) : c = c' := by
  rw [← repC_mk φ c, ← repC_mk φ c']
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simpa using h))

/-- The ratio of the chosen representatives of two base cosets lies in the base subgroup exactly
when the cosets coincide. -/
theorem mul_mem_baseSub_iff (φ : ∀ i, H →* G i) (c c' : Psh φ ⧸ baseSub φ) :
    (repC φ c)⁻¹ * repC φ c' ∈ baseSub φ ↔ c = c' := by
  refine ⟨fun h => eq_of_mul_mem_baseSub φ h, fun h => ?_⟩
  subst h
  simp

/-- Every letter of the list `clets φ γ p` lies in the subgroup `ofSub φ i` indexed by it. -/
theorem clets_mem_ofSub {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) y) :
    ∀ x ∈ clets φ γ p, x.2 ∈ ofSub φ x.1 := by
  induction p with
  | nil => simp [clets]
  | @cons x y p e ih =>
      rw [clets_cons]
      intro z hz
      rw [List.mem_append] at hz
      rcases hz with hz | hz
      · exact ih z hz
      · by_cases hlen : p.length % 2 = 1
        · rw [if_pos hlen, List.mem_singleton] at hz
          rw [hz]
          have hpar : p.length % 2 ≠ 0 := by omega
          have hxleaf : ¬ ∃ c, x = ctr φ c := by
            intro h
            obtain ⟨c, hc⟩ := h
            exact hpar ((length_even_iff_ctr φ γ x p).mp ⟨c, hc⟩)
          have hleaf : ∃ i, x = lf φ i (cstateC φ γ p) := by
            rcases cstateC_spec φ γ x p with h1 | h1
            · obtain ⟨c, hxc, -⟩ := h1
              exact absurd ((length_even_iff_ctr φ γ x p).mp ⟨c, hxc⟩) hpar
            · exact h1
          obtain ⟨i₀, hi₀⟩ := hleaf
          have he_x : x = lf φ e.idx e.lbl := by
            rcases Arrow.endpoints e with h1 | h1
            · exact absurd h1.1 (fun h => hxleaf ⟨Arrow.lbl e, h⟩)
            · exact h1.1
          exact mem_ofSub_of_cosetMap_eq φ (i := e.idx) (by
            have hlf : lf φ i₀ (cstateC φ γ p) = lf φ e.idx e.lbl := hi₀.symm.trans he_x
            simp only [lf] at hlf
            obtain ⟨hidx, hheq⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hlf)
            subst hidx
            exact eq_of_heq hheq)
        · rw [if_neg hlen] at hz
          exact (List.not_mem_nil hz).elim

/-! ## No reduced closed path starting at a centre -/

/-- The product of the letters attached to a closed path starting at a centre is trivial. -/
theorem prod_clets_eq_one (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ)
    (p : Quiver.Path (ctr φ γ) (ctr φ γ)) :
    ((clets φ γ p).map Prod.snd).prod = 1 := by
  rw [prod_clets]
  rcases cstateC_spec φ γ (ctr φ γ) p with ⟨c, hc, hst⟩ | ⟨i, hi⟩
  · have hc' : c = γ := (ctr_inj (φ := φ) hc).symm
    rw [hst, hc']
    group
  · exact absurd hi (ctr_ne_lf φ γ (cstateC φ γ p) i)

/-- **There is no non-trivial reduced closed path starting at a centre.** -/
theorem no_reduced_closed_ctr (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ)
    (p : Quiver.Path (ctr φ γ) (ctr φ γ)) (hp : p.IsReduced) : p = Quiver.Path.nil := by
  by_contra hne
  have hlen0 : p.length ≠ 0 := fun h => hne (Quiver.Path.eq_nil_of_length_zero p h)
  have hmod : p.length % 2 = 0 := (length_even_iff_ctr φ γ (ctr φ γ) p).mp ⟨γ, rfl⟩
  have hne_list : clets φ γ p ≠ [] := by
    intro h
    have h1 := clets_length φ γ (ctr φ γ) p
    rw [h] at h1
    simp only [List.length_nil] at h1
    omega
  have hmem := clets_mem_ofSub φ γ p
  have hnot := clets_notMem_baseSub_of_isReduced φ γ p hp
  have hchain := clets_isChain_fst_of_isReduced φ γ p hp
  refine absurd (reduced_prod_notMem_baseSub φ (clets φ γ p) hchain hmem hnot hne_list) ?_
  rw [prod_clets_eq_one]
  exact fun h => h (Subgroup.one_mem _)

/-! ## No reduced closed path starting anywhere -/

/-- Given an arrow `e : a ⟶ w` with `a` a leaf and a reduced path `e.toPath.comp p₂`, the path
`p₂.cons e` closing `p₂` at the centre `w` is reduced as well. -/
theorem cons_isReduced_of_comp_isReduced {φ : ∀ i, H →* G i} {a w : Vtx φ}
    (ha : ¬ ∃ c, a = ctr φ c) (e : a ⟶ w) {p₂ : Quiver.Path w a}
    (hp : (e.toPath.comp p₂).IsReduced) : (p₂.cons e).IsReduced := by
  have hp₂ : p₂.IsReduced := path_isReduced_of_comp hp
  rw [Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff]
  refine ⟨hp₂, ?_⟩
  rintro p' e' hp₂eq heq
  rcases eq_ctr_or_eq_lf φ w with ⟨c₀, rfl⟩ | ⟨i₀, c₀, rfl⟩
  · -- `w` is a centre
    have hp'red : p'.IsReduced :=
      ((Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff p' e').mp (hp₂eq ▸ hp₂)).1
    by_cases hp'0 : p'.length = 0
    · -- `p' = nil`: the path `e.toPath.comp p₂` has a backtrack
      have hp'nil : p' = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p' hp'0
      have he' : e' = Quiver.reverse e :=
        (Quiver.reverse_reverse e').symm.trans (congrArg Quiver.reverse heq).symm
      have hp₂rev : p₂ = (Quiver.reverse e).toPath := by
        rw [hp₂eq, hp'nil, he', nil_cons_eq_toPath]
      have hbad : ¬ (e.toPath.cons (Quiver.reverse e)).IsReduced := by
        intro hred
        have h2 := ((Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff e.toPath
          (Quiver.reverse e)).mp hred).2
        exact (h2 Quiver.Path.nil e (nil_cons_eq_toPath e).symm) rfl
      rw [hp₂rev, Quiver.Path.comp_toPath_eq_cons] at hp
      exact hbad hp
    · exact absurd (no_reduced_closed_ctr φ c₀ p' hp'red) (by
        intro h
        rw [h] at hp'0
        exact hp'0 rfl)
  · -- `w` is a leaf, so `a` would have to be a centre, contradicting `ha`
    have hw : ¬ ∃ c, lf φ i₀ c₀ = ctr φ c :=
      fun h => h.elim fun c hc => lf_ne_ctr φ c₀ c i₀ hc
    exact ha (not_not.mp (mt (ctr_excl (φ := φ) e').mpr hw))

/-- **There is no non-trivial reduced closed path.** -/
theorem no_reduced_closed_any (φ : ∀ i, H →* G i) (a : Vtx φ) (p : Quiver.Path a a)
    (hp : p.IsReduced) : p = Quiver.Path.nil := by
  rcases eq_ctr_or_eq_lf φ a with ⟨c, rfl⟩ | ⟨i, c, rfl⟩
  · exact no_reduced_closed_ctr φ c p hp
  · by_cases hlen : p.length = 0
    · exact Quiver.Path.eq_nil_of_length_zero p hlen
    · exfalso
      obtain ⟨z, e, p₂, hp₂len, hpeq⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ p (n := p.length - 1) (by omega)
      have hp' : (e.toPath.comp p₂).IsReduced := hpeq ▸ hp
      have ha : ¬ ∃ c', lf φ i c = ctr φ c' :=
        fun h => h.elim fun c' hc => ctr_ne_lf φ c' c i hc.symm
      have hz : ∃ c₀, z = ctr φ c₀ :=
        not_not.mp (mt (ctr_excl (φ := φ) e).mpr ha)
      obtain ⟨c₀, rfl⟩ := hz
      have hq : (p₂.cons e).IsReduced := cons_isReduced_of_comp_isReduced ha e hp'
      have hqnil : p₂.cons e = Quiver.Path.nil := no_reduced_closed_ctr φ c₀ (p₂.cons e) hq
      have hlenq : (p₂.cons e).length = 0 := by rw [hqnil]; rfl
      rw [Quiver.Path.length_cons] at hlenq
      omega

/-! ## Connectivity -/

/-- Right multiplication by an element of `ofSub φ i` preserves reachability of centres from the
base centre, by a path of length two. -/
theorem path_mul_ofSub (φ : ∀ i, H →* G i) (g : Psh φ) {i : ι} {u : Psh φ}
    (hu : u ∈ ofSub φ i)
    (h : Nonempty (Quiver.Path (ctr φ (Quotient.mk'' (1 : Psh φ)))
      (ctr φ (Quotient.mk'' g)))) :
    Nonempty (Quiver.Path (ctr φ (Quotient.mk'' (1 : Psh φ)))
      (ctr φ (Quotient.mk'' (g * u)))) := by
  obtain ⟨p⟩ := h
  have hlf : lf φ i (Quotient.mk'' g) = lf φ i (Quotient.mk'' (g * u)) := by
    simp only [lf]
    congr 1
    rw [cosetMap_mk, cosetMap_mk]
    congr 1
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
      (show g⁻¹ * (g * u) ∈ ofSub φ i from by rw [inv_mul_cancel_left]; exact hu))
  refine ⟨(p.cons (arrowCtrLf φ i (Quotient.mk'' g))).cons ?_⟩
  exact ⟨(i, Quotient.mk'' (g * u)), Or.inr ⟨hlf, rfl⟩⟩

/-- The images of the `G i` in the pushout generate it. -/
theorem closure_iUnion_ofSub_eq_top (φ : ∀ i, H →* G i) [Nonempty ι] :
    Subgroup.closure (⋃ i, (ofSub φ i : Set (Psh φ))) = ⊤ := by
  refine le_antisymm le_top ?_
  intro g _
  refine Monoid.PushoutI.induction_on (φ := φ) g ?_ ?_ ?_
  · intro i x
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, ⟨x, rfl⟩⟩)
  · intro h
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [← Monoid.PushoutI.of_apply_eq_base (φ := φ) i₀ h]
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i₀, ⟨φ i₀ h, rfl⟩⟩)
  · intro x y hx hy
    exact Subgroup.mul_mem _ hx hy

/-- Every centre is reachable from the base centre. -/
theorem exists_path_ctr_mk (φ : ∀ i, H →* G i) [Nonempty ι] (g : Psh φ) :
    Nonempty (Quiver.Path (ctr φ (Quotient.mk'' (1 : Psh φ))) (ctr φ (Quotient.mk'' g))) := by
  have htop := closure_iUnion_ofSub_eq_top φ
  have hg : g ∈ Subgroup.closure (⋃ i, (ofSub φ i : Set (Psh φ))) := by rw [htop]; trivial
  refine Subgroup.closure_induction_right (p := fun x _ => Nonempty (Quiver.Path
    (ctr φ (Quotient.mk'' (1 : Psh φ))) (ctr φ (Quotient.mk'' x)))) ?_ ?_ ?_ hg
  · exact ⟨Quiver.Path.nil⟩
  · intro x _ y hy ih
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hyi⟩ := hy
    exact path_mul_ofSub φ x hyi ih
  · intro x _ y hy ih
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hyi⟩ := hy
    exact path_mul_ofSub φ x (Subgroup.inv_mem _ hyi) ih

/-- Every vertex is reachable from the base centre. -/
theorem exists_path_ctr_mk_to (φ : ∀ i, H →* G i) [Nonempty ι] (v : Vtx φ) :
    Nonempty (Quiver.Path (ctr φ (Quotient.mk'' (1 : Psh φ))) v) := by
  rcases eq_ctr_or_eq_lf φ v with ⟨c, rfl⟩ | ⟨i, c, rfl⟩
  · obtain ⟨g, hg⟩ := Quotient.exists_rep c
    rw [← hg]
    exact exists_path_ctr_mk φ g
  · obtain ⟨g, hg⟩ := Quotient.exists_rep c
    rw [← hg]
    obtain ⟨p⟩ := exists_path_ctr_mk φ g
    exact ⟨p.cons (arrowCtrLf φ i (Quotient.mk'' g))⟩

/-! ## The degenerate case of an empty index type -/

/-- For an empty index type the base subgroup is everything. -/
theorem baseSub_eq_top_of_isEmpty (φ : ∀ i, H →* G i) [IsEmpty ι] : baseSub φ = ⊤ := by
  refine le_antisymm le_top ?_
  intro g _
  refine Monoid.PushoutI.induction_on (φ := φ) g ?_ ?_ ?_
  · intro i
    exact isEmptyElim i
  · intro h
    exact ⟨h, rfl⟩
  · intro x y hx hy
    exact Subgroup.mul_mem _ hx hy

/-- With an empty index type every path has length zero. -/
theorem path_length_eq_zero_of_isEmpty (φ : ∀ i, H →* G i) [IsEmpty ι] {a b : Vtx φ}
    (p : Quiver.Path a b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons q e _ => exact (IsEmpty.false e.1.1).elim

/-- With an empty index type the star graph has a single vertex and no arrows. -/
theorem isTree_of_isEmpty (φ : ∀ i, H →* G i) [IsEmpty ι] :
    Work.ORBassSerre.IsTree (Vtx φ) := by
  have htop : baseSub φ = ⊤ := baseSub_eq_top_of_isEmpty φ
  haveI h1 : Subsingleton (Psh φ ⧸ baseSub φ) := by
    refine ⟨fun x y => ?_⟩
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b =>
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by rw [htop]; trivial))
  haveI hsub : Subsingleton (Vtx φ) :=
    ⟨fun a b => by
      cases a with
      | inl c =>
        cases b with
        | inl d => exact congrArg Sum.inl (Subsingleton.elim c d)
        | inr z => exact (IsEmpty.false z.1).elim
      | inr z => exact (IsEmpty.false z.1).elim⟩
  constructor
  · intro a b
    rw [Subsingleton.elim a b]
    exact ⟨Quiver.Path.nil⟩
  · intro a p _
    have hlen : p.length = 0 := path_length_eq_zero_of_isEmpty φ p
    exact Quiver.Path.eq_nil_of_length_zero p hlen

/-- **The star graph of a pushout of groups is a tree.** -/
theorem pushoutStarTree_isTree {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) :
    Work.ORBassSerre.IsTree (Work.ORLocInd.FKSKernel.Vtx φ) := by
  by_cases hι : Nonempty ι
  · haveI := hι
    refine ⟨fun a b => ?_, fun a p hp => ?_⟩
    · obtain ⟨pa⟩ := exists_path_ctr_mk_to φ a
      obtain ⟨pb⟩ := exists_path_ctr_mk_to φ b
      exact ⟨pa.reverse.comp pb⟩
    · exact no_reduced_closed_any φ a p hp
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    exact isTree_of_isEmpty φ

end Work.ORLocInd.FKSKernel
