/-
# Assembly: one-relator groups are virtually torsion-free

The main theorem of node N4 is assembled here from the inputs of the paper:

* the per-relator Magnus--Moldavanskii--Masters hierarchy `Work.OROneRel.MagnusMoldavanskiiAt r`
  (node N2), which presents `⟨α | r⟩` as a tower of HNN extensions over free Magnus subgroups,
  ending at the groups of terminal relators `1` or `of x ^ k`;
* the general HNN step `Work.ORLocInd.HNNVirtualTorsionFree` (Fischer--Karrass--Solitar 1972),
  which propagates virtual torsion-freeness up the tower.

(`hKMS` is kept in the signature for faithfulness to the paper's input; the argument below does not
need it: the terminal levels are handled directly by the explicit description of their groups as
free products `F(α∖{x}) ∗ ℤ/k`.)

## Universes

The hypotheses `hMM`, `hstep` (and `hKMS`) are taken at the single universe `u` of this file, and the
generating type `α` of a one-relator group is not assumed to be small.  The proof therefore

1. reduces `⟨α | r⟩` to the free product of a one-relator group presented on a *finite* generating
   type and a free group (`exists_coprod_presentation`, via the fact that a relator only involves
   finitely many letters);
2. presents that finitely generated group on `Fin n`, and moves it to the universe `u` using
   `ULift.{u, 0}` of `Fin n`;
3. proves virtual torsion-freeness of every level of the hierarchy by induction on
   `HasMMHierarchy`, taking `hstep` in that universe (`Work.ORLocInd.Assembly.vt_of_hierarchy`); the
   `embed` case of the hierarchy (Magnus's embedding of the no-zero-exponent-sum case) is handled by
   passing to the subgroup `ι.range` and using
   `Work.ORLocInd.Virtual.virtuallyTorsionFree_subgroup`.
-/
import Mathlib
import Submission.Work.ORLocInd.Core
import Submission.Work.ORLocInd.Bridge.N2
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.Derived
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod
import Submission.Work.ORLocInd.presentedGroup_iso_of_mulEquiv
import Submission.Work.ORLocInd.hnnExtension_congr
import Submission.Work.ORLocInd.Virtual.virtuallyTorsionFree_subgroup
import Submission.Work.OROneRel.coprod_isOfFinOrder_conj

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORLocInd.Assembly

open Work.ORLocInd


/-! ## Temporary placeholders for the delegated lemmas (removed once they land) -/

/-- **Virtual torsion-freeness is preserved by free products.**  If `M' ⊴ M` and `N' ⊴ N` are
torsion-free of finite index, then the kernel of `M ∗ N → M/M' × N/N'` is normal, of finite index,
and torsion-free: an element of finite order in a free product is conjugate into one of the factors
(`Work.OROneRel.coprod_isOfFinOrder_conj`), and the kernel meets `M` in `M'` and `N` in `N'`. -/
theorem virtuallyTorsionFree_coprod_aux {M N : Type u} [Group M] [Group N]
    (hM : VirtuallyTorsionFree M) (hN : VirtuallyTorsionFree N) :
    VirtuallyTorsionFree (Monoid.Coprod M N) := by
  obtain ⟨M', hMn, hMfi, hMtf⟩ := hM
  obtain ⟨N', hNn, hNfi, hNtf⟩ := hN
  haveI := hMn
  haveI := hNn
  haveI := hMfi
  haveI := hNfi
  let φ₁ : M →* (M ⧸ M') × (N ⧸ N') :=
    { toFun := fun a => (QuotientGroup.mk' M' a, 1)
      map_one' := by simp
      map_mul' := by intro a b; simp }
  let φ₂ : N →* (M ⧸ M') × (N ⧸ N') :=
    { toFun := fun b => (1, QuotientGroup.mk' N' b)
      map_one' := by simp
      map_mul' := by intro b c; simp }
  let π : Monoid.Coprod M N →* (M ⧸ M') × (N ⧸ N') := Monoid.Coprod.lift φ₁ φ₂
  have hπ_inl : ∀ a : M, π (Monoid.Coprod.inl a) = (QuotientGroup.mk' M' a, 1) :=
    fun a => Monoid.Coprod.lift_apply_inl φ₁ φ₂ a
  have hπ_inr : ∀ b : N, π (Monoid.Coprod.inr b) = (1, QuotientGroup.mk' N' b) :=
    fun b => Monoid.Coprod.lift_apply_inr φ₁ φ₂ b
  refine ⟨π.ker, MonoidHom.normal_ker π, Subgroup.finiteIndex_ker π, ?_⟩
  intro x hxfin
  have hxfin' : IsOfFinOrder (x : Monoid.Coprod M N) := MonoidHom.isOfFinOrder π.ker.subtype hxfin
  have hxker : (x : Monoid.Coprod M N) ∈ π.ker := x.2
  rcases Work.OROneRel.coprod_isOfFinOrder_conj (M := M) (N := N) hxfin' with
    ⟨h, a, ha⟩ | ⟨h, b, hb⟩
  · -- a conjugate of `x` lies in the first factor
    have hmem : (Monoid.Coprod.inl a : Monoid.Coprod M N) ∈ π.ker := by
      have hconj : (Monoid.Coprod.inl a : Monoid.Coprod M N) = h⁻¹ * (x : Monoid.Coprod M N) * h := by
        rw [ha]; group
      rw [MonoidHom.mem_ker, hconj, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hxker]
      simp
    have haM : a ∈ M' := by
      have h1 : (QuotientGroup.mk' M' a, (1 : N ⧸ N')) = (1, 1) := by
        have := MonoidHom.mem_ker.mp hmem
        rwa [hπ_inl] at this
      exact (QuotientGroup.eq_one_iff a).mp (Prod.ext_iff.mp h1).1
    have hInf : IsOfFinOrder (Monoid.Coprod.inl a : Monoid.Coprod M N) := by
      have hconj := Work.OROneRel.isOfFinOrder_conj h⁻¹ (x : Monoid.Coprod M N) hxfin'
      rwa [show h⁻¹ * (x : Monoid.Coprod M N) * h⁻¹⁻¹ = Monoid.Coprod.inl a from by rw [ha]; group]
        at hconj
    have hafin : IsOfFinOrder a := by
      obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.mp hInf
      exact isOfFinOrder_iff_pow_eq_one.mpr
        ⟨n, hn, Monoid.Coprod.inl_injective (by rw [map_pow, hn1, map_one])⟩
    have ha1 : a = 1 := by
      have h1 : (⟨a, haM⟩ : ↥M') = 1 := hMtf ⟨a, haM⟩ (by
        obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.mp hafin
        exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (by simpa using hn1)⟩)
      simpa using congrArg Subtype.val h1
    exact Subtype.ext (by rw [ha, ha1]; simp)
  · -- a conjugate of `x` lies in the second factor
    have hmem : (Monoid.Coprod.inr b : Monoid.Coprod M N) ∈ π.ker := by
      have hconj : (Monoid.Coprod.inr b : Monoid.Coprod M N) = h⁻¹ * (x : Monoid.Coprod M N) * h := by
        rw [hb]; group
      rw [MonoidHom.mem_ker, hconj, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hxker]
      simp
    have hbN : b ∈ N' := by
      have h1 : ((1 : M ⧸ M'), QuotientGroup.mk' N' b) = (1, 1) := by
        have := MonoidHom.mem_ker.mp hmem
        rwa [hπ_inr b] at this
      exact (QuotientGroup.eq_one_iff b).mp (Prod.ext_iff.mp h1).2
    have hInf : IsOfFinOrder (Monoid.Coprod.inr b : Monoid.Coprod M N) := by
      have hconj := Work.OROneRel.isOfFinOrder_conj h⁻¹ (x : Monoid.Coprod M N) hxfin'
      rwa [show h⁻¹ * (x : Monoid.Coprod M N) * h⁻¹⁻¹ = Monoid.Coprod.inr b from by rw [hb]; group]
        at hconj
    have hbfin : IsOfFinOrder b := by
      obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.mp hInf
      exact isOfFinOrder_iff_pow_eq_one.mpr
        ⟨n, hn, Monoid.Coprod.inr_injective (by rw [map_pow, hn1, map_one])⟩
    have hb1 : b = 1 := by
      have h1 : (⟨b, hbN⟩ : ↥N') = 1 := hNtf ⟨b, hbN⟩ (by
        obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.mp hbfin
        exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (by simpa using hn1)⟩)
      simpa using congrArg Subtype.val h1
    exact Subtype.ext (by rw [hb, hb1]; simp)

/-! ## The letter set of a relator is finite -/

theorem relatorLetters_finite {α : Type u} (r : FreeGroup α) :
    (Work.OROneRel.relatorLetters r).Finite := by
  classical
  have h : Work.OROneRel.relatorLetters r =
      Prod.fst '' {p : α × Bool | p ∈ FreeGroup.toWord r} := by
    ext a
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨(a, b), hb, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
  rw [h]
  exact (List.finite_toSet (FreeGroup.toWord r)).image Prod.fst

/-! ## Splitting off the unused generators -/

/-- **A one-relator group is the free product of a finitely generated one-relator group and a free
group.**  The relator `r` involves only the finitely many letters in `Work.OROneRel.relatorLetters r`,
so the remaining generators split off as a free factor. -/
theorem exists_coprod_presentation {α : Type u} (r : FreeGroup α) :
    ∃ (r' : FreeGroup {a // a ∈ Work.OROneRel.relatorLetters r}) (γ : Type u),
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
        Monoid.Coprod
          (PresentedGroup ({r'} : Set (FreeGroup {a // a ∈ Work.OROneRel.relatorLetters r})))
          (FreeGroup γ)) := by
  obtain ⟨r', ⟨e⟩⟩ := Work.OROneRel.presentedGroup_iso_coprod_of_supported r
    (Work.OROneRel.relatorLetters r) (fun _ h => h)
  exact ⟨r', {a : α // a ∉ Work.OROneRel.relatorLetters r}, ⟨e⟩⟩

/-! ## Virtual torsion-freeness of free and of finite groups -/

theorem virtuallyTorsionFree_of_finite (G : Type u) [Group G] [Finite G] :
    VirtuallyTorsionFree G :=
  VirtuallyTorsionFree.of_finiteIndex ⟨⊥, inferInstance, fun x _ => Subsingleton.elim x 1⟩

theorem virtuallyTorsionFree_freeGroup (α : Type u) : VirtuallyTorsionFree (FreeGroup α) :=
  VirtuallyTorsionFree.of_finiteIndex
    ⟨⊤, inferInstance,
      IsTorsionFree.top (IsTorsionFree.of_isMulTorsionFree (G := FreeGroup α))⟩

/-! ## The terminal levels of a Magnus--Moldavanskii hierarchy -/

/-- **The terminal case, without any torsion input.**  If `r` is a terminal relator, then
`⟨α | r⟩` is free (for `r = 1`) or the free product `ℤ/k ∗ F(α∖{x})` (for `r = of x ^ k`); both
are virtually torsion-free by the free-product lemma. -/
theorem virtuallyTorsionFree_of_terminal {α : Type u} {r : FreeGroup α}
    (hr : Work.OROneRel.IsTerminalRelator r) :
    VirtuallyTorsionFree (PresentedGroup ({r} : Set (FreeGroup α))) := by
  rcases hr with h1 | ⟨x, m, hm, hrx⟩
  · rw [h1]
    exact virtuallyTorsionFree_presentedGroup_one
  · rw [hrx]
    haveI : NeZero m.natAbs := ⟨Int.natAbs_ne_zero.mpr hm⟩
    obtain ⟨e⟩ := Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod x m hm
    refine VirtuallyTorsionFree.of_mulEquiv e.symm ?_
    refine VirtuallyTorsionFree.of_mulEquiv
      (MulEquiv.coprodCongr (MulEquiv.ulift : ULift.{u, 0} (Multiplicative (ZMod m.natAbs)) ≃*
        Multiplicative (ZMod m.natAbs)) (MulEquiv.refl _)) ?_
    haveI : Finite (ULift.{u, 0} (Multiplicative (ZMod m.natAbs))) :=
      Finite.of_injective
        (Equiv.ulift : ULift.{u, 0} (Multiplicative (ZMod m.natAbs)) ≃
          Multiplicative (ZMod m.natAbs)) Equiv.ulift.injective
    exact virtuallyTorsionFree_coprod_aux
      (virtuallyTorsionFree_of_finite (ULift.{u, 0} (Multiplicative (ZMod m.natAbs))))
      (virtuallyTorsionFree_freeGroup _)

/-! ## Induction over a Magnus--Moldavanskii hierarchy -/

/-- **Virtual torsion-freeness of every level of a hierarchy.**  If `⟨α | r⟩` is a level of a
Magnus--Moldavanskii hierarchy and the HNN step hypothesis holds in the universe of the relator,
then `⟨α | r⟩` is virtually torsion-free.

The HNN step is taken in the universe of the relator itself: this is what lets the `embed` case of
`HasMMHierarchy` (Magnus's embedding of the no-zero-exponent-sum case) be handled by passing to the
subgroup `ι.range`. -/
theorem vt_of_hierarchy {α : Type u} {r : FreeGroup α} (h : Work.OROneRel.HasMMHierarchy α r)
    (hstep : HNNVirtualTorsionFree.{u}) :
    VirtuallyTorsionFree (PresentedGroup ({r} : Set (FreeGroup α))) := by
  induction h with
  | base r hterm =>
      exact virtuallyTorsionFree_of_terminal hterm
  | step r r' hlt hh A B hA hB φ e ih =>
      exact VirtuallyTorsionFree.of_mulEquiv e.symm
        (hstep.step (PresentedGroup (Set.singleton r')) ih A B φ)
  | embed r r' hrec ι hι ih =>
      exact VirtuallyTorsionFree.of_mulEquiv (MonoidHom.ofInjective hι).symm
        (Work.ORLocInd.Virtual.virtuallyTorsionFree_subgroup ih ι.range)

/-! ## The main theorem -/

theorem oneRelator_virtually_torsionFree {G : Type*} [Group G] (hG : Group.OneRelator G)
    (hstep : Work.ORLocInd.HNNVirtualTorsionFree.{u})
    (hKMS : ∀ {α : Type u} (r : FreeGroup α), Work.OROneRel.KMSTorsionAt r)
    (hMM : ∀ {α : Type u} (r : FreeGroup α), Work.OROneRel.MagnusMoldavanskiiAt r) :
    Work.ORLocInd.VirtuallyTorsionFree G := by
  obtain ⟨α, r, ⟨eG⟩⟩ := hG
  obtain ⟨r', γ, ⟨edecomp⟩⟩ := exists_coprod_presentation r
  let Z := {a : α // a ∈ Work.OROneRel.relatorLetters r}
  haveI : Fintype Z := (relatorLetters_finite r).fintype
  let ι : Z ≃ Fin (Fintype.card Z) := Fintype.equivFin Z
  let r₀ : FreeGroup (Fin (Fintype.card Z)) := FreeGroup.freeGroupCongr ι r'
  -- `⟨Fin n | r₀⟩` is virtually torsion-free
  have hVT₀ : VirtuallyTorsionFree
      (PresentedGroup ({r₀} : Set (FreeGroup (Fin (Fintype.card Z))))) := by
    -- the same relator, over the universe of `hMM`
    let r₃ : FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z))) :=
      FreeGroup.freeGroupCongr (Equiv.ulift.symm) r₀
    have hmm₃ : Work.OROneRel.MagnusMoldavanskiiAt r₃ := hMM r₃
    obtain ⟨eP₃⟩ : Nonempty (PresentedGroup ({r₀} : Set (FreeGroup (Fin (Fintype.card Z)))) ≃*
        PresentedGroup ({r₃} : Set (FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z)))))) :=
      presentedGroup_iso_of_mulEquiv
        (FreeGroup.freeGroupCongr (Equiv.ulift.symm : Fin (Fintype.card Z) ≃
          ULift.{u, 0} (Fin (Fintype.card Z)))) r₀
    by_cases hr₃ : r₃ = 1
    · -- the relator is trivial, so the group is free
      refine VirtuallyTorsionFree.of_mulEquiv eP₃.symm ?_
      rw [hr₃]
      exact virtuallyTorsionFree_presentedGroup_one
    · -- the hierarchy of a cyclically reduced conjugate
      obtain ⟨s₃, hs₃, hs₃ne, ⟨eiso⟩⟩ := Work.OROneRel.exists_cyclicallyReduced_conjugate r₃ hr₃
      have hh : Work.OROneRel.HasMMHierarchy (ULift.{u, 0} (Fin (Fintype.card Z))) s₃ :=
        (hMM s₃) hs₃ hs₃ne
      -- the same relator again, over the universe of `hstep`
      let r₄ : FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z))) :=
        FreeGroup.freeGroupCongr (Equiv.ulift.symm) r₀
      obtain ⟨eP₄⟩ : Nonempty (PresentedGroup ({r₀} : Set (FreeGroup (Fin (Fintype.card Z)))) ≃*
          PresentedGroup ({r₄} : Set (FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z)))))) :=
        presentedGroup_iso_of_mulEquiv
          (FreeGroup.freeGroupCongr (Equiv.ulift.symm : Fin (Fintype.card Z) ≃
            ULift.{u, 0} (Fin (Fintype.card Z)))) r₀
      let ee : PresentedGroup ({s₃} : Set (FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z))))) ≃*
          PresentedGroup ({r₄} : Set (FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z))))) :=
        (eiso.symm.trans eP₃.symm).trans eP₄
      have hVT₃ : VirtuallyTorsionFree
          (PresentedGroup ({s₃} : Set (FreeGroup (ULift.{u, 0} (Fin (Fintype.card Z)))))) :=
        vt_of_hierarchy hh hstep
      exact VirtuallyTorsionFree.of_mulEquiv eP₃.symm
        (VirtuallyTorsionFree.of_mulEquiv eiso.symm hVT₃)
  -- back to the finitely generated factor, then the free product, then `G`
  obtain ⟨eP'⟩ : Nonempty (PresentedGroup ({r'} : Set (FreeGroup Z)) ≃*
      PresentedGroup ({r₀} : Set (FreeGroup (Fin (Fintype.card Z))))) :=
    presentedGroup_iso_of_mulEquiv (FreeGroup.freeGroupCongr ι) r'
  have hVT_P : VirtuallyTorsionFree (PresentedGroup ({r'} : Set (FreeGroup Z))) :=
    VirtuallyTorsionFree.of_mulEquiv eP'.symm hVT₀
  have hVT_coprod : VirtuallyTorsionFree
      (Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup Z))) (FreeGroup γ)) :=
    virtuallyTorsionFree_coprod_aux hVT_P (virtuallyTorsionFree_freeGroup γ)
  exact VirtuallyTorsionFree.of_mulEquiv eG
    (VirtuallyTorsionFree.of_mulEquiv edecomp.symm hVT_coprod)

end Work.ORLocInd.Assembly
