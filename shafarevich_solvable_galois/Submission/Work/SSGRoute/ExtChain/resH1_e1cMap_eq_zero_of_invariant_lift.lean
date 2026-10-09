import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero

/-!
# The extension criterion for `resH1_D (e1cMap R ·) = 0` at an *arbitrary* subgroup, with no
`Finite R.V` hypothesis

The workspace's `ExtChain.resH1_e1cMap_eq_zero_of_extension` (proved, sorry-free) states the useful
direction of the extension criterion — a `D`-invariant lift `Φ : (E1cF R).V → Ωˣ` of the
`Kˣ`-valued coefficient data kills the restricted `E1c` class — but it carries the hypothesis
`[Finite R.V]`, which comes from the dualised short exact sequence `PT.e1aSESgen R` (whose
construction needs a *finite* index type for the free cover).

That hypothesis is **never satisfiable for the coefficient this lane actually needs**: the syzygy
`R = ker (freeCover N)` of the finite module `N = e1aN0 p k Ω K T E` has carrier
`N.V →₀ ℤ[G]`, which is a *finitely generated* (indeed free of rank `|N.V| · |G|`) `ℤ`-module
(`ExtChain.freeCoverSES_finite`, `ExtChain.freeCoverSES_lattice`) but an **infinite type**.  So the
criterion as recorded cannot be instantiated on `R`, and the whole local-comparison lane had to go
through the cocycle-level argument of
`ExtChain/resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero.lean` instead.

This file removes the obstruction: the same conclusion is derived for an arbitrary subgroup `D`,
using only `[Module.Finite ℤ R.V]`, by the cocycle-level route of the `zpowers` case (whose two
involution hypotheses are demonstrably dead — see the review of this statement).  The engine is
`resZ1_subgroup_mem_B1`, the `D`-general form of that file's `resZ1_zpowers_mem_B1`.

Consequences for the lane: the extension criterion is now available at the canonical syzygy, so
every future proof of the finite-place input can be phrased as "produce a `D_A`-invariant lift"
without leaving the `Ext`/`H¹` vocabulary.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- The coboundary of an arbitrary subgroup, in the explicit `.smul` shape.  The `zpowers` case is
`resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero.d0_zpowers_apply`; the proof is the same
because it only uses `Subgroup.smul_def` and `smul_homCoind_eq_algEquiv`. -/
theorem d0_subgroup_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (D : Subgroup (Ω ≃ₐ[k] Ω))
    (m : homCoind k Ω K R) (hh : ↥D) :
    (Work.GroupCohomology.d0 (↥D) (homCoind k Ω K R) m) hh
      = (homCoind.instDistribMulActionAlgEquiv R).smul (hh : Ω ≃ₐ[k] Ω) m - m := by
  rw [Work.GroupCohomology.d0_apply, Subgroup.smul_def,
    smul_homCoind_eq_algEquiv (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) m]

/-- An element of `E1cN R` fixed by the subgroup `↥D` is fixed by the explicit action of every
element of `D` (the `D`-general form of
`resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero.algEquiv_smul_eq_of_mem_H0_zpowers`). -/
theorem algEquiv_smul_eq_of_mem_H0_subgroup (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (γ : Ω ≃ₐ[k] Ω) (hγ : γ ∈ D)
    (z : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hz : z ∈ Work.AbsoluteKummer.H0 ↥D (E1cN (k := k) (Ω := Ω) (K := K) R)) :
    (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul γ z = z := by
  have h := (Work.GroupCohomology.mem_invariants (↥D)
    (E1cN (k := k) (Ω := Ω) (K := K) R) z).mp hz ⟨γ, hγ⟩
  rw [Subgroup.smul_def] at h
  exact h

/-- **The coboundary engine at an arbitrary subgroup.**  If `m` is a lift of `liftOf c - z' - Φ`,
where `z'` is `Γ`-invariant and `Φ` is `↥D`-invariant, then the restriction of the cocycle `c` to
`↥D` is a coboundary.  This is `resZ1_zpowers_mem_B1` with the subgroup `⟨σ⟩` replaced by an
arbitrary `D` (no hypothesis on `D` is used). -/
theorem resZ1_subgroup_mem_B1 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)))
    (Φ : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hΦinv : Φ ∈ Work.AbsoluteKummer.H0 ↥D (E1cN (k := k) (Ω := Ω) (K := K) R))
    (z' : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)))
    (m : homCoind k Ω K R)
    (hm : iotaH (k := k) (Ω := Ω) (K := K) R m
      = liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ) :
    ((Work.SSGRoute.PT.H2Fin.resZ1 D (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥D) (homCoind k Ω K R)) :
      (↥D) → homCoind k Ω K R)
      ∈ Work.AbsoluteKummer.B1 (↥D) (homCoind k Ω K R) := by
  rw [Work.AbsoluteKummer.mem_B1_iff]
  refine ⟨m, ?_⟩
  funext hh
  apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
  have h1 : iotaH (k := k) (Ω := Ω) (K := K) R
      ((Work.GroupCohomology.d0 (↥D) (homCoind k Ω K R) m) hh)
      = (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω)
          (iotaH (k := k) (Ω := Ω) (K := K) R m)
        - iotaH (k := k) (Ω := Ω) (K := K) R m := by
    rw [d0_subgroup_apply (k := k) (Ω := Ω) (K := K) R D m hh, map_sub]
    congr 1
    exact iotaH_algEquiv_smul (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) m
  rw [h1]
  have h2 : iotaH (k := k) (Ω := Ω) (K := K) R
      ((Work.SSGRoute.PT.H2Fin.resZ1 D (homCoind k Ω K R) c :
          (↥D) → homCoind k Ω K R) hh)
      = (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω)
          (liftOf (k := k) (Ω := Ω) (K := K) R c)
        - liftOf (k := k) (Ω := Ω) (K := K) R c := by
    rw [show ((Work.SSGRoute.PT.H2Fin.resZ1 D (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥D) (homCoind k Ω K R)) :
          (↥D) → homCoind k Ω K R) hh
        = (c : (Ω ≃ₐ[k] Ω) → homCoind k Ω K R) (hh : Ω ≃ₐ[k] Ω) from rfl]
    have hmap : iotaH (k := k) (Ω := Ω) (K := K) R
        ((c : (Ω ≃ₐ[k] Ω) → homCoind k Ω K R) (hh : Ω ≃ₐ[k] Ω))
        = ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
            (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
          ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
            (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R)
          (hh : Ω ≃ₐ[k] Ω) :=
      (Work.AbsoluteKummer.mapZ1_apply (iotaH (k := k) (Ω := Ω) (K := K) R)
        (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c (hh : Ω ≃ₐ[k] Ω)).symm
    have hspec := congrFun (liftOf_spec (k := k) (Ω := Ω) (K := K) R c) (hh : Ω ≃ₐ[k] Ω)
    rw [Work.GroupCohomology.d0_apply] at hspec
    exact hmap.trans hspec.symm
  rw [h2, hm]
  rw [show liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      = liftOf (k := k) (Ω := Ω) (K := K) R c - (z'.1 + Φ) from by abel]
  rw [dma_smul_sub (homCoind.instDistribMulActionAlgEquiv (E1cF R)) (hh : Ω ≃ₐ[k] Ω)
      (liftOf (k := k) (Ω := Ω) (K := K) R c) (z'.1 + Φ),
    dma_smul_add (homCoind.instDistribMulActionAlgEquiv (E1cF R)) (hh : Ω ≃ₐ[k] Ω) z'.1 Φ,
    algEquiv_smul_eq_of_mem_H0 (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) z'.1 z'.2,
    algEquiv_smul_eq_of_mem_H0_subgroup (k := k) (Ω := Ω) (K := K) R D
      (hh : Ω ≃ₐ[k] Ω) hh.2 Φ hΦinv]
  abel

/-- **The extension criterion at an arbitrary subgroup, with no `Finite R.V`.**  If
`Φ ∈ H⁰(↥D, Hom_ℤ(F_R, Ωˣ))` restricts along the canonical syzygy inclusion `kappa R` to the
`Ωˣ`-image of the `Kˣ`-valued data `w`, then the `E1c` class `e1cMap R (PhiE R w)` restricts to `0`
on `D`.

This is `ExtChain.resH1_e1cMap_eq_zero_of_extension` with `[Finite R.V]` dropped: same conclusion,
same two hypotheses, only `[Module.Finite ℤ R.V]` — exactly the hypothesis that the canonical
syzygy of the `himg` lane satisfies (`ExtChain.freeCoverSES_finite`). -/
theorem resH1_e1cMap_eq_zero_of_invariant_lift
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (w : CategoryTheory.Abelian.Ext.{0}
      (E1cR1 (k := k) (Ω := Ω) (K := K) R) (SSGRoute.PTExt.unitsK k K) 0)
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (Φ : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥D (E1cN (k := k) (Ω := Ω) (K := K) R))
    (hκ : AddMonoidHom.comp Φ (kappa (k := k) (Ω := Ω) (K := K) R)
      = (PsiEMap (k := k) (Ω := Ω) (K := K)
          (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1) :
    Work.SSGRoute.PT.H2Fin.resH1 D (homCoind k Ω K R)
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)) = 0 := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  have hpiΦ : piH (k := k) (Ω := Ω) (K := K) R Φ
      = (PsiEMap (k := k) (Ω := Ω) (K := K)
          (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 := by
    rw [show piH (k := k) (Ω := Ω) (K := K) R Φ
        = AddMonoidHom.comp Φ (kappa (k := k) (Ω := Ω) (K := K) R) from rfl]
    exact hκ
  have hbeta : betaH (k := k) (Ω := Ω) (K := K) R
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w))
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w) := by
    rw [← betaEquiv_apply, e1cMap_Phi, AddEquiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)).subtype)
    (e1cMap (k := k) (Ω := Ω) (K := K) R
      (PhiE (k := k) (Ω := Ω) (K := K) R w))
  have hbc : QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
        (betaRaw (k := k) (Ω := Ω) (K := K) R c)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w) := by
    rw [← hbeta, ← hc, betaH_mk]
  have hmem : (betaRaw (k := k) (Ω := Ω) (K := K) R c)
      - (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 (k := k) (Ω := Ω) (K := K) R) w)
      ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range :=
    QuotientAddGroup.eq_iff_sub_mem.mp hbc
  obtain ⟨z', hz'⟩ := AddMonoidHom.mem_range.mp hmem
  have hz'' : piH (k := k) (Ω := Ω) (K := K) R z'.1
      = piH (k := k) (Ω := Ω) (K := K) R
          (liftOf (k := k) (Ω := Ω) (K := K) R c)
        - (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 := by
    have hzv := congrArg Subtype.val hz'
    simpa [piH0, Work.GroupCohomology.mapH0, betaRaw] using hzv
  have hker : liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      ∈ (piH (k := k) (Ω := Ω) (K := K) R).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, hz'', hpiΦ]
    abel
  have hker' : liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      ∈ (iotaH (k := k) (Ω := Ω) (K := K) R).range := by
    rw [iotaH_range_eq_piH_ker]
    exact hker
  obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp hker'
  have hB1 : ((Work.SSGRoute.PT.H2Fin.resZ1 D (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥D) (homCoind k Ω K R)) :
      (↥D) → homCoind k Ω K R)
      ∈ Work.AbsoluteKummer.B1 (↥D) (homCoind k Ω K R) :=
    resZ1_subgroup_mem_B1 (k := k) (Ω := Ω) (K := K) R D c Φ hΦ z' m hm
  rw [show e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (homCoind k Ω K R) c from hc.symm]
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.H1π_eq_zero_iff]
  exact hB1

/-- **The finite-place restriction square of the `E1c` dictionary.**

This is the finite-place analogue of the *proved*
`resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero.`
`resH1_zpowers_e1cMap_eq_zero_of_extRes_eq_zero`: if the restriction of the `PhiE`-generator of `w`
to a subgroup `Dq` of `G = Gal(K/k)` vanishes, then the `E1c` class of that generator restricts to
`0` on every subgroup `D ≤ Γ = Gal(Ω/k)` whose image `res k K '' D` lies in `Dq`.

The proof produces the `D`-invariant Ωˣ-valued lift of the coefficient data out of the
`Dq`-equivariant `Kˣ`-valued one (`exists_lift_of_extRes_PhiE_eq_zero`) by the `Kˣ ↪ Ωˣ`-extension
`unitsAddToOmega`: for `δ ∈ D`, `Φ (ρ (res δ) v) = unitsAddToOmega (Ψ (ρ (res δ) v)) =
unitsAddToOmega ((res δ) • Ψ v) = δ • Φ v`, using the `Dq`-equivariance of `Ψ` and the fact that its
values lie in `K` (`smul_unitsAddToOmega`).  The vanishing is then the finite-place extension
criterion `resH1_e1cMap_eq_zero_of_invariant_lift`.

For `D = decomp k A` (`A` a finite place, `Dq = res k K '' decomp k A`) this is the "level-change
square" of the finite-place `himg` input, in the direction that is *true*; the notes measure that
the *input* form needed by the lane is the weaker coefficient-changed statement
`cc_{(K·Ω^{D_A})ˣ} (res_{D_q} z) = 0`, which is *not* implied by `extRes_{D_q} z = 0`. -/
theorem resH1_e1cMap_eq_zero_of_extRes_map_eq_zero
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (Dq : Subgroup (K ≃ₐ[k] K))
    (hD : ∀ δ ∈ D, SSGRoute.res k K δ ∈ Dq)
    (w : CategoryTheory.Abelian.Ext.{0}
      (E1cR1 (k := k) (Ω := Ω) (K := K) R) (SSGRoute.PTExt.unitsK k K) 0)
    (h : SSGRoute.PTExt.extRes Dq.subtype
      (PhiE (k := k) (Ω := Ω) (K := K) R w) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 D (homCoind k Ω K R)
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)) = 0 := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_lift_of_extRes_PhiE_eq_zero
    (k := k) (Ω := Ω) (K := K) R Dq w h
  let Φ : E1cN (k := k) (Ω := Ω) (K := K) R :=
    (unitsAddToOmega (k := k) (Ω := Ω) (K := K)).comp (Rep.Hom.hom Ψ).toAddMonoidHom
  have hΦκ : ∀ x : (E1cR1 (k := k) (Ω := Ω) (K := K) R).V,
      Φ (kappa (k := k) (Ω := Ω) (K := K) R x)
        = (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 x := by
    intro x
    show unitsAddToOmega (k := k) (Ω := Ω) (K := K)
      (Rep.Hom.hom Ψ (kappa (k := k) (Ω := Ω) (K := K) R x)) = _
    rw [PsiEMap_apply_toCoindH0, Work.SSGRoute.toCoindH0_apply,
      unitsAddToOmega_apply, hΨ x]
  refine resH1_e1cMap_eq_zero_of_invariant_lift (k := k) (Ω := Ω) (K := K) R w D Φ ?_ ?_
  · rw [Work.GroupCohomology.mem_invariants]
    intro hh
    change (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω) Φ = Φ
    apply AddMonoidHom.ext
    intro v
    rw [smul_conj_homCoindFreeT]
    have key : ∀ u : (E1cF R).V,
        Φ ((E1cF R).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u)
          = homCoind.smulHom (k := k) (Ω := Ω) (hh : Ω ≃ₐ[k] Ω) (Φ u) := by
      intro u
      have heq : Rep.Hom.hom Ψ ((E1cF R).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u)
          = (SSGRoute.PTExt.unitsK k K).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))
              (Rep.Hom.hom Ψ u) :=
        Rep.hom_comm_apply Ψ ⟨SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω), hD _ hh.2⟩ u
      show unitsAddToOmega (k := k) (Ω := Ω) (K := K)
          (Rep.Hom.hom Ψ ((E1cF R).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u))
        = homCoind.smulHom (k := k) (Ω := Ω) (hh : Ω ≃ₐ[k] Ω)
            (unitsAddToOmega (k := k) (Ω := Ω) (K := K) (Rep.Hom.hom Ψ u))
      rw [heq, Work.SSGRoute.homCoind.smulHom_apply,
        ← smul_unitsAddToOmega (k := k) (Ω := Ω) (K := K)
            (hh : Ω ≃ₐ[k] Ω) (Rep.Hom.hom Ψ u)]
      rfl
    rw [← key ((E1cF R).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))⁻¹ v)]
    congr 1
    first
      | (rw [← Module.End.mul_apply, mul_inv_cancel, Module.End.one_apply])
      | (rw [← Module.End.mul_apply,
            ← map_mul (E1cF R).ρ (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))
              (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))⁻¹,
            mul_inv_cancel, map_one, Module.End.one_apply])
  · have hpi : piH (k := k) (Ω := Ω) (K := K) R Φ
        = (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 :=
      AddMonoidHom.ext hΦκ
    rw [← piH_apply]
    exact hpi

end

end Work.SSGRoute.ExtChain
