import Mathlib
import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.RatModZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Cohomological vanishing from a single free homology group

Let `C` be a chain complex of `ℤ`-modules whose terms are projective (for the relative singular
chains `C_*(X,A)` this is `Work.Cohomology.relChainsProjective`).  If the `(n+1)`-st homology of
`C` vanishes and the `n`-th homology is free, then the `(n+1)`-st cohomology of the dual complex
`Hom_ℤ(C,ℤ)` vanishes: `H^{n+1}(Hom(C,ℤ)) = 0`.

This is the universal coefficient theorem in the one degree where both of its terms vanish
(`Hom(H_{n+1},ℤ) = 0` because `H_{n+1} = 0`, and `Ext(H_n,ℤ) = 0` because `H_n` is free), proved
here without ever defining `Ext`: a cocycle `f : C_{n+1} → ℤ` kills the `(n+1)`-cycles, hence
factors as `φ ∘ ∂` through the boundaries, and `φ` is extended to `C_n` by first passing to `ℚ`
(injective), splitting off the rational functional on the cycles that is only defined modulo `ℤ`,
and correcting — this is where the freeness of `H_n` enters, through the projectivity of
`H_n` (a free module) and of the quotient `Z_n ⧸ B_n`.

## Main results

* `Work.Cohomology.ratIntCorrection` — correction modulo `ℤ` of a `ℚ`-valued functional;
* `Work.Cohomology.exists_lift_of_cocycle` — every cocycle of the dual complex is a coboundary;
* `Work.Cohomology.subsingleton_dual_homology_of_free` — `H^{n+1}(Hom(C,ℤ)) = 0`;
* `Work.Cohomology.relComplex_vanishing_of_homology_free` — the requested statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

theorem projective_quot_cycles (E : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : Module.Free ℤ (↥(E.homology k))) :
    Module.Projective ℤ (↥(uctZ E k) ⧸ uctH E k) := by
  obtain ⟨e⟩ := homology_iso_H E k
  haveI : Module.Free ℤ (↥(E.homology k)) := h
  exact Module.Projective.of_equiv' (uctIsoToLinearEquiv e)

theorem ker_eq_range_of_isZero_homology (E : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : CategoryTheory.Limits.IsZero (E.homology k)) :
    LinearMap.ker (E.d k (k - 1)).hom = LinearMap.range (E.d (k + 1) k).hom := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxZ : x ∈ uctZ E k := hx
    obtain ⟨e⟩ := homology_iso_H E k
    haveI : Subsingleton ↥(E.homology k) := ModuleCat.isZero_iff_subsingleton.mp h
    have hz : CategoryTheory.Limits.IsZero (ModuleCat.of ℤ (↥(uctZ E k) ⧸ uctH E k)) :=
      CategoryTheory.Limits.IsZero.of_iso h e.symm
    haveI : Subsingleton (↥(uctZ E k) ⧸ uctH E k) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    have h0 : (uctH E k).mkQ ⟨x, hxZ⟩ = 0 := by
      have := @Subsingleton.elim _ this ((uctH E k).mkQ ⟨x, hxZ⟩) 0
      simpa using this
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact (mem_uctH E k ⟨x, hxZ⟩).mp h0
  · intro x hx
    exact uctB_le_uctZ E k hx

theorem ratIntCorrection (E : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (n : ℕ)
    (hproj : Module.Projective ℤ (↥(uctZ E n) ⧸ uctH E n))
    (hP : Module.Projective ℤ (↥(E.X (n - 1))))
    (b : (↥(E.X n)) →ₗ[ℤ] ℚ)
    (hb : ∀ x ∈ uctB E n, b x ∈ ratIntSub) :
    ∃ w : (↥(E.X n)) →ₗ[ℤ] ℚ,
      (∀ x, Submodule.mkQ ratIntSub (w x) = Submodule.mkQ ratIntSub (b x)) ∧
      (∀ x ∈ uctB E n, w x = 0) := by
  haveI := hproj
  -- the reduction of `b` modulo `ℤ`
  set d : (↥(E.X n)) →ₗ[ℤ] qZ := (Submodule.mkQ ratIntSub).comp b with hd
  have hdB : ∀ x ∈ uctB E n, d x = 0 := by
    intro x hx
    simp only [hd, LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hb x hx
  -- restricted to the cycles it kills the boundaries
  set dZ : ↥(uctZ E n) →ₗ[ℤ] qZ := d.comp (uctZ E n).subtype with hdZdef
  have hdZ_coe : ∀ y : ↥(uctZ E n), dZ y = d y := fun _ => rfl
  have hdZ : ∀ x ∈ uctH E n, dZ x = 0 := by
    intro x hx
    rw [hdZ_coe x]
    exact hdB x ((mem_uctH E n x).mp hx)
  -- so it factors through the quotient of cycles by boundaries
  have hdZker : uctH E n ≤ LinearMap.ker dZ := by
    intro x hx
    rw [LinearMap.mem_ker]
    exact hdZ x hx
  set dZbar : (↥(uctZ E n) ⧸ uctH E n) →ₗ[ℤ] qZ := (uctH E n).liftQ dZ hdZker with hdZbardef
  have hdZbar_apply : ∀ x : ↥(uctZ E n), dZbar ((uctH E n).mkQ x) = dZ x := by
    intro x
    simp only [hdZbardef, Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- and lifts to `ℚ`, using the projectivity of `Hₙ`
  obtain ⟨ψbar, hψbar⟩ := Module.projective_lifting_property (Submodule.mkQ ratIntSub) dZbar
    (Submodule.mkQ_surjective ratIntSub)
  set ψ : ↥(uctZ E n) →ₗ[ℤ] ℚ := ψbar.comp (uctH E n).mkQ with hψdef
  have hψ : ∀ x : ↥(uctZ E n), Submodule.mkQ ratIntSub (ψ x) = dZ x := by
    intro x
    have h := LinearMap.congr_fun hψbar ((uctH E n).mkQ x)
    simp only [LinearMap.comp_apply] at h
    rw [hψdef, LinearMap.comp_apply, h, hdZbar_apply x]
  have hψH : ∀ x ∈ uctH E n, ψ x = 0 := by
    intro x hx
    have hx0 : (uctH E n).mkQ x = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hx
    simp only [hψdef, LinearMap.comp_apply, hx0, map_zero]
  -- extend it to the whole of `E.X n`
  haveI : Module.Injective ℤ ℚ := injective_rat
  obtain ⟨w0, hw0⟩ := Module.Injective.out (f := (uctZ E n).subtype)
    (fun a b h => Subtype.ext h) ψ
  have hw0_coe : ∀ y : ↥(uctZ E n), w0 (y : ↥(E.X n)) = ψ y := fun y => hw0 y
  -- the difference `mkQ ∘ w0 - d` vanishes on the cycles
  set e0 : (↥(E.X n)) →ₗ[ℤ] qZ := (Submodule.mkQ ratIntSub).comp w0 - d with he0
  have he0ker : LinearMap.ker (E.d n (n - 1)).hom ≤ LinearMap.ker e0 := by
    intro x hx
    have hxZ : x ∈ uctZ E n := hx
    rw [LinearMap.mem_ker]
    simp only [he0, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hw0_coe ⟨x, hxZ⟩, hψ ⟨x, hxZ⟩, hdZ_coe ⟨x, hxZ⟩]
    simp
  -- factor through the range of `E.d n (n-1)`
  set e1 : (↥(E.X n) ⧸ LinearMap.ker (E.d n (n - 1)).hom) →ₗ[ℤ] qZ :=
    (LinearMap.ker (E.d n (n - 1)).hom).liftQ e0 he0ker with he1
  set η0 : ↥(LinearMap.range (E.d n (n - 1)).hom) →ₗ[ℤ] qZ :=
    e1.comp (LinearMap.quotKerEquivRange (E.d n (n - 1)).hom).symm.toLinearMap with hη0def
  have hη0 : ∀ x, η0 ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ = e0 x := by
    intro x
    simp only [hη0def, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearMap.quotKerEquivRange_symm_apply_image _ x ⟨x, rfl⟩]
    simp only [he1, Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- extend `η0` to `E.X (n-1)`
  haveI : Module.Injective ℤ qZ := injective_qZ
  obtain ⟨η1, hη1⟩ := Module.Injective.out (f := (LinearMap.range (E.d n (n - 1)).hom).subtype)
    (fun a b h => Subtype.ext h) η0
  have hη1_coe : ∀ y : ↥(LinearMap.range (E.d n (n - 1)).hom),
      η1 (y : ↥(E.X (n - 1))) = η0 y := fun y => hη1 y
  have hη1_apply : ∀ x, η1 ((E.d n (n - 1)).hom x) = e0 x := by
    intro x
    exact (hη1 (⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ : ↥(LinearMap.range (E.d n (n - 1)).hom))).trans
      (hη0 x)
  haveI : Module.Projective ℤ (↥(E.X (n - 1))) := hP
  obtain ⟨η2, hη2⟩ := Module.projective_lifting_property (f := Submodule.mkQ ratIntSub)
    (g := η1) (Submodule.mkQ_surjective ratIntSub)
  have hη2_coe : ∀ y : ↥(E.X (n - 1)), Submodule.mkQ ratIntSub (η2 y) = η1 y := by
    intro y
    have h := LinearMap.congr_fun hη2 y
    simpa [LinearMap.comp_apply] using h
  refine ⟨w0 - η2.comp (E.d n (n - 1)).hom, ?_, ?_⟩
  · intro x
    have h2 : η1 ((E.d n (n - 1)).hom x) = e0 x := hη1_apply x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hη2_coe, h2]
    simp only [he0, LinearMap.sub_apply, LinearMap.comp_apply]
    abel
  · intro x hx
    change x ∈ LinearMap.range (E.d (n + 1) n).hom at hx
    obtain ⟨y, rfl⟩ := hx
    have hxZ : (E.d (n + 1) n).hom y ∈ uctZ E n := uctB_le_uctZ E n ⟨y, rfl⟩
    have hxH : (⟨(E.d (n + 1) n).hom y, hxZ⟩ : ↥(uctZ E n)) ∈ uctH E n :=
      (mem_uctH E n _).mpr ⟨y, rfl⟩
    have hw0y : w0 ((E.d (n + 1) n).hom y) = 0 := by
      show w0 ((uctZ E n).subtype ⟨(E.d (n + 1) n).hom y, hxZ⟩) = 0
      rw [hw0 (⟨(E.d (n + 1) n).hom y, hxZ⟩ : ↥(uctZ E n)), hψH _ hxH]
    have hdy : (E.d n (n - 1)).hom ((E.d (n + 1) n).hom y) = 0 := by
      have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 1) n (n - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h y
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hw0y, hdy, map_zero, sub_zero]
theorem exists_lift_of_cocycle (E : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (n : ℕ)
    (h1 : CategoryTheory.Limits.IsZero (E.homology (n + 1)))
    (h0 : Module.Free ℤ (↥(E.homology n)))
    (hP : Module.Projective ℤ (↥(E.X (n - 1))))
    (f : (↥(E.X (n + 1))) →ₗ[ℤ] ℤ)
    (hf : f.comp (E.d (n + 2) (n + 1)).hom = 0) :
    ∃ g : (↥(E.X n)) →ₗ[ℤ] ℤ, g.comp (E.d (n + 1) n).hom = f := by
  have hker : LinearMap.ker (E.d (n + 1) n).hom = LinearMap.range (E.d (n + 2) (n + 1)).hom :=
    ker_eq_range_of_isZero_homology E (n + 1) h1
  -- `f` kills the cycles
  have hfker : LinearMap.ker (E.d (n + 1) n).hom ≤ LinearMap.ker f := by
    rw [hker]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun hf y
    simpa [LinearMap.comp_apply] using h
  -- so it factors through the boundaries
  let φ : ↥(LinearMap.range (E.d (n + 1) n).hom) →ₗ[ℤ] ℤ :=
    ((LinearMap.ker (E.d (n + 1) n).hom).liftQ f hfker).comp
      (LinearMap.quotKerEquivRange (E.d (n + 1) n).hom).symm.toLinearMap
  have hφ : ∀ x, φ ⟨(E.d (n + 1) n).hom x, ⟨x, rfl⟩⟩ = f x := by
    intro x
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearMap.quotKerEquivRange_symm_apply_image _ x ⟨x, rfl⟩]
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- extend the resulting functional on the boundaries to a `ℚ`-valued functional
  haveI : Module.Injective ℤ ℚ := injective_rat
  obtain ⟨b, hb⟩ := Module.Injective.out (f := (LinearMap.range (E.d (n + 1) n).hom).subtype)
    (fun a b h => Subtype.ext h)
    ((LinearMap.toSpanSingleton ℤ ℚ (1 : ℚ)).comp φ)
  have hcast : ∀ z : ℤ, (LinearMap.toSpanSingleton ℤ ℚ (1 : ℚ)) z = (z : ℚ) := by
    intro z
    rw [LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one]
  have hb_apply : ∀ (y : ↥(E.X n)) (hy : y ∈ LinearMap.range (E.d (n + 1) n).hom),
      b y = (φ ⟨y, hy⟩ : ℚ) := by
    intro y hy
    have h := hb (⟨y, hy⟩ : ↥(LinearMap.range (E.d (n + 1) n).hom))
    simpa [LinearMap.comp_apply, hcast] using h
  have hbZ : ∀ x ∈ uctB E n, b x ∈ ratIntSub := by
    intro x hx
    change x ∈ LinearMap.range (E.d (n + 1) n).hom at hx
    obtain ⟨y, rfl⟩ := hx
    exact mem_ratIntSub.mpr ⟨f y, by rw [hb_apply _ ⟨y, rfl⟩, hφ y]⟩
  -- correct it modulo `ℤ` so that it vanishes on the boundaries
  obtain ⟨w, hw1, hw2⟩ := ratIntCorrection E n (projective_quot_cycles E n h0) hP b hbZ
  -- the resulting difference is integral, giving the desired functional
  let g₀ : (↥(E.X n)) →ₗ[ℤ] ↥ratIntSub := (b - w).codRestrict ratIntSub (by
    intro x
    rw [← mkQ_qZ_eq_zero, LinearMap.sub_apply, map_sub, hw1 x]
    simp)
  let g : (↥(E.X n)) →ₗ[ℤ] ℤ := intEquiv.symm.toLinearMap.comp g₀
  have hg : ∀ x, ((g x : ℤ) : ℚ) = (b - w) x := by
    intro x
    show ((intEquiv (g x) : ↥ratIntSub) : ℚ) = (b - w) x
    rw [show intEquiv (g x) = g₀ x from LinearEquiv.apply_symm_apply intEquiv (g₀ x)]
    rfl
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  apply Int.cast_injective (α := ℚ)
  rw [LinearMap.comp_apply, hg ((E.d (n + 1) n).hom x)]
  have hbx : b ((E.d (n + 1) n).hom x) = (f x : ℚ) := by
    rw [hb_apply _ ⟨x, rfl⟩, hφ x]
  have hwx : w ((E.d (n + 1) n).hom x) = 0 := hw2 _ ⟨x, rfl⟩
  simp only [LinearMap.sub_apply, hbx, hwx, sub_zero]

theorem subsingleton_dual_homology_of_free (E : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (n : ℕ)
    (h1 : CategoryTheory.Limits.IsZero (E.homology (n + 1)))
    (h0 : Module.Free ℤ (↥(E.homology n)))
    (hP : Module.Projective ℤ (↥(E.X (n - 1)))) :
    Subsingleton ((dualComplex ℤ E).homology (n + 1)) := by
  have hrange : LinearMap.range ((dualComplex ℤ E).d n (n + 1)).hom
      = LinearMap.ker ((dualComplex ℤ E).d (n + 1) (n + 2)).hom := by
    apply le_antisymm
    · rintro f ⟨g, rfl⟩
      rw [LinearMap.mem_ker, uct_d_apply, uct_d_apply]
      apply LinearMap.ext
      intro x
      have h : (E.d (n + 1) n).hom ((E.d (n + 2) (n + 1)).hom x) = 0 := by
        have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 2) (n + 1) n)
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact LinearMap.congr_fun h x
      have h2 : (dval E n g) ((E.d (n + 1) n).hom ((E.d (n + 2) (n + 1)).hom x)) = 0 := by
        rw [h, map_zero]
      simpa [dval, LinearMap.comp_apply] using h2
    · intro f hf
      rw [LinearMap.mem_ker, uct_d_apply] at hf
      have hf' : f.comp (E.d (n + 2) (n + 1)).hom = 0 := by
        ext x
        simpa [dval, LinearMap.comp_apply] using LinearMap.congr_fun hf x
      obtain ⟨g, hg⟩ := exists_lift_of_cocycle E n h1 h0 hP f hf'
      refine ⟨g, ?_⟩
      rw [uct_d_apply]
      simpa [dval] using hg
  have hexact : (dualComplex ℤ E).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' (dualComplex ℤ E) n (n + 1) (n + 2)
      (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))]
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr ?_
    have hf : ((dualComplex ℤ E).sc' n (n + 1) (n + 2)).f
        = (dualComplex ℤ E).d n (n + 1) := rfl
    have hg : ((dualComplex ℤ E).sc' n (n + 1) (n + 2)).g
        = (dualComplex ℤ E).d (n + 1) (n + 2) := rfl
    rw [hf, hg]
    exact hrange
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((HomologicalComplex.exactAt_iff_isZero_homology (dualComplex ℤ E) (n + 1)).mp hexact)

theorem relComplex_vanishing_of_homology_free {X : TopCat} (A : Set X) (n : ℕ)
    (h1 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains X A).homology (n + 1)))
    (h0 : Module.Free ℤ ↥((Work.Cohomology.relChains X A).homology n)) :
    Subsingleton ((Work.Cohomology.relComplex ℤ X A).homology (n + 1)) := by
  have hsub : Subsingleton ((dualComplex ℤ (relChains X A)).homology (n + 1)) :=
    subsingleton_dual_homology_of_free (relChains X A) n h1 h0
      (relChainsProjective X A (n - 1))
  obtain ⟨e⟩ := relComplexIsoDual X A
  have hbij := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMapIso e (n + 1)).hom
  exact ⟨fun a b => hbij.1 (Subsingleton.elim _ _)⟩

end

end Work.Cohomology
