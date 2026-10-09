import Mathlib
import Submission.Work.SSGRoute.TPatom.levelCocycleDatum_of_blockData
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDatum
import Submission.Work.SSGcrux.concentratedLevelDataExists
import Submission.Work.SSGRoute.TPatom.blockSystemTransversal
import Submission.Work.SSGRoute.TPatom.orbitBlockSystem
import Submission.Work.SSGRoute.TPatom.detectionSingleBlock
import Submission.Work.SSGRoute.TPatom.valueFormulaDirac
import Submission.Work.SSGRoute.TPatom.shapiroTransport
import Submission.Work.SSGRoute.TPatom.exists_concentratedLevelData
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
import Submission.Work.SSGRoute.Sha2Lib.levelCocycleDatum_of_components
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Work.SSGRoute.C6ValueFormula.coset_sum
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup
import Submission.Work.SSGcrux.mackeyInvDirac
import Submission.Work.SSGcrux.diracSubtypeApply
import Submission.Work.SSGcrux.zmodAddHom_ne_zero
import Submission.Work.SSGcrux.muDirac_ne_zero_of_doubleCoset
import Submission.Work.SSGcrux.eq_of_mem_block
import Submission.Work.SSGRoute.coind_res_mackey
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

open scoped NumberField Pointwise
open CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Two elementary place-theoretic API lemmas used by the assembly

* `isInertiaAt_galRes`: the inertia group descends along restriction.
* `decompK_le_fixingSubgroup_iff_split`: the decomposition group lies in the fixing subgroup of
  an intermediate Galois field `F` exactly when `F` splits completely at the place. -/

/-- **Inertia descends along restriction.** -/
theorem isInertiaAt_galRes {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (γ : L ≃ₐ[k] L) (hγ : SSGRoute.PTExt.IsInertiaAt q' γ) :
    SSGRoute.PTExt.IsInertiaAt (k := k) q (SSGRoute.PTExt.galRes k K L γ) := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  exact SSGRoute.E9Nodes.e9_inertia_restrict k K L q q' hq' γ (SSGRoute.PTExt.galRes k K L γ)
    (fun x => (AlgEquiv.restrictNormal_commutes γ K x).symm) hγ

/-- **The decomposition group is contained in the fixing subgroup of `F` iff `F` splits
completely at the place.** -/
theorem decompK_le_fixingSubgroup_iff_split {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [FiniteDimensional K F] [IsGalois K F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hQ : Q.asIdeal.LiesOver q.asIdeal) :
    SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q) ≤ F.fixingSubgroup ↔
      ((Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).ramificationIdx
          (NumberField.RingOfIntegers K) = 1 ∧
        (Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).inertiaDeg
          (NumberField.RingOfIntegers K) = 1) := by
  haveI : Normal K ↥F := inferInstance
  let q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F) :=
    ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥F), inferInstance,
      Ideal.under_ne_bot _ Q.ne_bot⟩
  have hq'eq : q'.asIdeal = Q.asIdeal.under (NumberField.RingOfIntegers ↥F) := rfl
  have hq'q : q'.asIdeal.LiesOver q.asIdeal := by
    haveI : Q.asIdeal.LiesOver q'.asIdeal := by
      rw [hq'eq]; exact Ideal.over_under Q.asIdeal
    haveI : Q.asIdeal.LiesOver q.asIdeal := hQ
    exact Ideal.LiesOver.tower_bot Q.asIdeal q'.asIdeal q.asIdeal
  have hliesF : Q.asIdeal.LiesOver q'.asIdeal := by
    rw [hq'eq]; exact Ideal.over_under Q.asIdeal
  have hbridge : SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q :=
    Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup (K := K) Q
  rw [hbridge]
  have hker : F.fixingSubgroup
      = (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F).ker :=
    (IntermediateField.restrictNormalHom_ker (K := K) F).symm
  rw [hker, ← Subgroup.map_eq_bot_iff]
  have hmap : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q' := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact Commons.NumberTheory.NumberField.Completion.restrictNormalHom_mem_decompositionSubgroup
        F Q q' hq'eq hσ
    · intro τ hτ
      obtain ⟨σ, hσ⟩ :=
        Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
          (K := K) (M := L) F q' Q hq'eq hliesF ⟨τ, hτ⟩
      exact ⟨σ, σ.2, hσ⟩
  rw [hmap,
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) q q' hq'q]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F),
      Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F)]

/-- **A nonzero functional on the coinduced permutation module is nonzero on a coset Dirac.**
The coset Diracs `δ_{Nγ}` (`γ ↦` the indicator function of the coset `Nγ` with value `1`) span the
coinduced module `coind_N^Γ 𝔽_p`, so a nonzero `D_w`-equivariant functional takes a nonzero value
at one of them.  This is the detection input of the non-invariant case: it produces the element
`γ₀` at which the concentrated level data is invoked. -/
theorem exists_dirac_ne_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ γ : K ≃ₐ[k] K,
      μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))
        (fun _ _ _ => rfl) γ 1) ≠ 0 := by
  classical
  have hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially N.subtype
      (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) := by
    intro d hd a
    have hd1 : d = 1 := N.subtype_injective (by simpa using hd)
    subst hd1; rfl
  have hpick := Work.SSGRoute.C6ValueFormula.coind_eq_sum_dirac N.subtype
    (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) hker
    (Work.SSGRoute.TatePoitouRoute.sect N)
    (fun γ => by
      have h : γ * (Work.SSGRoute.TatePoitouRoute.sect N γ)⁻¹ ∈ N := by
        have h1 := Work.SSGRoute.TatePoitouRoute.sect_mul_inv_mem N γ
        simpa [mul_inv_rev] using (N.inv_mem h1)
      simpa using h)
    (fun γ => by
      have hγ : (⟨Work.SSGRoute.TatePoitouRoute.sect N γ * γ⁻¹,
            Work.SSGRoute.TatePoitouRoute.sect_mul_inv_mem N γ⟩ : ↥N) * γ
          = Work.SSGRoute.TatePoitouRoute.sect N γ := by
        rw [show (⟨Work.SSGRoute.TatePoitouRoute.sect N γ * γ⁻¹,
            Work.SSGRoute.TatePoitouRoute.sect_mul_inv_mem N γ⟩ : ↥N) * γ
            = (Work.SSGRoute.TatePoitouRoute.sect N γ * γ⁻¹) * γ from rfl]
        group
      conv_lhs => rw [← hγ]
      exact Work.SSGRoute.TatePoitouRoute.sect_const N _ γ)
    (fun γ γ' h => by
      obtain ⟨n, hn⟩ := h
      have hn' : (n : K ≃ₐ[k] K) = γ * γ'⁻¹ := hn
      rw [show γ = (n : K ≃ₐ[k] K) * γ' by rw [hn']; group,
        Work.SSGRoute.TatePoitouRoute.sect_const])
  by_contra hcon
  simp only [not_exists, not_ne_iff] at hcon
  refine hμ (Rep.hom_ext ?_)
  rw [Rep.zero_hom, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro v
  simp only [Representation.IntertwiningMap.coe_toLinearMap]
  rw [hpick v, map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  have key : ∀ n : ℕ, Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) hker x ((n : ZMod p))
      = n • Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) hker x 1 := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, zero_nsmul,
        Work.SSGRoute.C6ValueFormula.dirac_zero]
    | succ k ih =>
        rw [Nat.cast_succ, Work.SSGRoute.C6ValueFormula.dirac_add, ih, succ_nsmul]
  have hrel : Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) hker x ((v.1) x)
      = ((v.1) x).val • Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) hker x 1 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val ((v.1) x)]
    exact key _
  rw [hrel, map_nsmul, hcon x, smul_zero]

/-- **The Shapiro factor `cfunc` at an element of `H` is a conjugate.**  If `γ ∈ H` then
`cfunc H g γ = ⟨sect H g * γ * (sect H g)⁻¹, _⟩`. -/
theorem ssg_cfunc_eq_conj {Γ : Type} [Group Γ] [Fintype Γ] {H : Subgroup Γ} [H.Normal]
    (g : Γ) (γ : ↥H) :
    SSGRoute.TatePoitouRoute.cfunc H g (γ : Γ) =
      ⟨SSGRoute.TatePoitouRoute.sect H g * (γ : Γ) * (SSGRoute.TatePoitouRoute.sect H g)⁻¹,
        (inferInstance : H.Normal).conj_mem (γ : Γ) γ.2 (SSGRoute.TatePoitouRoute.sect H g)⟩ := by
  have hsec : SSGRoute.TatePoitouRoute.sect H (g * (γ : Γ))
      = SSGRoute.TatePoitouRoute.sect H g := by
    have hmem : (g * (γ : Γ) * g⁻¹) * g = g * (γ : Γ) := by group
    rw [← hmem]
    exact SSGRoute.TatePoitouRoute.sect_const H
      ⟨g * (γ : Γ) * g⁻¹, (inferInstance : H.Normal).conj_mem (γ : Γ) γ.2 g⟩ g
  apply Subtype.ext
  rw [SSGRoute.TatePoitouRoute.coe_cfunc, hsec]

/-- **The pointwise inertia clause of the Shapiro cocycle.**  If `I ≤ H` is a subgroup on which the
character `y` vanishes through the normal closure of `I` in `Γ`, then the Shapiro cocycle of `y`
vanishes *pointwise* on `I`.  (Local copy of the lemma of the same name in
`Submission/Work/SSGRoute/C6Detector/rankOneLevelDatumAlgClosure.lean`, inlined here so that this
module does not depend on that (large) file.) -/
theorem ssg_shapiroCocycle_cfunc_eq_zero {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Fintype Γ]
    {H : Subgroup Γ} [H.Normal]
    (I : Subgroup Γ) (hIH : I ≤ H)
    (y : ↥H →* Multiplicative (ZMod p))
    (hy : ∀ x : ↥H, ((x : Γ)) ∈ Subgroup.normalClosure (I : Set Γ) → y x = 1)
    (γ : Γ) (hγ : γ ∈ I) :
    (⟨fun g : Γ => Multiplicative.toAdd (y (SSGRoute.TatePoitouRoute.cfunc H g γ)), by
        intro n g
        show Multiplicative.toAdd (y (SSGRoute.TatePoitouRoute.cfunc H ((n : Γ) * g) γ))
          = (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)).ρ n
              (Multiplicative.toAdd (y (SSGRoute.TatePoitouRoute.cfunc H g γ)))
        rw [SSGRoute.TatePoitouRoute.cfunc_inv]
        rfl⟩ : (Rep.coind H.subtype
            (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p))).V) = 0 := by
  have hγH : γ ∈ H := hIH hγ
  apply Subtype.ext
  funext g
  show Multiplicative.toAdd (y (SSGRoute.TatePoitouRoute.cfunc H g γ)) = 0
  have hmem : (SSGRoute.TatePoitouRoute.sect H g * γ * (SSGRoute.TatePoitouRoute.sect H g)⁻¹) ∈ H :=
    (inferInstance : H.Normal).conj_mem γ hγH (SSGRoute.TatePoitouRoute.sect H g)
  have hconj : (SSGRoute.TatePoitouRoute.sect H g * γ * (SSGRoute.TatePoitouRoute.sect H g)⁻¹) ∈
      Subgroup.normalClosure (I : Set Γ) :=
    (inferInstance : (Subgroup.normalClosure (I : Set Γ)).Normal).conj_mem γ
      (Subgroup.subset_normalClosure hγ) (SSGRoute.TatePoitouRoute.sect H g)
  have hcc : SSGRoute.TatePoitouRoute.cfunc H g γ =
      ⟨SSGRoute.TatePoitouRoute.sect H g * γ * (SSGRoute.TatePoitouRoute.sect H g)⁻¹, hmem⟩ := by
    have h1 := ssg_cfunc_eq_conj (H := H) g ⟨γ, hγH⟩
    simpa using h1
  have hy1 : y ⟨SSGRoute.TatePoitouRoute.sect H g * γ * (SSGRoute.TatePoitouRoute.sect H g)⁻¹, hmem⟩
      = 1 :=
    hy _ (by simpa using hconj)
  rw [hcc, hy1]
  rfl

/-- **The level-cocycle datum in the non-invariant case** (`μ ≠ 0` with `μ (const 1) = 0`), for
the coinduced permutation module `coind_N^Γ 𝔽_p`: the block-data route of
`TPatom.noninvariantLevelDatum`, whose only missing input is the concentrated level data
`Work.SSGcrux.concentratedLevelData` (respectively `TPatom.exists_concentratedLevelData`). -/
theorem noninvariantLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0)
    (hnoninv : μ.hom (⟨fun _ => 1, fun _ _ => rfl⟩ : (Rep.coind N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V) = 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  classical
  obtain ⟨γ₀, hγ₀⟩ := exists_dirac_ne_zero p k K w N μ hμ
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq', hcop, d, f, hdH, y, hdmem, hfpos, hdgen, hfmin,
    hinertia_nc, hyC⟩ :=
    Work.SSGcrux.concentratedLevelDataExists p k K Ω w q hwq hpq N hNI ζ hζ hNζ γ₀
  haveI : NumberField ↥L := hnfL
  haveI : FiniteDimensional k ↥L := hfdL
  haveI : IsGalois k ↥L := hgalL
  haveI hFL : Fintype (↥L ≃ₐ[k] ↥L) := Fintype.ofFinite _
  haveI hDL : DecidableEq (↥L ≃ₐ[k] ↥L) := Classical.decEq _
  -- the level subgroup `H = galRes⁻¹ N` and the decomposition group `D = D_{q'}`
  let H : Subgroup (↥L ≃ₐ[k] ↥L) := Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N
  haveI hHn : H.Normal := inferInstance
  set D : Subgroup (↥L ≃ₐ[k] ↥L) :=
    SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') with hDdef
  have hDLmem : d ∈ D := hdmem
  -- the block system of the `⟨d⟩`-orbits on `H \ Gal(L/k)`
  have hdgen' : ∀ δ : ↥D, ∃ m : ℕ, ((δ : ↥L ≃ₐ[k] ↥L))⁻¹ * d ^ m ∈ H :=
    fun δ => hdgen (δ : ↥L ≃ₐ[k] ↥L) δ.2
  have hfmin' : ∀ m : ℕ, 0 < m → m < f → d ^ m ∉ H := hfmin
  have hdHD' : ((⟨d, hdmem⟩ : ↥D) : ↥L ≃ₐ[k] ↥L) ^ f ∈ H := hdH
  obtain ⟨X, _cX, hpart, hblock, _, _, _, _⟩ :=
    Work.SSGRoute.TPatom.exists_blockSystem_transversal H hHn D ⟨d, hdmem⟩ f hfpos hdHD' hdgen' hfmin'
  have hpart' : ∀ γ : ↥L ≃ₐ[k] ↥L, ∃! q : (↥L ≃ₐ[k] ↥L) × Fin f,
      q.1 ∈ X ∧ γ * (q.1 * d ^ (q.2 : ℕ))⁻¹ ∈ H := hpart
  have hblock' : ∀ x ∈ X, ∀ δ : ↥D, ∃ j : Fin f,
      (x * (δ : ↥L ≃ₐ[k] ↥L)) * (x * d ^ (j : ℕ))⁻¹ ∈ H := hblock
  -- a lift of `γ₀` to `Gal(L/k)`
  obtain ⟨γ₀', hγ₀'⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) ↥L γ₀
  -- the detecting block
  obtain ⟨q₀, hq₀spec, -⟩ := hpart' γ₀'
  obtain ⟨x₀, j₀⟩ := q₀
  obtain ⟨hx₀X, hx₀H⟩ := hq₀spec
  -- the restriction homomorphism `D → D_w`
  obtain ⟨fd, hfd⟩ := Work.SSGRoute.decompK_restrict_exists k K ↥L w
    (NK.GlobalCFT.Place.ofFinite q') hq'
  have hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K ↥L (σ : ↥L ≃ₐ[k] ↥L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w := by
    intro σ
    simpa [hfd] using (fd ⟨σ.1, σ.2⟩).2
  have hgald : SSGRoute.PTExt.galRes k K ↥L d ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w := by
    simpa [hfd] using (fd ⟨d, hdmem⟩).2
  have hgalx₀ : SSGRoute.PTExt.galRes k K ↥L x₀ ∈ Work.SSGRoute.TPatom.concSet k K w N γ₀ := by
    have hN : γ₀ *
        (SSGRoute.PTExt.galRes k K ↥L x₀ *
          (SSGRoute.PTExt.galRes k K ↥L d) ^ (j₀ : ℕ))⁻¹ ∈ N := by
      have h := hx₀H
      rw [Subgroup.mem_comap] at h
      simp only [map_mul, map_inv, map_pow, hγ₀'] at h
      exact h
    set n₀ : ↥N := ⟨γ₀ *
        (SSGRoute.PTExt.galRes k K ↥L x₀ *
          (SSGRoute.PTExt.galRes k K ↥L d) ^ (j₀ : ℕ))⁻¹, hN⟩ with hn₀def
    refine ⟨((SSGRoute.PTExt.galRes k K ↥L d) ^ (j₀ : ℕ))⁻¹,
      Subgroup.inv_mem _ (Subgroup.pow_mem _ hgald (j₀ : ℕ)),
      SSGRoute.PTExt.galRes k K ↥L d ^ (j₀ : ℕ) *
        (γ₀⁻¹ * ((n₀ : ↥N) : K ≃ₐ[k] K)⁻¹ * γ₀) *
        (SSGRoute.PTExt.galRes k K ↥L d ^ (j₀ : ℕ))⁻¹, ?_, ?_⟩
    · exact (inferInstance : N.Normal).conj_mem _
        ((inferInstance : N.Normal).conj_mem _ (N.inv_mem n₀.2) γ₀⁻¹)
        (SSGRoute.PTExt.galRes k K ↥L d ^ (j₀ : ℕ))
    · have hn₀val : ((n₀ : ↥N) : K ≃ₐ[k] K) = γ₀ *
          (SSGRoute.PTExt.galRes k K ↥L x₀ *
            (SSGRoute.PTExt.galRes k K ↥L d) ^ (j₀ : ℕ))⁻¹ := rfl
      rw [hn₀val]
      group
  -- **`galRes σ ∈ concSet γ₀ → σ ∈ H · γ₀' · D`** (i.e. `σ` lies in the block of `γ₀'`)
  have hmem_block : ∀ σ : ↥L ≃ₐ[k] ↥L,
      SSGRoute.PTExt.galRes k K ↥L σ ∈ Work.SSGRoute.TPatom.concSet k K w N γ₀ →
        ∃ h ∈ H, ∃ δ ∈ D, σ = h * γ₀' * δ := by
    intro σ hmem
    obtain ⟨δw, hδw, n, hn, hgn⟩ := hmem
    obtain ⟨δ₀, hδ₀eq⟩ := Work.SSGRoute.decompK_restrict_surjective
      (k := k) (K := K) (L := ↥L) w (NK.GlobalCFT.Place.ofFinite q') hq' fd hfd ⟨δw, hδw⟩
    have hδ₀' : SSGRoute.PTExt.galRes k K ↥L (δ₀ : ↥L ≃ₐ[k] ↥L) = δw := by
      have h1 := hfd δ₀
      rw [hδ₀eq] at h1
      simpa using h1.symm
    refine ⟨σ * (γ₀' * (δ₀ : ↥L ≃ₐ[k] ↥L))⁻¹, ?_, δ₀, δ₀.2, ?_⟩
    · rw [Subgroup.mem_comap]
      simp only [map_mul, map_inv, hδ₀', hγ₀']
      rw [← hgn]
      have hgrp : γ₀ * (δw * n) * (γ₀ * δw)⁻¹ = γ₀ * (δw * n * δw⁻¹) * γ₀⁻¹ := by group
      rw [hgrp]
      exact (inferInstance : N.Normal).conj_mem _
        ((inferInstance : N.Normal).conj_mem _ hn δw) γ₀
    · group
  -- `γ₀' = h₀ x₀ d^{j₀}` in the shape `H · x₀ · D`
  have hγ₀'block : ∃ a ∈ H, γ₀' = a * x₀ * d ^ (j₀ : ℕ) :=
    ⟨γ₀' * (x₀ * d ^ (j₀ : ℕ))⁻¹, hx₀H, by group⟩
  -- **`galRes x ∉ concSet γ₀` for `x ∈ X`, `x ≠ x₀`**
  have hnotmem : ∀ x ∈ X, x ≠ x₀ →
      SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ₀ := by
    intro x hx hxne hmem
    obtain ⟨a, ha, δ, hδ, hxeq⟩ := hmem_block x hmem
    obtain ⟨a₀, ha₀, hγ₀'eq⟩ := hγ₀'block
    refine hxne (Work.SSGcrux.eq_of_mem_block H hHn D ⟨d, hdmem⟩ f hfpos hdH hdgen' hfmin' X
      hpart' x x₀ hx hx₀X ⟨a * a₀, H.mul_mem ha ha₀,
        ⟨⟨d ^ (j₀ : ℕ) * δ, D.mul_mem (D.pow_mem hDLmem j₀) hδ⟩, ?_⟩⟩)
    rw [hxeq, hγ₀'eq]
    group
  -- `hne` and `hvan` from the concentration clause
  have hnefun : y (Work.SSGRoute.TatePoitouRoute.cfunc H x₀ (⟨d ^ f, hdH⟩ : ↥H)) ≠ 1 :=
    fun hc => ((hyC x₀).mp hc) hgalx₀
  have hne : Multiplicative.toAdd (y (Work.SSGRoute.TatePoitouRoute.cfunc H x₀
      (⟨d ^ f, hdH⟩ : ↥H))) ≠ 0 := by
    intro h0
    exact hnefun (by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this)
  have hvan : ∀ x ∈ X, x ≠ x₀ →
      Multiplicative.toAdd (y (Work.SSGRoute.TatePoitouRoute.cfunc H x
        (⟨d ^ f, hdH⟩ : ↥H))) = 0 := by
    intro x hx hxne
    rw [(hyC x).mpr (hnotmem x hx hxne)]
    rfl
  -- ## the Mackey isomorphism `θ`
  let fg : (↥L ≃ₐ[k] ↥L) →* (K ≃ₐ[k] K) := SSGRoute.PTExt.galRes k K ↥L
  have hsurj : Function.Surjective fg := by
    show Function.Surjective (SSGRoute.PTExt.galRes k K ↥L)
    exact AlgEquiv.restrictNormalHom_surjective (E := ↥L)
  haveI hdecN : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  haveI hdecH : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  haveI hfinqN : Fintype ((K ≃ₐ[k] K) ⧸ N) := Fintype.ofFinite _
  haveI hfinqH : Fintype ((↥L ≃ₐ[k] ↥L) ⧸ H) := Fintype.ofFinite _
  obtain ⟨θ₀, hθval, -, -⟩ := Work.SSGRoute.coind_res_mackey fg hsurj N
  let Xc : Rep.{0} SSGRoute.PTExt.Coeff ↥N := Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)
  let Wc : Rep.{0} SSGRoute.PTExt.Coeff ↥H := Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)
  let θ : Rep.res fg (Rep.coind N.subtype Xc) ≅ Rep.coind H.subtype Wc := θ₀.app Xc
  have hθ : ∀ (φ : (Rep.coind N.subtype Xc).V) (x : ↥L ≃ₐ[k] ↥L),
      (θ.hom.hom φ).1 x = φ.1 (fg x) := fun φ x => hθval Xc φ x
  -- ## `θ.inv` of a Dirac is a Dirac; hence `μ`-detection at `1` transfers
  have hθinv : ∀ g : K ≃ₐ[k] K,
      (θ.inv.hom (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀ 1)).1 g
        = if g * (fg x₀)⁻¹ ∈ N then (1 : ZMod p) else 0 :=
    fun g => Work.SSGcrux.mackeyInvDirac fg hsurj N Xc (fun _ _ => rfl) θ hθ x₀ 1 g
  have hθinv_eq : θ.inv.hom (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀ 1)
      = Work.SSGRoute.C6ValueFormula.dirac N.subtype Xc (fun _ _ _ => rfl) (fg x₀) 1 := by
    apply Subtype.ext
    funext g
    rw [hθinv g, Work.SSGcrux.diracSubtypeApply Xc (fun _ _ => rfl) (fg x₀) 1 g]
  have hbase : μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype Xc (fun _ _ _ => rfl)
      (fg x₀) 1) ≠ 0 := by
    have hmem : ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w, ∃ n ∈ N,
        γ₀ * (δ * n) = fg x₀ := hgalx₀
    exact Work.SSGcrux.muDirac_ne_zero_of_doubleCoset N (SSGRoute.PTExt.decompK (k := k) (K := K) w)
      μ γ₀ (fg x₀) hγ₀ hmem
  have hinj : ∀ a : Wc.V, a ≠ 0 →
      (Work.SSGRoute.TPatom.transportedFunctional p k K ↥L w N H μ θ D hgal).hom
        (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀ a) ≠ 0 := by
    intro a ha
    rw [Work.SSGRoute.TPatom.transportedFunctional_apply]
    have hF1 : ((μ.hom.toAddMonoidHom).comp ((θ.inv.hom).toAddMonoidHom.comp
        (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀))) 1 ≠ 0 := by
      show μ.hom (θ.inv.hom (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀ 1)) ≠ 0
      rw [hθinv_eq]
      exact hbase
    exact Work.SSGcrux.zmodAddHom_ne_zero
      ((μ.hom.toAddMonoidHom).comp ((θ.inv.hom).toAddMonoidHom.comp
        (Work.Sha2Lib.diracHom Wc (fun _ _ _ => rfl) x₀))) hF1 a ha
  -- ## the inertia clause
  have hlies : q'.asIdeal.LiesOver q.asIdeal := by
    have h1 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite q) := by
      rw [← hwq]; exact hq'
    rcases (NK.GlobalCFT.Place.liesOver_iff _ _).1 h1 with
      ⟨w', v', hw', hv', -⟩ | ⟨q₁, Q₁, hq1, hQ1, hl⟩
    · exact absurd hw'.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q')
    · obtain rfl : q₁ = q' := (NK.GlobalCFT.Place.ofFinite_inj.mp hq1).symm
      obtain rfl : Q₁ = q := (NK.GlobalCFT.Place.ofFinite_inj.mp hQ1).symm
      exact hl
  have hinertia : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      θ.inv.hom (Work.SSGRoute.TPatom.shapiroTerm Wc (fun _ _ => rfl)
        (Work.SSGRoute.TatePoitouRoute.cfunc H) (Work.SSGRoute.TatePoitouRoute.cfunc_inv H) y γ)
        = 0 := by
    intro γ hγ
    let I : Subgroup (↥L ≃ₐ[k] ↥L) := Ideal.inertia (↥L ≃ₐ[k] ↥L) q'.asIdeal
    have hIeq : ∀ σ : ↥L ≃ₐ[k] ↥L, σ ∈ I ↔ SSGRoute.PTExt.IsInertiaAt q' σ :=
      fun σ => (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥L) q' σ).symm
    have hIH : I ≤ H := by
      intro σ hσ
      rw [Subgroup.mem_comap]
      exact hNI (SSGRoute.PTExt.galRes k K ↥L σ)
        (isInertiaAt_galRes q q' hlies σ ((hIeq σ).mp hσ))
    have hy : ∀ x : ↥H, (x : ↥L ≃ₐ[k] ↥L) ∈ Subgroup.normalClosure (I : Set (↥L ≃ₐ[k] ↥L)) →
        y x = 1 := by
      intro x hx
      apply hinertia_nc x
      convert hx using 2
      ext σ
      exact (hIeq σ).symm
    have h0 := ssg_shapiroCocycle_cfunc_eq_zero I hIH y hy γ ((hIeq γ).mpr hγ)
    have hT : Work.SSGRoute.TPatom.shapiroTerm Wc (fun _ _ => rfl)
        (Work.SSGRoute.TatePoitouRoute.cfunc H) (Work.SSGRoute.TatePoitouRoute.cfunc_inv H) y γ
        = 0 := by
      rw [← h0]
      apply Subtype.ext
      funext g
      rfl
    rw [hT, map_zero]
  -- ## the block-data wiring
  exact Work.SSGRoute.TPatom.levelCocycleDatum_of_blockData (p := p) (k := k) (K := K) (Ω := Ω)
    (w := w) (q := q) (hwq := hwq) (N := N) (μ := μ)
    (L := L) (q' := q') (hq' := hq') (hcop := hcop) (H := H) (θ := θ)
    (c := Work.SSGRoute.TatePoitouRoute.cfunc H)
    (hcmul := Work.SSGRoute.TatePoitouRoute.cfunc_mul H)
    (hcunit := Work.SSGRoute.TatePoitouRoute.cfunc_one H)
    (hcoinv := Work.SSGRoute.TatePoitouRoute.cfunc_inv H)
    (hgal := hgal) (d := ⟨d, hdmem⟩) (f := f) (hf := hfpos) (hdH := hdH) (X := X)
    (hpart := hpart') (hblock := hblock') (y := y) (x₀ := x₀) (hx₀ := hx₀X)
    (hinj := hinj) (hne := hne) (hvan := hvan) (hinertia := hinertia)

end Work.SSGcrux
