import Mathlib
import Submission.NK.FieldTheory.Galois.DecompDefs
import Submission.NK.Mine.Generation
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero

/-!
# The decomposition groups of a finite Galois extension of number fields generate the Galois group

Let `L / K` be a finite Galois extension of number fields.  For a finite place `w` of `L` the
decomposition subgroup `D_w ≤ Gal(L/K)` is the stabiliser of `w`.  The main result of this file is

`iSup_decompositionSubgroup_eq_top : (⨆ w, D_w) = ⊤`,

i.e. the decomposition subgroups generate the whole Galois group.

The mathematical content is the following.  Let `N := ⨆ w, D_w`.  Since the family of
decomposition subgroups is stable under conjugation (`D_{σ w} = σ D_w σ⁻¹`), `N` is normal in
`Gal(L/K)`, so it cuts out an intermediate field `F := L^N` which is Galois over `K`.  Every
decomposition subgroup of the extension `F/K` is trivial: an element of `D_q(F/K)` lifts to an
element of `D_P(L/K) ⊆ N = Gal(L/F)` for a place `P` of `L` above `q`, hence restricts to `1` on
`F`.  A trivial decomposition group means that the place is unramified with residue degree one,
so the fundamental identity shows that every prime of `K` splits completely in `F`.  But the
"easy half of Čebotarev" (`NK.Mine.exists_prime_not_splitsCompletely`) says that a nontrivial
Galois extension of number fields has a prime that does *not* split completely.  Hence `F = K`
and `N = ⊤`.
-/

set_option linter.style.haveILetI false

namespace NK.FieldTheory.Galois

open scoped Pointwise

theorem iSup_decompositionSubgroup_eq_top {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (⨆ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      NK.FieldTheory.Galois.decompSubgroup (K := K) w) = ⊤ := by
  classical
  set N : Subgroup (L ≃ₐ[K] L) := ⨆ w, NK.FieldTheory.Galois.decompSubgroup (K := K) w
    with hNdef
  by_contra hN
  -- ## The decomposition group of `σ w` is the conjugate of the decomposition group of `w`
  have hconj : ∀ (σ : L ≃ₐ[K] L)
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (NK.FieldTheory.Galois.decompSubgroup (K := K) w).map (MulAut.conj σ) =
        NK.FieldTheory.Galois.decompSubgroup (K := K)
          (Submission.NeukirchUchida.Local.placeSmul σ w) := fun σ w => by
    ext τ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change σ * x * σ⁻¹ ∈ NK.FieldTheory.Galois.decompSubgroup (K := K)
          (Submission.NeukirchUchida.Local.placeSmul σ w)
      rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
      rw [show σ * x * σ⁻¹ = σ * (x * σ⁻¹) from by group]
      rw [Submission.NeukirchUchida.Local.placeSmul_mul,
        Submission.NeukirchUchida.Local.placeSmul_mul]
      rw [show Submission.NeukirchUchida.Local.placeSmul σ⁻¹
          (Submission.NeukirchUchida.Local.placeSmul σ w) = w from by
        rw [← Submission.NeukirchUchida.Local.placeSmul_mul, inv_mul_cancel σ,
          Submission.NeukirchUchida.Local.placeSmul_one]]
      rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup.mp hx]
    · intro hτ
      refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
      · rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
        rw [show σ⁻¹ * τ * σ = σ⁻¹ * (τ * σ) from by group]
        rw [Submission.NeukirchUchida.Local.placeSmul_mul,
          Submission.NeukirchUchida.Local.placeSmul_mul]
        rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup.mp hτ]
        rw [show Submission.NeukirchUchida.Local.placeSmul σ⁻¹
            (Submission.NeukirchUchida.Local.placeSmul σ w) = w from by
          rw [← Submission.NeukirchUchida.Local.placeSmul_mul, inv_mul_cancel σ,
            Submission.NeukirchUchida.Local.placeSmul_one]]
      · change σ * (σ⁻¹ * τ * σ) * σ⁻¹ = τ
        group
  -- ## `N` is normal
  have hmap_le : ∀ σ : L ≃ₐ[K] L, N.map (MulAut.conj σ) ≤ N := by
    intro σ
    rw [hNdef, Subgroup.map_iSup]
    apply iSup_le; intro w
    rw [hconj σ w]
    exact le_iSup (fun w => NK.FieldTheory.Galois.decompSubgroup (K := K) w)
      (Submission.NeukirchUchida.Local.placeSmul σ w)
  haveI hNnormal : N.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro σ
    refine le_antisymm (hmap_le σ) ?_
    have hcomp : (MulAut.conj σ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)).comp
        (MulAut.conj σ⁻¹ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)) = MonoidHom.id (L ≃ₐ[K] L) := by
      apply MonoidHom.ext
      intro x
      change σ * (σ⁻¹ * x * σ) * σ⁻¹ = x
      group
    have h2 : (N.map (MulAut.conj σ⁻¹ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L))).map
        (MulAut.conj σ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)) = N := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    calc N = (N.map (MulAut.conj σ⁻¹ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L))).map
          (MulAut.conj σ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)) := h2.symm
      _ ≤ N.map (MulAut.conj σ) := Subgroup.map_mono (hmap_le σ⁻¹)
  -- ## The fixed field of `N`
  set F : IntermediateField K L := IntermediateField.fixedField N with hFdef
  haveI hFgal : IsGalois K ↥F := by rw [hFdef]; infer_instance
  haveI hFnf : NumberField ↥F :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := L) F
  -- ## Every decomposition group of `F / K` is trivial
  have htriv : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F),
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q = ⊥ := by
    intro q
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    -- a place `P` of `L` above `q`
    obtain ⟨P0⟩ :=
      (inferInstance : Nonempty (q.asIdeal.primesOver (NumberField.RingOfIntegers L)))
    let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      ⟨P0.1, P0.2.1, Ideal.ne_bot_of_mem_primesOver q.ne_bot P0.2⟩
    have hlies : P.asIdeal.LiesOver q.asIdeal := P0.2.2
    have hwL : q.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers ↥F) := P0.2.2.over
    -- `τ` lifts to the decomposition group of `P` in `Gal(L/K)`, which is contained in `N`
    obtain ⟨σ, hσ⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
        (K := K) (M := L) F q P hwL hlies ⟨τ, hτ⟩
    have hσN : (σ : L ≃ₐ[K] L) ∈ N := by
      rw [hNdef]
      exact le_iSup (fun w => NK.FieldTheory.Galois.decompSubgroup (K := K) w) P σ.2
    have hfix : (σ : L ≃ₐ[K] L) ∈
        IntermediateField.fixingSubgroup (IntermediateField.fixedField N) := by
      rw [IntermediateField.fixingSubgroup_fixedField N]
      exact hσN
    -- so `τ` is the restriction of an element acting trivially on `F`
    have hone : AlgEquiv.restrictNormalHom F (σ : L ≃ₐ[K] L) = 1 := by
      show (σ : L ≃ₐ[K] L).restrictNormal F = 1
      rw [AlgEquiv.restrictNormal_eq_one_iff]
      exact (IntermediateField.mem_fixingSubgroup_iff (IntermediateField.fixedField N)
        (σ : L ≃ₐ[K] L)).mp hfix
    have hτ1 : τ = 1 := by
      have h := hσ.symm.trans hone
      simpa using h
    exact hτ1
  -- ## Hence every prime of `K` splits completely in `F`
  have hcount : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥F)).ncard = Module.finrank K ↥F := by
    intro p
    obtain ⟨q0⟩ :=
      (inferInstance : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥F)))
    let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F) :=
      ⟨q0.1, q0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q0.2⟩
    have hlies : q.asIdeal.LiesOver p.asIdeal := q0.2.2
    have hbot :
        Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q = ⊥ :=
      htriv q
    have hef :=
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
        (K := K) (L := ↥F) p q hlies).mp hbot
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers ↥F)
      (G := ↥F ≃ₐ[K] ↥F) p.asIdeal
    simp only [hef.1, hef.2, mul_one] at hfund
    rw [hfund, IsGalois.card_aut_eq_finrank K ↥F]
  -- ## `F ≠ K`
  have hfin : 1 < Module.finrank K ↥F := by
    have hpos : 0 < Module.finrank K ↥F := Module.finrank_pos
    have hne : Module.finrank K ↥F ≠ 1 := by
      intro h
      have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h
      apply hN
      have h2 : IntermediateField.fixedField N = ⊥ := by rw [← hFdef]; exact hbot
      rw [IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
        IntermediateField.fixingSubgroup_bot] at h2
      exact h2.symm
    omega
  -- ## The "easy half of Čebotarev" gives a contradiction
  obtain ⟨p, hp⟩ := NK.Mine.exists_prime_not_splitsCompletely (K := K) (L := ↥F) hfin
  rw [hcount p] at hp
  exact absurd hp (lt_irrefl _)

end NK.FieldTheory.Galois
