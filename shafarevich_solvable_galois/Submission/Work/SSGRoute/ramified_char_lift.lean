import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.exists_inertia_of_lift
import Submission.Work.SSGRoute.exists_kummer_theta_of_decomp
import Submission.Work.SSGRoute.kummerRatioHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute

/-- The inertia subgroup `ValuationSubring.inertiaSubgroup` of `D_A` is exactly the set of
`SSGRoute.IsInertia` elements, i.e. the elements of `D_A` acting trivially on the residue field. -/
lemma mem_inertiaSubgroup_iff {A : ValuationSubring SSGRoute.QBar}
    (σ : ↥(SSGRoute.decomp ℚ A)) :
    σ ∈ ValuationSubring.inertiaSubgroup ℚ A ↔ SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h
    refine ⟨σ.2, ?_⟩
    intro x hx
    have hres : ∀ b : ↥A, (IsLocalRing.residue ↥A) (σ • b) = (IsLocalRing.residue ↥A) b := by
      intro b
      have h1 : σ • (IsLocalRing.residue ↥A) b = (IsLocalRing.residue ↥A) b := by
        have h2 := congrArg (fun f : RingAut (IsLocalRing.ResidueField ↥A) =>
          f ((IsLocalRing.residue ↥A) b)) h
        simpa using h2
      rw [IsLocalRing.ResidueField.residue_smul]
      exact h1
    have hmem : (σ • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
    have hv := (ValuationSubring.valuation_lt_one_iff A
      (σ • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩)).mp hmem
    simpa [NK.Ramification.coe_smul] using hv
  · intro h
    show (MulSemiringAction.toRingAut ↥(A.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField A)) σ = 1
    ext r
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
    have hv : A.valuation ((σ : SSGRoute.GalQ) (b : SSGRoute.QBar) - (b : SSGRoute.QBar)) < 1 :=
      h.2 (b : SSGRoute.QBar) b.2
    have hmem : (σ • b - b) ∈ IsLocalRing.maximalIdeal ↥A := by
      refine (ValuationSubring.valuation_lt_one_iff A (σ • b - b)).mpr ?_
      simpa [NK.Ramification.coe_smul] using hv
    have h1 : (IsLocalRing.residue ↥A) (σ • b - b) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, sub_eq_zero] at h1
    have h2 : (MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ))
        (IsLocalRing.ResidueField ↥A)) σ ((IsLocalRing.residue ↥A) b)
        = σ • ((IsLocalRing.residue ↥A) b) := rfl
    rw [h2, ← IsLocalRing.ResidueField.residue_smul]
    exact h1

/-! ## The tame lifting of a totally ramified character -/

/-- Tame (Kummer/reciprocity) lifting of a totally ramified continuous character of the
decomposition group `D_A` of a finite place `A` of `ℚ̄` with residue characteristic `≠ p`:
if `μ_{p^{a+1}}` is fixed by `D_A`, then every continuous character `χ : D_A → μ_{p^a}` whose
values are attained on the inertia group lifts to a character `χ' : D_A → μ_{p^{a+1}}` (with the
same inertia property) reducing to `χ`. -/
theorem ramified_char_lift (p a : ℕ) (hp : p.Prime) (A : ValuationSubring SSGRoute.QBar)
    (hfin : SSGRoute.IsFinPlace ℚ A) (hnotp : ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (hμ : ∃ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ (p ^ (a + 1)) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ζ = ζ)
    (χ : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ a)))
    (hopen : IsOpen (χ.ker : Set ↥(SSGRoute.decomp ℚ A)))
    (hiner : ∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (τ : SSGRoute.GalQ) ∧ χ τ = χ σ) :
    ∃ χ' : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ (a + 1))),
      IsOpen (χ'.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
        SSGRoute.IsInertia ℚ A (τ : SSGRoute.GalQ) ∧ χ' τ = χ' σ) ∧
      ∀ σ : ↥(SSGRoute.decomp ℚ A),
        Multiplicative.toAdd (χ σ) =
          ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
            (Multiplicative.toAdd (χ' σ)) := by
  classical
  by_cases hχ1 : χ = 1
  · refine ⟨1, ?_, ?_, ?_⟩
    · rw [MonoidHom.ker_one]; exact isOpen_univ
    · intro σ
      exact ⟨1, ⟨Subgroup.one_mem _, by intro x hx; simp⟩, rfl⟩
    · intro σ
      rw [hχ1]; simp
  · obtain ⟨ζ, hζprim, hζfix⟩ := hμ
    have hN0 : p ^ (a + 1) ≠ 0 := (pow_pos hp.pos (a + 1)).ne'
    have hNa0 : p ^ a ≠ 0 := (pow_pos hp.pos a).ne'
    haveI hNne : NeZero (p ^ (a + 1)) := ⟨hN0⟩
    haveI hNane : NeZero (p ^ a) := ⟨hNa0⟩
    have hζ0 : ζ ≠ 0 := hζprim.ne_zero hN0
    let ζu : SSGRoute.QBarˣ := Units.mk0 ζ hζ0
    have hζu : IsPrimitiveRoot ζu (p ^ (a + 1)) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa [ζu] using hζprim)
    let ζa : SSGRoute.QBar := ζ ^ p
    have hζa : IsPrimitiveRoot ζa (p ^ a) :=
      hζprim.pow (by positivity) (by rw [pow_succ, mul_comm])
    have hζa0 : ζa ≠ 0 := hζa.ne_zero hNa0
    let ζau : SSGRoute.QBarˣ := Units.mk0 ζa hζa0
    have hζau : IsPrimitiveRoot ζau (p ^ a) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa [ζau] using hζa)
    have hζau_pow : ζu ^ p = ζau := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]
    have hfixRU : ∀ σ ∈ SSGRoute.decomp ℚ A, ∀ η : SSGRoute.QBar,
        η ^ (p ^ (a + 1)) = 1 → σ η = η := by
      intro σ hσ η hη
      obtain ⟨i, -, hi⟩ := hζprim.eq_pow_of_pow_eq_one hη
      rw [← hi, map_pow, hζfix σ hσ]
    have hμa : ∀ η : SSGRoute.QBar, IsPrimitiveRoot η (p ^ a) →
        ∀ σ ∈ SSGRoute.decomp ℚ A, σ η = η := by
      intro η hη σ hσ
      obtain ⟨i, -, hi⟩ := hζa.eq_pow_of_pow_eq_one hη.pow_eq_one
      have hζafix : (σ : SSGRoute.GalQ) ζa = ζa := by
        show (σ : SSGRoute.GalQ) (ζ ^ p) = ζ ^ p
        rw [map_pow, hζfix σ hσ]
      rw [← hi, map_pow, hζafix]
    obtain ⟨θ, hθ0, hθ⟩ := exists_kummer_theta_of_decomp p a hp A hμa ζa hζa χ hopen
    have hθfix : ∀ σ : ↥(SSGRoute.decomp ℚ A),
        (σ : SSGRoute.GalQ) (θ ^ (p ^ a)) = θ ^ (p ^ a) := by
      intro σ
      have h1 : (σ : SSGRoute.GalQ) θ = θ * ζa ^ (Multiplicative.toAdd (χ σ)).val := by
        rw [← hθ σ]
        field_simp
      rw [map_pow, h1, mul_pow, ← pow_mul, pow_mul', hζa.pow_eq_one, one_pow, mul_one]
    obtain ⟨θ', hθ'⟩ := IsAlgClosed.exists_pow_nat_eq (θ ^ (p ^ a)) (pow_pos hp.pos (a + 1))
    have hθ'0 : θ' ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_pos hp.pos (a + 1)).ne'] at hθ'
      exact (pow_ne_zero (p ^ a) hθ0) hθ'.symm
    obtain ⟨ψ, hψ⟩ := kummerRatioHom A (p ^ (a + 1)) hN0 θ' hθ'0
      (by intro σ; rw [hθ']; exact hθfix σ) hfixRU
    let χ' : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ (a + 1))) :=
      (zr hζu).symm.toMonoidHom.comp ψ
    have hχ'ψ : ∀ σ : ↥(SSGRoute.decomp ℚ A), zr hζu (χ' σ) = ψ σ := by
      intro σ
      exact MulEquiv.apply_symm_apply (zr hζu) (ψ σ)
    have hψp : ∀ σ : ↥(SSGRoute.decomp ℚ A),
        (((ψ σ : ↥(rootsOfUnity (p ^ (a + 1)) SSGRoute.QBar)) : SSGRoute.QBarˣ)) ^ p
          = ((zr hζau (χ σ) : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ) := by
      intro σ
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hψ σ]
      have hz : (((zr hζau (χ σ) : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ) :
            SSGRoute.QBar) = (ζa : SSGRoute.QBar) ^ (Multiplicative.toAdd (χ σ)).val := by
        have h1 : ((zr hζau (Multiplicative.ofAdd (Multiplicative.toAdd (χ σ)))
            : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ)
            = ζau ^ ((Multiplicative.toAdd (χ σ)).val : ℕ) := by
          rw [zr_apply_val hζau (Multiplicative.toAdd (χ σ)), zpow_natCast]
        have h2 : ((zr hζau (χ σ) : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ)
            = ((zr hζau (Multiplicative.ofAdd (Multiplicative.toAdd (χ σ)))
                : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ) :=
          congrArg (fun x => ((zr hζau x : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ))
            (Equiv.apply_symm_apply (Multiplicative.ofAdd) (χ σ)).symm
        rw [h2, h1, Units.val_pow_eq_pow_val,
          show (ζau : SSGRoute.QBar) = ζa from Units.val_mk0 hζa0]
      rw [hz]
      rw [div_pow, ← map_pow]
      have hηpow : (θ' ^ p / θ) ^ (p ^ a) = 1 := by
        rw [div_pow, ← pow_mul, show p * p ^ a = p ^ (a + 1) from by rw [pow_succ, mul_comm],
          hθ', div_self (pow_ne_zero _ hθ0)]
      have hηfix : (σ : SSGRoute.GalQ) (θ' ^ p / θ) = θ' ^ p / θ :=
        hfixRU (σ : SSGRoute.GalQ) σ.2 _ (by
          rw [show p ^ (a + 1) = p ^ a * p from by rw [pow_succ], pow_mul, hηpow, one_pow])
      have h3 : (σ : SSGRoute.GalQ) (θ' ^ p) = (θ' ^ p / θ) * ((σ : SSGRoute.GalQ) θ) := by
        conv_lhs => rw [show θ' ^ p = (θ' ^ p / θ) * θ from (div_mul_cancel₀ _ hθ0).symm]
        rw [map_mul, hηfix]
      rw [h3, show (θ' ^ p / θ * (σ : SSGRoute.GalQ) θ) / θ' ^ p = (σ : SSGRoute.GalQ) θ / θ
        from by field_simp, hθ σ]
    have hred : ∀ σ : ↥(SSGRoute.decomp ℚ A), Multiplicative.toAdd (χ σ)
        = ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
            (Multiplicative.toAdd (χ' σ)) := by
      intro σ
      have hcast := zr_pow_castHom (p := p) (a := a) hζu hζau hζau_pow (χ' σ)
      have hA : (((zr hζu (χ' σ) : ↥(rootsOfUnity (p ^ (a + 1)) SSGRoute.QBar)) :
            SSGRoute.QBarˣ)) ^ p
          = ((zr hζau (χ σ) : ↥(rootsOfUnity (p ^ a) SSGRoute.QBar)) : SSGRoute.QBarˣ) := by
        rw [hχ'ψ σ]
        exact hψp σ
      have hEq : zr hζau (Multiplicative.ofAdd ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a))
            (ZMod (p ^ a))) (Multiplicative.toAdd (χ' σ)))) = zr hζau (χ σ) := by
        apply Subtype.ext
        rw [← hcast, hA]
      have h2 := (zr hζau).injective hEq
      rw [← h2]
      rfl
    refine ⟨χ', ?_, ?_, hred⟩
    · have hFixOpen : IsOpen (((IntermediateField.adjoin ℚ ({θ'} : Set SSGRoute.QBar)).fixingSubgroup :
          Set SSGRoute.GalQ)) := by
        haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({θ'} : Set SSGRoute.QBar)) :=
          IntermediateField.adjoin.finiteDimensional
            (Algebra.IsIntegral.isIntegral (R := ℚ) θ')
        exact IntermediateField.fixingSubgroup_isOpen _
      have hker : (χ'.ker : Set ↥(SSGRoute.decomp ℚ A))
          = Subtype.val ⁻¹' (((IntermediateField.adjoin ℚ ({θ'} : Set SSGRoute.QBar)).fixingSubgroup :
              Set SSGRoute.GalQ)) := by
        ext σ
        constructor
        · intro hσ
          have hσ' : χ' σ = 1 := MonoidHom.mem_ker.mp hσ
          rw [Set.mem_preimage]
          have h1 : ψ σ = 1 := by
            rw [← hχ'ψ σ, hσ', map_one]
          have h2 : (((ψ σ : ↥(rootsOfUnity (p ^ (a + 1)) SSGRoute.QBar)) : SSGRoute.QBarˣ) :
              SSGRoute.QBar) = 1 := by
            rw [h1]; rfl
          have h3 : (σ : SSGRoute.GalQ) θ' = θ' := by
            have h4 : ((σ : SSGRoute.GalQ) θ') / θ' = 1 := by
              rw [← hψ σ, h2]
            exact (div_eq_one_iff_eq hθ'0).mp h4
          refine (IntermediateField.mem_fixingSubgroup_iff
            (IntermediateField.adjoin ℚ ({θ'} : Set SSGRoute.QBar)) (σ : SSGRoute.GalQ)).mpr ?_
          intro y hy
          have h5 : (IntermediateField.adjoin ℚ ({θ'} : Set SSGRoute.QBar)) ≤
              IntermediateField.fixedField (Subgroup.zpowers (σ : SSGRoute.GalQ)) := by
            rw [IntermediateField.adjoin_le_iff]
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            rw [hx]
            refine (IntermediateField.mem_fixedField_iff
              (Subgroup.zpowers (σ : SSGRoute.GalQ)) θ').mpr ?_
            intro f hf
            have hσstab : (σ : SSGRoute.GalQ) ∈ MulAction.stabilizer SSGRoute.GalQ θ' := by
              rw [MulAction.mem_stabilizer_iff]
              simpa [AlgEquiv.smul_def] using h3
            have hff := (Subgroup.zpowers_le.mpr hσstab) hf
            rw [MulAction.mem_stabilizer_iff] at hff
            simpa [AlgEquiv.smul_def] using hff
          exact (IntermediateField.mem_fixedField_iff (Subgroup.zpowers (σ : SSGRoute.GalQ)) y).mp
            (h5 hy) (σ : SSGRoute.GalQ) (Subgroup.mem_zpowers _)
        · intro hσ
          have h3 : (σ : SSGRoute.GalQ) θ' = θ' :=
            (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ θ'
              (IntermediateField.subset_adjoin ℚ ({θ'} : Set SSGRoute.QBar)
                (Set.mem_singleton θ'))
          have h4 : ((σ : SSGRoute.GalQ) θ') / θ' = 1 := by rw [h3, div_self hθ'0]
          have h5 : (((ψ σ : ↥(rootsOfUnity (p ^ (a + 1)) SSGRoute.QBar)) : SSGRoute.QBarˣ) :
              SSGRoute.QBar) = 1 := by
            rw [hψ σ, h4]
          have h6 : ψ σ = 1 := by
            apply Subtype.ext
            apply Units.ext
            simpa using h5
          have h7 : χ' σ = 1 := by
            rw [show χ' σ = (zr hζu).symm (ψ σ) from rfl, h6, map_one]
          exact MonoidHom.mem_ker.mpr h7
      rw [hker]
      exact hFixOpen.preimage continuous_subtype_val
    · have hine : ∀ σ : ↥(SSGRoute.decomp ℚ A),
          ∃ τ ∈ ValuationSubring.inertiaSubgroup ℚ A, χ τ = χ σ := by
        intro σ
        obtain ⟨τ, hτI, hτχ⟩ := hiner σ
        exact ⟨τ, (mem_inertiaSubgroup_iff τ).mpr hτI, hτχ⟩
      have hres := exists_inertia_of_lift hp (ValuationSubring.inertiaSubgroup ℚ A) χ' χ (fun σ => (hred σ).symm) hine hχ1
      intro σ
      obtain ⟨τ, hτmem, hτχ⟩ := hres σ
      exact ⟨τ, (mem_inertiaSubgroup_iff τ).mp hτmem, hτχ⟩

end Work.SSGRoute
