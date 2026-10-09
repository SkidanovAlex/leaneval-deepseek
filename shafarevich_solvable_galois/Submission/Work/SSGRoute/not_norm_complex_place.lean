import Mathlib
import Submission.Work.SSGRoute.normImage_at_level_proper

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.SSGRoute

/-- **A negative real local unit at a complex archimedean place is not a `⊥`-relative norm.**

Let `L/k` be a finite Galois extension of number fields and `u` an infinite place of `L` whose
stabiliser in `Gal(L/k)` has exactly two elements (equivalently `u` is complex above a real place).
Let `y ∈ L_uˣ` be a local unit whose image under the canonical identification `L_u ≃+* ℂ` is a
complex number of **negative real part**.  Then `y` is not the norm of the quotiented level for
`N = ⊥`: there is no `bb ∈ L_uˣ` fixed by `N` with `∑_{x ∈ D_u/⊥} ρ(out x) bb = y`. -/
theorem not_norm_complex_place {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (u : NumberField.InfinitePlace L)
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofInfinite u)) = 2)
    (y : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ)
    (hy : (NumberField.InfinitePlace.Completion.extensionEmbedding u (y : u.Completion)).re < 0)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u) ⧸
      (⊥ : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u))))] :
    ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u),
        (∀ n : (⊥ : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L)
            (NK.GlobalCFT.Place.ofInfinite u))),
          (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u)).ρ
            (n : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)) bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u) ⧸
            (⊥ : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L)
              (NK.GlobalCFT.Place.ofInfinite u))),
          (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u)).ρ
            (Quotient.out x) bb) = Additive.ofMul y) := by
  classical
  rintro ⟨bb, -, hsum⟩
  -- The decomposition group `Γ = D_u` has order `2`; let `σ₀ ≠ 1` be its non-trivial element.
  obtain ⟨σ₀, hσ₀ne, hσ₀all⟩ :=
    (Nat.card_eq_two_iff' (x := (1 : stabInf (k := k) (L := L) u))).mp hcard
  have hcov : ∀ c : stabInf (k := k) (L := L) u, c = 1 ∨ c = σ₀ := by
    intro c
    by_cases h : c = 1
    · exact Or.inl h
    · exact Or.inr (hσ₀all c h)
  -- `σ₀` fixes `u`, and being non-trivial it acts by complex conjugation at `u`;
  -- in particular `u` is a complex place.
  have hσ₀mem : (σ₀ : L ≃ₐ[k] L) ∈ MulAction.stabilizer (L ≃ₐ[k] L) u := by
    rw [MulAction.mem_stabilizer_iff]
    have h := MulAction.mem_stabilizer_iff.mp σ₀.2
    rwa [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj] at h
  have hIsConj : NumberField.ComplexEmbedding.IsConj (u.embedding) σ₀.1 := by
    have hiff := NumberField.InfinitePlace.mem_stabilizer_mk_iff (u.embedding) σ₀.1
    rw [NumberField.InfinitePlace.mk_embedding] at hiff
    rcases hiff.mp hσ₀mem with h1 | hc
    · exact absurd (Subtype.ext h1) hσ₀ne
    · exact hc
  have hconj : ∀ x : L, u.embedding (σ₀.1 x) = starRingEnd ℂ (u.embedding x) := by
    intro x
    have h := RingHom.congr_fun hIsConj x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h
    exact h.symm
  have huC : u.IsComplex := by
    rw [← NumberField.InfinitePlace.mk_embedding u, NumberField.InfinitePlace.isComplex_mk_iff]
    intro hreal
    apply hσ₀ne
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have h := RingHom.congr_fun hIsConj x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h
    have h2 : (NumberField.ComplexEmbedding.conjugate (u.embedding)) x = u.embedding x :=
      RingHom.congr_fun ((NumberField.ComplexEmbedding.isReal_iff).mp hreal) x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    rw [h2] at h
    exact (u.embedding).injective h.symm
  -- The canonical identification `L_u ≃+* ℂ`, under which `σ₀` is complex conjugation.
  set e : u.Completion ≃+* ℂ :=
    NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex huC with he
  have hcact : ∀ z : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u),
      e (NK.HassePrinciple.localAutHom (K := k) (L := L) (NK.GlobalCFT.Place.ofInfinite u) σ₀ z)
        = starRingEnd ℂ (e z) := by
    intro z
    exact ringEquivComplex_localAutHom (k := k) u huC σ₀ hconj z
  -- The quotient `Γ/⊥ ≃ Γ` has exactly two elements, `1` and `q₁ = mk' ⊥ σ₀`.
  have hinj : Function.Injective ⇑(QuotientGroup.mk' (⊥ : Subgroup
      (stabInf (k := k) (L := L) u))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk'])
  set q₁ : stabInf (k := k) (L := L) u ⧸
      (⊥ : Subgroup (stabInf (k := k) (L := L) u)) :=
    QuotientGroup.mk' (⊥ : Subgroup (stabInf (k := k) (L := L) u)) σ₀ with hq₁def
  have hq₁ne : q₁ ≠ 1 := by
    intro h
    apply hσ₀ne
    apply hinj
    rw [hq₁def] at h
    rw [h, map_one]
  have hcovQ : ∀ c : stabInf (k := k) (L := L) u ⧸
      (⊥ : Subgroup (stabInf (k := k) (L := L) u)), c = 1 ∨ c = q₁ := by
    intro c
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective
      (⊥ : Subgroup (stabInf (k := k) (L := L) u)) c
    rcases hcov γ with h | h
    · left; rw [h]; exact map_one _
    · right; rw [h, hq₁def]
  have hout1 : (Quotient.out (1 : stabInf (k := k) (L := L) u ⧸
      (⊥ : Subgroup (stabInf (k := k) (L := L) u))) :
      stabInf (k := k) (L := L) u) = 1 := by
    apply hinj
    rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq', map_one]
  have houtq₁ : (Quotient.out q₁ : stabInf (k := k) (L := L) u) = σ₀ := by
    apply hinj
    rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq', hq₁def]
  -- Split the norm sum over the two-element quotient.
  set uu : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ :=
    Additive.toMul bb with huu
  have hbb : bb = Additive.ofMul uu := by rw [huu]; exact (ofMul_toMul bb).symm
  rw [hbb] at hsum
  have h1 : (NK.HassePrinciple.localUnitsRep k L
      (NK.GlobalCFT.Place.ofInfinite u)).ρ (1 : stabInf (k := k) (L := L) u)
        (Additive.ofMul uu) = Additive.ofMul uu := by
    rw [show (NK.HassePrinciple.localUnitsRep k L
        (NK.GlobalCFT.Place.ofInfinite u)).ρ (1 : stabInf (k := k) (L := L) u)
          (Additive.ofMul uu)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofInfinite u) 1 uu) from rfl,
      NK.HassePrinciple.localUnitsEquiv_one]
    rfl
  have h2 : (NK.HassePrinciple.localUnitsRep k L
      (NK.GlobalCFT.Place.ofInfinite u)).ρ σ₀ (Additive.ofMul uu)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofInfinite u) σ₀ uu) := rfl
  have hsplit2 : (∑ x : stabInf (k := k) (L := L) u ⧸
      (⊥ : Subgroup (stabInf (k := k) (L := L) u)),
      (NK.HassePrinciple.localUnitsRep k L
        (NK.GlobalCFT.Place.ofInfinite u)).ρ (Quotient.out x) (Additive.ofMul uu))
      = Additive.ofMul uu + Additive.ofMul (NK.HassePrinciple.localUnitsEquiv
          (K := k) (L := L) (NK.GlobalCFT.Place.ofInfinite u) σ₀ uu) := by
    rw [sum_eq_add_of_cover (1 : stabInf (k := k) (L := L) u ⧸
        (⊥ : Subgroup (stabInf (k := k) (L := L) u))) q₁ (Ne.symm hq₁ne) hcovQ]
    rw [hout1, houtq₁, h1, h2]
    rfl
  have hsplit : Additive.ofMul uu + Additive.ofMul (NK.HassePrinciple.localUnitsEquiv
      (K := k) (L := L) (NK.GlobalCFT.Place.ofInfinite u) σ₀ uu) = Additive.ofMul y := by
    rw [← hsplit2]; exact hsum
  rw [← ofMul_mul] at hsplit
  have hmain : uu * NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofInfinite u) σ₀ uu = y := Additive.ofMul.injective hsplit
  -- Applying `L_u ≃+* ℂ` turns the norm condition into `y = z · conj z`, a non-negative real.
  have hE := congrArg (fun w : (NK.GlobalCFT.Place.localField L
      (NK.GlobalCFT.Place.ofInfinite u))ˣ =>
      (w : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))) hmain
  simp only [Units.val_mul] at hE
  have hE' := congrArg e hE
  rw [map_mul, NK.HassePrinciple.coe_localUnitsEquiv] at hE'
  rw [hcact (uu : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))] at hE'
  rw [Complex.mul_conj] at hE'
  have hre : Complex.normSq (e (uu : NK.GlobalCFT.Place.localField L
      (NK.GlobalCFT.Place.ofInfinite u))) = (e ↑y).re := by
    have := congrArg Complex.re hE'
    simpa using this
  have hye : (e (y : u.Completion)).re
      = (NumberField.InfinitePlace.Completion.extensionEmbedding u (y : u.Completion)).re := rfl
  have hnn := Complex.normSq_nonneg (e (uu : NK.GlobalCFT.Place.localField L
      (NK.GlobalCFT.Place.ofInfinite u)))
  rw [hye] at hre
  linarith

end Work.SSGRoute
