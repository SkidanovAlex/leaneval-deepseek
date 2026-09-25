import Mathlib
import Submission.Work.CFTLib.Basic
import Submission.Work.Tower.TowerCut.isPGroup_gal_iSup

/-!
# The Galois group of the normal closure of a degree-`p` Galois extension is a `p`-group

Let `F` be a number field, `K'/F` a finite Galois `p`-extension, `L'/K'` a Galois extension of
degree the prime `p`, and let `M = conjSup p K' L'` be the compositum, inside the algebraic closure
of `F`, of the conjugates `σ(L')` (`σ ∈ Gal(K'/F)`).  If `M/F` is Galois, then `Gal(M/F)` is a
`p`-group.

Proof.  Restriction to `K'` (which is contained in `M`) gives a homomorphism
`Gal(M/F) →* Gal(K'/F)` whose kernel is the group of automorphisms of `M` fixing `K'`
pointwise.  The target is a `p`-group by hypothesis, so it suffices to show that the kernel is one:
for `τ` in the kernel, the lift of `τ` to the algebraic closure is linear over `K'` and restricts
to an automorphism of each conjugate `conjT K' L' σ`, which has order dividing `p` by Artin's
argument (`pow_fixes_conjT`); hence `τ^p` fixes every conjugate pointwise and therefore, since the conjugates
generate `M` over `K'`, is the identity.
-/

namespace Work.CFTLib.ConjSup

noncomputable section

open Work.CFTLib

/-! ## Automorphism groups of prime degree extensions -/

/-- **Artin's argument.**  If `E/K` is finite dimensional of prime degree `p`, then every
`K`-automorphism of `E` has order dividing `p`: the fixed field `E^{⟨τ⟩}` of a single
automorphism `τ` satisfies `[E : E^{⟨τ⟩}] = orderOf τ`, and `orderOf τ` divides `[E : K] = p`. -/
theorem pow_eq_one_of_finrank_prime {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] {p : ℕ} [Fact p.Prime] (h : Module.finrank K E = p)
    (τ : E ≃ₐ[K] E) : τ ^ p = 1 := by
  have hfix : Module.finrank ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) E =
      orderOf τ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have htower := Module.finrank_mul_finrank K
    ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) E
  rw [hfix, h] at htower
  exact (orderOf_dvd_iff_pow_eq_one).mp ⟨_, by rw [← htower, mul_comm]⟩

/-- The automorphism group of a finite dimensional field extension of prime degree `p` is a
`p`-group. -/
theorem isPGroup_aut_of_finrank_prime {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] {p : ℕ} [Fact p.Prime] (h : Module.finrank K E = p) :
    IsPGroup p (E ≃ₐ[K] E) :=
  fun τ => ⟨1, by rw [pow_one]; exact pow_eq_one_of_finrank_prime h τ⟩

/-! ## The conjugates and their basic properties -/

variable {F : Type} [Field F] [NumberField F]

/-- The conjugate of `L'` by `σ ∈ Gal(K'/F)`: the image of `L'` under the extension
`σ.liftNormal (AlgebraicClosure F)` of `σ` to the algebraic closure. -/
def conjT (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) (σ : ↥K' ≃ₐ[F] ↥K') :
    IntermediateField F (AlgebraicClosure F) :=
  (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom

/-- `conjSup p K' L'` is the supremum of the conjugates, by definition. -/
theorem conjSup_eq_iSup (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) :
    (⨆ σ : ↥K' ≃ₐ[F] ↥K', conjT K' L' σ) = conjSup p K' L' := rfl

/-- `K'` is contained in every conjugate of `L'`. -/
theorem le_conjT (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) (σ : ↥K' ≃ₐ[F] ↥K') :
    K' ≤ conjT K' L' σ := by
  intro x hx
  rw [conjT, IntermediateField.mem_map]
  refine ⟨((σ.symm ⟨x, hx⟩ : ↥K') : AlgebraicClosure F), ?_, ?_⟩
  · exact L'.algebraMap_mem (σ.symm ⟨x, hx⟩)
  · change σ.liftNormal (AlgebraicClosure F)
      ((algebraMap ↥K' (AlgebraicClosure F)) (σ.symm ⟨x, hx⟩)) = x
    rw [AlgEquiv.liftNormal_commutes]
    simp

/-- Every conjugate is contained in `conjSup p K' L'`. -/
theorem conjT_le_conjSup (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) (σ : ↥K' ≃ₐ[F] ↥K') :
    conjT K' L' σ ≤ conjSup p K' L' :=
  le_iSup (fun σ => conjT K' L' σ) σ

/-- `K' ≤ conjSup p K' L'`. -/
theorem le_conjSup (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) :
    K' ≤ conjSup p K' L' :=
  (le_conjT K' L' 1).trans (conjT_le_conjSup p K' L' 1)

/-- The restriction of the extension of `σ` to the algebraic closure is a ring isomorphism onto
the conjugate `conjT K' L' σ`. -/
def conjRingEquiv (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) (σ : ↥K' ≃ₐ[F] ↥K') :
    ↥L' ≃+* ↥(toOver (le_conjT K' L' σ)) where
  toFun y := ⟨σ.liftNormal (AlgebraicClosure F) y,
    (IntermediateField.mem_map (L'.restrictScalars F)).mpr ⟨y, y.2, rfl⟩⟩
  invFun x := ⟨(σ.liftNormal (AlgebraicClosure F)).symm x, by
    obtain ⟨y, hy, hxy⟩ := (IntermediateField.mem_map (L'.restrictScalars F)).mp x.2
    rw [← hxy]
    simpa using hy⟩
  left_inv y := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- Each conjugate, with its `K'`-algebra structure, is normal over `K'`: it is the image of the
normal extension `L'/K'` under an isomorphism of `A` over `F` realising the automorphism `σ` of
`K'`. -/
theorem conjT_normal (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [IsGalois ↥K' ↥L']
    (σ : ↥K' ≃ₐ[F] ↥K') : Normal ↥K' ↥(toOver (le_conjT K' L' σ)) :=
  Normal.of_equiv_equiv (F := ↥K') (E := ↥L')
    (M := ↥K') (N := ↥(toOver (le_conjT K' L' σ)))
    (f := σ.toRingEquiv) (g := conjRingEquiv p K' L' σ) (by
      ext k
      exact (AlgEquiv.liftNormal_commutes σ (AlgebraicClosure F) k).symm)

/-- The conjugate, as an `F`-algebra, is isomorphic to `L'`. -/
def conjAlgEquivF (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) (σ : ↥K' ≃ₐ[F] ↥K') :
    ↥L' ≃ₐ[F] ↥(toOver (le_conjT K' L' σ)) :=
  AlgEquiv.ofRingEquiv (f := conjRingEquiv p K' L' σ) (by
    intro c
    exact Subtype.ext (AlgEquiv.commutes (σ.liftNormal (AlgebraicClosure F)) c))

/-- The conjugate has degree `p` over `K'`. -/
theorem conjT_finrank_toOver (p : ℕ) (K' : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K'] (L' : IntermediateField ↥K' (AlgebraicClosure F))
    (σ : ↥K' ≃ₐ[F] ↥K') (hLdeg : Module.finrank ↥K' L' = p) :
    Module.finrank ↥K' ↥(toOver (le_conjT K' L' σ)) = p := by
  have h1 : Module.finrank F ↥(toOver (le_conjT K' L' σ)) = Module.finrank F ↥L' :=
    (LinearEquiv.finrank_eq ((conjAlgEquivF p K' L' σ).toLinearEquiv)).symm
  have h2 : Module.finrank F ↥L' = Module.finrank F ↥K' * Module.finrank ↥K' ↥L' :=
    (Module.finrank_mul_finrank F ↥K' ↥L').symm
  have h3 := Module.finrank_mul_finrank F ↥K' ↥(toOver (le_conjT K' L' σ))
  rw [h1, h2, hLdeg] at h3
  exact Nat.mul_left_cancel (Module.finrank_pos (R := F) (M := ↥K')) h3

/-- Each conjugate is finite dimensional over `K'`. -/
theorem conjT_finiteDimensional (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K'] (L' : IntermediateField ↥K' (AlgebraicClosure F))
    (σ : ↥K' ≃ₐ[F] ↥K') (hLdeg : Module.finrank ↥K' L' = p) :
    FiniteDimensional ↥K' ↥(toOver (le_conjT K' L' σ)) :=
  FiniteDimensional.of_finrank_pos (by
    rw [conjT_finrank_toOver p K' L' σ hLdeg]
    exact (Fact.out : p.Prime).pos)

/-- The automorphism group of a conjugate over `K'` is a `p`-group. -/
theorem isPGroup_gal_conjT (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K'] (L' : IntermediateField ↥K' (AlgebraicClosure F))
    (σ : ↥K' ≃ₐ[F] ↥K') (hLdeg : Module.finrank ↥K' L' = p) :
    IsPGroup p (↥(toOver (le_conjT K' L' σ)) ≃ₐ[↥K'] ↥(toOver (le_conjT K' L' σ))) := by
  haveI := conjT_finiteDimensional p K' L' σ hLdeg
  exact isPGroup_aut_of_finrank_prime (conjT_finrank_toOver p K' L' σ hLdeg)

/-! ## The key lemma -/

/-- **Key lemma.**  Let `τ` be an `F`-automorphism of `M = conjSup p K' L'` which fixes `K'`
pointwise.  Then `τ ^ p` fixes each conjugate `conjT K' L' σ` pointwise.

Indeed, `τ` lifts to an `F`-automorphism `tl` of the algebraic closure, which is linear over `K'`
(since `τ` fixes `K'` pointwise), hence restricts to an automorphism of the conjugate `conjT σ`;
that restriction has order dividing `p` by Artin's argument, so its `p`-th power is the identity.
Transporting back along `AlgEquiv.restrict_liftNormal` gives the claim. -/
theorem pow_fixes_conjT (p : ℕ) [Fact p.Prime] (K' : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    (hLgal : IsGalois ↥K' ↥L') (hLdeg : Module.finrank ↥K' L' = p)
    (hMgal : IsGalois F ↥(conjSup p K' L'))
    (τ : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L'))
    (hτfix : ∀ k : ↥K', τ ⟨k.1, (le_conjSup p K' L') k.2⟩ = ⟨k.1, (le_conjSup p K' L') k.2⟩)
    (σ : ↥K' ≃ₐ[F] ↥K') (x : ↥(toOver (le_conjT K' L' σ))) :
    ((τ ^ p) ⟨x.1, (conjT_le_conjSup p K' L' σ) x.2⟩ : ↥(conjSup p K' L')) =
      ⟨x.1, (conjT_le_conjSup p K' L' σ) x.2⟩ := by
  haveI : IsGalois ↥K' ↥L' := hLgal
  haveI hNormalM : Normal F ↥(conjSup p K' L') := hMgal.to_normal
  haveI : Normal ↥K' ↥(toOver (le_conjT K' L' σ)) := conjT_normal p K' L' σ
  haveI : FiniteDimensional ↥K' ↥(toOver (le_conjT K' L' σ)) :=
    conjT_finiteDimensional p K' L' σ hLdeg
  let tl : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := τ.liftNormal (AlgebraicClosure F)
  have htlfix : ∀ k : ↥K', tl (algebraMap ↥K' (AlgebraicClosure F) k) =
      algebraMap ↥K' (AlgebraicClosure F) k := by
    intro k
    change (τ.liftNormal (AlgebraicClosure F))
      ((algebraMap ↥(conjSup p K' L') (AlgebraicClosure F))
        ⟨k.1, (le_conjSup p K' L') k.2⟩) = _
    rw [AlgEquiv.liftNormal_commutes]
    exact congr_arg Subtype.val (hτfix k)
  let tlK : AlgebraicClosure F ≃ₐ[↥K'] AlgebraicClosure F :=
    AlgEquiv.ofRingEquiv (f := tl.toRingEquiv) htlfix
  have htlKcoe : (AlgEquiv.restrictScalarsHom F tlK) = tl := AlgEquiv.ext (fun _ => rfl)
  let ρ : ↥(toOver (le_conjT K' L' σ)) ≃ₐ[↥K'] ↥(toOver (le_conjT K' L' σ)) :=
    AlgEquiv.restrictNormalHom (F := ↥K') (K₁ := AlgebraicClosure F)
      (↥(toOver (le_conjT K' L' σ))) tlK
  have hρ : ρ ^ p = 1 := pow_eq_one_of_finrank_prime (conjT_finrank_toOver p K' L' σ hLdeg) ρ
  have h1 : AlgEquiv.restrictNormalHom (F := ↥K') (K₁ := AlgebraicClosure F)
      (↥(toOver (le_conjT K' L' σ))) (tlK ^ p) = 1 := by
    rw [map_pow, hρ]
  have h2 := AlgEquiv.restrictNormalHom_apply (F := ↥K') (K₁ := AlgebraicClosure F)
    (L := (toOver (le_conjT K' L' σ))) (tlK ^ p) x
  rw [h1] at h2
  simp only [AlgEquiv.one_apply] at h2
  have hpow : AlgEquiv.restrictScalarsHom F (tlK ^ p) = tl ^ p := by
    rw [map_pow, htlKcoe]
  have hnat : (((τ ^ p) ⟨x.1, (conjT_le_conjSup p K' L' σ) x.2⟩ :
      ↥(conjSup p K' L')) : AlgebraicClosure F) =
      (tl ^ p) ((⟨x.1, (conjT_le_conjSup p K' L' σ) x.2⟩ : ↥(conjSup p K' L')) :
        AlgebraicClosure F) := by
    have hbase : (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F)
        (↥(conjSup p K' L'))) tl = τ := by
      change (τ.liftNormal (AlgebraicClosure F)).restrictNormal ↥(conjSup p K' L') = τ
      rw [AlgEquiv.restrict_liftNormal]
    have hn : (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F)
        (↥(conjSup p K' L'))) (tl ^ p) = τ ^ p := by
      rw [map_pow, hbase]
    have h3 := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := AlgebraicClosure F)
      (L := (conjSup p K' L')) (tl ^ p) ⟨x.1, (conjT_le_conjSup p K' L' σ) x.2⟩
    rw [hn] at h3
    exact h3
  refine Subtype.ext ?_
  rw [hnat, ← hpow]
  exact h2.symm

/-- Conjugation of `R`-algebra automorphisms along an `R`-algebra isomorphism. -/
def algEquivConjMulEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) : (A ≃ₐ[R] A) ≃* (B ≃ₐ[R] B) where
  toFun σ := e.symm.trans (σ.trans e)
  invFun τ := e.trans (τ.trans e.symm)
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp [AlgEquiv.mul_apply]

theorem isPGroup (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (hKp : IsPGroup p (K' ≃ₐ[F] K'))
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    (hLgal : IsGalois ↥K' L') (hLdeg : Module.finrank ↥K' L' = p)
    (hMgal : IsGalois F ↥(conjSup p K' L')) :
    IsPGroup p (↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L')) := by
  haveI : IsGalois ↥K' ↥L' := hLgal
  haveI : Normal F ↥(conjSup p K' L') := hMgal.to_normal
  -- `K'` inside `M`, and its fixing subgroup
  have hK'leM : K' ≤ conjSup p K' L' := le_conjSup p K' L'
  let NK : IntermediateField F ↥(conjSup p K' L') := K'.restrict hK'leM
  haveI hNKnormal : Normal F ↥NK := Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hK'leM)
  -- restriction on `K'`, as a homomorphism `Gal(M/F) →* Gal(K'/F)`
  let φ : (↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L')) →* (↥K' ≃ₐ[F] ↥K') :=
    ((algEquivConjMulEquiv (IntermediateField.restrictAlgEquiv hK'leM)).symm).toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(conjSup p K' L')) (↥NK))
  -- elements of the kernel fix `K'` pointwise
  have hker_fixes : ∀ τ : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L'), τ ∈ φ.ker →
      ∀ x : ↥NK, τ x = x := by
    intro τ hτ x
    have hf : (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(conjSup p K' L')) (↥NK)) τ = 1 := by
      have h1 : φ τ = 1 := by simpa only [MonoidHom.mem_ker] using hτ
      have h1' : ((algEquivConjMulEquiv (IntermediateField.restrictAlgEquiv hK'leM)).symm)
          ((AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(conjSup p K' L')) (↥NK)) τ) = 1 := h1
      exact (algEquivConjMulEquiv (IntermediateField.restrictAlgEquiv hK'leM)).symm.injective
        (by rw [h1', map_one])
    have h2 := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := ↥(conjSup p K' L'))
      (L := NK) τ x
    rw [hf] at h2
    simp only [AlgEquiv.one_apply] at h2
    exact h2.symm
  -- the conjugates generate `M` over `F`
  have hsup : (⨆ σ : ↥K' ≃ₐ[F] ↥K',
      (conjT K' L' σ).restrict (conjT_le_conjSup p K' L' σ)) = ⊤ := by
    apply IntermediateField.lift_injective (conjSup p K' L')
    rw [Work.Tower.TowerCut.lift_iSup (conjSup p K' L')
      (fun σ : ↥K' ≃ₐ[F] ↥K' => (conjT K' L' σ).restrict (conjT_le_conjSup p K' L' σ))]
    simp only [IntermediateField.lift_restrict]
    rw [← conjSup_eq_iSup p K' L', IntermediateField.lift_top]
  -- the kernel is a `p`-group
  have hker : IsPGroup p φ.ker := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    refine Subtype.ext ?_
    have hτfix : ∀ k : ↥K', (g : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L'))
        ⟨k.1, hK'leM k.2⟩ = ⟨k.1, hK'leM k.2⟩ := by
      intro k
      simpa using hker_fixes (g : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L')) g.2
        (⟨⟨k.1, hK'leM k.2⟩, IntermediateField.mem_restrict hK'leM _ |>.mpr k.2⟩ : ↥NK)
    have hmem : (g : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L')) ^ p ∈
        ⨅ σ : ↥K' ≃ₐ[F] ↥K',
          ((conjT K' L' σ).restrict (conjT_le_conjSup p K' L' σ)).fixingSubgroup := by
      rw [Subgroup.mem_iInf]
      intro σ
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : (x : AlgebraicClosure F) ∈ conjT K' L' σ :=
        (IntermediateField.mem_restrict (conjT_le_conjSup p K' L' σ) x).mp hx
      have hkey := pow_fixes_conjT p K' L' hLgal hLdeg hMgal
        (g : ↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L')) hτfix σ
        (⟨(x : AlgebraicClosure F), hx'⟩ : ↥(toOver (le_conjT K' L' σ)))
      convert hkey using 2
    rw [← Work.Tower.TowerCut.fixingSubgroup_iSup
      (fun σ : ↥K' ≃ₐ[F] ↥K' => (conjT K' L' σ).restrict (conjT_le_conjSup p K' L' σ)), hsup,
      IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
    exact hmem
  -- conclude: `Gal(M/F)` is an extension of `Gal(K'/F)` by the kernel
  have htop : IsPGroup p (⊤ : Subgroup (↥K' ≃ₐ[F] ↥K')) := IsPGroup.to_subgroup hKp ⊤
  have hmain := IsPGroup.comap_of_ker_isPGroup htop φ hker
  rw [Subgroup.comap_top] at hmain
  exact IsPGroup.of_equiv hmain (Subgroup.topEquiv)

end

end Work.CFTLib.ConjSup
