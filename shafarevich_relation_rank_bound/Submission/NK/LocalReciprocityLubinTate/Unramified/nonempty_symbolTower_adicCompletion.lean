import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_nested_unramified_levels
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_unramifiedSymbol_family
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_family
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits_gen
import Submission.NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity
import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_lubinTateModule
import Submission.NK.LocalReciprocityLubinTate.Units.inf_sup_zpowers_pow_eq_gen
import Submission.NK.FieldTheory.Galois.exists_prod_restrictNormalHom_of_card
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_symbol_family_map_algEquiv

namespace NK.LocalReciprocityLubinTate.Unramified

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open scoped ValuativeRel

noncomputable section

/-- **The group-theoretic index squeeze.** -/
private theorem le_of_le_of_index_eq {G : Type*} [Group G] {N A : Subgroup G}
    (h : N ≤ A) (hN : N.index ≠ 0) (hcard : N.index ≤ A.index) : A ≤ N := by
  haveI : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr hN
  have hA : A.index ≠ 0 := (Subgroup.finiteIndex_of_le h).index_ne_zero
  have hidx : A.index ≤ N.index := Subgroup.index_antitone h
  have hidxeq : N.index = A.index := le_antisymm hcard hidx
  have hrel : N.relIndex A = 1 := by
    have h1 : N.relIndex A * A.index = A.index := by
      rw [Subgroup.relIndex_mul_index h, hidxeq]
    have h2 : N.relIndex A * A.index = 1 * A.index := by
      rw [one_mul]
      exact h1
    exact mul_right_cancel₀ hA h2
  exact Subgroup.relIndex_eq_one.mp hrel

/-- **Commutativity of a Galois group transports along an `F`-algebra isomorphism.** -/
private theorem commutative_of_algEquiv {F : Type*} {Ω Ω' : Type*} [Field F] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F Ω'] (e : Ω ≃ₐ[F] Ω')
    (h : ∀ σ τ : Ω ≃ₐ[F] Ω, σ * τ = τ * σ) :
    ∀ σ τ : Ω' ≃ₐ[F] Ω', σ * τ = τ * σ := by
  intro σ τ
  apply (AlgEquiv.autCongr e.symm).injective
  rw [map_mul, map_mul]
  exact h _ _

/-- Restriction of an `F`-automorphism of the normal field `B` to the normal subfield `A ≤ B`. -/
private noncomputable def resLevel {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    (A B : IntermediateField F F') [Normal F ↥A] [Normal F ↥B] (h : A ≤ B) :
    (↥B ≃ₐ[F] ↥B) →* (↥A ≃ₐ[F] ↥A) := by
  letI : Algebra ↥A ↥B := RingHom.toAlgebra (IntermediateField.inclusion h)
  haveI : IsScalarTower F ↥A ↥B := IsScalarTower.of_algebraMap_eq fun x =>
    (IntermediateField.inclusion h).commutes x
  exact AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥B) ↥A

private theorem resLevel_apply_val {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    (A B : IntermediateField F F') [Normal F ↥A] [Normal F ↥B] (h : A ≤ B)
    (σ : ↥B ≃ₐ[F] ↥B) (x : ↥A) :
    (((resLevel A B h σ) x : ↥A) : F') = ((σ ⟨x.1, h x.2⟩ : ↥B) : F') := by
  letI : Algebra ↥A ↥B := RingHom.toAlgebra (IntermediateField.inclusion h)
  haveI : IsScalarTower F ↥A ↥B := IsScalarTower.of_algebraMap_eq fun x =>
    (IntermediateField.inclusion h).commutes x
  have h1 : (algebraMap ↥A ↥B) (((AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥B) ↥A) σ) x)
      = σ ((algebraMap ↥A ↥B) x) :=
    AlgEquiv.restrictNormal_commutes (F := F) σ ↥A x
  have h2 : (algebraMap ↥A ↥B) x = ⟨x.1, h x.2⟩ := rfl
  rw [h2] at h1
  exact congrArg (fun z : ↥B => (z : F')) h1

theorem nonempty_symbolTower_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    Nonempty (NK.LocalReciprocityLubinTate.LubinTateSymbolTower (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))) := by
  classical
  let F := Q.adicCompletion K
  let F' := SeparableClosure (Q.adicCompletion K)
  let MM := NK.LocalReciprocity.maxAbelianSubext F F'
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  -- ## the unramified side
  obtain ⟨E, hEmono, γ, hEfd, hEgal, hEfin, hγord, hγcompat, hEnorm⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.exists_nested_unramified_levels (K := K) Q
  have hEnorm' : ∀ m : ℕ, NK.LocalReciprocity.normGroup F ↥(E m) =
      Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F 0 := by
    intro m
    have h1 : NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q (Nat.factorial (m+1)) =
        Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
          NK.LocalReciprocityLubinTate.higherUnits F 0 :=
      NK.LocalReciprocityLubinTate.Unramified.unramifiedNormGroup_eq_zpowers_sup Q π hπ _
    simp only [NK.LocalReciprocityLubinTate.unramifiedNormGroup] at h1
    rw [hEnorm m]
    exact h1
  obtain ⟨Ψ, hΨsurj, hΨπ, hΨunit, hΨcompat⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.exists_unramifiedSymbol_family Q hπ E hEmono
      hEfd hEgal hEfin γ hγord hγcompat hEnorm
  have hΨker : ∀ m : ℕ, MonoidHom.ker (Ψ m) =
      Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F 0 := by
    intro m
    have hle : Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F 0 ≤ MonoidHom.ker (Ψ m) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, map_pow, hΨπ m]
        rw [← hγord m]; exact pow_orderOf_eq_one (γ m)
      · rw [NK.LocalReciprocityLubinTate.Unramified.higherUnits_zero F]
        rintro _ ⟨u, rfl⟩
        exact MonoidHom.mem_ker.mpr (hΨunit m u)
    have hNidx : (Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F 0).index = Nat.factorial (m+1) := by
      rw [NK.LocalReciprocityLubinTate.Unramified.higherUnits_zero F]
      exact NK.LocalReciprocityLubinTate.Units.index_zpowers_pow_sup_range_units F π hπ
        (Nat.factorial_pos (m+1))
    have hKidx : (MonoidHom.ker (Ψ m)).index = Nat.factorial (m+1) := by
      haveI : FiniteDimensional F ↥(E m) := hEfd m
      haveI : IsGalois F ↥(E m) := hEgal m
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (hΨsurj m), Subgroup.card_top,
        IsGalois.card_aut_eq_finrank F ↥(E m), hEfin m]
    exact le_antisymm (le_of_le_of_index_eq hle
      (by rw [hNidx]; exact Nat.factorial_ne_zero (m+1))
      (by rw [hNidx, hKidx])) hle
  have hEcomm : ∀ m : ℕ, ∀ σ τ : ↥(E m) ≃ₐ[F] ↥(E m), σ * τ = τ * σ := by
    intro m σ τ
    haveI : FiniteDimensional F ↥(E m) := hEfd m
    haveI : IsGalois F ↥(E m) := hEgal m
    have htop : Subgroup.zpowers (γ m) = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, hγord m, IsGalois.card_aut_eq_finrank F ↥(E m), hEfin m]
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top σ)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top τ)
    rw [← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
  have hEmono' : ∀ {m m' : ℕ}, m ≤ m' → E m ≤ E m' := by
    intro m m' h
    induction h with
    | refl => exact le_rfl
    | step hle ih => exact ih.trans (hEmono _)
  have hKey : ∀ (d : ℕ) (m : ℕ) (x : Fˣ) (z : ↥(E m)),
      ((Ψ (m+d) x) ⟨z.1, hEmono' (Nat.le_add_right m d) z.2⟩ : ↥(E (m+d))) =
        ⟨((Ψ m x) z).1, hEmono' (Nat.le_add_right m d) ((Ψ m x) z).2⟩ := by
    intro d
    induction d with
    | zero => intro m x z; rfl
    | succ d ih =>
        intro m x z
        have hstep := hΨcompat (m+d) x ⟨z.1, hEmono' (Nat.le_add_right m d) z.2⟩
        have hih := ih m x z
        have h1 : ((Ψ (m+(d+1))) x) ⟨z.1, hEmono' (Nat.le_add_right m (d+1)) z.2⟩
            = ((Ψ (m+d+1)) x) ⟨(⟨z.1, hEmono' (Nat.le_add_right m d) z.2⟩ : ↥(E (m+d))).1,
                hEmono (m+d) (⟨z.1, hEmono' (Nat.le_add_right m d) z.2⟩ : ↥(E (m+d))).2⟩ := rfl
        exact h1.trans (hstep.trans
          (Subtype.ext (congrArg (fun w : ↥(E (m+d)) => (w : F')) hih)))
  have hΨcompat_gen : ∀ {m m' : ℕ} (hm : m ≤ m') (x : Fˣ) (z : ↥(E m)),
      ((Ψ m' x) ⟨z.1, hEmono' hm z.2⟩ : ↥(E m')) =
        ⟨((Ψ m x) z).1, hEmono' hm ((Ψ m x) z).2⟩ := by
    intro m m' hm x z
    obtain ⟨d, rfl⟩ := Nat.le.dest hm
    exact hKey d m x z
  -- ## the Lubin–Tate side
  obtain ⟨P, hPirr, hPcoe⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.exists_irreducible_natCast_of_isUniformizer F π hπ
  obtain ⟨Mlt, hMltpi⟩ := NK.LocalReciprocityLubinTate.LubinTate.nonempty_lubinTateModule
    (NK.LocalReciprocityLubinTate.LubinTate.isLubinTateCoeff_integers F P hPirr)
    (NK.LocalReciprocityLubinTate.LubinTate.isFrobeniusPower_integers F P hPirr)
    (NK.LocalReciprocityLubinTate.LubinTate.isLubinTateSeries_piXAddXq P
      (NK.LocalReciprocityLubinTate.residueCard F) hq)
  obtain ⟨Φ, hKmono, hΦsurj, hΦker, hΦcompat⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_family P hPirr π hPcoe.symm Mlt hMltpi
  let e : AlgebraicClosure F ≃ₐ[F] F' := IsSepClosure.equiv F (AlgebraicClosure F) F'
  let LTL : ℕ → IntermediateField F (AlgebraicClosure F) := fun n =>
    NK.LocalReciprocityLubinTate.LTLevel F (P : F) (NK.LocalReciprocityLubinTate.residueCard F) n
  let Kt : ℕ → IntermediateField F F' := fun n => IntermediateField.map e.toAlgHom (LTL n)
  have hKmono' : ∀ {n n' : ℕ}, n ≤ n' → Kt n ≤ Kt n' := fun h =>
    IntermediateField.map_mono e.toAlgHom (hKmono h)
  have hKfd : ∀ n : ℕ, FiniteDimensional F ↥(Kt n) := by
    intro n
    haveI : FiniteDimensional F ↥(LTL n) :=
      NK.LocalReciprocityLubinTate.LubinTate.finiteDimensional_LTLevel F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n hq
    exact FiniteDimensional.of_surjective (IntermediateField.equivMap (LTL n) e.toAlgHom).toLinearEquiv.toLinearMap
      (IntermediateField.equivMap (LTL n) e.toAlgHom).toLinearEquiv.surjective
  have hKgal : ∀ n : ℕ, IsGalois F ↥(Kt n) := by
    intro n
    haveI : IsGalois F ↥(LTL n) :=
      NK.LocalReciprocityLubinTate.LubinTate.isGalois_LTLevel F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n hq
    exact IsGalois.of_algEquiv (IntermediateField.equivMap (LTL n) e.toAlgHom)
  have hKcomm : ∀ n : ℕ, ∀ σ τ : ↥(Kt (n+1)) ≃ₐ[F] ↥(Kt (n+1)), σ * τ = τ * σ := by
    intro n
    exact commutative_of_algEquiv (IntermediateField.equivMap (LTL (n+1)) e.toAlgHom)
      (NK.LocalReciprocityLubinTate.LubinTate.LTLevel_commutative P hPirr (n+1) (by omega))
  have hKnorm : ∀ n : ℕ, NK.LocalReciprocity.normGroup F ↥(Kt (n+1)) =
      Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F (n+1) := by
    intro n
    rw [← NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.equivMap (LTL (n+1)) e.toAlgHom)]
    change NK.LocalReciprocity.normGroup F ↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n+1)) = _
    rw [hPcoe]
    exact NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity F π hπ (n+1) (by omega)
  have hKfinrank : ∀ n : ℕ, Module.finrank F ↥(Kt (n+1)) =
      (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ n := by
    intro n
    haveI : FiniteDimensional F ↥(LTL (n+1)) :=
      NK.LocalReciprocityLubinTate.LubinTate.finiteDimensional_LTLevel F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) (n+1) hq
    rw [← LinearEquiv.finrank_eq (IntermediateField.equivMap (LTL (n+1)) e.toAlgHom).toLinearEquiv]
    change Module.finrank F ↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n+1)) = _
    rw [hPcoe]
    exact NK.LocalReciprocityLubinTate.Unramified.finrank_LTLevel_eq_of_isUniformizer F π hπ (n+1) (by omega)
  -- ## transport of the Lubin–Tate symbols to `F'`
  have hL3 : ∃ Φ' : ∀ n : ℕ, Fˣ →* (↥(Kt n) ≃ₐ[F] ↥(Kt n)),
      (∀ n, Function.Surjective (Φ n) ↔ Function.Surjective (Φ' n)) ∧
      (∀ n, MonoidHom.ker (Φ n) = MonoidHom.ker (Φ' n)) ∧
      (∀ (n n' : ℕ) (h : n ≤ n') (x : Fˣ) (y : ↥(Kt n)),
        ((Φ' n' x) ⟨y.1, hKmono' h y.2⟩ : ↥(Kt n')) =
          ⟨((Φ' n x) y).1, hKmono' h ((Φ' n x) y).2⟩) :=
    NK.LocalReciprocityLubinTate.LubinTate.exists_symbol_family_map_algEquiv e LTL hKmono Φ hΦcompat
  obtain ⟨Φ', hΦ'surj, hΦ'ker, hΦ'compat⟩ := hL3
  have hΦ'ker' : ∀ n : ℕ, MonoidHom.ker (Φ' n) =
      Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F n := fun n =>
    (hΦ'ker n).symm.trans (hΦker n)
  -- ## the two-parameter levels
  let L : ℕ → ℕ → IntermediateField F F' := fun m n => E m ⊔ Kt (n + 1)
  have hLstruct : ∀ m n, FiniteDimensional F ↥(L m n) ∧ IsGalois F ↥(L m n) ∧
      (∀ σ τ : ↥(L m n) ≃ₐ[F] ↥(L m n), σ * τ = τ * σ) := by
    intro m n
    haveI : FiniteDimensional F ↥(E m) := hEfd m
    haveI : IsGalois F ↥(E m) := hEgal m
    haveI : FiniteDimensional F ↥(Kt (n+1)) := hKfd (n+1)
    haveI : IsGalois F ↥(Kt (n+1)) := hKgal (n+1)
    exact NK.LocalReciprocityLubinTate.Unramified.isGalois_sup_of_commutative
      (E m) (Kt (n+1)) (hEcomm m) (hKcomm n)
  have hLfd : ∀ m n, FiniteDimensional F ↥(L m n) := fun m n => (hLstruct m n).1
  have hLgal : ∀ m n, IsGalois F ↥(L m n) := fun m n => (hLstruct m n).2.1
  have hLcomm : ∀ m n, ∀ σ τ : ↥(L m n) ≃ₐ[F] ↥(L m n), σ * τ = τ * σ :=
    fun m n => (hLstruct m n).2.2
  have hLsub : ∀ m n, L m n ≤ MM := by
    intro m n
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    exact NK.LocalReciprocity.le_maxAbelianSubext_of_commutative (L m n) (hLcomm m n)
  have hLmono : ∀ {m n m' n' : ℕ}, m ≤ m' → n ≤ n' → L m n ≤ L m' n' := by
    intro m n m' n' hm hn
    exact sup_le_sup (hEmono' hm) (hKmono' (Nat.succ_le_succ hn))
  -- ## the norm group of a level, by the index squeeze
  have hLnorm : ∀ m n : ℕ, NK.LocalReciprocity.normGroup F ↥(L m n) =
      Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F (n+1) := by
    intro m n
    haveI : FiniteDimensional F ↥(E m) := hEfd m
    haveI : FiniteDimensional F ↥(Kt (n+1)) := hKfd (n+1)
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    have hleE : NK.LocalReciprocity.normGroup F ↥(L m n) ≤
        NK.LocalReciprocity.normGroup F ↥(E m) := by
      letI : Algebra ↥(E m) ↥(L m n) :=
        RingHom.toAlgebra (IntermediateField.inclusion (show E m ≤ L m n from le_sup_left))
      haveI : IsScalarTower F ↥(E m) ↥(L m n) := IsScalarTower.of_algebraMap_eq fun x =>
        (IntermediateField.inclusion (show E m ≤ L m n from le_sup_left)).commutes x
      exact NK.LocalReciprocity.normGroup_le_of_tower
    have hleK : NK.LocalReciprocity.normGroup F ↥(L m n) ≤
        NK.LocalReciprocity.normGroup F ↥(Kt (n+1)) := by
      letI : Algebra ↥(Kt (n+1)) ↥(L m n) :=
        RingHom.toAlgebra (IntermediateField.inclusion (show Kt (n+1) ≤ L m n from le_sup_right))
      haveI : IsScalarTower F ↥(Kt (n+1)) ↥(L m n) := IsScalarTower.of_algebraMap_eq fun x =>
        (IntermediateField.inclusion (show Kt (n+1) ≤ L m n from le_sup_right)).commutes x
      exact NK.LocalReciprocity.normGroup_le_of_tower
    have hleA : NK.LocalReciprocity.normGroup F ↥(L m n) ≤
        Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
          NK.LocalReciprocityLubinTate.higherUnits F (n+1) := by
      rw [← NK.LocalReciprocityLubinTate.Units.inf_sup_zpowers_pow_eq_gen F π hπ
        (Nat.factorial (m+1)) n (Nat.factorial_pos (m+1))]
      exact le_inf (hleE.trans (le_of_eq (hEnorm' m))) (hleK.trans (le_of_eq (hKnorm n)))
    have hNindex : (NK.LocalReciprocity.normGroup F ↥(L m n)).index =
        Module.finrank F ↥(L m n) := by
      rw [← NK.LocalReciprocityLubinTate.Unramified.normGroup_restrictLevel (L m n) (hLsub m n),
        NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q
          (NK.LocalReciprocityLubinTate.Unramified.restrictLevel (L m n) (hLsub m n))]
      exact (LinearEquiv.finrank_eq
        (NK.LocalReciprocityLubinTate.Unramified.restrictLevelEquiv (L m n) (hLsub m n)).toLinearEquiv).symm
    have hNpos : (NK.LocalReciprocity.normGroup F ↥(L m n)).index ≠ 0 := by
      rw [hNindex]
      exact (Module.finrank_pos (R := F) (M := ↥(L m n))).ne'
    have hcard : (NK.LocalReciprocity.normGroup F ↥(L m n)).index ≤
        (Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
          NK.LocalReciprocityLubinTate.higherUnits F (n+1)).index := by
      rw [hNindex, Subgroup.index_eq_card]
      calc Module.finrank F ↥(L m n)
          ≤ Module.finrank F ↥(E m) * Module.finrank F ↥(Kt (n+1)) :=
            IntermediateField.finrank_sup_le (E1 := E m) (E2 := Kt (n+1))
        _ = Nat.factorial (m+1) * ((NK.LocalReciprocityLubinTate.residueCard F - 1) *
              NK.LocalReciprocityLubinTate.residueCard F ^ n) := by
              rw [hEfin m, hKfinrank n]
        _ = Nat.card (Fˣ ⧸ (Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
              NK.LocalReciprocityLubinTate.higherUnits F (n+1))) := by
              rw [NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen
                F π hπ (Nat.factorial (m+1)) (n+1) (Nat.factorial_pos (m+1)) (by omega)]
              rw [Nat.add_sub_cancel, ← Nat.mul_assoc]
    exact le_antisymm hleA (le_of_le_of_index_eq hleA hNpos hcard)
  have hLindex : ∀ m n : ℕ, Module.finrank F ↥(L m n) =
      Nat.factorial (m+1) * ((NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ n) := by
    intro m n
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    have hNindex : (NK.LocalReciprocity.normGroup F ↥(L m n)).index =
        Module.finrank F ↥(L m n) := by
      rw [← NK.LocalReciprocityLubinTate.Unramified.normGroup_restrictLevel (L m n) (hLsub m n),
        NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q
          (NK.LocalReciprocityLubinTate.Unramified.restrictLevel (L m n) (hLsub m n))]
      exact (LinearEquiv.finrank_eq
        (NK.LocalReciprocityLubinTate.Unramified.restrictLevelEquiv (L m n) (hLsub m n)).toLinearEquiv).symm
    rw [← hNindex, hLnorm m n, Subgroup.index_eq_card,
      NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen
        F π hπ (Nat.factorial (m+1)) (n+1) (Nat.factorial_pos (m+1)) (by omega)]
    rw [Nat.add_sub_cancel, ← Nat.mul_assoc]
  -- ## the product decomposition of every level
  have hprod : ∀ m n, ∃ φ : (↥(L m n) ≃ₐ[F] ↥(L m n)) ≃*
      ((↥(E m) ≃ₐ[F] ↥(E m)) × (↥(Kt (n+1)) ≃ₐ[F] ↥(Kt (n+1)))),
      (∀ (σ : ↥(L m n) ≃ₐ[F] ↥(L m n)) (x : ↥(E m)),
        (((φ σ).1 x : ↥(E m)) : F') =
          ((σ ⟨x.1, (le_sup_left : E m ≤ L m n) x.2⟩ : ↥(L m n)) : F')) ∧
      (∀ (σ : ↥(L m n) ≃ₐ[F] ↥(L m n)) (y : ↥(Kt (n+1))),
        (((φ σ).2 y : ↥(Kt (n+1))) : F') =
          ((σ ⟨y.1, (le_sup_right : Kt (n+1) ≤ L m n) y.2⟩ : ↥(L m n)) : F')) := by
    intro m n
    haveI : FiniteDimensional F ↥(E m) := hEfd m
    haveI : Normal F ↥(E m) := (hEgal m).to_normal
    haveI : FiniteDimensional F ↥(Kt (n+1)) := hKfd (n+1)
    haveI : Normal F ↥(Kt (n+1)) := (hKgal (n+1)).to_normal
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    have hcardL : Nat.card (↥(L m n) ≃ₐ[F] ↥(L m n)) =
        Nat.card ((↥(E m) ≃ₐ[F] ↥(E m)) × (↥(Kt (n+1)) ≃ₐ[F] ↥(Kt (n+1)))) := by
      haveI : IsGalois F ↥(E m) := hEgal m
      haveI : IsGalois F ↥(Kt (n+1)) := hKgal (n+1)
      haveI : IsGalois F ↥(L m n) := hLgal m n
      rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F ↥(E m), hEfin m,
        IsGalois.card_aut_eq_finrank F ↥(Kt (n+1)), hKfinrank n,
        IsGalois.card_aut_eq_finrank F ↥(L m n), hLindex m n]
    exact NK.FieldTheory.Galois.exists_prod_restrictNormalHom_of_card (E m) (Kt (n+1)) hcardL
  let φφ : ∀ m n, (↥(L m n) ≃ₐ[F] ↥(L m n)) ≃*
      ((↥(E m) ≃ₐ[F] ↥(E m)) × (↥(Kt (n+1)) ≃ₐ[F] ↥(Kt (n+1)))) :=
    fun m n => Classical.choose (hprod m n)
  let symbolL : ∀ m n : ℕ, Fˣ →* (↥(L m n) ≃ₐ[F] ↥(L m n)) := fun m n =>
    (φφ m n).symm.toMonoidHom.comp ((Ψ m).prod (Φ' (n+1)))
  have hSymbolL_apply_E : ∀ (m n : ℕ) (x : Fˣ) (z : ↥(E m)),
      (((symbolL m n x) ⟨z.1, (le_sup_left : E m ≤ L m n) z.2⟩ : ↥(L m n)) : F') =
        ((Ψ m x z : ↥(E m)) : F') := by
    intro m n x z
    have h1 : (φφ m n (symbolL m n x)).1 = Ψ m x := by
      show ((φφ m n) ((φφ m n).symm (((Ψ m).prod (Φ' (n+1))) x))).1 = Ψ m x
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 := (Classical.choose_spec (hprod m n)).1 (symbolL m n x) z
    rw [h1] at h2
    exact h2.symm
  have hSymbolL_apply_K : ∀ (m n : ℕ) (x : Fˣ) (z : ↥(Kt (n+1))),
      (((symbolL m n x) ⟨z.1, (le_sup_right : Kt (n+1) ≤ L m n) z.2⟩ : ↥(L m n)) : F') =
        ((Φ' (n+1) x z : ↥(Kt (n+1))) : F') := by
    intro m n x z
    have h1 : (φφ m n (symbolL m n x)).2 = Φ' (n+1) x := by
      show ((φφ m n) ((φφ m n).symm (((Ψ m).prod (Φ' (n+1))) x))).2 = Φ' (n+1) x
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 := (Classical.choose_spec (hprod m n)).2 (symbolL m n x) z
    rw [h1] at h2
    exact h2.symm
  have hSymbolL_ker : ∀ m n : ℕ, MonoidHom.ker (symbolL m n) =
      Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F (n+1) := by
    intro m n
    have h2 : MonoidHom.ker (symbolL m n) =
        MonoidHom.ker ((Ψ m).prod (Φ' (n+1))) :=
      MonoidHom.ker_comp_of_injective ((Ψ m).prod (Φ' (n+1)))
        (φφ m n).symm.toMonoidHom (φφ m n).symm.injective
    rw [h2, MonoidHom.ker_prod, hΨker m, hΦ'ker' (n+1),
      NK.LocalReciprocityLubinTate.Units.inf_sup_zpowers_pow_eq_gen F π hπ
        (Nat.factorial (m+1)) n (Nat.factorial_pos (m+1))]
  have hSymbolL_surj : ∀ m n : ℕ, Function.Surjective (symbolL m n) := by
    intro m n
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    haveI : IsGalois F ↥(L m n) := hLgal m n
    rw [← Subgroup.index_ker (symbolL m n), hSymbolL_ker m n, Subgroup.index_eq_card,
      NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen
        F π hπ (Nat.factorial (m+1)) (n+1) (Nat.factorial_pos (m+1)) (by omega)]
    rw [Nat.add_sub_cancel, IsGalois.card_aut_eq_finrank F ↥(L m n), hLindex m n,
      ← Nat.mul_assoc]
  have hSymbolL_compatT : ∀ (m n m' n' : ℕ) (hm : m ≤ m') (hn : n ≤ n') (x : Fˣ),
      resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x) = symbolL m n x := by
    intro m n m' n' hm hn x
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    haveI : Normal F ↥(L m' n') := (hLgal m' n').to_normal
    haveI : Normal F ↥(E m) := (hEgal m).to_normal
    haveI : Normal F ↥(E m') := (hEgal m').to_normal
    haveI : Normal F ↥(Kt (n+1)) := (hKgal (n+1)).to_normal
    haveI : Normal F ↥(Kt (n'+1)) := (hKgal (n'+1)).to_normal
    set T : ↥(L m n) ≃ₐ[F] ↥(L m n) :=
      resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x) with hT
    apply (φφ m n).injective
    refine Prod.ext ?_ ?_
    · apply AlgEquiv.ext
      intro z'
      apply Subtype.ext
      have h0 : ((((φφ m n) T).1 z' : ↥(E m)) : F')
          = (((resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x))
              ⟨z'.1, (le_sup_left : E m ≤ L m n) z'.2⟩ : ↥(L m n)) : F') :=
        (Classical.choose_spec (hprod m n)).1 _ z'
      have h1 : ((((resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x))
              ⟨z'.1, (le_sup_left : E m ≤ L m n) z'.2⟩ : ↥(L m n))) : F')
          = (((symbolL m' n' x ⟨z'.1, hLmono hm hn ((le_sup_left : E m ≤ L m n) z'.2)⟩
              : ↥(L m' n'))) : F') :=
        resLevel_apply_val (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x)
          ⟨z'.1, (le_sup_left : E m ≤ L m n) z'.2⟩
      have h2 : (((symbolL m' n' x ⟨z'.1, hLmono hm hn ((le_sup_left : E m ≤ L m n) z'.2)⟩
              : ↥(L m' n'))) : F')
          = (((Ψ m' x) ⟨z'.1, hEmono' hm z'.2⟩ : ↥(E m')) : F') :=
        hSymbolL_apply_E m' n' x ⟨z'.1, hEmono' hm z'.2⟩
      have h3 : ((((Ψ m' x) ⟨z'.1, hEmono' hm z'.2⟩ : ↥(E m'))) : F')
          = (((Ψ m x) z' : ↥(E m)) : F') :=
        congrArg (fun w : ↥(E m') => (w : F')) (hΨcompat_gen hm x z')
      have h4 : ((((Ψ m x) z' : ↥(E m))) : F')
          = ((((φφ m n) (symbolL m n x)).1 z' : ↥(E m)) : F') :=
        (((Classical.choose_spec (hprod m n)).1 (symbolL m n x) z').trans
          (hSymbolL_apply_E m n x z')).symm
      exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
    · apply AlgEquiv.ext
      intro y'
      apply Subtype.ext
      have h0 : ((((φφ m n) T).2 y' : ↥(Kt (n+1))) : F')
          = (((resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x))
              ⟨y'.1, (le_sup_right : Kt (n+1) ≤ L m n) y'.2⟩ : ↥(L m n)) : F') :=
        (Classical.choose_spec (hprod m n)).2 _ y'
      have h1 : ((((resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x))
              ⟨y'.1, (le_sup_right : Kt (n+1) ≤ L m n) y'.2⟩ : ↥(L m n))) : F')
          = (((symbolL m' n' x ⟨y'.1, hLmono hm hn ((le_sup_right : Kt (n+1) ≤ L m n) y'.2)⟩
              : ↥(L m' n'))) : F') :=
        resLevel_apply_val (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x)
          ⟨y'.1, (le_sup_right : Kt (n+1) ≤ L m n) y'.2⟩
      have h2 : (((symbolL m' n' x ⟨y'.1, hLmono hm hn ((le_sup_right : Kt (n+1) ≤ L m n) y'.2)⟩
              : ↥(L m' n'))) : F')
          = (((Φ' (n'+1) x) ⟨y'.1, hKmono' (Nat.succ_le_succ hn) y'.2⟩ : ↥(Kt (n'+1))) : F') :=
        hSymbolL_apply_K m' n' x ⟨y'.1, hKmono' (Nat.succ_le_succ hn) y'.2⟩
      have h3 : ((((Φ' (n'+1) x) ⟨y'.1, hKmono' (Nat.succ_le_succ hn) y'.2⟩
              : ↥(Kt (n'+1)))) : F')
          = (((Φ' (n+1) x) y' : ↥(Kt (n+1))) : F') :=
        congrArg (fun w : ↥(Kt (n'+1)) => (w : F'))
          (hΦ'compat (n+1) (n'+1) (Nat.succ_le_succ hn) x y')
      have h4 : ((((Φ' (n+1) x) y' : ↥(Kt (n+1)))) : F')
          = ((((φφ m n) (symbolL m n x)).2 y' : ↥(Kt (n+1))) : F') :=
        (((Classical.choose_spec (hprod m n)).2 (symbolL m n x) y').trans
          (hSymbolL_apply_K m n x y')).symm
      exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hSymbolL_compat : ∀ {m n m' n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') (x : Fˣ)
      (z : ↥(L m n)),
      ((symbolL m' n' x) ⟨z.1, hLmono hm hn z.2⟩ : ↥(L m' n')) =
        ⟨((symbolL m n x) z).1, hLmono hm hn ((symbolL m n x) z).2⟩ := by
    intro m n m' n' hm hn x z
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    haveI : Normal F ↥(L m' n') := (hLgal m' n').to_normal
    have h1 := hSymbolL_compatT m n m' n' hm hn x
    have h2 : (resLevel (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x)) z
        = (symbolL m n x) z := by rw [h1]
    have h3 := resLevel_apply_val (L m n) (L m' n') (hLmono hm hn) (symbolL m' n' x) z
    refine Subtype.ext ?_
    rw [h2] at h3
    exact h3.symm
  -- ## transfer along `restrictLevel`
  let lvl : ∀ m n : ℕ, IntermediateField F MM := fun m n => restrictLevel (L m n) (hLsub m n)
  let sym : ∀ m n : ℕ, Fˣ →* (↥(lvl m n) ≃ₐ[F] ↥(lvl m n)) := fun m n =>
    (AlgEquiv.autCongr (restrictLevelEquiv (L m n) (hLsub m n))).toMonoidHom.comp (symbolL m n)
  have hSym_apply : ∀ (m n : ℕ) (x : Fˣ) (w : ↥(lvl m n)),
      (((sym m n x) w : ↥(lvl m n)) : F') =
        ((symbolL m n x ⟨(w.1 : F'), w.2⟩ : ↥(L m n)) : F') := by
    intro m n x w
    show (((AlgEquiv.autCongr (restrictLevelEquiv (L m n) (hLsub m n)) (symbolL m n x)) w
      : ↥(lvl m n)) : F') = _
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    have h1 : (restrictLevelEquiv (L m n) (hLsub m n)).symm w = ⟨(w.1 : F'), w.2⟩ := rfl
    rw [h1]
    rfl
  have hmono : ∀ {m n m' n' : ℕ}, m ≤ m' → n ≤ n' → lvl m n ≤ lvl m' n' :=
    fun hm hn => (IntermediateField.gc_map_comap MM.val).monotone_u (hLmono hm hn)
  have hSymbol_ker : ∀ m n : ℕ, MonoidHom.ker (sym m n) =
      NK.LocalReciprocity.normGroup F ↥(lvl m n) := by
    intro m n
    have h1 : MonoidHom.ker (sym m n) = MonoidHom.ker (symbolL m n) :=
      MonoidHom.ker_comp_of_injective (symbolL m n)
        (AlgEquiv.autCongr (restrictLevelEquiv (L m n) (hLsub m n))).toMonoidHom
        (AlgEquiv.autCongr (restrictLevelEquiv (L m n) (hLsub m n))).injective
    rw [h1, hSymbolL_ker m n]
    rw [show lvl m n = restrictLevel (L m n) (hLsub m n) from rfl,
      NK.LocalReciprocityLubinTate.Unramified.normGroup_restrictLevel]
    exact (hLnorm m n).symm
  have hSymbol_surj : ∀ m n : ℕ, Function.Surjective (sym m n) := fun m n =>
    (AlgEquiv.autCongr (restrictLevelEquiv (L m n) (hLsub m n))).surjective.comp
      (hSymbolL_surj m n)
  have hSymbol_compat : ∀ {m n m' n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') (x : Fˣ)
      (y : ↥(lvl m n)),
      ((sym m' n' x) ⟨y.1, hmono hm hn y.2⟩ : ↥(lvl m' n')) =
        ⟨((sym m n x) y).1, hmono hm hn ((sym m n x) y).2⟩ := by
    intro m n m' n' hm hn x y
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    haveI : Normal F ↥(L m' n') := (hLgal m' n').to_normal
    apply Subtype.ext
    apply Subtype.ext
    rw [hSym_apply m' n' x ⟨y, hmono hm hn y.2⟩, hSym_apply m n x y]
    exact congrArg (fun w : ↥(L m' n') => (w : F'))
      (hSymbolL_compat hm hn x ⟨(y.1 : F'), y.2⟩)
  -- ## assembly
  let lvlfd : ∀ m n : ℕ, FiniteDimensional F ↥(lvl m n) := fun m n => by
    haveI : FiniteDimensional F ↥(L m n) := hLfd m n
    exact inferInstance
  let lvlnormal : ∀ m n : ℕ, Normal F ↥(lvl m n) := fun m n => by
    haveI : Normal F ↥(L m n) := (hLgal m n).to_normal
    exact inferInstance
  let lvlcomm : ∀ m n : ℕ, ∀ σ τ : ↥(lvl m n) ≃ₐ[F] ↥(lvl m n), σ * τ = τ * σ :=
    fun m n => commutative_restrictLevel (L m n) (hLsub m n) (hLcomm m n)
  let lvlnorm : ∀ m n : ℕ, NK.LocalReciprocity.normGroup F ↥(lvl m n) =
      Subgroup.zpowers (π ^ Nat.factorial (m+1)) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F (n+1) := fun m n => by
    rw [show lvl m n = restrictLevel (L m n) (hLsub m n) from rfl,
      NK.LocalReciprocityLubinTate.Unramified.normGroup_restrictLevel]
    exact hLnorm m n
  exact ⟨{ level := lvl
           finiteDimensional := lvlfd
           normal := lvlnormal
           commutative := lvlcomm
           normGroup_eq := lvlnorm
           mono := hmono
           symbol := sym
           symbol_surjective := hSymbol_surj
           symbol_ker := hSymbol_ker
           symbol_compat := hSymbol_compat }⟩

end

end NK.LocalReciprocityLubinTate.Unramified
