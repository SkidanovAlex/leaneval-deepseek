import Mathlib
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.CFTLib.Existence.KummerCountNotes
import Submission.NK.CFTLib.Existence.natCard_abelianization_le_of_kummer_orbit
import Submission.NK.CFTLib.Existence.cyclotomicExtension_galois_cyclic
import Submission.NK.CFTLib.Existence.kummerOrbitHelpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bounding the norm index of the Galois closure of a degree-`p` Kummer extension

Let `K ⊆ K' ⊆ M` be a tower of number fields with `K' / K` finite Galois cyclic and
`M / K'` finite Galois of degree `p`, and let `K'` contain a primitive `p`-th root of unity `ζ`.
Then the index of the norm class subgroup of the Galois closure `N = galoisClosure K M` of `M / K`
is at most `p * [K' : K]`.

The proof is the "Kummer count" of `NK.CFTLib.Existence.natCard_abelianization_le_of_kummer_orbit`:
`[C_K : N_{N/K} C_N] = |Gal(N/K)^{ab}|` (the norm index theorem for a Galois extension, from the
fundamental class `hFC`), and `|Gal(N/K)^{ab}| ≤ p · [K' : K]`.

The Kummer input is that `M = K'(β)` for a `p`-th root `β` of an element of `K'`; the conjugates of
`M` over `K` are then the fields `K'(σ^i β)`, where `σ` is a lift of a generator of `Gal(K'/K)` to
`Gal(N/K)`, and these generate `N` over `K'` (they already form a normal extension of `K`).

The formalisation works with `NΩ` below, a copy of the Galois closure which is an intermediate
field of `Ω = AlgebraicClosure M` *over `K'`*; this makes both scalar structures (`K` and `K'`)
available without disturbing the canonical instances on `galoisClosure K M` (with which `NΩ` is
definitionally equal).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4000000

namespace NK.CFTLib.Existence

open IntermediateField

noncomputable abbrev NOmega {K : Type} [Field K] [NumberField K]
    {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
    {M : Type} [Field M] [NumberField M] [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    [FiniteDimensional K M] [FiniteDimensional K' M] :
    IntermediateField K' (AlgebraicClosure M) :=
  { (IntermediateField.normalClosure K M (AlgebraicClosure M)).toSubfield with
    algebraMap_mem' := fun c => by
      rw [IsScalarTower.algebraMap_apply K' M (AlgebraicClosure M)]
      exact AlgHom.fieldRange_le_normalClosure
        (IsScalarTower.toAlgHom K M (AlgebraicClosure M)) ⟨algebraMap K' M c, rfl⟩ }

section Main

variable {K : Type} [Field K] [NumberField K]
    {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
    {M : Type} [Field M] [NumberField M] [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    [FiniteDimensional K M] [FiniteDimensional K' M]

local notation "NΩ" => ↥(NOmega (K := K) (K' := K') (M := M))

theorem NOmega_finiteDimensional_K :
    FiniteDimensional K ↥(NOmega (K := K) (K' := K') (M := M)) := by
  change FiniteDimensional K ↥(IntermediateField.normalClosure K M (AlgebraicClosure M))
  infer_instance

attribute [local instance] NOmega_finiteDimensional_K

theorem NOmega_normal_K :
    Normal K ↥(NOmega (K := K) (K' := K') (M := M)) := by
  change Normal K ↥(IntermediateField.normalClosure K M (AlgebraicClosure M))
  infer_instance

attribute [local instance] NOmega_normal_K

theorem NOmega_isGalois_K :
    IsGalois K ↥(NOmega (K := K) (K' := K') (M := M)) := by
  change IsGalois K ↥(IntermediateField.normalClosure K M (AlgebraicClosure M))
  exact Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero

attribute [local instance] NOmega_isGalois_K

theorem NOmega_isScalarTower_K_K' :
    IsScalarTower K K' ↥(NOmega (K := K) (K' := K') (M := M)) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext
    rw [show ((algebraMap K NΩ x : NΩ) : AlgebraicClosure M)
        = algebraMap K (AlgebraicClosure M) x from rfl]
    rw [show ((algebraMap K' NΩ (algebraMap K K' x) : NΩ) : AlgebraicClosure M)
        = algebraMap K' (AlgebraicClosure M) (algebraMap K K' x) from rfl]
    rw [IsScalarTower.algebraMap_apply K K' (AlgebraicClosure M)])

attribute [local instance] NOmega_isScalarTower_K_K'

theorem NOmega_isGalois_K' [IsGalois K K'] :
    IsGalois K' ↥(NOmega (K := K) (K' := K') (M := M)) :=
  IsGalois.tower_top_of_isGalois K K' _

attribute [local instance] NOmega_isGalois_K'

theorem NOmega_finiteDimensional_K' [IsGalois K K'] :
    FiniteDimensional K' ↥(NOmega (K := K) (K' := K') (M := M)) :=
  Module.Finite.of_restrictScalars_finite K K' _

attribute [local instance] NOmega_finiteDimensional_K'

theorem NOmega_numberField :
    NumberField ↥(NOmega (K := K) (K' := K') (M := M)) :=
  NumberField.of_module_finite K _

attribute [local instance] NOmega_numberField

set_option maxHeartbeats 8000000 in
/-- **The generation statement.** -/
theorem adjoin_orbit_eq_top [IsGalois K K']
    {p : ℕ} [Fact p.Prime] {ζ : K'} (hζ : IsPrimitiveRoot ζ p)
    {a : K'ˣ} {βM : M} {β : NΩ}
    (hβM : βM ^ p = algebraMap K' M (a : K'))
    (hgenM : IntermediateField.adjoin K' ({βM} : Set M) = ⊤)
    (hβeq : (β : AlgebraicClosure M) = algebraMap M (AlgebraicClosure M) βM)
    (hβp : β ^ p = algebraMap K' NΩ (a : K'))
    (σ : K' ≃ₐ[K] K') (hσ : ∀ τ : K' ≃ₐ[K] K', ∃ n : ℕ, τ = σ ^ n)
    (σN : NΩ ≃ₐ[K] NΩ)
    (hσN : ∀ x : K', σN (algebraMap K' NΩ x) = algebraMap K' NΩ (σ x)) :
    IntermediateField.adjoin K' (Set.range fun i : ℕ => ((σN : NΩ → NΩ)^[i]) β) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  let g : ℕ → AlgebraicClosure M := fun i => (((σN ^ i) β : NΩ) : AlgebraicClosure M)
  let K'Ω : IntermediateField K (AlgebraicClosure M) :=
    (⊥ : IntermediateField K' (AlgebraicClosure M)).restrictScalars K
  have hK'Ω : (K'Ω : Set (AlgebraicClosure M)) =
      Set.range (algebraMap K' (AlgebraicClosure M)) := by
    rw [show K'Ω = (⊥ : IntermediateField K' (AlgebraicClosure M)).restrictScalars K from rfl,
      IntermediateField.coe_restrictScalars, IntermediateField.coe_bot]
  let A₀ : IntermediateField K (AlgebraicClosure M) :=
    IntermediateField.adjoin K ((K'Ω : Set (AlgebraicClosure M)) ∪ Set.range g)
  have hmemA₀ : ∀ x : AlgebraicClosure M, x ∈ (K'Ω : Set (AlgebraicClosure M)) ∪ Set.range g →
      x ∈ A₀ := fun x hx => IntermediateField.subset_adjoin K _ hx
  have hmemK'Ω : ∀ c : K', algebraMap K' (AlgebraicClosure M) c ∈ (A₀ : Set (AlgebraicClosure M)) :=
    fun c => hmemA₀ _ (Or.inl (by rw [hK'Ω]; exact Set.mem_range_self c))
  have hmemg : ∀ i : ℕ, g i ∈ (A₀ : Set (AlgebraicClosure M)) :=
    fun i => hmemA₀ _ (Or.inr ⟨i, rfl⟩)
  have hgp : ∀ i : ℕ, (g i) ^ p = algebraMap K' (AlgebraicClosure M) ((σ ^ i) (a : K')) := by
    intro i
    have h3 : (σN ^ i) (algebraMap K' NΩ (a : K')) = (σN ^ i) (β ^ p) := by rw [hβp]
    have h2 : ((σN ^ i) β) ^ p = algebraMap K' NΩ ((σ ^ i) (a : K')) := by
      rw [← map_pow, ← h3]
      clear h3
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσN, pow_succ']; rfl
    have h4 := congrArg (fun x : NΩ => (x : AlgebraicClosure M)) h2
    have h5 : g i = (((σN ^ i) β : NΩ) : AlgebraicClosure M) := rfl
    rw [h5]
    exact h4
  have horbit : ∀ (σ₀ : AlgebraicClosure M ≃ₐ[K] AlgebraicClosure M) (i : ℕ),
      σ₀ (g i) ∈ (A₀ : Set (AlgebraicClosure M)) := by
    intro σ₀ i
    obtain ⟨j, hj⟩ := exists_pow_restrict_of_algEquiv σ hσ σ₀
    have hgne : g (i + j) ≠ 0 := by
      intro h0
      have h := hgp (i + j)
      rw [h0, zero_pow hp.ne_zero] at h
      have h1 : (σ ^ (i + j)) (a : K') = 0 :=
        (algebraMap K' (AlgebraicClosure M)).injective (by simpa using h.symm)
      exact (Units.ne_zero a) ((σ ^ (i + j)).injective (by simpa using h1))
    have h1 : (σ₀ (g i)) ^ p = (g (i + j)) ^ p := by
      rw [← map_pow, hgp i, hj, hgp (i + j)]
      congr 1
      rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_comm]
    have h2 : (σ₀ (g i) / g (i + j)) ^ p = 1 := by
      rw [div_pow, h1, div_self (pow_ne_zero p hgne)]
    obtain ⟨c, hc⟩ := pow_eq_one_mem_range (k := K') (K := AlgebraicClosure M) hζ h2
    have h3 : σ₀ (g i) = algebraMap K' (AlgebraicClosure M) c * g (i + j) := by
      rw [← hc, div_mul_cancel₀ _ hgne]
    rw [h3]
    exact mul_mem (hmemK'Ω c) (hmemg (i + j))
  have hNormal₀ : Normal K A₀ := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro σ₀
    rw [show A₀ = IntermediateField.adjoin K ((K'Ω : Set (AlgebraicClosure M)) ∪ Set.range g)
      from rfl, IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨x, hx, rfl⟩
    rcases hx with hx | ⟨i, rfl⟩
    · rw [hK'Ω] at hx
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨j, hj⟩ := exists_pow_restrict_of_algEquiv σ hσ σ₀
      have hx' : σ₀ ((algebraMap K' (AlgebraicClosure M)) c) ∈
          (A₀ : Set (AlgebraicClosure M)) := by
        rw [hj]
        exact hmemK'Ω _
      simpa using hx' 
    · exact horbit σ₀ i
  have hMle : ∀ f : M →ₐ[K] AlgebraicClosure M, f.fieldRange ≤ A₀ := by
    intro f
    obtain ⟨τ, hτ⟩ := exists_algEquiv_comp_algebraMap_of_normal (K := K) (k := K')
      (Ω := AlgebraicClosure M) (f.comp (IsScalarTower.toAlgHom K K' M))
    obtain ⟨j, hj⟩ := hσ τ
    have hfj : ∀ c : K', f (algebraMap K' M c) =
        algebraMap K' (AlgebraicClosure M) ((σ ^ j) c) := by
      intro c
      have h := hτ c
      rw [hj] at h
      exact h
    have hgjne : g j ≠ 0 := by
      intro h0
      have h := hgp j
      rw [h0, zero_pow hp.ne_zero] at h
      have h1 : (σ ^ j) (a : K') = 0 :=
        (algebraMap K' (AlgebraicClosure M)).injective (by simpa using h.symm)
      exact (Units.ne_zero a) ((σ ^ j).injective (by simpa using h1))
    have hfβ : f βM ∈ (A₀ : Set (AlgebraicClosure M)) := by
      have h1 : (f βM) ^ p = (g j) ^ p := by
        rw [hgp j, ← hfj a, ← map_pow, hβM]
      have h2 : (f βM / g j) ^ p = 1 := by
        rw [div_pow, h1, div_self (pow_ne_zero p hgjne)]
      obtain ⟨c, hc⟩ := pow_eq_one_mem_range (k := K') (K := AlgebraicClosure M) hζ h2
      have h3 : f βM = algebraMap K' (AlgebraicClosure M) c * g j := by
        rw [← hc, div_mul_cancel₀ _ hgjne]
      rw [h3]
      exact mul_mem (hmemK'Ω c) (hmemg j)
    rintro y ⟨x, rfl⟩
    have hx : x ∈ IntermediateField.adjoin K' ({βM} : Set M) := by
      rw [hgenM]; exact IntermediateField.mem_top
    refine IntermediateField.adjoin_induction K' (p := fun z _ => f z ∈ A₀) ?_ ?_ ?_ ?_ ?_ hx
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hfβ
    · intro c
      rw [hfj c]
      exact hmemK'Ω _
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro x _ hx
      rw [map_inv₀]
      exact inv_mem hx
    · intro x y _ _ hx hy
      rw [map_mul]
      exact mul_mem hx hy
  have hA₀N : A₀ = IntermediateField.normalClosure K M (AlgebraicClosure M) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | ⟨i, rfl⟩)
      · rw [hK'Ω] at hx
        obtain ⟨c, rfl⟩ := hx
        exact AlgHom.fieldRange_le_normalClosure (IsScalarTower.toAlgHom K M (AlgebraicClosure M))
          ⟨algebraMap K' M c,
            (IsScalarTower.algebraMap_apply K' M (AlgebraicClosure M) c).symm⟩
      · exact ((σN ^ i) β).2
    · rw [normalClosure_def]
      exact iSup_le fun f => hMle f
  have hmemRange : Set.range g ⊆ (IntermediateField.adjoin K' (Set.range g) :
      Set (AlgebraicClosure M)) := fun x hx => IntermediateField.subset_adjoin K' _ hx
  have hA' : (IntermediateField.adjoin K' (Set.range g) : Set (AlgebraicClosure M)) =
      (A₀ : Set (AlgebraicClosure M)) := by
    let A₀' : IntermediateField K' (AlgebraicClosure M) :=
      { A₀.toSubfield with
        algebraMap_mem' := fun c => hmemA₀ _ (Or.inl (by rw [hK'Ω]; exact Set.mem_range_self c)) }
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have h : IntermediateField.adjoin K' (Set.range g) ≤ A₀' := by
        rw [IntermediateField.adjoin_le_iff]
        rintro y ⟨i, rfl⟩
        exact hmemg i
      exact h hx
    · intro x hx
      have h : A₀ ≤ (IntermediateField.adjoin K' (Set.range g)).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        rintro y (hy | ⟨i, rfl⟩)
        · rw [hK'Ω] at hy
          obtain ⟨c, rfl⟩ := hy
          exact IntermediateField.algebraMap_mem _ c
        · exact IntermediateField.subset_adjoin K' _ (Set.mem_range_self i)
      exact h hx
  have hfinal : IntermediateField.lift (IntermediateField.adjoin K' (Set.range fun i : ℕ =>
      ((σN : NΩ → NΩ)^[i]) β)) = IntermediateField.lift (⊤ : IntermediateField K' NΩ) := by
    rw [IntermediateField.lift_top, IntermediateField.lift_adjoin]
    have hcoe : ∀ i : ℕ, (((σN : NΩ → NΩ)^[i]) β : NΩ) = (σN ^ i) β := by
      intro i
      rw [AlgEquiv.coe_pow]
    have hset : (Subtype.val '' Set.range (fun i : ℕ => ((σN : NΩ → NΩ)^[i]) β)) = Set.range g := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        have h5 : g i = (((σN ^ i) β : NΩ) : AlgebraicClosure M) := rfl
        rw [h5]
        exact congrArg Subtype.val (hcoe i).symm
      · rintro ⟨i, rfl⟩
        refine ⟨((σN : NΩ → NΩ)^[i]) β, ⟨i, rfl⟩, ?_⟩
        have h5 : g i = (((σN ^ i) β : NΩ) : AlgebraicClosure M) := rfl
        rw [h5]
        exact congrArg Subtype.val (hcoe i)
    rw [hset]
    apply SetLike.coe_injective
    show (IntermediateField.adjoin K' (Set.range g) : Set (AlgebraicClosure M)) =
      (NOmega (K := K) (K' := K') (M := M) : Set (AlgebraicClosure M))
    rw [hA', hA₀N]
    rfl
  exact IntermediateField.lift_injective _ hfinal

set_option maxHeartbeats 4000000 in
theorem index_normClassSubgroup_galoisClosure_le_aux
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    [IsGalois K K'] [IsMulCommutative (K' ≃ₐ[K] K')] [IsCyclic (K' ≃ₐ[K] K')]
    [IsGalois K' M] {p : ℕ} [Fact p.Prime] {ζ : K'} (hζ : IsPrimitiveRoot ζ p)
    (hMdeg : Module.finrank K' M = p) :
    (NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M)).index ≤
      p * Module.finrank K K' := by
  classical
  obtain ⟨a, βM, hβM, hgenM⟩ :=
    exists_kummer_root_of_finrank_prime (k := K') (L := M) p hζ inferInstance hMdeg
  have hmemβ : algebraMap M (AlgebraicClosure M) βM ∈
      IntermediateField.normalClosure K M (AlgebraicClosure M) :=
    AlgHom.fieldRange_le_normalClosure
      (IsScalarTower.toAlgHom K M (AlgebraicClosure M)) ⟨βM, rfl⟩
  let β : NΩ := ⟨algebraMap M (AlgebraicClosure M) βM, hmemβ⟩
  have hβp : β ^ p = algebraMap K' NΩ (a : K') := by
    refine Subtype.ext ?_
    show ((algebraMap M (AlgebraicClosure M) βM) ^ p) = _
    rw [show ((algebraMap K' NΩ (a : K') : NΩ) : AlgebraicClosure M)
        = algebraMap K' (AlgebraicClosure M) (a : K') from rfl]
    rw [← map_pow, hβM, IsScalarTower.algebraMap_apply K' M (AlgebraicClosure M)]
  haveI : Finite (K' ≃ₐ[K] K') := by
    have h : Nat.card (K' ≃ₐ[K] K') ≠ 0 := by
      rw [IsGalois.card_aut_eq_finrank]
      exact (Module.finrank_pos (R := K) (M := K')).ne'
    exact (Nat.card_ne_zero.mp h).2
  obtain ⟨σ, hσ⟩ := exists_generator_pow_eq_of_isCyclic (G := K' ≃ₐ[K] K')
  obtain ⟨σN, hσN⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K') NΩ σ
  have hσN' : ∀ x : K', σN (algebraMap K' NΩ x) = algebraMap K' NΩ (σ x) := by
    intro x
    have h := AlgEquiv.restrictNormal_commutes (F := K) (K₁ := NΩ) (K₂ := NΩ) σN K' x
    rw [← h]
    rw [show σN.restrictNormal K' = σ from hσN]
  let orbit : Set NΩ := Set.range fun i : ℕ => ((σN : NΩ → NΩ)^[i]) β
  have hβeq : (β : AlgebraicClosure M) = algebraMap M (AlgebraicClosure M) βM := rfl
  have hgen : IntermediateField.adjoin K' orbit = ⊤ :=
    adjoin_orbit_eq_top (K := K) (K' := K') (M := M) hζ hβM hgenM hβeq hβp σ hσ σN hσN'
  have hpow : ∀ s ∈ orbit, ∃ c : K', s ^ p = algebraMap K' NΩ c := by
    rintro s ⟨i, rfl⟩
    refine ⟨(σ ^ i) (a : K'), ?_⟩
    have key : ((σN ^ i) β) ^ p = algebraMap K' NΩ ((σ ^ i) (a : K')) := by
      have h3 : (σN ^ i) (algebraMap K' NΩ (a : K')) = (σN ^ i) (β ^ p) := by rw [hβp]
      rw [← map_pow, ← h3]
      clear h3
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσN', pow_succ']; rfl
    show ((σN : NΩ → NΩ)^[i]) β ^ p = algebraMap K' NΩ ((σ ^ i) (a : K'))
    rw [show ((σN : NΩ → NΩ)^[i]) β = (σN ^ i) β from congrFun (AlgEquiv.coe_pow σN i).symm β]
    exact key
  haveI : IsMulCommutative (NΩ ≃ₐ[K'] NΩ) :=
    isMulCommutative_of_kummer_generators p hζ orbit hpow hgen
  have hcard : Nat.card (Abelianization (NΩ ≃ₐ[K] NΩ)) ≤ p * Module.finrank K K' :=
    natCard_abelianization_le_of_kummer_orbit (K := K) (K' := K') (N := NΩ) p hζ σ hσ σN hσN'
      a β hβp hgen
  have hidx := NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
    hFC (K := K) (L := NΩ)
  calc (NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M)).index
      = (NK.GlobalCFT.Idele.normClassSubgroup K NΩ).index := rfl
    _ = Nat.card (Abelianization (NΩ ≃ₐ[K] NΩ)) := hidx
    _ ≤ p * Module.finrank K K' := hcard


set_option maxHeartbeats 4000000 in
theorem index_normClassSubgroup_galoisClosure_le
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K : Type} [Field K] [NumberField K]
    {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
    [IsGalois K K'] [IsMulCommutative (K' ≃ₐ[K] K')] [IsCyclic (K' ≃ₐ[K] K')]
    {M : Type} [Field M] [NumberField M] [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    [FiniteDimensional K M] [FiniteDimensional K' M] [IsGalois K' M]
    {p : ℕ} [Fact p.Prime] {ζ : K'} (hζ : IsPrimitiveRoot ζ p)
    (hMdeg : Module.finrank K' M = p) :
    (NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M)).index ≤
      p * Module.finrank K K' :=
  index_normClassSubgroup_galoisClosure_le_aux (K := K) (K' := K') (M := M) hFC hζ hMdeg

end Main

end NK.CFTLib.Existence
