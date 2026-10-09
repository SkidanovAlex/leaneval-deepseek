import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open IntermediateField Polynomial

private lemma eq_X_sq_add_C_mul_X_add_C {F : Type*} [Field F] {p : F[X]}
    (hmonic : p.Monic) (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have h2 : p.coeff 2 = 1 := by rw [← hdeg, coeff_natDegree, hmonic.leadingCoeff]
    simp [h2]
  · have hp : p.coeff (n + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hp]

private lemma quadratic_root_swap_exists {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (Λ : IntermediateField F Ω) (hf : Module.finrank F ↥Λ = 2)
    (σ : Ω ≃ₐ[F] Ω) (hσ : σ ∉ Λ.fixingSubgroup) :
    ∃ y ∈ Λ, y ∉ Set.range (algebraMap F Ω) ∧
      ∃ y' ∈ Λ, y' ≠ y ∧ σ y = y' ∧ σ y' = y ∧
        (Λ = IntermediateField.adjoin F ({y} : Set Ω)) ∧ minpoly F y = minpoly F y' := by
  haveI : FiniteDimensional F ↥Λ := FiniteDimensional.of_finrank_pos (by rw [hf]; norm_num)
  have hnebot : Λ ≠ ⊥ := by
    intro h; rw [h, IntermediateField.finrank_bot] at hf; norm_num at hf
  obtain ⟨y, hy, hyF⟩ : ∃ y ∈ Λ, y ∉ Set.range (algebraMap F Ω) := by
    by_contra h
    push Not at h
    exact hnebot (le_antisymm (fun x hx => by
      rw [IntermediateField.mem_bot]; exact h x hx) bot_le)
  have hgen : Λ = IntermediateField.adjoin F ({y} : Set Ω) := by
    have hle : IntermediateField.adjoin F ({y} : Set Ω) ≤ Λ :=
      IntermediateField.adjoin_le_iff.mpr (by rintro z rfl; exact hy)
    have hdvd : Module.finrank F ↥(IntermediateField.adjoin F ({y} : Set Ω)) ∣ 2 := by
      have h := IntermediateField.finrank_dvd_of_le_right hle
      rwa [hf] at h
    have hne1 : Module.finrank F ↥(IntermediateField.adjoin F ({y} : Set Ω)) ≠ 1 := by
      intro h1
      rw [IntermediateField.finrank_adjoin_simple_eq_one_iff] at h1
      rw [IntermediateField.mem_bot] at h1
      exact hyF h1
    have h2 : Module.finrank F ↥(IntermediateField.adjoin F ({y} : Set Ω)) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    exact (IntermediateField.eq_of_le_of_finrank_eq hle (by rw [h2, hf])).symm
  have hyme : y ∈ Λ := hy
  have hint : IsIntegral F y := by
    have h1 : IsIntegral F (⟨y, hyme⟩ : ↥Λ) := IsIntegral.of_finite F _
    simpa using h1.map (IntermediateField.val Λ)
  have hdeg : (minpoly F y).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, ← hgen]
    exact hf
  obtain ⟨b, c, hquad⟩ : ∃ b c : F, minpoly F y = X ^ 2 + C b * X + C c :=
    ⟨_, _, eq_X_sq_add_C_mul_X_add_C (minpoly.monic hint) hdeg⟩
  set y'' : Ω := -(algebraMap F Ω b) - y with hy''def
  have hy''mem : y'' ∈ Λ := by
    rw [hy''def]
    exact sub_mem (neg_mem ((bot_le : (⊥ : IntermediateField F Ω) ≤ Λ)
      (IntermediateField.mem_bot.mpr ⟨b, rfl⟩))) hy
  have hyroot : y ^ 2 + algebraMap F Ω b * y + algebraMap F Ω c = 0 := by
    have h := minpoly.aeval F y
    rw [hquad] at h
    simpa using h
  have hy''root : y'' ^ 2 + algebraMap F Ω b * y'' + algebraMap F Ω c = 0 := by
    rw [hy''def]; linear_combination hyroot
  have hy'root : (σ y) ^ 2 + algebraMap F Ω b * (σ y) + algebraMap F Ω c = 0 := by
    have h := minpoly.aeval_algHom F (σ.toAlgHom) y
    rw [hquad] at h
    simpa using h
  have hne : σ y ≠ y := by
    intro h
    exact hσ (by rw [hgen]; exact Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple y σ h)
  have hy'eq : σ y = y'' := by
    have h1 : (σ y) ^ 2 + algebraMap F Ω b * (σ y) + algebraMap F Ω c
        = (σ y - y) * (σ y - y'') := by
      rw [hy''def]; linear_combination hyroot
    have hfac : (σ y - y) * (σ y - y'') = 0 := by rw [← h1, hy'root]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact sub_eq_zero.mp h
  have hσy'' : σ y'' = y := by
    rw [hy''def, map_sub, map_neg, σ.commutes, hy'eq, hy''def]; ring
  exact ⟨y, hy, hyF, y'', hy''mem, (fun h => hne (hy'eq.trans h)), hy'eq, hσy'',
    hgen, by have h := minpoly.algEquiv_eq σ y; rw [hy'eq] at h; exact h.symm⟩

private lemma exists_restrictAut {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K : IntermediateField F Ω) [FiniteDimensional F ↥K] (σ : Ω ≃ₐ[F] Ω)
    (hK : ∀ x : Ω, σ x ∈ K ↔ x ∈ K) :
    ∃ σK : ↥K ≃ₐ[F] ↥K, ∀ x : ↥K, (σK x : Ω) = σ x := by
  have hf_mem : ∀ x : ↥K, σ x.1 ∈ K := fun x => (hK x.1).mpr x.2
  let f : ↥K →ₐ[F] ↥K :=
    ((σ.toAlgHom).comp (IntermediateField.val K)).codRestrict K.toSubalgebra hf_mem
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (σ.injective (congrArg Subtype.val hab))
  refine ⟨AlgEquiv.ofBijective f ⟨hinj, ?_⟩, fun x => rfl⟩
  exact (LinearMap.injective_iff_surjective (f := f.toLinearMap)).mp hinj

private lemma isIntegral_of_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (Λ : IntermediateField F Ω) [FiniteDimensional F ↥Λ] {y : Ω} (hy : y ∈ Λ) :
    IsIntegral F y := by
  have h1 : IsIntegral F (⟨y, hy⟩ : ↥Λ) := IsIntegral.of_finite F _
  simpa using h1.map (IntermediateField.val Λ)

private lemma isGalois_of_restrict {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K : IntermediateField F Ω) [FiniteDimensional F ↥K] (hf : Module.finrank F ↥K = 2)
    (σ : Ω ≃ₐ[F] Ω) (hK : ∀ x : Ω, σ x ∈ K ↔ x ∈ K)
    (hne : ∃ x : ↥K, σ x.1 ≠ x.1) :
    IsGalois F K := by
  obtain ⟨σK, hσK⟩ := exists_restrictAut K σ hK
  have hsne : σK ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by rw [← hσK x]; exact congrArg Subtype.val (h ▸ rfl))
  have hcardle : Nat.card (↥K ≃ₐ[F] ↥K) ≤ 2 := by
    have h := AlgEquiv.card_le (F := F) (K := ↥K)
    rw [Nat.card_eq_fintype_card]
    simpa [hf] using h
  have hcardge : 2 ≤ Nat.card (↥K ≃ₐ[F] ↥K) := by
    haveI : Nontrivial (↥K ≃ₐ[F] ↥K) := ⟨⟨σK, 1, hsne⟩⟩
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_of_lt Fintype.one_lt_card
  exact IsGalois.of_card_aut_eq_finrank F ↥K (by rw [le_antisymm hcardle hcardge, hf])

private lemma adjoin_conj_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (Λ : IntermediateField F Ω) [FiniteDimensional F ↥Λ] (hf : Module.finrank F ↥Λ = 2)
    {y y' : Ω} (hy : Λ = IntermediateField.adjoin F ({y} : Set Ω)) (hy' : y' ∈ Λ)
    (hmin : minpoly F y = minpoly F y') (hne : y' ≠ y) :
    IntermediateField.adjoin F ({y'} : Set Ω) = Λ := by
  have hyme : y ∈ Λ := hy.symm ▸ IntermediateField.mem_adjoin_simple_self F y
  have hint : IsIntegral F y := isIntegral_of_mem Λ hyme
  have hdeg : (minpoly F y).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, ← hy]; exact hf
  have hint' : IsIntegral F y' :=
    ⟨minpoly F y, minpoly.monic hint, hmin.symm ▸ minpoly.aeval F y'⟩
  have hle : IntermediateField.adjoin F ({y'} : Set Ω) ≤ Λ :=
    IntermediateField.adjoin_le_iff.mpr (by rintro z rfl; exact hy')
  have hfin : Module.finrank F ↥(IntermediateField.adjoin F ({y'} : Set Ω)) = 2 := by
    rw [IntermediateField.adjoin.finrank hint', ← hmin, hdeg]
  exact IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hfin, hf])

private lemma map_eq_self {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (σ : Ω ≃ₐ[F] Ω) (Λ : IntermediateField F Ω) {y y' : Ω}
    (hy : Λ = IntermediateField.adjoin F ({y} : Set Ω))
    (hy' : IntermediateField.adjoin F ({y'} : Set Ω) = Λ) (hσ : σ y = y') :
    Λ.map σ.toAlgHom = Λ := by
  rw [hy, IntermediateField.adjoin_map, Set.image_singleton, AlgEquiv.coe_toAlgHom, hσ, hy']
  exact hy

private lemma finrank_sup_eq_four {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {Λ₁ Λ₂ : IntermediateField F Ω}
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2) (h₁₂ : Λ₁ ≠ Λ₂) :
    Module.finrank F ↥(Λ₁ ⊔ Λ₂) = 4 := by
  haveI : FiniteDimensional F ↥Λ₁ := FiniteDimensional.of_finrank_pos (by rw [h₁]; norm_num)
  haveI : FiniteDimensional F ↥Λ₂ := FiniteDimensional.of_finrank_pos (by rw [h₂]; norm_num)
  have hle : Module.finrank F ↥(Λ₁ ⊔ Λ₂) ≤ 4 := by
    have h := IntermediateField.finrank_sup_le Λ₁ Λ₂
    rw [h₁, h₂] at h; simpa using h
  have hdvd : 2 ∣ Module.finrank F ↥(Λ₁ ⊔ Λ₂) := by
    rw [← h₁]; exact IntermediateField.finrank_dvd_of_le_right le_sup_left
  have hge : 2 ≤ Module.finrank F ↥(Λ₁ ⊔ Λ₂) := by
    rw [← h₁]; exact IntermediateField.finrank_le_of_le_right le_sup_left
  have hne : Module.finrank F ↥(Λ₁ ⊔ Λ₂) ≠ 2 := by
    intro h
    haveI : FiniteDimensional F ↥(Λ₁ ⊔ Λ₂) := FiniteDimensional.of_finrank_pos (by omega)
    have heq : Λ₁ ⊔ Λ₂ = Λ₁ :=
      (IntermediateField.eq_of_le_of_finrank_eq le_sup_left (by rw [h, h₁])).symm
    have h21 : Λ₂ ≤ Λ₁ := by rw [← heq]; exact le_sup_right
    exact h₁₂ (IntermediateField.eq_of_le_of_finrank_eq (K := F) (L := Ω) (F := Λ₂) (E := Λ₁)
      h21 (by rw [h₂, h₁])).symm
  obtain ⟨k, hk⟩ := hdvd
  omega

private lemma sup_eq_of_quadratic {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {Λ₁ Λ₂ Λ₃ : IntermediateField F Ω}
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2)
    (h₃ : Module.finrank F ↥Λ₃ = 2) (h₁₂ : Λ₁ ≠ Λ₂)
    (hle : Λ₃ ≤ Λ₁ ⊔ Λ₂) (hne₁ : Λ₃ ≠ Λ₁) :
    Λ₁ ⊔ Λ₃ = Λ₁ ⊔ Λ₂ := by
  have h4 : Module.finrank F ↥(Λ₁ ⊔ Λ₃) = 4 := finrank_sup_eq_four h₁ h₃ (Ne.symm hne₁)
  have h4' : Module.finrank F ↥(Λ₁ ⊔ Λ₂) = 4 := finrank_sup_eq_four h₁ h₂ h₁₂
  haveI : FiniteDimensional F ↥(Λ₁ ⊔ Λ₂) := FiniteDimensional.of_finrank_pos (by rw [h4']; norm_num)
  exact IntermediateField.eq_of_le_of_finrank_eq (sup_le le_sup_left hle) (by rw [h4, h4'])

private lemma three_two_subgroups {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G ≤ 4)
    (H₁ H₂ H₃ : Subgroup G) (h1 : Nat.card H₁ = 2) (h2 : Nat.card H₂ = 2) (h3 : Nat.card H₃ = 2)
    (h12 : H₁ ≠ H₂) (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃)
    (σ : G) (hσ1 : σ ∉ H₁) (hσ2 : σ ∉ H₂) : σ ∈ H₃ := by
  classical
  have key : ∀ (H : Subgroup G), Nat.card H = 2 → ∃ a, a ∈ H ∧ a ≠ 1 := by
    intro H hH
    have hc : Fintype.card ↥H = 2 := by rw [← Nat.card_eq_fintype_card, hH]
    obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥H) (by rw [hc]; norm_num) (1 : ↥H)
    exact ⟨x, x.2, fun hh => hx (Subtype.ext hh)⟩
  obtain ⟨a, haH, ha1⟩ := key H₁ h1
  obtain ⟨b, hbH, hb1⟩ := key H₂ h2
  obtain ⟨c, hcH, hc1⟩ := key H₃ h3
  have zp : ∀ (H : Subgroup G) (hH : Nat.card H = 2) (a : G) (ha : a ∈ H) (ha1 : a ≠ 1),
      H = Subgroup.zpowers a := by
    intro H hH a ha ha1
    have hle : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr ha
    have hup : Nat.card ↥(Subgroup.zpowers a) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [hH] at hup
    have hne : Nat.card ↥(Subgroup.zpowers a) ≠ 1 := by
      intro hone
      have hbot : Subgroup.zpowers a = ⊥ := by
        apply (Subgroup.eq_bot_iff_forall _).mpr
        intro x hx
        have hs : (⟨x, hx⟩ : ↥(Subgroup.zpowers a)) = 1 := by
          haveI := (Nat.card_eq_one_iff_unique.mp hone).1
          exact Subsingleton.elim _ _
        exact Subtype.ext_iff.mp hs
      rw [Subgroup.zpowers_eq_bot] at hbot
      exact ha1 hbot
    haveI : Nonempty ↥(Subgroup.zpowers a) := ⟨⟨1, Subgroup.one_mem _⟩⟩
    have hpos : 1 ≤ Nat.card ↥(Subgroup.zpowers a) := Nat.card_pos
    have h2 : Nat.card ↥(Subgroup.zpowers a) = 2 := by omega
    have hbij : Function.Bijective (Subgroup.inclusion hle : ↥(Subgroup.zpowers a) → ↥H) := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨Subgroup.inclusion_injective hle, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h2, hH]⟩
    refine le_antisymm ?_ hle
    intro x hx
    obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    have hy2 : x = (y : G) := (Subtype.ext_iff.mp hy).symm
    rw [hy2]; exact y.2
  have hab : a ≠ b := fun hab => h12 (by rw [zp H₁ h1 a haH ha1, zp H₂ h2 a (hab.symm ▸ hbH) ha1])
  have hac : a ≠ c := fun hac => h13 (by rw [zp H₁ h1 a haH ha1, zp H₃ h3 a (hac.symm ▸ hcH) ha1])
  have hbc : b ≠ c := fun hbc => h23 (by rw [zp H₂ h2 b hbH hb1, zp H₃ h3 b (hbc.symm ▸ hcH) hb1])
  have hcard4 : ({1, a, b, c} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hc1⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hab, hac⟩),
        Set.ncard_insert_of_notMem (by simpa using hbc), Set.ncard_singleton]
  have h4 : Fintype.card G = 4 := by
    have h := Set.ncard_le_card ({1, a, b, c} : Set G)
    rw [hcard4, Nat.card_eq_fintype_card] at h
    omega
  have hGeq : ({1, a, b, c} : Set G) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (ht := Set.finite_univ)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, h4, hcard4]
  have hσmem : σ ∈ ({1, a, b, c} : Set G) := by rw [hGeq]; exact Set.mem_univ σ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσmem
  rcases hσmem with h | h | h | h
  · exact absurd (h ▸ one_mem H₁) hσ1
  · exact absurd (h ▸ haH) hσ1
  · exact absurd (h ▸ hbH) hσ2
  · rw [h]; exact hcH

private lemma mem_restrict_fixing_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {L : IntermediateField F Ω} {K : IntermediateField F Ω} (h : K ≤ L)
    (σ : Ω ≃ₐ[F] Ω) (σL : ↥L ≃ₐ[F] ↥L) (hσL : ∀ x : ↥L, (σL x : Ω) = σ x) :
    σL ∈ (K.restrict h).fixingSubgroup ↔ σ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hf x hx
    have h2 := hf (⟨x, h hx⟩ : ↥L) ((IntermediateField.mem_restrict h (⟨x, h hx⟩ : ↥L)).mpr hx)
    exact (hσL ⟨x, h hx⟩).symm.trans (Subtype.ext_iff.mp h2)
  · intro hf x hx
    apply Subtype.ext
    have h2 : (x : Ω) ∈ K := (IntermediateField.mem_restrict h x).mp hx
    exact (hσL x).trans (hf (x : Ω) h2)

private lemma restrict_inj_on {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {K₁ K₂ L : IntermediateField F Ω} (h₁ : K₁ ≤ L) (h₂ : K₂ ≤ L)
    (e : K₁.restrict h₁ = K₂.restrict h₂) : K₁ = K₂ := by
  have l₁ := IntermediateField.lift_restrict (F := K₁) h₁
  have l₂ := IntermediateField.lift_restrict (F := K₂) h₂
  rw [e] at l₁
  exact l₁.symm.trans l₂

set_option synthInstance.maxHeartbeats 400000 in
private lemma main_bothfalse {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (Λ₁ Λ₂ Λ₃ : IntermediateField F Ω)
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2)
    (h₃ : Module.finrank F ↥Λ₃ = 2) (h₁₂ : Λ₁ ≠ Λ₂)
    (hle : Λ₃ ≤ Λ₁ ⊔ Λ₂) (hne₁ : Λ₃ ≠ Λ₁) (hne₂ : Λ₃ ≠ Λ₂)
    (σ : Ω ≃ₐ[F] Ω) (hσ1 : σ ∉ Λ₁.fixingSubgroup) (hσ2 : σ ∉ Λ₂.fixingSubgroup) :
    σ ∈ Λ₃.fixingSubgroup := by
  haveI : FiniteDimensional F ↥Λ₁ := FiniteDimensional.of_finrank_pos (by rw [h₁]; norm_num)
  haveI : FiniteDimensional F ↥Λ₂ := FiniteDimensional.of_finrank_pos (by rw [h₂]; norm_num)
  obtain ⟨y₁, hy₁mem, _, y₁', hy₁'mem, hy₁'ne, hσy₁, hσy₁', hy₁gen, hmin₁⟩ :=
    quadratic_root_swap_exists Λ₁ h₁ σ hσ1
  obtain ⟨y₂, hy₂mem, _, y₂', hy₂'mem, hy₂'ne, hσy₂, hσy₂', hy₂gen, hmin₂⟩ :=
    quadratic_root_swap_exists Λ₂ h₂ σ hσ2
  have hΛ₁' := adjoin_conj_eq Λ₁ h₁ hy₁gen hy₁'mem hmin₁ hy₁'ne
  have hΛ₂' := adjoin_conj_eq Λ₂ h₂ hy₂gen hy₂'mem hmin₂ hy₂'ne
  have hmap₁ := map_eq_self σ Λ₁ hy₁gen hΛ₁' hσy₁
  have hmap₂ := map_eq_self σ Λ₂ hy₂gen hΛ₂' hσy₂
  have hmapL : (Λ₁ ⊔ Λ₂).map σ.toAlgHom = Λ₁ ⊔ Λ₂ := by
    rw [IntermediateField.map_sup, hmap₁, hmap₂]
  have hKL : ∀ x : Ω, σ x ∈ (Λ₁ ⊔ Λ₂) ↔ x ∈ (Λ₁ ⊔ Λ₂) := by
    intro x
    constructor
    · intro h
      rw [← hmapL] at h
      rw [IntermediateField.mem_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      rw [← σ.injective hyx]; exact hy
    · intro h
      rw [← hmapL]
      exact (IntermediateField.mem_map _).mpr ⟨x, h, rfl⟩
  haveI : FiniteDimensional F ↥(Λ₁ ⊔ Λ₂) := FiniteDimensional.of_finrank_pos
    (by rw [finrank_sup_eq_four h₁ h₂ h₁₂]; norm_num)
  have hK₁ : ∀ x : Ω, σ x ∈ Λ₁ ↔ x ∈ Λ₁ := by
    intro x
    constructor
    · intro h
      rw [← hmap₁] at h
      rw [IntermediateField.mem_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      rw [← σ.injective hyx]; exact hy
    · intro h
      rw [← hmap₁]
      exact (IntermediateField.mem_map _).mpr ⟨x, h, rfl⟩
  have hK₂ : ∀ x : Ω, σ x ∈ Λ₂ ↔ x ∈ Λ₂ := by
    intro x
    constructor
    · intro h
      rw [← hmap₂] at h
      rw [IntermediateField.mem_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      rw [← σ.injective hyx]; exact hy
    · intro h
      rw [← hmap₂]
      exact (IntermediateField.mem_map _).mpr ⟨x, h, rfl⟩
  haveI : IsGalois F ↥Λ₁ := isGalois_of_restrict Λ₁ h₁ σ hK₁
    ⟨⟨y₁, hy₁mem⟩, fun h => hy₁'ne (hσy₁.symm.trans h)⟩
  haveI : IsGalois F ↥Λ₂ := isGalois_of_restrict Λ₂ h₂ σ hK₂
    ⟨⟨y₂, hy₂mem⟩, fun h => hy₂'ne (hσy₂.symm.trans h)⟩
  haveI : IsGalois F ↥(Λ₁ ⊔ Λ₂) := inferInstance
  obtain ⟨σL, hσL⟩ := exists_restrictAut (Λ₁ ⊔ Λ₂) σ hKL
  have hL : Module.finrank F ↥(Λ₁ ⊔ Λ₂) = 4 := finrank_sup_eq_four h₁ h₂ h₁₂
  have hGle : Fintype.card (↥(Λ₁ ⊔ Λ₂) ≃ₐ[F] ↥(Λ₁ ⊔ Λ₂)) ≤ 4 := by
    have h := AlgEquiv.card_le (F := F) (K := ↥(Λ₁ ⊔ Λ₂))
    rw [hL] at h; exact h
  have hAcard : Nat.card ↥(Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂))]
    have hfr : Module.finrank F ↥(Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)) = 2 := by
      rw [← h₁]
      exact (IntermediateField.restrictAlgEquiv
        (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)).toLinearEquiv.finrank_eq.symm
    have h := Module.finrank_mul_finrank F
      ↥(Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)) ↥(Λ₁ ⊔ Λ₂)
    rw [hL, hfr] at h
    omega
  have hBcard : Nat.card ↥(Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂))]
    have hfr : Module.finrank F ↥(Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)) = 2 := by
      rw [← h₂]
      exact (IntermediateField.restrictAlgEquiv
        (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)).toLinearEquiv.finrank_eq.symm
    have h := Module.finrank_mul_finrank F
      ↥(Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)) ↥(Λ₁ ⊔ Λ₂)
    rw [hL, hfr] at h
    omega
  have hCcard : Nat.card ↥(Λ₃.restrict hle).fixingSubgroup = 2 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank (Λ₃.restrict hle)]
    have hfr : Module.finrank F ↥(Λ₃.restrict hle) = 2 := by
      rw [← h₃]
      exact (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finrank_eq.symm
    have h := Module.finrank_mul_finrank F ↥(Λ₃.restrict hle) ↥(Λ₁ ⊔ Λ₂)
    rw [hL, hfr] at h
    omega
  have hmemA := mem_restrict_fixing_iff (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂) σ σL hσL
  have hmemB := mem_restrict_fixing_iff (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂) σ σL hσL
  have hmemC := mem_restrict_fixing_iff hle σ σL hσL
  have hAB : (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup ≠
      (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup := by
    intro h
    apply h₁₂
    refine restrict_inj_on (K₁ := Λ₁) (K₂ := Λ₂) (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)
      (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂) ?_
    have a := IsGalois.fixedField_fixingSubgroup (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂))
    have b := IsGalois.fixedField_fixingSubgroup (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂))
    rw [h] at a
    exact a.symm.trans b
  have hAC : (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup ≠
      (Λ₃.restrict hle).fixingSubgroup := by
    intro h
    apply hne₁
    refine restrict_inj_on (K₁ := Λ₃) (K₂ := Λ₁) hle (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂) ?_
    have a := IsGalois.fixedField_fixingSubgroup (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂))
    have b := IsGalois.fixedField_fixingSubgroup (Λ₃.restrict hle)
    rw [h] at a
    exact (a.symm.trans b).symm
  have hBC : (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup ≠
      (Λ₃.restrict hle).fixingSubgroup := by
    intro h
    apply hne₂
    refine restrict_inj_on (K₁ := Λ₃) (K₂ := Λ₂) hle (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂) ?_
    have a := IsGalois.fixedField_fixingSubgroup (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂))
    have b := IsGalois.fixedField_fixingSubgroup (Λ₃.restrict hle)
    rw [h] at a
    exact (a.symm.trans b).symm
  have hσLmem := three_two_subgroups hGle
    (Λ₁.restrict (le_sup_left : Λ₁ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup
    (Λ₂.restrict (le_sup_right : Λ₂ ≤ Λ₁ ⊔ Λ₂)).fixingSubgroup
    (Λ₃.restrict hle).fixingSubgroup
    hAcard hBcard hCcard hAB hAC hBC σL (fun h => hσ1 (hmemA.mp h)) (fun h => hσ2 (hmemB.mp h))
  exact hmemC.mp hσLmem

/-- The main theorem. -/
theorem mem_fixingSubgroup_iff_iff_of_biquadratic {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (Λ₁ Λ₂ Λ₃ : IntermediateField F Ω)
    (h₁ : Module.finrank F ↥Λ₁ = 2) (h₂ : Module.finrank F ↥Λ₂ = 2)
    (h₃ : Module.finrank F ↥Λ₃ = 2) (h₁₂ : Λ₁ ≠ Λ₂)
    (hle : Λ₃ ≤ Λ₁ ⊔ Λ₂) (hne₁ : Λ₃ ≠ Λ₁) (hne₂ : Λ₃ ≠ Λ₂)
    (σ : Ω ≃ₐ[F] Ω) :
    (σ ∈ Λ₃.fixingSubgroup) ↔ ((σ ∈ Λ₁.fixingSubgroup) ↔ (σ ∈ Λ₂.fixingSubgroup)) := by
  constructor
  · intro hσ3
    constructor
    · intro hσ1
      have : σ ∈ (Λ₁ ⊔ Λ₃).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]; exact ⟨hσ1, hσ3⟩
      rw [sup_eq_of_quadratic h₁ h₂ h₃ h₁₂ hle hne₁, IntermediateField.fixingSubgroup_sup] at this
      exact this.2
    · intro hσ2
      have hsup : Λ₂ ⊔ Λ₃ = Λ₂ ⊔ Λ₁ :=
        sup_eq_of_quadratic h₂ h₁ h₃ h₁₂.symm (by rwa [sup_comm]) hne₂
      have : σ ∈ (Λ₂ ⊔ Λ₃).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]; exact ⟨hσ2, hσ3⟩
      rw [hsup, sup_comm Λ₂ Λ₁, IntermediateField.fixingSubgroup_sup] at this
      exact this.1
  · intro h
    by_cases hσ1 : σ ∈ Λ₁.fixingSubgroup
    · have hσ2 : σ ∈ Λ₂.fixingSubgroup := h.mp hσ1
      have : σ ∈ (Λ₁ ⊔ Λ₂).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]; exact ⟨hσ1, hσ2⟩
      exact IntermediateField.fixingSubgroup_le hle this
    · have hσ2 : σ ∉ Λ₂.fixingSubgroup := fun h2 => hσ1 (h.mpr h2)
      exact main_bothfalse Λ₁ Λ₂ Λ₃ h₁ h₂ h₃ h₁₂ hle hne₁ hne₂ σ hσ1 hσ2


end Work.SSGRoute.ZDataTwo
