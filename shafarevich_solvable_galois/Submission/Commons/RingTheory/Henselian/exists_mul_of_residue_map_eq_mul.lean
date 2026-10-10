import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Submission.Commons.RingTheory.Henselian.exists_monic_mul_of_map_eq_mul

set_option maxHeartbeats 3200000

open Polynomial IsLocalRing


lemma Polynomial.eq_X_pow_add_sum_of_monic {R : Type*} [Semiring R] (p : Polynomial R)
    (hp : p.Monic) :
    p = Polynomial.X ^ p.natDegree +
      ∑ i : Fin p.natDegree, Polynomial.C (p.coeff i) * Polynomial.X ^ (i : ℕ) := by
  ext k
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rcases lt_trichotomy k p.natDegree with h | h | h
  · rw [if_neg (by omega), zero_add]
    rw [Finset.sum_eq_single ⟨k, h⟩]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro hkb
      exact hb (Fin.ext hkb.symm)
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · subst h
    rw [if_pos rfl, Finset.sum_eq_zero, add_zero]
    · exact hp
    · intro b _
      rw [if_neg]
      intro hb
      have := b.isLt
      omega
  · rw [if_neg (by omega), zero_add, Finset.sum_eq_zero]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt h
    · intro b _
      rw [if_neg]
      intro hb
      have := b.isLt
      omega

lemma Polynomial.eq_sum_of_natDegree_le {R : Type*} [Semiring R] (p : Polynomial R) {m : ℕ}
    (hm : p.natDegree ≤ m) :
    p = ∑ j : Fin (m + 1), Polynomial.C (p.coeff j) * Polynomial.X ^ (j : ℕ) := by
  ext k
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ≤ m
  · rw [Finset.sum_eq_single ⟨k, Nat.lt_succ_of_le hk⟩]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro hkb
      exact hb (Fin.ext hkb.symm)
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hm (not_le.mp hk))]
    intro b _
    rw [if_neg]
    intro hb
    have := b.isLt
    omega


namespace Commons.RingTheory.Henselian


open Polynomial IsLocalRing

/-- Retraction lemma for étale algebras over a Henselian local ring, given a surjective
`A`-algebra map to the residue field. -/
theorem exists_algHom_retract_of_isEtale_of_surjective
    {A B : Type*} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] (hB : Algebra.Etale A B)
    (φ : B →ₐ[A] (IsLocalRing.maximalIdeal A).ResidueField) (hφ : Function.Surjective φ) :
    ∃ τ : B →ₐ[A] A, ∀ b : B,
      algebraMap A (IsLocalRing.maximalIdeal A).ResidueField (τ b) = φ b := by
  let Q := RingHom.ker φ.toRingHom
  haveI hQp : Q.IsPrime := RingHom.ker_isPrime _
  haveI hQover : Q.LiesOver (IsLocalRing.maximalIdeal A) := ⟨by
    rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap,
      Ideal.ker_algebraMap_residueField]⟩
  haveI : Algebra.FinitePresentation A B := hB.finitePresentation
  haveI hEt : Algebra.IsEtaleAt A Q := inferInstance
  obtain ⟨g₀, hg₀Q, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away g₀
  haveI : Algebra.IsStandardEtale A S := hSE
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := A) (S := S)
  let k := (IsLocalRing.maximalIdeal A).ResidueField
  have hφunit : IsUnit (φ g₀) := by
    refine isUnit_iff_ne_zero.mpr fun h => hg₀Q ?_
    show g₀ ∈ RingHom.ker φ.toRingHom
    exact h
  let φ₁ : S →ₐ[A] k := IsLocalization.Away.liftAlgHom g₀ (f := φ) hφunit
  have hφ₁ : ∀ b : B, φ₁ (algebraMap B S b) = φ b := by
    intro b
    have hh := IsLocalization.Away.lift_comp (R := B) (S := S) (P := k) g₀ hφunit
      (g := φ.toRingHom)
    have h2 := RingHom.congr_fun hh b
    simpa [φ₁, IsLocalization.Away.coe_liftAlgHom] using h2
  let φ₂ : P.Ring →ₐ[A] k := φ₁.comp P.equivRing.symm.toAlgHom
  let a₀ : k := φ₂ P.X
  have ha₀ : P.P.HasMap a₀ := by
    have := P.hasMap.map φ₁
    simpa [a₀, φ₂, StandardEtalePresentation.equivRing_symm_X] using this
  have hderiv : P.P.f.derivative.eval₂ (algebraMap A k) a₀ ≠ 0 := by
    have h := ha₀.isUnit_derivative_f
    rw [isUnit_iff_ne_zero] at h
    simpa [Polynomial.aeval_def] using h
  obtain ⟨α, hαroot, hαres⟩ :=
    Commons.RingTheory.Henselian.exists_root_of_eval₂_of_surjective (algebraMap A k)
      (Ideal.algebraMap_residueField_surjective _) P.P.monic_f ha₀.1 hderiv
  have hα : P.P.HasMap α := by
    refine ⟨?_, ?_⟩
    · simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hαroot
    · have hg : IsUnit (P.P.g.eval α) := by
        rw [← notMem_maximalIdeal]
        intro hmem
        have h0 : algebraMap A k (P.P.g.eval α) = 0 :=
          Ideal.algebraMap_residueField_eq_zero.mpr hmem
        have hthis : (aeval a₀) P.P.g = 0 := by
          rw [Polynomial.aeval_def, ← hαres, Polynomial.eval₂_at_apply]
          exact h0
        exact (isUnit_iff_ne_zero.mp ha₀.2) hthis
      simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hg
  let τS : S →ₐ[A] A := (P.P.lift α hα).comp P.equivRing.toAlgHom
  refine ⟨τS.comp (IsScalarTower.toAlgHom A B S), ?_⟩
  have hkey : ∀ s : S, algebraMap A k (τS s) = φ₁ s := by
    have hcomp : (Algebra.ofId A k).comp τS = φ₁ := by
      apply P.hom_ext
      show algebraMap A k (τS P.x) = φ₁ P.x
      rw [show τS P.x = α by
        simp [τS, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X],
        show φ₁ P.x = a₀ by
          simp [a₀, φ₂, StandardEtalePresentation.equivRing_symm_X]]
      exact hαres
    intro s
    exact AlgHom.congr_fun hcomp s
  intro b
  show algebraMap A k (τS ((IsScalarTower.toAlgHom A B S) b)) = φ b
  rw [IsScalarTower.toAlgHom_apply, hkey, hφ₁]


theorem exists_mul_of_residue_map_eq_mul {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {f : Polynomial A} {g h : Polynomial (IsLocalRing.ResidueField A)} (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime g h) (hfac : Polynomial.map (IsLocalRing.residue A) f = g * h) :
    ∃ f₁ f₂ : Polynomial A, f₁.Monic ∧ Polynomial.map (IsLocalRing.residue A) f₁ = g
      ∧ Polynomial.map (IsLocalRing.residue A) f₂ = h ∧ f = f₁ * f₂ := by
  set 𝔪 := IsLocalRing.maximalIdeal A with h𝔪
  haveI : 𝔪.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  haveI : 𝔪.IsPrime := inferInstance
  set 𝔨 := 𝔪.ResidueField with h𝔨
  let e : IsLocalRing.ResidueField A ≃+* 𝔨 :=
    RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField A) 𝔨)
      (Ideal.bijective_algebraMap_quotient_residueField 𝔪)
  have he_apply : ∀ x : IsLocalRing.ResidueField A,
      e x = algebraMap (IsLocalRing.ResidueField A) 𝔨 x :=
    fun x => RingEquiv.ofBijective_apply _ _ x
  have hmap_eq : (algebraMap A 𝔨 : A →+* 𝔨) = e.toRingHom.comp (IsLocalRing.residue A) := by
    ext x
    show (algebraMap A 𝔨) x = e ((IsLocalRing.residue A) x)
    rw [he_apply, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) 𝔨]
  have hfac' : Polynomial.map (algebraMap A 𝔨) f =
      g.map e.toRingHom * h.map e.toRingHom := by
    rw [hmap_eq, ← Polynomial.map_map, hfac, Polynomial.map_mul]
  set G : Polynomial 𝔨 := g.map e.toRingHom with hG
  set H : Polynomial 𝔨 := h.map e.toRingHom with hH
  have hGmonic : G.Monic := hg.map e.toRingHom
  have hHmonic : H.Monic := hh.map e.toRingHom
  have hcop' : IsCoprime G H := IsCoprime.map hcop (Polynomial.mapRingHom e.toRingHom)
  set n := G.natDegree with hn
  set N := f.natDegree with hN
  set m := N - n with hm
  have hdeg : (Polynomial.map (algebraMap A 𝔨) f).natDegree = n + H.natDegree := by
    rw [hfac', Polynomial.natDegree_mul hGmonic.ne_zero hHmonic.ne_zero]
  have hnle : n ≤ N := by
    have h2 : (Polynomial.map (algebraMap A 𝔨) f).natDegree ≤ N := Polynomial.natDegree_map_le
    omega
  have hnm : n + m = N := by rw [hm]; exact Nat.add_sub_cancel' hnle
  have hHm : H.natDegree ≤ m := by
    have h2 : (Polynomial.map (algebraMap A 𝔨) f).natDegree ≤ N := Polynomial.natDegree_map_le
    omega
  let ι := Fin n ⊕ Fin (m + 1)
  let R := MvPolynomial ι A
  let A₁ : Polynomial R := Polynomial.X ^ n + ∑ i : Fin n,
      Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
  let A₂ : Polynomial R := ∑ j : Fin (m + 1),
      Polynomial.C (MvPolynomial.X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
  let kk : ι → ℕ := fun k => match k with
    | Sum.inl i => (i : ℕ) | Sum.inr j => n + (j : ℕ)
  have hcoeffA₁ : ∀ d : ℕ, A₁.coeff d =
      (if h : d < n then MvPolynomial.X (Sum.inl ⟨d, h⟩) else if d = n then 1 else 0) := by
    intro d
    simp only [A₁, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
    by_cases h : d < n
    · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨d, h⟩),
        Fin.ext_iff, @eq_comm _ d, h, h.ne']
    · rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; lia), add_zero, dif_neg h]
  have hcoeffA₂ : ∀ d : ℕ, A₂.coeff d =
      (if h : d < m + 1 then MvPolynomial.X (Sum.inr ⟨d, h⟩) else 0) := by
    intro d
    simp only [A₂, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    by_cases h : d < m + 1
    · simp +contextual [Finset.sum_eq_single (ι := Fin (m+1)) (a := ⟨d, h⟩),
        Fin.ext_iff, @eq_comm _ d, h, h.ne']
    · rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; omega), dif_neg h]
  let Ψ : ι → 𝔨 := fun k => match k with
    | Sum.inl i => G.coeff (i : ℕ) | Sum.inr j => H.coeff (j : ℕ)
  let Φ₀ : R →ₐ[A] 𝔨 := MvPolynomial.aeval Ψ
  have hΦ₀X : ∀ k : ι, Φ₀ (MvPolynomial.X k) = Ψ k := fun k => MvPolynomial.aeval_X Ψ k
  have hmapA₁ : A₁.map Φ₀.toRingHom = G := by
    have h1 : A₁.map Φ₀.toRingHom = Polynomial.X ^ n +
        ∑ i : Fin n, Polynomial.C (G.coeff i) * Polynomial.X ^ (i : ℕ) := by
      show (Polynomial.X ^ n + ∑ i : Fin n,
          Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)).map Φ₀.toRingHom = _
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
        congr 1
        simpa using hΦ₀X (Sum.inl i)
    rw [h1]
    exact (Polynomial.eq_X_pow_add_sum_of_monic G hGmonic).symm
  have hmapA₂ : A₂.map Φ₀.toRingHom = H := by
    have h1 : A₂.map Φ₀.toRingHom =
        ∑ j : Fin (m+1), Polynomial.C (H.coeff j) * Polynomial.X ^ (j : ℕ) := by
      show (∑ j : Fin (m+1),
          Polynomial.C (MvPolynomial.X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)).map Φ₀.toRingHom = _
      rw [Polynomial.map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      congr 1
      simpa using hΦ₀X (Sum.inr j)
    rw [h1]
    exact (Polynomial.eq_sum_of_natDegree_le H hHm).symm
  have hrel : ∀ v : ι, Φ₀ ((A₁ * A₂).coeff (kk v)) = algebraMap A 𝔨 (f.coeff (kk v)) := by
    intro v
    rw [show Φ₀ ((A₁ * A₂).coeff (kk v)) = (Polynomial.map Φ₀.toRingHom (A₁ * A₂)).coeff (kk v) from
      (Polynomial.coeff_map Φ₀.toRingHom (kk v)).symm]
    rw [Polynomial.map_mul, hmapA₁, hmapA₂]
    rw [← hfac']
    rw [Polynomial.coeff_map]
  let rel : ι → R := fun v => (A₁ * A₂).coeff (kk v) - MvPolynomial.C (f.coeff (kk v))
  have hΦrel : ∀ v : ι, Φ₀ (rel v) = 0 := by
    intro v
    have hΦ₀C : ∀ a : A, Φ₀ (MvPolynomial.C a) = algebraMap A 𝔨 a :=
      fun a => MvPolynomial.aeval_C Ψ a
    show Φ₀ ((A₁ * A₂).coeff (kk v) - MvPolynomial.C (f.coeff (kk v))) = 0
    rw [map_sub, hrel v, hΦ₀C]
    exact sub_self _
  let B := R ⧸ Ideal.span (Set.range rel)
  have hker : Ideal.span (Set.range rel) ≤ RingHom.ker Φ₀.toRingHom := by
    rw [Ideal.span_le]
    rintro x ⟨v, rfl⟩
    exact hΦrel v
  let φ : B →ₐ[A] 𝔨 := Ideal.Quotient.liftₐ _ Φ₀ hker
  have hφ_mk : ∀ x : R, φ (Ideal.Quotient.mk _ x) = Φ₀ x := by
    intro x
    rw [← Ideal.Quotient.mkₐ_eq_mk A (Ideal.span (Set.range rel))]
    exact DFunLike.congr_fun
      (Ideal.Quotient.liftₐ_comp (Ideal.span (Set.range rel)) Φ₀ hker) x
  let P : Algebra.PreSubmersivePresentation A B ι ι :=
    { Algebra.Presentation.naive (v := rel) with map := id, map_inj := fun _ _ h => h }
  have hPrel : ∀ v : ι, P.relation v = rel v := fun v => rfl
  have hPmap : ∀ i : ι, P.map i = i := fun i => rfl
  let D₁ : ι → Polynomial R := fun k => match k with
    | Sum.inl a => Polynomial.X ^ (a : ℕ) | Sum.inr _ => 0
  let D₂ : ι → Polynomial R := fun k => match k with
    | Sum.inl _ => 0 | Sum.inr b => Polynomial.X ^ (b : ℕ)
  have hpderA₁ : ∀ (i : ι) (a : ℕ), MvPolynomial.pderiv i (A₁.coeff a) = (D₁ i).coeff a := by
    intro i a
    rw [hcoeffA₁ a]
    cases i with
    | inl c =>
      simp only [D₁, Polynomial.coeff_X_pow]
      by_cases h : a < n
      · rw [dif_pos h, MvPolynomial.pderiv_X, Pi.single_apply]
        by_cases hac : a = c
        · rw [if_pos (Sum.inl_injective.eq_iff.mpr (Fin.ext hac)), if_pos hac]
        · rw [if_neg (fun hh => hac (Fin.ext_iff.mp (Sum.inl_injective hh))), if_neg hac]
      · rw [dif_neg h]
        by_cases h2 : a = n
        · rw [if_pos h2, MvPolynomial.pderiv_one, if_neg (by omega)]
        · rw [if_neg h2, map_zero, if_neg (by omega)]
    | inr c =>
      simp only [D₁]
      by_cases h : a < n
      · rw [dif_pos h, MvPolynomial.pderiv_X, Pi.single_apply,
          if_neg (by simp), Polynomial.coeff_zero]
      · rw [dif_neg h]
        by_cases h2 : a = n
        · rw [if_pos h2, MvPolynomial.pderiv_one, Polynomial.coeff_zero]
        · rw [if_neg h2, map_zero, Polynomial.coeff_zero]
  have hpderA₂ : ∀ (i : ι) (b : ℕ), MvPolynomial.pderiv i (A₂.coeff b) = (D₂ i).coeff b := by
    intro i b
    rw [hcoeffA₂ b]
    cases i with
    | inl c =>
      simp only [D₂]
      by_cases h : b < m + 1
      · rw [dif_pos h, MvPolynomial.pderiv_X, Pi.single_apply,
          if_neg (by simp), Polynomial.coeff_zero]
      · rw [dif_neg h, map_zero, Polynomial.coeff_zero]
    | inr c =>
      simp only [D₂, Polynomial.coeff_X_pow]
      by_cases h : b < m + 1
      · rw [dif_pos h, MvPolynomial.pderiv_X, Pi.single_apply]
        by_cases hbc : b = c
        · rw [if_pos (Sum.inr_injective.eq_iff.mpr (Fin.ext hbc)), if_pos hbc]
        · rw [if_neg (fun hh => hbc (Fin.ext_iff.mp (Sum.inr_injective hh))), if_neg hbc]
      · rw [dif_neg h, map_zero, if_neg (by omega)]
  have hpderrel : ∀ (i j : ι),
      MvPolynomial.pderiv i (rel j) = ((D₁ i) * A₂ + A₁ * (D₂ i)).coeff (kk j) := by
    intro i j
    show MvPolynomial.pderiv i ((A₁ * A₂).coeff (kk j) - MvPolynomial.C (f.coeff (kk j)))
      = ((D₁ i) * A₂ + A₁ * (D₂ i)).coeff (kk j)
    rw [map_sub, MvPolynomial.pderiv_C, sub_zero]
    rw [Polynomial.coeff_mul, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul]
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [MvPolynomial.pderiv_mul, hpderA₁, hpderA₂]
  let ee : ι → ℕ := fun k => match k with
    | Sum.inl a => (a : ℕ) | Sum.inr b => (b : ℕ)
  let PP : ι → Polynomial 𝔨 := fun k => match k with
    | Sum.inl _ => H | Sum.inr _ => G
  have hmat : ∀ i j : ι, (P.jacobiMatrix.map Φ₀.toRingHom) i j =
      (Polynomial.X ^ (ee i) * PP i).coeff (kk j) := by
    intro i j
    rw [Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hPmap, hPrel,
      hpderrel]
    rw [← Polynomial.coeff_map Φ₀.toRingHom (kk j)]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hmapA₁, hmapA₂]
    cases i with
    | inl a =>
      dsimp only [D₁, D₂, PP, ee]
      simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero,
        mul_zero, add_zero]
    | inr b =>
      dsimp only [D₁, D₂, PP, ee]
      simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero,
        zero_mul, zero_add]
      rw [mul_comm]
  -- the sylvester identification
  have hPB : (algebraMap P.Ring B : P.Ring →+* B) = Ideal.Quotient.mk _ :=
    RingHom.ext fun x => rfl
  have hφjac : φ P.jacobian = Φ₀ P.jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hPB, hφ_mk]
  let MN : Matrix ι ι 𝔨 := fun i j => (Polynomial.X ^ (ee i) * PP i).coeff (kk j)
  have hMN : P.jacobiMatrix.map Φ₀.toRingHom = MN := Matrix.ext (fun i j => hmat i j)
  have hEntry_inl : ∀ (a : Fin n) (k : ℕ),
      (Polynomial.X ^ (a:ℕ) * H).coeff k =
        (if k ∈ Set.Icc (a:ℕ) ((a:ℕ) + (m+1)) then H.coeff (k - (a:ℕ)) else 0) := by
    intro a k
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h1 : (a:ℕ) ≤ k
    · rw [if_pos h1]
      by_cases h2 : k ≤ (a:ℕ) + (m+1)
      · rw [if_pos (Set.mem_Icc.mpr ⟨h1, h2⟩)]
      · rw [if_neg (fun hh => h2 (Set.mem_Icc.mp hh).2)]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := not_le.mp h2; omega)
    · rw [if_neg h1, if_neg (fun hh => h1 (Set.mem_Icc.mp hh).1)]
  have hEntry_inr : ∀ (b : Fin (m+1)) (k : ℕ),
      (Polynomial.X ^ (b:ℕ) * G).coeff k =
        (if k ∈ Set.Icc (b:ℕ) ((b:ℕ) + n) then G.coeff (k - (b:ℕ)) else 0) := by
    intro b k
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h1 : (b:ℕ) ≤ k
    · rw [if_pos h1]
      by_cases h2 : k ≤ (b:ℕ) + n
      · rw [if_pos (Set.mem_Icc.mpr ⟨h1, h2⟩)]
      · rw [if_neg (fun hh => h2 (Set.mem_Icc.mp hh).2)]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := not_le.mp h2; omega)
    · rw [if_neg h1, if_neg (fun hh => h1 (Set.mem_Icc.mp hh).1)]
  let Syl : Matrix (Fin (n + (m+1))) (Fin (n + (m+1))) 𝔨 := Polynomial.sylvester G H n (m+1)
  have hMN_eq : MN = Matrix.reindex (finSumFinEquiv.symm : Fin (n + (m+1)) ≃ ι)
      (finSumFinEquiv.symm : Fin (n + (m+1)) ≃ ι) Syl.transpose := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
    cases i with
    | inl a =>
      cases j with
      | inl c =>
        show MN (Sum.inl a) (Sum.inl c) = Syl (finSumFinEquiv (Sum.inl c)) (finSumFinEquiv (Sum.inl a))
        dsimp only [MN, ee, PP, kk]
        rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
        rw [show Syl (Fin.castAdd (m+1) c) (Fin.castAdd (m+1) a) =
            (if (c:ℕ) ∈ Set.Icc (a:ℕ) ((a:ℕ) + (m+1)) then H.coeff ((c:ℕ) - (a:ℕ)) else 0) by
          simp [Syl, Polynomial.sylvester, Fin.addCases_left]]
        exact hEntry_inl a c
      | inr d =>
        show MN (Sum.inl a) (Sum.inr d) = Syl (finSumFinEquiv (Sum.inr d)) (finSumFinEquiv (Sum.inl a))
        dsimp only [MN, ee, PP, kk]
        rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left]
        rw [show Syl (Fin.natAdd n d) (Fin.castAdd (m+1) a) =
            (if ((n + (d:ℕ))) ∈ Set.Icc (a:ℕ) ((a:ℕ) + (m+1)) then H.coeff ((n + (d:ℕ)) - (a:ℕ)) else 0) by
          simp [Syl, Polynomial.sylvester, Fin.addCases_left, Fin.val_natAdd]]
        exact hEntry_inl a (n + (d:ℕ))
    | inr b =>
      cases j with
      | inl c =>
        show MN (Sum.inr b) (Sum.inl c) = Syl (finSumFinEquiv (Sum.inl c)) (finSumFinEquiv (Sum.inr b))
        dsimp only [MN, ee, PP, kk]
        rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        rw [show Syl (Fin.castAdd (m+1) c) (Fin.natAdd n b) =
            (if (c:ℕ) ∈ Set.Icc (b:ℕ) ((b:ℕ) + n) then G.coeff ((c:ℕ) - (b:ℕ)) else 0) by
          simp [Syl, Polynomial.sylvester, Fin.addCases_right]]
        exact hEntry_inr b c
      | inr d =>
        show MN (Sum.inr b) (Sum.inr d) = Syl (finSumFinEquiv (Sum.inr d)) (finSumFinEquiv (Sum.inr b))
        dsimp only [MN, ee, PP, kk]
        rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
        rw [show Syl (Fin.natAdd n d) (Fin.natAdd n b) =
            (if ((n + (d:ℕ))) ∈ Set.Icc (b:ℕ) ((b:ℕ) + n) then G.coeff ((n + (d:ℕ)) - (b:ℕ)) else 0) by
          simp [Syl, Polynomial.sylvester, Fin.addCases_right, Fin.val_natAdd]]
        exact hEntry_inr b (n + (d:ℕ))
  have hSylne : Syl.det ≠ 0 := by
    have hHm' : H.natDegree ≤ m + 1 := by omega
    have h1 : Polynomial.resultant G H n (m+1) = Polynomial.resultant G H := by
      conv_lhs => rw [show m + 1 = H.natDegree + (m + 1 - H.natDegree) from (Nat.add_sub_cancel' hHm').symm]
      rw [Polynomial.resultant_add_right_deg]
      rw [show G.coeff n = 1 from hGmonic.coeff_natDegree, one_pow, one_mul]
      rfl
    have h2 : IsUnit (Polynomial.resultant G H) :=
      (Polynomial.isUnit_resultant_iff_isCoprime hGmonic).mpr hcop'
    have h3 : Polynomial.resultant G H n (m+1) ≠ 0 := by rw [h1]; exact h2.ne_zero
    simpa [Syl, Polynomial.resultant] using h3
  have hMdet : MN.det ≠ 0 := by
    rw [hMN_eq, Matrix.det_reindex_self, Matrix.det_transpose]
    exact hSylne
  have hφjac_ne : φ P.jacobian ≠ 0 := by
    have h1 : Φ₀ P.jacobiMatrix.det = MN.det := by
      rw [show Φ₀ P.jacobiMatrix.det = (P.jacobiMatrix.map Φ₀.toRingHom).det from
        RingHom.map_det Φ₀.toRingHom P.jacobiMatrix]
      rw [hMN]
    rw [hφjac, h1]
    exact hMdet
  -- étale localization and retraction
  let Δ : B := P.jacobian
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective 𝔪 x
    exact ⟨algebraMap A B a, AlgHom.commutes φ a⟩
  have hφΔunit : IsUnit (φ Δ) := isUnit_iff_ne_zero.mpr hφjac_ne
  let φ' : Localization.Away Δ →ₐ[A] 𝔨 := IsLocalization.Away.liftAlgHom Δ (f := φ) hφΔunit
  have hφ'b : ∀ b : B, φ' (algebraMap B (Localization.Away Δ) b) = φ b := by
    intro b
    have hh := IsLocalization.Away.lift_comp (R := B) (S := Localization.Away Δ) (P := 𝔨)
      Δ hφΔunit (g := φ.toRingHom)
    exact RingHom.congr_fun hh b
  have hφ'surj : Function.Surjective φ' := by
    intro x
    obtain ⟨b, hb⟩ := hφsurj x
    exact ⟨algebraMap B (Localization.Away Δ) b, by rw [hφ'b b, hb]⟩
  let Qpres : Algebra.PreSubmersivePresentation B (Localization.Away Δ) Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway (Localization.Away Δ) Δ
  let hSub : Algebra.SubmersivePresentation A (Localization.Away Δ) (Unit ⊕ ι) (Unit ⊕ ι) :=
    { (Qpres.comp P) with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit Δ).mul (IsLocalization.Away.algebraMap_isUnit Δ) }
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away Δ) :=
    Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension hSub
      (by rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension Qpres P]
          simp [Algebra.Presentation.dimension])
  haveI hEtale : Algebra.Etale A (Localization.Away Δ) := inferInstance
  obtain ⟨τ, hτ⟩ := exists_algHom_retract_of_isEtale_of_surjective hEtale φ' hφ'surj
  -- extraction
  let ca : Fin n → A := fun a => τ (algebraMap B (Localization.Away Δ)
    (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl a))))
  let cb : Fin (m+1) → A := fun b => τ (algebraMap B (Localization.Away Δ)
    (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr b))))
  let F₁ : Polynomial A := Polynomial.X ^ n +
    ∑ a : Fin n, Polynomial.C (ca a) * Polynomial.X ^ (a : ℕ)
  let F₂ : Polynomial A := ∑ b : Fin (m+1), Polynomial.C (cb b) * Polynomial.X ^ (b : ℕ)
  let Θ : R →ₐ[A] A := τ.comp ((IsScalarTower.toAlgHom A B (Localization.Away Δ)).comp
    (Ideal.Quotient.mkₐ A (Ideal.span (Set.range rel))))
  have hΘX : ∀ i : ι, Θ (MvPolynomial.X i) =
      (match i with | Sum.inl a => ca a | Sum.inr b => cb b) := by
    intro i
    cases i <;> rfl
  have hΘmk : ∀ x : R, Θ x = τ (algebraMap B (Localization.Away Δ) (Ideal.Quotient.mk _ x)) := by
    intro x
    rfl
  have hΘrel : ∀ v : ι, Θ (rel v) = 0 := by
    intro v
    rw [hΘmk, show Ideal.Quotient.mk _ (rel v) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self v)), map_zero, map_zero]
  have hΘC : ∀ a : A, Θ (MvPolynomial.C a) = a := fun a => AlgHom.commutes Θ a
  have hmapΘ₁ : A₁.map Θ.toRingHom = F₁ := by
    have h1 : A₁.map Θ.toRingHom = Polynomial.X ^ n +
        ∑ i : Fin n, Polynomial.C (ca i) * Polynomial.X ^ (i : ℕ) := by
      show (Polynomial.X ^ n + ∑ i : Fin n,
          Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)).map Θ.toRingHom = _
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
        rfl
    rw [h1]
  have hmapΘ₂ : A₂.map Θ.toRingHom = F₂ := by
    have h1 : A₂.map Θ.toRingHom =
        ∑ j : Fin (m+1), Polynomial.C (cb j) * Polynomial.X ^ (j : ℕ) := by
      show (∑ j : Fin (m+1),
          Polynomial.C (MvPolynomial.X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)).map Θ.toRingHom = _
      rw [Polynomial.map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      rfl
    rw [h1]
  have hFFcoeff : ∀ v : ι, (F₁ * F₂).coeff (kk v) = f.coeff (kk v) := by
    intro v
    have h1 : Θ ((A₁ * A₂).coeff (kk v)) = (F₁ * F₂).coeff (kk v) := by
      rw [show Θ ((A₁ * A₂).coeff (kk v)) =
        (Polynomial.map Θ.toRingHom (A₁ * A₂)).coeff (kk v) from
        (Polynomial.coeff_map Θ.toRingHom (kk v)).symm]
      rw [Polynomial.map_mul, hmapΘ₁, hmapΘ₂]
    have h2 : Θ (rel v) = 0 := hΘrel v
    rw [show rel v = (A₁ * A₂).coeff (kk v) - MvPolynomial.C (f.coeff (kk v)) from rfl,
      map_sub, hΘC, sub_eq_zero] at h2
    rw [← h1, h2]
  have hkk_surj : ∀ k ≤ N, ∃ v : ι, kk v = k := by
    intro k hk
    by_cases h : k < n
    · exact ⟨Sum.inl ⟨k, h⟩, rfl⟩
    · refine ⟨Sum.inr ⟨k - n, by omega⟩, ?_⟩
      dsimp only [kk]
      omega
  have hSdeg : (∑ a : Fin n, Polynomial.C (ca a) * Polynomial.X ^ (a : ℕ)).degree < (n : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    exact if_neg (by have := a.isLt; omega)
  have hF₁monic : F₁.Monic := by
    dsimp only [F₁]
    exact Polynomial.monic_X_pow_add hSdeg
  have hF₂deg : F₂.natDegree ≤ m := by
    dsimp only [F₂]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro b _
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  have hF₁deg : F₁.natDegree ≤ n := by
    dsimp only [F₁]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_of_eq (Polynomial.natDegree_X_pow n)
    · rw [Polynomial.natDegree_le_iff_degree_le]
      exact le_of_lt hSdeg
  have hFF : F₁ * F₂ = f := by
    ext k
    by_cases hk : k ≤ N
    · obtain ⟨v, hv⟩ := hkk_surj k hk
      rw [← hv]
      exact hFFcoeff v
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (le_trans Polynomial.natDegree_mul_le (by omega : F₁.natDegree + F₂.natDegree ≤ N))
        (by omega : N < k))
  have hca : ∀ a : Fin n, algebraMap A 𝔨 (ca a) = G.coeff (a : ℕ) := by
    intro a
    have h1 : algebraMap A 𝔨 (ca a) = φ' (algebraMap B (Localization.Away Δ)
        (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl a)))) := hτ _
    rw [h1, hφ'b, hφ_mk, hΦ₀X]
  have hcb : ∀ b : Fin (m+1), algebraMap A 𝔨 (cb b) = H.coeff (b : ℕ) := by
    intro b
    have h1 : algebraMap A 𝔨 (cb b) = φ' (algebraMap B (Localization.Away Δ)
        (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr b)))) := hτ _
    rw [h1, hφ'b, hφ_mk, hΦ₀X]
  have hmapF₁ : Polynomial.map (algebraMap A 𝔨) F₁ = G := by
    have h1 : Polynomial.map (algebraMap A 𝔨) F₁ = Polynomial.X ^ n +
        ∑ a : Fin n, Polynomial.C (G.coeff (a:ℕ)) * Polynomial.X ^ (a : ℕ) := by
      dsimp only [F₁]
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hca a]
    rw [h1]
    exact (Polynomial.eq_X_pow_add_sum_of_monic G hGmonic).symm
  have hmapF₂ : Polynomial.map (algebraMap A 𝔨) F₂ = H := by
    have h1 : Polynomial.map (algebraMap A 𝔨) F₂ =
        ∑ b : Fin (m+1), Polynomial.C (H.coeff (b:ℕ)) * Polynomial.X ^ (b : ℕ) := by
      dsimp only [F₂]
      rw [Polynomial.map_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hcb b]
    rw [h1]
    exact (Polynomial.eq_sum_of_natDegree_le H hHm).symm
  refine ⟨F₁, F₂, hF₁monic, ?_, ?_, hFF.symm⟩
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [Polynomial.map_map, ← hmap_eq, hmapF₁, hG]
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [Polynomial.map_map, ← hmap_eq, hmapF₂, hH]

end Commons.RingTheory.Henselian