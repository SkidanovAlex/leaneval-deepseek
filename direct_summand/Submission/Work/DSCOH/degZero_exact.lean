/-
Area DSCOH — exactness of the degree-zero part of the chart localizations.

Given a complex of graded `A[X₀,…,X_{n-1}]`-modules

  `ℳ  --f-->  ℳ'  --g-->  ℳ''`

which is degreewise left-exact at `ℳ'` (`ker g ⊓ ℳ'_d ⊆ f ℳ_d`), the induced maps on the
degree-zero parts of the localizations at the chart `S` preserve these degree-zero parts
and form a left-exact sequence of `A`-modules there.  Its proof uses that multiplication by
`X_S = ∏_{i∈S} Xᵢ` shifts the graded pieces by exactly `|S|`, so that the degree-zero part of
the localization is the filtered union of the pieces `ℳ_{k|S|}/X_S^k`.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.degZero_locMapOf
import Submission.Work.DSCOH.divPow_toLoc_mem

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Elementary lemmas on the chart localizations -/

/-- The element `divPow S k (toLoc S m) = m / X_S^k` is the class of `m` with denominator
`(∏_{i∈S} Xᵢ)^k`. -/
private lemma divPow_toLoc_eq_mk {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) (k : ℕ) (m : M) :
    divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) =
      LocalizedModule.mk m ⟨monomial (A := A) S ^ k,
        Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩ := by
  unfold divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

/-- The chosen presentation of the degree-zero part is stable under raising the index:
`m / X_S^k = (X_S^j · m) / X_S^{k+j}`. -/
private lemma divPow_toLoc_smul_monomial_pow {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) (k j : ℕ) (m : M) :
    divPow (A := A) (M := M) S (k + j)
        (toLoc (A := A) (M := M) S ((monomial (A := A) S) ^ j • m)) =
      divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) := by
  have h1 := divPow_toLoc_eq_mk (A := A) (S := S) (M := M) (k := k + j)
    (m := (monomial (A := A) S) ^ j • m)
  have h2 := divPow_toLoc_eq_mk (A := A) (S := S) (M := M) (k := k) (m := m)
  rw [h1, h2]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, smul_smul, ← pow_add]

/-- The map induced on localizations sends `m / X_S^k` to `φ m / X_S^k`. -/
private lemma locMapOf_divPow_toLoc {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    (φ : M →ₗ[Poly A n] N) (S : Finset (Fin n)) (k : ℕ) (m : M) :
    locMapOf φ S (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      divPow (A := A) (M := N) S k (toLoc (A := A) (M := N) S (φ m)) := by
  unfold locMapOf divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]
  rw [IsLocalizedModule.map_LocalizedModules]

/-- A fraction `m / s` vanishes in the localization at `S` exactly when some `u ∈ S`
annihilates `m`. -/
private lemma mk_eq_zero_iff {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) (m : M) (s : subS (A := A) S) :
    LocalizedModule.mk m s = 0 ↔ ∃ u : subS (A := A) S, u • m = 0 := by
  rw [show (0 : LocalizedModule (subS (A := A) S) M) = LocalizedModule.mk (0 : M) 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by simpa using hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by simp [hu]⟩

/-- The product of the variables in `S` is homogeneous of degree `|S|`. -/
private lemma monomial_mem_homSub (S : Finset (Fin n)) :
    monomial (A := A) S ∈ homSub A n S.card := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  unfold monomial Var
  simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)

/-- Its `j`-th power is homogeneous of degree `j·|S|`. -/
private lemma monomial_pow_mem_homSub (S : Finset (Fin n)) (j : ℕ) :
    (monomial (A := A) S) ^ j ∈ homSub A n (j * S.card) := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  have h1 : (monomial (A := A) S).IsHomogeneous S.card := by
    unfold monomial Var
    simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)
  simpa only [mul_comm] using h1.pow j

/-- Splitting off a variable from the monomial `∏_{i∈S} Xᵢ`. -/
private lemma monomial_eq_Var_mul (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    monomial (A := A) S = Var (A := A) i * monomial (A := A) (S.erase i) := by
  unfold monomial Var
  exact (Finset.prod_erase_mul S (fun k => (MvPolynomial.X k : Poly A n)) hi).symm.trans
    (mul_comm _ _)

/-- Every element of the submonoid generated by the variables indexed by `S` divides some
power of `X_S = ∏_{i∈S} Xᵢ`.  This is what allows us to replace an arbitrary annihilator
`u ∈ subS S` of a localized element by a power of `X_S`. -/
private lemma monomial_pow_mul (S : Finset (Fin n)) (u : Poly A n)
    (hu : u ∈ subS (A := A) S) :
    ∃ j v, monomial (A := A) S ^ j = u * v := by
  refine Submonoid.closure_induction (motive := fun u _ => ∃ j v, monomial (A := A) S ^ j = u * v)
    ?_ ?_ ?_ hu
  · rintro x ⟨i, hi, rfl⟩
    exact ⟨1, monomial (A := A) (S.erase i),
      by rw [pow_one]; exact monomial_eq_Var_mul S i hi⟩
  · exact ⟨0, 1, by simp⟩
  · intro x y _ _ ihx ihy
    obtain ⟨j1, v1, hv1⟩ := ihx
    obtain ⟨j2, v2, hv2⟩ := ihy
    refine ⟨j1 + j2, v1 * v2, ?_⟩
    rw [pow_add, hv1, hv2]
    ring

/-- An injective map of modules induces an injective map of their localizations. -/
private lemma locMapOf_injective {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    (φ : M →ₗ[Poly A n] N) (hφ : Function.Injective φ) (S : Finset (Fin n)) :
    Function.Injective (locMapOf φ S) := by
  unfold locMapOf
  exact IsLocalizedModule.map_injective (subS (A := A) S) (LocalizedModule.mkLinearMap (subS S) M)
    (LocalizedModule.mkLinearMap (subS S) N) φ hφ

/-! ## The degree-zero part as a filtered union -/

/-- **Generator description of the degree-zero part.**  If `ℳ` is a graded family
(`homSub A n` acts on it), every element of `degZero ℳ S` has the form `m / X_S^k` with
`m ∈ ℳ (k · |S|)`.  This is where the `GradedSMul` hypothesis is used: it makes the pieces
`ℳ (k|S|)/X_S^k` increasing in `k`. -/
private lemma mem_degZero_iff_graded {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (S : Finset (Fin n))
    (y : locAt (A := A) (M := M) S) :
    y ∈ degZero ℳ S ↔ ∃ k m, m ∈ ℳ (k * S.card) ∧
      divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) = y := by
  constructor
  · intro hy
    have hmono : Monotone (fun k => Submodule.map
        ((divPow (A := A) (M := M) S k).comp (toLoc (A := A) (M := M) S))
        (ℳ (k * S.card))) := by
      apply monotone_nat_of_le_succ
      intro k
      rintro _ ⟨m, hm, rfl⟩
      refine Submodule.mem_map.mpr ⟨(monomial (A := A) S) ^ 1 • m, ?_, ?_⟩
      · rw [pow_one]
        have hsm := SetLike.GradedSMul.smul_mem (monomial_mem_homSub (A := A) S) hm
        rwa [show S.card +ᵥ (k * S.card) = (k + 1) * S.card from by
          rw [show S.card +ᵥ (k * S.card) = S.card + k * S.card from rfl]; ring] at hsm
      · show divPow (A := A) (M := M) S (k + 1)
            (toLoc (A := A) (M := M) S ((monomial (A := A) S) ^ 1 • m)) =
          divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)
        exact divPow_toLoc_smul_monomial_pow (A := A) (M := M) S k 1 m
    have hy' : y ∈ ⨆ k, Submodule.map
        ((divPow (A := A) (M := M) S k).comp (toLoc (A := A) (M := M) S))
        (ℳ (k * S.card)) := hy
    obtain ⟨k, m, hm, hmy⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hy'
    exact ⟨k, m, hm, hmy⟩
  · rintro ⟨k, m, hm, rfl⟩
    exact divPow_toLoc_mem ℳ S k hm

/-- **Generator description after pushing forward along a surjective-in-each-degree map.**
Here `ℳ'' d = g (ℳ' d)`; the graded structure of `ℳ'` is what makes the pieces of `ℳ''`
increasing, so that a single generator suffices. -/
private lemma mem_degZero_map_iff {M' : Type*} [AddCommGroup M'] [Module A M']
    [Module (Poly A n) M'] [IsScalarTower A (Poly A n) M']
    {M'' : Type*} [AddCommGroup M''] [Module A M''] [Module (Poly A n) M'']
    [IsScalarTower A (Poly A n) M'']
    {ℳ' : ℕ → Submodule A M'} [SetLike.GradedSMul (homSub A n) ℳ']
    {ℳ'' : ℕ → Submodule A M''}
    (g : M' →ₗ[Poly A n] M'')
    (hgr2 : ∀ d, Submodule.map (g.restrictScalars A) (ℳ' d) = ℳ'' d) (S : Finset (Fin n))
    (z : locAt (A := A) (M := M'') S) :
    z ∈ degZero ℳ'' S ↔ ∃ k m', m' ∈ ℳ' (k * S.card) ∧
      divPow (A := A) (M := M'') S k (toLoc (A := A) (M := M'') S (g m')) = z := by
  have hmonoQ : Monotone (fun k => Submodule.map
      ((divPow (A := A) (M := M'') S k).comp (toLoc (A := A) (M := M'') S))
      (ℳ'' (k * S.card))) := by
    apply monotone_nat_of_le_succ
    intro k
    rintro _ ⟨z'', hz'', rfl⟩
    obtain ⟨m', hm', hm'eq⟩ := Submodule.mem_map.mp (hgr2 (k * S.card) ▸ hz'')
    have hmem : (monomial (A := A) S) • m' ∈ ℳ' ((k + 1) * S.card) := by
      have h0 := SetLike.GradedSMul.smul_mem (monomial_mem_homSub (A := A) S) hm'
      rwa [show S.card +ᵥ (k * S.card) = (k + 1) * S.card from by
        rw [show S.card +ᵥ (k * S.card) = S.card + k * S.card from rfl]; ring] at h0
    have hg : (monomial (A := A) S) • z'' = g ((monomial (A := A) S) • m') := by
      rw [← hm'eq]
      exact (map_smul g (monomial (A := A) S) m').symm
    refine Submodule.mem_map.mpr ⟨(monomial (A := A) S) ^ 1 • z'', ?_, ?_⟩
    · rw [pow_one, hg]
      rw [← hgr2 ((k + 1) * S.card)]
      exact Submodule.mem_map.mpr ⟨_, hmem, rfl⟩
    · show divPow (A := A) (M := M'') S (k + 1)
          (toLoc (A := A) (M := M'') S ((monomial (A := A) S) ^ 1 • z'')) =
        divPow (A := A) (M := M'') S k (toLoc (A := A) (M := M'') S z'')
      exact divPow_toLoc_smul_monomial_pow (A := A) (M := M'') S k 1 z''
  constructor
  · intro hz
    have hz' : z ∈ ⨆ k, Submodule.map
        ((divPow (A := A) (M := M'') S k).comp (toLoc (A := A) (M := M'') S))
        (ℳ'' (k * S.card)) := hz
    obtain ⟨k, z'', hz'', hz''eq⟩ := (Submodule.mem_iSup_of_directed _ hmonoQ.directed_le).mp hz'
    obtain ⟨m', hm', hm'eq⟩ := Submodule.mem_map.mp (hgr2 (k * S.card) ▸ hz'')
    rw [← hm'eq] at hz''eq
    exact ⟨k, m', hm', hz''eq⟩
  · rintro ⟨k, m', hm', rfl⟩
    refine divPow_toLoc_mem ℳ'' S k ?_
    rw [← hgr2 (k * S.card)]
    exact Submodule.mem_map.mpr ⟨m', hm', rfl⟩

/-! ## The main exactness statement -/

theorem degZero_exact {A : Type*} [CommRing A] {n : ℕ}
    {M M' M'' : Type*}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    [AddCommGroup M'] [Module A M'] [Module (Poly A n) M'] [IsScalarTower A (Poly A n) M']
    [AddCommGroup M''] [Module A M''] [Module (Poly A n) M''] [IsScalarTower A (Poly A n) M'']
    {ℳ : ℕ → Submodule A M} {ℳ' : ℕ → Submodule A M'} [SetLike.GradedSMul (homSub A n) ℳ']
    {ℳ'' : ℕ → Submodule A M''}
    (f : M →ₗ[Poly A n] M') (g : M' →ₗ[Poly A n] M'')
    (hinj : Function.Injective f)
    (hgr1 : ∀ d, Submodule.map (f.restrictScalars A) (ℳ d) ≤ ℳ' d)
    (hgr2 : ∀ d, Submodule.map (g.restrictScalars A) (ℳ' d) = ℳ'' d)
    (hker : ∀ d, ℳ' d ⊓ LinearMap.ker (g.restrictScalars A) ≤
      Submodule.map (f.restrictScalars A) (ℳ d))
    (S : Finset (Fin n)) :
    (∀ x ∈ degZero ℳ S, locMapOf f S x ∈ degZero ℳ' S) ∧
    (∀ y ∈ degZero ℳ' S, locMapOf g S y ∈ degZero ℳ'' S) ∧
    (∀ x ∈ degZero ℳ S, locMapOf f S x = 0 → x = 0) ∧
    (∀ y ∈ degZero ℳ' S, locMapOf g S y = 0 → ∃ x ∈ degZero ℳ S, locMapOf f S x = y) ∧
    (∀ z ∈ degZero ℳ'' S, ∃ y ∈ degZero ℳ' S, locMapOf g S y = z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact degZero_locMapOf (A := A) (n := n) ℳ ℳ' f hgr1 S
  · exact degZero_locMapOf (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) S
  · intro x _ hx0
    have h : locMapOf (A := A) (M := M) f S x = locMapOf (A := A) (M := M) f S 0 := by
      rw [map_zero]
      exact hx0
    exact locMapOf_injective (A := A) (M := M) (N := M') f hinj S h
  · intro y hy hy0
    obtain ⟨k, m', hm', hky⟩ := (mem_degZero_iff_graded (A := A) (n := n) ℳ' S y).mp hy
    -- `locMapOf g S y = 0` means that `g m'` is annihilated by some `u ∈ subS S`.
    have hg0 : divPow (A := A) (M := M'') S k (toLoc (A := A) (M := M'') S (g m')) = 0 := by
      have h := hy0
      rw [← hky] at h
      rwa [locMapOf_divPow_toLoc (A := A) (M := M') (N := M'') g S k m'] at h
    have hmk : LocalizedModule.mk (g m') ⟨monomial (A := A) S ^ k,
        Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩ = 0 := by
      rw [← divPow_toLoc_eq_mk (A := A) (M := M'') S k (g m')]
      exact hg0
    obtain ⟨u, hu⟩ := (mk_eq_zero_iff (A := A) (M := M'') S (g m')
      ⟨monomial (A := A) S ^ k,
        Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩).mp hmk
    rw [Submonoid.smul_def] at hu
    -- replace the arbitrary annihilator `u` by a power of `X_S`.
    obtain ⟨j, v, hv⟩ := monomial_pow_mul (A := A) S (↑u) u.2
    have hX0 : (monomial (A := A) S) ^ j • (g m') = 0 := by
      rw [hv]
      rw [mul_comm, mul_smul, hu, smul_zero]
    -- the shifted element still lies in the graded piece and in `ker g`.
    have hw_gr : (monomial (A := A) S) ^ j • m' ∈ ℳ' ((k + j) * S.card) := by
      have h0 := SetLike.GradedSMul.smul_mem (monomial_pow_mem_homSub (A := A) S j) hm'
      rwa [show j * S.card +ᵥ (k * S.card) = (k + j) * S.card from by
        rw [show j * S.card +ᵥ (k * S.card) = j * S.card + k * S.card from rfl]; ring] at h0
    have hw_ker : (monomial (A := A) S) ^ j • m' ∈ LinearMap.ker (g.restrictScalars A) := by
      rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply]
      simpa [map_smul] using hX0
    obtain ⟨m, hm, hfm⟩ := Submodule.mem_map.mp
      (hker ((k + j) * S.card) (Submodule.mem_inf.mpr ⟨hw_gr, hw_ker⟩))
    refine ⟨divPow (A := A) (M := M) S (k + j) (toLoc (A := A) (M := M) S m),
      divPow_toLoc_mem ℳ S (k + j) hm, ?_⟩
    show locMapOf (A := A) (M := M) f S
        (divPow (A := A) (M := M) S (k + j) (toLoc (A := A) (M := M) S m)) = y
    rw [locMapOf_divPow_toLoc (A := A) (M := M) (N := M') f S (k + j) m]
    rw [LinearMap.restrictScalars_apply] at hfm
    rw [hfm]
    rw [divPow_toLoc_smul_monomial_pow (A := A) (M := M') S k j m']
    exact hky
  · intro z hz
    obtain ⟨k, m', hm', hkz⟩ := (mem_degZero_map_iff (A := A) (n := n) g hgr2 S z).mp hz
    refine ⟨divPow (A := A) (M := M') S k (toLoc (A := A) (M := M') S m'),
      divPow_toLoc_mem ℳ' S k hm', ?_⟩
    show locMapOf (A := A) (M := M') g S
        (divPow (A := A) (M := M') S k (toLoc (A := A) (M := M') S m')) = z
    rw [locMapOf_divPow_toLoc (A := A) (M := M') (N := M'') g S k m', hkz]

end Work.DSCOH
