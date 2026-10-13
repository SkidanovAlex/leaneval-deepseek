import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

/-- The element `m ∈ ℳ (k · |S|)` gives the degree-zero element `m / X_S^k` of the localization at
`S`; `divPow S k (toLoc S m) = m / X_S^k`. -/
private lemma divPow_toLoc_eq {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) (k : ℕ) (m : M) :
    divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m) =
      @LocalizedModule.mk (Poly A n) _ (subS (A := A) S) M _ _ m
        ⟨monomial (A := A) S ^ k,
          Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩ := by
  unfold divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

/-- `resAt h (m / X_S^k) = (X_{T\S})^k · m / X_T^k`: the transition map of the charts is
compatible with the chosen descriptions of the degree-zero parts on both sides. -/
private lemma resAt_divPow_eq {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) (m : M) :
    resAt (A := A) (M := M) h (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      divPow (A := A) (M := M) T k
        (toLoc (A := A) (M := M) T ((monomial (A := A) (T \ S)) ^ k • m)) := by
  have hpoly : (monomial (A := A) T) ^ k =
      (monomial (A := A) S) ^ k * (monomial (A := A) (T \ S)) ^ k := by
    rw [show monomial (A := A) T = monomial (A := A) S * monomial (A := A) (T \ S) from by
      unfold monomial Var; rw [← Finset.prod_sdiff h]; exact mul_comm _ _]
    rw [mul_pow]
  rw [show resAt (A := A) (M := M) h
        (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      @LocalizedModule.mk (Poly A n) _ (subS (A := A) T) M _ _ m
        ⟨(monomial (A := A) S) ^ k,
          subS_mono (A := A) h
            (Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k)⟩ from by
    unfold resAt divPow toLoc
    simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, LocalizedModule.liftOfLE, one_mul]
    rw [IsLocalizedModule.mk_eq_mk']
    simp only [IsLocalizedModule.liftOfLE_mk']
    rw [← IsLocalizedModule.mk_eq_mk']]
  unfold divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul]
  rw [smul_smul, ← hpoly]

/-- The `ℳ`-degree of `(X_{T\S})^k · m` exceeds that of `m` by `k · |S|`, exactly filling the gap
`k·|S| → k·|T|`. -/
private lemma smul_monomial_sdiff_pow_mem {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) {m : M} (hm : m ∈ ℳ (k * S.card)) :
    (monomial (A := A) (T \ S)) ^ k • m ∈ ℳ (k * T.card) := by
  have hmono : (monomial (A := A) (T \ S)) ^ k ∈ homSub A n (k * (T \ S).card) := by
    rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
    have h1 : (monomial (A := A) (T \ S)).IsHomogeneous (T \ S).card := by
      unfold monomial Var
      have := MvPolynomial.IsHomogeneous.prod (R := A) (T \ S)
        (fun i => MvPolynomial.X i) (fun _ => 1)
        (fun i _ => MvPolynomial.isHomogeneous_X A i)
      simpa using this
    have h2 := h1.pow k
    rwa [mul_comm] at h2
  have hsmul := SetLike.GradedSMul.smul_mem hmono hm
  have hcard : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card h
  have hcard' : k * (T \ S).card +ᵥ k * S.card = k * T.card := by
    rw [show k * (T \ S).card +ᵥ k * S.card = k * (T \ S).card + k * S.card from rfl,
      ← Nat.mul_add, hcard]
  rwa [hcard'] at hsmul

theorem resAt_degZero {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    ∀ x ∈ degZero ℳ S, resAt (M := M) h x ∈ degZero ℳ T := by
  intro x hx
  suffices hmap : Submodule.map ((resAt (A := A) (M := M) h).restrictScalars A) (degZero ℳ S) ≤
      degZero ℳ T by
    exact hmap (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [degZero, Submodule.map_iSup]
  refine iSup_le (fun k => ?_)
  intro y hy
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨m', hm', rfl⟩ := Submodule.mem_map.mp hm
  change resAt (A := A) (M := M) h
    (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m')) ∈ degZero ℳ T
  rw [resAt_divPow_eq h k m']
  rw [degZero]
  refine le_iSup (fun l => Submodule.map
    ((divPow (A := A) (M := M) T l).comp (toLoc (A := A) (M := M) T)) (ℳ (l * T.card))) k ?_
  exact Submodule.mem_map.mpr ⟨_, smul_monomial_sdiff_pow_mem h k hm', rfl⟩

end Work.DSCOH
