import Submission.Work.DSMap.Mix2

/-! # DSMap.Mix2Fix — positive-degree repair of the MIX2 node set (curric-46, 10-13)

DSM8m found two contract defects, both machine-checked
(`Submission/Work/DSM8m/M2p_refutation.lean`, `Main.lean`):
* `DSMap.Mix.area_M2'` is **FALSE**. Its root clause applies to the monic polynomial `F = 1` and forces
  `1 = 0` in `B`, contradicting faithful flatness over the nonzero ring `A/(p)`.
* `DSMap.Mix2.area_M8m` is **vacuous**: `F = 1` gives `AdjoinRoot 1 = 0`.
Repair: the root clause asks only for `0 < F.natDegree` (`area_M2pos`); M8m also yields
`0 < F.natDegree` (`area_M8mpos`; `F` is the minimal polynomial of a primitive element). M6G and
the assembly are re-proved below (`root_of_clause` handles the trivial-ring case), and
`area_MIX2pos` has exactly `area_MIX`'s type. Retired: `Mix.area_M2'`, `Mix2.area_M8m`,
`Mix2.area_M6G`, `Mix2.area_MIX2`. -/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DSMap.Mix2Fix
open DSMap DSMap.Mix DSMap.Mix2

universe a b c

/-- **M2pos** (André's flatness lemma, perfectoid form) with the corrected root clause. -/
theorem area_M2pos (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (P : PerfectoidData p A) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∀ F : Polynomial A, F.Monic → 0 < F.natDegree →
        ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := sorry

/-- **M8mpos**: `area_M8m` plus `0 < F.natDegree`. -/
theorem area_M8mpos (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    ∃ (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1)) (F : Polynomial A)
      (θ : Γ(X, chartCover i ⟨j⟩) →+*
        Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g))),
      g ∉ Ideal.span {(p : A)} ∧ IsClosedImmersion i ∧ i ≫ PSpace.toSpec A N = f ∧ F.Monic ∧
      0 < F.natDegree ∧
      θ.comp (phiU A X f (chartCover i ⟨j⟩)) =
        (algebraMap (AdjoinRoot F) _).comp (algebraMap A (AdjoinRoot F)) := sorry

/-- The root clause also covers degree-0 cases over the trivial ring. -/
theorem root_of_clause (p : ℕ) {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hcl : ∀ F : Polynomial A, F.Monic → 0 < F.natDegree →
      ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k)
    (F : Polynomial A) (hF : F.Monic) (hd : Nontrivial A → 0 < F.natDegree) :
    ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  by_cases h : Nontrivial A
  · exact hcl F hF (hd h)
  · rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : B) = 0 := by
      rw [← map_one (algebraMap A B), ← map_zero (algebraMap A B), Subsingleton.elim (1 : A) 0]
    have : Subsingleton B := subsingleton_of_zero_eq_one h1.symm
    exact ⟨fun _ => 0, Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem area_M6Gpos (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1))
    (F : Polynomial A)
    (θ : Γ(X, chartCover i ⟨j⟩) →+*
      Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g)))
    (hi : IsClosedImmersion i) (hif : i ≫ PSpace.toSpec A N = f) (hF : F.Monic)
    (hFd : 0 < F.natDegree)
    (hθ : θ.comp (phiU A X f (chartCover i ⟨j⟩)) =
      (algebraMap (AdjoinRoot F) _).comp (algebraMap A (AdjoinRoot F)))
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f (chartCover i) P ε)
    (D : Type a) [CommRing D] (QD : PerfectoidData p D) (ψ : A →+* D) (n : ℕ)
    (hdiv : ψ g ∣ (p : D) ^ n) :
    ∀ m k, ModSplit P ε ψ (Ideal.span {(p : D) ^ m}) (QD.ϖ k) := by
  intro m k
  obtain ⟨hP1, hP2, φ, -, hφ⟩ := hP
  -- 1. André on `D` for `F`: a root `r 0 ∈ W₁`
  obtain ⟨W₁, _, _, Q₁, hQ₁, hFF₁, hroot₁⟩ := area_M2pos p D QD
  obtain ⟨r, hr0, -⟩ := root_of_clause p hroot₁ (F.map ψ) (hF.map ψ)
    (fun h => by haveI := h; rw [hF.natDegree_map ψ]; exact hFd)
  let ψ₁ : A →+* W₁ := (algebraMap D W₁).comp ψ
  have hFr : F.eval₂ ψ₁ (r 0) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map] at hr0; exact hr0
  let L₀ : AdjoinRoot F →+* W₁ := AdjoinRoot.lift ψ₁ (r 0) hFr
  have hL₀ : ∀ x : A, L₀ (algebraMap A (AdjoinRoot F) x) = ψ₁ x := fun x => by
    rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.lift_of hFr
  have hu₁ : IsUnit (((algebraMap W₁ (Localization.Away (p : W₁))).comp L₀)
      (algebraMap A (AdjoinRoot F) ((p : A) * g))) := by
    rw [RingHom.comp_apply, hL₀, map_mul, map_mul, map_natCast]
    refine (IsLocalization.Away.algebraMap_isUnit _).mul ?_
    obtain ⟨y, hy⟩ := hdiv
    refine isUnit_of_dvd_unit ⟨algebraMap W₁ _ (algebraMap D W₁ y), ?_⟩
      ((IsLocalization.Away.algebraMap_isUnit (p : W₁)).pow n)
    change _ = algebraMap W₁ _ (algebraMap D W₁ (ψ g)) * _
    rw [← map_mul, ← map_mul, ← hy]
    simp
  let L₁ : Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g)) →+*
      Localization.Away (p : W₁) := IsLocalization.Away.lift _ hu₁
  let θ₁ := L₁.comp θ
  -- 2. homogeneous coordinates `t₁ ∈ W₁` of the point, normalised `t₁ j = ϖ₀^{pe}`
  obtain ⟨e, t₀, ht₀⟩ := exists_chart_gens p W₁ Q₁
    (fun k : ULift.{a} (Fin (N + 1)) => θ₁ (xiSec i j k.down))
  let t₁ : ULift.{a} (Fin (N + 1)) → W₁ := Function.update t₀ ⟨j⟩ (Q₁.ϖ 0 ^ (p * e))
  have ht₁j : t₁ ⟨j⟩ = Q₁.ϖ 0 ^ (p * e) := Function.update_self _ _ _
  -- 3. roots of the `t₁ k` in a second André extension `W₂`
  obtain ⟨W₂, _, _, Q₂, hQ₂, hFF₂, tr, htr0, htr⟩ := area_ROOTS p W₁ Q₁ t₁
  let ψ₂ : A →+* W₂ := (algebraMap W₁ W₂).comp ψ₁
  let t₂ : ULift.{a} (Fin (N + 1)) → W₂ := fun k => algebraMap W₁ W₂ (t₁ k)
  have hu₂ : IsUnit (((algebraMap W₂ (Localization.Away (p : W₂))).comp (algebraMap W₁ W₂))
      (p : W₁)) := by
    rw [RingHom.comp_apply, map_natCast]; exact IsLocalization.Away.algebraMap_isUnit _
  let L₂ : Localization.Away (p : W₁) →+* Localization.Away (p : W₂) :=
    IsLocalization.Away.lift _ hu₂
  have hL₂ : ∀ x : W₁, L₂ (algebraMap W₁ _ x) = algebraMap W₂ _ (algebraMap W₁ W₂ x) :=
    fun x => IsLocalization.Away.lift_eq _ hu₂ x
  let θ₂ := L₂.comp θ₁
  have hθ₂ : θ₂.comp (phiU A X f (chartCover i ⟨j⟩)) = (algebraMap W₂ _).comp ψ₂ := by
    ext x
    have := congrArg (fun φ => φ x) hθ
    simp only [RingHom.comp_apply] at this ⊢
    change L₂ (L₁ (θ _)) = _
    rw [this, IsLocalization.Away.lift_eq, RingHom.comp_apply, hL₀, hL₂]
    rfl
  have ht₂j : t₂ ⟨j⟩ = Q₂.ϖ 0 ^ (p * e) := by
    change algebraMap W₁ W₂ (t₁ ⟨j⟩) = _; rw [ht₁j, map_pow, hQ₂]
  have hθ₂k : ∀ k, k ≠ j → algebraMap W₂ (Localization.Away (p : W₂)) (t₂ ⟨k⟩) =
      algebraMap W₂ _ (t₂ ⟨j⟩) * θ₂ (xiSec i j k) := by
    intro k hk
    have hne : (⟨k⟩ : ULift.{a} (Fin (N + 1))) ≠ ⟨j⟩ := fun h => hk (congrArg ULift.down h)
    have h1 : t₁ ⟨k⟩ = t₀ ⟨k⟩ := Function.update_of_ne hne _ _
    change algebraMap W₂ _ (algebraMap W₁ W₂ (t₁ ⟨k⟩)) =
      algebraMap W₂ _ (algebraMap W₁ W₂ (t₁ ⟨j⟩)) * L₂ (θ₁ (xiSec i j k))
    rw [← hL₂, ← hL₂, ← map_mul, h1, ht₁j, ht₀ ⟨k⟩]
  -- 4. the chart chain map (SEC) and blowup almost splitting (M5d) over `W₂`
  obtain ⟨χ, hχ⟩ := area_SEC p A X f N i hi hif j W₂ Q₂.torsionFree ψ₂ θ₂ hθ₂ t₂
    (by rw [ht₂j]; exact isUnit_varpi_pow p Q₂ _) hθ₂k
  have h5 := area_M5d p W₂ Q₂ t₂ tr htr0 htr ⟨j⟩ (p * e) ht₂j ψ₂ P hP1 ε hP2 (φ ≫ χ) (by
    have hφ' : ε ≫ φ.f 0 = coaug0 A X f (chartCover i) ≫
        ((cech A X f (chartCover i)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv := by
      apply (Iso.eq_comp_inv _).2
      exact (Category.assoc _ _ _).trans hφ
    rw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ε, hφ']
    exact (Category.assoc _ _ _).trans hχ) m k
  -- 5. descend `W₂ → W₁ → D` (AM2 + FFP)
  have h6 : ModSplit P ε ψ₁ (Ideal.span {(p : W₁) ^ m}) (Q₁.ϖ k) := by
    refine modSplit_descent_p p P hP1 ε hP2 ψ₁ Q₁.torsionFree Q₂.torsionFree hFF₂ m _ ?_
    rw [← hQ₂]; exact h5
  refine modSplit_descent_p p P hP1 ε hP2 ψ QD.torsionFree Q₁.torsionFree hFF₁ m _ ?_
  rw [← hQ₁]; exact h6

theorem area_MIX2pos (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f)
    (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := by
  have : IsDomain A := area_REG A
  obtain ⟨g, N, i, j, F, θ, hgp, hi, hif, hF, hFd, hθ⟩ := area_M8mpos A p X f hs hg hp
  obtain ⟨P, ε, hP⟩ := area_MX0U A X f hp (chartCover i) (chartCover_affine i hi)
    (chartCover_iSup i)
  refine area_MX0bU A X f (chartCover i) (chartCover_affine i hi) (chartCover_iSup i) P ε hP ?_
  obtain ⟨B₁, _, _, P₁, hFF₁⟩ := area_M1' A p
  obtain ⟨B₂, _, _, Q₂, -, hFF₁₂, hroots⟩ := area_M2pos p B₁ P₁
  let _ : Algebra A B₂ := ((algebraMap B₁ B₂).comp (algebraMap A B₁)).toAlgebra
  have : IsScalarTower A B₁ B₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.FaithfullyFlat A B₂ := area_M2b A p B₁ B₂ Q₂ hFF₁₂
  obtain ⟨r, hr0, hr⟩ := root_of_clause p hroots
    (Polynomial.X - Polynomial.C (algebraMap A B₁ g)) (Polynomial.monic_X_sub_C _)
    (fun h => by haveI := h; rw [Polynomial.natDegree_X_sub_C]; exact Nat.one_pos)
  have hr0' : r 0 = algebraMap A B₂ g := by
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hr0
    rw [hr0]; rfl
  obtain ⟨D, _, _, QD, tr, hQD, hdiv, hq⟩ := area_M4p p B₂ Q₂ r hr
  refine area_M7p A p P ε hP.1 hP.2.1 B₂ Q₂ g hgp r hr0' hr D QD tr hQD hq ?_
  intro n m k
  refine area_M6Gpos p A X f g N i j F θ hi hif hF hFd hθ P ε hP (D n) (QD n) _ n ?_ m k
  obtain ⟨y, hy⟩ := hdiv n
  refine ⟨y, ?_⟩
  rw [← hy, RingHom.comp_apply, ← hr0']

end DSMap.Mix2Fix

/-- the repaired assembly has exactly `area_MIX`'s statement -/
example : @DSMap.Mix2Fix.area_MIX2pos = @DSMap.area_MIX := rfl
