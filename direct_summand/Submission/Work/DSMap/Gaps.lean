import Submission.Work.DSMap.Mix2Fix

/-!
# direct_summand — node statements for the three gaps of 2026-10-13 (curric-46 design)

Design notes: `cbc/direct_summand_gaps_1013.md`.  Box copy: `~/scratch-c46/dsdesign/Gaps.lean`.
LEAD FILE (frozen, read-only). Imports only the lead files. Reviewed: cbc/direct_summand_gaps_1013_REVIEW.md.

* GAP 1 (EQP): new nodes `area_GOOD`, `eqp_cech_torsion`, `eqp_perfModel`, `area_GAMMA`,
  `modSplit_twist`, `modSplit_one_of_roots`, `area_KUNZ`.  `area_EQP_gaps` is PROVED from them plus
  the frozen nodes `area_REG`, `area_MX0U`, `area_MX0bU`, `chartCover_affine`, `chartCover_iSup`,
  `modSplit_of_almostAcyc` (AMR, already proved by DSAMR) and DSEQP's `faithfullyFlat_pPerfection`.
  An `rfl` check shows it has exactly the type of `DSMap.area_EQP`.
* GAP 2 (shared, Cohen-free): `area_SER`, `area_GRPOLY`, `area_NORM`; and G4b's `gonf_residue`.
* GAP 3: `area_M2pos1` (single-polynomial André lemma) and the analytic node `area_AAL`.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DSMap.Gaps
open DSMap DSMap.Mix DSMap.Mix2

universe a b c

/-! ## GAP 1: equal characteristic `p` -/

/-- **GOOD** (characteristic-free good coordinate; also the first half of M8m): `f⁻¹ D(g)` lies
in one chart `X ∩ D₊(x_j)` of a projective embedding, for some `g ≠ 0`. -/
theorem area_GOOD (A : Type a) [CommRing A] [IsDomain A] [IsNoetherianRing A] (X : Scheme.{a})
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    ∃ (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1)),
      g ≠ 0 ∧ IsClosedImmersion i ∧ i ≫ PSpace.toSpec A N = f ∧
      f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens) ≤ chartCover i ⟨j⟩ := sorry

/-- **LOC** higher Čech cohomology is killed by a power of `g` when `f⁻¹ D(g)` lies in one member
of the cover (after inverting `g` the cover contains the whole space, so the localized Čech complex
is contractible; finite generation of `Hᵠ` comes from the finite free model). -/
theorem eqp_cech_torsion (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsSeparated f] {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (g : A) (j : ι)
    (hgood : f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens) ≤ U j)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε) (q : ℕ) :
    ∃ N : ℕ, ∀ z : (cech A X f U).X (q + 1), ((cech A X f U).d (q + 1) (q + 2)).hom z = 0 →
      ∃ y : (cech A X f U).X q, ((cech A X f U).d q (q + 1)).hom y = g ^ N • z := sorry

/-- **PERF** the Čech complex of the *perfected* structure presheaf, over `W = Γ(X,⊤)_perf`, is
`g^{1/p^∞}`-almost acyclic, and the model `P` maps to it compatibly with the units.
(Construction: `K := Č(U; U' ↦ Γ(X,U')_perf)` with the perfection defined for rings with `p = 0`,
so that empty intersections are allowed; `ρ := φ ≫ (level-0 map)`.) -/
theorem eqp_perfModel (A : Type a) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsSeparated f] {ι : Type a}
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (g : A)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε)
    (htors : ∀ q : ℕ, ∃ N : ℕ, ∀ z : (cech A X f U).X (q + 1),
      ((cech A X f U).d (q + 1) (q + 2)).hom z = 0 →
        ∃ y : (cech A X f U).X q, ((cech A X f U).d q (q + 1)).hom y = g ^ N • z) :
    ∃ (W : Type a) (_ : CommRing W) (_ : CharP W p) (_ : PerfectRing W p) (ψW : Γ(X, ⊤) →+* W)
      (K : CochainComplex (ModuleCat.{a} W) ℕ) (eK : ModuleCat.of W W ⟶ K.X 0)
      (ρ : P ⟶ ((ModuleCat.restrictScalars (ψW.comp (phi A X f))).mapHomologicalComplex _).obj
        (K.extend ComplexShape.embeddingUpNat)),
      Function.Injective ψW ∧
      (∀ w : W, ∃ (n : ℕ) (x : Γ(X, ⊤)), w = ((frobeniusEquiv W p).symm^[n]) (ψW x)) ∧
      AlmostAcyc (fun k => ((frobeniusEquiv W p).symm^[k]) (ψW (phi A X f g))) ⊥ K eK ∧
      ε ≫ ρ.f 0 ≫ (ModuleCat.restrictScalars (ψW.comp (phi A X f))).map
          (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        unitA (ψW.comp (phi A X f)) ≫ (ModuleCat.restrictScalars (ψW.comp (phi A X f))).map eK :=
  sorry

/-- **GAMMA** `Γ(X,𝒪)` admits an `A`-linear functional nonzero at `1` (finite by COH, torsion-free
because `f` is dominant; then DSEQP's `evalIdeal_ne_bot`). -/
theorem area_GAMMA (A : Type a) [CommRing A] [IsDomain A] [IsNoetherianRing A] (X : Scheme.{a})
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hp : IsProjOver A f) :
    letI := (phi A X f).toAlgebra
    ∃ φ : Γ(X, ⊤) →ₗ[A] A, φ 1 ≠ 0 := sorry

/-- **TWIST** (replaces "almost purity for `Č⁰`"): an almost splitting over the perfection `W` of
`B` with value `c^{1/p^k}` gives one over any perfect `A`-algebra `S` with value
`(c·φ(1))^{1/p^k}`, for any `A`-linear `φ : B → A`.  (Restrict to `P⁰`; the finitely generated
image lies in the level `W_n = ψW(B)^{1/p^n}`; compose with `x^{1/p^n} ↦ φ(x)^{1/p^n}`.) -/
theorem modSplit_twist {A B W S : Type a} [CommRing A] [CommRing B] [Algebra A B] [CommRing W]
    [CommRing S] (p : ℕ) [Fact p.Prime] [CharP W p] [PerfectRing W p] [CharP S p]
    [PerfectRing S p] (ψW : B →+* W) (hψW : Function.Injective ψW)
    (hW : ∀ w : W, ∃ (n : ℕ) (x : B), w = ((frobeniusEquiv W p).symm^[n]) (ψW x))
    (ψS : A →+* S) (φ : B →ₗ[A] A) (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0) (c : A) (k : ℕ)
    (h : ModSplit P ε (ψW.comp (algebraMap A B)) ⊥
      (((frobeniusEquiv W p).symm^[k]) (ψW (algebraMap A B c)))) :
    ModSplit P ε ψS ⊥ (((frobeniusEquiv S p).symm^[k]) (ψS (c * φ 1))) := sorry

/-- **KRULL-P** (DSEQP's `one_mem_of_forall_pthRoot_mem` at model level): almost splittings with
values a compatible system of roots of `d ≠ 0`, over a faithfully flat `S`, give an honest one.
(The value set over `S` is `I_P·S` because `coker(P⁻¹ → P⁰)` is finitely presented.) -/
theorem modSplit_one_of_roots (A S : Type a) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S] (p : ℕ)
    [Fact p.Prime] (P : CochainComplex (ModuleCat.{a} A) ℤ) (hP : IsBddFinFree P)
    (ε : ModuleCat.of A A ⟶ P.X 0) (d : A) (hd : d ≠ 0) (r : ℕ → S)
    (hr : ∀ e, r e ^ (p ^ e) = algebraMap A S d)
    (h : ∀ e, ModSplit P ε (algebraMap A S) ⊥ (r e)) :
    ModSplit P ε (RingHom.id A) ⊥ 1 := sorry

/-- **KUNZ** for complete regular local rings with perfect residue field (SER gives
`A = Σ_{α<p} A^p x^α`; GRPOLY gives independence of the `x^α` over `A^p`). -/
theorem area_KUNZ (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharP A p] : (frobenius A p).Flat := sorry

-- The EQP assembly (`area_EQP_gaps`, proved from these nodes) is DSEQP's plan; see
-- cbc/direct_summand_gaps_1013.lean and the DSEQP brief.


/-! ## GAP 2: shared Cohen-free inputs -/

/-- **SER** (series lemma; Frobenius surjectivity modulo `p` after adjoining `p`-th roots of a
generating set of `𝔪`).  `R` complete Noetherian local, residue field perfect (elementary form
`hperf`), `p ∈ 𝔪`, `z` generating `𝔪`, `R' = R[Z]/(Z_i^p - z_i)`.  Every `a ∈ R` is `b^p + p·h`,
and `h ∈ (Z)` when `a ∈ 𝔪`.  (Characteristic `p`: `a = Σ_{α<p} b_α^p x^α`.) -/
theorem area_SER (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hpm : (p : R) ∈ maximalIdeal R) (hperf : ∀ x : R, ∃ μ : R, x - μ ^ p ∈ maximalIdeal R)
    {d : ℕ} (z : Fin d → R) (hz : Ideal.span (Set.range z) = maximalIdeal R) (x : R) :
    ∃ b h : MvPolynomial (Fin d) R ⧸
        Ideal.span (Set.range fun i => MvPolynomial.X i ^ p - MvPolynomial.C (z i)),
      b ^ p = algebraMap R _ x + (p : R) • h ∧
      (x ∈ maximalIdeal R → h ∈ Ideal.span (Set.range fun i => Ideal.Quotient.mk _
        (MvPolynomial.X i))) := sorry

/-- **GRPOLY** (Matsumura Thm 16.2 for a regular system of parameters: `gr_𝔪 A ≅ k[X]`):
a homogeneous form of degree `n` whose value lies in `𝔪^{n+1}` has all coefficients in `𝔪`. -/
theorem area_GRPOLY (A : Type a) [CommRing A] [IsRegularLocalRing A] {d : ℕ} (x : Fin d → A)
    (hx : Ideal.span (Set.range x) = maximalIdeal A) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (F : MvPolynomial (Fin d) A) (n : ℕ) (hF : F.IsHomogeneous n)
    (h : MvPolynomial.eval x F ∈ maximalIdeal A ^ (n + 1)) :
    ∀ s, F.coeff s ∈ maximalIdeal A := sorry

/-- **NORM** regular local rings are integrally closed (from GRPOLY: initial forms are
multiplicative and `k[X]` is a UFD; successive approximation + Krull intersection). -/
theorem area_NORM (A : Type a) [CommRing A] [IsRegularLocalRing A] : IsIntegrallyClosed A := sorry

/-- **G4b residue enlargement** (no Cohen, no Noetherianity of `B`): p-basis tower for the
perfect closure, then one localisation of `⊗_α B₁[T]/(F_α)` for the separable closure. -/
theorem gonf_residue (R : Type a) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (B : Type a) (_ : CommRing B) (_ : IsLocalRing B) (ψ : R →+* B),
      ψ.Flat ∧ (maximalIdeal R).map ψ = maximalIdeal B ∧ IsAlgClosed (ResidueField B) := sorry

/-! ## GAP 3: André's lemma -/

/-- **M2pos1** single-polynomial form of `Mix2Fix.area_M2pos` (all consumers use one polynomial at
a time: MIX2pos `X - g`, M6Gpos `F`, ROOTS `X - t_i`). -/
theorem area_M2pos1 (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (P : PerfectoidData p A)
    (F : Polynomial A) (hF : F.Monic) (hFd : 0 < F.natDegree) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := sorry

/-- **AAL** (the only analytic input of GAP 3; CS `approx-lem` + `nilp-lem`): every element `P` of
a perfectoid `R` is close to an element `Q` with compatible `p`-power roots, in the algebraic form
used by CS: `(P - Q)^{p^t} ∈ (ϖ)`, and a `p`-power of `(P - Q)/ϖ^m` lies in `ϖ·R[P/ϖ^m]` and in
`ϖ·R[Q/ϖ^m]` inside `R[1/ϖ]`. -/
theorem area_AAL (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] (QR : PerfectoidData p R)
    (P : R) (m : ℕ) :
    ∃ (Qr : ℕ → R) (t e : ℕ), (∀ j, Qr (j + 1) ^ p = Qr j) ∧
      (P - Qr 0) ^ (p ^ t) ∈ Ideal.span {QR.ϖ 0} ∧
      let L := Localization.Away (QR.ϖ 0)
      let u : L := IsLocalization.Away.invSelf (QR.ϖ 0) ^ m
      (algebraMap R L (P - Qr 0) * u) ^ (p ^ e) ∈
          (Algebra.adjoin R {algebraMap R L P * u}).toSubmodule.map
            (LinearMap.mulLeft R (algebraMap R L (QR.ϖ 0))) ∧
      (algebraMap R L (P - Qr 0) * u) ^ (p ^ e) ∈
          (Algebra.adjoin R {algebraMap R L (Qr 0) * u}).toSubmodule.map
            (LinearMap.mulLeft R (algebraMap R L (QR.ϖ 0))) := sorry


/-! ## Consumers rebased on `area_M2pos1` (mechanical; curric-46 lead) -/

theorem m2pos1_any (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (P : PerfectoidData p A)
    (F : Polynomial A) (hF : F.Monic) (hd : Nontrivial A → 0 < F.natDegree) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  by_cases h : Nontrivial A
  · exact area_M2pos1 p A P F hF (hd h)
  · rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (A ⧸ Ideal.span {(p : A)}) := Ideal.Quotient.mk_surjective.subsingleton
    have : Subsingleton (A ⧸ (Ideal.span {(p : A)}).map (algebraMap A A)) :=
      Ideal.Quotient.mk_surjective.subsingleton
    refine ⟨A, inferInstance, Algebra.id A, P, fun _ => rfl, ?_, fun _ => 0,
      Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    exact { toFlat := inferInstance,
            submodule_ne_top := fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim }

theorem area_M6Gpos1 (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (X : Scheme.{a})
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
  obtain ⟨W₁, _, _, Q₁, hQ₁, hFF₁, r, hr0, -⟩ := m2pos1_any p D QD (F.map ψ) (hF.map ψ)
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

theorem area_MIX2pos1 (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f)
    (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := by
  have : IsDomain A := area_REG A
  obtain ⟨g, N, i, j, F, θ, hgp, hi, hif, hF, hFd, hθ⟩ := Mix2Fix.area_M8mpos A p X f hs hg hp
  obtain ⟨P, ε, hP⟩ := area_MX0U A X f hp (chartCover i) (chartCover_affine i hi)
    (chartCover_iSup i)
  refine area_MX0bU A X f (chartCover i) (chartCover_affine i hi) (chartCover_iSup i) P ε hP ?_
  obtain ⟨B₁, _, _, P₁, hFF₁⟩ := area_M1' A p
  obtain ⟨B₂, _, _, Q₂, -, hFF₁₂, r, hr0, hr⟩ := m2pos1_any p B₁ P₁
    (Polynomial.X - Polynomial.C (algebraMap A B₁ g)) (Polynomial.monic_X_sub_C _)
    (fun h => by haveI := h; rw [Polynomial.natDegree_X_sub_C]; exact Nat.one_pos)
  let _ : Algebra A B₂ := ((algebraMap B₁ B₂).comp (algebraMap A B₁)).toAlgebra
  have : IsScalarTower A B₁ B₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.FaithfullyFlat A B₂ := area_M2b A p B₁ B₂ Q₂ hFF₁₂
  have hr0' : r 0 = algebraMap A B₂ g := by
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hr0
    rw [hr0]; rfl
  obtain ⟨D, _, _, QD, tr, hQD, hdiv, hq⟩ := area_M4p p B₂ Q₂ r hr
  refine area_M7p A p P ε hP.1 hP.2.1 B₂ Q₂ g hgp r hr0' hr D QD tr hQD hq ?_
  intro n m k
  refine area_M6Gpos1 p A X f g N i j F θ hi hif hF hFd hθ P ε hP (D n) (QD n) _ n ?_ m k
  obtain ⟨y, hy⟩ := hdiv n
  refine ⟨y, ?_⟩
  rw [← hy, RingHom.comp_apply, ← hr0']

end DSMap.Gaps

/-- the rebased MIX assembly has exactly `area_MIX`'s statement -/
example : @DSMap.Gaps.area_MIX2pos1 = @DSMap.area_MIX := rfl