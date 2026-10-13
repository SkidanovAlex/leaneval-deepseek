import Submission.Work.DSMap.Map

/-! LEAD-OWNED (curric-46, 2026-10-13): mixed-characteristic area interfaces from cbc/direct_summand_mix_design.md
and its REVIEW (copies in sources/dsmap/). Do not edit. KNOWN DEFECTIVE / NOT TO BE DISPATCHED until restated:
area_M4 and IsQRET (review: forces every PerfectoidData ring to be zero — needs the pro form with uniform c),
area_M7 (to be restated against the pro IsQRET), area_M3_fixed, area_M3plus, area_M5_fixed (superseded),
area_M8 (needs the monogenic clause), IsFinFreeModel/area_MX0 (to be parametrised by the cover). -/
/-!
# direct_summand — MIX subtree design (curric-46 research design, 2026-10-13)

Restated (true) MIX sub-area interfaces + a compiled assembly of `area_MIX`'s statement.
Design notes: `cbc/direct_summand_mix_design.md`.  Imports the frozen lead file read-only.
Box copy: `18.221:~/scratch-c46-dsmix/DSMixDesign.lean` (compiled with `lake env lean` from the
workspace root; 0 errors; `area_MIX_assembly` uses only the sorried interfaces below).
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DSMap.Mix

universe a b c

/-! ## V-MIX: new MIX vocabulary (derived-category free) -/

/-- bounded-above complex of finite free modules (a K-projective model). -/
def IsBddFinFree {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ) : Prop :=
  (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
    ∃ N : ℤ, ∀ i, N < i → Limits.IsZero (P.X i)

/-- `(P, ε)` is a finite free model of `RΓ(X, 𝒪)` with its unit: a quasi-isomorphism to the Čech
complex of some finite affine cover, carrying `ε` to the Čech coaugmentation.
(No derived-category instances: universe-independent.) -/
def IsFinFreeModel (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0) : Prop :=
  IsBddFinFree P ∧ (∀ k, ε ≫ P.d 0 k = 0) ∧
    ∃ (ι : Type a) (_ : Finite ι) (U : ι → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
      (_ : ⨆ i, U i = ⊤) (φ : P ⟶ cechZ A X f U), QuasiIso φ ∧
      ε ≫ φ.f 0 ≫ ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        coaug0 A X f U

/-- Splitting of `ε : A → P⁰` after base change along `ψ : A → D`, modulo `I`, with value `c`:
a `D`-linear `s : D ⊗ P⁰ → D/I` killing `d⁻¹` with `s(1 ⊗ ε 1) = c`.  For `P` bounded-above finite
free this is exactly a map `P ⊗ D → (D/I)[0]` in `D(D)` sending the unit to `c`. -/
def ModSplit {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D)
    (c : D) : Prop :=
  letI := ψ.toAlgebra
  ∃ s : TensorProduct A D (P.X 0) →ₗ[D] D ⧸ I,
    (∀ y, s ((P.d (-1) 0).hom.baseChange D y) = 0) ∧
      s ((1 : D) ⊗ₜ[A] ε.hom 1) = Ideal.Quotient.mk I c

/-- iterated transition maps of a tower `D (n+1) → D n`. -/
def iterTr {B : Type a} [CommRing B] {D : ℕ → Type a} [∀ n, CommRing (D n)]
    [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n) (n : ℕ) :
    ∀ c : ℕ, D (n + c) →ₐ[B] D n
  | 0 => AlgHom.id B (D n)
  | c + 1 => (iterTr tr n c).comp (tr (n + c))

/-- Bhatt Thm 3.1 + Rmk 3.2 (quantitative Riemann extension), algebraic form: for every `m`, the
pro-system `{B/pᵐ → Dₙ/pᵐ}ₙ` is an almost-pro-isomorphism w.r.t. `(ϖ·g)^{1/p^∞}`:
kernels killed by `ϖ_k g_k`; cokernels uniformly almost-pro-zero. -/
def IsQRET (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B) (D : ℕ → Type a)
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n) : Prop :=
  ∀ m : ℕ,
    (∀ n k (x : B), algebraMap B (D n) x ∈ Ideal.span {((p : D n)) ^ m} →
        ϖ k * gr k * x ∈ Ideal.span {(p : B) ^ m}) ∧
    (∀ k, ∃ c : ℕ, ∀ n (y : D (n + c)), ∃ x : B,
        algebraMap B (D n) (ϖ k * gr k) * iterTr tr n c y - algebraMap B (D n) x ∈
          Ideal.span {(p : D n) ^ m})

/-! ## Interfaces used by the assembly -/

/-- **MX0** (F1 + COH + Noetherian pseudo-coherence): a projective `X` over Noetherian `A` has a
finite free model of `RΓ(X,𝒪)`. Shared with G4a. -/
theorem area_MX0_model (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      IsFinFreeModel A X f P ε := sorry

/-- **MX0b** bridge (F1): an honest splitting of a model gives `DSplit` (all instance choices). -/
theorem area_MX0b_bridge (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsProper f] (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModel A X f P ε) (h : ModSplit P ε (RingHom.id A) ⊥ 1) :
    DSplit.{a, b, c} A X f := sorry

/-- **M8** generic étaleness + good coordinate: `g ∉ (p)` with `X` finite étale over `D(pg)` and a
projective embedding whose coordinate `x_j` is invertible on `X_{D(pg)}` (this makes `X` the blowup
of `Γ(X,𝒪)` in an ideal containing `(pg)^e`, used by the M6N design). -/
theorem area_M8 (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    ∃ (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1)),
      g ∉ Ideal.span {(p : A)} ∧ IsClosedImmersion i ∧ i ≫ PSpace.toSpec A N = f ∧
      f ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens) ≤
        i ⁻¹ᵁ Proj.basicOpen (PGr A N) (MvPolynomial.X j) ∧
      IsFinite (f ∣_ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens)) ∧
      Etale (f ∣_ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens)) := sorry

/-- **M1'** (Bhatt Prop 4.2, generalized-perfectoid form; no almost purity): a faithfully flat
perfectoid cover. Unramified: `W⟦x⟧ → (W⟦x⟧[p^{1/p^∞}, x^{1/p^∞}])^`; ramified: Bhatt's `A'`
(`ϖ := (ḡ^{1/p^∞})♯`, `ϖ^p = p·unit`). -/
theorem area_M1' (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (_ : PerfectoidData p B),
      Module.FaithfullyFlat A B := sorry

/-- **M2'** André's lemma, Česnavičius–Scholze form (CS Thm `Andre-lem`, completed):
`A/p → B/pB` faithfully flat, `B` perfectoid with the same `ϖ`, and every monic polynomial over `A`
has a root in `B` with compatible `p`-power roots. (Fixes the vacuous M2: `B = 0` violates FF.) -/
theorem area_M2' (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (P : PerfectoidData p A) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∀ F : Polynomial A, F.Monic →
        ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := sorry

/-- **M2b** (Bhatt Prop 4.1 + composition): faithful flatness of the composite cover. -/
theorem area_M2b (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (B₁ B₂ : Type a) [CommRing B₁] [CommRing B₂] [Algebra A B₁]
    [Algebra B₁ B₂] [Algebra A B₂] [IsScalarTower A B₁ B₂] [Module.FaithfullyFlat A B₁]
    (Q : PerfectoidData p B₂)
    (h : Module.FaithfullyFlat (B₁ ⧸ Ideal.span {(p : B₁)})
      (B₂ ⧸ (Ideal.span {(p : B₁)}).map (algebraMap B₁ B₂))) :
    Module.FaithfullyFlat A B₂ := sorry

/-- **M4** quantitative Riemann extension (Bhatt §3, with `t := ϖ₀`): the tower
`Dₙ = B⟨ϖ₀^{pn}/g⟩` (perfectoid rational localizations, algebraic presentation of Scholze
Lemma 6.4). -/
theorem area_M4 (p : ℕ) [Fact p.Prime] (B : Type a) [CommRing B] (Q : PerfectoidData p B)
    (gr : ℕ → B) (hgr : ∀ k, gr (k + 1) ^ p = gr k) :
    ∃ (D : ℕ → Type a) (_ : ∀ n, CommRing (D n)) (_ : ∀ n, Algebra B (D n))
      (QD : ∀ n, PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n),
      (∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)) ∧
      (∀ n, ∃ y : D n, algebraMap B (D n) (gr 0) * y = (p : D n) ^ n) ∧
      IsQRET p B Q.ϖ gr D tr := sorry

/-- **M6N** (Bhatt Prop 5.2, Noetherian-origin form, model level): for `X` over Noetherian `A`,
finite étale over `D(pg)` with a good coordinate, and any perfectoid `D` with `g ∣ pⁿ`, the
model unit `D/pᵐ → P ⊗ D/pᵐ` is almost split.  Route: André descent + M3⁺ (almost purity) +
M5′ (blowup acyclicity, review §4(b) algebraic route); or Bhatt's route via `area_M6_fixed`. -/
theorem area_M6N (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] [IsNoetherianRing A]
    [IsDomain A] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f]
    (hs : Function.Surjective f) (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1))
    (hi : IsClosedImmersion i) (hif : i ≫ PSpace.toSpec A N = f)
    (hgood : f ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens) ≤
        i ⁻¹ᵁ Proj.basicOpen (PGr A N) (MvPolynomial.X j))
    (hfin : IsFinite (f ∣_ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens)))
    (het : Etale (f ∣_ (PrimeSpectrum.basicOpen ((p : A) * g) : (Spec (.of A)).Opens)))
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModel A X f P ε) (D : Type a) [CommRing D] (QD : PerfectoidData p D)
    (ψ : A →+* D) (n : ℕ) (hdiv : ψ g ∣ (p : D) ^ n) :
    ∀ m k, ModSplit P ε ψ (Ideal.span {(p : D) ^ m}) (QD.ϖ k) := sorry

/-- **M7** (Bhatt Thm 4.4/5.1 assembly, model level): faithfully flat perfectoid cover with roots
of `g`, the RET tower, and almost splittings mod `pᵐ` over every `Dₙ` ⇒ honest splitting over `A`
(obstruction class; `lim¹` via Artin–Rees; Krull's intersection theorem). -/
theorem area_M7 (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hP : IsBddFinFree P) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (B : Type a) [CommRing B] [Algebra A B] (Q : PerfectoidData p B) [Module.FaithfullyFlat A B]
    (g : A) (hg : g ∉ Ideal.span {(p : A)}) (gr : ℕ → B) (hgr0 : gr 0 = algebraMap A B g)
    (hgr : ∀ k, gr (k + 1) ^ p = gr k) (D : ℕ → Type a) [∀ n, CommRing (D n)]
    [∀ n, Algebra B (D n)] (QD : ∀ n, PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (hQD : ∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)) (hq : IsQRET p B Q.ϖ gr D tr)
    (hsplit : ∀ n m k, ModSplit P ε ((algebraMap B (D n)).comp (algebraMap A B))
      (Ideal.span {(p : D n) ^ m}) ((QD n).ϖ k)) :
    ModSplit P ε (RingHom.id A) ⊥ 1 := sorry

/-! ## Assembly (proved from the interfaces) -/

theorem area_MIX_assembly (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f)
    (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := by
  have : IsDomain A := area_REG A
  obtain ⟨P, ε, hP⟩ := area_MX0_model A X f hp
  refine area_MX0b_bridge A X f P ε hP ?_
  obtain ⟨g, N, i, j, hgp, hi, hif, hgood, hfin, het⟩ := area_M8 A p X f hs hg hp
  obtain ⟨B₁, _, _, P₁, hFF₁⟩ := area_M1' A p
  obtain ⟨B₂, _, _, Q₂, -, hFF₁₂, hroots⟩ := area_M2' p B₁ P₁
  letI : Algebra A B₂ := ((algebraMap B₁ B₂).comp (algebraMap A B₁)).toAlgebra
  haveI : IsScalarTower A B₁ B₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.FaithfullyFlat A B₂ := area_M2b A p B₁ B₂ Q₂ hFF₁₂
  obtain ⟨r, hr0, hr⟩ := hroots (Polynomial.X - Polynomial.C (algebraMap A B₁ g))
    (Polynomial.monic_X_sub_C _)
  have hr0' : r 0 = algebraMap A B₂ g := by
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hr0
    rw [hr0]; rfl
  obtain ⟨D, _, _, QD, tr, hQD, hdiv, hq⟩ := area_M4 p B₂ Q₂ r hr
  refine area_M7 A p P ε hP.1 hP.2.1 B₂ Q₂ g hgp r hr0' hr D QD tr hQD hq ?_
  intro n m k
  refine area_M6N p A X f hs g N i j hi hif hgood hfin het P ε hP (D n) (QD n) _ n ?_ m k
  obtain ⟨y, hy⟩ := hdiv n
  refine ⟨y, ?_⟩
  rw [← hy, RingHom.comp_apply, ← hr0']

/-! ## Restated MIX stubs of the reviewed map (true versions; feed M6N's proof) -/

/-- **M3** fixed (adds faithfulness; `S = 0` was a counterexample). -/
theorem area_M3_fixed (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (S : Type a) [CommRing S] [Algebra (Localization.Away (p : A)) S]
    [Algebra A S] [IsScalarTower A (Localization.Away (p : A)) S]
    [Algebra.Etale (Localization.Away (p : A)) S] [Module.Finite (Localization.Away (p : A)) S]
    (hinj : Function.Injective (algebraMap (Localization.Away (p : A)) S)) :
    ∀ k, ∃ σ : integralClosure A S →ₗ[A] A, σ 1 = P.ϖ k := sorry

/-- **M3⁺** almost purity, output form needed by M6 (Scholze 7.9(i)+(iii)): a perfectoid `C`
receiving the integral closure, equal to it after inverting `p`, almost split over `A`. -/
theorem area_M3plus (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (S : Type a) [CommRing S] [Algebra (Localization.Away (p : A)) S]
    [Algebra A S] [IsScalarTower A (Localization.Away (p : A)) S]
    [Algebra.Etale (Localization.Away (p : A)) S] [Module.Finite (Localization.Away (p : A)) S]
    (hinj : Function.Injective (algebraMap (Localization.Away (p : A)) S)) :
    ∃ (C : Type a) (_ : CommRing C) (_ : Algebra A C) (Q : PerfectoidData p C)
      (φ : integralClosure A S →ₐ[A] C),
      (∀ k, Q.ϖ k = algebraMap A C (P.ϖ k)) ∧ Function.Injective φ ∧
      (∀ x : C, ∃ (e : ℕ) (y : integralClosure A S), (p : C) ^ e * x = φ y) ∧
      ∀ k, ∃ σ : C →ₗ[A] A, σ 1 = P.ϖ k := sorry

/-- **M5** fixed (adds finite presentation, needed for admissible-blowup domination).
Bhatt route only (research gap 1). -/
theorem area_M5_fixed (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (Y : Scheme.{a}) (f : Y ⟶ Spec (.of A)) [IsProper f]
    [LocallyOfFinitePresentation f]
    [IsIso (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens))] :
    AlmostDSplit.{a, b, c} A P.ϖ Y f := sorry

/-- **M6** fixed (adds surjectivity — `Y = ∅` was a counterexample — and finite presentation). -/
theorem area_M6_fixed (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (Y : Scheme.{a}) (f : Y ⟶ Spec (.of A)) [IsProper f]
    [LocallyOfFinitePresentation f] (hs : Function.Surjective f)
    (hfin : IsFinite (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens)))
    (het : Etale (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens))) :
    AlmostDSplit.{a, b, c} A P.ϖ Y f := sorry

end DSMap.Mix

/-! # Foundations (almost mathematics + perfectoid basics), exact node statements -/

namespace DSMap.Mix
universe a

/-! ## AM: almost mathematics at the model level -/

/-- **AM1** (proved) a splitting with value `c` gives one with value `c * d`. -/
theorem modSplit_mul {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D)
    (c d : D) (h : ModSplit P ε ψ I c) : ModSplit P ε ψ I (c * d) := by
  letI := ψ.toAlgebra
  obtain ⟨s, hs, hse⟩ := h
  refine ⟨(Ideal.Quotient.mk I d) • s, fun y => by simp [hs y], ?_⟩
  simp only [LinearMap.smul_apply, hse, smul_eq_mul, map_mul, mul_comm]

/-- **AM2** (`ModSplit` descends along maps that are faithfully flat modulo `I`): the obstruction class
lives in `H¹ Hom(cone(ε) ⊗ D, D/I)`, which commutes with flat base change because `P` is
degreewise finite free, and faithful flatness detects `c·α = 0`. -/
theorem modSplit_descent {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D) [Algebra D D'] (I : Ideal D)
    (hff : Module.FaithfullyFlat (D ⧸ I) (D' ⧸ I.map (algebraMap D D'))) (c : D)
    (h : ModSplit P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D')) (algebraMap D D' c)) :
    ModSplit P ε ψ I c := sorry

/-- **AM3** composition with an almost retraction of the coefficients: a `D`-linear
`σ : D' → D` with `σ 1 = c'`, compatible with `I`, transports splittings from `D'` to `D`. -/
theorem modSplit_of_retraction {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D)
    [Algebra D D'] (I : Ideal D) (σ : D' →ₗ[D] D) (c c' : D)
    (hσI : ∀ x ∈ I.map (algebraMap D D'), σ x ∈ I) (hσ1 : σ 1 = c')
    (h : ModSplit P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D')) (algebraMap D D' c)) :
    ModSplit P ε ψ I (c * c') := sorry

/-! ## PB: perfectoid basics (tilt, `♯`, mod-`p` comparison) on top of Mathlib's `PreTilt` -/

/-- **PB1** the chosen roots of `ϖ` define `ϖ♭ ∈ C♭` with `(ϖ♭)♯ = ϖ₀`. -/
theorem perfectoid_varpiFlat (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : PerfectoidData p C) [Fact ¬IsUnit (p : C)] :
    letI := P.complete
    ∃ ϖf : PreTilt C p, PreTilt.untilt ϖf = P.ϖ 0 := sorry

/-- **PB2** `C/p ≅ C♭/(ϖ♭)^p`, compatibly with `♯` (BMS1 Lemma 3.10 in the `ϖ^p = p·unit` form). -/
theorem perfectoid_modp_tilt (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : PerfectoidData p C) [Fact ¬IsUnit (p : C)] (ϖf : PreTilt C p)
    (hϖ : (letI := P.complete; PreTilt.untilt ϖf) = P.ϖ 0) :
    letI := P.complete
    ∃ e : (C ⧸ Ideal.span {(p : C)}) ≃+* (PreTilt C p ⧸ Ideal.span {ϖf ^ p}),
      ∀ x : PreTilt C p, e (Ideal.Quotient.mk _ (PreTilt.untilt x)) = Ideal.Quotient.mk _ x :=
  sorry

/-- **PB5** torsion in a perfect ring is almost zero along `t^{1/p^∞}`. -/
theorem perfect_torsion_almostZero (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] (t x : R) (h : t * x = 0) (e : ℕ) :
    ((frobeniusEquiv R p).symm^[e] t) * x = 0 := sorry

end DSMap.Mix

/-- the assembly has exactly `area_MIX`'s statement -/
example : @DSMap.Mix.area_MIX_assembly = @DSMap.area_MIX := rfl
