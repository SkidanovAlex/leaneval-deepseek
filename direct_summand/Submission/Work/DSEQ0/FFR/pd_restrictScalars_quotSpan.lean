import Mathlib

set_option linter.style.haveILetI false
set_option linter.defProp false

/-!
# Projective dimension after restriction of scalars along `R ⟶ R ⧸ (x)`

If `x` is a regular element of a commutative ring `R` and `N` is a module over
`S = R ⧸ (x)` of projective dimension `< j` (as an `S`-module), then `N`, viewed as an
`R`-module by restriction of scalars, has projective dimension `< j + 1`.

The mathematical content is the change-of-rings bound `pd_R N ≤ pd_S N + pd_R S` with
`pd_R S ≤ 1` (from the two-term resolution `0 ⟶ R --x--> R ⟶ S ⟶ 0`).

The proof is an induction on `j`:
* for `j = 0` the module `N` is zero;
* in the inductive step one uses the presentation `(↥N →₀ S) ↠ N` (a free, hence
  projective, `S`-module); its kernel `K` satisfies `pd_S K < j` (dimension shifting),
  so by induction `pd_R K < j + 1`, whereas the free module `(↥N →₀ S)` satisfies
  `pd_R < 2` (the base case, proved from the two-term resolution of `R ⧸ (x)` and
  the exactness of `I →₀ -`), and `pd` is subadditive along short exact sequences.
-/

namespace Work.DSEQ0.FFR

universe u

open CategoryTheory Limits

/-- A regular element of `R` is regular on every free `R`-module `I →₀ R`. -/
private theorem isSMulRegular_finsupp (R : Type u) [CommRing R] (x : R) (hx : IsSMulRegular R x)
    (I : Type u) : IsSMulRegular (I →₀ R) x := by
  intro a b hab
  ext i
  exact hx (by simpa using congrArg (fun (f : I →₀ R) => f i) hab)

/-- The `R`-module `I →₀ (R ⧸ (x))` has projective dimension at most one.

This is the base case of the change-of-rings induction: `R ⧸ (x)` is the cokernel of the
injective map `R --x--> R`, and the exactness of `I →₀ -` promotes this two-term
resolution to a two-term resolution of `I →₀ (R ⧸ (x))`. -/
private theorem hasProjectiveDimensionLT_restrictScalars_free (R : Type u) [CommRing R] (x : R)
    (hx : IsSMulRegular R x) (I : Type u) :
    HasProjectiveDimensionLT ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
      (ModuleCat.of (R ⧸ Ideal.span {x}) (I →₀ (R ⧸ Ideal.span {x})))) 2 := by
  classical
  -- `QuotSMulTop x (I →₀ R)` is the cokernel of `x • ·` on the free module `I →₀ R`.
  have hq : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (I →₀ R))) 2 := by
    have hreg : IsSMulRegular (I →₀ R) x := isSMulRegular_finsupp R x hx I
    have hSES := hreg.smulShortComplex_shortExact (M := ModuleCat.of R (I →₀ R))
    have h1 : HasProjectiveDimensionLT (ModuleCat.of R (I →₀ R)) 1 := inferInstance
    have h2 : HasProjectiveDimensionLT (ModuleCat.of R (I →₀ R)) 2 := inferInstance
    exact hSES.hasProjectiveDimensionLT_X₃ 1 h1 h2
  haveI : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (I →₀ R))) 2 := hq
  -- `QuotSMulTop x (I →₀ R) ≅ (R ⧸ (x)) ⊗ (I →₀ R) ≅ I →₀ ((R ⧸ (x)) ⊗ R) ≅ I →₀ (R ⧸ (x))`
  let e : QuotSMulTop x (I →₀ R) ≃ₗ[R] (I →₀ (R ⧸ Ideal.span {x})) :=
    (QuotSMulTop.equivQuotTensor x (I →₀ R)) ≪≫ₗ
    (TensorProduct.finsuppRight R R (R ⧸ Ideal.span {x}) R I) ≪≫ₗ
    (Finsupp.mapRange.linearEquiv (TensorProduct.rid R (R ⧸ Ideal.span {x})))
  have h' : HasProjectiveDimensionLT (ModuleCat.of R (I →₀ (R ⧸ Ideal.span {x}))) 2 :=
    hasProjectiveDimensionLT_of_iso e.toModuleIso 2
  -- the module structure of the restricted scalars is definitionally the one above
  exact hasProjectiveDimensionLT_of_iso (Iso.refl (ModuleCat.of R (I →₀ (R ⧸ Ideal.span {x})))) 2

/-- **Change of rings for a quotient by a nonzerodivisor** (induction step):
if `N` is a module over `S = R ⧸ (x)` with `pd_S N < n`, then `pd_R N < n + 1`. -/
private theorem aux (R : Type u) [CommRing R] (x : R) (hx : IsSMulRegular R x) (n : ℕ) :
    ∀ (N : ModuleCat.{u} (R ⧸ Ideal.span {x})), HasProjectiveDimensionLT N n →
      HasProjectiveDimensionLT ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N)
        (n + 1) := by
  induction n with
  | zero =>
    -- `pd_S N < 0` means that `N` is the zero module
    intro N hN
    haveI : IsZero N := isZero_of_hasProjectiveDimensionLT_zero N
    have hz : IsZero ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) :=
      Functor.map_isZero (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))) ‹IsZero N›
    haveI : HasProjectiveDimensionLT
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) 0 :=
      hz.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 1 (by omega)
  | succ n ih =>
    intro N hN
    classical
    -- the presentation `(↥N →₀ S) ↠ N` of `N` by a free `S`-module, and its kernel `K`
    let f : (↥N →₀ (R ⧸ Ideal.span {x})) →ₗ[R ⧸ Ideal.span {x}] ↥N :=
      Finsupp.linearCombination (R ⧸ Ideal.span {x}) (id : ↥N → ↥N)
    have hf : Function.Surjective f := Finsupp.linearCombination_id_surjective _ ↥N
    have hSES : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    haveI hepi : Epi f.shortComplexKer.g := hSES.epi_g
    -- the base case: the free `S`-module `↥N →₀ S` has `R`-projective dimension `< 2`
    have hbaseX := hasProjectiveDimensionLT_restrictScalars_free R x hx ↥N
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: `N` is projective, hence a retract of the free module `↥N →₀ S`
      subst hn
      haveI : Projective N := projective_iff_hasProjectiveDimensionLT_one.mpr hN
      obtain ⟨s, hs⟩ := CategoryTheory.Projective.factors (𝟙 N) f.shortComplexKer.g
      let r : Retract N f.shortComplexKer.X₂ := Retract.mk s f.shortComplexKer.g hs
      haveI : HasProjectiveDimensionLT ((ModuleCat.restrictScalars
          (Ideal.Quotient.mk (Ideal.span {x}))).obj f.shortComplexKer.X₂) 2 := hbaseX
      exact (r.map (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x})))).hasProjectiveDimensionLT 2
    · -- `n ≥ 1`: dimension shifting gives `pd_S K < n`, then use the induction hypothesis
      have hproj : Projective f.shortComplexKer.X₂ := inferInstance
      haveI : HasProjectiveDimensionLT f.shortComplexKer.X₂ 1 := inferInstance
      have hX₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ n :=
        hasProjectiveDimensionLT_of_ge _ 1 n hn
      have hN' : HasProjectiveDimensionLT f.shortComplexKer.X₃ (n + 1) := hN
      have hX₁ : HasProjectiveDimensionLT f.shortComplexKer.X₁ n :=
        hSES.hasProjectiveDimensionLT_X₁ n hX₂ hN'
      have ihK := ih f.shortComplexKer.X₁ hX₁
      -- restriction of scalars along `R ⟶ S` is exact, so the `S`-short exact sequence
      -- `0 ⟶ K ⟶ (↥N →₀ S) ⟶ N ⟶ 0` remains short exact over `R`
      have hRsc : (f.shortComplexKer.map
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x})))).ShortExact :=
        hSES.map_of_exact _
      have hbase' : HasProjectiveDimensionLT ((f.shortComplexKer.map
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x})))).X₂) (n + 2) := by
        haveI : HasProjectiveDimensionLT ((f.shortComplexKer.map
            (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x})))).X₂) 2 := hbaseX
        exact hasProjectiveDimensionLT_of_ge _ 2 (n + 2) (by omega)
      exact hRsc.hasProjectiveDimensionLT_X₃ (n + 1) ihK hbase'

theorem pd_restrictScalars_quotSpan (R : Type u) [CommRing R] (x : R) (hx : IsSMulRegular R x) (N : ModuleCat.{u} (R ⧸ Ideal.span {x})) (j : ℕ) (h : CategoryTheory.HasProjectiveDimensionLT N j) : CategoryTheory.HasProjectiveDimensionLT ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) (j + 1) :=
  aux R x hx j N h

end Work.DSEQ0.FFR
