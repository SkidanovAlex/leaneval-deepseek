import Mathlib
import Submission.Work.DSNORM.Defs
import Submission.Work.DSNORM.quotient_span_isRegularLocalRing
import Submission.Work.DSEQ0.FFR.torsionBy_stabilizes
import Submission.Work.DSEQ0.FFR.pd_of_pow_isTorsionBy
import Submission.Work.DSEQ0.FFR.pd_restrictScalars_quotSpan
import Submission.Work.DSEQ0.FFR.boundedFinFreeComplex_of_pdLE

/-!
# Every finitely generated module over a regular local ring has a bounded finite free resolution

This file proves `Work.DSEQ0.finFreeResolution_of_isRegularLocalRing`: over a regular local ring
`A`, every finitely generated module `M` is quasi-isomorphic to a bounded complex of finitely
generated free `A`-modules.

## Strategy

The mathematical input is Serre's theorem that a regular local ring has finite global dimension,
in the form `projectiveDimension M ≤ dim A` for every finitely generated `M`, proved here by
induction on the embedding dimension `d = (maximalIdeal A).spanFinrank = ringKrullDim A`:

* `d = 0` means that `A` is a field, and every module over a field is free;
* for `d + 1`, choose `x ∈ 𝔪 \ 𝔪²` (a minimal generator), so that `A ⧸ (x)` is regular local of
  embedding dimension `d`.  By induction, every finitely generated module over `A ⧸ (x)` has
  projective dimension `≤ d` there, and change of rings upgrades this to projective dimension
  `≤ d + 1` over `A` for every finitely generated `A`-module killed by `x`.  The induction step
  `hasProjectiveDimensionLT_of_forall_isTorsionBy` then splits an arbitrary finitely generated
  `M` into its `x`-power torsion part and `M ⧸ x^∞M`, on which `x` is a nonzerodivisor, so that
  Mathlib's `projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` applies.

Finally `boundedFinFreeComplex_of_pdLE` turns the projective dimension bound into the required
bounded complex of free modules.
-/

namespace Work.DSEQ0

universe u

open CategoryTheory

open scoped Pointwise

set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas -/

/-- `a ≤ a + 1` in `WithBot ℕ∞`. -/
lemma le_add_one_withBot (a : WithBot ℕ∞) : a ≤ a + 1 := by
  have h : (0 : WithBot ℕ∞) ≤ 1 := by simp
  simpa using add_le_add_right h a

/-- **Nakayama.**  A Noetherian local ring whose maximal ideal satisfies `𝔪 * 𝔪 = 𝔪` is a field. -/
theorem maximalIdeal_eq_bot_of_mul_self_eq_self {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (h : IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R = IsLocalRing.maximalIdeal R) :
    IsLocalRing.maximalIdeal R = ⊥ := by
  have hle : IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R • IsLocalRing.maximalIdeal R := by
    rw [Ideal.smul_eq_mul, h]
  have hmain := Submodule.eq_smul_of_le_smul_of_le_jacobson
    (N := IsLocalRing.maximalIdeal R) (I := IsLocalRing.maximalIdeal R) (J := ⊥)
    (Ideal.fg_of_isNoetherianRing _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  simpa using hmain

/-- A regular local ring of embedding dimension `d + 1` has an element of `𝔪 \ 𝔪²`. -/
theorem exists_mem_maximalIdeal_notMem_sq (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {d : ℕ} (hd : (IsLocalRing.maximalIdeal R).spanFinrank = d + 1) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  by_contra h
  push_neg at h
  have hmul : IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R
      = IsLocalRing.maximalIdeal R := by
    refine le_antisymm Ideal.mul_le_left (fun x hx => ?_)
    simpa [pow_two] using h x hx
  have hbot := maximalIdeal_eq_bot_of_mul_self_eq_self hmul
  rw [hbot] at hd
  simp at hd

/-- A regular local ring of embedding dimension `0` is a field, so every module has projective
dimension `0` (it is free). -/
theorem hasProjectiveDimensionLT_one_of_spanFinrank_eq_zero (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : (IsLocalRing.maximalIdeal R).spanFinrank = 0)
    (M : ModuleCat.{u} R) : CategoryTheory.HasProjectiveDimensionLT M 1 := by
  have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R))).mp hd
  have hfield : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot
  letI : Field R := hfield.toField
  haveI : Module.Free R ↥M := Module.Free.of_divisionRing R ↥M
  haveI : Module.Projective R ↥M :=
    Module.Projective.of_basis (Module.Free.chooseBasis R ↥M)
  exact CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp
    M.projective_of_categoryTheory_projective

/-! ## The induction step -/

set_option maxHeartbeats 4000000 in
/-- **Induction step.**  Let `x ∈ 𝔪` and suppose that every finitely generated `R`-module killed
by `x` has projective dimension `≤ D`.  Then every finitely generated `R`-module has projective
dimension `≤ D`. -/
theorem hasProjectiveDimensionLT_of_forall_isTorsionBy
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) (D : ℕ) (M : ModuleCat.{u} R)
    [Module.Finite R M]
    (hR' : ∀ (N : ModuleCat.{u} R), Module.Finite R N → Module.IsTorsionBy R N x →
      CategoryTheory.HasProjectiveDimensionLT N (D + 1)) :
    CategoryTheory.HasProjectiveDimensionLT M (D + 1) := by
  classical
  -- the `x`-power torsion submodule of `M`
  set T : Submodule R M := ⨆ k : ℕ, Submodule.torsionBy R M (x ^ k) with hTdef
  -- it is finitely generated
  have hTfg : T.FG := by
    have htop : (⊤ : Submodule R ↥M).FG := Module.Finite.fg_top
    exact htop.of_le le_top
  haveI hTfin : Module.Finite R ↥T := Module.Finite.iff_fg.mpr hTfg
  -- it is annihilated by a power of `x`
  obtain ⟨K, hK⟩ := Work.DSEQ0.FFR.torsionBy_stabilizes (R := R) (M := ↥M) x
  have hTeq : T = Submodule.torsionBy R ↥M (x ^ K) :=
    le_antisymm hK (le_iSup (fun k => Submodule.torsionBy R ↥M (x ^ k)) K)
  have hTtor : Module.IsTorsionBy R ↥T (x ^ K) := by
    intro t
    exact Subtype.ext ((Submodule.mem_torsionBy_iff (x ^ K) (t : ↥M)).mp (hTeq ▸ t.2))
  -- hence `pd T ≤ D`
  have hpdT : CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R ↥T) (D + 1) :=
    Work.DSEQ0.FFR.pd_of_pow_isTorsionBy (R := R) x hxm D (ModuleCat.of R ↥T) K hTtor hR'
  -- `x` is a nonzerodivisor on `M ⧸ T`
  have hxMT : IsSMulRegular (↥M ⧸ T) x := by
    intro a b hab
    obtain ⟨a₀, rfl⟩ := Submodule.mkQ_surjective T a
    obtain ⟨b₀, rfl⟩ := Submodule.mkQ_surjective T b
    have h1 : x • a₀ - x • b₀ ∈ T := by
      have h2 : (Submodule.mkQ T) (x • a₀) = (Submodule.mkQ T) (x • b₀) := by
        rw [map_smul, map_smul]
        exact hab
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at h2
      exact (Submodule.Quotient.eq T).mp h2
    have h3 : a₀ - b₀ ∈ T := by
      have h4 : x ^ (K + 1) • (a₀ - b₀) = 0 := by
        have h5 := (Submodule.mem_torsionBy_iff (x ^ K) (x • a₀ - x • b₀)).mp (hTeq ▸ h1)
        have h5' : x ^ K • (x • a₀) = x ^ K • (x • b₀) := by
          rw [smul_sub, sub_eq_zero] at h5
          exact h5
        have h6 : x ^ (K + 1) • a₀ = x ^ (K + 1) • b₀ := by
          calc x ^ (K + 1) • a₀ = x ^ K • (x • a₀) := by rw [pow_succ, mul_smul]
            _ = x ^ K • (x • b₀) := h5'
            _ = x ^ (K + 1) • b₀ := by rw [pow_succ, mul_smul]
        rw [smul_sub, h6, sub_self]
      exact le_iSup (fun k => Submodule.torsionBy R ↥M (x ^ k)) (K + 1)
        ((Submodule.mem_torsionBy_iff (x ^ (K + 1)) (a₀ - b₀)).mpr h4)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq T).mpr h3
  -- `QuotSMulTop x (M ⧸ T)` is finitely generated and killed by `x`
  have hN'fin : Module.Finite R (QuotSMulTop x (↥M ⧸ T)) :=
    Module.Finite.quotient R (x • (⊤ : Submodule R (↥M ⧸ T)))
  have hN'tor : Module.IsTorsionBy R (QuotSMulTop x (↥M ⧸ T)) x :=
    (Module.isTorsionBy_iff_mem_annihilator R (QuotSMulTop x (↥M ⧸ T))).mpr
      (QuotSMulTop.mem_annihilator (↥M ⧸ T) x)
  have hN' : CategoryTheory.HasProjectiveDimensionLT
      (ModuleCat.of R (QuotSMulTop x (↥M ⧸ T))) (D + 1) :=
    hR' _ hN'fin hN'tor
  -- hence `pd (M ⧸ T) ≤ D`
  have hpdMT : CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R (↥M ⧸ T)) (D + 1) := by
    have heq := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (R := R) (ModuleCat.of R (↥M ⧸ T)) x hxMT hxm
    have hN'' : CategoryTheory.projectiveDimension
        (ModuleCat.of R (QuotSMulTop x (↥M ⧸ T))) ≤ (D : WithBot ℕ∞) :=
      (CategoryTheory.projectiveDimension_le_iff _ D).mpr hN'
    rw [heq] at hN''
    refine (CategoryTheory.projectiveDimension_le_iff _ D).mp
      (le_trans (le_add_one_withBot _) hN'')
  -- assemble the short exact sequence `0 → T → M → M ⧸ T → 0`
  have hS : (ShortComplex.mk (ModuleCat.ofHom T.subtype) (ModuleCat.ofHom (Submodule.mkQ T))
      (by ext m; simp [Submodule.mkQ_apply])).ShortExact :=
    ModuleCat.shortComplex_shortExact _
      (by simpa using LinearMap.exact_subtype_mkQ T)
      (by simpa using T.injective_subtype)
      (by simpa using Submodule.mkQ_surjective T)
  exact hS.hasProjectiveDimensionLT_X₂ (D + 1) hpdT hpdMT

/-! ## The main induction -/

/-- **Serre's theorem (weak form).**  Every finitely generated module over a regular local ring of
embedding dimension `d` has projective dimension `≤ d`. -/
theorem hasProjectiveDimensionLT_of_isRegularLocalRing :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = d →
      ∀ (M : ModuleCat.{u} R), Module.Finite R M →
        CategoryTheory.HasProjectiveDimensionLT M (d + 1) := by
  intro d
  induction d with
  | zero =>
      intro R _ _ hd M _
      exact hasProjectiveDimensionLT_one_of_spanFinrank_eq_zero R hd M
  | succ d ih =>
      intro R _ _ hd M hM
      haveI : IsDomain R := Work.DSREG.isDomain_of_isRegularLocalRing R
      obtain ⟨x, hxm, hxsq⟩ := exists_mem_maximalIdeal_notMem_sq R hd
      have hx0 : x ≠ 0 := fun h => hxsq (by rw [h]; exact Submodule.zero_mem _)
      have hxreg : IsSMulRegular R x := fun a b hab => mul_left_cancel₀ hx0 hab
      haveI hntriv : Nontrivial (R ⧸ Ideal.span {x}) :=
        Work.DSREG.nontrivial_quotient_span_singleton hxm
      obtain ⟨hreg', -, hdim'⟩ := Work.DSNORM.quotient_span_isRegularLocalRing R hxm hxsq
      haveI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hreg'
      have hd' : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = d := by
        have := hdim'
        omega
      have hR' : ∀ (N : ModuleCat.{u} R), Module.Finite R N → Module.IsTorsionBy R N x →
          CategoryTheory.HasProjectiveDimensionLT N (d + 2) := by
        intro N hNfin hNtor
        letI : Module (R ⧸ Ideal.span {x}) ↥N := Module.IsTorsionBy.module hNtor
        have hNfin' : Module.Finite (R ⧸ Ideal.span {x}) ↥N :=
          Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) ↥N
        have hbd := ih (R ⧸ Ideal.span {x}) hd' (ModuleCat.of (R ⧸ Ideal.span {x}) ↥N) hNfin'
        have hcr := Work.DSEQ0.FFR.pd_restrictScalars_quotSpan R x hxreg
          (ModuleCat.of (R ⧸ Ideal.span {x}) ↥N) (d + 1) hbd
        -- the `R`-module structure induced on `N` by restriction of scalars along `R → R ⧸ (x)`
        -- is the original one, since `x` acts trivially on `N`
        have e : (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
            (ModuleCat.of (R ⧸ Ideal.span {x}) ↥N) ≅ N :=
          { hom := ModuleCat.ofHom
              { toFun := id, map_add' := fun a b => rfl
                map_smul' := fun r n => Module.IsTorsionBy.mk_smul hNtor r n }
            inv := ModuleCat.ofHom
              { toFun := id, map_add' := fun a b => rfl
                map_smul' := fun r n => (Module.IsTorsionBy.mk_smul hNtor r n).symm }
            hom_inv_id := by ext n; rfl
            inv_hom_id := by ext n; rfl }
        exact CategoryTheory.hasProjectiveDimensionLT_of_iso e (d + 2)
      exact hasProjectiveDimensionLT_of_forall_isTorsionBy (R := R) hxm (d + 1) M hR'

universe a

/-- **Every finitely generated module over a regular local ring has a bounded finite free
resolution.** -/
theorem finFreeResolution_of_isRegularLocalRing (A : Type a) [CommRing A]
    [IsRegularLocalRing A] (i : ℤ) {M : Type a} [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    ∃ (G : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ j, Module.Finite A (G.X j)) ∧ (∀ j, Module.Free A (G.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧
      ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
          (ModuleCat.of A M),
        QuasiIso g := by
  have hpd : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of A M)
      (IsLocalRing.maximalIdeal A).spanFinrank :=
    hasProjectiveDimensionLT_of_isRegularLocalRing _ A rfl (ModuleCat.of A M) inferInstance
  exact Work.DSEQ0.FFR.boundedFinFreeComplex_of_pdLE A (IsLocalRing.maximalIdeal A).spanFinrank
    (ModuleCat.of A M) i hpd

end Work.DSEQ0
