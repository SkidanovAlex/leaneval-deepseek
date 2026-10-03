import Mathlib
import Submission.Work.ORCoherence.Imports
import Submission.Work.ORCoherence.Tor
import Submission.Work.ORCoherence.Criterion

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits
open scoped TensorProduct ZeroObject

namespace Work.ORCoherence.Tor

universe u

/-!
# From the vanishing of `Tor₂` to the injectivity criterion `TorTwoVanishes`

Given a ring homomorphism `f : R →+* S` and the assumption that `Tor₂^R(S, M) = 0` for
every left `R`-module `M` (that is, `S` has weak dimension `≤ 1` as a right `R`-module),
we show that for every short exact sequence
`0 → P₂ → P₁ → P₀ → M → 0` with `P₀`, `P₁`, `P₂` projective, the induced map
`S ⊗[R] P₂ → S ⊗[R] P₁` is injective.

The proof builds the length-two projective resolution of `M` whose chain complex is
concentrated in degrees `0, 1, 2` with `X 0 = P₀`, `X 1 = P₁`, `X 2 = P₂`, so that the
second homology of the complex obtained by applying `S ⊗[R] -` is
`ker (Balanced.map f d₂.hom)`, while `ProjectiveResolution.isoLeftDerivedObj` identifies it
with `Tor₂^R(S, M) = 0`.
-/

section Chain

variable {R : Type u} [Ring R]

/-- The objects of the length-two chain complex attached to an exact sequence
`P₂ → P₁ → P₀`: it is `P₀`, `P₁`, `P₂` in degrees `0`, `1`, `2` and zero from degree `3` on. -/
noncomputable abbrev seqX (P₀ P₁ P₂ : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  match n with
  | 0 => P₀
  | 1 => P₁
  | 2 => P₂
  | _ => 0

/-- The differentials of the length-two chain complex attached to an exact sequence
`P₂ → P₁ → P₀`. -/
noncomputable abbrev seqD {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀) (n : ℕ) :
    seqX P₀ P₁ P₂ (n + 1) ⟶ seqX P₀ P₁ P₂ n :=
  match n with
  | 0 => d₁
  | 1 => d₂
  | _ => 0

/-- The chain complex concentrated in degrees `0, 1, 2` attached to a pair of composable
morphisms `P₂ --d₂--> P₁ --d₁--> P₀` with `d₂ ≫ d₁ = 0`. -/
noncomputable abbrev seqComplex {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (h : d₂ ≫ d₁ = 0) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (seqX P₀ P₁ P₂) (seqD d₂ d₁)
    (fun n => by
      rcases n with _ | m
      · exact h
      · rw [show seqD d₂ d₁ (m + 1 + 1) = 0 from rfl, zero_comp])

lemma seqComplex_d_zero_one {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (h : d₂ ≫ d₁ = 0) : (seqComplex d₂ d₁ h).d 1 0 = d₁ :=
  ChainComplex.of_d (seqX P₀ P₁ P₂) (seqD d₂ d₁) 0

lemma seqComplex_d_one_two {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (h : d₂ ≫ d₁ = 0) : (seqComplex d₂ d₁ h).d 2 1 = d₂ :=
  ChainComplex.of_d (seqX P₀ P₁ P₂) (seqD d₂ d₁) 1

lemma seqComplex_d_two_three {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (h : d₂ ≫ d₁ = 0) : (seqComplex d₂ d₁ h).d 3 2 = 0 :=
  ChainComplex.of_d (seqX P₀ P₁ P₂) (seqD d₂ d₁) 2

lemma seqComplex_d_zero_zero {P₂ P₁ P₀ : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (h : d₂ ≫ d₁ = 0) : (seqComplex d₂ d₁ h).d 0 0 = 0 :=
  ChainComplex.of_d_ne (seqX P₀ P₁ P₂) (seqD d₂ d₁) (by norm_num : ¬ ((0 : ℕ) = 0 + 1))

/-- The augmentation `seqComplex d₂ d₁ h ⟶ M` induced by the projection `π : P₀ ⟶ M`. -/
noncomputable abbrev seqπ {P₂ P₁ P₀ M : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (π : P₀ ⟶ M) (h : d₂ ≫ d₁ = 0) (h' : d₁ ≫ π = 0) :
    seqComplex d₂ d₁ h ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M :=
  (ChainComplex.toSingle₀Equiv (seqComplex d₂ d₁ h) M).symm ⟨π, by
    rw [seqComplex_d_zero_one d₂ d₁ h]
    exact h'⟩

lemma seqπ_f_zero {P₂ P₁ P₀ M : ModuleCat.{u} R} (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀)
    (π : P₀ ⟶ M) (h : d₂ ≫ d₁ = 0) (h' : d₁ ≫ π = 0) : (seqπ d₂ d₁ π h h').f 0 = π := by
  show ((ChainComplex.toSingle₀Equiv (seqComplex d₂ d₁ h) M).symm ⟨π, _⟩).f 0 = π
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := seqComplex d₂ d₁ h) (X := M) π _

/-- The length-two projective resolution of `M` provided by an exact sequence
`0 → P₂ → P₁ → P₀ → M → 0` with `P₀`, `P₁`, `P₂` projective. -/
noncomputable def seqResolution {P₂ P₁ P₀ M : ModuleCat.{u} R}
    [Projective P₂] [Projective P₁] [Projective P₀]
    (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀) (π : P₀ ⟶ M) (h : d₂ ≫ d₁ = 0) (h' : d₁ ≫ π = 0)
    (hm : Mono d₂) (he : (ShortComplex.mk d₂ d₁ h).Exact) (he' : (ShortComplex.mk d₁ π h').Exact)
    (hπ : Epi π) : ProjectiveResolution M where
  complex := seqComplex d₂ d₁ h
  projective := fun n => by
    rcases n with _|_|_|k
    · change Projective P₀; infer_instance
    · change Projective P₁; infer_instance
    · change Projective P₂; infer_instance
    · exact IsZero.projective (isZero_zero (ModuleCat.{u} R))
  π := seqπ d₂ d₁ π h h'
  quasiIso := ⟨fun i => by
    rcases i with _ | n
    · refine (ChainComplex.quasiIsoAt₀_iff _).2 ?_
      refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ⟨?_, ?_⟩
      · exact seqComplex_d_zero_zero d₂ d₁ h
      · exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 M 1 0
      · exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 M 0 0
      · exact he'
      · exact hπ
    · refine (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj M n)).2 ?_
      rcases n with _ | _ | k
      · refine (HomologicalComplex.exactAt_iff' (seqComplex d₂ d₁ h) 2 1 0
          (by norm_num) (by norm_num)).2 ?_
        exact he
      · refine (HomologicalComplex.exactAt_iff' (seqComplex d₂ d₁ h) 3 2 1
          (by norm_num) (by norm_num)).2 ?_
        refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
        · exact seqComplex_d_two_three d₂ d₁ h
        · exact hm
      · refine (HomologicalComplex.exactAt_iff' (seqComplex d₂ d₁ h) (k+4) (k+3) (k+2)
          (by rw [ChainComplex.prev ℕ (k+3)]; omega)
          (by show (ComplexShape.down ℕ).next ((k+2)+1) = k+2
              rw [ChainComplex.next_nat_succ])).2 ?_
        exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero (ModuleCat.{u} R))⟩

end Chain

/-- `Tor₂^R(S, M) = 0` for all `M` implies `TorTwoVanishes f`.

Recommended route (no long exact sequence needed): given the exact sequence
`0 → P₂ → P₁ → P₀ → M → 0` supplied by `TorTwoVanishes`, build the `ProjectiveResolution M`
whose chain complex is concentrated in degrees `0,1,2` with `X 0 = P₀`, `X 1 = P₁`, `X 2 = P₂`
(use `ChainComplex.of`, `ChainComplex.toSingle₀Equiv` and `quasiIsoAt_iff_exactAt'`,
`ChainComplex.quasiIsoAt₀_iff` as in `ProjectiveResolution.of`).  Then
`ProjectiveResolution.isoLeftDerivedObj P (tensorFunctor f) 2` identifies `Tor f 2 M` with the
second homology of the complex `Balanced f P₀ ← Balanced f P₁ ← Balanced f P₂ ← 0`, which is
`LinearMap.ker (Balanced.map f d₂)`; since the differential out of degree 3 is `0`, `IsZero`
of that homology gives that this kernel is `⊥`, i.e. injectivity of `Balanced.map f d₂`. -/
theorem torTwoVanishes_of_torVanishes {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (h : TorVanishes f) : TorTwoVanishes f := by
  intro M P₂ P₁ P₀ _ _ _ d₂ d₁ π hd hd' hm he he' hπ
  let P : ProjectiveResolution M := seqResolution d₂ d₁ π hd hd' hm he he' hπ
  let Q : ChainComplex (ModuleCat.{u} S) ℕ :=
    ((tensorFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  -- `Q` is `S ⊗[R] -` applied to the length-two resolution, so its homology in degree `2`
  -- computes `Tor₂^R(S, M)`.
  have hQ : IsZero (Q.homology 2) :=
    IsZero.of_iso (h M) (P.isoLeftDerivedObj (tensorFunctor f) 2).symm
  have hEx : Q.ExactAt 2 := (HomologicalComplex.exactAt_iff_isZero_homology Q 2).2 hQ
  have hEx' : (Q.sc' 3 2 1).Exact :=
    (HomologicalComplex.exactAt_iff' Q 3 2 1 (by norm_num) (by norm_num)).1 hEx
  -- The differential `Q.d 3 2` vanishes, hence exactness at `2` says exactly that `Q.d 2 1`
  -- is a monomorphism.
  have hd32 : P.complex.d 3 2 = 0 := seqComplex_d_two_three d₂ d₁ hd
  have hzero : (Q.sc' 3 2 1).f = 0 := by
    have h1 : (Q.sc' 3 2 1).f = (tensorFunctor f).map (P.complex.d 3 2) := rfl
    rw [h1, hd32, (tensorFunctor f).map_zero]
    rfl
  have hmono : Mono (Q.d 2 1) :=
    (ShortComplex.exact_iff_mono (Q.sc' 3 2 1) hzero).1 hEx'
  -- `Q.d 2 1` is `Balanced.map f d₂.hom`.
  have h2 : Mono (ModuleCat.ofHom (Balanced.map f d₂.hom)) := hmono
  exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom (Balanced.map f d₂.hom))).1 h2

end Work.ORCoherence.Tor
