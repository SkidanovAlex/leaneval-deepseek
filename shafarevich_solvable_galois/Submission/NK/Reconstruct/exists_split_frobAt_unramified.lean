import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Reconstruct.frobAt_descend_of_galRestrict_commutes
import Submission.NK.Reconstruct.galRestrict_commutes_of_field_commutes
import Submission.NK.Reconstruct.ramificationIdx_under_eq_one_and_eq_one
import Submission.NK.Reconstruct.restrictNormalHom_eq_one_of_commutes
import Submission.NK.Reconstruct.splitFrobeniusBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open NK.Chebotarev
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Čebotarev with a completely split prime, sharpened by the unramifiedness of the Frobenius
prime over the base.**  Let `Ω/ℚ` be Galois, `L` a finite normal level of `Ω/ℚ`, `N/L` a finite
normal number-field level inside `Ω` and `τ ∈ Gal(N/L)`.  Then there is a prime `𝔭` of `L` which is
**completely split over `ℚ`** (`SplitsCompletelyOverRat 𝔭`: inertia degree and ramification index
of `𝔭` over `𝓞 ℚ` are both `1`) and a prime `P` of `𝓞 N` above `𝔭` such that
* `P` is **unramified over `𝔭`** (`P.asIdeal.ramificationIdx (𝓞 ↥L.L) = 1`), and
* `τ` is an arithmetic Frobenius element at `P` over the base field `L`
  (`IsFrobAt (K := ↥L.L) (L := ↥N) P τ`).

This is `NK.Reconstruct.exists_split_frobAt` with the additional conclusion that `P` is
unramified over `𝔭`; that extra fact is what makes the Frobenius element at `P` over the base `L`
*unique* (`NK.Chebotarev.IsFrobAt.eq_of_isFrobAt`), which is needed to extend a Frobenius element
at a *fixed* completely split prime from one finite level to all levels of `Ω/L`.

Plan (the proof of `exists_split_frobAt` with one extra clause).  Let `Ñ :=
IntermediateField.normalClosure ℚ ↥N Ω`, the Galois closure of `N` over `ℚ` inside `Ω`: it is finite
over `ℚ` (`normalClosure.is_finiteDimensional`), normal over `ℚ` (`normalClosure.normal`), hence a
number field (`Commons.NumberTheory.NumberField.numberField_of_intermediateField`), and it contains
`N`.  Since `Ñ/ℚ` is Galois, so is `Ñ/↥L.L`, and `Gal(Ñ/L) → Gal(N/L)` is surjective because `N/L`
is normal (`AlgEquiv.restrictNormalHom_surjective`): lift `τ` to `τ̃ ∈ Gal(Ñ/L)`, viewed as an
element of `Gal(Ñ/ℚ)`.  Apply `hc : ChebotarevInput ℚ Ω` at the level `Ñ/ℚ` to `τ̃`: this gives a
rational prime `p₀` and a prime `P̃` of `𝓞 Ñ` above it with `P̃` **unramified over `𝓞 ℚ`**
(`P̃.asIdeal.ramificationIdx (𝓞 ℚ) = 1` — this is the hypothesis of `ChebotarevInput`) and
`IsFrobAt (K := ℚ) (L := ↥Ñ) P̃ τ̃`.  Set `𝔭 := P̃ ∩ L` and `P := P̃ ∩ N` (both contractions land
over `𝔭`).  Then:
* `IsFrobAt (K := ℚ) (L := ↥L.L) 𝔭 1` because `τ̃` fixes `L` (restriction of a Frobenius along the
  normal subextension `L/ℚ` — `NK.Chebotarev.IsFrobAtRestrictNormalHom`), so
  `𝔭.asIdeal.inertiaDeg (𝓞 ℚ) = 1` by `NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one`
  applied to `𝔭` (unramified over `ℚ` because `P̃` is);
* `𝔭.asIdeal.ramificationIdx (𝓞 ℚ) = 1` from `Ideal.ramificationIdx_tower` at `𝔭 ⊆ P̃`
  (`1 = e(P̃/ℚ) = e(𝔭/ℚ) * e(P̃/𝔭)`), so that `SplitsCompletelyOverRat 𝔭` holds;
* the base change `ℚ → L` of Frobenius elements
  (`NK.Reconstruct.isFrobAt_of_isFrobAt_restrictScalars`, whose hypothesis
  `f(𝔭/ℚ) = 1` is the inertia-degree statement above) gives
  `IsFrobAt (K := ↥L.L) (L := ↥Ñ) P̃ τ̃`, and restricting to `N`
  (`NK.Chebotarev.IsFrobAtRestrictNormalHom`) gives `IsFrobAt (K := ↥L.L) (L := ↥N) P τ`;
* the extra clause: `1 = e(P̃/ℚ) = e(P/ℚ) * e(P̃/P)` by `Ideal.ramificationIdx_tower`, so
  `e(P/ℚ) = 1`, and `1 = e(P/ℚ) = e(𝔭/ℚ) * e(P/𝔭) = e(P/𝔭)` since `e(𝔭/ℚ) = 1`. -/
theorem exists_split_frobAt_unramified {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    (hc : NK.Reconstruct.ChebotarevInput ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (N : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L N] [Normal ↥L.L N] [NumberField ↥N]
    (τ : Gal(↥N/↥L.L)) :
    ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (P : NK.Chebotarev.PrimeIdeal ↥N),
      P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L.L) = 1 ∧
      NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥N) P τ := by
  classical
  -- (0) Ω is normal over `↥L.L`
  haveI hNormalOmega : Normal ↥L.L Ω := IsGalois.to_normal
  -- (1) `N` is finite over `ℚ`
  have hfinN : FiniteDimensional ℚ ↥N := FiniteDimensional.trans ℚ ↥L.L ↥N
  letI : FiniteDimensional ℚ ↥N := hfinN
  -- (2) `M` : the normal closure of `N` over `ℚ` inside `Ω`, a finite normal number-field level
  let M : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ ↥N Ω
  letI : Algebra ℚ ↥M := IntermediateField.algebra' M
  haveI hMfin : FiniteDimensional ℚ ↥M := normalClosure.is_finiteDimensional ℚ ↥N Ω
  haveI hMnor : Normal ℚ ↥M := normalClosure.normal ℚ ↥N Ω
  haveI hMnf : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ℚ) (K' := Ω) M
  -- (3) `N ⊆ M` and `L ⊆ M`
  have hNM : N.toSubsemiring ≤ M.toSubsemiring := fun x hx => by
    show x ∈ (⨆ f : ↥N →ₐ[ℚ] Ω, f.fieldRange : IntermediateField ℚ Ω)
    exact le_iSup (fun f : ↥N →ₐ[ℚ] Ω => f.fieldRange) (N.val.restrictScalars ℚ) ⟨⟨x, hx⟩, rfl⟩
  have hLM : L.L.toSubsemiring ≤ M.toSubsemiring := fun x hx =>
    hNM (N.algebraMap_mem (⟨x, hx⟩ : ↥L.L))
  -- (4) the algebra structures `↥N → ↥M` and `↥L.L → ↥M`
  letI : Algebra ↥N ↥M := (Subsemiring.inclusion hNM).toAlgebra
  letI : Algebra ↥L.L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI tLNM : @IsScalarTower ↥L.L ↥N ↥M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  -- the `ℚ`-algebra structure on `↥L.L` is the one induced by its structure of intermediate field
  letI instLL : Algebra ℚ ↥L.L := IntermediateField.algebra' (K := ℚ) (L := Ω) L.L
  haveI tQLM : @IsScalarTower ℚ ↥L.L ↥M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  -- (5) `↥L.L` is normal (hence Galois) over `ℚ`, and `M` is normal over `↥L.L`
  have hNorLL : Normal ℚ ↥L.L := by
    have he : (IntermediateField.algebra' (K := ℚ) (L := Ω) L.L : Algebra ℚ ↥L.L) = instLL :=
      Subsingleton.elim _ _
    exact he ▸ L.normal
  haveI := hNorLL
  haveI hgalLL : IsGalois ℚ ↥L.L :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hMnorL : Normal ↥L.L ↥M := Normal.tower_top_of_normal (F := ℚ) (K := ↥L.L) (E := ↥M)
  -- (6) lift `τ` to `ρ ∈ Gal(M/L)`
  obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L.L) (K₁ := ↥N) (E := ↥M) τ
  -- (7) `ρ` as a `ℚ`-automorphism, and Čebotarev at the level `M`
  let ρ₀ : Gal(↥M/ℚ) := ρ.restrictScalars ℚ
  obtain ⟨p₀, Pt, hPtlies, he0, hρ₀frob⟩ := hc M ρ₀
  -- (8) the primes of `L` and of `N` below `Pt`
  let pp : PrimeIdeal ↥L.L := Pt.under (𝓞 ↥L.L)
  let P : PrimeIdeal ↥N := Pt.under (𝓞 ↥N)
  -- (9) `ρ` fixes `↥L.L`
  have hρ' : ρ.restrictNormal ↥N = τ := hρ
  have hfix : ∀ x : ↥L.L, ρ (algebraMap ↥L.L ↥M x) = algebraMap ↥L.L ↥M x := by
    intro x
    rw [IsScalarTower.algebraMap_apply ↥L.L ↥N ↥M x]
    rw [← AlgEquiv.restrictNormal_commutes ρ ↥N (algebraMap ↥L.L ↥N x), hρ', AlgEquiv.commutes]
  -- (10) unramifiedness: `e(𝔭/ℚ) = 1` and `e(Pt/𝔭) = 1`
  obtain ⟨hunr_pp, hunr_Pt⟩ :=
    ramificationIdx_under_eq_one_and_eq_one (K := ℚ) (L := ↥L.L) (M := ↥M) Pt he0
  -- (11) the restriction of `ρ₀` to `L` is trivial, hence `𝔭` is completely split over `ℚ`
  have hres := isFrobAt_restrictNormalHom_le (K := ℚ) (K' := Ω) (L := L.L) (M := M) hLM hρ₀frob
  have hres1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ↥M) L.L ρ₀ = 1 := by
    refine restrictNormalHom_eq_one_of_commutes (K := ℚ) (K' := Ω) L.L M ?_
    intro x
    exact hfix x
  have hfrob1 : IsFrobAt (K := ℚ) (L := ↥L.L) pp 1 := by
    rw [hres1] at hres
    exact hres
  have hlies_pp : pp.asIdeal.LiesOver p₀.asIdeal := ⟨by
    show p₀.asIdeal = Ideal.under (𝓞 ℚ) pp.asIdeal
    rw [show pp.asIdeal = Ideal.under (𝓞 ↥L.L) Pt.asIdeal from rfl,
      Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 ↥L.L) (𝔓 := Pt.asIdeal), ← hPtlies.over]⟩
  have hf_pp : pp.asIdeal.inertiaDeg (𝓞 ℚ) = 1 :=
    (IsFrobAt_eq_one_iff_inertiaDeg_eq_one (K := ℚ) (L := ↥L.L) hlies_pp hunr_pp).1 hfrob1
  have hsplit : SplitsCompletelyOverRat pp := by
    refine ⟨?_, ?_⟩
    · convert hf_pp using 2
      congr 1
      exact Subsingleton.elim _ _
    · convert hunr_pp using 2
      congr 1
      exact Subsingleton.elim _ _
  -- (12) unramifiedness of `P` over `𝔭`
  have hlies_P : P.asIdeal.LiesOver pp.asIdeal := ⟨by
    show pp.asIdeal = Ideal.under (𝓞 ↥L.L) P.asIdeal
    rw [show P.asIdeal = Ideal.under (𝓞 ↥N) Pt.asIdeal from rfl,
      Ideal.under_under (A := 𝓞 ↥L.L) (B := 𝓞 ↥N) (𝔓 := Pt.asIdeal),
      show pp.asIdeal = Ideal.under (𝓞 ↥L.L) Pt.asIdeal from rfl]⟩
  obtain ⟨hunr_P, -⟩ :=
    ramificationIdx_under_eq_one_and_eq_one (K := ↥L.L) (L := ↥N) (M := ↥M) Pt hunr_Pt
  -- (13) descent of the Frobenius element from `M` to `N`
  have hρfrob : IsFrobAt (K := ↥L.L) (L := ↥M) Pt ρ :=
    isFrobAt_of_isFrobAt_restrictScalars (K := ℚ) (L := ↥L.L) (M := ↥M) Pt ρ hf_pp hρ₀frob
  have hcommL : ∀ y : 𝓞 ↥N,
      galRestrict (𝓞 ↥L.L) ↥L.L ↥M (𝓞 ↥M) ρ (algebraMap (𝓞 ↥N) (𝓞 ↥M) y)
        = algebraMap (𝓞 ↥N) (𝓞 ↥M) (galRestrict (𝓞 ↥L.L) ↥L.L ↥N (𝓞 ↥N) τ y) :=
    galRestrict_commutes_of_field_commutes (L := ↥L.L) (N := ↥N) (M := ↥M)
      (ρ := ρ) (τ := τ) (fun x => by
        rw [← AlgEquiv.restrictNormal_commutes ρ ↥N x, hρ'])
  have hfcard : Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L))
      = Nat.card (𝓞 ↥L.L ⧸ Pt.asIdeal.under (𝓞 ↥L.L)) := by
    show Nat.card (𝓞 ↥L.L ⧸ Ideal.under (𝓞 ↥L.L)
          (Ideal.under (𝓞 ↥N) Pt.asIdeal))
        = Nat.card (𝓞 ↥L.L ⧸ Ideal.under (𝓞 ↥L.L) Pt.asIdeal)
    rw [Ideal.under_under]
  have hliesPt : Pt.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  have hfrobP : IsFrobAt (K := ↥L.L) (L := ↥N) P τ :=
    frobAt_descend_of_galRestrict_commutes (K := ↥L.L) (L := ↥L.L) (N := ↥N) (M := ↥M)
      hliesPt hρfrob hcommL hfcard
  exact ⟨pp, P, hlies_P, hsplit, hunr_P, hfrobP⟩

end NK.Reconstruct
