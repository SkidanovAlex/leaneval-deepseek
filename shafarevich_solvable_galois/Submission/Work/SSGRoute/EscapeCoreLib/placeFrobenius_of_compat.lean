import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.EscapeCoreLib.isGalois_comap
import Submission.Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset
import Submission.Work.SSGRoute.EscapeCoreLib.algEquiv_extend_compositum
import Submission.Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split

/-!
# The escape place with the split condition, from the orthogonality

`Work.SSGRoute.EscapeCoreLib.exists_place_frobenius_of_compat` is the general Čebotarev step of
Grünwald-with-escape (node N2 of the Step-4 design), in the form in which the *escape* prime is
chosen over the base field `k`:

> `K/k` a finite Galois extension of number fields, `M/↥K` finite Galois, `N/k` finite Galois with
> `K ≤ N`, `α ∈ Gal(M/↥K)` whose restriction to `M ⊓ N` is the identity (the *orthogonality*
> hypothesis), `Bad` a finite set of places of `Ω`.  Then there is a finite place `Q` of `Ω`,
> `G_k`-conjugate to none of `Bad`, completely split in `N` over `k`, whose decomposition group
> contains `σ ∈ G_k` with `σ|_M = α`.

The construction is the one of `_NOTE_STEP4_DESIGN.md` (Step 4) and of
`PING_N2_orthogonality_and_galois_over_k.md` §2: choose a finite Galois extension `L/k` containing
`K`, `M`, `N`; inside `L`, transported to `↥K`-intermediate fields (`baseChange K L _`,
`IntermediateField.comap`), the hypothesis `α|_{M ⊓ N} = 1` is exactly the hypothesis of
`exists_algEquiv_restrict_eq_of_fixing`, which supplies `g ∈ Gal(L/↥K)` extending `α` and fixing
`N`; lifting `g` to `τ ∈ G_k` (`AlgEquiv.restrictNormalHom_surjective`) gives
`τ|_N = 1` and `τ|_M = α`, and Čebotarev with the split condition
(`Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`) produces the place `Q`.

Because `τ` fixes `N` over `k`, the place `Q` is completely split in `N/k`, and because it acts
as `α` on `M`, the Frobenius of the `↥K`-prime below `Q` in `M/↥K` is `α` — that is the
"prescribed Frobenius" clause which, together with the orthogonality, makes the escaping element
unramified outside the classes of `T` and of `Q`.
-/

open scoped Pointwise
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EscapeCoreLib

open _root_.SSGRoute

/-- **The escape place, given the orthogonality.**  See the module docstring. -/
theorem exists_place_frobenius_of_compat
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (Bad : Finset (ValuationSubring Ω))
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ N) → ((α x : ↥M) : Ω) = (x : Ω)) :
    ∃ Q : ValuationSubring Ω, SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ C ∈ Bad, ¬ SSGRoute.IsConjPlace k C Q) ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k Q ∧
        ∀ x : ↥M, σ (x : Ω) = ((α x : ↥M) : Ω) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  -- ### Step 1: a finite Galois extension of `k` containing `K`, `M` and `N`
  let Mk : IntermediateField k Ω := M.restrictScalars k
  have hMk : (Mk : Set Ω) = (M : Set Ω) := IntermediateField.coe_restrictScalars k (E := M)
  haveI : FiniteDimensional k Mk := by
    haveI : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
    exact ‹FiniteDimensional k ↥M›
  obtain ⟨L, hLd, hLg, hKL, hMLk, hNL⟩ := exists_finiteDimensional_galois_superset K Mk N
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  -- ### Step 2: view `M` and `N` as `↥K`-intermediate fields inside the finite Galois level `LK`
  let LK : IntermediateField ↥K Ω := baseChange K L hKL
  haveI htow_k_LK_Ω : IsScalarTower k ↥LK Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htow_k_K_LK : IsScalarTower k ↥K ↥LK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois k ↥LK := IsGalois.of_algEquiv (baseChangeAlgEquiv K L hKL)
  haveI : IsGalois ↥K LK := isGalois_baseChange K L hKL
  haveI : FiniteDimensional k ↥LK := finiteDimensional_baseChange K L hKL
  haveI : FiniteDimensional ↥K ↥LK := Module.Finite.of_restrictScalars_finite k ↥K ↥LK
  let NK : IntermediateField ↥K Ω := baseChange K N hKN
  haveI : IsGalois ↥K NK := isGalois_baseChange K N hKN
  haveI : FiniteDimensional k ↥NK := finiteDimensional_baseChange K N hKN
  haveI : FiniteDimensional ↥K ↥NK := Module.Finite.of_restrictScalars_finite k ↥K ↥NK
  have hMLK : M ≤ LK := fun x hx => (mem_baseChange K L hKL).mpr (hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx))
  have hNKLK : NK ≤ LK := fun x hx =>
    (mem_baseChange K L hKL).mpr (hNL ((mem_baseChange K N hKN).mp hx))
  let ML : IntermediateField ↥K ↥LK := M.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  let NL : IntermediateField ↥K ↥LK := NK.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  haveI : IsGalois ↥K ML := isGalois_comap_of_le_over K LK M hMLK
  haveI : IsGalois ↥K NL := isGalois_comap_of_le_over K LK NK hNKLK
  haveI : FiniteDimensional ↥K ↥ML :=
    FiniteDimensional.of_injective (comapAlgEquiv K LK M hMLK).symm.toLinearEquiv.toLinearMap
      (comapAlgEquiv K LK M hMLK).symm.injective
  haveI : FiniteDimensional ↥K ↥NL :=
    FiniteDimensional.of_injective (comapAlgEquiv K LK NK hNKLK).symm.toLinearEquiv.toLinearMap
      (comapAlgEquiv K LK NK hNKLK).symm.injective
  -- ### Step 3: extend `α` to a `↥K`-automorphism of `LK` fixing `NL`
  let e := comapAlgEquiv K LK M hMLK
  let α' : ↥ML ≃ₐ[↥K] ↥ML := e.symm.trans (α.trans e)
  have hα'fix : ∀ x : ↥ML, ((x : ↥LK) ∈ NL) → (((α' x : ↥ML) : ↥LK)) = (x : ↥LK) := by
    intro x hx
    refine Subtype.ext ?_
    have hxN : ((x : ↥LK) : Ω) ∈ NK := hx
    exact comapAlgEquiv_transport K LK M NK hMLK α
      (fun y hy => hαfix y ((mem_baseChange K N hKN).mp hy)) x hxN
  obtain ⟨g, hgML, hgNL⟩ :=
    exists_algEquiv_restrict_eq_of_fixing (K := ↥K) (L := ↥LK) ML NL α' hα'fix
  -- ### Step 4: lift the `↥K`-automorphism of `LK` to a `k`-automorphism `τ` of `Ω`
  let gk : ↥LK ≃ₐ[k] ↥LK := g.restrictScalars k
  have hgk_apply : ∀ y : ↥LK, gk y = g y := fun y => rfl
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥LK) (E := Ω) gk
  -- ### Step 5: `τ` fixes `N` pointwise, hence `res k N τ = 1`
  have hτN : SSGRoute.res k N τ = 1 := by
    rw [show SSGRoute.res k N τ = AlgEquiv.restrictNormalHom N τ from rfl,
      ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    -- goal: `τ x = x` in `Ω`
    have hxL : x ∈ L := hNL hx
    have hxLK : x ∈ LK := (mem_baseChange K L hKL).mpr hxL
    have hxNK : x ∈ NK := (mem_baseChange K N hKN).mpr hx
    have hxNL : (⟨x, hxLK⟩ : ↥LK) ∈ NL := hxNK
    have hτx : τ x = (((gk ⟨x, hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨x, hxLK⟩ : ↥LK) : Ω) = τ x :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨x, hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨x, hxLK⟩ = gk ⟨x, hxLK⟩ :=
        congrArg (fun f => f ⟨x, hxLK⟩) hτ
      rw [← h1, hy]
    have hgx : (((g ⟨x, hxLK⟩ : ↥LK)) : Ω) = x := by
      have h := congrArg (fun (z : ↥LK) => (z : Ω)) (hgNL _ hxNL)
      simpa using h
    rw [hτx, hgk_apply, hgx]
  -- ### Step 6: Čebotarev with the split condition
  obtain ⟨Q, hQfin, hQavoid, _hQunr, hQsplit, σ, hσdec, hσres⟩ :=
    Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split k Ω hc L N Bad τ hτN
  refine ⟨Q, hQfin, hQsplit, hQavoid, σ, hσdec, fun x => ?_⟩
  have hxL : (x : Ω) ∈ L := hMLk (by show (x : Ω) ∈ (Mk : Set Ω); rw [hMk]; exact x.2)
  have hxLK : (x : Ω) ∈ LK := (mem_baseChange K L hKL).mpr hxL
  -- `σ` and `τ` agree on `L`
  have hστ : σ (x : Ω) = τ (x : Ω) := by
    have h := congrArg (fun (f : ↥L ≃ₐ[k] ↥L) => (((f ⟨(x : Ω), hxL⟩ : ↥L)) : Ω)) hσres
    have h1 : ((((AlgEquiv.restrictNormalHom ↥L) σ) ⟨(x : Ω), hxL⟩ : ↥L) : Ω) = σ (x : Ω) :=
      AlgEquiv.restrictNormal_commutes σ ↥L ⟨(x : Ω), hxL⟩
    have h2 : ((((AlgEquiv.restrictNormalHom ↥L) τ) ⟨(x : Ω), hxL⟩ : ↥L) : Ω) = τ (x : Ω) :=
      AlgEquiv.restrictNormal_commutes τ ↥L ⟨(x : Ω), hxL⟩
    rw [h1, h2] at h
    exact h
  rw [hστ]
  -- `τ` and `gk` agree on `LK`
  have hτx : τ (x : Ω) = (((gk ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) := by
    have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨(x : Ω), hxLK⟩ : ↥LK) : Ω) = τ (x : Ω) :=
      AlgEquiv.restrictNormal_commutes τ ↥LK ⟨(x : Ω), hxLK⟩
    have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨(x : Ω), hxLK⟩ = gk ⟨(x : Ω), hxLK⟩ :=
      congrArg (fun f => f ⟨(x : Ω), hxLK⟩) hτ
    rw [← h1, hy]
  rw [hτx, hgk_apply]
  -- `g` on `ML` corresponds to `α'`
  have hzx : (((e x : ↥ML)) : ↥LK) = ⟨(x : Ω), hxLK⟩ := by
    refine Subtype.ext ?_
    rw [comapAlgEquiv_coe]
  have hgval : (((g ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) = ((((α' (e x) : ↥ML)) : ↥LK) : Ω) := by
    have h1 : g ⟨(x : Ω), hxLK⟩ = ((α' (e x) : ↥ML) : ↥LK) := by
      rw [← hzx]
      exact hgML (e x)
    exact congrArg (fun (z : ↥LK) => (z : Ω)) h1
  rw [hgval]
  -- the `Ω`-value of `α' (e x)` is that of `α x`
  have hα'x : α' (e x) = e (α x) := by
    simp only [α', AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [hα'x]
  exact comapAlgEquiv_coe K LK M hMLK (α x)

end Work.SSGRoute.EscapeCoreLib
