import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.hasse_open
import Submission.NK.NUV2.LC.RouteB.kill_one_place
import Submission.NK.NUV2.LC.RouteB.res_surjective_open
import Submission.NK.NUV2.LC.RouteB.loc_smul_eq_zero_iff
import Submission.NK.NUV2.LC.RouteB.live_places_one_orbit_of_hasseSurj
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist
import Submission.NK.NUV2.LC.RouteB.finite_support_isMuOpen

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NUV2/LC/RouteB/DESIGN_containment_v3.md first (the orchestrator's redesign of decompContainment_B; your lemma is one node). Never use the circular le_stabSubgroup_of_localType, SurjTwo/HasseTwo/ABHNSurjectivity shapes. hFC and hKC are PROVED (NK.CFTLib.fundamentalClassElement, NK.NUV2.kernelCondition_all).

# exists_loc_ne_zero_of_isClosed (S3: the core of Claim E)

**Target file** `RouteB/exists_loc_ne_zero_of_isClosed.lean`. Imports: `Submission.NK.NUV2.LC.RouteB.Defs`,
`Submission.NK.NUV2.LC.RouteB.hasse_open`, `Submission.NK.NUV2.LC.RouteB.kill_one_place`,
`Submission.NK.NUV2.LC.RouteB.res_surjective_open`, `Submission.NK.NUV2.LC.RouteB.loc_smul_eq_zero_iff`,
`Submission.NK.NUV2.LC.RouteB.finite_support_isMuOpen`, `Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap`,
`Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq`, `Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist`.

This is the Hasse principle at a CLOSED `μ_p`-level, obtained as a limit of the open-level Hasse
principle. It is **not** containment-strength: `NOTES_live_place_exists.md` and the docstring of
`exists_live_place_of_localType.lean` are wrong on this point. The "coherence of level-wise places"
they call missing is exactly what the compactness argument below supplies.

**Proof.**
1. **Lift.** `res_surjective_open` (with `U := rootFix ζ`, which is open) gives an open `U₀` with
   `V ≤ U₀ ≤ rootFix ζ` and `x₀` with `res x₀ = x`. Let `𝒰` be the open subgroups `U` with
   `V ≤ U ≤ U₀`; the family is directed under `⊓`. Put `x_U := res_{U₀→U} x₀`. Then `x_U ≠ 0`, because
   `res_{U→V} x_U = x` (`OddTwist.H2Profinite_res_comp`).
2. **Hasse at each level.** `hasse_open p hp hp2 ζ hζ U ⟨hUopen, hU≤rootFix⟩ x_U` gives some `A` with
   `loc_A x_U ≠ 0`. Since `loc_A x_U = res(loc_A x₀)` (`loc_eq_res` + `res_comp`), also
   `loc_A x₀ ≠ 0`. So the prime of `A` lies in the finite set `T` of S2 for `x₀`.
3. **One prime.** Let `T(U) ⊆ T` be the primes carrying a place `A` with `loc_A x_U ≠ 0`. These sets are
   nonempty and antitone. `T` is finite and `𝒰` is directed, so some `𝔭` lies in every `T(U)`: if
   not, the infimum of finitely many witnesses `U_𝔮` would have `T = ∅`.
4. **One place.** Fix a place `B` over `𝔭` and put `Y(U) := {g ∈ Gal(K'/K) | loc_{g•B} x_U ≠ 0}`.
   - `Y(U)` is nonempty: every `A` over `𝔭` is `g • B` (`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq`).
   - `Y(U)` is clopen: `u ∈ U` gives `loc_{(u g)•B} x_U = 0 ↔ loc_{g•B} x_U = 0` (`loc_smul_eq_zero_iff`),
     so `Y(U)` and its complement are unions of cosets `U·g`.
   - `Y` is antitone and directed.

   Compactness (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) gives
   `g ∈ ⋂ Y(U)`. Put `A := g • B`.
5. **Conclude.** Suppose `loc_A x = loc_A (res x₀) = 0`. Then `kill_one_place` (with `W := U₀`,
   `Y := x₀`) gives an open `W'` with `V ≤ W' ≤ U₀` and `loc_A (res_{U₀→W'} x₀) = 0`. That says
   `g ∉ Y(W')`, a contradiction.

**Sanity checks.**
- `K = ℚ`, `p = 3`, `V = rootFix ζ₃` (open): this is classical Hasse.
- `V = D_A ⊓ rootFix` with `A | 7`: `loc_A = id`.
- `V = ⊥`: `H² = 0`, so the statement is vacuous.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse (stabSubgroup H2Profinite OverFinitePrime)

/-- A left-`U`-invariant subset of a topological group, `U` open, is clopen. -/
lemma isClopen_of_left_invariant {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U : Subgroup G} (hU : IsOpen (U : Set G)) {S : Set G}
    (hS : ∀ g ∈ S, ∀ u ∈ U, u * g ∈ S) : IsOpen S ∧ IsClosed S := by
  have hcompl : ∀ g : G, g ∉ S → ∀ u ∈ U, u * g ∉ S := by
    intro g hg u hu h
    apply hg
    have h1 : u⁻¹ * (u * g) ∈ S := hS (u * g) h u⁻¹ (U.inv_mem hu)
    rwa [inv_mul_cancel_left] at h1
  have hkey : ∀ T : Set G, (∀ g ∈ T, ∀ u ∈ U, u * g ∈ T) →
      T = ⋃ g ∈ T, Set.image (fun x : G => x * g) (U : Set G) := by
    intro T hT
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
      exact ⟨1, U.one_mem, by simp⟩
    · intro hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨g, hg, hxg⟩ := hx
      rw [Set.mem_image] at hxg
      obtain ⟨u, hu, hux⟩ := hxg
      rw [← hux]
      exact hT g hg u hu
  have hopen : ∀ g : G, IsOpen (Set.image (fun x : G => x * g) (U : Set G)) :=
    fun g => (Homeomorph.mulRight g).isOpenMap _ hU
  constructor
  · rw [hkey S hS]
    exact isOpen_iUnion (fun g => isOpen_iUnion (fun _ => hopen g))
  · rw [← isOpen_compl_iff, hkey Sᶜ (fun g hg u hu => hcompl g hg u hu)]
    exact isOpen_iUnion (fun g => isOpen_iUnion (fun _ => hopen g))

/-- **Claim E core (Hasse principle at a closed level).** -/
theorem exists_loc_ne_zero_of_isClosed (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (V : Subgroup Gal(K'/K)) (hVcl : IsClosed (V : Set Gal(K'/K)))
    (hVζ : V ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ)
    (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) (hx : x ≠ 0) :
    ∃ A : NK.BrauerHasse.OverFinitePrime K K', NK.BrauerHasse.H2Profinite.loc p V x A ≠ 0 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsGalois K K' := IsSepClosure.isGalois
  -- ## 1. lift `x` to an open `μ_p`-level `U₀`
  have hrootOpen : IsOpen (rootFix (K := K) (K' := K') ζ : Set Gal(K'/K)) :=
    isOpen_rootFix p hp ζ hζ
  obtain ⟨U₀, hU₀open, hVU₀, hU₀root, x₀, hx₀⟩ :=
    res_surjective_open (K := K) (K' := K') p (U := rootFix (K := K) (K' := K') ζ)
      hrootOpen hVζ x
  have hx₀L : NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p hVU₀ x₀ = x := by
    rw [show NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p hVU₀ x₀ =
      res (K := K) (K' := K') p hVU₀ x₀ from rfl]
    exact hx₀
  have hx₀_ne : x₀ ≠ 0 := by
    intro h0
    exact hx (by
      rw [← hx₀, h0]
      exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p _)
  -- ## 2. the index type: open subgroups `U` with `V ≤ U ≤ U₀`
  let ι := {U : Subgroup Gal(K'/K) // IsOpen (U : Set Gal(K'/K)) ∧ V ≤ U ∧ U ≤ U₀}
  haveI : Nonempty ι := ⟨⟨U₀, hU₀open, hVU₀, le_rfl⟩⟩
  let xU : (U : ι) → NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (U : Subgroup Gal(K'/K)) :=
    fun U => NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p U.2.2.2 x₀
  have hxU_ne : ∀ U : ι, xU U ≠ 0 := by
    intro U h0
    have hcomp := NK.NUV2.LC.OddTwist.H2Profinite_res_comp (K := K) (K' := K') p
      (W := U₀) (U := (U : Subgroup Gal(K'/K))) (V := V) U.2.2.1 U.2.2.2 x₀
    have h2 : NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p U.2.2.1 (xU U) =
        NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p hVU₀ x₀ := by
      rw [show xU U = NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p
        U.2.2.2 x₀ from rfl, hcomp]
    have h3 : NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p U.2.2.1 (xU U)
        = 0 := by
      rw [h0]; exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p _
    rw [h2, hx₀L] at h3
    exact hx h3
  -- ## 3. the finite support `T` of `x₀`
  set T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    {𝔭 | ∃ A : NK.BrauerHasse.OverFinitePrime K K',
      A.1.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧
      NK.BrauerHasse.H2Profinite.loc p U₀ x₀ A ≠ 0} with hTdef
  have hTfin : T.Finite := by
    rw [hTdef]
    exact finite_support_isMuOpen (K := K) (K' := K') p hp hp2 ζ hζ U₀
      ⟨hU₀open, hU₀root⟩ x₀
  have hTne : T.Nonempty := by
    by_contra h
    have hzero : ∀ A : NK.BrauerHasse.OverFinitePrime K K',
        NK.BrauerHasse.H2Profinite.loc p U₀ x₀ A = 0 := by
      intro A
      by_contra hA
      apply h
      obtain ⟨𝔭, h𝔭⟩ :=
        NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A.1 A.2
      exact ⟨𝔭, A, h𝔭, hA⟩
    exact hx₀_ne (hasse_open p hp hp2 ζ hζ U₀ ⟨hU₀open, hU₀root⟩ x₀ hzero)
  haveI hTfintype : Fintype ↥T := hTfin.fintype
  let eT : ↥T ≃ Fin (Fintype.card ↥T) := Fintype.equivFin ↥T
  -- base place over each prime of `T`
  have hbases : ∀ i : Fin (Fintype.card ↥T), ∃ A : NK.BrauerHasse.OverFinitePrime K K',
      A.1.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K (eT.symm i).1 :=
    fun i => (eT.symm i).2.imp (fun _ h => h.1)
  choose B hB using hbases
  -- ## 4. the parameter sets
  let Aof : Fin (Fintype.card ↥T) → Gal(K'/K) → NK.BrauerHasse.OverFinitePrime K K' :=
    fun i g => ⟨g • (B i).1, by
      rw [NK.LocalDecomposition.comap_smul]
      exact (B i).2⟩
  let C : ι → Fin (Fintype.card ↥T) → Set Gal(K'/K) :=
    fun U i => {g | NK.BrauerHasse.H2Profinite.loc p (U : Subgroup Gal(K'/K)) (xU U)
      (Aof i g) ≠ 0}
  have hCmem : ∀ (U : ι) (i : Fin (Fintype.card ↥T)) (g : Gal(K'/K)),
      (g ∈ C U i) ↔ (NK.BrauerHasse.H2Profinite.loc p (U : Subgroup Gal(K'/K)) (xU U)
        (Aof i g) ≠ 0) := fun U i g => Iff.rfl
  let Y : ι → Set (Fin (Fintype.card ↥T) × Gal(K'/K)) :=
    fun U => ⋃ i : Fin (Fintype.card ↥T), ({i} : Set (Fin (Fintype.card ↥T))) ×ˢ (C U i)
  have hYU : ∀ U : ι, Y U = ⋃ i : Fin (Fintype.card ↥T),
      ({i} : Set (Fin (Fintype.card ↥T))) ×ˢ (C U i) := fun U => rfl
  have hCinv : ∀ (U : ι) (i : Fin (Fintype.card ↥T)), ∀ g ∈ C U i,
      ∀ u ∈ (U : Subgroup Gal(K'/K)), u * g ∈ C U i := by
    intro U i g hg u hu
    rw [hCmem] at hg ⊢
    have hA : Aof i (u * g) = u • (Aof i g) := by
      refine Subtype.ext ?_
      show (u * g) • (B i).1 = (u • (Aof i g)).1
      rw [smul_OverFinitePrime_val]
      exact mul_smul u g (B i).1
    rw [hA]
    intro h0
    exact hg ((loc_smul_eq_zero_iff (K := K) (K' := K') p (W := (U : Subgroup Gal(K'/K)))
      hu (xU U) (Aof i g)).mp h0)
  have hCcl : ∀ (U : ι) (i : Fin (Fintype.card ↥T)), IsClosed (C U i) :=
    fun U i => (isClopen_of_left_invariant (U := (U : Subgroup Gal(K'/K))) U.2.1
      (hCinv U i)).2
  have hYcl : ∀ U : ι, IsClosed (Y U) := by
    intro U
    rw [hYU U]
    exact isClosed_iUnion_of_finite (fun i => IsClosed.prod isClosed_singleton (hCcl U i))
  have hYne : ∀ U : ι, (Y U).Nonempty := by
    intro U
    by_contra h
    have hloc : ∀ A : NK.BrauerHasse.OverFinitePrime K K',
        NK.BrauerHasse.H2Profinite.loc p (U : Subgroup Gal(K'/K)) (xU U) A = 0 := by
      intro A
      by_contra hA
      apply h
      obtain ⟨𝔭, h𝔭⟩ :=
        NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A.1 A.2
      have hlocU₀ : NK.BrauerHasse.H2Profinite.loc p U₀ x₀ A ≠ 0 := by
        intro h0
        apply hA
        have hlr := loc_res (K := K) (K' := K') p (U := U₀) (V := (U : Subgroup Gal(K'/K)))
          U.2.2.2 A (inf_le_inf_right (stabSubgroup A.1) U.2.2.2) x₀
        rw [show xU U = NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p
          U.2.2.2 x₀ from rfl, hlr, h0]
        exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p _
      have h𝔭T : 𝔭 ∈ T := by
        rw [hTdef]
        exact ⟨A, h𝔭, hlocU₀⟩
      have hBeq : (B (eT ⟨𝔭, h𝔭T⟩)).1.comap (algebraMap K K') = A.1.comap (algebraMap K K') := by
        rw [hB (eT ⟨𝔭, h𝔭T⟩), eT.symm_apply_apply, h𝔭]
      obtain ⟨g, hg⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := K) (E := K')
        (B (eT ⟨𝔭, h𝔭T⟩)).1 A.1 hBeq
      refine ⟨(eT ⟨𝔭, h𝔭T⟩, g), ?_⟩
      rw [hYU U, Set.mem_iUnion]
      refine ⟨eT ⟨𝔭, h𝔭T⟩, ?_⟩
      rw [Set.mem_prod]
      refine ⟨rfl, ?_⟩
      rw [hCmem]
      have hAi : Aof (eT ⟨𝔭, h𝔭T⟩) g = A := Subtype.ext hg
      rw [hAi]
      exact hA
    exact hxU_ne U (hasse_open p hp hp2 ζ hζ (U : Subgroup Gal(K'/K))
      ⟨U.2.1, fun y hy => hU₀root (U.2.2.2 hy)⟩ (xU U) hloc)
  -- ## 5. the compactness step
  have hxU_comp : ∀ (U U' : ι) (h : (U' : Subgroup Gal(K'/K)) ≤ (U : Subgroup Gal(K'/K))),
      NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p h (xU U) = xU U' := by
    intro U U' h
    rw [show xU U = NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p
      U.2.2.2 x₀ from rfl,
      NK.NUV2.LC.OddTwist.H2Profinite_res_comp (K := K) (K' := K') p h U.2.2.2 x₀]
  have hYanti : ∀ (U U' : ι), (U' : Subgroup Gal(K'/K)) ≤ (U : Subgroup Gal(K'/K)) →
      Y U' ⊆ Y U := by
    intro U U' hle a ha
    rw [hYU U', Set.mem_iUnion] at ha
    obtain ⟨i, ha⟩ := ha
    rw [Set.mem_prod] at ha
    obtain ⟨ha1, ha2⟩ := ha
    rw [hYU U, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_prod]
    refine ⟨ha1, ?_⟩
    rw [hCmem] at ha2 ⊢
    intro hzero
    apply ha2
    have hlr := loc_res (K := K) (K' := K') p (U := (U : Subgroup Gal(K'/K)))
      (V := (U' : Subgroup Gal(K'/K))) hle (Aof i a.2) (inf_le_inf_right _ hle) (xU U)
    rw [← hxU_comp U U' hle, hlr, hzero]
    exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p _
  have hYdir : Directed (· ⊇ ·) Y := by
    intro U₁ U₂
    let U₃ : ι := ⟨(U₁ : Subgroup Gal(K'/K)) ⊓ (U₂ : Subgroup Gal(K'/K)),
      U₁.2.1.inter U₂.2.1, le_inf U₁.2.2.1 U₂.2.2.1,
      inf_le_left.trans U₁.2.2.2⟩
    refine ⟨U₃, ?_, ?_⟩
    · exact hYanti U₁ U₃ inf_le_left
    · exact hYanti U₂ U₃ inf_le_right
  obtain ⟨q₀, hq₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    Y hYdir (fun U => hYne U) (fun U => (hYcl U).isCompact) (fun U => hYcl U)
  obtain ⟨i₀, g₀⟩ := q₀
  have hlive : ∀ U : ι, NK.BrauerHasse.H2Profinite.loc p (U : Subgroup Gal(K'/K)) (xU U)
      (Aof i₀ g₀) ≠ 0 := by
    intro U
    have h1 : (i₀, g₀) ∈ Y U := Set.mem_iInter.mp hq₀ U
    rw [hYU U, Set.mem_iUnion] at h1
    obtain ⟨i, h1⟩ := h1
    rw [Set.mem_prod] at h1
    obtain ⟨h1a, h1b⟩ := h1
    rw [Set.mem_singleton_iff] at h1a
    subst h1a
    rwa [hCmem] at h1b
  -- ## 6. conclude by killing one place
  refine ⟨Aof i₀ g₀, fun hVzero => ?_⟩
  obtain ⟨W', hVW', hW'U₀, hW'open, hkill⟩ :=
    kill_one_place p V U₀ hVcl hU₀open hVU₀ x₀ (Aof i₀ g₀)
      (by rw [hx₀]; exact hVzero)
  rw [show NK.NUV2.LC.RouteB.res (K := K) (K' := K') p hW'U₀ x₀ =
    NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p hW'U₀ x₀ from rfl] at hkill
  exact hlive ⟨W', hW'open, hVW', hW'U₀⟩ (by
    rw [show xU ⟨W', hW'open, hVW', hW'U₀⟩ =
      NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') p hW'U₀ x₀ from rfl]
    exact hkill)

end NK.NUV2.LC.RouteB
