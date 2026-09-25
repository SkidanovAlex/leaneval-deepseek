import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_finite
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two
import Submission.NK.ChebotarevGeneral.exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

/-! ## Two elementary facts about Dirichlet density

Both are used in the proof of `exists_place_notMem_of_notMem_Lpow`. -/

/-- **Monotonicity of Dirichlet density.**  If `S ⊆ T` and both have a density, then the density
of `S` is at most that of `T`. -/
theorem hasDirichletDensity_mono {K : Type} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ ε : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ)
    (hT : NumberField.Set.HasDirichletDensity T ε) (hST : S ⊆ T) : δ ≤ ε := by
  rw [NumberField.Set.HasDirichletDensity] at hS hT
  refine le_of_tendsto_of_tendsto hS hT ?_
  filter_upwards [Filter.Tendsto.eventually_gt_atTop
      (Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT K) 0,
    self_mem_nhdsWithin] with s hpos hs
  exact div_le_div_of_nonneg_right
    (Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_mono hST hs) (le_of_lt hpos)

/-- **A set of primes with bounded Dirichlet series has Dirichlet density zero.** -/
theorem hasDirichletDensity_zero_of_bounded {K : Type} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (h : ∃ C : ℝ, ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum S s ≤ C) :
    NumberField.Set.HasDirichletDensity S 0 := by
  obtain ⟨C, hC⟩ := h
  rw [NumberField.Set.HasDirichletDensity]
  refine tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := max C 0) ?_ ?_
    (Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT K)
  · filter_upwards with s
    exact NumberField.Set.primeIdealZetaSum_nonneg S s
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact le_trans (hC s hs) (le_max_left _ _)

/-- **The inertia degree over the base field is the `inertiaDeg'` of the prime below.** -/
theorem inertiaDeg_eq_inertiaDeg'_under {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : NK.Chebotarev.PrimeIdeal L) :
    Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).inertiaDeg' Q.asIdeal := by
  haveI : Q.asIdeal.LiesOver (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal) :=
    (Ideal.liesOver_iff _ _).mpr rfl
  haveI : Q.asIdeal.IsMaximal := Q.isMaximal
  haveI : (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).IsMaximal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) Q]
    exact (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q).isMaximal
  exact (Ideal.inertiaDeg'_eq_inertiaDeg _ _).symm

/-- **The set of primes of `L` whose prime below is outside a prescribed finite set and whose
inertia degree is one has Dirichlet density one.** -/
theorem hasDirichletDensity_one_of_under_notMem_and_inertiaDeg' {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {Bad : Set (NK.Chebotarev.PrimeIdeal K)} (hBad : Bad.Finite) :
    NumberField.Set.HasDirichletDensity
      ({Q : NK.Chebotarev.PrimeIdeal L |
        Q ∈ Set.univ ∧
          (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).inertiaDeg' Q.asIdeal ∨
            IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q ∈ Bad)})ᶜ
      1 := by
  have hb := NK.ChebotarevGeneral.exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite
    (K := K) (M := L) Set.univ Bad hBad
  have h0 := hasDirichletDensity_zero_of_bounded hb
  have h := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl h0
  simpa using h


/-!
# A prime at which `b` is not a local `p`-th power, splitting completely in `L`

Let `L / K` be a finite Galois extension of number fields and `b ∈ K` an element which is not a
`p`-th power in `L`.  Then there is a finite prime `q` of `K`, outside a prescribed finite set `S`
containing the ramified primes, at which

* `q` splits completely in `L` (all primes above it are unramified of residue degree one), and
* `b` is not a `p`-th power in the completion `K_q`.

The proof is a *density* argument on the primes of `L` (`L` carries the Kummer extension
`F = L(b^{1/p})`, of degree `p` over `L` since `b` is not a `p`-th power in `L`):

* `X`, the primes of `L` that do **not** split completely in `F`, has Dirichlet density
  `1 - 1/p > 0`; by the local Kummer dichotomy (`localDeg_kummerField_eq_one_iff`), a prime of `L`
  outside `X` is exactly one at which `b` *is* a local `p`-th power;
* `Y`, the primes of `L` whose prime below is outside `S` and whose residue degree over `K` is
  `1`, has Dirichlet density `1`: the primes of residue degree `≥ 2` contribute a bounded Dirichlet
  series (`NK.ChebotarevGeneral.exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite`) and
  the primes above `S` are finite;
* two subsets of the primes of `L` of densities `> 0` and `1` must meet (monotonicity of the
  Dirichlet density).

For `Q ∈ X ∩ Y` the prime `q = Q ∩ K` lies outside `S` by construction, is unramified in `L` by
the hypothesis on `S`, and has residue degree one at `Q`; since `L/K` is Galois this forces `f = 1`
at *every* prime above `q`, so `q` splits completely.  Finally `b ∉ L_Q^{×p}` (by `Q ∈ X`), and
`L_Q = K_q` because `e = f = 1` at `Q`, whence `b ∉ K_q^{×p}`.

Note that the hypotheses `hcard`, `hSp`, `hSinf`, `hbS` are not needed: the argument uses only the
\(`p\)-th power)\) hypothesis `hbl` and the ramification hypothesis `hSram`.
-/

theorem exists_place_notMem_of_notMem_Lpow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (hSram : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal ∧
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) → NK.GlobalCFT.Place.ofFinite q ∈ S)
    {b : K} (hb : b ≠ 0) (hbS : Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (S : Set (NK.GlobalCFT.Place K)))
    (hbl : ¬ ∃ β : L, β ^ p = algebraMap K L b) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧ Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ∧
      (¬ ∃ c : (q.adicCompletion K)ˣ,
        algebraMap K (q.adicCompletion K) b = ((c : (q.adicCompletion K)ˣ) : q.adicCompletion K) ^ p) := by
  classical
  -- ## Step 1: the degree of `L / K`
  have hfinKL : Module.finrank K L = p := by
    rw [← IsGalois.card_aut_eq_finrank K L, hcard]
  have hp2 : 2 ≤ p := hp.two_le
  -- ## Step 2: the Kummer extension `F = L(b^{1/p})` in a separable closure of `L`
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (RingHom.injective (algebraMap K L))
  let bL : Lˣ := Units.map (algebraMap K L).toMonoidHom (Units.mk0 b hb)
  have hble : (bL : L) = algebraMap K L b := rfl
  have hbL : bL ∉ NK.LocalAnabelian.powSubgroup p L := by
    rw [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range]
    rintro ⟨u, hu⟩
    apply hbl
    refine ⟨(u : L), ?_⟩
    have h2 := congrArg (fun v : Lˣ => (v : L)) hu
    rw [powMonoidHom_apply] at h2
    simpa [hble] using h2
  haveI : IsSepClosure L (SeparableClosure L) :=
    separableClosure.isSepClosure L (AlgebraicClosure L)
  let F : IntermediateField L (SeparableClosure L) :=
    NK.LocalAnabelian.kummerField (K' := SeparableClosure L) p bL
  have hKummerF := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
    (K' := SeparableClosure L) p hp hζL bL hbL
  haveI : IsGalois L ↥F := hKummerF.1
  have hfinFL : Module.finrank L ↥F = p := hKummerF.2
  haveI : FiniteDimensional L ↥F :=
    Module.finite_of_finrank_pos (R := L) (M := ↥F) (by rw [hfinFL]; exact hp.pos)
  haveI : NumberField ↥F :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField F
  -- ## Step 3: `X`, the primes of `L` at which `b` is not a local `p`-th power
  set X : Set (NK.Chebotarev.PrimeIdeal L) :=
    {Q | ¬ NK.UchidaKummer.SplitsCompletely (K := L) (L := ↥F) Q} with hXdef
  have hsplitF : NumberField.Set.HasDirichletDensity
      {Q : NK.Chebotarev.PrimeIdeal L |
        (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥F)).ncard = Module.finrank L ↥F}
      (1 / (p : ℝ)) := by
    have h := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
      (K := L) (L := ↥F)
    rw [hfinFL] at h ⊢
    exact h
  have hsplitF' : NumberField.Set.HasDirichletDensity
      {Q : NK.Chebotarev.PrimeIdeal L |
        NK.UchidaKummer.SplitsCompletely (K := L) (L := ↥F) Q} (1 / (p : ℝ)) :=
    hsplitF
  have hX : NumberField.Set.HasDirichletDensity X (1 - 1 / (p : ℝ)) := by
    have h := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hsplitF'
    simpa [X, Set.compl_setOf] using h
  -- ## Step 4: `Y`, the primes of `L` with under-prime outside `S` and inertia degree one
  set Bad : Set (NK.Chebotarev.PrimeIdeal K) :=
    {q | NK.GlobalCFT.Place.ofFinite q ∈ S} with hBaddef
  have hBadFin : Bad.Finite := by
    rw [hBaddef]
    refine Set.Finite.preimage ?_ S.finite_toSet
    intro q _ q' _ h
    exact Place.ofFinite_inj.mp h
  set BadSet : Set (NK.Chebotarev.PrimeIdeal L) :=
    {Q | Q ∈ Set.univ ∧
      (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).inertiaDeg' Q.asIdeal ∨
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q ∈ Bad)}
    with hBadSetdef
  have hY : NumberField.Set.HasDirichletDensity BadSetᶜ 1 :=
    hasDirichletDensity_one_of_under_notMem_and_inertiaDeg' (K := K) (L := L) hBadFin
  -- ## Step 5: the two sets meet
  have hne : (X ∩ BadSetᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : BadSetᶜ ⊆ Xᶜ := by
      intro Q hQ
      rw [Set.mem_compl_iff]
      intro hQX
      exact Set.notMem_empty Q (h ▸ Set.mem_inter hQX hQ)
    have hXcompl := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hX
    have hle := hasDirichletDensity_mono hY hXcompl hsub
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hhalf : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hpR
    have hcalc : (1 : ℝ) - (1 - 1 / (p : ℝ)) = 1 / (p : ℝ) := by ring
    linarith
  obtain ⟨Q, hQX, hQY⟩ := hne
  have hQXs : ¬ NK.UchidaKummer.SplitsCompletely (K := L) (L := ↥F) Q := by
    simpa [X] using hQX
  have hQY' : ¬ (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).inertiaDeg'
        Q.asIdeal) ∧
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q ∉ Bad := by
    have h := hQY
    simp only [Set.mem_compl_iff, hBadSetdef, Set.mem_setOf_eq, Set.mem_univ, true_and,
      not_or] at h
    exact h
  -- ## Step 6: the prime below
  haveI hGalGroup : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  set q : NK.Chebotarev.PrimeIdeal K :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q with hqdef
  have hq_asIdeal : q.asIdeal = Q.asIdeal.under (NumberField.RingOfIntegers K) := by
    rw [hqdef, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  have hQlies : Q.asIdeal.LiesOver q.asIdeal := (Ideal.liesOver_iff _ _).mpr hq_asIdeal
  haveI : Q.asIdeal.LiesOver q.asIdeal := hQlies
  have hqS : NK.GlobalCFT.Place.ofFinite q ∉ S := by
    simpa [q, hBaddef] using hQY'.2
  -- the inertia degree of `q` is one
  have hbridge := inertiaDeg_eq_inertiaDeg'_under (K := K) (L := L) Q
  have hdegQ : Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
    have hpos : 0 < Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      Ideal.inertiaDeg_pos Q.asIdeal (NumberField.RingOfIntegers K)
    have hfpos : 0 < (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal).inertiaDeg'
        Q.asIdeal := by rwa [← hbridge]
    omega
  have hdegIn : q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers L) q.asIdeal Q.asIdeal (Gal(L/K)), hdegQ]
  -- ## Step 7: `b` is not a `p`-th power at `q`
  have hlocal : ¬ ∃ c : (Q.adicCompletion L)ˣ,
      algebraMap L (Q.adicCompletion L) (bL : L) = (c : Q.adicCompletion L) ^ p := by
    intro h
    refine hQXs ((NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
      (K := L) (L := ↥F) Q).mpr ?_)
    refine (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := L)
      (K' := SeparableClosure L) p hp hζL bL F rfl Q).mpr ?_
    exact h
  -- ## Conclusion
  refine ⟨q, hqS, ?_, ?_⟩
  · intro Q' hQ'
    refine ⟨?_, ?_⟩
    · by_contra he
      exact hqS (hSram q ⟨Q', hQ', he⟩)
    · haveI : Q'.asIdeal.LiesOver q.asIdeal := hQ'
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers L) q.asIdeal Q'.asIdeal (Gal(L/K))]
      exact hdegIn
  · rintro ⟨c, hc⟩
    -- the image of `c` in the completion of `L` at `Q` is a unit whose `p`-th power is the
    -- image of `b`
    letI : Algebra (q.adicCompletion K) (Q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies)
    haveI hST : IsScalarTower K (q.adicCompletion K) (Q.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion q Q hQlies
    set c' : Q.adicCompletion L :=
      Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies (c : q.adicCompletion K)
      with hc'def
    have hc'0 : c' ≠ 0 := by
      rw [hc'def]
      intro h0
      have h1 : (c : q.adicCompletion K) = 0 :=
        RingHom.injective (Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies)
          (by simpa using h0)
      exact Units.ne_zero c h1
    have hkey : algebraMap L (Q.adicCompletion L) (bL : L) =
        ((Units.mk0 c' hc'0 : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) ^ p := by
      have h1 : algebraMap L (Q.adicCompletion L) (bL : L) =
          algebraMap K (Q.adicCompletion L) b := by
        rw [hble, ← IsScalarTower.algebraMap_apply K L (Q.adicCompletion L) b]
      have h2 : algebraMap K (Q.adicCompletion L) b =
          Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies
            (algebraMap K (q.adicCompletion K) b) := by
        rw [IsScalarTower.algebraMap_apply K (q.adicCompletion K) (Q.adicCompletion L) b,
          RingHom.algebraMap_toAlgebra]
      have h3 : Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies
            (algebraMap K (q.adicCompletion K) b) = c' ^ p := by
        rw [hc, map_pow, hc'def]
      calc algebraMap L (Q.adicCompletion L) (bL : L)
          = algebraMap K (Q.adicCompletion L) b := h1
        _ = Commons.RingTheory.Henselian.adicCompletionMap q Q hQlies
              (algebraMap K (q.adicCompletion K) b) := h2
        _ = c' ^ p := h3
        _ = ((Units.mk0 c' hc'0 : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) ^ p := rfl
    exact hlocal ⟨Units.mk0 c' hc'0, hkey⟩


end NK.GlobalCFTdeep.SecondInequality.KummerCase
