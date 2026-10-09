import Submission.Work.SSGRoute.ZDataMup.LangReexport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's theorem, converse direction: admissible `⟹` product condition

`NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe` (Lang's transfer, from Artin's lemma, at a fixed
modulus `m`, clean) gives the containment `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)` as soon as `m` is
*admissible* and every prime outside `(m)` is unramified.  Together with

* the index inequality `[L:K] ≤ [I(m) : P(m)·𝔑(m)]` (`NK.NUV2.ARL.Gap.langCyclicRelIndex`,
  cyclic `L/K`, admissible `m`) and
* the surjectivity of the Artin symbol on `I(m)`
  (`NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime`),

the two nested subgroups `ker ψ ∩ I(m)` and `P(m)·𝔑(m)` of `I(m)` have the same index `[L:K]` and
are therefore equal; hence `P(m) ⊆ ker ψ`, i.e. `NK.CFTLib.artinKillsPrincipal K L m`.

This is the converse of `Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal`: for a cyclic
extension, admissibility of a modulus containing the ramified primes is *equivalent* to the
product condition of the conductor theorem at that modulus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal

/-- **The Lang-Kernel assembly**: for a cyclic extension `L/K`, an admissible modulus `m` that
contains all the ramified primes satisfies the product condition `artinKillsPrincipal K L m` of
the conductor theorem (Lang, *Algebraic Number Theory*, X §2, Theorem 2). -/
theorem artinKillsPrincipal_of_isAdmissible
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (Gal(L/K))]
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    NK.CFTLib.artinKillsPrincipal K L m := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  -- the index inequality at `m`
  obtain ⟨hPNI, hIdxle⟩ := (NK.NUV2.ARL.Gap.langCyclicRelIndex K L) m hm hram hadm
  -- Lang's transfer at the fixed modulus `m`
  have hcont : ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym hcomm (A : FractionalIdeal (𝓞 K)⁰ K) = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
    fun A hcop hsym =>
      NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe K L m hm hadm hram A hcop hsym
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac K →* Gal(L/K) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
  let I : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m
  let PN : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m
  let J : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) := f.ker ⊓ I
  -- ## the kernel of the Artin symbol on `I(m)` is contained in `P(m)·𝔑(m)`
  have hJPN : J ≤ PN := by
    intro A hA
    have hAJ : A ∈ f.ker := (Subgroup.mem_inf.mp hA).1
    have hAI : A ∈ I := (Subgroup.mem_inf.mp hA).2
    have hkerA : f A = 1 := MonoidHom.mem_ker.mp hAJ
    have hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A :=
      (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff (K := K) m A).mp hAI
    refine hcont A hcop ?_
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] at hkerA
    exact hkerA
  -- ## the Artin symbol is surjective on `I(m)`
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAσ⟩ :=
      NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime (K := K) (L := L) m hm hram σ
    refine Subgroup.mem_map.mpr ⟨(A : NK.CFTLib.ArtinReciprocityIdeal.Frac K), A.2, ?_⟩
    simpa only [f, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hAσ
  have hcardI : f.ker.relIndex I = Nat.card (Gal(L/K)) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := Gal(L/K))).toEquiv
  -- ## `[I(m) : ker ∩ I(m)] = [L : K]`
  have hJrelI : J.relIndex I = Module.finrank K L := by
    rw [show J.relIndex I = f.ker.relIndex I from Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank K L]
  have hJI_ne : J.relIndex I ≠ 0 := by
    rw [hJrelI]
    exact (Module.finrank_pos (R := K) (M := L)).ne'
  -- ## `[I(m) : P(m)·𝔑(m)] = [L : K]` as well, so the two subgroups agree
  have hPNrelI : PN.relIndex I = Module.finrank K L := by
    refine le_antisymm ?_ hIdxle
    rw [← hJrelI]
    exact Subgroup.relIndex_le_of_le_left hJPN hJI_ne
  have hJrelPN : J.relIndex PN = 1 := by
    have h' : J.relIndex PN * PN.relIndex I = 1 * PN.relIndex I := by
      rw [Subgroup.relIndex_mul_relIndex J PN I hJPN hPNI, hJrelI, hPNrelI, one_mul]
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (by rw [hPNrelI, ← hJrelI]; exact hJI_ne)) h'
  have hPNJ : PN ≤ J := Subgroup.relIndex_eq_one.mp hJrelPN
  -- ## consequently the Artin symbol kills the principal ray
  have hPker : NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ≤ f.ker := by
    intro A hA
    exact (Subgroup.mem_inf.mp (hPNJ (Subgroup.mem_sup_left hA))).1
  -- ## translation into the product condition
  refine NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_of_artinSymbolKillsPrincipal
    m hram ?_
  intro a ha hpos
  rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_artinSym_spanSingleton
    (K := K) (L := L) (hcomm := hcomm) m hram a ha]
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : ((0 : 𝓞 K) : K) = 0 := by simp
    rw [h0, FractionalIdeal.spanSingleton_eq_zero_iff.mpr rfl]
    exact NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_zero hcomm
  · have haK : (a : K) ≠ 0 := by
      intro h
      exact ha0 (RingOfIntegers.coe_injective (by simpa [RingOfIntegers.coe_eq_algebraMap] using h))
    set u : Kˣ := Units.mk0 (a : K) haK with hu
    have huK : (u : K) = (a : K) := by rw [hu, Units.val_mk0]
    obtain ⟨c, hc⟩ : ∃ c : 𝓞 K, a - 1 = (m : 𝓞 K) * c := Ideal.mem_span_singleton.mp ha
    have hcu : (u : K) - 1 = (m : K) * (c : K) := by
      have h2 : (((a - 1 : 𝓞 K)) : K) = ((a : 𝓞 K) : K) - 1 := by push_cast; ring
      have h3 : (((a - 1 : 𝓞 K)) : K) = (((m : 𝓞 K)) : K) * ((c : 𝓞 K) : K) := by
        rw [hc]; push_cast; ring
      rw [huK, ← h2, h3]
      push_cast
      ring
    have hposu : ∀ (w : InfinitePlace K) (hw : w.IsReal),
        0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (u : K)) := by
      intro w hw
      have h1 := hpos ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.comp
        (algebraMap K w.Completion))
      rw [huK]
      exact h1
    have hcong : NK.CFTLib.ArtinReciprocityIdeal.CongrOne m u :=
      NK.CFTLib.ArtinReciprocityIdeal.congrOne_of_exists_mul m u c hcu hposu
    have hmemP : NK.CFTLib.ArtinReciprocityIdeal.spanUnit u ∈
        NK.CFTLib.ArtinReciprocityIdeal.principalRay K m :=
      Subgroup.subset_closure ⟨u, hcong, rfl⟩
    have hf1 : f (NK.CFTLib.ArtinReciprocityIdeal.spanUnit u) = 1 :=
      MonoidHom.mem_ker.mp (hPker hmemP)
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] at hf1
    have hcoe : ((NK.CFTLib.ArtinReciprocityIdeal.spanUnit u :
        NK.CFTLib.ArtinReciprocityIdeal.Frac K) : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K)) := by
      rw [NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit, huK]
    rw [hcoe] at hf1
    exact hf1

end Work.SSGRoute.ZDataMup
