import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_diagonal
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.antiInvariantPairingAux
import Submission.Work.SSGRoute.NodeS37.pinnedValueOfHistoryOfInertSquare
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.antiInvariantDichotomy
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_coprime_representative_two
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_sum_attach_eq_zero_of_kills
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup_right
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsLocalGroup_of_one_unit
import Submission.Work.SSGRoute.NodeS37.divisorOfClassRepresentative
import Submission.Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime
import Submission.Work.SSGRoute.NodeS37.oddCountAtEscape
import Submission.Work.SSGRoute.NodeS37.killsLocalGroupAtSBlockConj
import Submission.Work.SSGRoute.NodeS37.oPairAt_eq_zero_of_even_count
import Submission.Work.SSGRoute.NodeS37.localDichotomy
import Submission.Work.SSGRoute.ZConstruction.OThetaLocalNorm
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ZConstruction.UnramifiedLocalNorm
import Submission.Work.SSGRoute.ZConstruction.DichotomyKills
import Submission.Work.SSGRoute.ZConstruction.HCharMulSq
import Submission.Work.SSGRoute.ZConstruction.exists_finset_covering_notUnit
import Submission.Work.SSGRoute.ZConstruction.isSquare_adicCompletion_of_inert
import Submission.Work.SSGRoute.PinnedTwin.oPairAtPairEqZero
import Submission.Work.SSGRoute.PinnedTwin.divisorRepresentative
import Submission.Work.SSGRoute.ZConstruction.twinDivisorConsequences
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
import Submission.Work.SSGRoute.P2Nat.oPairAt_smul_conj
import Submission.Work.SSGRoute.H9.swCount_conjUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `TwoRec.pinnedValue_diagonal_proved` — the p. 16 arithmetic core, proved

This is the (statement-identical) proved version of `TwoRec.pinnedValue_diagonal`, the arithmetic
core of Schmidt--Wingberg's p. 16 computation for the corrected `p = 2` §4 recursion.

## The shape of the proof (see `NOTE_pinnedValue_diagonal_proved_state.md`)

`V := pinValue … 0 ρ = oPairAt A (χ_b)(χ_{ρb})` by the dictionary `claimOfPreTwo_dictionary`
(`A := galLift K ρ • Q` the sibling).  The divisor of `b` is `𝔮 · (ideal)²` (`evenCountAtNonEscapePrime`
+ the odd clause of `PreTwo`), so Čebotarev (`exists_prime_in_class_not_fixed`, via
`PinnedTwin.divisorRepresentative`) gives `z = b y²` with `div z = 𝔮 Q'²`, `Q' ≠ ρQ'`, `Q' ≠ ρ𝔮`.

Put `X := z - ρz`, `a := (z + ρz)/2`.  The multi-place product formula
`oPairAt_sum_attach_eq_zero_of_kills` for the pair `(ρz, X)` over a `ρ`-stable finite set `T'` of
places (one per `K`-prime of `supp X ∪ supp 2 ∪ {𝔮, ρ𝔮}`), with the dictionary at the sibling,
gives `V = 0`: every other term of the sum vanishes, either individually (dyadic/ramified primes via
`claimOfPreTwo_squareAtSBlock` + `killsLocalGroupAtSBlockConj`; a `ρ`-fixed prime dividing `X` via
the inert squareness `isSquare_adicCompletion_of_inert`; primes where `X` is a unit via the even-count
dictionary) or in `ρ`-pairs (the `ρ`-split primes via `oPairAtPairEqZero`).
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

theorem pinnedValue_diagonal_proved {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (m : ℕ) (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1) :
    Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 ρ = 0 := by
  classical
  -- ## 0. The bookkeeping clauses of the prefix invariant at stage `m + 1`.
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  set Q : ValuationSubring Ω := (s.f m).1 with hQdef
  set b : (↥K)ˣ := (s.f m).2 with hbdef
  have hQfin : SSGRoute.IsFinPlace k Q := hfin m hm
  have hQsplitΛ : SSGRoute.IsSplitIn k Λ Q := hsplit m hm
  have hQsplitK : SSGRoute.IsSplitIn k K Q :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ hQsplitΛ
  -- the sibling place
  set A : ValuationSubring Ω := Work.SSGRoute.ZDataMup.galLift K ρ • Q with hAdef
  have hAfin : SSGRoute.IsFinPlace k A :=
    (SSGRoute.isFinPlace_smul_iff Q (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hQfin
  have hAsib : Work.SSGRoute.ZDataMup.siblingPlace K ρ Q = A := rfl
  have hsep : ¬ Work.SSGRoute.gesKConj K Q A := by
    rw [hAdef]
    exact Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hρ1 hQsplitK
  -- ## 1. The dictionary: the pinned value is the local pairing at the sibling.
  have hdict := Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary (K := K) (Λ := Λ) hKΛ
    ζ hζ hζK S y hy hyT s hs m ρ hρ1 hρ2
  -- the `IsFinPlace` argument is a proposition, so the two families agree
  have hdictA : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 ρ
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hAfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b)) := by
    rw [show (fun _ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m)
        = (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) from
      funext fun n => Subsingleton.elim _ _]
    exact hdict
  -- ## 2. The prime of `↥K` below `Q`.
  set 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQfin with h𝔮def
  have h𝔮spec : Q.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hQfin
  -- ## 3. The divisor normalisation of the representative.
  have heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      P ≠ 𝔮 → Even (FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
    intro P hP
    rw [h𝔮def] at hP
    rw [hbdef]
    exact Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y
      hy hyT s hs m P hP
  have hodd : Odd (FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
    obtain ⟨𝔮₀, h𝔮₀comap, h𝔮₀odd⟩ := hnorm m hm
    have h : 𝔮₀ = 𝔮 := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← h𝔮₀comap, h𝔮spec]
    rw [hbdef, ← h]
    exact h𝔮₀odd
  have hneSib : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮 := by
    intro hfix
    refine hsep ?_
    have hcomap : A.comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
      have h1 : A.comap (algebraMap ↥K Ω) = ρ • (Q.comap (algebraMap ↥K Ω)) := by
        rw [hAdef]
        exact Work.SSGRoute.ZDataTwo.TwoRec.comap_galLift_smul_place (K := K) ρ Q
      rw [h1, h𝔮spec,
        Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
          𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ρ
          (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔮),
        hfix]
    obtain ⟨τ, hτ, hτA⟩ :=
      Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K := K)
        A Q (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K hAfin) hcomap
    exact Work.SSGRoute.H9.swGesKConj_symm ⟨τ, hτ, hτA⟩
  obtain ⟨z, yv, hzy, Q', hQ'nfix, hQ'miss, hdiv⟩ :=
    Work.SSGRoute.PinnedTwin.divisorRepresentative (k := k) (K := ↥K) ρ hρ2 b 𝔮 heven hodd hneSib
  obtain ⟨hzne, hane_z, hcop⟩ :=
    Work.SSGRoute.ZConstruction.twinDivisorConsequences (k := k) (K := ↥K) ρ hρ2 𝔮 Q' z hneSib
      hQ'nfix hQ'miss hdiv
  -- the explicit shape of the divisor of `z`
  have hzcount : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K))
      = (if P = 𝔮 then 1 else 0) + 2 * (if P = Q' then 1 else 0) := by
    intro P
    rw [hdiv P, Work.SSGRoute.ZDataTwo.TwoRec.count_asIdeal_eq 𝔮 P,
      Work.SSGRoute.ZDataTwo.TwoRec.count_asIdeal_eq Q' P]
  have hzint : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      0 ≤ FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) := by
    intro P
    rw [hzcount P]
    split_ifs <;> norm_num
  -- ## 4. The conjugate units, the switch and the average.
  set bt : (↥K)ˣ := Units.map ρ.toRingEquiv.toMonoidHom b with hbtdef
  set rz : (↥K)ˣ := Units.map ρ.toRingEquiv.toMonoidHom z with hrzdef
  have hrzval : (rz : ↥K) = ρ (z : ↥K) := rfl
  have hrzconj : rz = Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z := by
    rw [hrzdef, ← Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_eq_unitsMap (K := K) ρ z]
  have hbtconj : bt = Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b := by
    rw [hbtdef, ← Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_eq_unitsMap (K := K) ρ b]
  have hzy' : z = b * (yv * yv) := by rw [hzy, pow_two]
  have hzne' : (z : ↥K) - (rz : ↥K) ≠ 0 := hzne
  have hane_z' : (z : ↥K) + (rz : ↥K) ≠ 0 := hane_z
  set X : (↥K)ˣ := Units.mk0 ((z : ↥K) - (rz : ↥K)) hzne' with hXdef
  have hXcoe : (X : ↥K) = (z : ↥K) - (rz : ↥K) := Units.val_mk0 hzne'
  have hane : ((z : ↥K) + (rz : ↥K)) / 2 ≠ 0 := div_ne_zero hane_z' two_ne_zero
  set a : (↥K)ˣ := Units.mk0 (((z : ↥K) + (rz : ↥K)) / 2) hane with hadef
  have hacoe : (a : ↥K) = ((z : ↥K) + (rz : ↥K)) / 2 := Units.val_mk0 hane
  have ha2 : (2 : ↥K) * (a : ↥K) = (z : ↥K) + (rz : ↥K) := by
    rw [hacoe]
    field_simp
  have hρρ : ∀ x : ↥K, ρ (ρ x) = x := by
    intro x
    have h := congrArg (fun e : K ≃ₐ[k] K => e x) hρ2
    simpa [pow_two] using h
  have hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a := by
    apply Units.ext
    rw [Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_apply (K := K) ρ a, hadef, Units.val_mk0,
      map_div₀, map_add, map_ofNat, hrzval, hρρ]
    ring
  have hXanti : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X := by
    apply Units.ext
    rw [Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_apply (K := K) ρ X, Units.val_neg, hXdef,
      Units.val_mk0, map_sub, hrzval, hρρ]
    ring
  -- ## 5. The cochains of `z` and `ρz` agree with those of `b` and `ρb`.
  have hχz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
    rw [hzy']
    funext ψ
    by_cases hψ : ψ ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZConstruction.nodeKummerCocharZMod_mul_sq (K := K) ζ hζ hζK b yv ψ hψ
    · rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := b * (yv * yv)) hψ,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := b) hψ]
  have hrzeq : rz = bt * (Units.map ρ.toRingEquiv.toMonoidHom yv
      * Units.map ρ.toRingEquiv.toMonoidHom yv) := by
    rw [hrzdef, hbtdef, hzy]
    simp only [map_mul, map_pow, pow_two]
  have hχrz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt := by
    rw [hrzeq]
    funext ψ
    by_cases hψ : ψ ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZConstruction.nodeKummerCocharZMod_mul_sq (K := K) ζ hζ hζK bt
        (Units.map ρ.toRingEquiv.toMonoidHom yv) ψ hψ
    · rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := bt * (Units.map ρ.toRingEquiv.toMonoidHom yv
            * Units.map ρ.toRingEquiv.toMonoidHom yv)) hψ,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := bt) hψ]
  -- ## 6. The `S`-block and the confinement of the two classes.
  -- the conjugate class kills the local groups of the dyadic and ramified places
  have hsblock : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A' ∈ S, SSGRoute.IsConjPlace k A' B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0 :=
    fun B hB hBS hP => Work.SSGRoute.NodeS37.killsLocalGroupAtSBlockConj (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S hSfin hSram y hy0 s hs ρ m B hB hBS hP
  have hconfb : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
    intro B hB hnc u hI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ)
        hKΛ ζ hζ hζK S y hy hyT s hs m B hB hnc u huK hI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := b) huK
  have hconfbt : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K A B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0 := by
    have h := Work.SSGRoute.H9.CV2.hconf_conjUnit (K := K) ζ hζ hζK b ρ Q hconfb
    rw [← hbtdef, hAsib] at h
    exact h
  have hinfbt : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt c = 0 := by
    have h := Work.SSGRoute.H9.CV2.hinf_conjUnit (K := K) ζ hζ hζK b ρ
      (fun c hc hc2 => hinv m hm c hc hc2)
    rw [← hbtdef] at h
    exact h
  -- ## 7. The finite set of primes and one chosen place above each.
  let 𝓘X : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (X : ↥K)
  let 𝓘2 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (2 : ↥K)
  have hfinX : {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) |
      FractionalIdeal.count ↥K P 𝓘X ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥K) 𝓘X)
  have hfin2 : {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) |
      FractionalIdeal.count ↥K P 𝓘2 ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥K) 𝓘2)
  let SX : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    hfinX.toFinset
  let S2 : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    hfin2.toFinset
  let F : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    insert (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) (insert 𝔮 (SX ∪ S2))
  have hFmem : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      P ∈ F ↔ FractionalIdeal.count ↥K P 𝓘X ≠ 0 ∨ FractionalIdeal.count ↥K P 𝓘2 ≠ 0
        ∨ P = 𝔮 ∨ P = Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by
    intro P
    show P ∈ insert (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (insert 𝔮 (SX ∪ S2)) ↔ _
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_union, hfinX.mem_toFinset,
      hfin2.mem_toFinset]
    tauto
  have hFρ : ∀ P ∈ F, Commons.NumberTheory.NumberField.Completion.placeSmul ρ P ∈ F := by
    intro P hP
    rw [hFmem] at hP ⊢
    rcases hP with h | h | h | h
    · left
      exact (Work.SSGRoute.ZDataTwo.TwoRec.count_ne_zero_iff_count_placeSmul_ne_zero (K := K)
        ρ hρ2 X (Or.inr hXanti) P).mp h
    · right; left
      have h2fix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ)
          (Units.mk0 (2 : ↥K) (by norm_num)) = Units.mk0 (2 : ↥K) (by norm_num) := by
        apply Units.ext
        rw [Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_apply (K := K) ρ]
        exact map_ofNat ρ 2
      exact (Work.SSGRoute.ZDataTwo.TwoRec.count_ne_zero_iff_count_placeSmul_ne_zero (K := K)
        ρ hρ2 (Units.mk0 (2 : ↥K) (by norm_num)) (Or.inl h2fix) P).mp h
    · right; right; right
      rw [h]
    · right; right; left
      rw [h]
      exact Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 𝔮
  let A₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) →
      ValuationSubring Ω := fun P => (Work.SSGRoute.ZDataTwo.TwoRec.exists_finPlace_over_prime
        (K := K) P).choose
  have hA₀fin : ∀ P, SSGRoute.IsFinPlace k (A₀ P) := fun P =>
    (Work.SSGRoute.ZDataTwo.TwoRec.exists_finPlace_over_prime (K := K) P).choose_spec.1
  have hA₀comap : ∀ P, (A₀ P).comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K P := fun P =>
    (Work.SSGRoute.ZDataTwo.TwoRec.exists_finPlace_over_prime (K := K) P).choose_spec.2
  have hA₀prime : ∀ P, Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (A₀ P) (hA₀fin P) = P := by
    intro P
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
    rw [← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A₀ P) (hA₀fin P),
      hA₀comap P]
  let T' : Finset (ValuationSubring Ω) := F.image A₀
  have hT'fin : ∀ B ∈ T', SSGRoute.IsFinPlace k B := by
    intro B hB
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hB
    exact hA₀fin P
  have hT'disj : ∀ B ∈ T', ∀ C ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ C ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B) → B = C := by
    intro B hB C hC hform
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨P', -, rfl⟩ := Finset.mem_image.mp hC
    have hgc : Work.SSGRoute.gesKConj K (A₀ P) (A₀ P') :=
      (Work.SSGRoute.H9.gesKConj_iff_smul_form (K := K) (A₀ P) (A₀ P')).mpr hform
    have hcomap := Work.SSGRoute.ZConstruction.comap_eq_of_gesKConj (K := K) hgc
    rw [hA₀comap P, hA₀comap P'] at hcomap
    rw [Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K) hcomap]
  -- ## 8. The confinement of the switch outside `T'`.
  have hconfX : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ C ∈ T', ¬ Work.SSGRoute.gesKConj K C B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X u = 0 := by
    intro B hB hnc u hI
    have hunitX : B.valuation (algebraMap ↥K Ω (X : ↥K)) = 1 := by
      by_contra hne
      set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
        Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB with hPdef
      have hcount : FractionalIdeal.count ↥K P 𝓘X ≠ 0 :=
        (Work.SSGRoute.ZDataTwo.TwoRec.valuation_ne_one_iff_count_ne_zero (K := K) B P
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := B) hB) X).mp hne
      have hmem : A₀ P ∈ T' := by
        rw [Finset.mem_image]
        exact ⟨P, (hFmem P).mpr (Or.inl hcount), rfl⟩
      have hcomap : (A₀ P).comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hA₀comap, hPdef, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := B) hB]
      exact (hnc (A₀ P) hmem)
        (Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K := K)
          (A₀ P) B (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K (hA₀fin P)) hcomap)
    have hnot2 : ¬ B.valuation (2 : Ω) < 1 := by
      intro hlt
      set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
        Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB with hPdef
      have hlt' : B.valuation (algebraMap ↥K Ω
          ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K)) < 1 := by
        have h2Ω : algebraMap ↥K Ω
            ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) = (2 : Ω) := by
          rw [show ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) = (2 : ↥K) from rfl,
            map_ofNat (algebraMap ↥K Ω) 2]
        rwa [h2Ω]
      have hcount : FractionalIdeal.count ↥K P 𝓘2 ≠ 0 :=
        ne_of_gt ((Work.SSGRoute.ZDataTwo.TwoRec.count_pos_iff_place_valuation_lt_one (K := K) B P
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := B) hB)
          (Units.mk0 (2 : ↥K) (by norm_num))).mpr hlt')
      have hmem : A₀ P ∈ T' := by
        rw [Finset.mem_image]
        exact ⟨P, (hFmem P).mpr (Or.inr (Or.inl hcount)), rfl⟩
      have hcomap : (A₀ P).comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hA₀comap, hPdef, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := B) hB]
      exact (hnc (A₀ P) hmem)
        (Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K := K)
          (A₀ P) B (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K (hA₀fin P)) hcomap)
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo (K := K) ζ hζ hζK X B hB
        hnot2 hunitX u huK hI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := X) huK
  have hconfrz : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ C ∈ T', ¬ Work.SSGRoute.gesKConj K C B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz u = 0 := by
    intro B hB hnc u hI
    rw [hχrz]
    refine hconfbt B hB ?_ u hI
    intro hconj
    have hmem : A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ∈ T' := by
      rw [Finset.mem_image]
      exact ⟨_, (hFmem _).mpr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩
    refine hnc _ hmem ?_
    have hcomap : (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)).comap
        (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
      have h1 : (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)).comap
          (algebraMap ↥K Ω) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) := hA₀comap _
      rw [h1]
      rw [show Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮
          = Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
              (Work.SSGRoute.ZDataMup.galLift K ρ • Q) hAfin from
        (Work.SSGRoute.ZDataTwo.TwoRec.oddPrime_galLift_smul_place (K := K) ρ Q hQfin hAfin).symm]
      exact (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hAfin).symm
    exact Work.SSGRoute.H9.swGesKConj_trans
      (Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K := K)
        (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)) A
        (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K
          (hA₀fin (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮))) hcomap)
      hconj
  have hinfrz : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz c = 0 := by
    intro c hc hc2
    rw [hχrz]
    exact hinfbt c hc hc2
  -- ## 9. The product formula over `T'`.
  have hsum0 : ∑ B ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B.1 (hT'fin B.1 B.2)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) = 0 :=
    Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_sum_attach_eq_zero_of_kills (K := K) ζ hζ hζK rz X T'
      hT'fin hT'disj hconfrz hconfX hinfrz
  let G : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) → ZMod 2 :=
    fun P => Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
      (hA := hA₀fin P) rz X
  have hGdef : ∀ P, G P = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k)
      (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
      (hA := hA₀fin P) rz X := fun P => rfl
  have hsumF : F.sum G = 0 := by
    -- the two sums are the sums over `T'` and over `F` of the same terms
    let Fn : {B // B ∈ T'} → ZMod 2 := fun B =>
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B.1 (hT'fin B.1 B.2)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
    let Gn : {P // P ∈ F} → ZMod 2 := fun P => G P.1
    have hsum0' : T'.attach.sum Fn = 0 := hsum0
    have hbij : F.attach.sum Gn = T'.attach.sum Fn := by
      refine Finset.sum_bij (fun (P : {P // P ∈ F}) _ =>
        (⟨A₀ P.1, Finset.mem_image_of_mem A₀ P.2⟩ : {B // B ∈ T'})) ?_ ?_ ?_ ?_
      · intro P _
        exact Finset.mem_attach _ _
      · intro P₁ _ P₂ _ h
        have h1 : A₀ P₁.1 = A₀ P₂.1 := Subtype.mk.injEq _ _ _ _ ▸ h
        have h2 : P₁.1 = P₂.1 := by
          apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
          rw [← hA₀comap P₁.1, ← hA₀comap P₂.1, h1]
        exact Subtype.ext h2
      · intro B _
        obtain ⟨P, hP, hAP⟩ := Finset.mem_image.mp B.2
        exact ⟨⟨P, hP⟩, Finset.mem_attach _ _, Subtype.ext hAP⟩
      · intro P _
        exact Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_eq_oPairAt_proof_irrel (K := K) (k := k) (Ω := Ω)
          ζ hζ hζK rz X (A₀ P.1) (hA₀fin P.1)
          (hT'fin (A₀ P.1) (Finset.mem_image_of_mem A₀ P.2))
    have hFA : F.sum G = F.attach.sum Gn := (Finset.sum_attach F G).symm
    rw [hFA, hbij]
    exact hsum0'

  -- ## 10. The invariant "the place is dyadic".
  have h2fix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ)
      (Units.mk0 (2 : ↥K) (by norm_num)) = Units.mk0 (2 : ↥K) (by norm_num) := by
    apply Units.ext
    rw [Work.SSGRoute.ZDataTwo.TwoRec.conjUnit_galLift_apply (K := K) ρ]
    exact map_ofNat ρ 2
  have hcount2nonneg : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      0 ≤ FractionalIdeal.count ↥K P 𝓘2 := by
    intro P
    have hle : (A₀ P).valuation (algebraMap ↥K Ω
        ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K)) ≤ 1 := by
      rw [show ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) = (2 : ↥K) from rfl,
        show algebraMap ↥K Ω ((2 : ↥K)) = (2 : Ω) from map_ofNat (algebraMap ↥K Ω) 2,
        ValuationSubring.valuation_le_one_iff]
      have hh : (2 : Ω) = 1 + 1 := by norm_num
      rw [hh]
      exact (A₀ P).add_mem 1 1 (A₀ P).one_mem (A₀ P).one_mem
    exact (Work.SSGRoute.ZDataTwo.TwoRec.count_nonneg_iff_place_valuation_le_one (K := K) (A₀ P)
      P (hA₀comap P) (Units.mk0 (2 : ↥K) (by norm_num))).mpr hle
  have hcount2eq : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) 𝓘2
        = FractionalIdeal.count ↥K P 𝓘2 := by
    intro P
    have h := Work.SSGRoute.ZDataTwo.TwoRec.count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2
      (Units.mk0 (2 : ↥K) (by norm_num)) P
    rw [h2fix] at h
    exact h.symm
  have hcount2pos : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      0 < FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) 𝓘2
        ↔ 0 < FractionalIdeal.count ↥K P 𝓘2 :=
    fun P => Iff.of_eq (congrArg (fun n => 0 < n) (hcount2eq P))
  -- the prime below the sibling is `ρ𝔮`
  have hprA : Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hAfin
      = Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 :=
    (Work.SSGRoute.ZDataTwo.TwoRec.oddPrime_galLift_smul_place (K := K) ρ Q hQfin hAfin).trans
      (congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) h𝔮def.symm)
  have hdyA : A.valuation (2 : Ω) < 1 ↔ 0 < FractionalIdeal.count ↥K 𝔮 𝓘2 := by
    rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) A hAfin, hprA]
    exact hcount2pos 𝔮
  have hdyA₀ : (A₀ 𝔮).valuation (2 : Ω) < 1 ↔ 0 < FractionalIdeal.count ↥K 𝔮 𝓘2 := by
    rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ 𝔮) (hA₀fin 𝔮),
      hA₀prime 𝔮]
  -- ## 11. The value at the sibling.
  have hV : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 ρ
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hAfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b)) := hdictA
  -- the `oPairGlob` form of the `S`-block
  have hSblock_glob : ∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
      (∃ A' ∈ S, SSGRoute.IsConjPlace k A' B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (hA := hB) rz X
        = 0 := by
    intro B hB hBS hP
    rw [← Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK rz X B hB,
      hχrz]
    exact Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup (K := K) ζ hζ hζK bt X
      B hB (hsblock B hB hBS hP)
  by_cases hdy : 0 < FractionalIdeal.count ↥K 𝔮 𝓘2
  · -- ## 12. The dyadic case: the `S`-block kills the conjugate class at the sibling.
    rw [hV]
    exact Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup_right (K := K) ζ hζ hζK b
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b) A hAfin
      (fun u hu => by
        rw [← hbtconj]
        exact hsblock A hAfin (hSram A hAfin (Or.inr (hdyA.mpr hdy))) (Or.inr (hdyA.mpr hdy)) u hu)
  · -- ## 13. The odd case.
    have hA2 : ¬ A.valuation (2 : Ω) < 1 := fun h => hdy (hdyA.mp h)
    have hq2 : ¬ (A₀ 𝔮).valuation (2 : Ω) < 1 := fun h => hdy (hdyA₀.mp h)
    -- the counts of `z` and `ρz` at the sibling's prime and at `𝔮`
    have hcountzρq : FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) = 0 := by
      rw [hzcount (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮),
        if_neg hneSib, if_neg (fun h => hQ'miss h.symm)]
      norm_num
    have hcrzA : 0 < FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (rz : ↥K)) := by
      have h := Work.SSGRoute.ZDataTwo.TwoRec.count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 z
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
      rw [Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 𝔮, ← hrzconj] at h
      rw [h, hzcount 𝔮, if_pos rfl]
      split_ifs <;> norm_num
    have hcrzq : FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (rz : ↥K)) = 0 := by
      have h := Work.SSGRoute.ZDataTwo.TwoRec.count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 z 𝔮
      rw [← hrzconj] at h
      rw [h]
      exact hcountzρq
    -- the local facts at the sibling
    have hvzA : A.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 := by
      refine (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero A
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hAfin)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hAfin) z).mpr ?_
      rw [hprA]
      exact hcountzρq
    have hvrzA : A.valuation (algebraMap ↥K Ω (rz : ↥K)) < 1 :=
      Work.SSGRoute.ZDataTwo.TwoRec.valuation_lt_one_of_count_pos (K := K) A
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hAfin)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hAfin) rz (by
          rw [hprA]
          exact hcrzA)
    have hvXA : A.valuation (algebraMap ↥K Ω (X : ↥K)) = 1 := by
      have hsub : algebraMap ↥K Ω (X : ↥K)
          = algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K) := by
        rw [hXcoe, map_sub]
      rw [hsub, Valuation.map_sub_eq_of_lt_left]
      · exact hvzA
      · rw [hvzA]; exact hvrzA
    -- ## 13a. The term at the sibling's class is `V`.
    have hGrq : G (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m)
          0 ρ := by
      have hclass : Work.SSGRoute.gesKConj K
          (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)) A := by
        exact Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq
          (K := K) _ A (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K
            (hA₀fin (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)))
          (by
            rw [hA₀comap, ← hprA]
            exact (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hAfin).symm)
      rw [hGdef]
      rw [Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_eq_of_gesKConj (K := K) (k := k) (Ω := Ω) ζ hζ hζK
        rz X (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)) A (hA₀fin _) hAfin
        hclass]
      rw [← Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_sibling_eq_oPairGlob_antiInvariant (K := K) (k := k)
        (Ω := Ω) ζ hζ hζK ρ hρ2 b z yv rz X hzy' hrzconj hXcoe A hAfin hA2 hvzA hvXA hvrzA]
      exact hV.symm
    -- ## 13b. The term at `𝔮` vanishes (both classes are units there).
    have hvzq : (A₀ 𝔮).valuation (algebraMap ↥K Ω (z : ↥K)) < 1 :=
      Work.SSGRoute.ZDataTwo.TwoRec.valuation_lt_one_of_count_pos (K := K) (A₀ 𝔮) 𝔮 (hA₀comap 𝔮) z
        (by rw [hzcount 𝔮, if_pos rfl]; split_ifs <;> norm_num)
    have hvrzq : (A₀ 𝔮).valuation (algebraMap ↥K Ω (rz : ↥K)) = 1 :=
      (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero (A₀ 𝔮) 𝔮
        (hA₀comap 𝔮) rz).mpr hcrzq
    have hvXq : (A₀ 𝔮).valuation (algebraMap ↥K Ω (X : ↥K)) = 1 := by
      have hsub : algebraMap ↥K Ω (X : ↥K)
          = algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K) := by
        rw [hXcoe, map_sub]
      rw [hsub, Valuation.map_sub_eq_of_lt_right]
      · exact hvrzq
      · rw [hvrzq]; exact hvzq
    have hGq : G 𝔮 = 0 := by
      rw [hGdef]
      exact Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_eq_zero_of_units ζ hζ hζK rz X (A₀ 𝔮) (hA₀fin 𝔮)
        hq2 hvrzq hvXq
    -- ## 13c. The remaining terms.
    let F0 : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
      (F.erase 𝔮).erase (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
    have hnotmem : ∀ P ∈ F0,
        P ≠ 𝔮 ∧ P ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by
      intro P hP
      exact ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase hP)).1, (Finset.mem_erase.mp hP).1⟩
    have hF0ρ : ∀ P ∈ F0,
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ P ∈ F0 := by
      intro P hP
      obtain ⟨hPne, hPne'⟩ := hnotmem P hP
      have hPF : P ∈ F := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hP)
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, hFρ P hPF⟩
      · intro h
        refine hPne ?_
        have h2 := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) h
        rwa [Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 P,
          Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 𝔮] at h2
      · intro h
        refine hPne' ?_
        have h2 := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) h
        rwa [Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 P] at h2
    -- the local units at a prime of `F0` where the switch is not a unit
    have hloc : ∀ (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)),
        FractionalIdeal.count ↥K P 𝓘X ≠ 0 → FractionalIdeal.count ↥K P 𝓘2 = 0 →
        ∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
          Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB = P →
          B.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 ∧
          B.valuation (algebraMap ↥K Ω (rz : ↥K)) = 1 ∧
          B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1 ∧
          B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 := by
      intro P hPX hP2 B hB hBP
      have hcB : FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
          𝓘X ≠ 0 := by rw [hBP]; exact hPX
      have h2B : ¬ B.valuation (2 : Ω) < 1 := by
        rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) B hB, hBP]
        exact not_lt.mpr (le_of_eq hP2)
      obtain ⟨h1, h2, h3, h4⟩ := Work.SSGRoute.ZDataTwo.TwoRec.localUnits_of_count_X_ne_zero
        (K := K) ρ hρ2 z X a (by rw [← hrzconj]; exact hXcoe) (by rw [← hrzconj]; exact ha2)
        hzint hcop B hB h2B hcB
      refine ⟨h1, ?_, h3, h4⟩
      rw [← hrzconj] at h2
      exact h2
    -- the value of `G` at a prime of `F0` where the switch is not a unit
    have hGred : ∀ (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)),
        FractionalIdeal.count ↥K P 𝓘X ≠ 0 → FractionalIdeal.count ↥K P 𝓘2 = 0 →
        G P = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
          (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
          (A₀ P) (hA₀fin P)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by
      intro P hPX hP2
      obtain ⟨hvz, hvrz, hva, hvX⟩ := hloc P hPX hP2 (A₀ P) (hA₀fin P) (hA₀prime P)
      have h2B : ¬ (A₀ P).valuation (2 : Ω) < 1 := by
        rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ P)
          (hA₀fin P), hA₀prime P]
        exact not_lt.mpr (le_of_eq hP2)
      rw [hGdef]
      rw [← Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK rz X (A₀ P)
        (hA₀fin P)]
      exact Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_mul_left_rz_eq_mul_left_a (K := K) (k := k)
        (Ω := Ω) ζ hζ hζK ρ hρ2 z rz X a hrzconj hXcoe ha2 (A₀ P) (hA₀fin P) h2B hvrz hva hvX
    -- the split-pair equality
    have hsplit_eq : ∀ P ∈ F0, Commons.NumberTheory.NumberField.Completion.placeSmul ρ P ≠ P →
        G (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) = G P := by
      intro P hP hne
      obtain ⟨hPne, hPne'⟩ := hnotmem P hP
      have hPF : P ∈ F := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hP)
      have hdisj : FractionalIdeal.count ↥K P 𝓘X ≠ 0 ∨ FractionalIdeal.count ↥K P 𝓘2 ≠ 0 := by
        rcases (hFmem P).mp hPF with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hPne
        · exact absurd h hPne'
      by_cases hP2 : FractionalIdeal.count ↥K P 𝓘2 = 0
      · -- the switch is not a unit at `P`: the two local terms are equal
        have hPX : FractionalIdeal.count ↥K P 𝓘X ≠ 0 := by
          rcases hdisj with h | h
          · exact h
          · exact (h hP2).elim
        obtain ⟨hvz, hvrz, hva, hvX⟩ := hloc P hPX hP2 (A₀ P) (hA₀fin P) (hA₀prime P)
        have hPX' : FractionalIdeal.count ↥K
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) 𝓘X ≠ 0 :=
          (Work.SSGRoute.ZDataTwo.TwoRec.count_ne_zero_iff_count_placeSmul_ne_zero (K := K) ρ hρ2 X
            (Or.inr hXanti) P).mp hPX
        have hP2' : FractionalIdeal.count ↥K
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) 𝓘2 = 0 := by
          rw [hcount2eq P]; exact hP2
        obtain ⟨hvz', hvrz', hva', hvX'⟩ :=
          hloc (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) hPX' hP2'
            (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P)
            ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
              (hA₀fin P))
            ((Work.SSGRoute.ZDataTwo.TwoRec.oddPrime_galLift_smul_place (K := K) ρ (A₀ P)
              (hA₀fin P) _).trans (congrArg
                (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) (hA₀prime P)))
        have h2B : ¬ (A₀ P).valuation (2 : Ω) < 1 := by
          rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ P)
            (hA₀fin P), hA₀prime P]
          exact not_lt.mpr (le_of_eq hP2)
        have h2B' : ¬ (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P).valuation (2 : Ω) < 1 := by
          rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K)
            (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P)
            ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
              (hA₀fin P)),
            Work.SSGRoute.ZDataTwo.TwoRec.oddPrime_galLift_smul_place (K := K) ρ (A₀ P)
              (hA₀fin P)
              ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
                (hA₀fin P)),
            hA₀prime P]
          exact not_lt.mpr (le_of_eq hP2')
        have hpair := Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_antiInvariant_eq_galLift_smul
          (K := K) (k := k) (Ω := Ω) ζ hζ hζK ρ hρ1 hρ2 z rz X a hrzconj hXcoe ha2 hafix hXanti
          (A₀ P) (hA₀fin P) h2B h2B' hvrz hva hvX hvrz' hva' hvX'
        have hclass : Work.SSGRoute.gesKConj K
            (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P)
            (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)) := by
          refine Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq
            (K := K) _ _
            (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K
              ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
                (hA₀fin P))) ?_
          rw [Work.SSGRoute.ZDataTwo.TwoRec.comap_galLift_smul_place (K := K) ρ (A₀ P),
            hA₀comap P,
            Work.SSGRoute.ZDataTwo.TwoRec.smul_valuationSubringAtPrime_eq (K := K) ρ P,
            hA₀comap (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)]
        show Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
            (hA := hA₀fin (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)) rz X
          = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
            (hA := hA₀fin P) rz X
        rw [← Work.SSGRoute.ZDataTwo.TwoRec.oPairGlob_eq_of_gesKConj (K := K) (k := k) (Ω := Ω) ζ hζ
            hζK rz X (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P)
            (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P))
            ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
              (hA₀fin P)) (hA₀fin _) hclass,
          ← hpair]
      · -- the prime is dyadic: the `S`-block kills both terms
        have hpos : 0 < FractionalIdeal.count ↥K P 𝓘2 :=
          lt_of_le_of_ne (hcount2nonneg P) (Ne.symm hP2)
        have hdyaB : (A₀ P).valuation (2 : Ω) < 1 :=
          (Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ P)
            (hA₀fin P)).mpr (by rw [hA₀prime P]; exact hpos)
        have hpos' : 0 < FractionalIdeal.count ↥K
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) 𝓘2 :=
          (hcount2pos P).mpr hpos
        have hdyaB' : (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)).valuation
            (2 : Ω) < 1 :=
          (Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) _ _).mpr (by
            rw [hA₀prime]; exact hpos')
        show Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
            (hA := hA₀fin (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)) rz X
          = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
            (hA := hA₀fin P) rz X
        rw [hSblock_glob (A₀ (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)) (hA₀fin _)
            (hSram _ (hA₀fin _) (Or.inr hdyaB')) (Or.inr hdyaB'),
          hSblock_glob (A₀ P) (hA₀fin P) (hSram _ (hA₀fin P) (Or.inr hdyaB)) (Or.inr hdyaB)]
    -- the terms at the `ρ`-fixed primes vanish
    have hfixed : ∀ P ∈ F0, Commons.NumberTheory.NumberField.Completion.placeSmul ρ P = P →
        G P = 0 := by
      intro P hP hfix
      obtain ⟨hPne, hPne'⟩ := hnotmem P hP
      have hPF : P ∈ F := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hP)
      have hdisj : FractionalIdeal.count ↥K P 𝓘X ≠ 0 ∨ FractionalIdeal.count ↥K P 𝓘2 ≠ 0 := by
        rcases (hFmem P).mp hPF with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hPne
        · exact absurd h hPne'
      by_cases hP2 : FractionalIdeal.count ↥K P 𝓘2 = 0
      · have hPX : FractionalIdeal.count ↥K P 𝓘X ≠ 0 := by
          rcases hdisj with h | h
          · exact h
          · exact (h hP2).elim
        obtain ⟨hvz, hvrz, hva, hvX⟩ := hloc P hPX hP2 (A₀ P) (hA₀fin P) (hA₀prime P)
        have h2B : ¬ (A₀ P).valuation (2 : Ω) < 1 := by
          rw [Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ P)
            (hA₀fin P), hA₀prime P]
          exact not_lt.mpr (le_of_eq hP2)
        by_cases hram : SSGRoute.IsRamifiedIn k K (A₀ P)
        · -- ramified: the `S`-block
          have hramΛ : SSGRoute.IsRamifiedIn k Λ (A₀ P) := by
            obtain ⟨σ, hσI, hσK⟩ := hram
            exact ⟨σ, hσI, fun hΛ => hσK fun x => by
              have hx := hΛ ⟨x, hKΛ x.2⟩
              simpa using hx⟩
          have hnotsplit : ¬ SSGRoute.IsSplitIn k K (A₀ P) := by
            obtain ⟨σ, hσI, hσK⟩ := hram
            intro hsplit
            exact hσK (hsplit hσI.1)
          rw [hGdef]
          rw [hSblock_glob (A₀ P) (hA₀fin P) (hSram _ (hA₀fin P) (Or.inl hramΛ))
            (Or.inl hnotsplit)]
        · -- unramified: the inert squareness
          have hfixB : Work.SSGRoute.gesKConj K
              (Work.SSGRoute.ZDataMup.galLift K ρ • A₀ P) (A₀ P) := by
            refine Work.SSGRoute.ZDataMup.OddForm.exists_mem_fixingSubgroup_smul_eq_of_comap_eq
              (K := K) _ _
              (SSGRoute.comap_algebraMap_ne_top_of_isFinPlace K
                ((SSGRoute.isFinPlace_smul_iff (A₀ P) (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
                  (hA₀fin P))) ?_
            rw [Work.SSGRoute.ZDataTwo.TwoRec.comap_galLift_smul_place (K := K) ρ (A₀ P),
              hA₀comap P,
              show ρ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K P
                = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K P from by
                rw [Work.SSGRoute.ZDataTwo.TwoRec.smul_valuationSubringAtPrime_eq (K := K) ρ P, hfix]]
          have hunr : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.res k K σ = ρ →
              ¬ SSGRoute.IsInertia k (A₀ P) σ := by
            intro σ hσ hI
            refine hram ⟨σ, hI, fun hmem => hρ1 ?_⟩
            rw [← hσ]
            exact show (SSGRoute.res k K) σ = 1 from by
              rw [← MonoidHom.mem_ker, show (SSGRoute.res k K).ker = K.fixingSubgroup from
                IntermediateField.restrictNormalHom_ker K]
              exact hmem
          rw [hGred P hPX hP2]
          exact Work.SSGRoute.NodeS37.oPairAt_inertPrime_eq_zero (K := K) (k := k) (Ω := Ω) ζ hζ
            hζK ρ hρ1 hρ2 a X hafix hXanti (A₀ P) (hA₀fin P) h2B hfixB hunr hva
      · -- dyadic: the `S`-block
        have hpos : 0 < FractionalIdeal.count ↥K P 𝓘2 :=
          lt_of_le_of_ne (hcount2nonneg P) (Ne.symm hP2)
        have hdyaB : (A₀ P).valuation (2 : Ω) < 1 :=
          (Work.SSGRoute.ZDataTwo.TwoRec.place_two_lt_one_iff_count_pos (K := K) (A₀ P)
            (hA₀fin P)).mpr (by rw [hA₀prime P]; exact hpos)
        rw [hGdef]
        rw [hSblock_glob (A₀ P) (hA₀fin P) (hSram _ (hA₀fin P) (Or.inr hdyaB)) (Or.inr hdyaB)]
    -- ## 13d. The sum over the `ρ`-stable part vanishes.
    have hF0sum : F0.sum G = 0 := by
      have hsum_inv := Work.SSGRoute.ZDataTwo.TwoRec.sum_involution_zmodTwo
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) F0 G
        (fun x _ => Work.SSGRoute.ZDataTwo.TwoRec.placeSmul_placeSmul (K := ↥K) ρ hρ2 x)
        hF0ρ hsplit_eq
      rw [hsum_inv]
      refine Finset.sum_eq_zero fun P hP => hfixed P (Finset.mem_of_mem_filter P hP)
        (Finset.mem_filter.mp hP).2
    -- ## 13e. The conclusion.
    have hsplitF : F.sum G = G (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        + G 𝔮 + F0.sum G := by
      have hmem : 𝔮 ∈ F := (hFmem 𝔮).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have hmem' : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∈ F.erase 𝔮 :=
        Finset.mem_erase.mpr ⟨hneSib, (hFmem _).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩
      have h1 : (F.erase 𝔮).sum G + G 𝔮 = F.sum G := Finset.sum_erase_add F G hmem
      have h2 : F0.sum G + G (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
          = (F.erase 𝔮).sum G := by
        rw [show F0 = (F.erase 𝔮).erase (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
          from rfl]
        exact Finset.sum_erase_add (F.erase 𝔮) G hmem'
      rw [← h1, ← h2]
      abel
    have hGrq0 : G (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) = 0 := by
      have h := hsumF
      rw [hsplitF, hGq, hF0sum] at h
      simpa using h
    rw [← hGrq]
    exact hGrq0

end Work.SSGRoute.ZDataTwo.TwoRec
