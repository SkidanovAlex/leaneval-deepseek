import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined
import Submission.Work.SSGRoute.NodeS37.pinValue_of_pinnedAtLevel
import Submission.Work.SSGRoute.NodeS37.preTwo_siblingValue
import Submission.Work.SSGRoute.ZDataTwo.SWFourTwo
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.pinValue_cross_two
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.pinValue_self_symm
import Submission.Work.SSGRoute.ZDataTwo.pigeonhole_three_minimal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open scoped Pointwise

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Two combinatorial preliminaries -/

/-- **The shoe box of the `p = 2` §4 recursion**: the pigeonhole on the `Ψ`-vector sequence
`m ↦ TwoRec.valSeq f m` (into the finite type `Gam K → ZMod 2`) produces `i < j < N` with equal
`Ψ`-vectors and the witness pattern `(W_{ij}, W_{iN}, W_{jN}) = (F, T, F)` of the rule (4). -/
private theorem shoebox_extract' {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [Fintype (K ≃ₐ[k] K)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → ValuationSubring Ω × (↥K)ˣ) :
    ∃ i j N : ℕ, i < j ∧ j < N ∧
      (∀ υ : Gam K, Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f j υ
        = Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f i υ) ∧
      (∀ υ : Gam K, Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f N υ
        = Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f j υ) ∧
      ¬ Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) i j ∧
      Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) i N ∧
      ¬ Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) j N := by
  classical
  obtain ⟨i, j, N, hij, hjN, hE1, hE2, hmin, hconv1, hconv2⟩ :=
    Work.SSGRoute.ZDataTwo.pigeonhole_three_minimal
      (fun m => Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f m)
  refine ⟨i, j, N, hij, hjN, fun υ => (congrFun hE1 υ).symm, fun υ => (congrFun hE2 υ).symm,
    ?_, ?_, ?_⟩
  · rintro ⟨t, hit, htj, hval⟩
    exact hconv2 t hit htj (funext fun υ => hval υ)
  · exact ⟨j, hij, hjN, fun υ => (congrFun hE1 υ).symm⟩
  · rintro ⟨t, hjt, htN, hval⟩
    exact hconv1 t hjt htN (funext fun υ => hval υ)

/-- **The three coefficient identities of the `p = 2` §4 verification.** -/
private theorem eGam_coefficients' {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → ValuationSubring Ω × (↥K)ˣ) (i j N : ℕ)
    (hw1 : ¬ Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) i j)
    (hw2 : Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) i N)
    (hw3 : ¬ Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) j N) :
    (∀ ρ : Gam K, ¬ IsInv ρ →
        1 + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j ρ
          + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N ρ = 0) ∧
    (∀ ρ : Gam K, ¬ IsInv ρ →
        1 + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N ρ
          + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j (ginv ρ) = 0) ∧
    (∀ ρ : Gam K, ¬ IsInv ρ →
        1 + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N (ginv ρ)
          + Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N (ginv ρ) = 0) := by
  classical
  have hbran : ∀ (l m : ℕ) (υ : Gam K), ¬ IsInv υ →
      Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f l m υ =
        (if theta υ = υ then
          (if Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) l m then 1 else 0)
        else
          (if Witness (Work.SSGRoute.ZDataTwo.TwoRec.valSeq (K := K) ζ hζ hζK f) l m then 0 else 1)) := by
    intro l m υ h
    rw [Work.SSGRoute.ZDataTwo.TwoRec.eGam, if_neg h]
  have hgi_ne : ∀ (ρ : Gam K), ¬ IsInv ρ → ginv ρ ≠ ρ := by
    intro ρ hρ h
    refine hρ (by
      have h2 : (ρ : K ≃ₐ[k] K)⁻¹ = (ρ : K ≃ₐ[k] K) := congrArg Subtype.val h
      show (ρ : K ≃ₐ[k] K) ^ 2 = 1
      calc (ρ : K ≃ₐ[k] K) ^ 2 = (ρ : K ≃ₐ[k] K)⁻¹ * (ρ : K ≃ₐ[k] K) := by rw [pow_two, h2]
        _ = 1 := inv_mul_cancel _)
  have hbranch : ∀ (ρ : Gam K) (_ : ¬ IsInv ρ),
      (theta ρ = ρ → theta (ginv ρ) ≠ ginv ρ) ∧
      (theta ρ = ginv ρ → theta (ginv ρ) = ginv ρ) ∧
      (theta ρ = ginv ρ → theta ρ ≠ ρ) := by
    intro ρ hρ
    refine ⟨fun hs hc => ?_, fun hs => by rw [theta_ginv, hs], fun hs hc => ?_⟩
    · exact hgi_ne ρ hρ (hs.symm.trans ((theta_ginv ρ).symm.trans hc)).symm
    · exact hgi_ne ρ hρ (hc.symm.trans hs).symm
  refine ⟨?_, ?_, ?_⟩ <;> intro ρ hρ
  · obtain ⟨hb1, hb2, hb3⟩ := hbranch ρ hρ
    rcases theta_eq_self_or_ginv ρ with hs | hgv
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j ρ = 0 := by
        rw [hbran i j ρ hρ, if_pos hs, if_neg hw1]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N ρ = 1 := by
        rw [hbran i N ρ hρ, if_pos hs, if_pos hw2]
      rw [h1, h2]; decide
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j ρ = 1 := by
        rw [hbran i j ρ hρ, if_neg (hb3 hgv), if_neg hw1]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N ρ = 0 := by
        rw [hbran i N ρ hρ, if_neg (hb3 hgv), if_pos hw2]
      rw [h1, h2]; decide
  · obtain ⟨hb1, hb2, hb3⟩ := hbranch ρ hρ
    have hgi : ¬ IsInv (ginv ρ) := not_isInv_ginv hρ
    rcases theta_eq_self_or_ginv ρ with hs | hgv
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N ρ = 0 := by
        rw [hbran j N ρ hρ, if_pos hs, if_neg hw3]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j (ginv ρ) = 1 := by
        rw [hbran i j (ginv ρ) hgi, if_neg (hb1 hs), if_neg hw1]
      rw [h1, h2]; decide
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N ρ = 1 := by
        rw [hbran j N ρ hρ, if_neg (hb3 hgv), if_neg hw3]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i j (ginv ρ) = 0 := by
        rw [hbran i j (ginv ρ) hgi, if_pos (hb2 hgv), if_neg hw1]
      rw [h1, h2]; decide
  · obtain ⟨hb1, hb2, hb3⟩ := hbranch ρ hρ
    have hgi : ¬ IsInv (ginv ρ) := not_isInv_ginv hρ
    rcases theta_eq_self_or_ginv ρ with hs | hgv
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N (ginv ρ) = 0 := by
        rw [hbran i N (ginv ρ) hgi, if_neg (hb1 hs), if_pos hw2]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N (ginv ρ) = 1 := by
        rw [hbran j N (ginv ρ) hgi, if_neg (hb1 hs), if_neg hw3]
      rw [h1, h2]; decide
    · have h1 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f i N (ginv ρ) = 1 := by
        rw [hbran i N (ginv ρ) hgi, if_pos (hb2 hgv), if_pos hw2]
      have h2 : Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK f j N (ginv ρ) = 0 := by
        rw [hbran j N (ginv ρ) hgi, if_pos (hb2 hgv), if_neg hw3]
      rw [h1, h2]; decide

/-- `a + a + a = a` in `ZMod 2`. -/
private theorem ZMod2_three_add (a : ZMod 2) : a + a + a = a := by
  revert a
  decide

/-! ## The three scalar book-keepings of the coefficient computation

The three summands of `χ_{b_i b_j b_N}` at the pinned Frobenius `ψ` are `v`, `a • v`, `b • v` in some
order; the coefficient identity of the rule (4) is `1 + a + b = 0` in `𝔽₂`.  The three permutations
below turn that identity into the vanishing of the sum. -/

/-- The own term first: `(v + a•v) + b•v = 0` when `1 + a + b = 0`. -/
private theorem ZMod2_three_sum_left {v a b : ZMod 2} (h : 1 + a + b = 0) :
    (v + a • v) + b • v = 0 := by
  revert v a b
  decide

/-- The own term in the middle: `(b•v + v) + a•v = 0` when `1 + a + b = 0`. -/
private theorem ZMod2_three_sum_mid {v a b : ZMod 2} (h : 1 + a + b = 0) :
    (b • v + v) + a • v = 0 := by
  revert v a b
  decide

/-- The own term last: `(a•v + b•v) + v = 0` when `1 + a + b = 0`. -/
private theorem ZMod2_three_sum_right {v a b : ZMod 2} (h : 1 + a + b = 0) :
    (a • v + b • v) + v = 0 := by
  revert v a b
  decide

/-! THE VERIFICATION HALF of the `p = 2` §4 core (`ZDataTwo.mu2ThreeHalves`): from a history with
the recursion invariant `Work.SSGRoute.ZDataTwo.TwoRec.PreTwo` at every prefix, produce the single
*good class* `B = b_i * b_j * b_N` with the four local properties (1)--(4) of
`ZDataTwo/ACTION_mu2_three_halves_plan.md` §1, with `Pset = {Q_i, Q_j, Q_N}` the minimal shoe-box
triple of `ZDataTwo.pigeonhole_three_minimal` applied to the `Ψ`-vector `TwoRec.valSeq`.

`hclaim` is the paper's Claim (`SSGRoute/NodeS37/claimOfPreTwo`, being proved in another file): it is
what closes the *involutive* companions `σ • Q_x`, for which `ZDataTwo.blocks_of_prVal` says nothing
(it carries `hiτ : ¬ IsInv τ`).  It is taken here as a hypothesis so that this verification does not
depend on it.  SW p. 17 uses it for the `s = t` case and reduces `s < t` to it.

Route (SW p. 17; `ZDataTwo/ACTION_final_wiring.md` (b)--(f)):
* `ZDataTwo.pigeonhole_three_minimal` on `a m := TwoRec.valSeq (K := K) ζ hζ hζK s.f s.hf m`
  gives `i < j < N` with `val i = val j = val N`, `¬ Witness val i j`, `Witness val i N`
  (witness `j`) and `¬ Witness val j N`;
* `ZDataTwo.blocks_of_prVal` (proved, purely combinatorial) gives the six `𝔽₂` identities;
* the *own* values are `TwoRec.valSeq`/`TwoRec.psiVal` by definition (`TwoRec.sibVal` is
  `NodeS35.pinValue` at the sibling, so it is `χ_{b_m}` at a Frobenius pinned at the Kummer level);
  the *prescribed* values come from `PreTwo`'s realisation clause (5) at the blocks
  `A ∈ TBlock S s.f m` (`TwoRec.TBlock_covers_Q`, `TwoRec.prescDatum_eq_of_escape`,
  `TwoRec.prVal_eq_eGam_smul`), transported along `gesKConj` as in
  `H9/swHistKExists_proved.lean`'s `Pre_step` tail (the `τ⁻¹ * σ * τ` computation);
* the *foreign* values (`χ_{b_i}` at a sibling of `Q_j` for `i < j`, and at a sibling of `Q_N` for
  `i, j < N`) come from the crossed two-place identity — `ZDataTwo.crossedValueTwoProof` (proved,
  21 vetted hypotheses) or its packaged form `ZDataTwo.TwoRec.crossTwoChainCore` (proved) with
  `TwoRec.pinValue_cross_two` / `pinValue_self_symm` (proved) and, for the `σ⁻¹`-orientation,
  `NodeS37.crossedValue` (proved);
* "vanishes at a pinned Frobenius" → "vanishes on the whole local group of the companion":
  `ZDataTwo.threeTerm_kills_localGroup` (proved).  `hur` holds because `(b_m) = 𝔮_m · A_m²` with the
  `𝔮_m` pairwise distinct, so for `B'` a companion of `Q_x` the valuations of `b_m` (`m ≠ x`) are
  even, and `v_{B'}(b_x)` is even too because `B'` lies over a conjugate prime of `↥K`; the level `L`
  may be taken to be `Λ` (`PreTwo` (1) + `Λ/k` Galois give unramifiedness);
* clauses (1), (2), (3) are read off `PreTwo`'s clauses (5), (6) and (5)+(7);
* clause (3) of the conclusion (`¬ IsConjPlace k A P` for `A ∈ S`) comes from the oracle's
  `¬ IsConjPlace` clause at the stage `x` (true by `hs (x+1)`) together with `TwoRec.TBlock_covers_S`. -/
theorem goodClassOfHistory {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]
    (hKΛ : K ≤ Λ)
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
    (hclaim : ∀ m l : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup →
      (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0) :
    ∃ (Pset : Finset (ValuationSubring Ω)) (B : (↥K)ˣ),
      (∀ P ∈ Pset, SSGRoute.IsFinPlace k P) ∧
      (∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P) ∧
      (∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P) ∧
      (∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B') →
        ∀ σ ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ B σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ B c = 0) ∧
      (∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B') →
        (∀ P ∈ Pset, ∀ τ ∈ K.fixingSubgroup, τ • P ≠ B') →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B' σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ B σ = 0) ∧
      (∀ P ∈ Pset, ∀ B' : ValuationSubring Ω, SSGRoute.IsConjPlace k P B' →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B') →
        ∀ u ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ B u = 0) := by
  classical
  -- ## 0. the shoe box
  obtain ⟨i, j, N, hij, hjN, hshij, hshjN, hw1, hw2, hw3⟩ :=
    shoebox_extract' (K := K) ζ hζ hζK s.f
  -- ## 1. the invariant at stage `N + 1`
  obtain ⟨hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, hF9⟩ := hs (N + 1)
  have hidx : ∀ m : ℕ, m ≤ N → m < N + 1 := fun m hm => Nat.lt_succ_of_le hm
  have hfin : ∀ m : ℕ, m ≤ N → SSGRoute.IsFinPlace k (s.f m).1 :=
    fun m hm => hF1 m (hidx m hm)
  have hsplitK : ∀ m : ℕ, m ≤ N → SSGRoute.IsSplitIn k K (s.f m).1 :=
    fun m hm => Work.SSGRoute.NodeS35.isSplitIn_of_le hKΛ (hF2 m (hidx m hm))
  have hinfm : ∀ m : ℕ, m ≤ N → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 c = 0 :=
    fun m hm => hF7 m (hidx m hm)
  have hconfm : ∀ m : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K (s.f m).1 B → ∀ σ ∈ K.fixingSubgroup,
        SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = 0 :=
    fun m => Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined
      (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT s hs m
  have hoddm : ∀ m : ℕ, (hm : m ≤ N) → Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (s.f m).1 (hfin m hm))
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((s.f m).2 : ↥K))) := by
    intro m hm
    obtain ⟨𝔮, h𝔮, hodd⟩ := hF9 m (hidx m hm)
    have hspec := Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := (s.f m).1)
      (hfin m hm)
    have heq : 𝔮 = Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (s.f m).1 (hfin m hm) :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
        (by rw [← h𝔮, hspec])
    rwa [heq] at hodd
  -- ## 2. the Kummer level `ΛK` of the four classes, and its instances
  let b₁ : (↥K)ˣ := (s.f i).2
  let b₂ : (↥K)ˣ := (s.f j).2
  let b₃ : (↥K)ˣ := (s.f N).2
  let b₄ : (↥K)ˣ := (s.f i).2 * (s.f j).2 * (s.f N).2
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  let ℓh : (↥K)ˣ → IntermediateField ↥K Ω :=
    fun w => Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := 2) w
  let M₁ : IntermediateField ↥K Ω := ℓh b₁ ⊔ ℓh b₂
  let M₂ : IntermediateField ↥K Ω := ℓh b₃ ⊔ ℓh b₄
  let ΛK : IntermediateField ↥K Ω := M₁ ⊔ M₂
  haveI hℓ₁ : FiniteDimensional ↥K (ℓh b₁) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (K := K) (Ω := Ω) (p := 2)
      ⟨ζ, hζK⟩ hζK' b₁
  haveI hℓ₂ : FiniteDimensional ↥K (ℓh b₂) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (K := K) (Ω := Ω) (p := 2)
      ⟨ζ, hζK⟩ hζK' b₂
  haveI hℓ₃ : FiniteDimensional ↥K (ℓh b₃) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (K := K) (Ω := Ω) (p := 2)
      ⟨ζ, hζK⟩ hζK' b₃
  haveI hℓ₄ : FiniteDimensional ↥K (ℓh b₄) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (K := K) (Ω := Ω) (p := 2)
      ⟨ζ, hζK⟩ hζK' b₄
  haveI hM₁fd : FiniteDimensional ↥K M₁ := IntermediateField.finiteDimensional_sup _ _
  haveI hM₂fd : FiniteDimensional ↥K M₂ := IntermediateField.finiteDimensional_sup _ _
  haveI hM₁gal : IsGalois ↥K M₁ :=
    (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
      ⟨ζ, hζK⟩ hζK' b₁ b₂).2.1
  haveI hM₂gal : IsGalois ↥K M₂ :=
    (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
      ⟨ζ, hζK⟩ hζK' b₃ b₄).2.1
  have hΛKgal : IsGalois ↥K ΛK :=
    (Work.SSGRoute.ZConstruction.galois_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
      M₁ M₂
      (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
        ⟨ζ, hζK⟩ hζK' b₁ b₂).2.2.2
      (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
        ⟨ζ, hζK⟩ hζK' b₃ b₄).2.2.2
      (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
        ⟨ζ, hζK⟩ hζK' b₁ b₂).2.2.1
      (Work.SSGRoute.ZConstruction.hLevel_sup_structure (p := 2) (k := k) (Ω := Ω) (K := K)
        ⟨ζ, hζK⟩ hζK' b₃ b₄).2.2.1).1
  haveI hΛKgal' : IsGalois ↥K ΛK := hΛKgal
  haveI hΛKfd : FiniteDimensional ↥K ΛK := IntermediateField.finiteDimensional_sup _ _
  haveI hΛKnf : NumberField ↥ΛK := NumberField.of_module_finite ↥K ↥ΛK
  have hle₁ : ℓh b₁ ≤ ΛK := le_trans le_sup_left le_sup_left
  have hle₂ : ℓh b₂ ≤ ΛK := le_trans le_sup_right le_sup_left
  have hle₃ : ℓh b₃ ≤ ΛK := le_trans le_sup_left le_sup_right
  have hle₄ : ℓh b₄ ≤ ΛK := le_trans le_sup_right le_sup_right
  -- ## 3. the two auxiliary steps of the verification
  have cl4 : ∀ m : ℕ, m ≤ N → ∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B') →
      ∀ σ ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 σ = y σ := by
    intro m hm B' hB'fin hB'S σ hσ
    obtain ⟨A₀, hA₀, hA₀B'⟩ := hB'S
    obtain ⟨A, hA, hAK⟩ :=
      Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (S := S) (f := s.f) (m := m)
        hA₀ hA₀B'
    obtain ⟨v, hvK, hvA⟩ := hAK
    obtain ⟨w, hw⟩ := hA₀B'
    have hAconj : ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A :=
      ⟨A₀, hA₀, ⟨v⁻¹ * w, by rw [mul_smul, hw, ← hvA, inv_smul_smul]⟩⟩
    have hσ'K : v⁻¹ * σ * v ∈ K.fixingSubgroup :=
      K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hvK)
        (Subgroup.mem_inf.mp hσ).2) hvK
    have hσ'D : v⁻¹ * σ * v ∈ SSGRoute.decomp k A := by
      show (v⁻¹ * σ * v) • A = A
      rw [mul_smul, mul_smul, hvA, (Subgroup.mem_inf.mp hσ).1, ← hvA, inv_smul_smul]
    have hpresc : Work.SSGRoute.ZDataTwo.TwoRec.prescDatum (K := K) ζ hζ hζK S y s.f m A
        (v⁻¹ * σ * v) = 0 :=
      congrFun (Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_zero_of_isConjPlace (K := K)
        (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y) (f := s.f) (m := m) (A := A)
        hAconj) (v⁻¹ * σ * v)
    have hreal := hF6 m (hidx m hm) A hA (v⁻¹ * σ * v) ⟨hσ'D, hσ'K⟩
    rw [hpresc, add_zero] at hreal
    have hconj := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj (K := K) (ζ := ζ) (hζ := hζ)
      (hζK := hζK) (b := (s.f m).2) hvK (v⁻¹ * σ * v)
    rw [show v * (v⁻¹ * σ * v) * v⁻¹ = σ from by group] at hconj
    have hyconj := Work.SSGRoute.ZDataMup.additive_conj_invariant (K := K) y hy
      (K.fixingSubgroup.inv_mem hvK) (Subgroup.mem_inf.mp hσ).2
    rw [inv_inv] at hyconj
    rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
      (s.f m).2 σ, hconj, hreal, ← hyconj]
  have hcomp : ∀ x : ℕ, x = i ∨ x = j ∨ x = N → ∀ B' : ValuationSubring Ω,
      SSGRoute.IsConjPlace k (s.f x).1 B' →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • (s.f x).1 = B') →
      ∀ u ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ ((s.f i).2 * (s.f j).2 * (s.f N).2) u = 0 := by
    intro x hx B' hB'conj hB'notK u hu
    have hxN : x ≤ N := by
      rcases hx with h | h | h <;> omega
    obtain ⟨σ, hσ⟩ := hB'conj
    have hσK : σ ∉ K.fixingSubgroup := by
      intro h
      exact hB'notK ⟨σ, h, hσ⟩
    rw [← hσ] at hu
    by_cases hInv : (SSGRoute.res k K σ) ^ 2 = 1
    · rw [Work.SSGRoute.ZDataTwo.threeTerm_eq_of_mul k Ω K ζ hζ hζK (s.f i).2 (s.f j).2
        (s.f N).2]
      rw [_root_.Pi.add_apply, _root_.Pi.add_apply, hclaim i x σ hσK hInv u hu,
        hclaim j x σ hσK hInv u hu, hclaim N x σ hσK hInv u hu]
      decide
    · -- `ρ := res k K σ` is not an involution: the coefficient computation at the sibling of `Q_x`
      set ρ : K ≃ₐ[k] K := SSGRoute.res k K σ with hρdef
      have hρ1 : ρ ≠ 1 := by
        intro h
        exact hσK (by rw [← IntermediateField.restrictNormalHom_ker K]; exact h)
      have hρ2 : ¬ IsInv (⟨ρ, hρ1⟩ : Gam K) := by
        rw [IsInv]
        simpa only [hρdef, Subtype.coe_mk] using hInv
      -- the canonical sibling `A = ρ Q_x` of the escape prime, and the conjugating element
      set A : ValuationSubring Ω := Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f x).1 with hAdef
      have hAfin : SSGRoute.IsFinPlace k A :=
        (Work.SSGRoute.isFinPlace_smul_iff (k := k) (s.f x).1
          (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr (hfin x hxN)
      set w : Ω ≃ₐ[k] Ω := σ * (Work.SSGRoute.ZDataMup.galLift K ρ)⁻¹ with hwdef
      have hwK : w ∈ K.fixingSubgroup := by
        rw [hwdef, ← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
          Work.SSGRoute.ZDataMup.galLift_spec, hρdef, mul_inv_cancel]
      have hwA : w • A = B' := by
        rw [hwdef, hAdef, Work.SSGRoute.ZDataMup.siblingPlace, mul_smul, inv_smul_smul]
        exact hσ
      -- the three classes, and the product, kill the inertia at `A`
      have hnotA : ∀ (m : ℕ), m ≤ N → ¬ Work.SSGRoute.gesKConj K (s.f m).1 A := by
        intro m hm hconj
        have hkx : SSGRoute.IsConjPlace k ((s.f m).1) ((s.f x).1) := by
          have h1 : SSGRoute.IsConjPlace k ((s.f m).1) A :=
            Work.SSGRoute.NodeS37.gesKConj_isConjPlace hconj
          rw [hAdef] at h1
          exact SSGRoute.isConjPlace_trans h1
            (Work.SSGRoute.NodeS37.siblingPlace_isConjPlace ρ (s.f x).1)
        by_cases hmx : m = x
        · rw [hmx] at hconj
          exact (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K hρ1 (hsplitK x hxN)) hconj
        · rcases lt_or_gt_of_ne hmx with hlt | hgt
          · exact hF4 m x hlt (by omega) hkx
          · exact hF4 x m hgt (by omega) (SSGRoute.isConjPlace_symm hkx)
      have hkill4 : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2) u = 0 := by
        have hsum : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2)
            = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f i).2
              + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2
              + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f N).2 := by
          rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK ((s.f i).2 * (s.f j).2) (s.f N).2,
            Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK (s.f i).2 (s.f j).2]
        intro u hu huI
        rw [hsum, _root_.Pi.add_apply, _root_.Pi.add_apply,
          hconfm i A hAfin (hnotA i (le_of_lt (lt_trans hij hjN))) u hu huI,
          hconfm j A hAfin (hnotA j (le_of_lt hjN)) u hu huI,
          hconfm N A hAfin (hnotA N le_rfl) u hu huI]
        decide
      -- `ΛK` is unramified at `A`
      have hunrΛ : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥ΛK)
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hAfin) := by
        refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup
          (K := ↥K) (Ω := Ω) ΛK (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hAfin) ?_
        intro B hB hBc σ' hσ'
        rw [show ΛK = M₁ ⊔ M₂ from rfl, IntermediateField.fixingSubgroup_sup]
        refine ⟨?_, ?_⟩
        · rw [show M₁ = ℓh b₁ ⊔ ℓh b₂ from rfl, IntermediateField.fixingSubgroup_sup]
          exact ⟨Work.SSGRoute.NodeS35.inertia_subset_fixingSubgroup_hLevel (K := K) (p := 2)
              (k := k) (Ω := Ω) ζ hζ hζK b₁ A hAfin
              (hconfm i A hAfin (hnotA i (le_of_lt (lt_trans hij hjN)))) B hB hBc σ' hσ',
            Work.SSGRoute.NodeS35.inertia_subset_fixingSubgroup_hLevel (K := K) (p := 2)
              (k := k) (Ω := Ω) ζ hζ hζK b₂ A hAfin
              (hconfm j A hAfin (hnotA j (le_of_lt hjN))) B hB hBc σ' hσ'⟩
        · rw [show M₂ = ℓh b₃ ⊔ ℓh b₄ from rfl, IntermediateField.fixingSubgroup_sup]
          exact ⟨Work.SSGRoute.NodeS35.inertia_subset_fixingSubgroup_hLevel (K := K) (p := 2)
              (k := k) (Ω := Ω) ζ hζ hζK b₃ A hAfin
              (hconfm N A hAfin (hnotA N le_rfl)) B hB hBc σ' hσ',
            Work.SSGRoute.NodeS35.inertia_subset_fixingSubgroup_hLevel (K := K) (p := 2)
              (k := k) (Ω := Ω) ζ hζ hζK b₄ A hAfin hkill4 B hB hBc σ' hσ'⟩
      -- `χ_B` kills the level-`ΛK` kernel
      have hkerM : ∀ u : K.fixingSubgroup,
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ΛK
            ((IntermediateField.fixingSubgroupEquiv K) u) = 1 →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2) ↑u = 0 := by
        intro u hu
        have hfixΛ : ∀ x ∈ ΛK, ((IntermediateField.fixingSubgroupEquiv K) u) x = x :=
          (AlgEquiv.restrictNormal_eq_one_iff ΛK _).mp hu
        have hmem4 : (IntermediateField.fixingSubgroupEquiv K) u ∈ (ℓh b₄).fixingSubgroup :=
          (IntermediateField.mem_fixingSubgroup_iff (ℓh b₄) _).mpr
            (fun x hx => hfixΛ x (hle₄ hx))
        have hzero := (Work.SSGRoute.ZDataMup.OddForm.odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup
          (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζK' b₄
          ((IntermediateField.fixingSubgroupEquiv K) u)).mpr hmem4
        rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := (s.f i).2 * (s.f j).2 * (s.f N).2) (σ := (↑u : Ω ≃ₐ[k] Ω))
          u.2]
        exact hzero
      -- a pinned Frobenius at `ΛK` and the vanishing of `χ_B` there
      obtain ⟨ψ, hψ, hpin⟩ := Work.SSGRoute.H9.swPinnedFrob_exists (p := 2) (k := k) (Ω := Ω)
        (K := K) ΛK A hAfin
      -- THE ONE REMAINING GAP: the *coefficient computation* at the sibling `A = ρ Q_x` of `Q_x`,
      -- i.e. `χ_{b_i b_j b_N}(ψ) = 0` for `ψ` pinned at `ΛK` for `A`.  The plan (all ingredients
      -- below are available in this file / in the imported modules):
      -- * `v := pinValue (fun _ => ((s.f x).1, (s.f x).2)) (fun _ => hfin x hxN) 0 ρ`;
      -- * `m = x`: `χ_{b_x}(ψ) = v` by `pinValue_of_pinnedAtLevel` (with `hkill := hconfm x A hAfin
      --   (hnotA x hxN)` and `hle := hleₓ`);
      -- * `m > x`: `χ_{b_m}(ψ) = eGam x m ⟨ρ,hρ1⟩ • v` by `preTwo_siblingValue` (`l := x`) at `ψ`
      --   composed with the `m = x` identification;
      -- * `m < x`: `χ_{b_m}(ψ) = pinValue (Q_x,b_m) ρ` [D3]` = pinValue (Q_m,b_x) ρ⁻¹`
      --   [`pinValue_cross_two`, Qs := Q_m, Qt := Q_x, bs := b_m, bt := b_x, σ := ρ; its hsep comes
      --   from `hF4`, its hconfs/hconft from `hconfm`, its hcounts/hcountt from `hoddm`, its hinf
      --   from `hinfm`]` = eGam m x ⟨ρ⁻¹,_⟩ • v` [D3 at a second pinned element `ψ'` for
      --   `siblingPlace K ρ⁻¹ (s.f m).1`, then `preTwo_siblingValue` (`l := m`), then
      --   `pinValue_self_symm`, then the shoe box `pinValue_{b_m}(ρ) = pinValue_{b_x}(ρ)` which
      --   follows from `hshij`/`hshjN` through `pinValue_self_symm` and the definition
      --   `valSeq f m υ = pinValue (f m) (theta υ)`];
      -- * sum the three terms and apply `eGam_coefficients' i j N hw1 hw2 hw3` (the identity
      --   selected by the case `x = i`, `x = j`, `x = N`) to get `(…) • v = 0`.
      have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          ((s.f i).2 * (s.f j).2 * (s.f N).2) ψ = 0 := by
        -- ## 0. the tool kit at the sibling `A = ρ Q_x` of `Q_x`
        have hρi1 : ρ⁻¹ ≠ 1 := fun h => hρ1 (inv_eq_one.mp h)
        have hgi : (⟨ρ⁻¹, hρi1⟩ : Gam K) = ginv (⟨ρ, hρ1⟩ : Gam K) := Subtype.ext rfl
        -- `ΛK` contains the Kummer level of every one of the three classes
        have hle_x : ℓh (s.f x).2 ≤ ΛK := by
          rcases hx with h | h | h
          · rw [h]; exact hle₁
          · rw [h]; exact hle₂
          · rw [h]; exact hle₃
        -- the value of the x-th class at the pinned Frobenius
        set v : ZMod 2 :=
          Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f x) ρ with hv
        -- `sibVal` is `pinValue` at a finite place
        have hsibval : ∀ (q : ValuationSubring Ω × (↥K)ˣ)
            (hq : SSGRoute.IsFinPlace k q.1) (σ : K ≃ₐ[k] K),
            Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK q σ
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => q)
                  (fun _ => hq) 0 σ := by
          intro q hq σ
          rw [Work.SSGRoute.ZDataTwo.TwoRec.sibVal]
          exact dif_pos hq
        -- the Kummer symmetry `ρ ↔ ρ⁻¹` of every stage
        have hself : ∀ m (hm : m ≤ N),
            Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                (fun _ => ((s.f m).1, (s.f m).2)) (fun _ => hfin m hm) 0 ρ⁻¹
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                (fun _ => ((s.f m).1, (s.f m).2)) (fun _ => hfin m hm) 0 ρ := by
          intro m hm
          have h := Work.SSGRoute.ZDataTwo.TwoRec.pinValue_self_symm (K := K) ζ hζ hζK
            (s.f m).1 (hfin m hm) (hsplitK m hm) (s.f m).2 (hconfm m) (hoddm m hm)
            (hinfm m hm) ρ⁻¹
          simpa only [inv_inv] using h
        -- `theta` selects `ρ` or `ρ⁻¹` at the index `ρ`
        have htheta : (theta (⟨ρ, hρ1⟩ : Gam K)).1 = ρ
            ∨ (theta (⟨ρ, hρ1⟩ : Gam K)).1 = ρ⁻¹ := by
          rcases theta_eq_self_or_ginv (⟨ρ, hρ1⟩ : Gam K) with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (by rw [h, ginv_val])
        -- the `θ`-indexing does not change the value at the `ρ`-sibling
        have hkind : ∀ m (hm : m ≤ N),
            Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f m) ρ
              = Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f m)
                  (theta (⟨ρ, hρ1⟩ : Gam K)).1 := by
          intro m hm
          rcases htheta with h | h
          · rw [h]
          · rw [h, hsibval (s.f m) (hfin m hm) ρ, hsibval (s.f m) (hfin m hm) ρ⁻¹]
            exact (hself m hm).symm
        -- ## 1. the shoe box of the recursion at the `ρ`-level
        have hkey : ∀ w : ℕ, (w = i ∨ w = j ∨ w = N) →
            Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f w)
                (theta (⟨ρ, hρ1⟩ : Gam K)).1
              = Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f j)
                  (theta (⟨ρ, hρ1⟩ : Gam K)).1 := by
          intro w hw
          rcases hw with h | h | h
          · rw [h]; exact (hshij (⟨ρ, hρ1⟩ : Gam K)).symm
          · rw [h]
          · rw [h]; exact hshjN (⟨ρ, hρ1⟩ : Gam K)
        have hshoeij : Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f i) ρ
            = Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f j) ρ :=
          (hkind i (le_of_lt (lt_trans hij hjN))).trans
            ((hkey i (Or.inl rfl)).trans (hkind j (le_of_lt hjN)).symm)
        have hshoeN : Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f N) ρ
            = Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f j) ρ :=
          (hkind N le_rfl).trans
            ((hkey N (Or.inr (Or.inr rfl))).trans (hkind j (le_of_lt hjN)).symm)
        have hshoejN : Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f j) ρ
            = Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f N) ρ :=
          hshoeN.symm
        -- ## 2. the value of the `x`-th class at `ψ`
        have hx_psi : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f x).2 ψ = v := by
          rw [hv, hsibval (s.f x) (hfin x hxN) ρ]
          exact pinValue_of_pinnedAtLevel (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
            (b := (s.f x).2) (Q := (s.f x).1) (hQ := hfin x hxN) (ρ := ρ) (hρ := hρ1)
            (Λ := ΛK) (hle := hle_x) (hkill := hconfm x A hAfin (hnotA x hxN)) (ψ := ψ)
            (hψ := hψ) (hpin := hpin)
        -- ## 3. `m > x`: the prescription of the rule at `ψ`
        have hgt_gen : ∀ m (hmx : x < m) (hmN : m ≤ N),
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
              = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f x m ⟨ρ, hρ1⟩ • v := by
          intro m hmx hmN
          have h := preTwo_siblingValue (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs
            (l := x) (m := m) (ρ := ρ) hmx hρ1 ψ hψ
          rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
              (s.f m).2 ψ,
            Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
              (s.f x).2 ψ] at h
          rw [h, hx_psi]
        -- ## 4. `m < x`: the crossed two-place identity through the `ρ⁻¹`-sibling of `Q_m`
        have hlt_gen : ∀ m (hmx : m < x) (hmN : m ≤ N)
            (hshoem : Work.SSGRoute.ZDataTwo.TwoRec.sibVal (K := K) ζ hζ hζK (s.f m) ρ = v)
            (hmle : ℓh (s.f m).2 ≤ ΛK),
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
              = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f m x ⟨ρ⁻¹, hρi1⟩ • v := by
          intro m hmx hmN hshoem hmle
          -- (a) the value at the `ρ`-sibling of `Q_x`
          have h1 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                  (fun _ => ((s.f x).1, (s.f m).2)) (fun _ => hfin x hxN) 0 ρ :=
            pinValue_of_pinnedAtLevel (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
              (b := (s.f m).2) (Q := (s.f x).1) (hQ := hfin x hxN) (ρ := ρ) (hρ := hρ1)
              (Λ := ΛK) (hle := hmle) (hkill := hconfm m A hAfin (hnotA m hmN)) (ψ := ψ)
              (hψ := hψ) (hpin := hpin)
          -- (b) the crossed two-place identity
          have hsep : ∀ σ : K ≃ₐ[k] K, σ ≠ 1 →
              ¬ Work.SSGRoute.gesKConj K (s.f m).1
                  (Work.SSGRoute.ZDataMup.galLift K σ • (s.f x).1) := by
            intro σ _ hc
            obtain ⟨τ, _hτK, hτ⟩ := hc
            exact hF4 m x hmx (hidx x hxN)
              ⟨(Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * τ, by
                rw [mul_smul, hτ, inv_smul_smul]⟩
          have h2 : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                (fun _ => ((s.f x).1, (s.f m).2)) (fun _ => hfin x hxN) 0 ρ
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                (fun _ => ((s.f m).1, (s.f x).2)) (fun _ => hfin m hmN) 0 ρ⁻¹ :=
            Work.SSGRoute.ZDataTwo.TwoRec.pinValue_cross_two (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
              (Qs := (s.f m).1) (hQsfin := hfin m hmN) (Qt := (s.f x).1) (hQtfin := hfin x hxN)
              (bs := (s.f m).2) (bt := (s.f x).2) hsep (hconfm m) (hconfm x)
              (hoddm m hmN) (hoddm x hxN) (hinfm m hmN) ρ
          -- (c) a pinned Frobenius at the `ρ⁻¹`-sibling of `Q_m`
          have hAmfin : SSGRoute.IsFinPlace k
              (Work.SSGRoute.ZDataMup.siblingPlace K ρ⁻¹ (s.f m).1) :=
            (Work.SSGRoute.isFinPlace_smul_iff (k := k) (s.f m).1
              (Work.SSGRoute.ZDataMup.galLift K ρ⁻¹)).mpr (hfin m hmN)
          obtain ⟨ψ', hψ', hpin'⟩ := Work.SSGRoute.H9.swPinnedFrob_exists (p := 2) (k := k) (Ω := Ω)
            (K := K) ΛK (Work.SSGRoute.ZDataMup.siblingPlace K ρ⁻¹ (s.f m).1) hAmfin
          have hnotAm : ¬ Work.SSGRoute.gesKConj K (s.f m).1
              (Work.SSGRoute.ZDataMup.siblingPlace K ρ⁻¹ (s.f m).1) :=
            Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hρi1 (hsplitK m hmN)
          have hm' : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ'
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                  (fun _ => ((s.f m).1, (s.f m).2)) (fun _ => hfin m hmN) 0 ρ⁻¹ :=
            pinValue_of_pinnedAtLevel (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
              (b := (s.f m).2) (Q := (s.f m).1) (hQ := hfin m hmN) (ρ := ρ⁻¹) (hρ := hρi1)
              (Λ := ΛK) (hle := hmle) (hkill := hconfm m _ hAmfin hnotAm) (ψ := ψ')
              (hψ := hψ') (hpin := hpin')
          have hnotAx : ¬ Work.SSGRoute.gesKConj K (s.f x).1
              (Work.SSGRoute.ZDataMup.siblingPlace K ρ⁻¹ (s.f m).1) := by
            intro hc
            obtain ⟨τ, _hτK, hτ⟩ := hc
            exact hF4 m x hmx (hidx x hxN) (SSGRoute.isConjPlace_symm
              ⟨(Work.SSGRoute.ZDataMup.galLift K ρ⁻¹)⁻¹ * τ, by
                rw [mul_smul, hτ, Work.SSGRoute.ZDataMup.siblingPlace, inv_smul_smul]⟩)
          have hx' : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f x).2 ψ'
              = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                  (fun _ => ((s.f m).1, (s.f x).2)) (fun _ => hfin m hmN) 0 ρ⁻¹ :=
            pinValue_of_pinnedAtLevel (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
              (b := (s.f x).2) (Q := (s.f m).1) (hQ := hfin m hmN) (ρ := ρ⁻¹) (hρ := hρi1)
              (Λ := ΛK) (hle := hle_x) (hkill := hconfm x _ hAmfin hnotAx) (ψ := ψ')
              (hψ := hψ') (hpin := hpin')
          -- (d) the prescription of the `x`-th class at the sibling of `Q_m`
          have hstep : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f x).2 ψ'
              = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f m x ⟨ρ⁻¹, hρi1⟩ •
                  Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ' := by
            have h := preTwo_siblingValue (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs
              (l := m) (m := x) (ρ := ρ⁻¹) hmx hρi1 ψ' hψ'
            rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
                (s.f x).2 ψ',
              Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
                (s.f m).2 ψ'] at h
            exact h
          -- (e) the shoe box at `ρ` closes the computation
          have h3 : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
                (fun _ => ((s.f m).1, (s.f x).2)) (fun _ => hfin m hmN) 0 ρ⁻¹
              = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f m x ⟨ρ⁻¹, hρi1⟩ • v := by
            rw [← hx', hstep, hm']
            congr 1
            rw [hself m hmN, ← hsibval (s.f m) (hfin m hmN) ρ]
            exact hshoem
          rw [h1, h2, h3]
        -- ## 5. the three cases, and the coefficient identity of the rule (4)
        rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK ((s.f i).2 * (s.f j).2) (s.f N).2,
          Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK (s.f i).2 (s.f j).2,
          _root_.Pi.add_apply, _root_.Pi.add_apply]
        rcases hx with hxi | hxj | hxNc
        · -- `x = i`: the own term is first
          rw [hxi] at hv hx_psi hgt_gen hlt_gen
          have hiN : i ≤ N := le_of_lt (lt_trans hij hjN)
          have hjN' : j ≤ N := le_of_lt hjN
          have hj := hgt_gen j hij hjN'
          have hN := hgt_gen N (lt_trans hij hjN) le_rfl
          rw [hx_psi, hj, hN]
          have hc := (eGam_coefficients' (K := K) ζ hζ hζK s.f i j N hw1 hw2 hw3).1
            ⟨ρ, hρ1⟩ hρ2
          exact ZMod2_three_sum_left hc
        · -- `x = j`: the own term is in the middle, `i` comes from the crossed identity
          rw [hxj] at hv hx_psi hgt_gen hlt_gen
          have hiN : i ≤ N := le_of_lt (lt_trans hij hjN)
          have hjN' : j ≤ N := le_of_lt hjN
          have hN := hgt_gen N hjN le_rfl
          have hi := hlt_gen i hij hiN (hshoeij.trans hv.symm) hle₁
          rw [hi, hx_psi, hN]
          have hc := (eGam_coefficients' (K := K) ζ hζ hζK s.f i j N hw1 hw2 hw3).2.1
            ⟨ρ, hρ1⟩ hρ2
          rw [← hgi] at hc
          exact ZMod2_three_sum_mid hc
        · -- `x = N`: the own term is last, both other classes come from the crossed identity
          rw [hxNc] at hv hx_psi hgt_gen hlt_gen
          have hiN : i ≤ N := le_of_lt (lt_trans hij hjN)
          have hjN' : j ≤ N := le_of_lt hjN
          have hi := hlt_gen i (lt_trans hij hjN) hiN
            (hshoeij.trans (hshoejN.trans hv.symm)) hle₁
          have hj := hlt_gen j hjN hjN' (hshoejN.trans hv.symm) hle₂
          rw [hi, hj, hx_psi]
          have hc := (eGam_coefficients' (K := K) ζ hζ hζK s.f i j N hw1 hw2 hw3).2.2
            ⟨ρ, hρ1⟩ hρ2
          rw [← hgi] at hc
          exact ZMod2_three_sum_right hc
      have hcanonZ : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2) u = 0 :=
        Work.SSGRoute.H9.swLocalValue_eq_zero_of_level_isFrobAtPrime (p := 2) (K := K)
          ΛK A hAfin hunrΛ (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2))
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ
            ((s.f i).2 * (s.f j).2 * (s.f N).2)) hkerM ψ hψ hpin hval
      -- transport along the `K`-conjugacy `B' = w • A`
      have huB : u • B' = B' := by
        rw [← hσ]
        exact (Subgroup.mem_inf.mp hu).1
      have hu'K : w⁻¹ * u * w ∈ K.fixingSubgroup :=
        K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hwK)
          (Subgroup.mem_inf.mp hu).2) hwK
      have hu'D : w⁻¹ * u * w ∈ SSGRoute.decomp k A := by
        show (w⁻¹ * u * w) • A = A
        rw [mul_smul, mul_smul, hwA, huB, ← hwA, inv_smul_smul]
      have hcw := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj (K := K) (ζ := ζ) (hζ := hζ)
        (hζK := hζK) (b := (s.f i).2 * (s.f j).2 * (s.f N).2)
        (K.fixingSubgroup.inv_mem hwK) u
      rw [show w⁻¹ * u * (w⁻¹)⁻¹ = w⁻¹ * u * w from by rw [inv_inv]] at hcw
      rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        ((s.f i).2 * (s.f j).2 * (s.f N).2) u, ← hcw]
      exact hcanonZ _ ⟨hu'D, hu'K⟩
  refine ⟨{(s.f i).1, (s.f j).1, (s.f N).1},
    (s.f i).2 * (s.f j).2 * (s.f N).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) finiteness
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP
    · rw [hP]; exact hfin i (le_of_lt (lt_trans hij hjN))
    · rw [hP]; exact hfin j (le_of_lt hjN)
    · rw [hP]; exact hfin N le_rfl
  · -- (2) splitness in `Λ`
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP
    · rw [hP]; exact hF2 i (hidx i (le_of_lt (lt_trans hij hjN)))
    · rw [hP]; exact hF2 j (hidx j (le_of_lt hjN))
    · rw [hP]; exact hF2 N (hidx N le_rfl)
  · -- (3) the escape primes are not `k`-conjugate to `S`
    intro P hP A hA hconj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP
    · rw [hP] at hconj
      obtain ⟨A', hA', hA'Q⟩ := Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S
        (K := K) (S := S) (f := s.f) (m := i) hA hconj
      exact hF5 i (hidx i (le_of_lt (lt_trans hij hjN))) A' hA' hA'Q
    · rw [hP] at hconj
      obtain ⟨A', hA', hA'Q⟩ := Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S
        (K := K) (S := S) (f := s.f) (m := j) hA hconj
      exact hF5 j (hidx j (le_of_lt hjN)) A' hA' hA'Q
    · rw [hP] at hconj
      obtain ⟨A', hA', hA'Q⟩ := Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S
        (K := K) (S := S) (f := s.f) (m := N) hA hconj
      exact hF5 N (hidx N le_rfl) A' hA' hA'Q
  · -- (4) agreement with `y` at the `S`-blocks
    intro B' hB'fin hB'S σ hσ
    rw [Work.SSGRoute.ZDataTwo.threeTerm_eq_of_mul k Ω K ζ hζ hζK (s.f i).2 (s.f j).2
      (s.f N).2]
    rw [_root_.Pi.add_apply, _root_.Pi.add_apply,
      cl4 i (le_of_lt (lt_trans hij hjN)) B' hB'fin hB'S σ hσ,
      cl4 j (le_of_lt hjN) B' hB'fin hB'S σ hσ,
      cl4 N le_rfl B' hB'fin hB'S σ hσ]
    exact ZMod2_three_add (y σ)
  · -- (5) the involutions
    intro c hc hc2
    rw [Work.SSGRoute.ZDataTwo.threeTerm_eq_of_mul k Ω K ζ hζ hζK (s.f i).2 (s.f j).2
      (s.f N).2]
    rw [_root_.Pi.add_apply, _root_.Pi.add_apply,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f i).2 c,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f j).2 c,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f N).2 c,
      hinfm i (le_of_lt (lt_trans hij hjN)) c hc hc2, hinfm j (le_of_lt hjN) c hc hc2,
      hinfm N le_rfl c hc hc2]
    decide
  · -- (6) the inertia outside the `S`-classes and the `Pset`-orbits
    intro B' hB'fin hB'notS hB'notP σ hσK hσI
    rw [Work.SSGRoute.ZDataTwo.threeTerm_eq_of_mul k Ω K ζ hζ hζK (s.f i).2 (s.f j).2
      (s.f N).2]
    rw [_root_.Pi.add_apply, _root_.Pi.add_apply,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f i).2 σ,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f j).2 σ,
      Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
        (s.f N).2 σ]
    have h1 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f i).2 σ = 0 :=
      hconfm i B' hB'fin (by
        rintro ⟨τ, hτK, hτB'⟩
        exact hB'notP (s.f i).1 (by simp) τ hτK hτB') σ hσK hσI
    have h2 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 σ = 0 :=
      hconfm j B' hB'fin (by
        rintro ⟨τ, hτK, hτB'⟩
        exact hB'notP (s.f j).1 (by simp) τ hτK hτB') σ hσK hσI
    have h3 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f N).2 σ = 0 :=
      hconfm N B' hB'fin (by
        rintro ⟨τ, hτK, hτB'⟩
        exact hB'notP (s.f N).1 (by simp) τ hτK hτB') σ hσK hσI
    rw [h1, h2, h3]
    decide
  · -- (7) the companions of the three escape primes
    intro P hP B' hB'conj hB'notK u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP
    · exact hcomp i (Or.inl rfl) B' (by rw [← hP]; exact hB'conj) (by rwa [← hP]) u hu
    · exact hcomp j (Or.inr (Or.inl rfl)) B' (by rw [← hP]; exact hB'conj) (by rwa [← hP]) u hu
    · exact hcomp N (Or.inr (Or.inr rfl)) B' (by rw [← hP]; exact hB'conj) (by rwa [← hP]) u hu

end Work.SSGRoute.NodeS37
