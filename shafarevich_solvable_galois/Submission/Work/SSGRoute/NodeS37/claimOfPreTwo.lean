import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.pinnedValueOfHistoryOfInertSquare
import Submission.Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.pinValue_cross_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

open scoped Pointwise

/-- **Every entry of a history satisfying the prefix invariant at all stages is a finite place.** -/
theorem preTwo_finPlace {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ j : ℕ, SSGRoute.IsFinPlace k ((s.f j).1) :=
  fun j => (hs (j + 1)).1 j (Nat.lt_succ_self j)

/-! ## The `m > l` case: the prescription of the rule (Schmidt--Wingberg condition (3))

For `m > l` the `σ`-sibling of the escape prime `Q_l` is `K`-conjugate to a block of the stage-`m`
place set `TBlock S s.f m`, whose attachment is the pair `(l, res σ)` — the branch of the rule (4)
which is *prescribed to be zero* at an involution (`eGam = 0` on the `IsInv` branch).  Hence
`χ_{b_m} = eGam · χ_{b_l} = 0` on that whole local group, and the invariance of `χ_{b_m}` under
`G_K`-conjugation transports the vanishing to the local group of the sibling itself.

This is the `s > t` case of the paper's p. 17 sentence; no arithmetic is used. -/

theorem claimOfPreTwo_gt {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m l : ℕ, l < m → ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m l hlm σ hσK hσ2 u hu
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (m + 1)
  have hl_lt : l < m + 1 := by omega
  have hm_lt : m < m + 1 := Nat.lt_succ_self m
  have hsplit_l : SSGRoute.IsSplitIn k K (s.f l).1 :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le hKΛ (hsplit l hl_lt)
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with htdef
  have ht_ne : t ≠ 1 := by
    intro ht1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← htdef]
      exact ht1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  -- the sibling of `Q_l` at the index `res σ` is `K`-conjugate to `σ • Q_l`
  have hAtt1 : Work.SSGRoute.gesKConj K (σ • (s.f l).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, htdef, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • (s.f l).1)
        = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  -- the block of the stage-`m` place set covering `σ • Q_l`
  obtain ⟨A', hA'mem, hA'⟩ := Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_Q (K := K)
    (S := S) (f := s.f) (m := m) (j := l) hlm (B := σ • (s.f l).1) ⟨σ, rfl⟩
  have hAtt : Work.SSGRoute.gesKConj K A'
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) :=
    Work.SSGRoute.H9.swGesKConj_trans hA' hAtt1
  -- that block is not `k`-conjugate to an element of `S`
  have hSnotA' : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A' := by
    rintro ⟨A₀, hA₀, hc⟩
    have hA'c : SSGRoute.IsConjPlace k A' (s.f l).1 :=
      Work.SSGRoute.isConjPlace_trans
        (hA'.imp fun τ hτ => hτ.2) ⟨σ⁻¹, by rw [inv_smul_smul]⟩
    have hA₀Q : SSGRoute.IsConjPlace k A₀ (s.f l).1 :=
      Work.SSGRoute.isConjPlace_trans hc hA'c
    obtain ⟨A'', hA'', hA''Q⟩ := Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K)
      (S := S) (f := s.f) (m := l) hA₀ hA₀Q
    exact hexcl l hl_lt A'' hA'' hA''Q
  -- the attachment of `A'` is unique, and equal to `(l, res σ)`
  have huniq_aux : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K, ρ' ≠ 1 →
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1) A' →
      l' = l ∧ ρ' = t := by
    intro l' hl' ρ' hρ' hconj
    have h12 : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1)
        (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) :=
      Work.SSGRoute.H9.swGesKConj_trans hconj hAtt
    have hconjQ : SSGRoute.IsConjPlace k ((s.f l').1) ((s.f l).1) :=
      Work.SSGRoute.isConjPlace_trans ⟨Work.SSGRoute.ZDataMup.galLift K ρ', rfl⟩
        (Work.SSGRoute.isConjPlace_trans (h12.imp fun τ hτ => hτ.2)
          ⟨(Work.SSGRoute.ZDataMup.galLift K t)⁻¹,
            by rw [Work.SSGRoute.ZDataMup.siblingPlace, inv_smul_smul]⟩)
    have hll : l' = l := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hdisjC l' l hlt (by omega) hconjQ
      · exact hdisjC l l' hgt (by omega) (Work.SSGRoute.isConjPlace_symm hconjQ)
    rw [hll] at h12
    refine ⟨hll, ?_⟩
    obtain ⟨w, hwK, hwQ⟩ := h12
    have hwQ' : w • (Work.SSGRoute.ZDataMup.galLift K ρ' • (s.f l).1)
        = Work.SSGRoute.ZDataMup.galLift K t • (s.f l).1 := hwQ
    have hw1 : SSGRoute.res k K w = 1 := by
      have : w ∈ (SSGRoute.res k K).ker := by
        rw [IntermediateField.restrictNormalHom_ker K]; exact hwK
      exact MonoidHom.mem_ker.mp this
    have hstab : (Work.SSGRoute.ZDataMup.galLift K t)⁻¹ * w * Work.SSGRoute.ZDataMup.galLift K ρ'
        ∈ SSGRoute.decomp k (s.f l).1 := by
      show ((Work.SSGRoute.ZDataMup.galLift K t)⁻¹ * w
        * Work.SSGRoute.ZDataMup.galLift K ρ') • (s.f l).1 = (s.f l).1
      rw [mul_smul, mul_smul, hwQ', inv_smul_smul]
    have hres1 : SSGRoute.res k K ((Work.SSGRoute.ZDataMup.galLift K t)⁻¹ * w
        * Work.SSGRoute.ZDataMup.galLift K ρ') = 1 := by
      have : (Work.SSGRoute.ZDataMup.galLift K t)⁻¹ * w * Work.SSGRoute.ZDataMup.galLift K ρ'
          ∈ (SSGRoute.res k K).ker := by
        rw [IntermediateField.restrictNormalHom_ker K]; exact hsplit_l hstab
      exact MonoidHom.mem_ker.mp this
    have hres2 : SSGRoute.res k K ((Work.SSGRoute.ZDataMup.galLift K t)⁻¹ * w
        * Work.SSGRoute.ZDataMup.galLift K ρ') = t⁻¹ * ρ' := by
      rw [map_mul, map_mul, map_inv, Work.SSGRoute.ZDataMup.galLift_spec,
        Work.SSGRoute.ZDataMup.galLift_spec, hw1]
      simp
    rw [hres2] at hres1
    exact (inv_mul_eq_one.mp hres1).symm
  have huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1) A' →
      l' = l ∧ ρ' = t := by
    intro l' hl' ρ' hconj
    by_cases hρ' : ρ' = 1
    · -- the `1`-sibling is the `K`-class of `Q_{l'}` itself, which cannot be `A'`
      subst hρ'
      have hsq : Work.SSGRoute.gesKConj K ((s.f l').1) (Work.SSGRoute.ZDataMup.siblingPlace K 1 (s.f l').1) :=
        ⟨Work.SSGRoute.ZDataMup.galLift K 1, ?_, rfl⟩
      · have hA'Q : Work.SSGRoute.gesKConj K A' ((s.f l').1) :=
          Work.SSGRoute.H9.swGesKConj_trans (Work.SSGRoute.H9.swGesKConj_symm hconj)
            (Work.SSGRoute.H9.swGesKConj_symm hsq)
        have hA'l : SSGRoute.IsConjPlace k A' (s.f l').1 := hA'Q.imp fun τ hτ => hτ.2
        have hA'lQ : SSGRoute.IsConjPlace k A' (s.f l).1 :=
          Work.SSGRoute.isConjPlace_trans
            (hA'.imp fun τ hτ => hτ.2) ⟨σ⁻¹, by rw [inv_smul_smul]⟩
        have hll : l' = l := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hdisjC l' l hlt (by omega)
              (Work.SSGRoute.isConjPlace_trans (Work.SSGRoute.isConjPlace_symm hA'l) hA'lQ)
          · exact hdisjC l l' hgt (by omega)
              (Work.SSGRoute.isConjPlace_trans (Work.SSGRoute.isConjPlace_symm hA'lQ) hA'l)
        rw [hll] at hA'Q
        exact absurd (Work.SSGRoute.H9.swGesKConj_trans
          (Work.SSGRoute.H9.swGesKConj_symm hA'Q) hAtt)
          (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) ht_ne hsplit_l)
      · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker,
          Work.SSGRoute.ZDataMup.galLift_spec]
    · exact huniq_aux l' hl' ρ' hρ' hconj
  -- the prescribed datum at `A'` collapses to `-y + 0 = -y`
  have hpresc := Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_of_attachment (K := K)
    (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y) (f := s.f)
    (m := m) (A := A') hSnotA' hlm (Work.SSGRoute.H9.swGesKConj_symm hAtt) huniq
  have hgam0 : Work.SSGRoute.ZDataTwo.TwoRec.eScalar (K := K) ζ hζ hζK s.f l m t = 0 := by
    rw [Work.SSGRoute.ZDataTwo.TwoRec.eScalar, dif_neg ht_ne,
      Work.SSGRoute.ZDataTwo.TwoRec.eGam]
    exact if_pos (by simpa [Work.SSGRoute.NodeS37.IsInv, htdef] using hσ2)
  -- transport the vanishing along the `K`-conjugacy `A' = v⁻¹ • (σ • Q_l)`
  obtain ⟨v, hvK, hvA⟩ := hA'
  set w : Ω ≃ₐ[k] Ω := v⁻¹ * u * v with hwdef
  have hwK : w ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hvK)
      (Subgroup.mem_inf.mp hu).2) hvK
  have hwD : w ∈ SSGRoute.decomp k A' := by
    have hvA' : v⁻¹ • (σ • (s.f l).1) = A' := by
      rw [← hvA, inv_smul_smul]
    show w • A' = A'
    rw [hwdef, mul_smul, mul_smul, hvA, (Subgroup.mem_inf.mp hu).1, hvA']
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 w
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u := by
    have h := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2
      (K.fixingSubgroup.inv_mem hvK) u
    rw [inv_inv] at h
    exact h
  have hclause := hreal m hm_lt A' hA'mem w ⟨hwD, hwK⟩
  rw [hpresc] at hclause
  simp only [hgam0, zero_smul, add_zero, add_neg_cancel] at hclause
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 := by
    rw [← hval]; exact hclause
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
    (s.f m).2 u]
  exact hfinal

/-! THE PAPER'S CLAIM (Schmidt--Wingberg arXiv:math/9809211, pp. 16--17), for a history satisfying
the `p = 2` recursion invariant `Work.SSGRoute.ZDataTwo.TwoRec.PreTwo`.

For an involution `σ` of `G(K|k)` that is *not* in `G_K` (`σ ∉ K.fixingSubgroup` and
`(res k K σ)^2 = 1`), every class of the recursion vanishes on the decomposition group of the
`σ`-sibling of every escape prime:

  `∀ m l, χ_{b_m} vanishes on decomp k (σ • Q_l) ⊓ G_K`.

`PreTwo`'s confinement clause (7) only gives that `χ_{b_m}` kills the *inertia* there, so this is
genuinely extra; it is exactly what SW p. 17 consumes (their `G₁` sentence).

The three index cases:
* `m > l`: `σ • Q_l` is `K`-conjugate to a block of `TBlock S s.f m` (`TwoRec.TBlock_covers_Q`),
  whose attachment is `(l, res σ)` with `eScalar = 0` (an involution, `TwoRec.eGam`'s `IsInv`
  branch), so `PreTwo`'s realisation clause (5) plus `TwoRec.prescDatum_eq_of_escape` give
  `χ_{b_m} = y + (-y + 0) = 0` on that whole local group (transport along `gesKConj`, as in
  `H9/swHistKExists_proved.lean`'s `Pre_step` tail).
* `m = l`: the page-16 Hilbert-symbol computation
  `z_m(Frob_{σQ_m}) = (z̃_m, σz̃_m)_{σQ_m} = ∏_{P ∣ 2bδ}(2bδ, σz̃_m)_P = ∏_{P ∈ Σ}(2bδ, σz̃_m)_P = 1`
  with `Σ` the primes dividing `2bδ` outside the primes over `2`, the archimedean primes and
  `Ram(K|k)`.  The triviality of the factors *at* those excluded primes is supplied by:
  the realisation clause (5) at the `cs(S)`-blocks over `2` / ramified in `K|k` (they exist by
  `hSram` + `TwoRec.TBlock_covers_S`, and `prescDatum = 0` at an `S`-block) together with `hy0`;
  `PreTwo`'s involution clause (6) at the archimedean primes (a real place's complex conjugation is
  an involution of `G_K`); and the odd-`count` normalisation (8) for condition (1).  The Chebotarev
  normalisation of the representative `z̃_m` (SW's "there exists a prime ideal Q ∉ T(K) with
  Q = A·(x)") is part of the construction of the representative, not of the invariant.
* `m < l`: the product-formula chain of SW p. 17 (`(z_s,σz_t)_{σP_t} = (z_s,σz_t)_{P_t} =
  (σz_s,z_t)_{P_t} = (σz_s,z_t)_{σP_s} = …`), reducing to the two cases above.  The tools are
  `Work.SSGRoute.H9.swTwoPlacePairingTwo`, `Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside`
  (the product formula, general `p`), the local dictionaries `H9.CV2.oPairAt_eq_value_of_odd_count`
  and `H9.oPairAt_swapTwo`, `Work.SSGRoute.NodeS37.crossedValue`, and the `p = 2` archimedean
  triviality (`ZDataTwo/mem_normImage_of_localUnits_real.lean`, `N2v2`), exactly as the odd-`p`
  chain `H9.swChainValueH9` does at p. 15. -/

open Work.SSGRoute.ZDataMup.LTRecFamHonest (hLevel hLevel_finiteDimensional hLevel_isGalois
  hLevel_numberField)

/-- **The `m < l` case, chain step** (Schmidt--Wingberg p. 17, the `s < t` case).  The value of
`χ_{b_m}` at the pinned Frobenius of the `σ`-sibling of the escape prime `Q_l` equals the value of
`χ_{b_l}` at the pinned Frobenius of the `σ⁻¹`-sibling of `Q_m` (`TwoRec.pinValue_cross_two`, the two
place chain), and the second value vanishes by the `m > l` case: for `l > m` the class `χ_{b_l}` is
prescribed to be `0` on the local group of the sibling of the *earlier* prime `Q_m`.

The inputs are the strong confinement of the recursion's classes (the `claimOfPreTwoConfined`
obligation: each `χ_{b_m}` kills the inertia of every finite place that is not `K`-conjugate to
`Q_m`) and the vanishing at the sibling of `Q_m` (supplied by `claimOfPreTwo_gt`). -/
theorem pinnedValueAtSibling_eq_zero_lt {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (hconf : ∀ j : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f j).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 σ = 0)
    {m l : ℕ} (hml : m < l) (t : K ≃ₐ[k] K) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hgt : ∀ v ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1)
      ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 v = 0) :
    Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f l).1, (s.f m).2)) (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs l) 0 t = 0 := by
  classical
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (l + 1)
  have hm_lt : m < l + 1 := by omega
  -- the two primes are `k`-conjugate to no sibling of each other
  have hsep : ∀ ρ : K ≃ₐ[k] K, ρ ≠ 1 →
      ¬ Work.SSGRoute.gesKConj K ((s.f m).1) (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f l).1) := by
    intro ρ hρ hc
    have h1' : SSGRoute.IsConjPlace k ((s.f m).1) (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f l).1) :=
      hc.imp fun τ hτ => hτ.2
    have h2' : SSGRoute.IsConjPlace k (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f l).1) ((s.f l).1) :=
      ⟨(Work.SSGRoute.ZDataMup.galLift K ρ)⁻¹, by rw [inv_smul_smul]⟩
    exact hdisjC m l hml (by omega) (Work.SSGRoute.isConjPlace_trans h1' h2')
  -- the normalisations (condition (1) of the recursion)
  have hcount : ∀ j : ℕ, j < l + 1 → Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f j).1) (preTwo_finPlace (K := K) ζ hζ hζK S y s hs j))
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((s.f j).2 : ↥K))) := by
    intro j hj
    obtain ⟨𝔮, h𝔮, hodd⟩ := hnorm j hj
    have h𝔮eq : 𝔮 = Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f j).1) (preTwo_finPlace (K := K) ζ hζ hζK S y s hs j) := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← h𝔮, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (preTwo_finPlace (K := K) ζ hζ hζK S y s hs j)]
    rw [← h𝔮eq]
    exact hodd
  -- the two-place chain
  have hchain := Work.SSGRoute.ZDataTwo.TwoRec.pinValue_cross_two (K := K) ζ hζ hζK
    ((s.f m).1) ((s.f l).1) (preTwo_finPlace (K := K) ζ hζ hζK S y s hs m) (preTwo_finPlace (K := K) ζ hζ hζK S y s hs l) ((s.f m).2) ((s.f l).2) hsep (hconf m) (hconf l)
    (hcount m (by omega)) (hcount l (by omega)) (hinv m (by omega)) t
  rw [hchain]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht2)
  rw [htinv]
  -- the value of `χ_{b_l}` at the pinned Frobenius of the sibling of `Q_m`
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f l).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f l).2
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f l).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f l).2
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f l).2) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f l).2
  have hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k
      (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 u = 0 := by
    intro u hu huI
    refine hconf l _ ((SSGRoute.isFinPlace_smul_iff ((s.f m).1)
      (Work.SSGRoute.ZDataMup.galLift K t)).mpr (preTwo_finPlace (K := K) ζ hζ hζK S y s hs m)) ?_ u hu huI
    intro hc
    have h1' : SSGRoute.IsConjPlace k ((s.f l).1)
        (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) := hc.imp fun τ hτ => hτ.2
    have h2' : SSGRoute.IsConjPlace k (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1)
        ((s.f m).1) := ⟨(Work.SSGRoute.ZDataMup.galLift K t)⁻¹, by rw [inv_smul_smul]⟩
    exact hdisjC m l hml (by omega) (Work.SSGRoute.isConjPlace_symm
      (Work.SSGRoute.isConjPlace_trans h1' h2'))
  obtain ⟨⟨ψ, hψ⟩, hpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f l).2)) 0 (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1)
    ((SSGRoute.isFinPlace_smul_iff ((s.f m).1) (Work.SSGRoute.ZDataMup.galLift K t)).mpr
      (preTwo_finPlace (K := K) ζ hζ hζK S y s hs m)) hkill
  rw [← Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f l).2)) (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs m) 0 t ht1 ψ hψ hpin]
  exact hgt ψ hψ

/-! ## The `m < l` case: the two-place chain (Schmidt--Wingberg p. 17, the `s < t` case)

For `m < l` the value of `χ_{b_m}` at the `σ`-sibling of the escape prime `Q_l` is the value of
`χ_{b_l}` at the `σ⁻¹`-sibling of `Q_m` (`TwoRec.pinValue_cross_two`, the crossed two-place chain),
which vanishes by the `m > l` case (`claimOfPreTwo_gt`) — the prescription of the rule at the
*earlier* escape prime.  The passage from this pinned value to the vanishing on the whole local
group is `pinnedZeroImpLocalGroup`, and `claimOfPreTwoConfined` supplies the strong confinement of
`χ_{b_m}` outside the `K`-class of `Q_m` which both steps consume. -/

theorem claimOfPreTwo_lt {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m l : ℕ, m < l → ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m l hml σ hσK hσ2 u hu
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (l + 1)
  have hl : l < l + 1 := Nat.lt_succ_self l
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← ht]
      exact h1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  -- the strong confinement of the recursion's classes outside their own escape prime
  have hconf : ∀ j : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f j).1) B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 τ = 0 :=
    Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S y hy hyT s hs
  -- the sibling of `Q_l` at `res σ`, and the `K`-conjugacy `σ • Q_l ∼ sibling`
  have hAtt : Work.SSGRoute.gesKConj K (σ • (s.f l).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, ht, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • (s.f l).1)
        = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  have hAfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) :=
    (SSGRoute.isFinPlace_smul_iff (s.f l).1 (Work.SSGRoute.ZDataMup.galLift K t)).mpr (hfin l hl)
  -- the escape prime `Q_m` is not `K`-conjugate to the sibling
  have hQA : ¬ Work.SSGRoute.gesKConj K ((s.f m).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) := by
    intro hc
    have h1 : SSGRoute.IsConjPlace k ((s.f m).1) (s.f l).1 :=
      SSGRoute.isConjPlace_trans (hc.imp fun τ hτ => hτ.2)
        ⟨(Work.SSGRoute.ZDataMup.galLift K t)⁻¹,
          by rw [Work.SSGRoute.ZDataMup.siblingPlace, inv_smul_smul]⟩
    exact hdisjC m l hml hl h1
  have hkillA : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 τ = 0 :=
    fun τ hτK hτI => hconf m _ hAfin hQA τ hτK hτI
  -- the Kummer-pinned Frobenius at the sibling
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  obtain ⟨⟨ψ, hψ⟩, hpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f l).1, (s.f m).2)) 0 (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1)
    hAfin hkillA
  -- the value at the pinned Frobenius is the `pinValue`, which vanishes by the two-place chain
  have hpinv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f l).1, (s.f m).2))
          (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs l) 0 t :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f l).1, (s.f m).2))
      (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs l) 0 t ht1 ψ hψ hpin
  have hgt : ∀ v ∈ SSGRoute.decomp k
        (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 v = 0 := by
    intro v hv
    rw [Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar]
    exact Work.SSGRoute.NodeS37.claimOfPreTwo_gt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs l m hml
      (Work.SSGRoute.ZDataMup.galLift K t) (by
        intro hmem
        have h1 : SSGRoute.res k K (Work.SSGRoute.ZDataMup.galLift K t) = 1 := by
          have : Work.SSGRoute.ZDataMup.galLift K t ∈ (SSGRoute.res k K).ker := by
            rw [IntermediateField.restrictNormalHom_ker K]; exact hmem
          exact MonoidHom.mem_ker.mp this
        rw [Work.SSGRoute.ZDataMup.galLift_spec] at h1
        exact ht1 h1)
      (by rw [Work.SSGRoute.ZDataMup.galLift_spec]; exact hσ2) v hv
  have hpinVal : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f l).1, (s.f m).2))
      (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs l) 0 t = 0 :=
    Work.SSGRoute.NodeS37.pinnedValueAtSibling_eq_zero_lt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs
      hconf hml t ht1 hσ2 hgt
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ = 0 := by
    rw [hpinv, hpinVal]
  -- the whole local group at the sibling vanishes
  have hmain := pinnedZeroImpLocalGroup (K := K) ζ hζ hζK (s.f m).2
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) hAfin hkillA ψ hψ hpin h0
  -- transport the local group of `σ • Q_l` to the sibling
  obtain ⟨w, hwK, hwA⟩ := hAtt
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k (σ • (s.f l).1) := (Subgroup.mem_inf.mp hu).1
  have hu'K : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hu'D : w * u * w⁻¹ ∈ SSGRoute.decomp k
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1) := by
    show (w * u * w⁻¹) • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1)
      = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1
    rw [mul_smul, mul_smul, show w⁻¹ • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f l).1)
        = σ • (s.f l).1 from by rw [← hwA, inv_smul_smul],
      show u • (σ • (s.f l).1) = σ • (s.f l).1 from MulAction.mem_stabilizer_iff.mp huD, ← hwA]
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2 hwK u
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 := by
    rw [← hval]
    exact hmain _ (Subgroup.mem_inf.mpr ⟨hu'D, hu'K⟩)
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
    (s.f m).2 u]
  exact hfinal

/-! ## State of the proof of `claimOfPreTwo` (three index cases)

**`m > l`** — PROVED, `claimOfPreTwo_gt` above: the `σ`-sibling of `Q_l` is `K`-conjugate to a block
of `TBlock S s.f m` (`TwoRec.TBlock_covers_Q`), whose attachment is the pair `(l, res σ)` with
`eScalar = 0` (the `IsInv` branch of the rule, `TwoRec.eGam`); clause (5) of `PreTwo` plus
`TwoRec.prescDatum_eq_of_attachment` therefore give `χ_{b_m} = y + (-y + 0) = 0` on that local
group, and `ZDataMup.nodeKummerCocharZMod_conj` transports the vanishing to the sibling itself.

**`m < l`** — the *chain step* is PROVED, `pinnedValueAtSibling_eq_zero_lt` above: the two-place
chain `TwoRec.pinValue_cross_two` gives

  `pinValue (Q_l, b_m) (res σ) = pinValue (Q_m, b_l) (res σ)⁻¹`,

and the right-hand side is `0` because `l > m` (`claimOfPreTwo_gt`, i.e. the prescription of the
rule at the earlier prime).  The remaining mechanical part of this case is the standard reduction
"vanishing at a pinned Frobenius `⇒` vanishing on the whole local group" at the sibling of `Q_l`:
`NodeS37.value_eq_zero_iff_localGroup_zero` with
* the strong confinement of `χ_{b_m}` at the sibling (`claimOfPreTwoConfined` below),
* `H9.swIsUnramifiedIn_hLevel_of_kills_inertia` (the Kummer level of `b_m` is unramified there),
* `H9.swKummerCochar_kills_levelKernel` (the Kummer level's kernel; the root lies in `hLevel` by
  `NK.LocalAnabelian.mem_kummerField_of_pow_eq` + `kummerSqrtZMod_pow`),
* `ZDataMup.exists_isFrobAtPrime_split` for the `IsFrobAtPrime`-pinned element (`decomp k A ≤ G_K`
  for the sibling `A = siblingPlace K (res σ) Q_l`), and `NodeS37.value_eq_of_pinned` +
  `NodeS35.pinValue_eq` + `NodeS35.exists_pinned` to compare the two pinned values,
followed by the same `gesKConj K (σ • Q_l) (siblingPlace K (res σ) Q_l)` transport as in
`claimOfPreTwo_gt`.

**Strong confinement (a separate obligation).**  `PreTwo`'s clause (8) gives only confinement
outside `cs(TBlock S s.f m) ∪ cs(Q_m)`; the *strong* form
(`¬ gesKConj K Q_m B` alone, for every finite `B`) is what the two-place chain of `m < l` consumes.
It is delegated as `SSGRoute/NodeS37/claimOfPreTwoConfined/claimOfPreTwoConfined`; its proof is a
strong induction on `m`: at a block attached to `(l, ρ)` clause (5) gives
`χ_{b_m} = Σ attScalar · χ_{b_l}`, each term of which kills the inertia of the block by the
induction hypothesis (`attScalar` vanishes at `ρ = 1` by definition of `eScalar`, and for `ρ ≠ 1`
the sibling is not `K`-conjugate to `Q_l` by `ZDataMup.siblingPlace_not_gesKConj`), while blocks
over `S` are handled by `hyT` — exactly as in the odd-`p` twin `H9.swHistChi_confinement_proved`.

**`m = l`** — the paper's Claim (Schmidt--Wingberg p. 16), NOT yet formalised and the irreducible
core: `PreTwo`'s clauses prescribe the value of `χ_{b_m}` at every block of `T_m` and *prescribe
nothing* at the involutive sibling, so the vanishing there must come from the arithmetic of `b_m`
itself.  Outline of the missing argument:
* the local dictionary `H9.CV2.oPairAt_eq_value_of_odd_count` at `A = siblingPlace K (res σ) Q_m`
  (the odd count of `σ b_m` at `A` is `NodeS37.countSiblingOddNoTame`, from the normalisation
  clause), turning the pinned value into the local pairing
  `oPairAt (χ_{b_m}) (χ_{σ b_m})_A`;
* the global product formula for that pair
  (`ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside`, whose "outside" hypotheses are
  discharged at the 2-adic/ramified places by clause (5) + `hy0` and at the archimedean places by
  the involution clause (6), cf. `H9.swTwoPlacePairingTwo` for the `p = 2` shape);
* the p.16 computation itself: a good representative `z̃ = a + bδ` of the class of `b_m` in
  `K = K^σ(δ)` (Chebotarev normalisation of the representative — this does not change `χ`), the
  reduction of the pairing to `∏_{P ∈ Σ}(2bδ, a)_P` with `Σ` the primes of `2bδ` outside the
  primes over `2`, the archimedean primes and `Ram(K|k)`, and the inert/split dichotomy in `K|K^σ`
  (`Work.HilbertSymbolGeneral.exists_eq_add_mul_quadGen` and `exists_sq_sub_mul_sq_comm` are the
  first bricks of that development).
-/

/-- **The `m = l` case of the paper's claim, reduced to the vanishing of the pinned Frobenius value
at the `σ`-sibling of the escape prime itself.**

This is the interface of the diagonal case of `claimOfPreTwo` in the paper's own form: everything
except the arithmetic statement

  `V := pinValue (Q_m, b_m) 0 (res k K σ) = 0`   (Schmidt--Wingberg p. 16's `z_i(Frob_{σ P_i}) = 0`)

is proved here: the strong confinement of `χ_{b_m}` outside the `K`-class of `Q_m`
(`claimOfPreTwoConfined`, which supplies the inertia-killing making the Kummer level unramified at
the sibling), the Kummer-pinned Frobenius (`NodeS35.exists_pinned`), the identification of the
pinned value with `pinValue` (`NodeS35.pinValue_eq`), and the passage from the pinned value to the
vanishing on the whole local group (`pinnedZeroImpLocalGroup`) followed by the `gesKConj`-transport
from the sibling to `σ • Q_m`. -/
theorem claimOfPreTwo_eq_of_pinnedValueZero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (hV : ∀ m : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
        (fun _ => ((s.f m).1, (s.f m).2))
        (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs m) 0 (SSGRoute.res k K σ) = 0) :
    ∀ m : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f m).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m σ hσK hσ2 u hu
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← ht]
      exact h1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  have hsplitK : SSGRoute.IsSplitIn k K (s.f m).1 :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le hKΛ (hsplit m hm)
  have hconf : ∀ j : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f j).1) B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 τ = 0 :=
    Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S y hy hyT s hs
  -- the sibling of `Q_m` at `res σ`, and the `K`-conjugacy `σ • Q_m ∼ sibling`
  have hAtt : Work.SSGRoute.gesKConj K (σ • (s.f m).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, ht, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • (s.f m).1)
        = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  have hAfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) :=
    (SSGRoute.isFinPlace_smul_iff (s.f m).1 (Work.SSGRoute.ZDataMup.galLift K t)).mpr (hfin m hm)
  have hQA : ¬ Work.SSGRoute.gesKConj K ((s.f m).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K ht1 hsplitK
  have hkillA : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 τ = 0 :=
    fun τ hτK hτI => hconf m _ hAfin hQA τ hτK hτI
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  obtain ⟨⟨ψ, hψ⟩, hpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f m).2)) 0 (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
    hAfin hkillA
  have hpinv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs m) 0 t :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace (K := K) ζ hζ hζK S y s hs m) 0 t ht1 ψ hψ hpin
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ = 0 := by
    rw [hpinv]
    exact hV m σ hσK (by rwa [ht] at hσ2)
  have hmain := pinnedZeroImpLocalGroup (K := K) ζ hζ hζK (s.f m).2
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) hAfin hkillA ψ hψ hpin h0
  -- transport the local group of `σ • Q_m` to the sibling
  obtain ⟨w, hwK, hwA⟩ := hAtt
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k (σ • (s.f m).1) := (Subgroup.mem_inf.mp hu).1
  have hu'K : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hu'D : w * u * w⁻¹ ∈ SSGRoute.decomp k
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    show (w * u * w⁻¹) • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
      = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
    rw [mul_smul, mul_smul, show w⁻¹ • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
        = σ • (s.f m).1 from by rw [← hwA, inv_smul_smul],
      show u • (σ • (s.f m).1) = σ • (s.f m).1 from MulAction.mem_stabilizer_iff.mp huD, ← hwA]
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2 hwK u
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 := by
    rw [← hval]
    exact hmain _ (Subgroup.mem_inf.mpr ⟨hu'D, hu'K⟩)
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
    (s.f m).2 u]
  exact hfinal

theorem claimOfPreTwo {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
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
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m l : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m l σ hσK hσ2 u hu
  rcases lt_trichotomy m l with hlt | heq | hgt
  · -- `m < l`: the crossed two-place chain (Schmidt--Wingberg p. 17)
    exact claimOfPreTwo_lt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT s hs m l hlt σ hσK hσ2 u hu
  · -- `m = l`: the paper's Claim (Schmidt--Wingberg p. 16), via the pinned value at the sibling
    subst heq
    refine claimOfPreTwo_eq_of_pinnedValueZero (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT s hs
      (fun m τ hτK hτ2 => ?_) m σ hσK hσ2 u hu
    have hτ1 : SSGRoute.res k K τ ≠ 1 := by
      intro h1
      have hmem : τ ∈ (SSGRoute.res k K).ker := by rw [MonoidHom.mem_ker]; exact h1
      exact hτK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
    exact Work.SSGRoute.NodeS37.pinnedValueOfHistoryOfInertSquare (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf s hs
      (fun ρ hρ1 hρ2 a A hA 𝔭 h𝔭 h2 hfixA hunram hafix heven =>
        Work.SSGRoute.NodeS37.inertSquareOfRhoFixed (K := K) ζ hζ hζK ρ hρ1 hρ2 a A hA 𝔭 h𝔭
          h2 hfixA hunram hafix heven)
      m (SSGRoute.res k K τ) hτ1 hτ2
  · -- `l < m`: the prescription of the rule at the earlier escape prime
    exact claimOfPreTwo_gt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs m l hgt σ hσK hσ2 u hu

end Work.SSGRoute.NodeS37
