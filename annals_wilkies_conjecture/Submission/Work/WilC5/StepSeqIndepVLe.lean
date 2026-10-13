-- NOTE (WilC5 / S4OnePoint_general): this file is a *copy* of
-- `Submission/Work/WilC5/StepSeqIndep.lean` (proved by a colleague) in which the chain hypothesis
-- has the *correct* direction: vdDMM Lemma 4.4 has `v(log xₙ) ≤ v(xₙ₊₁)`, i.e.
-- `VLe (logFun (xs n)) (xs (n+1))` (the `xₙ₊₁` are closer to finite than `log xₙ`), and *not*
-- the reverse (the source's `v(xₙ) < v(log xₙ) < v(xₙ₊₁)`; see the note in
-- `Submission/Work/WilC5/S4ONEPOINT_GENERAL_NOTES.md`).  The proof of `StepSeqIndep` never uses
-- its `hchain` hypothesis, so the same proof establishes this statement.

/-
  WilC5 — **Claim 2 of van den Dries–Macintyre–Marker, Lemma 4.4**: the values `v(x₀), …, v(xₙ₋₁)`
  of the sequence of the extension step are `ℤ`-independent modulo the values of the base model
  `v(B^×)`.

  The statement is the `hind` hypothesis of `Submission/Work/WilC5/StepSeqDecomp.lean`: for
  `q : Fin n → ℤ`, if `c ∈ B \ {0}` makes `c · ∏ᵢ xᵢ ^ (qᵢ)` a unit (same value as `1`), then `q = 0`.

  ## The argument

  Write `aₙ = S.xs n`, `βₙ = S.beta n` and fix `q ≠ 0` with a witness `c`.  Let `m` be the *least*
  index with `q m ≠ 0` and put `q̄ = q m`, `β = βₘ`, `ε = ±1` so that `log aₘ = β + ε aₘ₊₁`
  (`S.hrel`), and `y = |c| · ∏ᵢ aᵢ ^ (qᵢ)`, unit-valued by hypothesis.  Two ingredients from the
  chain invariants of the sequence (`Work.WilC5.StepSeqChain`) are used:

  * `v(βₙ) ≥ v(log aₙ)`: otherwise the min rule (`Work.WilC5.SameArch_sub_of_VLe_of_not`) shows that
    the translate `βₙ - log aₙ = ±aₙ₊₁` has the value of `βₙ ∈ B`, contradicting the value-newness
    of `aₙ₊₁`;
  * hence `aₙ₊₁` is dominated by `aₙ` (triangle inequality), so the `aₙ` form a decreasing chain
    `VLe (aᵢ) (a_j)` for `i ≤ j`.

  Now take the logarithm of the product `y = |c| · ∏ᵢ aᵢ ^ (qᵢ)`
  (`Work.WilC5.SSLC.logFun_prod_zpow`, `Work.WilC5.logFun_mul`) and substitute `log aₘ = β + ε aₘ₊₁`:

      q̄ · ε · aₘ₊₁  =  (log y - ∑_{i>m} qᵢ log aᵢ)  +  (- log |c| - q̄ β)  =:  U + W.

  Every summand of `U` is *strictly* dominated by `aₘ₊₁`: `log y` is finite because `y` is a unit
  (`Work.WilC5.LogUnitFinite`) while `aₘ₊₁` is infinite, and `log aᵢ` (for `i > m`) is strictly
  dominated by `aₘ₊₁` because `v(log aᵢ) > v(aᵢ)` (log-domination) and `v(aᵢ) ≥ v(aₘ₊₁)` (the
  chain).  Also `W ∈ B`, by the field closure of `B` (`Work.WilC5.FOV.SubfieldClosureL`), its
  log-closure (`hBlog`) and the fact that the real constants lie in `B`.

  Since `T := q̄ ε aₘ₊₁` has the value of `aₘ₊₁`, the min rule gives the contradiction:

  * if `VLe W T`, then `v W = v T = v aₘ₊₁`, i.e. `SameArch W aₘ₊₁` with `W ∈ B`, contradicting
    value-newness;
  * if `¬ VLe W T`, then *all* summands of `T = U + W` are strictly dominated by `aₘ₊₁`, so the sum
    is strictly dominated (`Work.WilC5.VLe_add_strict`), contradicting `v T = v aₘ₊₁`.
-/
import Mathlib
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.FOV.SubfieldClosureL
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.SSLC.logFun_prod_zpow
import Submission.Work.WilC5.LogUnitFinite
import Submission.Work.WilC5.StepSeqChain

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem StepSeqIndepVLe
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hunb : Work.WilC5.StepSeq.Unbounded S)
    (hdom : Work.WilC5.StepSeq.LogDominated S)
    (hchain : ∀ n : ℕ,
      Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.xs (n + 1)))
    (n : ℕ) :
    ∀ q : Fin n → ℤ,
      (∃ c ∈ (B : Set K), c ≠ 0 ∧
        WilkiesDesign.CG.IsUnitVal (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) → q = 0 := by
  intro q hq_rel
  by_contra hq0
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  -- ## 0. The `LEc`-symbols against the field operations, and positivity of the sequence
  have hsubE : ∀ x y : K, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hTE hadd x y
  have hposE : ∀ x : K, 0 < x → Work.WilC5.leE Work.WilC5.zeroE x ∧
      ¬ Work.WilC5.leE x Work.WilC5.zeroE :=
    fun x hx => (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg x).mpr hx
  have hxs_pos : ∀ k : ℕ, 0 < S.xs k := fun k =>
    (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg (S.xs k)).mp (S.hpos k)
  have hxs_ne : ∀ k : ℕ, S.xs k ≠ 0 := fun k => ne_of_gt (hxs_pos k)
  -- `S.hrel` in field notation
  have hrelF : ∀ k : ℕ, Work.WilC5.logFun (S.xs k) =
      (S.beta k : K) + (if S.pos k then S.xs (k + 1) else -(S.xs (k + 1))) := by
    intro k
    have h := S.hrel k
    by_cases hp : S.pos k
    · rw [if_pos hp] at h ⊢
      rwa [hadd] at h
    · rw [if_neg hp] at h ⊢
      rw [hsubE] at h
      rwa [sub_eq_add_neg] at h
  -- the `Unbounded` hypothesis, before the instances are pinned
  have hinf : ∀ k N : ℕ, Work.WilC5.realConst K (N : ℝ) < S.xs k := by
    intro k N
    obtain ⟨h1, h2⟩ := hunb k N
    have h1' : Work.WilC5.realConst K (N : ℝ) ≤ S.xs k := (hleneg _ _).mp h1
    have h2' : ¬ (S.xs k ≤ Work.WilC5.realConst K (N : ℝ)) := fun h => h2 ((hleneg _ _).mpr h)
    exact lt_of_le_of_ne h1' (fun hh => h2' (le_of_eq hh.symm))
  -- the field closure of `B`
  obtain ⟨hB0, hB1, hBneg, hBinv, hBadd, hBmul⟩ :=
    Work.WilC5.FOV.SubfieldClosureL hrexp hadd hmul hone hleneg B hBdcl
  -- the two delegated facts, stated at the given instances (before the instances are pinned)
  obtain ⟨hbeta, hstep⟩ :=
    Work.WilC5.StepSeqChain hrexp hadd hmul hone hleneg B S hnew hdom
  have hUnitFinite : ∀ y : K, WilkiesDesign.CG.IsUnitVal y →
      IsFiniteVal (Work.WilC5.logFun y) :=
    fun y hy => Work.WilC5.LogUnitFinite hrexp hadd hmul hone hleneg hy
  -- ## 1. Pin the instances so that the ambient `LRc`-structure is the reduct
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4ExpF.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K := Work.WilC5.lrcRexpReduct K
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
  letI hLR : LRc.Structure K := LR.withConstantsStructure ℝ
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) =
      (inferInstance : LRc.Structure K) :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTR : @FirstOrder.Language.Theory.Model LRc K (inferInstance) WilkiesDesign.CG.TR :=
    hstruct ▸ (Work.WilC5.reduct_model_TR K hTE)
  haveI : @FirstOrder.Language.Theory.Model LRc K (inferInstance) WilkiesDesign.CG.TR := hTR
  -- the naturals against the real constants, and the unboundedness in `Nat.cast` form
  have hnat : ∀ N : ℕ, @Work.WilC5.realConst K (inferInstance) (N : ℝ) = (N : K) :=
    fun N => Work.WilC5.realConst_natCast N
  have hinf' : ∀ k N : ℕ, (N : K) < S.xs k := by
    intro k N
    have h : @Work.WilC5.realConst K (inferInstance) (N : ℝ) < S.xs k := hinf k N
    rwa [hnat N] at h
  -- the natural and integer constants lie in `B`
  have hnat_mem : ∀ n : ℕ, (n : K) ∈ (B : Set K) := by
    intro k
    induction k with
    | zero => simpa using hB0
    | succ k ih =>
        have hcast : ((k + 1 : ℕ) : K) = (k : K) + 1 := by push_cast; ring
        rw [hcast]
        exact hBadd _ ih _ hB1
  have hint_mem : ∀ k : ℤ, (k : K) ∈ (B : Set K) := by
    intro k
    have h1 : (k : K) = ((k.natAbs : ℕ) : K) ∨ (k : K) = -(((k.natAbs : ℕ)) : K) := by
      rcases Int.natAbs_eq k with h | h
      · left
        conv_lhs => rw [h]
        push_cast
        exact Work.WilC5.abs_intCast k
      · right
        conv_lhs => rw [h]
        push_cast
        rw [Work.WilC5.abs_intCast]
    rcases h1 with h | h
    · rw [h]
      exact hnat_mem _
    · rw [h]
      exact hBneg _ (hnat_mem _)
  -- ## 2. The decreasing chain of the sequence (from `Work.WilC5.StepSeqChain`)
  have hmono : ∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (S.xs i) (S.xs j) := by
    intro i j hij
    induction j with
    | zero =>
        have h0 : i = 0 := Nat.eq_zero_of_le_zero hij
        subst h0; exact Work.WilC5.VLe_refl _
    | succ j ih =>
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact Work.WilC5.VLe_trans (ih (Nat.lt_succ_iff.mp hlt)) (hstep j)
        · have h0 : i = j + 1 := le_antisymm hij hge
          subst h0; exact Work.WilC5.VLe_refl _
  -- ## 3. The least index `m` with `q m ≠ 0`
  have hex : ∃ k : ℕ, ∃ h : k < n, q ⟨k, h⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq0 (funext fun i => hcon i i.isLt)
  set m : ℕ := Nat.find hex with hm_def
  have hm_lt : m < n := (Nat.find_spec hex).1
  have hm_ne : q ⟨m, hm_lt⟩ ≠ 0 := (Nat.find_spec hex).2
  have hm_min : ∀ i (hi : i < m), q ⟨i, lt_trans hi hm_lt⟩ = 0 := by
    intro i hi
    by_contra hcon
    exact Nat.find_min hex (show i < Nat.find hex from hi) ⟨lt_trans hi hm_lt, hcon⟩
  set mi : Fin n := ⟨m, hm_lt⟩ with hmi
  set qm : ℤ := q mi with hqm
  have hqm_ne : qm ≠ 0 := by simpa [hqm] using hm_ne
  have hqm_zero_below : ∀ i : Fin n, (i : ℕ) < m → q i = 0 := by
    intro i hi
    exact hm_min (i : ℕ) hi
  -- ## 4. The two constants: `c` made positive, and the product
  obtain ⟨c, hcB, hc0, hunit⟩ := hq_rel
  set ca : K := if 0 < c then c else -c with hca
  have hca_abs : ca = |c| := by
    by_cases h : 0 < c
    · rw [hca, if_pos h, abs_of_pos h]
    · have hclt : c < 0 := lt_of_le_of_ne (le_of_not_gt h) hc0
      rw [hca, if_neg h, abs_of_neg hclt]
  have hca_pos : 0 < ca := by
    rw [hca_abs]; exact abs_pos.mpr hc0
  have hcaB : ca ∈ (B : Set K) := by
    by_cases h : 0 < c
    · rw [hca, if_pos h]; exact hcB
    · rw [hca, if_neg h]; exact hBneg c hcB
  set P : K := ∏ i : Fin n, S.xs (i : ℕ) ^ (q i) with hP
  have hP_pos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun i _ => zpow_pos (hxs_pos _) _)
  have hunit' : WilkiesDesign.CG.IsUnitVal (ca * P) := by
    have h1 : WilkiesDesign.CG.IsUnitVal |c * P| :=
      (Work.WilC5.isUnitVal_abs_iff (c * P)).mpr hunit
    have h2 : |c * P| = ca * P := by
      rw [abs_mul, hca_abs, abs_of_pos hP_pos]
    rwa [h2] at h1
  -- ## 5. The logarithm of the product and its splitting at `m`
  have hlog_prod : Work.WilC5.logFun P =
      ∑ i : Fin n, ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))) := by
    have h := Work.WilC5.SSLC.logFun_prod_zpow hTE hadd hmul hone hleneg
      (Finset.univ : Finset (Fin n)) (fun i => S.xs (i : ℕ)) q (fun i _ => hxs_pos _)
    simpa [hP] using h
  have hlog_y : Work.WilC5.logFun (ca * P) = Work.WilC5.logFun ca + Work.WilC5.logFun P := by
    have h := Work.WilC5.logFun_mul hTE (hposE ca hca_pos) (hposE P hP_pos)
    rwa [hmul, hadd] at h
  set M : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => m < (i : ℕ)) with hM
  have hMmem : ∀ i : Fin n, i ∈ M ↔ m < (i : ℕ) := fun i => by
    rw [hM, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  set A : K := ∑ i ∈ M, ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))) with hA
  have hsplit : (∑ i : Fin n, ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))))
      = (qm : K) * Work.WilC5.logFun (S.xs m) + A := by
    classical
    have h1 : (∑ i : Fin n, ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))))
        = (∑ i ∈ (Finset.univ.erase mi), ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))))
          + (q mi : K) * Work.WilC5.logFun (S.xs (mi : ℕ)) :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ mi)).symm
    have h2 : (∑ i ∈ M, ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))))
        = ∑ i ∈ (Finset.univ.erase mi), ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))) := by
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        rw [h] at hi
        exact absurd ((hMmem mi).mp hi) (lt_irrefl _)
      · intro i hi his
        rw [Finset.mem_erase] at hi
        have hle : ¬ (m < (i : ℕ)) := fun hcon => his ((hMmem i).mpr hcon)
        have hlt : (i : ℕ) < m := lt_of_le_of_ne (not_lt.mp hle) (fun h => hi.1 (Fin.ext h))
        rw [hqm_zero_below i hlt]
        simp
    have h3 : (q mi : K) * Work.WilC5.logFun (S.xs (mi : ℕ))
        = (qm : K) * Work.WilC5.logFun (S.xs m) := by
      rw [← hqm]
    rw [h1, ← h2, h3, hA]
    ring
  -- ## 6. The relation `T = U + W`
  set e : K := if S.pos m then S.xs (m + 1) else -(S.xs (m + 1)) with he
  have hrelm : Work.WilC5.logFun (S.xs m) = (S.beta mi : K) + e := by
    have h := hrelF m
    have hb : (S.beta m : K) = (S.beta mi : K) := by rw [hmi]
    rw [hb] at h
    rw [he]
    exact h
  have he_abs : |e| = S.xs (m + 1) := by
    by_cases hp : S.pos m
    · rw [he, if_pos hp, abs_of_pos (hxs_pos (m + 1))]
    · rw [he, if_neg hp, abs_neg, abs_of_pos (hxs_pos (m + 1))]
  set T : K := (qm : K) * e with hT
  have hT_abs : |T| = |(qm : K)| * S.xs (m + 1) := by
    rw [hT, abs_mul, he_abs]
  have hqm_ge_one : (1 : K) ≤ |(qm : K)| := by
    rw [Work.WilC5.abs_intCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hqm_ne (Int.natAbs_eq_zero.mp h))
  have hT_same : Work.WilC5.SameArch T (S.xs (m + 1)) := by
    rw [Work.WilC5.SameArch_iff_VLe]
    constructor
    · -- `VLe T a`
      refine ⟨0, ?_⟩
      rw [hT_abs]
      simp only [Nat.cast_zero, zero_add, one_mul]
      rw [abs_of_pos (hxs_pos (m + 1))]
      simpa using mul_le_mul_of_nonneg_right hqm_ge_one (le_of_lt (hxs_pos (m + 1)))
    · -- `VLe a T`
      obtain ⟨N, hN⟩ := Work.WilC5.VLe_intCast_mul qm e
      refine ⟨N, ?_⟩
      have he' : |S.xs (m + 1)| = |e| := by
        rw [abs_of_pos (hxs_pos (m + 1))]
        exact he_abs.symm
      rw [hT, he']
      exact hN
  -- the key relation
  have hT_eq : T = (qm : K) * (Work.WilC5.logFun (S.xs m) - (S.beta mi : K)) := by
    rw [hT, hrelm]
    ring
  have hkey : Work.WilC5.logFun (ca * P) - A
      = Work.WilC5.logFun ca + (qm : K) * Work.WilC5.logFun (S.xs m) := by
    rw [hlog_y, hlog_prod, hsplit]
    ring
  set W : K := -Work.WilC5.logFun ca - (qm : K) * (S.beta mi : K) with hW
  set U : K := Work.WilC5.logFun (ca * P) - A with hU
  have hTUW : T = U + W := by
    rw [hT_eq, hkey, hW]
    ring
  -- ## 7. `W ∈ B`
  have hlogcaB : Work.WilC5.logFun ca ∈ (B : Set K) := hBlog ca hcaB
  have hqm_mem : (qm : K) ∈ (B : Set K) := hint_mem qm
  have hW_mem : W ∈ (B : Set K) := by
    rw [hW, sub_eq_add_neg]
    exact hBadd _ (hBneg _ hlogcaB) _ (hBneg _ (hBmul _ hqm_mem _ (S.beta mi).2))
  -- ## 8. Domination facts at `a := S.xs (m+1)`
  have hfin_logy : IsFiniteVal (Work.WilC5.logFun (ca * P)) := hUnitFinite _ hunit'
  have ha_inf : ∀ N : ℕ, (N : K) < S.xs (m + 1) := fun N => hinf' (m + 1) N
  have hlogy_dom : Work.WilC5.VLe (S.xs (m + 1)) (Work.WilC5.logFun (ca * P)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (ca * P)) (S.xs (m + 1)) :=
    Work.WilC5.VLe_of_isFiniteVal_of_infinite ha_inf hfin_logy
  -- the terms `i > m` of the sum
  have hlogi : ∀ i ∈ M,
      Work.WilC5.VLe (S.xs (m + 1)) ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))) ∧
        ¬ Work.WilC5.VLe ((q i : K) * Work.WilC5.logFun (S.xs (i : ℕ))) (S.xs (m + 1)) := by
    intro i hi
    rw [hM, Finset.mem_filter] at hi
    have hmi_le : m + 1 ≤ (i : ℕ) := hi.2
    have h1 : Work.WilC5.VLe (S.xs (m + 1)) (Work.WilC5.logFun (S.xs (i : ℕ))) :=
      Work.WilC5.VLe_trans (hmono (m + 1) (i : ℕ) hmi_le) (hdom (i : ℕ)).1
    have h2 : ¬ Work.WilC5.VLe (Work.WilC5.logFun (S.xs (i : ℕ))) (S.xs (m + 1)) := by
      intro hcon
      exact (hdom (i : ℕ)).2 (Work.WilC5.VLe_trans hcon (hmono (m + 1) (i : ℕ) hmi_le))
    refine ⟨Work.WilC5.VLe_intCast_mul_left (q i) h1, ?_⟩
    intro hcon
    exact h2 (Work.WilC5.VLe_trans (Work.WilC5.VLe_intCast_mul (q i) _) hcon)
  have hA_dom : Work.WilC5.VLe (S.xs (m + 1)) A ∧
      ¬ Work.WilC5.VLe A (S.xs (m + 1)) := by
    rw [hA]
    exact Work.WilC5.VLe_sum_strict M (hxs_ne (m + 1)) _
      (fun i hi => (hlogi i hi).1) (fun i hi => (hlogi i hi).2)
  -- `U` is strictly dominated
  have hU_dom : Work.WilC5.VLe (S.xs (m + 1)) U ∧
      ¬ Work.WilC5.VLe U (S.xs (m + 1)) := by
    constructor
    · rw [hU, sub_eq_add_neg]
      exact Work.WilC5.VLe_add hlogy_dom.1 ((Work.WilC5.VLe_neg_right _ _).mpr hA_dom.1)
    · rw [hU, sub_eq_add_neg]
      exact Work.WilC5.VLe_add_strict hlogy_dom.1
        ((Work.WilC5.VLe_neg_right _ _).mpr hA_dom.1) hlogy_dom.2
        (fun hcon => hA_dom.2 ((Work.WilC5.VLe_neg_left A _).mp hcon))
  -- `T` has the value of `a`
  have hT_dom : Work.WilC5.VLe T (S.xs (m + 1)) ∧
      Work.WilC5.VLe (S.xs (m + 1)) T :=
    (Work.WilC5.SameArch_iff_VLe T (S.xs (m + 1))).mp hT_same
  -- `W` is dominated by `a`
  have hW_dom : Work.WilC5.VLe (S.xs (m + 1)) W := by
    have h1 : W = T + (-U) := by rw [hTUW]; ring
    rw [h1]
    exact Work.WilC5.VLe_add hT_dom.2 ((Work.WilC5.VLe_neg_right _ _).mpr hU_dom.1)
  -- ## 9. The two cases
  by_cases hWT : Work.WilC5.VLe W T
  · -- case 1: `W` has the value of `a`
    have hWa : Work.WilC5.VLe W (S.xs (m + 1)) := Work.WilC5.VLe_trans hWT hT_dom.1
    have hsame : Work.WilC5.SameArch W (S.xs (m + 1)) :=
      (Work.WilC5.SameArch_iff_VLe W (S.xs (m + 1))).mpr ⟨hWa, hW_dom⟩
    exact hnew (m + 1) ⟨W, hW_mem⟩ hsame
  · -- case 2: `W` is strictly smaller than `a`, hence so is every summand of `T = U + W`
    have hW_strict : ¬ Work.WilC5.VLe W (S.xs (m + 1)) := by
      intro hcon
      obtain ⟨M1, hM1⟩ := hcon
      obtain ⟨K1, hK1⟩ := hT_dom.2
      have hle : |T| ≤ (((K1 + 1) * (M1 + 1) : ℕ) : K) * |W| := by
        have hcast : (((K1 + 1) * (M1 + 1) : ℕ) : K)
            = ((K1 : K) + 1) * ((M1 : K) + 1) := by push_cast; ring
        rw [hcast]
        calc |T| ≤ ((K1 : K) + 1) * |S.xs (m + 1)| := hK1
          _ ≤ ((K1 : K) + 1) * (((M1 : K) + 1) * |W|) :=
              mul_le_mul_of_nonneg_left hM1 (by positivity)
          _ = (((K1 : K) + 1) * ((M1 : K) + 1)) * |W| := by ring
      have hgt : (((K1 + 1) * (M1 + 1) : ℕ) : K) * |W| < |T| := by
        have hmono : (((K1 + 1) * (M1 + 1) : ℕ) : K)
            ≤ ((((K1 + 1) * (M1 + 1) + 1 : ℕ)) : K) := by
          exact_mod_cast Nat.le_succ _
        have hlt := not_le.mp fun hh :
            |T| ≤ ((((K1 + 1) * (M1 + 1) + 1 : ℕ)) : K) * |W| =>
          hWT ⟨(K1 + 1) * (M1 + 1), by
            have hcast : (((K1 + 1) * (M1 + 1) : ℕ) : K) + 1
                = (((K1 + 1) * (M1 + 1) + 1 : ℕ) : K) := by push_cast; ring
            rw [hcast]
            exact hh⟩
        calc (((K1 + 1) * (M1 + 1) : ℕ) : K) * |W|
            ≤ ((((K1 + 1) * (M1 + 1) + 1 : ℕ)) : K) * |W| :=
              mul_le_mul_of_nonneg_right hmono (abs_nonneg W)
          _ < |T| := hlt
      exact absurd hle (not_le.mpr hgt)
    have hT_strict : ¬ Work.WilC5.VLe T (S.xs (m + 1)) := by
      rw [hTUW]
      exact Work.WilC5.VLe_add_strict hU_dom.1 hW_dom hU_dom.2 hW_strict
    exact hT_strict hT_dom.1

end Work.WilC5
