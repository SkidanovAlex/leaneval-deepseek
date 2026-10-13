-- NOTE (WilC5 / S4OnePoint_general): a *copy* of `Submission/Work/WilC5/StepSeqLogClosure.lean`
-- (proved by a colleague) in which the auxiliary definition `canonSyn` is renamed to
-- `canonSynSSLC` and the theorem to `StepSeqLogClosureCut`.  Reason: the original file defines
-- `Work.WilC5.canonSyn`, which clashes with the identically named definition of
-- `Submission/Work/WilC5/StepKeyOfValProp.lean`, and the latter is imported (transitively) by
-- `Submission/Work/WilC5/ExistsStepSeq.lean`; the two modules can therefore not be imported into
-- the same environment without this renaming.

/-
  WilC5 — `StepSeqLogClosure`: the **log-closure step** of the iteration of vdDMM §4
  (their Claim 5 for the sequence of Lemma 4.4).

  `B` is a `Dcl`-closed `LRc`-substructure of the `rexp`-reduct of a model `K ⊨ TE`, closed under
  the definable logarithm, `S` is the sequence `x₀, x₁, …` of vdDMM Lemma 4.4 (`log xₙ = βₙ ± x_{n+1}`
  with `βₙ ∈ B`) and `hdec` is the value decomposition of `Dcl (B ∪ {x₀,…,x_{n-1}})`:
  for `w ≠ 0` in that definable closure, some power `w ^ Q` is `z · ∏ xᵢ ^ Nᵢ · (1 + ε)` with
  `z ∈ B \ {0}`, `N : Fin n → ℤ` and `ε` infinitesimal.

  The claim is that the definable closure of `B ∪ {x₀,…,x_{n-1}}` is closed under the definable
  logarithm *into* the next level: `logFun w ∈ Dcl (B ∪ {x₀,…,x_n})`.

  ## Proof

  Take the logarithm of the decomposition.  Since `logFun` is additive on positive elements
  (`Work.WilC5.logFun_mul`) and `logFun (x ^ Q) = Q · logFun x` (`Work.WilC5.S4ExpF.logFun_zpow`),

      `Q · logFun w = logFun z + Σᵢ Nᵢ · logFun xᵢ + logFun (1 + ε)`,

  where `logFun z ∈ B` (`hBlog`, so in the definable closure), each `logFun xᵢ` is `βᵢ ± x_{i+1}`
  (`StepSeq.hrel`), with `βᵢ ∈ B` and `x_{i+1}` among the new generators, and `logFun (1 + ε)` is in
  the definable closure by `Work.WilC5.StepNoNewAux.logFun_one_add_mem_dcl` (`1 + ε` is in the
  definable closure — it is `w ^ Q · (z · ∏)⁻¹` — and `log` is, on the `rexp`-window, recovered by
  the `LRc`-definable condition `rexp u = 1 + ε`).  Each summand is therefore in
  `Dcl (B ∪ {x₀,…,x_n})`, and dividing by `Q` (an integer cast, hence in the definable closure)
  gives the claim.

  ## The instance bookkeeping

  The `Dcl`-API of `WilC2`/`WilC4`/`S4ExpF` is stated at the `LRc`-structure synthesized from the
  ordered-field instance bundle (`canonSynSSLC` below: ring from `Ring.CompatibleRing`, `rexp` from the
  `rexpL`-structure and the real constants), while the statement fixes the `rexp`-*reduct*
  `Work.WilC5.reductStruct K` of the ambient `LEc`-structure.  The two agree as soon as the given
  structure bundle is the *canonical* one derived from the reduct — which is obtained by shadowing
  (`letI`) the three instances involved (`Ring.CompatibleRing`, `rexpL`, `constantsOn ℝ`) by their
  reducts `lrcRingReduct`, `lrcRexpReduct`, `lrcConstReduct`; each of these agrees with the
  corresponding component of the reduct by definition, so the two structures are *definitionally*
  equal (`hstruct`), and the transports along `hstruct` are the identity at the level of the
  `Dcl`-API.
-/
import Mathlib
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.StepNoNewAux.logFun_one_add_mem_dcl
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC2.meetsDefinable_dcl

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- The canonical `LRc`-structure synthesized from the ordered-field data (ring, `rexp`, constants):
this is the structure at which the `Dcl`-API of `WilC2`/`WilC4`/`S4ExpF` is stated. -/
@[instance_reducible]
def canonSynSSLC (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] : LRc.Structure M :=
  LR.withConstantsStructure ℝ

/-! ## Auxiliary closure properties of `Dcl` -/

/-- `Dcl P` is closed under finite products. -/
theorem dcl_prod_finset_mem {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    {ι : Type*} (P : Set K) (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, f i ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P) :
    (∏ i ∈ s, f i) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Work.WilC5.S4ExpF.dcl_one_mem P
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Work.WilC5.S4ExpF.dcl_mul_mem P (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- `Dcl P` is closed under finite sums. -/
theorem dcl_sum_finset_mem {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    {ι : Type*} (P : Set K) (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, f i ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P) :
    (∑ i ∈ s, f i) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Work.WilC5.S4ExpF.dcl_zero_mem P
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Work.WilC5.S4ExpF.dcl_add_mem P (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **`logFun` of a finite product of integer powers**: `log (∏ fᵢ ^ Nᵢ) = Σ Nᵢ · log fᵢ`
for `0 < fᵢ`. -/
theorem logFun_finset_prod_zpow {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {ι : Type*} (s : Finset ι) (f : ι → K) (N : ι → ℤ)
    (hpos : ∀ i ∈ s, 0 < f i) :
    Work.WilC5.logFun (∏ i ∈ s, f i ^ (N i))
      = ∑ i ∈ s, (N i : K) * Work.WilC5.logFun (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact Work.WilC5.S4ExpF.logFun_one hTE hadd hone
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have ha_pos : 0 < f a := hpos a (Finset.mem_insert_self a s)
      have hs_pos : 0 < ∏ i ∈ s, f i ^ (N i) :=
        Finset.prod_pos fun i hi => zpow_pos (hpos i (Finset.mem_insert_of_mem hi)) (N i)
      rw [Work.WilC5.S4ExpF.logFun_mul_pos hTE hadd hmul hleneg (zpow_pos ha_pos (N a)) hs_pos]
      rw [Work.WilC5.S4ExpF.logFun_zpow hTE hadd hmul hone hleneg (f a) ha_pos (N a)]
      rw [ih fun i hi => hpos i (Finset.mem_insert_of_mem hi)]

/-! ## The log-closure step -/

theorem StepSeqLogClosureCut
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
    (hdec : ∀ (n : ℕ) {w : K},
      w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
        ((B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ))) → w ≠ 0 →
      ∃ Q : ℤ, 0 < Q ∧ ∃ N : Fin n → ℤ, ∃ z ∈ (B : Set K), z ≠ 0 ∧ ∃ ε : K,
        Work.WilC5.IsInfinitesimal ε ∧
          w ^ Q = z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε))
    (n : ℕ) {w : K}
    (hw : w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
        ((B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ)))) (hw0 : w ≠ 0) :
    Work.WilC5.logFun w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
        ((B : Set K) ∪ Set.range (fun i : Fin (n + 1) => S.xs (i : ℕ))) := by
  classical
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  -- ## The canonical structure: the reduct of the shadowed instances
  have hzero : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
  have hneg : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hTE hadd x
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hadd _ _
      funMap_mul := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hmul _ _
      funMap_neg := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hneg _
      funMap_zero := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hzero
      funMap_one := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI : WilkiesDesign.CG.rexpL.Structure K :=
    @Work.WilC5.lrcRexpReduct K (Work.WilC5.instStructureLRcOfLEc K)
  letI : (FirstOrder.Language.constantsOn ℝ).Structure K :=
    @Work.WilC5.lrcConstReduct K (Work.WilC5.instStructureLRcOfLEc K)
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = canonSynSSLC K := by
    ext m f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show Work.WilC5.rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  have hstructDcl : ∀ A : Set K, @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) A
      = @Work.WilC2.Dcl K (canonSynSSLC K) A :=
    fun A => congrArg (fun i => @Work.WilC2.Dcl K i A) hstruct
  -- ## The two parameter sets
  let Q : Set K := (B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ))
  let P : Set K := (B : Set K) ∪ Set.range (fun i : Fin (n + 1) => S.xs (i : ℕ))
  have hQP : Q ⊆ P := by
    intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩, rfl⟩
  have hwQ : w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) Q := hw
  have hwQ' : w ∈ @Work.WilC2.Dcl K (canonSynSSLC K) Q := hstructDcl Q ▸ hwQ
  -- ## The main argument, at the canonical structure
  have hmain : Work.WilC5.logFun w ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
    have hwP₀ : w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) P :=
      Work.WilC2.dcl_mono hQP hwQ
    have hwP : w ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := hstructDcl P ▸ hwP₀
    by_cases hpos : (0 : K) < w
    · obtain ⟨Qz, hQz, N, z, hzB, hz0, ε, hε, hdecEq⟩ := hdec n hw hw0
      have hxs_pos : ∀ i : Fin (n + 1), (0 : K) < S.xs (i : ℕ) :=
        fun i => (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg (S.xs (i : ℕ))).mp
          (S.hpos (i : ℕ))
      have hpos' : ∀ i : Fin n, (0 : K) < S.xs (i : ℕ) :=
        fun i => hxs_pos ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩
      have hprod_pos : 0 < ∏ i : Fin n, S.xs (i : ℕ) ^ (N i) :=
        Finset.prod_pos fun i _ => zpow_pos (hpos' i) (N i)
      have hprod_ne : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ≠ 0 := ne_of_gt hprod_pos
      have hwQpos : 0 < w ^ Qz := zpow_pos hpos Qz
      have hε_half : |ε| ≤ (2 : K)⁻¹ := by
        have h := hε 1
        rw [show (((1 : ℕ) : K) + 1) = 2 by norm_num] at h
        exact h
      have h1ε_pos : 0 < 1 + ε := by
        have hlow : -(2 : K)⁻¹ ≤ ε := (abs_le.mp hε_half).1
        linarith
      have hzpos : 0 < z := by
        have hprod : 0 < (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) * (1 + ε) := by
          rw [← hdecEq]; exact hwQpos
        have h1 : 0 < z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) :=
          (mul_pos_iff_of_pos_right h1ε_pos).mp hprod
        exact (mul_pos_iff_of_pos_right hprod_pos).mp h1
      -- ### membership of the pieces in `Dcl P`
      have hz_mem : z ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        Work.WilC2.subset_dcl_aux P (Or.inl hzB)
      have hxs_mem : ∀ i : Fin (n + 1), S.xs (i : ℕ) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        fun i => Work.WilC2.subset_dcl_aux P (Or.inr ⟨i, rfl⟩)
      have hprod_mem : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))
          ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        dcl_prod_finset_mem P Finset.univ (fun i : Fin n => S.xs (i : ℕ) ^ (N i))
          fun i _ => Work.WilC5.S4ExpF.dcl_zpow_mem P (hxs_mem ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩)
            (ne_of_gt (hpos' i)) (N i)
      have hden_mem : z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))
          ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        Work.WilC5.S4ExpF.dcl_mul_mem P hz_mem hprod_mem
      have hden_ne : z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ≠ 0 := mul_ne_zero hz0 hprod_ne
      have hwQ_mem : w ^ Qz ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        Work.WilC5.S4ExpF.dcl_zpow_mem P hwP (ne_of_gt hpos) Qz
      have h1ε_mem : 1 + ε ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
        have h : w ^ Qz * (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)))⁻¹
            ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
          Work.WilC5.S4ExpF.dcl_mul_mem P hwQ_mem
            (Work.WilC5.S4ExpF.dcl_inv_mem P hden_mem hden_ne)
        have heq : w ^ Qz * (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)))⁻¹ = 1 + ε := by
          rw [hdecEq, mul_comm (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))) (1 + ε)]
          exact mul_inv_cancel_right₀ hden_ne (1 + ε)
        rwa [heq] at h
      have hε_mem : ε ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
        have h := Work.WilC5.S4ExpF.dcl_add_mem P h1ε_mem
          (Work.WilC5.S4ExpF.dcl_neg_mem P (Work.WilC5.S4ExpF.dcl_one_mem P))
        rwa [show (1 + ε) + (-1) = ε by ring] at h
      have hδ1 : Work.WilC5.absLeOne
          (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε) := by
        have hmulE : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε
            = (2 : K) * ε := by
          rw [hadd, hone, hmul]; norm_num
        rw [hmulE, Work.WilC5.S4ExpF.absLeOne_iff_abs hTE hadd hone hleneg, abs_mul]
        have h2abs : |(2 : K)| = 2 := abs_of_pos (by norm_num : (0 : K) < 2)
        rw [h2abs]
        calc (2 : K) * |ε| ≤ (2 : K) * (2 : K)⁻¹ :=
              mul_le_mul_of_nonneg_left hε_half (by norm_num)
          _ = 1 := by field_simp
      have hlog1ε_mem : Work.WilC5.logFun (1 + ε) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
        have hrexp' : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
            WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x := fun x => rfl
        have hδmem : Work.WilC5.addE Work.WilC5.oneE ε ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
          rw [hadd, hone]; exact h1ε_mem
        have h := Work.WilC5.S4ExpF.logFun_one_add_mem_dcl hTE hrexp' hadd hone P hδmem hδ1
        rwa [hadd, hone] at h
      have hlogz_mem : Work.WilC5.logFun z ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        Work.WilC2.subset_dcl_aux P (Or.inl (hBlog z hzB))
      have hlogxs_mem : ∀ i : Fin n,
          Work.WilC5.logFun (S.xs (i : ℕ)) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P := by
        intro i
        by_cases hp : S.pos (i : ℕ)
        · rw [S.hrel (i : ℕ), if_pos hp, hadd]
          exact Work.WilC5.S4ExpF.dcl_add_mem P
            (Work.WilC2.subset_dcl_aux P (Or.inl (S.beta (i : ℕ)).2))
            (hxs_mem ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩)
        · rw [S.hrel (i : ℕ), if_neg hp, Work.WilC5.S4ExpF.subE_eq_sub hTE hadd, sub_eq_add_neg]
          exact Work.WilC5.S4ExpF.dcl_add_mem P
            (Work.WilC2.subset_dcl_aux P (Or.inl (S.beta (i : ℕ)).2))
            (Work.WilC5.S4ExpF.dcl_neg_mem P (hxs_mem ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩))
      have hsum_mem : (∑ i : Fin n, (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)))
          ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        dcl_sum_finset_mem P Finset.univ
          (fun i : Fin n => (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)))
          fun i _ => Work.WilC5.S4ExpF.dcl_mul_mem P
            (Work.WilC5.S4ExpF.dcl_intCast_mem P (N i)) (hlogxs_mem i)
      -- ### the logarithm of the decomposition
      have hprodlog : Work.WilC5.logFun (∏ i : Fin n, S.xs (i : ℕ) ^ (N i))
          = ∑ i : Fin n, (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)) :=
        logFun_finset_prod_zpow hTE hadd hmul hone hleneg Finset.univ
          (fun i : Fin n => S.xs (i : ℕ)) N (fun i _ => hpos' i)
      have hkey : (Qz : K) * Work.WilC5.logFun w
          = Work.WilC5.logFun z + (∑ i : Fin n, (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)))
            + Work.WilC5.logFun (1 + ε) := by
        rw [← Work.WilC5.S4ExpF.logFun_zpow hTE hadd hmul hone hleneg w hpos Qz, hdecEq]
        rw [Work.WilC5.S4ExpF.logFun_mul_pos hTE hadd hmul hleneg (mul_pos hzpos hprod_pos)
          h1ε_pos]
        rw [Work.WilC5.S4ExpF.logFun_mul_pos hTE hadd hmul hleneg hzpos hprod_pos, hprodlog]
      have hQ0 : (Qz : K) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hQz)
      have hfin : (Qz : K)⁻¹ * (Work.WilC5.logFun z
            + (∑ i : Fin n, (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)))
            + Work.WilC5.logFun (1 + ε)) ∈ @Work.WilC2.Dcl K (canonSynSSLC K) P :=
        Work.WilC5.S4ExpF.dcl_mul_mem P
          (Work.WilC5.S4ExpF.dcl_inv_mem P (Work.WilC5.S4ExpF.dcl_intCast_mem P Qz) hQ0)
          (Work.WilC5.S4ExpF.dcl_add_mem P
            (Work.WilC5.S4ExpF.dcl_add_mem P hlogz_mem hsum_mem) hlog1ε_mem)
      have heq : (Qz : K)⁻¹ * (Work.WilC5.logFun z
            + (∑ i : Fin n, (N i : K) * Work.WilC5.logFun (S.xs (i : ℕ)))
            + Work.WilC5.logFun (1 + ε)) = Work.WilC5.logFun w := by
        rw [← hkey, inv_mul_cancel_left₀ hQ0]
      rwa [heq] at hfin
    · rw [Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos hTE hadd hone hleneg w hpos]
      exact Work.WilC5.S4ExpF.dcl_zero_mem P
  -- ## Transport back to the reduct
  change Work.WilC5.logFun w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) P
  exact (hstructDcl P).symm ▸ hmain

end Work.WilC5
