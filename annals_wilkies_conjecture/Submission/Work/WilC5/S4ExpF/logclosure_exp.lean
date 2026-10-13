import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC5.dcl_ring_closure
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open Classical

namespace Work.WilC5.S4ExpF

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder FirstOrder.Language
open scoped FirstOrder

section Toolkit

variable {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]

theorem logFun_mul_pos (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {x y : K} (hx : 0 < x) (hy : 0 < y) :
    Work.WilC5.logFun (x * y) = Work.WilC5.logFun x + Work.WilC5.logFun y := by
  have hx' := (leE_zero_iff hTE hadd hleneg x).mpr hx
  have hy' := (leE_zero_iff hTE hadd hleneg y).mpr hy
  have h := Work.WilC5.logFun_mul hTE hx' hy'
  rwa [hmul x y, hadd] at h

theorem logFun_one (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hone : (Work.WilC5.oneE : K) = 1) :
    Work.WilC5.logFun (1 : K) = 0 := by
  have h := Work.WilC5.logFun_expE hTE (Work.WilC5.zeroE : K)
  rw [expE_zeroE_of_model hTE, hone, zeroE_eq_zero hTE hadd] at h
  exact h

end Toolkit

section ToolDcl

variable {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]

theorem dclClosure_facts (P : Set K) :
    (0 : K) ∈ Work.WilC2.Dcl P ∧ (1 : K) ∈ Work.WilC2.Dcl P ∧
      (∀ x ∈ Work.WilC2.Dcl P, -x ∈ Work.WilC2.Dcl P) ∧
      (∀ x ∈ Work.WilC2.Dcl P, x / 2 ∈ Work.WilC2.Dcl P) ∧
      (∀ x ∈ Work.WilC2.Dcl P, ∀ y ∈ Work.WilC2.Dcl P, x + y ∈ Work.WilC2.Dcl P) :=
  dclClosure_ring (A := Work.WilC2.Dcl P) (le_of_eq (Work.WilC2.dcl_idem P))

theorem dcl_zero_mem (P : Set K) : (0 : K) ∈ Work.WilC2.Dcl P :=
  (dclClosure_facts P).1

theorem dcl_one_mem (P : Set K) : (1 : K) ∈ Work.WilC2.Dcl P :=
  (dclClosure_facts P).2.1

theorem dcl_neg_mem (P : Set K) {x : K} (hx : x ∈ Work.WilC2.Dcl P) :
    -x ∈ Work.WilC2.Dcl P :=
  (dclClosure_facts P).2.2.1 x hx

theorem dcl_add_mem (P : Set K) {x y : K} (hx : x ∈ Work.WilC2.Dcl P)
    (hy : y ∈ Work.WilC2.Dcl P) : x + y ∈ Work.WilC2.Dcl P :=
  (dclClosure_facts P).2.2.2.2 x hx y hy

theorem dcl_mul_mem (P : Set K) {x y : K} (hx : x ∈ Work.WilC2.Dcl P)
    (hy : y ∈ Work.WilC2.Dcl P) : x * y ∈ Work.WilC2.Dcl P := by
  have hx' : x ∈ Work.WilC4.Dcl ∅ (Work.WilC2.Dcl P) := by
    rw [Work.WilC2.dcl_eq_WilC4, Work.WilC2.dcl_idem]; exact hx
  have hy' : y ∈ Work.WilC4.Dcl ∅ (Work.WilC2.Dcl P) := by
    rw [Work.WilC2.dcl_eq_WilC4, Work.WilC2.dcl_idem]; exact hy
  have h := Work.WilC4.dcl_mul hx' hy'
  rwa [Work.WilC2.dcl_eq_WilC4, Work.WilC2.dcl_idem] at h

theorem dcl_inv_mem (P : Set K) {x : K} (hx : x ∈ Work.WilC2.Dcl P) (hx0 : x ≠ 0) :
    x⁻¹ ∈ Work.WilC2.Dcl P := by
  have hx' : x ∈ Work.WilC4.Dcl ∅ (Work.WilC2.Dcl P) := by
    rw [Work.WilC2.dcl_eq_WilC4, Work.WilC2.dcl_idem]; exact hx
  have h := Work.WilC4.dcl_inv hx' hx0
  rwa [Work.WilC2.dcl_eq_WilC4, Work.WilC2.dcl_idem] at h

theorem dcl_natCast_mem (P : Set K) (n : ℕ) : (n : K) ∈ Work.WilC2.Dcl P := by
  induction n with
  | zero => simpa using dcl_zero_mem P
  | succ n ih =>
      rw [Nat.cast_succ]
      exact dcl_add_mem P ih (dcl_one_mem P)

theorem dcl_intCast_mem (P : Set K) (n : ℤ) : (n : K) ∈ Work.WilC2.Dcl P := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using dcl_natCast_mem P k
  · rw [Int.cast_neg, Int.cast_natCast]
    exact dcl_neg_mem P (dcl_natCast_mem P k)

theorem dcl_pow_nat_mem (P : Set K) {x : K} (hx : x ∈ Work.WilC2.Dcl P) (n : ℕ) :
    x ^ n ∈ Work.WilC2.Dcl P := by
  induction n with
  | zero => simpa using dcl_one_mem P
  | succ n ih =>
      rw [pow_succ]
      exact dcl_mul_mem P ih hx

theorem dcl_zpow_mem (P : Set K) {x : K} (hx : x ∈ Work.WilC2.Dcl P) (hx0 : x ≠ 0) (n : ℤ) :
    x ^ n ∈ Work.WilC2.Dcl P := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    exact dcl_pow_nat_mem P hx k
  · rw [zpow_neg, zpow_natCast]
    exact dcl_inv_mem P (dcl_pow_nat_mem P hx k) (pow_ne_zero k hx0)

end ToolDcl

section Definability

variable {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]

theorem logFun_one_add_mem_dcl
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (P : Set K) {δ : K}
    (hδmem : Work.WilC5.addE Work.WilC5.oneE δ ∈
      @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P)
    (hδ : Work.WilC5.absLeOne (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) δ)) :
    Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ) ∈
      @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P := by
  let sym : WilkiesDesign.CG.LRc.Functions 1 := Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)
  let t : WilkiesDesign.CG.LRc.Term (Fin 1) :=
    Term.func (L := WilkiesDesign.CG.LRc) (l := 1) sym (fun _ : Fin 1 => Term.var (0 : Fin 1))
  have hreal : ∀ v : Fin 1 → K, Term.realize v t = Work.WilC5.rexpFromExp (v 0) := by
    intro v
    have h1 : Term.realize v t
        = @Structure.funMap WilkiesDesign.CG.LRc K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
            1 sym (fun _ => v 0) := rfl
    rw [h1]
    rw [show @Structure.funMap WilkiesDesign.CG.LRc K
          (WilkiesDesign.CG.LR.withConstantsStructure ℝ) 1 sym (fun _ => v 0)
        = @Structure.funMap WilkiesDesign.CG.LR K _ 1
            (Sum.inr WilkiesDesign.CG.rexpFunc.rexp) (fun _ => v 0) from rfl]
    rw [show @Structure.funMap WilkiesDesign.CG.LR K _ 1
          (Sum.inr WilkiesDesign.CG.rexpFunc.rexp) (fun _ => v 0)
        = @Structure.funMap WilkiesDesign.CG.rexpL K _ 1
            WilkiesDesign.CG.rexpFunc.rexp (fun _ => v 0) from rfl]
    have hfun : (fun _ : Fin 1 => v 0) = ![v 0] := by funext i; fin_cases i; rfl
    rw [hfun]
    exact hrexp (v 0)
  have hterm' : (@Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P).DefinableFun
      WilkiesDesign.CG.LRc t.realize :=
    (Term.definableFun_realize t).mono (Set.empty_subset _)
  have h0 : (@Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P).Definable
      WilkiesDesign.CG.LRc {v : Fin 1 → K | t.realize v = Work.WilC5.addE Work.WilC5.oneE δ} :=
    hterm'.ofPred_eq_const hδmem
  have hseteq : {v : Fin 1 → K | Work.WilC5.rexpFromExp (v 0) = Work.WilC5.addE Work.WilC5.oneE δ}
      = {v : Fin 1 → K | t.realize v = Work.WilC5.addE Work.WilC5.oneE δ} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    rw [hreal v]
  have h1 : (@Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P).Definable
      WilkiesDesign.CG.LRc
        {v : Fin 1 → K | Work.WilC5.rexpFromExp (v 0) = Work.WilC5.addE Work.WilC5.oneE δ} := by
    rw [hseteq]; exact h0
  have hsing : {v : Fin 1 → K | Work.WilC5.rexpFromExp (v 0) = Work.WilC5.addE Work.WilC5.oneE δ}
      = {fun _ : Fin 1 => Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hv
      funext i
      rw [Subsingleton.elim i 0]
      exact Work.WilC5.logFun_eq_of_rexp_eq hTE hδ hv
    · intro hv
      rw [hv]
      exact Work.WilC5.logFun_one_add_rexp hTE hδ
  have hmem : Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ) ∈
      @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
        (@Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P) := by
    rw [@Work.WilC2.mem_dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) _
      (Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ))]
    show (@Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) P).Definable
      WilkiesDesign.CG.LRc
        {v : Fin 1 → K | v 0 ∈ ({Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ)} : Set K)}
    rw [show {v : Fin 1 → K | v 0 ∈
          ({Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ)} : Set K)}
        = {fun _ : Fin 1 => Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ)} from
          (Work.WilC2.setOf_mem_singleton_eq_const _)]
    rw [← hsing]
    exact h1
  rw [Work.WilC2.dcl_idem P] at hmem
  exact hmem

end Definability

theorem logclosure_exp {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (A : Set K)
    (hAdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) A ⊆ A)
    (hAlog : ∀ x ∈ A, Work.WilC5.logFun x ∈ A)
    (a : K) (ha : a ∈ A) (hx : Work.WilC5.expE a ∉ A)
    (hVA : ∀ w ∈ @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
        (A ∪ {Work.WilC5.expE a}), w ≠ 0 →
        ∃ Q : ℤ, 0 < Q ∧ ∃ N : ℤ, ∃ z ∈ A, z ≠ 0 ∧ ∃ ε : K, Work.WilC5.IsInfinitesimal ε ∧
          w ^ Q = z * (Work.WilC5.expE a) ^ N * (1 + ε)) :
    ∀ w ∈ @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
        (A ∪ {Work.WilC5.expE a}),
      Work.WilC5.logFun w ∈ @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
        (A ∪ {Work.WilC5.expE a}) := by
  intro w hw
  set P : Set K := A ∪ {Work.WilC5.expE a} with hP
  have hA_sub : ∀ x ∈ A, x ∈ Work.WilC2.Dcl P := fun x hx => Work.WilC2.subset_dcl_aux P (Or.inl hx)
  have hexp_sub : Work.WilC5.expE a ∈ Work.WilC2.Dcl P :=
    Work.WilC2.subset_dcl_aux P (Or.inr rfl)
  by_cases hw0 : w = 0
  · subst hw0
    rw [logFun_eq_zero_of_not_pos hTE hadd hone hleneg (0 : K) (not_lt.mpr le_rfl)]
    exact dcl_zero_mem P
  · by_cases hpos : 0 < w
    · obtain ⟨Q, hQ, N, z, hzA, hz0, ε, hε, hdec⟩ := hVA w hw hw0
      have hexp_pos : 0 < Work.WilC5.expE a :=
        (leE_zero_iff hTE hadd hleneg (Work.WilC5.expE a)).mp
          (Work.WilC5.expE_pos_of_model hTE a)
      have hwQpos : 0 < w ^ Q := zpow_pos hpos Q
      have hexNpos : 0 < (Work.WilC5.expE a) ^ N := zpow_pos hexp_pos N
      have hε_half : |ε| ≤ (2 : K)⁻¹ := by
        have h := hε 1
        rw [show (((1 : ℕ) : K) + 1) = 2 by norm_num] at h
        exact h
      have h2inv : (2 : K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by norm_num : (1 : K) < 2)
      have h1ε_pos : 0 < 1 + ε := by
        have hlow : -(2 : K)⁻¹ ≤ ε := (abs_le.mp hε_half).1
        linarith
      have hzpos : 0 < z := by
        have hprod : 0 < (z * (Work.WilC5.expE a) ^ N) * (1 + ε) := by
          rw [← hdec]; exact hwQpos
        have h1 : 0 < z * (Work.WilC5.expE a) ^ N :=
          (mul_pos_iff_of_pos_right h1ε_pos).mp hprod
        exact (mul_pos_iff_of_pos_right hexNpos).mp h1
      -- membership in the definable closure
      have hw_mem : w ∈ Work.WilC2.Dcl P := hw
      have hz_mem : z ∈ Work.WilC2.Dcl P := hA_sub z hzA
      have hwQ_mem : w ^ Q ∈ Work.WilC2.Dcl P := dcl_zpow_mem P hw_mem (ne_of_gt hpos) Q
      have hexN_mem : (Work.WilC5.expE a) ^ N ∈ Work.WilC2.Dcl P :=
        dcl_zpow_mem P hexp_sub (ne_of_gt hexp_pos) N
      have hden_mem : z * (Work.WilC5.expE a) ^ N ∈ Work.WilC2.Dcl P :=
        dcl_mul_mem P hz_mem hexN_mem
      have hden0 : z * (Work.WilC5.expE a) ^ N ≠ 0 :=
        mul_ne_zero hz0 (zpow_ne_zero N (ne_of_gt hexp_pos))
      have h1ε_mem : 1 + ε ∈ Work.WilC2.Dcl P := by
        have h : w ^ Q * (z * (Work.WilC5.expE a) ^ N)⁻¹ ∈ Work.WilC2.Dcl P :=
          dcl_mul_mem P hwQ_mem (dcl_inv_mem P hden_mem hden0)
        have heq : w ^ Q * (z * (Work.WilC5.expE a) ^ N)⁻¹ = 1 + ε := by
          rw [hdec, mul_comm (z * (Work.WilC5.expE a) ^ N) (1 + ε)]
          exact mul_inv_cancel_right₀ hden0 (1 + ε)
        rwa [heq] at h
      -- the logarithm of `1 + ε`
      have hδ1 : Work.WilC5.absLeOne
          (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε) := by
        have hmulE : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε
            = (2 : K) * ε := by
          rw [hadd, hone, hmul]; norm_num
        rw [hmulE, absLeOne_iff_abs hTE hadd hone hleneg, abs_mul]
        have h2abs : |(2 : K)| = 2 := abs_of_pos (by norm_num : (0 : K) < 2)
        rw [h2abs]
        calc (2 : K) * |ε| ≤ (2 : K) * (2 : K)⁻¹ :=
              mul_le_mul_of_nonneg_left hε_half (by norm_num)
          _ = 1 := by field_simp
      have hε_mem : ε ∈ Work.WilC2.Dcl P := by
        have h := dcl_add_mem P h1ε_mem (dcl_neg_mem P (dcl_one_mem P))
        rwa [show (1 + ε) + (-1) = ε from by ring] at h
      have hδmem : Work.WilC5.addE Work.WilC5.oneE ε ∈ Work.WilC2.Dcl P := by
        rw [hadd, hone]
        exact dcl_add_mem P (dcl_one_mem P) hε_mem
      have hlog1ε_tmp : Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE ε)
          ∈ Work.WilC2.Dcl P :=
        logFun_one_add_mem_dcl hTE hrexp hadd hone P hδmem hδ1
      have hlog1ε : Work.WilC5.logFun (1 + ε) ∈ Work.WilC2.Dcl P := by
        rwa [hadd, hone] at hlog1ε_tmp
      have hlogz : Work.WilC5.logFun z ∈ Work.WilC2.Dcl P := hA_sub _ (hAlog z hzA)
      have hNa : (N : K) * a ∈ Work.WilC2.Dcl P :=
        dcl_mul_mem P (dcl_intCast_mem P N) (hA_sub a ha)
      have hc_mem : Work.WilC5.logFun z + (N : K) * a + Work.WilC5.logFun (1 + ε)
          ∈ Work.WilC2.Dcl P :=
        dcl_add_mem P (dcl_add_mem P hlogz hNa) hlog1ε
      -- the key computation
      have hkey : (Q : K) * Work.WilC5.logFun w
          = Work.WilC5.logFun z + (N : K) * a + Work.WilC5.logFun (1 + ε) := by
        have h1 : Work.WilC5.logFun (w ^ Q) = (Q : K) * Work.WilC5.logFun w :=
          logFun_zpow hTE hadd hmul hone hleneg w hpos Q
        have h2 : Work.WilC5.logFun ((Work.WilC5.expE a) ^ N)
            = (N : K) * Work.WilC5.logFun (Work.WilC5.expE a) :=
          logFun_zpow hTE hadd hmul hone hleneg (Work.WilC5.expE a) hexp_pos N
        rw [← h1, hdec]
        rw [logFun_mul_pos hTE hadd hmul hleneg (mul_pos hzpos hexNpos) h1ε_pos]
        rw [logFun_mul_pos hTE hadd hmul hleneg hzpos hexNpos]
        rw [h2, Work.WilC5.logFun_expE hTE a]
      have hQ0 : (Q : K) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hQ)
      have hfin : Work.WilC5.logFun w ∈ Work.WilC2.Dcl P := by
        have h : (Q : K)⁻¹ * (Work.WilC5.logFun z + (N : K) * a + Work.WilC5.logFun (1 + ε))
            ∈ Work.WilC2.Dcl P :=
          dcl_mul_mem P (dcl_inv_mem P (dcl_intCast_mem P Q) hQ0) hc_mem
        have heq : (Q : K)⁻¹ * (Work.WilC5.logFun z + (N : K) * a + Work.WilC5.logFun (1 + ε))
            = Work.WilC5.logFun w := by
          rw [← hkey, inv_mul_cancel_left₀ hQ0]
        rwa [heq] at h
      exact hfin
    · rw [logFun_eq_zero_of_not_pos hTE hadd hone hleneg w hpos]
      exact dcl_zero_mem P

end Work.WilC5.S4ExpF
