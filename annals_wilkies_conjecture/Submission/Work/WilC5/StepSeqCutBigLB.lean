/-
  WilC5 — the two min-rule computations of vdDMM Lemma 4.4, Claim 4, for a positive `w ∈ Fₙ`.

  `sscb_cut_pos` is Claim 4 apart from the trivial case `w ≤ 0`: given the power decomposition
  `w^Q = z · ∏ xᵢ^{Nᵢ} · (1+ε)` of `StepSeqDecomp`, it produces the cut realisation of `xₙ` over
  `Fₙ` by `yₙ`.  If some `Nᵢ ≠ 0`, the least such index `m` is decided by two min-rule
  computations (`Work.WilC5.CutComp`), one on `K` and one on `L`, glued by order-preservation of
  `σ`; if all `Nᵢ = 0` then `w` lies in the archimedean class of an element of `B`, and the claim
  is `hcutB` transported by `sscb_same_arch_cut`.
-/
import Mathlib
import Submission.Work.WilC5.StepSeqCutBigAux
import Submission.Work.WilC5.StepSeqCutBigEmb
import Submission.Work.WilC5.DclRoot
import Submission.Work.WilC5.StepSeqYVLe
import Submission.Work.WilC5.ClassArith
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqIndep
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.StepSeqEstimates
import Submission.Work.WilC5.CutComp
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.FOV.SubfieldClosureL
import Submission.Work.WilC5.S4ExpF.logFun_pow_nat
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.LogUnitFinite
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem sscb_cut_pos_B
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B,
      τ ⟨Work.WilC5.logFun (b : K), hBlog (b : K) b.2⟩ = Work.WilC5.logFun (τ b))
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hxbig : ∀ (i N : ℕ), (N : K) < S.xs i)
    (hlogsm : ∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (S.xs i) (Work.WilC5.logFun (S.xs j)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (S.xs j)) (S.xs i))
    (hbetasm : ∀ i : ℕ, Work.WilC5.VLe (S.xs i) (S.beta i : K) ∧
      ¬ Work.WilC5.VLe (S.beta i : K) (S.xs i))
    {y0 : L}
    (hcutB : ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L))))
    {n : ℕ}
    (σ : WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S n) L)
    (hσB : ∀ b : ↥B, σ ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b)
    (hσxs : ∀ (i : ℕ) (hi : i < n),
      σ ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ = Work.WilC5.StepSeq.ys B τ S y0 i)
    {w : ↥(Work.WilC5.StepSeq.Fsub hK S n)} (hwpos : 0 < (w : K))
    {Q : ℤ} (hQpos : 0 < Q) {N : Fin n → ℤ}
    {z : K} (hzB : z ∈ (B : Set K)) (hz0 : z ≠ 0)
    {ε : K} (hεinf : Work.WilC5.IsInfinitesimal ε)
    (hdec : (w : K) ^ Q = z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) (hNex : ¬ (∃ k : ℕ, ∃ hk : k < n, N ⟨k, hk⟩ ≠ 0)) :
    (((w : K) < S.xs n ↔ (σ w : L) < Work.WilC5.StepSeq.ys B τ S y0 n) ∧
     (S.xs n < (w : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 n < (σ w : L))) := by
  classical
  haveI : K ⊨ WilkiesDesign.CG.TE := hK
  haveI : L ⊨ WilkiesDesign.CG.TE := hL
  -- ## 0. `B` and `Fₙ` are subfields
  obtain ⟨hB0, hB1, hBneg, hBinv, hBadd, hBmul⟩ :=
    Work.WilC5.FOV.SubfieldClosureL hrexpK haddK hmulK honeK hlenegK B hBdcl
  have hnat_mem : ∀ m : ℕ, (m : K) ∈ (B : Set K) := sscb_natCast_mem hB0 hB1 hBadd
  have hint_mem : ∀ k : ℤ, (k : K) ∈ (B : Set K) := sscb_intCast_mem hB0 hB1 hBneg hBadd
  obtain ⟨hF0, hF1, hFneg, hFinv, hFadd, hFmul⟩ :=
    Work.WilC5.FOV.SubfieldClosureL hrexpK haddK hmulK honeK hlenegK
      (Work.WilC5.StepSeq.Fsub hK S n) (Work.WilC5.StepSeq.Fsub_dcl hK S n)
  have hnatF : ∀ m : ℕ, (m : K) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    sscb_natCast_mem hF0 hF1 hFadd
  have hBadd' : ∀ a b : K, a ∈ (B : Set K) → b ∈ (B : Set K) → a + b ∈ (B : Set K) :=
    fun a b ha hb => hBadd a ha b hb
  have hBmul' : ∀ a b : K, a ∈ (B : Set K) → b ∈ (B : Set K) → a * b ∈ (B : Set K) :=
    fun a b ha hb => hBmul a ha b hb
  have hFadd' : ∀ a b : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      a + b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    fun a b ha hb => hFadd a ha b hb
  -- ## 1. bridges between the `LEc`-symbols and the field operations
  have hzeroK : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hK haddK
  have hzeroL : (Work.WilC5.zeroE : L) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hL haddL
  have hnegEK : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hK haddK x
  have hnegEL : ∀ x : L, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hL haddL x
  have hsubEK : ∀ x y : K, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hK haddK x y
  have hsubEL : ∀ x y : L, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hL haddL x y
  have hleEL_L : ∀ x y : L, Work.WilC5.leEL x y → x ≤ y := by
    intro x y hxy
    obtain ⟨c, hc⟩ := hxy
    have h1 : c * c = y - x := by rw [← hsubEL, ← hmulL]; exact hc
    have h2 : (0 : L) ≤ y - x := by rw [← h1]; exact mul_self_nonneg c
    linarith
  have hsubB : ∀ a b : K, a ∈ (B : Set K) → b ∈ (B : Set K) → a - b ∈ (B : Set K) := by
    intro a b ha hb; rw [sub_eq_add_neg]; exact hBadd _ ha _ (hBneg _ hb)
  have hsubF : ∀ a b : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      a - b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
    intro a b ha hb; rw [sub_eq_add_neg]; exact hFadd _ ha _ (hFneg _ hb)
  have hrootB : ∀ a : K, a ∈ (B : Set K) → 0 < a →
      ∃ c : K, c ∈ (B : Set K) ∧ c * c = a := by
    intro a ha hapos
    obtain ⟨b, hbB, -, hb2⟩ :=
      Work.WilC5.DclRoot (K := K) hK hrexpK haddK hmulK honeK hlenegK hBdcl ha hapos
        (Q := 2) (by norm_num)
    exact ⟨b, hbB, by rw [← hb2]; ring⟩
  have hrootF : ∀ a : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) → 0 < a →
      ∃ c : K, c ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) ∧ c * c = a := by
    intro a ha hapos
    obtain ⟨b, hbF, -, hb2⟩ :=
      Work.WilC5.DclRoot (K := K) hK hrexpK haddK hmulK honeK hlenegK
        (Work.WilC5.StepSeq.Fsub_dcl hK S n) ha hapos (Q := 2) (by norm_num)
    exact ⟨b, hbF, by rw [← hb2]; ring⟩
  have hτord : ∀ a b : ↥B, (((a : K) ≤ (b : K)) ↔ ((τ a : L) ≤ (τ b : L))) :=
    sscb_emb_order haddK hmulK hnegEK hleEL_L hsubB hrootB τ
  have hσord : ∀ a b : ↥(Work.WilC5.StepSeq.Fsub hK S n),
      (((a : K) ≤ (b : K)) ↔ ((σ a : L) ≤ (σ b : L))) :=
    sscb_emb_order haddK hmulK hnegEK hleEL_L hsubF hrootF σ
  have hτ0 : τ ⟨(0 : K), hB0⟩ = (0 : L) := sscb_emb_zero hzeroK hzeroL hB0 τ
  have hσ0 : σ ⟨(0 : K), hF0⟩ = (0 : L) := sscb_emb_zero hzeroK hzeroL hF0 σ
  have hxpos : ∀ i : ℕ, 0 < S.xs i := fun i => sscb_xs_pos hK haddK hlenegK S i
  have hypos : ∀ i : ℕ, 0 < Work.WilC5.StepSeq.ys B τ S y0 i := by
    intro i
    have h := (hcutB i ⟨(0 : K), hB0⟩).1
    rw [hτ0] at h
    exact h.mp (hxpos i)
  have hysbig : ∀ (i N : ℕ), (N : L) < Work.WilC5.StepSeq.ys B τ S y0 i := by
    intro i N
    have hτN : τ ⟨(N : K), hnat_mem N⟩ = (N : L) :=
      sscb_emb_natCast haddK haddL hzeroK hzeroL honeK honeL hB0 hB1 hBadd' τ hnat_mem N
    have h := (hcutB i ⟨(N : K), hnat_mem N⟩).1.mp (hxbig i N)
    rwa [hτN] at h
  have hlogltK : ∀ {x y : K}, 0 < x → 0 < y →
      (Work.WilC5.logFun x < Work.WilC5.logFun y ↔ x < y) := sscb_log_lt hK haddK hlenegK
  have hlogmulK : ∀ {x y : K}, 0 < x → 0 < y →
      Work.WilC5.logFun (x * y) = Work.WilC5.logFun x + Work.WilC5.logFun y :=
    fun {x y} hx hy => Work.WilC5.S4ExpF.logFun_mul_of_pos hK haddK hmulK hlenegK hx hy
  have hlogzpowK : ∀ {x : K}, 0 < x → ∀ k : ℤ,
      Work.WilC5.logFun (x ^ k) = (k : K) * Work.WilC5.logFun x :=
    fun {x} hx k => Work.WilC5.S4ExpF.logFun_zpow hK haddK hmulK honeK hlenegK x hx k
  -- ## 2. positivity of `σ`-images of positive elements
  have hσpos : ∀ a : ↥(Work.WilC5.StepSeq.Fsub hK S n), 0 < (a : K) → 0 < (σ a : L) :=
    sscb_emb_pos hF0 σ hσ0 hσord
  have hτpos : ∀ b : ↥B, 0 < (b : K) → 0 < (τ b : L) :=
    sscb_emb_pos hB0 τ hτ0 hτord
  -- ## 3. the elementary bounds on `ε` and on `z`
  have hεsmall : |ε| ≤ (2 : K)⁻¹ := by
    have h2 : ((1 : K) + 1) = (2 : K) := by norm_num
    have h := hεinf 1
    simp only [Nat.cast_one] at h
    rwa [h2] at h
  have h1εpos : 0 < 1 + ε := by
    have ht : (1 : K) ≤ |1 + ε| + |ε| := by
      have h := abs_add_le (1 + ε) (-ε)
      have h2 : (1 + ε) + (-ε) = (1 : K) := by ring
      rw [h2, abs_one, abs_neg] at h
      exact h
    have h2 : (2 : K)⁻¹ = 1 / 2 := by norm_num
    rw [h2] at hεsmall
    linarith [neg_le_abs ε]
  have hPpos : 0 < ∏ i : Fin n, S.xs (i : ℕ) ^ (N i) :=
    Finset.prod_pos (fun i _ => zpow_pos (hxpos _) _)
  have hzpos : 0 < z := by
    have h1 : 0 < (w : K) ^ Q := zpow_pos hwpos Q
    have h2 : 0 < (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε) := mul_pos hPpos h1εpos
    have h3 : z * ((∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) = (w : K) ^ Q := by
      rw [hdec]; ring
    have h4 : z = (w : K) ^ Q / ((∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) := by
      rw [eq_div_iff (ne_of_gt h2)]; exact h3
    rw [h4]; exact div_pos h1 h2
  -- ## 4. `Fₙ`-membership facts used by both cases
  have hFm : ∀ a b : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      a * b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    fun a b ha hb => hFmul a ha b hb
  have hFpow : ∀ (x : K), x ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) → 0 < x →
      ∀ zz : ℤ, x ^ zz ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    sscb_zpow_mem hF1 hFmul hFinv
  have hPF : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ∈
      ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
    refine Finset.prod_induction _ _ (fun a b ha hb => hFmul a ha b hb) hF1 ?_
    intro i _
    exact hFpow _ (Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt) (hxpos _) (N i)
  have hPne : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (ne_of_gt (hxpos _)))
  have hzF : z ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    Work.WilC5.StepSeq.B_mem_Fsub hK S n hzB
  have h1epsF : (1 + ε) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
    have hEq : 1 + ε = (w : K) ^ Q * (z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)))⁻¹ := by
      rw [hdec]; field_simp
    rw [hEq]
    exact hFmul _ (hFpow _ w.2 hwpos Q) _ (hFinv _ (hFmul _ hzF _ hPF) (mul_ne_zero hz0 hPne))
  have hN0 : ∀ i : Fin n, N i = 0 := by
    intro i
    by_contra hc
    exact hNex ⟨(i : ℕ), i.isLt, hc⟩
  have hprod1 : (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [hN0 i, zpow_zero]
  have hdecB : (w : K) ^ Q = z * (1 + ε) := by
    rw [hdec, hprod1]; ring
  have hQ0 : 0 ≤ Q := le_of_lt hQpos
  have hQcast : ((Q.toNat : ℕ) : ℤ) = Q := Int.toNat_of_nonneg hQ0
  obtain ⟨u, huB, hu0, huq⟩ :=
    Work.WilC5.DclRoot (K := K) hK hrexpK haddK hmulK honeK hlenegK hBdcl hzB hzpos
      (Q := Q.toNat) (by rw [Int.le_toNat hQ0]; exact hQpos)
  have hwq : (w : K) ^ Q.toNat = u ^ Q.toNat * (1 + ε) := by
    have h := hdecB
    rw [← hQcast, zpow_natCast] at h
    rwa [← huq] at h
  have hunit1 : Work.WilC5.SameArch (1 + ε) (1 : K) := by
    have hhalf : (2 : K)⁻¹ = 1 / 2 := by norm_num
    rw [hhalf] at hεsmall
    have hεhalf : ε ≤ (1 / 2 : K) := by linarith [le_abs_self ε, hεsmall]
    have hεhalf' : -(1 / 2 : K) ≤ ε := by linarith [neg_le_abs ε, hεsmall]
    refine ⟨1, ?_, ?_⟩
    · rw [abs_one, abs_of_pos h1εpos]
      have h2 : (((1 : ℕ)) : K) + 1 = (2 : K) := by norm_num
      rw [h2]; linarith
    · rw [abs_one, abs_of_pos h1εpos]
      have h2 : (((1 : ℕ)) : K) + 1 = (2 : K) := by norm_num
      rw [h2]; linarith
  have hsc : Work.WilC5.SameArch (u ^ Q.toNat * (1 + ε)) (u ^ Q.toNat) := by
    obtain ⟨N, hN1, hN2⟩ := hunit1
    rw [abs_one, mul_one] at hN1
    rw [abs_one] at hN2
    rw [abs_of_pos h1εpos] at hN1 hN2
    refine ⟨N, ?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left hN1 (abs_nonneg (u ^ Q.toNat))
      calc |u ^ Q.toNat * (1 + ε)| = |u ^ Q.toNat| * (1 + ε) := by
            rw [abs_mul, abs_of_pos h1εpos]
        _ ≤ |u ^ Q.toNat| * ((N : K) + 1) := h
        _ = ((N : K) + 1) * |u ^ Q.toNat| := by ring
    · have h := mul_le_mul_of_nonneg_left hN2 (abs_nonneg (u ^ Q.toNat))
      rw [mul_one] at h
      calc |u ^ Q.toNat| ≤ |u ^ Q.toNat| * (((N : K) + 1) * (1 + ε)) := h
        _ = ((N : K) + 1) * (|u ^ Q.toNat| * (1 + ε)) := by ring
        _ = ((N : K) + 1) * |u ^ Q.toNat * (1 + ε)| := by rw [abs_mul, abs_of_pos h1εpos]
  have hsame_wu : Work.WilC5.SameArch (w : K) u := by
    have h1 : Work.WilC5.SameArch ((w : K) ^ Q.toNat) (u ^ Q.toNat) := by rw [hwq]; exact hsc
    have hn : 1 ≤ Q.toNat := by rw [Int.le_toNat hQ0]; exact hQpos
    exact (Work.WilC5.SameArch_pow_iff_nat hn hwpos hu0).mp h1
  have huF : u ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    Work.WilC5.StepSeq.B_mem_Fsub hK S n huB
  have hnew_u : ¬ Work.WilC5.SameArch u (S.xs n) := hnew n ⟨u, huB⟩
  have hKcut := sscb_same_arch_cut hwpos hu0 (hxpos n) hsame_wu hnew_u
  have hcutu := hcutB n ⟨u, huB⟩
  have hσu : (σ ⟨u, huF⟩ : L) = τ ⟨u, huB⟩ := hσB ⟨u, huB⟩
  have hτupos : 0 < (τ ⟨u, huB⟩ : L) := by rw [← hσu]; exact hσpos ⟨u, huF⟩ hu0
  have htF : ((w : K) / u) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
    rw [div_eq_mul_inv]
    exact hFmul _ w.2 _ (hFinv _ huF (ne_of_gt hu0))
  have htpos : 0 < ((w : K) / u) := div_pos hwpos hu0
  have htunit : Work.WilC5.SameArch ((w : K) / u) (1 : K) := by
    obtain ⟨N, hN1, hN2⟩ := hsame_wu
    have huabs : 0 < |u| := abs_pos.mpr (ne_of_gt hu0)
    refine ⟨N, ?_, ?_⟩
    · rw [abs_div, abs_one, mul_one, div_le_iff₀ huabs]
      exact hN1
    · rw [abs_div, abs_one, ← mul_div_assoc, le_div_iff₀ huabs, one_mul]
      exact hN2
  have hunitσ : Work.WilC5.SameArch (σ ⟨(w : K) / u, htF⟩ : L) (1 : L) := by
    obtain ⟨N, hN1, hN2⟩ := htunit
    rw [abs_one, mul_one] at hN1
    rw [abs_one] at hN2
    rw [abs_of_pos htpos] at hN1 hN2
    have hpos : 0 < (σ ⟨(w : K) / u, htF⟩ : L) := hσpos ⟨_, htF⟩ htpos
    have hmemN : ((N : K) + 1) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
      rw [← Nat.cast_succ]; exact hnatF (N + 1)
    have hprod : ((N : K) + 1) * ((w : K) / u) ∈
        ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := hFmul _ hmemN _ htF
    have hσN : (σ ⟨((N : K) + 1), hmemN⟩ : L) = (N : L) + 1 := by
      have h := sscb_emb_natCast haddK haddL hzeroK hzeroL honeK honeL hF0 hF1 hFadd' σ
        hnatF (N + 1)
      simpa [Nat.cast_succ] using h
    refine ⟨N, ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_one, mul_one]
      have h := (hσord ⟨(w : K) / u, htF⟩ ⟨((N : K) + 1), hmemN⟩).mp hN1
      rwa [hσN] at h
    · rw [abs_one, abs_of_pos hpos]
      have h := (hσord ⟨(1 : K), hF1⟩ ⟨((N : K) + 1) * ((w : K) / u), hprod⟩).mp hN2
      rw [sscb_emb_one honeK honeL hF1 σ,
        sscb_emb_mul hmulK hmulL hFm σ ((N : K) + 1) ((w : K) / u) hmemN htF, hσN] at h
      exact h
  have hσw_eq : (σ w : L) = (τ ⟨u, huB⟩) * (σ ⟨(w : K) / u, htF⟩ : L) := by
    have hEq : (⟨(w : K), w.2⟩ : ↥(Work.WilC5.StepSeq.Fsub hK S n))
        = ⟨u * ((w : K) / u), hFmul _ huF _ htF⟩ := by
      apply Subtype.ext
      show (w : K) = u * ((w : K) / u)
      field_simp
    have h2 : (σ ⟨u * ((w : K) / u), hFmul _ huF _ htF⟩ : L)
        = (σ ⟨u, huF⟩ : L) * (σ ⟨(w : K) / u, htF⟩ : L) :=
      sscb_emb_mul hmulK hmulL hFm σ u ((w : K) / u) huF htF
    calc (σ w : L) = (σ ⟨(w : K), w.2⟩ : L) := rfl
      _ = (σ ⟨u * ((w : K) / u), hFmul _ huF _ htF⟩ : L) := congrArg σ hEq
      _ = (σ ⟨u, huF⟩ : L) * (σ ⟨(w : K) / u, htF⟩ : L) := h2
      _ = (τ ⟨u, huB⟩) * (σ ⟨(w : K) / u, htF⟩ : L) := by rw [hσu]
  have hsame_σ : Work.WilC5.SameArch (σ w : L) (τ ⟨u, huB⟩) := by
    rw [hσw_eq]
    obtain ⟨N, hN1, hN2⟩ := hunitσ
    rw [abs_one, mul_one] at hN1
    rw [abs_one] at hN2
    refine ⟨N, ?_, ?_⟩
    · rw [abs_mul]
      calc |(τ ⟨u, huB⟩ : L)| * |(σ ⟨(w : K) / u, htF⟩ : L)|
          ≤ |(τ ⟨u, huB⟩ : L)| * ((N : L) + 1) :=
            mul_le_mul_of_nonneg_left hN1 (abs_nonneg _)
        _ = ((N : L) + 1) * |(τ ⟨u, huB⟩ : L)| := by ring
    · rw [abs_mul]
      calc |(τ ⟨u, huB⟩ : L)| = |(τ ⟨u, huB⟩ : L)| * 1 := (mul_one _).symm
        _ ≤ |(τ ⟨u, huB⟩ : L)| * (((N : L) + 1) * |(σ ⟨(w : K) / u, htF⟩ : L)|) :=
            mul_le_mul_of_nonneg_left hN2 (abs_nonneg _)
        _ = ((N : L) + 1) * (|(τ ⟨u, huB⟩ : L)| * |(σ ⟨(w : K) / u, htF⟩ : L)|) := by ring
  have hnew_τu : ¬ Work.WilC5.SameArch (τ ⟨u, huB⟩)
      (Work.WilC5.StepSeq.ys B τ S y0 n) := by
    intro hc
    obtain ⟨ha, hb⟩ := (Work.WilC5.SameArch_iff_VLe _ _).mp hc
    have hStep := Work.WilC5.StepSeqYVLe (K := K) (L := L) hK hL hrexpK haddK hmulK honeK
      hlenegK hrexpL haddL hmulL honeL hlenegL τ S hnew hcutB n ⟨u, huB⟩
    exact hnew_u ((Work.WilC5.SameArch_iff_VLe u (S.xs n)).mpr
      ⟨hStep.1.mpr ha, hStep.2.mpr hb⟩)
  have hLcut := sscb_same_arch_cut (hσpos w hwpos) hτupos (hypos n) hsame_σ hnew_τu
  exact ⟨hKcut.1.trans (hcutu.1.trans hLcut.1.symm),
    hKcut.2.trans (hcutu.2.trans hLcut.2.symm)⟩

end Work.WilC5
