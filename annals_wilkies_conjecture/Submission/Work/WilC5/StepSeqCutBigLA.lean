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

theorem sscb_cut_pos_A
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
    (hdec : (w : K) ^ Q = z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) (hNex : ∃ k : ℕ, ∃ hk : k < n, N ⟨k, hk⟩ ≠ 0) :
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
  set m0 : ℕ := Nat.find hNex with hm0def
  have hm0lt : m0 < n := (Nat.find_spec hNex).1
  have hm0ne : N ⟨m0, hm0lt⟩ ≠ 0 := (Nat.find_spec hNex).2
  have hm0min : ∀ k (hk : k < m0), N ⟨k, lt_trans hk hm0lt⟩ = 0 := by
    intro k hk
    by_contra hc
    exact Nat.find_min hNex hk ⟨lt_trans hk hm0lt, hc⟩
  set m : Fin n := ⟨m0, hm0lt⟩ with hmdef
  have hmne : N m ≠ 0 := hm0ne
  have hmmin : ∀ i : Fin n, (i : ℕ) < (m : ℕ) → N i = 0 := by
    intro i hi
    exact hm0min (i : ℕ) hi
  have hxsl : ∀ j : ℕ, (m : ℕ) < j → j ≤ n →
      Work.WilC5.VLe (S.xs ((m : ℕ) + 1)) (Work.WilC5.logFun (S.xs j)) ∧
        ¬ Work.WilC5.VLe (Work.WilC5.logFun (S.xs j)) (S.xs ((m : ℕ) + 1)) :=
    fun j hlt _ => hlogsm ((m : ℕ) + 1) j (by omega)
  have h1εunit : WilkiesDesign.CG.IsUnitVal (1 + ε) := by
    have hhalf : ((((1 : ℕ)) : K) + 1)⁻¹ = (1 / 2 : K) := by norm_num
    have hεhalf : |ε| ≤ (1 / 2 : K) := by
      have h2 : (2 : K)⁻¹ = 1 / 2 := by norm_num
      rwa [h2] at hεsmall
    have ht : (1 : K) ≤ |1 + ε| + |ε| := by
      have h := abs_add_le (1 + ε) (-ε)
      have h3 : (1 + ε) + (-ε) = (1 : K) := by ring
      rw [h3, abs_one, abs_neg] at h
      exact h
    refine ⟨1, ?_, ?_⟩
    · rw [hhalf]
      linarith [neg_le_abs ε]
    · have h := abs_add_le (1 : K) ε
      rw [abs_one] at h
      have hgoal : (((1 : ℕ)) : K) + 1 = (2 : K) := by norm_num
      rw [hgoal]
      linarith [le_abs_self ε]
  have heps_small : Work.WilC5.VLe (S.xs ((m : ℕ) + 1)) (Work.WilC5.logFun (1 + ε)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (1 + ε)) (S.xs ((m : ℕ) + 1)) :=
    Work.WilC5.VLe_of_isFiniteVal_of_infinite (a := S.xs ((m : ℕ) + 1))
      (fun N => hxbig _ N)
      (Work.WilC5.LogUnitFinite hrexpK haddK hmulK honeK hlenegK h1εunit)
  have hrho : ¬ Work.WilC5.SameArch
      (Work.WilC5.logFun z + (N m : K) * (S.beta m : K)) (S.xs ((m : ℕ) + 1)) := by
    have hmem : Work.WilC5.logFun z + (N m : K) * (S.beta m : K) ∈ (B : Set K) :=
      hBadd _ (hBlog z hzB) _ (hBmul _ (hint_mem (N m)) _ (S.beta m).2)
    have h := hnew ((m : ℕ) + 1) ⟨_, hmem⟩
    simpa using h
  have hrel : Work.WilC5.logFun (S.xs (m : ℕ)) = (S.beta m : K) + S.xs ((m : ℕ) + 1) ∨
      Work.WilC5.logFun (S.xs (m : ℕ)) = (S.beta m : K) - S.xs ((m : ℕ) + 1) := by
    have h := S.hrel (m : ℕ)
    by_cases hp : S.pos (m : ℕ) = true
    · left; rw [if_pos hp, haddK] at h; exact h
    · right; rw [if_neg hp, hsubEK] at h; exact h
  have hKcomp := Work.WilC5.CutComp (log := Work.WilC5.logFun) hlogltK hlogmulK hlogzpowK
    (fun i : ℕ => S.xs i) hxpos hwpos hzpos h1εpos hQpos N hdec hmne hmmin hrel
    hxsl heps_small hrho
  -- ## the `L`-side
  have hdecL0 : (σ ⟨(w : K), w.2⟩ : L) ^ Q
      = (τ ⟨z, hzB⟩) * (∏ i : Fin n,
          (σ ⟨S.xs (i : ℕ), Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt⟩ : L) ^ (N i))
        * (1 + (σ ⟨1 + ε, h1epsF⟩ - 1)) := by
    have hEq : (⟨(w : K) ^ Q, hFpow _ w.2 hwpos Q⟩ : ↥(Work.WilC5.StepSeq.Fsub hK S n))
        = ⟨z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε),
            hFmul _ (hFmul _ hzF _ hPF) _ h1epsF⟩ := Subtype.ext hdec
    have h1 := congrArg σ hEq
    rw [sscb_emb_zpow honeK hmulK hmulL honeL hF1 hFm σ (w : K) w.2 (ne_of_gt hwpos)
      (fun i : ℕ => by rw [← zpow_natCast]; exact hFpow (w : K) w.2 hwpos (i : ℤ))
      (fun i : ℤ => hFpow (w : K) w.2 hwpos i) Q] at h1
    rw [sscb_emb_mul hmulK hmulL hFm σ _ _ (hFmul _ hzF _ hPF) h1epsF] at h1
    rw [sscb_emb_mul hmulK hmulL hFm σ _ _ hzF hPF] at h1
    rw [sscb_emb_prod_zpow honeK hmulK hmulL honeL hF1 hFm σ
      (fun i : Fin n => S.xs (i : ℕ)) (fun i => Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt)
      (fun i => ne_of_gt (hxpos _))
      (fun i (mm : ℕ) => by rw [← zpow_natCast]; exact hFpow (S.xs (i : ℕ)) (Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt) (hxpos (i : ℕ)) (mm : ℤ))
      (fun i (zz : ℤ) => hFpow (S.xs (i : ℕ)) (Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt) (hxpos (i : ℕ)) zz) N (Finset.univ) hPF] at h1
    rw [hσB ⟨z, hzB⟩] at h1
    rw [show (1 : L) + (σ ⟨1 + ε, h1epsF⟩ - 1) = σ ⟨1 + ε, h1epsF⟩ from by ring]
    exact h1
  have hdecL : (σ ⟨(w : K), w.2⟩ : L) ^ Q
      = (τ ⟨z, hzB⟩) * (∏ i : Fin n,
          Work.WilC5.StepSeq.ys B τ S y0 (i : ℕ) ^ (N i))
        * (1 + (σ ⟨1 + ε, h1epsF⟩ - 1)) := by
    rw [hdecL0, show (∏ i : Fin n,
          (σ ⟨S.xs (i : ℕ), Work.WilC5.StepSeq.xs_mem_Fsub hK S i.isLt⟩ : L) ^ (N i))
        = ∏ i : Fin n, Work.WilC5.StepSeq.ys B τ S y0 (i : ℕ) ^ (N i) from
      Finset.prod_congr rfl (fun i _ => by rw [hσxs (i : ℕ) i.isLt])]
  have hysinf : ∀ i : ℕ, ¬ Work.WilC5.IsFiniteVal (Work.WilC5.StepSeq.ys B τ S y0 i) :=
    fun i => sscb_not_finite (hysbig i)
  have hysdom : ∀ i : ℕ, Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 i)
      (Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i))
        (Work.WilC5.StepSeq.ys B τ S y0 i) :=
    fun i => Work.WilC5.LogDominatedOfInfinite hrexpL haddL hmulL honeL hlenegL
      (hypos i) (hysinf i)
  have hτβ : ∀ i : ℕ, Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 i) (τ (S.beta i)) ∧
      ¬ Work.WilC5.VLe (τ (S.beta i)) (Work.WilC5.StepSeq.ys B τ S y0 i) := by
    intro i
    have h := Work.WilC5.StepSeqYVLe (K := K) (L := L) hK hL hrexpK haddK hmulK honeK
      hlenegK hrexpL haddL hmulL honeL hlenegL τ S hnew hcutB i (S.beta i)
    exact ⟨h.2.mp (hbetasm i).1, fun hc => (hbetasm i).2 (h.1.mpr hc)⟩
  have hysstep : ∀ j : ℕ, Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 j)
      (Work.WilC5.StepSeq.ys B τ S y0 (j + 1)) := by
    intro j
    have hrelj := Work.WilC5.StepSeq.ys_rel B τ S y0 j
    have h2 : Work.WilC5.StepSeq.ys B τ S y0 (j + 1)
        = Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j) - (τ (S.beta j) : L) ∨
        Work.WilC5.StepSeq.ys B τ S y0 (j + 1)
          = (τ (S.beta j) : L) - Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j) := by
      by_cases hp : S.pos j = true
      · left; rw [hrelj, if_pos hp]; ring
      · right; rw [hrelj, if_neg hp]; ring
    have hb : |Work.WilC5.StepSeq.ys B τ S y0 (j + 1)|
        ≤ |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| + |(τ (S.beta j) : L)| := by
      rcases h2 with h | h
      · calc |Work.WilC5.StepSeq.ys B τ S y0 (j + 1)|
            = |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j) + -(τ (S.beta j) : L)| := by
              rw [h, sub_eq_add_neg]
          _ ≤ |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| + |-(τ (S.beta j) : L)| :=
              abs_add_le _ _
          _ = |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| + |(τ (S.beta j) : L)| := by
              rw [abs_neg]
      · calc |Work.WilC5.StepSeq.ys B τ S y0 (j + 1)|
            = |(τ (S.beta j) : L) + -(Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j))| := by
              rw [h, sub_eq_add_neg]
          _ ≤ |(τ (S.beta j) : L)| + |-(Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j))| :=
              abs_add_le _ _
          _ = |(τ (S.beta j) : L)| + |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| := by
              rw [abs_neg]
          _ = |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| + |(τ (S.beta j) : L)| := by
              ring
    obtain ⟨C1, hC1⟩ := (hysdom j).1
    obtain ⟨C2, hC2⟩ := (hτβ j).1
    refine ⟨C1 + C2 + 1, ?_⟩
    calc |Work.WilC5.StepSeq.ys B τ S y0 (j + 1)|
        ≤ |Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)| + |(τ (S.beta j) : L)| := hb
      _ ≤ (((C1 : ℕ) : L) + 1) * |Work.WilC5.StepSeq.ys B τ S y0 j|
          + (((C2 : ℕ) : L) + 1) * |Work.WilC5.StepSeq.ys B τ S y0 j| := add_le_add hC1 hC2
      _ = ((((C1 + C2 + 1 : ℕ)) : L) + 1) * |Work.WilC5.StepSeq.ys B τ S y0 j| := by
          push_cast; ring
  have hysmono : ∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 i)
      (Work.WilC5.StepSeq.ys B τ S y0 j) := by
    have hstep : ∀ i k : ℕ, Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 i)
        (Work.WilC5.StepSeq.ys B τ S y0 (i + k)) := by
      intro i k
      induction k with
      | zero => simpa using Work.WilC5.VLe_refl (Work.WilC5.StepSeq.ys B τ S y0 i)
      | succ k ih => rw [Nat.add_succ]; exact Work.WilC5.VLe_trans ih (hysstep (i + k))
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact hstep i k
  have hlogltL : ∀ {x y : L}, 0 < x → 0 < y →
      (Work.WilC5.logFun x < Work.WilC5.logFun y ↔ x < y) := sscb_log_lt hL haddL hlenegL
  have hlogmulL : ∀ {x y : L}, 0 < x → 0 < y →
      Work.WilC5.logFun (x * y) = Work.WilC5.logFun x + Work.WilC5.logFun y :=
    fun {x y} hx hy => Work.WilC5.S4ExpF.logFun_mul_of_pos hL haddL hmulL hlenegL hx hy
  have hlogzpowL : ∀ {x : L}, 0 < x → ∀ k : ℤ,
      Work.WilC5.logFun (x ^ k) = (k : L) * Work.WilC5.logFun x :=
    fun {x} hx k => Work.WilC5.S4ExpF.logFun_zpow hL haddL hmulL honeL hlenegL x hx k
  have hsmallL : ∀ j : ℕ, (m : ℕ) < j → j ≤ n →
      Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1))
        (Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 j))
        (Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1)) := by
    intro j hlt _
    have hji : (m : ℕ) + 1 ≤ j := by omega
    exact ⟨Work.WilC5.VLe_trans (hysmono _ _ hji) (hysdom j).1,
      fun hc => (hysdom j).2 (Work.WilC5.VLe_trans hc (hysmono _ _ hji))⟩
  have hzposL : 0 < (τ ⟨z, hzB⟩ : L) := hτpos ⟨z, hzB⟩ hzpos
  have h1epsLpos : 0 < (1 : L) + (σ ⟨1 + ε, h1epsF⟩ - 1) := by
    have hpos := hσpos ⟨1 + ε, h1epsF⟩ h1εpos
    rwa [show (1 : L) + (σ ⟨1 + ε, h1epsF⟩ - 1) = σ ⟨1 + ε, h1epsF⟩ from by ring]
  have heps_smallL : Work.WilC5.VLe (Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1))
        (Work.WilC5.logFun (1 + (σ ⟨1 + ε, h1epsF⟩ - 1))) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (1 + (σ ⟨1 + ε, h1epsF⟩ - 1)))
        (Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1)) := by
    have hunit : WilkiesDesign.CG.IsUnitVal (σ ⟨1 + ε, h1epsF⟩) := by
      have hle : (σ ⟨(0 : K), hF0⟩ : L) ≤ σ ⟨1 + ε, h1epsF⟩ :=
        (hσord ⟨(0 : K), hF0⟩ ⟨1 + ε, h1epsF⟩).mp (le_of_lt h1εpos)
      rw [hσ0] at hle
      have h2F : ((2 : ℕ) : K) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := hnatF 2
      have hσtwo : (σ ⟨((2 : ℕ) : K), h2F⟩ : L) = ((2 : ℕ) : L) :=
        sscb_emb_natCast haddK haddL hzeroK hzeroL honeK honeL hF0 hF1 hFadd' σ hnatF 2
      have h2L : ((2 : ℕ) : L) = (2 : L) := by norm_num
      have h2Kc : ((2 : ℕ) : K) = (2 : K) := by norm_num
      have hle2 : σ ⟨1 + ε, h1epsF⟩ ≤ (2 : L) := by
        rw [← h2L]
        have h2K : (1 : K) + ε ≤ ((2 : ℕ) : K) := by
          rw [h2Kc]
          have h1 : (2 : K)⁻¹ ≤ 1 := by norm_num
          linarith [le_abs_self ε, hεsmall, h1]
        have h := (hσord ⟨1 + ε, h1epsF⟩ ⟨((2 : ℕ) : K), h2F⟩).mp h2K
        rwa [hσtwo] at h
      refine ⟨1, ?_, ?_⟩
      · rw [show (((1 : ℕ)) : L) + 1 = (2 : L) from by norm_num, abs_of_nonneg hle,
          ← h2L]
        have hp1 : ((2 : ℕ) : K) ^ (-1 : ℤ) ∈
            ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
          hFpow ((2 : ℕ) : K) h2F (by norm_num) (-1)
        have hlow : ((2 : ℕ) : K) ^ (-1 : ℤ) ≤ 1 + ε := by
          rw [zpow_neg_one]
          have h2 : ((2 : ℕ) : K)⁻¹ = 1 / 2 := by norm_num
          rw [h2]
          have h3 : (2 : K)⁻¹ = 1 / 2 := by norm_num
          rw [h3] at hεsmall
          linarith [neg_le_abs ε, hεsmall]
        have h := (hσord ⟨((2 : ℕ) : K) ^ (-1 : ℤ), hp1⟩ ⟨1 + ε, h1epsF⟩).mp hlow
        have hz := sscb_emb_zpow honeK hmulK hmulL honeL hF1 hFm σ (((2 : ℕ) : K)) h2F
          (by norm_num)
          (fun nn : ℕ => by
            rw [← zpow_natCast]
            exact hFpow ((2 : ℕ) : K) h2F (by norm_num) (nn : ℤ))
          (hFpow ((2 : ℕ) : K) h2F (by norm_num)) (-1)
        rw [hz, zpow_neg_one, hσtwo] at h
        exact h
      · rw [show (((1 : ℕ)) : L) + 1 = (2 : L) from by norm_num, abs_of_nonneg hle]
        exact hle2
    have hfin' : Work.WilC5.IsFiniteVal
        (Work.WilC5.logFun (1 + (σ ⟨1 + ε, h1epsF⟩ - 1))) := by
      rw [show (1 : L) + (σ ⟨1 + ε, h1epsF⟩ - 1) = σ ⟨1 + ε, h1epsF⟩ from by ring]
      exact Work.WilC5.LogUnitFinite hrexpL haddL hmulL honeL hlenegL hunit
    exact Work.WilC5.VLe_of_isFiniteVal_of_infinite
      (a := Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1)) (hysbig _) hfin'
  have hrhoL : ¬ Work.WilC5.SameArch
      (Work.WilC5.logFun (τ ⟨z, hzB⟩) + (N m : L) * (τ (S.beta m) : L))
      (Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1)) := by
    have hmem : Work.WilC5.logFun z + (N m : K) * (S.beta m : K) ∈ (B : Set K) :=
      hBadd _ (hBlog z hzB) _ (hBmul _ (hint_mem (N m)) _ (S.beta m).2)
    have hStep := Work.WilC5.StepSeqYVLe (K := K) (L := L) hK hL hrexpK haddK hmulK honeK
      hlenegK hrexpL haddL hmulL honeL hlenegL τ S hnew hcutB ((m : ℕ) + 1) ⟨_, hmem⟩
    have hτmem : (τ ⟨_, hmem⟩ : L)
        = Work.WilC5.logFun (τ ⟨z, hzB⟩) + (N m : L) * (τ (S.beta m) : L) := by
      rw [sscb_emb_add haddK haddL hBadd' τ _ _
            (hBlog z hzB) (hBmul _ (hint_mem (N m)) _ (S.beta m).2),
          sscb_emb_mul hmulK hmulL hBmul' τ _ _ (hint_mem (N m)) (S.beta m).2,
          sscb_emb_intCast haddK haddL hzeroK hzeroL honeK honeL hnegEK hnegEL hB0 hB1 hBneg
            hBadd τ hint_mem (N m),
          hτlog ⟨z, hzB⟩]
    rw [← hτmem]
    intro hc
    exact hrho ((Work.WilC5.SameArch_iff_VLe _ _).mpr
      ⟨hStep.1.mpr ((Work.WilC5.SameArch_iff_VLe _ _).mp hc).1,
       hStep.2.mpr ((Work.WilC5.SameArch_iff_VLe _ _).mp hc).2⟩)
  have hrelL : Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 (m : ℕ))
      = (τ (S.beta m) : L) + Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1) ∨
      Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 (m : ℕ))
        = (τ (S.beta m) : L) - Work.WilC5.StepSeq.ys B τ S y0 ((m : ℕ) + 1) := by
    have h := Work.WilC5.StepSeq.ys_rel B τ S y0 (m : ℕ)
    by_cases hp : S.pos (m : ℕ) = true
    · left; rw [if_pos hp] at h; exact h
    · right; rw [if_neg hp] at h; exact h
  have hLcomp := Work.WilC5.CutComp (log := Work.WilC5.logFun) hlogltL hlogmulL hlogzpowL
    (fun i : ℕ => Work.WilC5.StepSeq.ys B τ S y0 i) hypos (hσpos w hwpos)
    hzposL h1epsLpos hQpos N hdecL hmne hmmin hrelL hsmallL heps_smallL hrhoL
  -- ## gluing the two min-rule computations
  have hxsF : S.xs (m : ℕ) ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    Work.WilC5.StepSeq.xs_mem_Fsub hK S m.isLt
  have hpwm : (S.xs (m : ℕ)) ^ (N m) ∈
      ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    hFpow _ hxsF (hxpos _) (N m)
  have haF : z * (S.xs (m : ℕ)) ^ (N m) ∈
      ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) :=
    hFmul _ hzF _ hpwm
  have hσa : (σ ⟨z * (S.xs (m : ℕ)) ^ (N m), haF⟩ : L)
      = (τ ⟨z, hzB⟩) * (Work.WilC5.StepSeq.ys B τ S y0 (m : ℕ)) ^ (N m) := by
    rw [sscb_emb_mul hmulK hmulL hFm σ z ((S.xs (m : ℕ)) ^ (N m)) hzF hpwm,
      sscb_emb_zpow honeK hmulK hmulL honeL hF1 hFm σ (S.xs (m : ℕ)) hxsF (ne_of_gt (hxpos _))
        (fun nn : ℕ => by rw [← zpow_natCast]; exact hFpow _ hxsF (hxpos _) (nn : ℤ))
        (hFpow _ hxsF (hxpos _)) (N m),
      hσB ⟨z, hzB⟩, hσxs (m : ℕ) m.isLt]
  have hle_lo := (hσord ⟨z * (S.xs (m : ℕ)) ^ (N m), haF⟩ ⟨(1 : K), hF1⟩)
  have hle_hi := (hσord ⟨(1 : K), hF1⟩ ⟨z * (S.xs (m : ℕ)) ^ (N m), haF⟩)
  rw [sscb_emb_one honeK honeL hF1 σ] at hle_lo hle_hi
  have hb1 : z * (S.xs (m : ℕ)) ^ (N m) < 1 ↔
      (τ ⟨z, hzB⟩) * (Work.WilC5.StepSeq.ys B τ S y0 (m : ℕ)) ^ (N m) < 1 := by
    rw [← hσa, lt_iff_le_not_ge, lt_iff_le_not_ge, hle_lo, hle_hi]
  have hb2 : 1 < z * (S.xs (m : ℕ)) ^ (N m) ↔
      1 < (τ ⟨z, hzB⟩) * (Work.WilC5.StepSeq.ys B τ S y0 (m : ℕ)) ^ (N m) := by
    rw [← hσa, lt_iff_le_not_ge, lt_iff_le_not_ge, hle_hi, hle_lo]
  exact ⟨hKcomp.2.trans (hb1.trans hLcomp.2.symm),
    hKcomp.1.trans (hb2.trans hLcomp.1.symm)⟩

end Work.WilC5
