import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.LRcSatOfLEcSat
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.StepExpVA
import Submission.Work.WilC5.StepExpDclExtend
import Submission.Work.WilC5.S4ExpG.logPreserving_exp_aux
import Submission.Work.WilC5.StepExpCut

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- A substructure of `M` at an explicitly given `LRc`-structure, from a carrier and its
closure under the function symbols. -/
def stepMkSub (M : Type) (i : LRc.Structure M) (S : Set M)
    (hmem : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → M),
      (∀ k, x k ∈ S) → @Structure.funMap LRc M i n f x ∈ S) :
    @FirstOrder.Language.Substructure LRc M i := by
  letI : LRc.Structure M := i
  exact ⟨S, fun {n} f x hx => hmem f x hx⟩

@[simp] theorem stepMkSub_coe {M : Type} (i : LRc.Structure M) (S : Set M) (hmem) :
    (stepMkSub M i S hmem : Set M) = S := rfl

/-- **`logFun` of an integer power**: `log (x^n) = n · log x` for `0 < x`. -/
theorem stepLogFun_zpow {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y)
    (hmul : ∀ x y : K, mulE x y = x * y) (hone : (oneE : K) = 1)
    (hleneg : ∀ x y : K, leE x y ↔ x ≤ y)
    {x : K} (hx : 0 < x) (n : ℤ) :
    logFun (x ^ n) = (n : K) * logFun x := by
  have hmulpos : ∀ {y z : K}, 0 < y → 0 < z →
      logFun (y * z) = logFun y + logFun z :=
    fun hy hz => S4ExpF.logFun_mul_pos hTE hadd hmul hleneg hy hz
  have hnat : ∀ k : ℕ, logFun (x ^ k) = (k : K) * logFun x := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero]
        have h := S4ExpF.logFun_one hTE hadd hone
        rw [h]; simp
    | succ k ih =>
        have hxk : 0 < x ^ k := pow_pos hx k
        rw [pow_succ, hmulpos hxk hx, ih]
        push_cast
        ring
  have hinv : ∀ {y : K}, 0 < y → logFun y⁻¹ = -logFun y := by
    intro y hy
    have hyi : 0 < y⁻¹ := inv_pos.mpr hy
    have h := hmulpos hy hyi
    rw [mul_inv_cancel₀ (ne_of_gt hy)] at h
    have h1 := S4ExpF.logFun_one hTE hadd hone
    rw [h1] at h
    linarith
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk, zpow_natCast]
    push_cast
    exact hnat k
  · rw [hk, zpow_neg, zpow_natCast]
    rw [show logFun ((x ^ k)⁻¹) = -logFun (x ^ k) from hinv (pow_pos hx k)]
    rw [hnat k]
    push_cast
    ring

theorem StepExp
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR) (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LEc L _ κ)
    {A₀ : WilkiesDesign.CG.LRc.Substructure K}
    {σ₀ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥A₀ L _ (Work.WilC5.reductStruct L)}
    (p : Work.WilC5.S4Pair A₀ σ₀)
    (a : ↥p.dom) (ha : Work.WilC5.expE (a : K) ∉ (p.dom : Set K))
    (hvalnew : ∀ y : K, y ∉ (p.dom : Set K) →
      ¬ (∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {y}) →
          ∃ b : ↥p.dom, Work.WilC5.SameVal K hK (b : K) w)) :
    ∃ q : Work.WilC5.S4Pair A₀ σ₀, p ≤ q ∧ ∃ b : ↥q.dom, (b : K) = Work.WilC5.expE (a : K) := by
  classical
  ------------------------------------------------------------------------------------ #
  -- Stage 1: the canonical ordered-field data, at the `rexp`-reduct                   #
  ------------------------------------------------------------------------------------ #
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  have hKTR : K ⊨ TR := reductTR hK
  have hLTR : L ⊨ TR := reductTR hL
  haveI : K ⊨ TR := hKTR
  haveI : L ⊨ TR := hLTR
  haveI : K ⊨ Theory.field := tr_ring_field K hKTR
  haveI : L ⊨ Theory.field := tr_ring_field L hLTR
  letI : Field K := cField K hK
  letI : LinearOrder K := cLin K hK
  letI : Ring.CompatibleRing K := FirstOrder.Field.compatibleRingOfModelField K
  letI : IsStrictOrderedRing K := tr_isStrictOrderedRing K hKTR
  letI : Field L := cField L hL
  letI : LinearOrder L := cLin L hL
  letI : Ring.CompatibleRing L := FirstOrder.Field.compatibleRingOfModelField L
  letI : IsStrictOrderedRing L := tr_isStrictOrderedRing L hLTR
  -- the syntactic structure agrees with the reduct
  have hstructK : (reductStruct K : LRc.Structure K) = (LR.withConstantsStructure ℝ) := by
    ext n f x
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r
          show Work.WilC5.rexpFromExp (x 0) = _
          rfl
      · rfl
    · nomatch f
  have hstructL : (reductStruct L : LRc.Structure L) = (LR.withConstantsStructure ℝ) := by
    ext n f x
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r
          show Work.WilC5.rexpFromExp (x 0) = _
          rfl
      · rfl
    · nomatch f
  have hKTRsyn : @Theory.Model LRc K (LR.withConstantsStructure ℝ) TR := hstructK ▸ hKTR
  have hLTRsyn : @Theory.Model LRc L (LR.withConstantsStructure ℝ) TR := hstructL ▸ hLTR
  have funMapK : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → K),
      @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f x
        = @Structure.funMap LRc K (reductStruct K) n f x :=
    fun f x => (congrArg (fun i => @Structure.funMap LRc K i _ f x) hstructK).symm
  have funMapL : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → L),
      @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f x
        = @Structure.funMap LRc L (reductStruct L) n f x :=
    fun f x => (congrArg (fun i => @Structure.funMap LRc L i _ f x) hstructL).symm
  -- compatibility of the `LEc` symbols with the field operations
  have hrexpK : ∀ x : K, @Structure.funMap rexpL K _ 1 rexpFunc.rexp ![x] = rexpFromExp x :=
    fun x => rfl
  have hrexpL : ∀ x : L, @Structure.funMap rexpL L _ 1 rexpFunc.rexp ![x] = rexpFromExp x :=
    fun x => rfl
  have haddK : ∀ x y : K, addE x y = x + y := by
    intro x y; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![x, y]
  have haddL : ∀ x y : L, addE x y = x + y := by
    intro x y; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![x, y]
  have hmulK : ∀ x y : K, mulE x y = x * y := by
    intro x y; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![x, y]
  have hmulL : ∀ x y : L, mulE x y = x * y := by
    intro x y; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![x, y]
  have honeK : (oneE : K) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  have honeL : (oneE : L) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  have hnegK : ∀ x : K, negE x = -x := by
    intro x; rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![x]
  have hnegL : ∀ x : L, negE x = -x := by
    intro x; rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![x]
  have hlenegK : ∀ x y : K, leE x y ↔ x ≤ y := by
    intro x y
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulK z z, subE, haddK, hnegK] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := K) hKTRsyn (y - x) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulK z z, subE, haddK, hnegK]; ring_nf; linarith [hz]⟩
  have hlenegL : ∀ x y : L, leE x y ↔ x ≤ y := by
    intro x y
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulL z z, subE, haddL, hnegL] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := L) hLTRsyn (y - x) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulL z z, subE, haddL, hnegL]; ring_nf; linarith [hz]⟩
  ------------------------------------------------------------------------------------ #
  -- Stage 2: the domain of `p`, at both structures                                    #
  ------------------------------------------------------------------------------------ #
  let A : Set K := (p.dom : Set K)
  have hAdcl : @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A ⊆ A := by
    intro z hz
    have h1 : @Work.WilC2.Dcl K (reductStruct K) A
        = @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A :=
      congrArg (fun i => @Work.WilC2.Dcl K i A) hstructK
    rw [← h1] at hz
    exact p.h4.dcl_closed hz
  have hAlog : ∀ x ∈ A, logFun x ∈ A := p.h4.log_closed
  have hExpa : expE (a : K) ∉ A := ha
  -- `B`: the domain of `p`, as a substructure at the syntactic structure
  let B : @FirstOrder.Language.Substructure LRc K (LR.withConstantsStructure ℝ) :=
    stepMkSub K (LR.withConstantsStructure ℝ) A (fun {n} f x hx => by
      rw [funMapK f x]
      exact p.dom.fun_mem f x hx)
  have hBcoe : (B : Set K) = A := rfl
  have hBlog : ∀ x ∈ (B : Set K), logFun x ∈ (B : Set K) := by
    intro x hx; rw [hBcoe] at hx ⊢; exact hAlog x hx
  ------------------------------------------------------------------------------------ #
  -- Stage 3: the value decomposition `hVA`                                             #
  ------------------------------------------------------------------------------------ #
  have hVA : ∀ w ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}), w ≠ 0 →
      ∃ Q : ℤ, 0 < Q ∧ ∃ N : ℤ, ∃ z ∈ A, z ≠ 0 ∧ ∃ ε : K, IsInfinitesimal ε ∧
        w ^ Q = z * (expE (a : K)) ^ N * (1 + ε) :=
    StepExpVA hOM hVI hK hrexpK haddK hmulK honeK hlenegK A hAdcl hAlog (a : K) a.2 hExpa
  ------------------------------------------------------------------------------------ #
  -- Stage 4: the embedding `τ : B → L`, and its log-preservation                       #
  ------------------------------------------------------------------------------------ #
  let aB : ↥B := ⟨(a : K), a.2⟩
  let τfun : ↥B → L := fun b => p.emb ⟨(b : K), b.2⟩
  have hτinj : Function.Injective τfun := by
    intro u v huv
    have h : (⟨(u : K), u.2⟩ : ↥p.dom) = ⟨(v : K), v.2⟩ := p.emb.injective huv
    exact Subtype.ext (congrArg (fun z : ↥p.dom => (z : K)) h)
  have hτmap : ∀ {n : ℕ} (f : LRc.Functions n) (y : Fin n → ↥B),
      τfun (@Structure.funMap LRc ↥B _ n f y)
        = @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f (τfun ∘ y) := by
    intro n f y
    let w : Fin n → ↥p.dom := fun i => ⟨(y i : K), (y i).2⟩
    have hLHS : τfun (@Structure.funMap LRc ↥B _ n f y)
        = p.emb (@Structure.funMap LRc ↥p.dom _ n f w) := by
      apply congrArg p.emb
      apply Subtype.ext
      show @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f (fun i => (y i : K))
        = @Structure.funMap LRc K (reductStruct K) n f (fun i => (w i : K))
      rw [show (fun i => (y i : K)) = (fun i => (w i : K)) from rfl]
      exact funMapK f (fun i => (w i : K))
    have hRHS : @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f (τfun ∘ y)
        = @Structure.funMap LRc L (reductStruct L) n f (p.emb ∘ w) := by
      rw [show (τfun ∘ y) = (p.emb ∘ w) from rfl]
      exact funMapL f (p.emb ∘ w)
    rw [hLHS, hRHS]
    exact @FirstOrder.Language.Embedding.map_fun' LRc ↥p.dom L _ _ p.emb n f w
  let τ : @FirstOrder.Language.Embedding LRc ↥B L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) B)
      (LR.withConstantsStructure ℝ) :=
    @Embedding.mk LRc ↥B L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) B)
      (LR.withConstantsStructure ℝ) ⟨τfun, hτinj⟩ hτmap
      (by intro n R x; exact nomatch R)
  have hτlog : ∀ x : ↥B, τ ⟨logFun (x : K), hBlog (x : K) x.2⟩ = logFun (τ x) := by
    intro x
    exact p.logpres ⟨(x : K), x.2⟩
  ------------------------------------------------------------------------------------ #
  -- Stage 5: the cut of `expE a` over `B` and the extension to the definable closure   #
  ------------------------------------------------------------------------------------ #
  have hcut := StepExpCut hMCr hOM hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL
    honeL hlenegL B hAdcl hBlog aB τ hτlog
  obtain ⟨S, hS, hSdcl, hle, hxS, σ', hσ'B, hσ'x⟩ :=
    StepExpDclExtend hMCr hOM B (model_TR_of_dcl_closed hOM B hAdcl) hAdcl τ hcut
  ------------------------------------------------------------------------------------ #
  -- Stage 6: log-closure of `S`                                                        #
  ------------------------------------------------------------------------------------ #
  set P : Set K := A ∪ {expE (a : K)} with hP
  have hPdcl : @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P = (S : Set K) := by
    rw [hP, hS, hBcoe]
  have hlogcl : ∀ w ∈ (S : Set K), logFun w ∈ (S : Set K) := by
    have h0 : ∀ w ∈ (S : Set K), logFun w ∈ (S : Set K) := by
      intro w hw
      have hwP : w ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P := by rw [hPdcl]; exact hw
      by_cases hw0 : w = 0
      · subst hw0
        rw [S4ExpF.logFun_eq_zero_of_not_pos hK haddK honeK hlenegK (0 : K) (not_lt.mpr le_rfl)]
        rw [← hPdcl]
        exact S4ExpF.dcl_zero_mem P
      · by_cases hpos : 0 < w
        · obtain ⟨Q, hQ, N, z, hzA, hz0, ε, hε, hdec⟩ := hVA w hwP hw0
          have hexp_pos : 0 < expE (a : K) :=
            (S4ExpF.leE_zero_iff hK haddK hlenegK (expE (a : K))).mp (expE_pos_of_model hK a)
          have hwQpos : 0 < w ^ Q := zpow_pos hpos Q
          have hexNpos : 0 < (expE (a : K)) ^ N := zpow_pos hexp_pos N
          have hε_half : |ε| ≤ (2 : K)⁻¹ := by
            have h := hε 1
            rw [show (((1 : ℕ) : K) + 1) = 2 by norm_num] at h
            exact h
          have h2inv : (2 : K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by norm_num : (1 : K) < 2)
          have h1ε_pos : 0 < 1 + ε := by
            have hlow : -(2 : K)⁻¹ ≤ ε := (abs_le.mp hε_half).1
            linarith
          have hzpos : 0 < z := by
            have hprod : 0 < (z * (expE (a : K)) ^ N) * (1 + ε) := by rw [← hdec]; exact hwQpos
            have h1 : 0 < z * (expE (a : K)) ^ N := (mul_pos_iff_of_pos_right h1ε_pos).mp hprod
            exact (mul_pos_iff_of_pos_right hexNpos).mp h1
          have hz_memP : z ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            WilC2.subset_dcl_aux P (Or.inl hzA)
          have hwQ_memP : w ^ Q ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_zpow_mem P hwP (ne_of_gt hpos) Q
          have hexN_memP : (expE (a : K)) ^ N ∈
              @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_zpow_mem P (WilC2.subset_dcl_aux P (Or.inr rfl)) (ne_of_gt hexp_pos) N
          have hden_memP : z * (expE (a : K)) ^ N ∈
              @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_mul_mem P hz_memP hexN_memP
          have hden0 : z * (expE (a : K)) ^ N ≠ 0 :=
            mul_ne_zero hz0 (zpow_ne_zero N (ne_of_gt hexp_pos))
          have h1ε_memP : 1 + ε ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P := by
            have h : w ^ Q * (z * (expE (a : K)) ^ N)⁻¹ ∈
                @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
              S4ExpF.dcl_mul_mem P hwQ_memP (S4ExpF.dcl_inv_mem P hden_memP hden0)
            have heq : w ^ Q * (z * (expE (a : K)) ^ N)⁻¹ = 1 + ε := by
              rw [hdec, mul_comm (z * (expE (a : K)) ^ N) (1 + ε)]
              exact mul_inv_cancel_right₀ hden0 (1 + ε)
            rwa [heq] at h
          have hδ1 : absLeOne (mulE (addE oneE oneE) ε) := by
            have hmulE : mulE (addE oneE oneE) ε = (2 : K) * ε := by
              rw [haddK, honeK, hmulK]; norm_num
            rw [hmulE, S4ExpF.absLeOne_iff_abs hK haddK honeK hlenegK, abs_mul]
            have h2abs : |(2 : K)| = 2 := abs_of_pos (by norm_num : (0 : K) < 2)
            rw [h2abs]
            calc (2 : K) * |ε| ≤ (2 : K) * (2 : K)⁻¹ :=
                  mul_le_mul_of_nonneg_left hε_half (by norm_num)
              _ = 1 := by field_simp
          have hδmemP : addE oneE ε ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P := by
            rw [haddK, honeK]; exact h1ε_memP
          have hlog1ε_memP : logFun (1 + ε) ∈
              @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P := by
            have h := S4ExpF.logFun_one_add_mem_dcl (K := K) hK hrexpK haddK honeK P hδmemP hδ1
            rwa [haddK, honeK] at h
          have hlogz_memP : logFun z ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            WilC2.subset_dcl_aux P (Or.inl (hAlog z hzA))
          have hNa_memP : (N : K) * (a : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_mul_mem P (S4ExpF.dcl_intCast_mem P N)
              (WilC2.subset_dcl_aux P (Or.inl a.2))
          have hsum_memP : logFun z + (N : K) * (a : K) + logFun (1 + ε) ∈
              @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_add_mem P (S4ExpF.dcl_add_mem P hlogz_memP hNa_memP) hlog1ε_memP
          have hkey : (Q : K) * logFun w = logFun z + (N : K) * (a : K) + logFun (1 + ε) := by
            have h1 : logFun (w ^ Q) = (Q : K) * logFun w :=
              stepLogFun_zpow hK haddK hmulK honeK hlenegK hpos Q
            have h2 : logFun ((expE (a : K)) ^ N) = (N : K) * logFun (expE (a : K)) :=
              stepLogFun_zpow hK haddK hmulK honeK hlenegK hexp_pos N
            rw [← h1, hdec]
            rw [S4ExpF.logFun_mul_pos hK haddK hmulK hlenegK (mul_pos hzpos hexNpos) h1ε_pos]
            rw [S4ExpF.logFun_mul_pos hK haddK hmulK hlenegK hzpos hexNpos]
            rw [h2, logFun_expE hK a]
          have hQ0 : (Q : K) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hQ)
          have h : (Q : K)⁻¹ * (logFun z + (N : K) * (a : K) + logFun (1 + ε)) ∈
              @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) P :=
            S4ExpF.dcl_mul_mem P (S4ExpF.dcl_inv_mem P (S4ExpF.dcl_intCast_mem P Q) hQ0)
              hsum_memP
          have heq : (Q : K)⁻¹ * (logFun z + (N : K) * (a : K) + logFun (1 + ε)) = logFun w := by
            rw [← hkey, inv_mul_cancel_left₀ hQ0]
          rw [heq] at h
          rw [← hPdcl]; exact h
        · rw [S4ExpF.logFun_eq_zero_of_not_pos hK haddK honeK hlenegK w hpos]
          rw [← hPdcl]
          exact S4ExpF.dcl_zero_mem P
    exact h0
  ------------------------------------------------------------------------------------ #
  -- Stage 7: log-preservation of `σ'`                                                  #
  ------------------------------------------------------------------------------------ #
  have hlogpres : ∀ w : ↥S, σ' ⟨logFun (w : K), hlogcl (w : K) w.2⟩ = logFun (σ' w) :=
    S4ExpG.logPreserving_exp_aux hMCr hOM hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL honeL
      hlenegL A hAdcl hAlog B hBcoe hBlog aB hExpa hVA τ hτlog S hS hSdcl
      hlogcl hle hxS σ' hσ'B hσ'x
  ------------------------------------------------------------------------------------ #
  -- Stage 8: the extension pair `q`                                                    #
  ------------------------------------------------------------------------------------ #
  -- the domain of `q`, at the `rexp`-reduct
  let domR : @FirstOrder.Language.Substructure LRc K (reductStruct K) :=
    stepMkSub K (reductStruct K) (S : Set K) (fun {n} f x hx => by
      have h : @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f x ∈ (S : Set K) :=
        @FirstOrder.Language.Substructure.fun_mem LRc K (LR.withConstantsStructure ℝ) S n f x hx
      have h3 : @Structure.funMap LRc K (reductStruct K) n f x
          = @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f x :=
        congrArg (fun i => @Structure.funMap LRc K i n f x) hstructK
      rw [h3]; exact h)
  -- the embedding of `q`, at the `rexp`-reduct
  let embfun : ↥domR → L := @Function.Embedding.toFun ↥S L
    (@FirstOrder.Language.Embedding.toEmbedding LRc ↥S L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) S)
      (LR.withConstantsStructure ℝ) σ')
  have hembinj : Function.Injective embfun := @Function.Embedding.injective ↥S L
    (@FirstOrder.Language.Embedding.toEmbedding LRc ↥S L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) S)
      (LR.withConstantsStructure ℝ) σ')
  have hembmap : ∀ {n : ℕ} (f : LRc.Functions n) (y : Fin n → ↥domR),
      embfun (@Structure.funMap LRc ↥domR
          (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) domR) n f y)
        = @Structure.funMap LRc L (reductStruct L) n f (embfun ∘ y) := by
    intro n f y
    have hmap : ((@Structure.funMap LRc ↥domR
          (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) domR) n f y
            : ↥domR) : ↥S)
        = @Structure.funMap LRc ↥S
          (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) S)
          n f y :=
      Subtype.ext (by
        change @Structure.funMap LRc K (reductStruct K) n f (fun i => (y i : K))
          = @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f (fun i => (y i : K))
        exact (funMapK f (fun i => (y i : K))).symm)
    rw [hmap]
    rw [show embfun (@Structure.funMap LRc ↥S
            (@FirstOrder.Language.Substructure.inducedStructure LRc K
              (LR.withConstantsStructure ℝ) S) n f y)
          = @Function.Embedding.toFun ↥S L
            (@FirstOrder.Language.Embedding.toEmbedding LRc ↥S L
              (@FirstOrder.Language.Substructure.inducedStructure LRc K
                (LR.withConstantsStructure ℝ) S) (LR.withConstantsStructure ℝ) σ')
            (@Structure.funMap LRc ↥S
              (@FirstOrder.Language.Substructure.inducedStructure LRc K
                (LR.withConstantsStructure ℝ) S) n f y) from rfl]
    rw [@FirstOrder.Language.Embedding.map_fun' LRc ↥S L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) S)
      (LR.withConstantsStructure ℝ) σ' n f y]
    exact funMapL f (embfun ∘ y)
  let embR : @FirstOrder.Language.Embedding LRc ↥domR L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) domR)
      (reductStruct L) :=
    @Embedding.mk LRc ↥domR L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) domR)
      (reductStruct L) ⟨embfun, hembinj⟩ hembmap
      (by intro n R x; exact nomatch R)
  ------------------------------------------------------------------------------------ #
  -- Stage 9: assembling the pair                                                       #
  ------------------------------------------------------------------------------------ #
  have hlogclR : ∀ x ∈ (domR : Set K), logFun x ∈ (domR : Set K) := by
    intro x hx; exact hlogcl x hx
  have hdclR : @Work.WilC2.Dcl K (reductStruct K) (domR : Set K) ⊆ (domR : Set K) := by
    intro z hz
    have h1 : @Work.WilC2.Dcl K (reductStruct K) (S : Set K)
        = @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (S : Set K) :=
      congrArg (fun i => @Work.WilC2.Dcl K i (S : Set K)) hstructK
    rw [show (domR : Set K) = (S : Set K) from rfl] at hz
    rw [h1] at hz
    exact hSdcl hz
  have hlogpresR : ∀ w : ↥domR, embR ⟨logFun (w : K), hlogclR (w : K) w.2⟩ = logFun (embR w) := by
    intro w
    exact hlogpres ⟨(w : K), w.2⟩
  refine ⟨{ dom := domR
            emb := embR
            h4 := ⟨hdclR, hlogclR⟩
            logpres := hlogpresR
            le_dom := ?_
            agrees := ?_ }, ?_, ?_⟩
  · -- `A₀ ≤ domR`
    intro x hx
    exact hle (p.le_dom hx)
  · -- `embR` extends `σ₀`
    intro x
    have hx1 : (x : K) ∈ (B : Set K) := p.le_dom x.2
    have hx2 : (x : K) ∈ (S : Set K) := hle hx1
    have h1 : embR ⟨(x : K), hx2⟩ = σ' ⟨(x : K), hx2⟩ := rfl
    have h2 : σ' ⟨(x : K), hx2⟩ = τ ⟨(x : K), hx1⟩ := hσ'B ⟨(x : K), hx1⟩
    have h3 : τ ⟨(x : K), hx1⟩ = p.emb ⟨(x : K), p.le_dom x.2⟩ := rfl
    rw [h1, h2, h3]
    exact p.agrees x
  · -- `p ≤ q`
    refine ⟨?_, ?_⟩
    · -- `p.dom ≤ domR`
      intro x hx
      exact hle hx
    · -- the embeddings agree
      intro x
      have hx1 : (x : K) ∈ (B : Set K) := x.2
      have hx2 : (x : K) ∈ (S : Set K) := hle hx1
      have h1 : embR ⟨(x : K), hx2⟩ = σ' ⟨(x : K), hx2⟩ := rfl
      have h2 : σ' ⟨(x : K), hx2⟩ = τ ⟨(x : K), hx1⟩ := hσ'B ⟨(x : K), hx1⟩
      have h3 : τ ⟨(x : K), hx1⟩ = p.emb ⟨(x : K), x.2⟩ := rfl
      rw [h1, h2, h3]
  · -- the new element
    refine ⟨⟨expE (a : K), hxS⟩, rfl⟩

end Work.WilC5
