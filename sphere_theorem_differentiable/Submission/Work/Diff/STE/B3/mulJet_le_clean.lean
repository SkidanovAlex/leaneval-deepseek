import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `mulJet_le_clean`: the Leibniz `L²` estimate for a cut-off, axiom-clean

A self-contained, sorry-free proof of the estimate used in the short-time-existence assembly:
the `L²` norm of the top jet `∂^β (φ · W)` is bounded by `4^m Kφ²` times the sum of the `L²`
norms of all the jets of `W` of order `≤ m`.

The proof is the iterated Leibniz rule `Work.Diff.STE.pdList_mul_sub` (in the "all splits" form,
`2^m` terms) combined with Cauchy--Schwarz: every split contributes at most
`Kφ · ‖∂^{p.2} W‖`, and the sum of these over the splits is at most `2^m` times the square root of
the sum of the squares.  The result is then integrated over the unit cube.

All helper lemmas are `private` so that the module can be imported alongside
`Submission.Work.Diff.STE.B3.mat_ENormSq_le` (which contains an identically named proof).
-/

noncomputable section

open MeasureTheory BigOperators

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.B3

/-- Lowering a smoothness level from `∞` to a finite one. -/
private lemma contDiff_level_le (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤)

/-- `pdVec` of a globally smooth function is continuous, at any order. -/
private lemma continuous_pdVec_of_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.continuous_pdVec m l f (hf.of_le (contDiff_level_le m))
/-! ## 5b. A sharp Leibniz bound for the jet of a product with a cut-off

This is a self-contained replacement for `Work.Diff.STE.B3.mulJet_le`, with the *sharp* constant
`Kφ` (no `+ 1`), which is what the assembly below needs.  The proof uses the iterated Leibniz rule
`Work.Diff.STE.pdList_mul_sub` (in the "all splits" form) and Cauchy--Schwarz on the at most
`2 ^ m` splits. -/

/-- A list sum of terms bounded by `c` is at most `length * c`. -/
private lemma list_sum_le_card_mul_b3 {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ L, f a ≤ c) : (L.map f).sum ≤ (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ c := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ c := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- A list sum of pointwise bounded terms is bounded termwise. -/
private lemma list_sum_le_sum_b3 {α : Type*} (L : List α) {f g : α → ℝ}
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ g a := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ g b := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- Factoring a constant out of a list sum. -/
private lemma list_sum_map_mul_left_b3 {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- The norm of a list sum is at most the sum of the norms. -/
private lemma norm_list_sum_le_b3 {α : Type*} (L : List α) (f : α → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map (fun a => ‖f a‖)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The norm of a complexified real is its absolute value. -/
private lemma norm_ofReal_eq_abs_b3 (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  exact Real.sqrt_mul_self_eq_abs x

/-- **One-step complexification.**  `∂ᵢ` commutes with the embedding `ℝ → ℂ` (no differentiability
hypothesis: both sides are junk-free, and vanish where the function is not differentiable). -/
private lemma pd_ofReal_b3 {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd i (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdR i g x : ℝ) : ℂ) := by
  funext x
  show (fderiv ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x) (Pi.single i 1)
    = ((fderiv ℝ g x) (Pi.single i 1) : ℂ)
  have hcomp : (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g := by
    funext y; exact (Complex.ofRealCLM_apply (g y)).symm
  by_cases hg : DifferentiableAt ℝ g x
  · rw [hcomp]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x hg.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · have hg' : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x := by
      intro h
      refine hg ?_
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
    simp

/-- Complexification commutes with the iterated partial derivative `pdList`. -/
private lemma pdList_ofReal_b3 {n : ℕ} (l : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdList l (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRList l f x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      show Work.Diff.STE.pd i (Work.Diff.STE.pdList rest (fun y => ((f y : ℝ) : ℂ)))
        = fun x => ((Work.Diff.STE.pdR i (Work.Diff.STE.pdRList rest f) x : ℝ) : ℂ)
      rw [ih]
      exact pd_ofReal_b3 i (Work.Diff.STE.pdRList rest f)

/-- `pdRList` of a list is `pdRVec` of the corresponding tuple. -/
private lemma pdRList_eq_pdRVec_b3 {n : ℕ} (q : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdRList q f
      = Work.Diff.STE.pdRVec q.length (fun i : Fin q.length => q.get i) f := by
  rw [Work.Diff.STE.pdRVec]
  congr 1
  exact (List.ofFn_get q).symm

/-- The `pdList` of the complexified cut-off is bounded by `Kφ`. -/
private lemma pdList_ofReal_norm_le_b3 {n m : ℕ} {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ}
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    {q : List (Fin n)} (hq : q.length ≤ m) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdList q (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Kφ := by
  rw [pdList_ofReal_b3]
  show ‖((Work.Diff.STE.pdRList q φ z : ℝ) : ℂ)‖ ≤ Kφ
  rw [norm_ofReal_eq_abs_b3]
  rw [pdRList_eq_pdRVec_b3 q φ]
  exact hφb q.length hq (fun i => q.get i) z

/-- **The iterated Leibniz rule in "all splits" form**: the `l`-th iterated partial derivative of
a product is the sum of the products `∂^{p.1}F · ∂^{p.2}G` over *all* complementary splits
`p ∈ splits l` (the split `([], l)`, in which no derivative hits `F`, is included). -/
private lemma pdList_mul_unfiltered_b3 {n : ℕ} (l : List (Fin n)) (F g : (Fin n → ℝ) → ℂ)
    (hF : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F))
    (hG : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q g))
    (y : Fin n → ℝ) :
    Work.Diff.STE.pdList l (fun z => F z * g z) y
      = ((Work.Diff.STE.splits l).map
          (fun p => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y)).sum := by
  classical
  set ψ : List (Fin n) × List (Fin n) → ℂ :=
    fun p => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y with hψ
  have h := congrFun (Work.Diff.STE.pdList_mul_sub l F g hF hG) y
  have hfilter : ((Work.Diff.STE.splitsNE l).map ψ).sum
      = ((((Work.Diff.STE.splits l).filter (fun p => decide (p.1 ≠ []))).map ψ)).sum := by
    rw [Work.Diff.STE.splitsNE_eq_filter]
  have hnil : ψ ([], l) = F y * Work.Diff.STE.pdList l g y := rfl
  have hsum := Work.Diff.STE.splitsNE_sum_add l ψ
  calc Work.Diff.STE.pdList l (fun z => F z * g z) y
      = (Work.Diff.STE.pdList l (fun z => F z * g z) y - F y * Work.Diff.STE.pdList l g y)
          + F y * Work.Diff.STE.pdList l g y := by ring
    _ = ((((Work.Diff.STE.splits l).filter (fun p => decide (p.1 ≠ []))).map ψ)).sum + ψ ([], l) := by
        rw [h, hnil]
    _ = ((Work.Diff.STE.splitsNE l).map ψ).sum + ψ ([], l) := by rw [hfilter]
    _ = ((Work.Diff.STE.splits l).map ψ).sum := hsum

/-- Continuity of the squared norm of an iterated partial derivative. -/
private lemma continuous_normSq_pdVec_b3 {n : ℕ} {W : (Fin n → ℝ) → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (j : ℕ) (γ : Fin j → Fin n) :
    Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2) := by
  have h := (continuous_pdVec_of_smooth hW j γ).norm
  convert h.mul h using 1
  ext z
  simp only [Pi.mul_apply, pow_two]

/-- **Sharp Leibniz bound.**  `∃C, ∫ ‖∂^β(φ · W)‖² ≤ C Kφ² Σ_{j ≤ m} Σ_γ ∫ ‖∂^γ W‖²`. -/
theorem mulJet_le_clean (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) W →
      (∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
        |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ) →
      ∀ (β : Fin m → Fin n),
        ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m β
            (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
          ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  classical
  refine ⟨(4 : ℝ) ^ m, by positivity, ?_⟩
  intro φ W Kφ hφ hW hφb β
  set F : (Fin n → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hF
  set l : List (Fin n) := List.ofFn β with hl
  have hl_len : l.length = m := by rw [hl]; exact List.length_ofFn
  set S : List (List (Fin n) × List (Fin n)) := Work.Diff.STE.splits l with hS
  have hS_len : (S.length : ℝ) = (2 : ℝ) ^ m := by
    rw [hS, Work.Diff.STE.cm_splits_length_count, hl_len]
    push_cast
    ring
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1),
    ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 with hB
  have hSsq : (S.length : ℝ) ^ 2 = (4 : ℝ) ^ m := by
    rw [hS_len]
    calc ((2 : ℝ) ^ m) ^ 2 = 2 ^ (m * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num
  have hBnn : ∀ z : Fin n → ℝ, 0 ≤ B z := by
    intro z
    rw [hB]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  -- differentiability hypotheses for the Leibniz rule
  have hFdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F) := by
    intro q _ _
    rw [hF]
    exact Work.Diff.STE.cm_diff_pdList_ofReal φ hφ q
  have hWdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q W) := by
    intro q _ _
    refine (Work.Diff.STE.cm_contDiff_pdList q 1 W ?_).differentiable (by norm_num)
    exact hW.of_le (contDiff_level_le (q.length + 1))
  -- every split contributes at most `Kφ * ‖∂^{p.2}W‖`
  have hterm : ∀ (z : Fin n → ℝ) (p : List (Fin n) × List (Fin n)), p ∈ S →
      ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖
        ≤ Kφ * ‖Work.Diff.STE.pdList p.2 W z‖ := by
    intro z p hp
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
    have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
    have hlen' : p.1.length ≤ m := by rw [hl_len] at hlen; omega
    exact pdList_ofReal_norm_le_b3 hφb hlen' z
  -- the pointwise bound
  have hpt : ∀ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
      ≤ (4 : ℝ) ^ m * Kφ ^ 2 * B z := by
    intro z
    have hpd : Work.Diff.STE.pdVec m β (fun z => F z * W z)
        = Work.Diff.STE.pdList l (fun z => F z * W z) := by rw [hl]; rfl
    have h1 : ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖
        ≤ Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum := by
      rw [pdList_mul_unfiltered_b3 l F W hFdiff hWdiff z]
      calc ‖(S.map (fun p => Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z)).sum‖
          ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖)).sum :=
            norm_list_sum_le_b3 S _
        _ ≤ (S.map (fun p => Kφ * ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
            list_sum_le_sum_b3 S (fun p hp => hterm z p hp)
        _ = Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
            list_sum_map_mul_left_b3 S Kφ _
    have h2 : (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum
        ≤ (S.length : ℝ) * Real.sqrt (B z) := by
      refine list_sum_le_card_mul_b3 S (fun p => ‖Work.Diff.STE.pdList p.2 W z‖) (Real.sqrt (B z)) ?_
      intro p hp
      refine Real.le_sqrt_of_sq_le ?_
      have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
      have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
      have hlen' : p.2.length ≤ m := by rw [hl_len] at hlen; omega
      have hpd' : Work.Diff.STE.pdList p.2 W
          = Work.Diff.STE.pdVec p.2.length (fun i : Fin p.2.length => p.2.get i) W := by
        rw [Work.Diff.STE.pdVec]
        congr 1
        exact (List.ofFn_get p.2).symm
      rw [hpd']
      refine (Finset.single_le_sum
        (f := fun γ : Fin p.2.length → Fin n => ‖Work.Diff.STE.pdVec p.2.length γ W z‖ ^ 2)
        (fun γ _ => sq_nonneg _) (Finset.mem_univ (fun i => p.2.get i))).trans ?_
      rw [hB]
      exact Finset.single_le_sum
        (f := fun j => ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2)
        (fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen'))
    have h3 : 0 ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
      List.sum_nonneg fun a ha => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact norm_nonneg _
    calc ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
        = ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖ ^ 2 := by rw [hpd]
      _ ≤ (Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = Kφ ^ 2 * ((S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 := by ring
      _ ≤ Kφ ^ 2 * ((S.length : ℝ) * Real.sqrt (B z)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2) (sq_nonneg Kφ)
      _ = Kφ ^ 2 * (S.length : ℝ) ^ 2 * B z := by
          rw [mul_pow, Real.sq_sqrt (hBnn z)]
          ring
      _ = (4 : ℝ) ^ m * Kφ ^ 2 * B z := by
          rw [hSsq]
          ring
  -- integration
  have hcontL : Continuous (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2) := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => F z * W z) := by
      rw [hF]
      exact (Complex.ofRealCLM.contDiff.comp hφ).mul hW
    have h := (continuous_pdVec_of_smooth hsm m β).norm
    have h2 := h.mul h
    convert h2 using 1
    ext z
    simp only [Pi.mul_apply, pow_two]
  have hcontB : Continuous B := by
    rw [hB]
    refine continuous_finset_sum (Finset.range (m + 1)) (fun j _ => ?_)
    exact continuous_finset_sum (Finset.univ : Finset (Fin j → Fin n))
      (fun γ _ => continuous_normSq_pdVec_b3 hW j γ)
  have hcontR : Continuous (fun z : Fin n → ℝ => (4 : ℝ) ^ m * Kφ ^ 2 * B z) :=
    hcontB.const_mul ((4 : ℝ) ^ m * Kφ ^ 2)
  have hint1 : ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
      ≤ ∫ z in Work.Diff.STE.unitCube, (4 : ℝ) ^ m * Kφ ^ 2 * B z :=
    setIntegral_mono_on
      (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcontL)
      (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcontR)
      Work.Diff.STE.BesselCont.measSet_unitCube (fun z _ => hpt z)
  have hint2 : ∫ z in Work.Diff.STE.unitCube, (4 : ℝ) ^ m * Kφ ^ 2 * B z
      = (4 : ℝ) ^ m * Kφ ^ 2 * ∫ z in Work.Diff.STE.unitCube, B z := by
    rw [integral_const_mul]
  have hint3 : ∫ z in Work.Diff.STE.unitCube, B z
      = ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
    rw [hB]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finset_sum]
      intro γ _
      exact Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
        (continuous_normSq_pdVec_b3 hW j γ)
    · intro j _
      exact integrable_finset_sum _ fun γ _ =>
        Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
          (continuous_normSq_pdVec_b3 hW j γ)
  refine hint1.trans ?_
  rw [hint2, hint3]
end Work.Diff.STE.B3
