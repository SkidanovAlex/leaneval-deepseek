import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_defs
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.exists_bound_pdRList
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.poincare_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

theorem commutator_estimate {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d)) (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (lam : ℝ) (hlam : 0 < lam)
    (K : ℝ) (hK : ∀ c d (l : Fin k → ι) x, |Work.Diff.STE.pdRVec k l (A c d) x| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u → Work.Diff.STE.Periodic1 u →
      |∑ l : Fin k → ι,
        Work.Diff.STE.L2re
          (fun x => Work.Diff.STE.pdVec k l
              (fun y => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x
            - ∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
          (Work.Diff.STE.pdVec k l u)|
        ≤ (lam / 4) * Work.Diff.STE.ENormSq (k + 1) u + C * Work.Diff.STE.ENormSq k u := by
  classical
  -- ## Step 0: a uniform bound on all iterated derivatives of the coefficients
  have hstep : ∀ c d : ι, ∃ Mb : ℝ, 0 ≤ Mb ∧
      ∀ q : List ι, q.length ≤ k → ∀ x, |pdRList q (A c d) x| ≤ Mb :=
    fun c d => cm_exists_bound_pdRList k (A c d) (hA c d) (hAper c d)
  choose Mb hMb0 hMbb using hstep
  set M : ℝ := ∑ c : ι, ∑ d : ι, Mb c d with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hMb0 c d
  have hMb : ∀ c d (q : List ι), q.length ≤ k → ∀ x, |pdRList q (A c d) x| ≤ M := by
    intro c d q hq x
    have h1 : Mb c d ≤ ∑ d' : ι, Mb c d' :=
      Finset.single_le_sum (fun d' _ => hMb0 c d') (Finset.mem_univ d)
    have h2 : (∑ d' : ι, Mb c d') ≤ ∑ c' : ι, ∑ d' : ι, Mb c' d' :=
      Finset.single_le_sum (fun c' _ => Finset.sum_nonneg fun d' _ => hMb0 c' d')
        (Finset.mem_univ c)
    exact le_trans (hMbb c d q hq x) (le_trans h1 h2)
  -- ## Step 1: the Poincaré constant
  obtain ⟨C0, hC00, hPoinc0⟩ := poincare_cube (ι := ι)
  set CP : ℝ := max 1 (C0 * ((Fintype.card ι : ℝ) + 1) ^ (k + 1)) with hCPdef
  have hCP1 : 1 ≤ CP := by rw [hCPdef]; exact le_max_left _ _
  have hCP0 : 0 ≤ CP := le_trans zero_le_one hCP1
  have hCPC : C0 * ((Fintype.card ι : ℝ) + 1) ^ (k + 1) ≤ CP := by
    rw [hCPdef]; exact le_max_right _ _
  have hC0CP : C0 ≤ CP := by
    have h1 : (1 : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) ^ (k + 1) :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι); linarith)
    exact le_trans (le_mul_of_one_le_right hC00 h1) hCPC
  have hPoinc : ∀ f : (ι → ℝ) → ℂ, ContDiff ℝ 1 f → Periodic1 f →
      (∫ x in unitCube, f x = 0) →
      ∫ x in unitCube, ‖f x‖ ^ 2 ≤ CP * ∑ i, ∫ x in unitCube, ‖pd i f x‖ ^ 2 := by
    intro f hf hper hmean
    exact le_trans (hPoinc0 f hf hper hmean)
      (mul_le_mul_of_nonneg_right hC0CP
        (Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _))
  -- ## Step 2: numerical constants
  set N : ℝ := (Fintype.card ι : ℝ) ^ k * (Fintype.card ι : ℝ) ^ 2 * 2 ^ k with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  set Bc : ℝ := (N + 1) * (M + 1) * (CP ^ (k + 1) + 1) with hBcdef
  have hBc0 : 0 < Bc := by rw [hBcdef]; positivity
  set eta : ℝ := (lam / 4) / Bc with hetadef
  have heta0 : 0 < eta := by rw [hetadef]; positivity
  have hetaB : eta * Bc = lam / 4 := by
    rw [hetadef]; field_simp
  refine ⟨Bc ^ 2 / lam, by positivity, ?_⟩
  intro u hu hup
  have hu' : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u := by simpa using hu
  have huL : ∀ {q : List ι}, q.length ≤ k → ContDiff ℝ ((q.length : ℕ) : WithTop ℕ∞) u :=
    fun {q} hq => cm_of_le hu' (by omega)
  -- Poincaré comparison along the `ENormSq` scale
  have hEN : ∀ j : ℕ, 1 ≤ j → j ≤ k → ENormSq j u ≤ CP * ENormSq (j + 1) u := by
    intro j hj hjk
    refine le_trans (cm_ENormSq_step C0 hC00 hPoinc0 k j hj hjk u (cm_of_le hu' (by omega)) hup) ?_
    exact mul_le_mul_of_nonneg_right hCPC (cm_ENormSq_nonneg _ _)
  -- ## Step 3: decomposition of each summand
  have hsplit : ∀ l : Fin k → ι,
      L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
          - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)
        = ∑ p : ι × ι,
            L2re (fun x => pdList (List.ofFn l)
                (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
              - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l)
                (fun z => pd p.1 (pd p.2 u) z) x) (pdVec k l u) := by
    intro l
    have h1x : ∀ x : ι → ℝ, pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
        = ∑ p : ι × ι, pdList (List.ofFn l)
            (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x := by
      intro x
      rw [pdVec]
      have hfun : (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y)
          = fun y => ∑ p : ι × ι, (A p.1 p.2 y : ℂ) * pd p.1 (pd p.2 u) y := by
        funext y
        rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [hfun]
      have hsum : pdList (List.ofFn l)
            (fun y => ∑ p : ι × ι, (A p.1 p.2 y : ℂ) * pd p.1 (pd p.2 u) y)
          = fun y => ∑ p : ι × ι, pdList (List.ofFn l)
              (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) y :=
        cm_pdList_sum (List.ofFn l) Finset.univ
          (fun p : ι × ι => fun y => (A p.1 p.2 y : ℂ) * pd p.1 (pd p.2 u) y)
          (fun p _ q hq hlen => by
            have hlen' : q.length < k := by
              have h := List.Sublist.length_le hq
              have hof : (List.ofFn l).length = k := List.length_ofFn
              omega
            exact cm_diff_pdList_mul k A u hA hu' p hlen')
      exact congrFun hsum x
    have h2x : ∀ x : ι → ℝ, (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
        = ∑ p : ι × ι, (A p.1 p.2 x : ℂ) * pdList (List.ofFn l)
            (fun z => pd p.1 (pd p.2 u) z) x := by
      intro x
      rw [← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
      rw [← cm_pdVec_pd_pd k l c d u hu']
      rfl
    have h3 : (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
          - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
        = fun x => ∑ p : ι × ι,
            (pdList (List.ofFn l) (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
              - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l)
                  (fun z => pd p.1 (pd p.2 u) z) x) := by
      funext x
      rw [h1x x, h2x x]
      exact (Finset.sum_sub_distrib _ _).symm
    rw [h3]
    refine cm_L2re_sum Finset.univ
      (fun (p : ι × ι) (x : ι → ℝ) => pdList (List.ofFn l)
          (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
        - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l) (fun z => pd p.1 (pd p.2 u) z) x)
      (pdVec k l u) (fun (p : ι × ι) _ => ?_) ?_
    · exact (cm_cont_pdList_mul k A u hA hu' p (q := List.ofFn l) (by simp)).sub
        ((Complex.ofRealCLM.continuous.comp (hA p.1 p.2).continuous).mul
          (cm_cont_pdList_pair (k := k) (u := u) hu' p.1 p.2 (q := List.ofFn l) (by simp)))
    · exact (cm_contDiff_pdList (List.ofFn l) 0 u (cm_of_le hu' (by
        have hof : (List.ofFn l).length = k := List.length_ofFn
        omega))).continuous
  -- ## Step 4: the per-(l,c,d) bound
  have hper : ∀ (l : Fin k → ι) (p : ι × ι),
      |L2re (fun x => pdList (List.ofFn l)
            (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
          - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l) (fun z => pd p.1 (pd p.2 u) z) x)
          (pdVec k l u)|
        ≤ 2 ^ k * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
            + (M / (4 * eta)) * ENormSq k u) := by
    intro l p
    have hF : ∀ q : List ι, List.Sublist q (List.ofFn l) → q.length < (List.ofFn l).length →
        Differentiable ℝ (pdList q (fun z => (A p.1 p.2 z : ℂ))) :=
      fun q _ _ => cm_diff_pdList_ofReal (A p.1 p.2) (hA p.1 p.2) q
    have hg : ∀ q : List ι, List.Sublist q (List.ofFn l) → q.length < (List.ofFn l).length →
        Differentiable ℝ (pdList q (fun z => pd p.1 (pd p.2 u) z)) := by
      intro q hq hlen
      have hlen' : q.length < k := by
        have h := List.Sublist.length_le hq
        have hof : (List.ofFn l).length = k := List.length_ofFn
        omega
      exact cm_diff_pdList_pair (k := k) (u := u) hu' p.1 p.2 hlen'
    have hleib := pdList_mul_sub (List.ofFn l) (fun z => (A p.1 p.2 z : ℂ))
      (fun z => pd p.1 (pd p.2 u) z) hF hg
    have hcontF : ∀ q : List ι, q.length ≤ (List.ofFn l).length →
        Continuous (pdList q (fun z => (A p.1 p.2 z : ℂ))) :=
      fun q _ => cm_cont_pdList_ofReal (A p.1 p.2) (hA p.1 p.2) q
    have hcontg : ∀ q : List ι, q.length ≤ (List.ofFn l).length →
        Continuous (pdList q (fun z => pd p.1 (pd p.2 u) z)) := by
      intro q hq
      exact cm_cont_pdList_pair (k := k) (u := u) hu' p.1 p.2 (q := q) (by simpa using hq)
    have hconth : Continuous (pdVec k l u) :=
      (cm_contDiff_pdList (List.ofFn l) 0 u (cm_of_le hu' (by
        have hof : (List.ofFn l).length = k := List.length_ofFn
        omega))).continuous
    have hFb : ∀ q : List ι, q.length ≤ (List.ofFn l).length → ∀ x,
        ‖pdList q (fun z => (A p.1 p.2 z : ℂ)) x‖ ≤ M := by
      intro q hq x
      exact cm_norm_pdList_ofReal_le (A p.1 p.2) (hA p.1 p.2) q M
        (fun y => hMb p.1 p.2 q (by simpa using hq) y) x
    have hAen : ∀ q : List ι, q.length < (List.ofFn l).length →
        ∫ x in unitCube, ‖pdList q (fun z => pd p.1 (pd p.2 u) z) x‖ ^ 2
          ≤ CP ^ (k + 1) * ENormSq (k + 1) u := by
      intro q hq
      have hqk : q.length < k := by
        have h := hq
        have hof : (List.ofFn l).length = k := List.length_ofFn
        omega
      rw [cm_pdList_pair q p.1 p.2 u]
      have h1 : ∫ x in unitCube, ‖pdList (q ++ [p.1, p.2]) u x‖ ^ 2
          ≤ ENormSq (q.length + 2) u := by
        refine le_trans (cm_integral_pdList_le_ENormSq (q ++ [p.1, p.2]) u) ?_
        simp [List.length_append]
      have h2 : ENormSq (q.length + 2) u
          ≤ CP ^ ((k + 1) - (q.length + 2)) * ENormSq (k + 1) u :=
        cm_ENormSq_le_pow CP hCP0 k u hEN (q.length + 2) (k + 1) (by omega) (by omega) (by omega)
      have h3 : CP ^ ((k + 1) - (q.length + 2)) ≤ CP ^ (k + 1) :=
        pow_le_pow_right₀ hCP1 (by omega)
      calc ∫ x in unitCube, ‖pdList (q ++ [p.1, p.2]) u x‖ ^ 2
          ≤ ENormSq (q.length + 2) u := h1
        _ ≤ CP ^ ((k + 1) - (q.length + 2)) * ENormSq (k + 1) u := h2
        _ ≤ CP ^ (k + 1) * ENormSq (k + 1) u :=
            mul_le_mul_of_nonneg_right h3 (cm_ENormSq_nonneg _ _)
    have hAen2 : ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2 ≤ ENormSq k u := by
      refine le_trans (cm_integral_pdList_le_ENormSq (List.ofFn l) u) ?_
      simp
    have hres := cm_comm_bound M eta (CP ^ (k + 1) * ENormSq (k + 1) u) (ENormSq k u)
      hM0 heta0 (mul_nonneg (pow_nonneg hCP0 _) (cm_ENormSq_nonneg _ _))
      (cm_ENormSq_nonneg _ _) (List.ofFn l)
      (fun z => (A p.1 p.2 z : ℂ)) (fun z => pd p.1 (pd p.2 u) z) (pdVec k l u)
      hleib hcontF hcontg hconth hFb hAen hAen2
    have hlen : ((splits (List.ofFn l)).length : ℝ) = 2 ^ k := by
      rw [cm_splits_length_count, List.length_ofFn]
      norm_num
    rwa [hlen] at hres
  -- ## Step 5: sum over `l` and `(c,d)`
  have hmain1 : |∑ l : Fin k → ι,
        L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
            - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)|
      ≤ ∑ l : Fin k → ι, ∑ p : ι × ι, |L2re (fun x => pdList (List.ofFn l)
            (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
          - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l)
            (fun z => pd p.1 (pd p.2 u) z) x) (pdVec k l u)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun l _ => ?_)
    rw [hsplit l]
    exact Finset.abs_sum_le_sum_abs _ _
  have hmain2 : ∑ l : Fin k → ι, ∑ p : ι × ι, |L2re (fun x => pdList (List.ofFn l)
          (fun z => (A p.1 p.2 z : ℂ) * pd p.1 (pd p.2 u) z) x
        - (A p.1 p.2 x : ℂ) * pdList (List.ofFn l)
          (fun z => pd p.1 (pd p.2 u) z) x) (pdVec k l u)|
      ≤ ∑ _l : Fin k → ι, ∑ _p : ι × ι, 2 ^ k * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
          + (M / (4 * eta)) * ENormSq k u) :=
    Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun p _ => hper l p))
  have hmain3 : ∑ _l : Fin k → ι, ∑ _p : ι × ι, 2 ^ k * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
        + (M / (4 * eta)) * ENormSq k u)
      = N * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
          + (M / (4 * eta)) * ENormSq k u) := by
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      Finset.card_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
    rw [hNdef]
    push_cast
    ring
  -- ## Step 6: the arithmetic
  have hNM : N * M * CP ^ (k + 1) ≤ Bc := by
    have h1 : N ≤ N + 1 := by linarith
    have h2 : M ≤ M + 1 := by linarith
    have h3 : CP ^ (k + 1) ≤ CP ^ (k + 1) + 1 := by linarith
    have h4 : (0 : ℝ) ≤ N := hN0
    have h5 : (0 : ℝ) ≤ M := hM0
    have h6 : (0 : ℝ) ≤ CP ^ (k + 1) := by positivity
    calc N * M * CP ^ (k + 1) ≤ (N + 1) * (M + 1) * (CP ^ (k + 1) + 1) := by
          nlinarith [mul_nonneg h4 h5, h1, h2, h3, h6]
      _ = Bc := by rw [hBcdef]
  have hNM2 : N * M ≤ Bc := by
    have h6 : (0 : ℝ) ≤ CP ^ (k + 1) := by positivity
    have h1 : N ≤ N + 1 := by linarith
    have h2 : M ≤ M + 1 := by linarith
    calc N * M ≤ (N + 1) * (M + 1) := by nlinarith [hN0, hM0, h1, h2]
      _ ≤ (N + 1) * (M + 1) * (CP ^ (k + 1) + 1) := by
          have : (1 : ℝ) ≤ CP ^ (k + 1) + 1 := by linarith
          exact le_mul_of_one_le_right (by positivity) this
      _ = Bc := by rw [hBcdef]
  have harm : N * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
        + (M / (4 * eta)) * ENormSq k u)
      ≤ (lam / 4) * ENormSq (k + 1) u + (Bc ^ 2 / lam) * ENormSq k u := by
    have hE1 : (0 : ℝ) ≤ ENormSq (k + 1) u := cm_ENormSq_nonneg _ _
    have hE0 : (0 : ℝ) ≤ ENormSq k u := cm_ENormSq_nonneg _ _
    have h1 : N * M * CP ^ (k + 1) * eta ≤ lam / 4 := by
      rw [← hetaB, mul_comm eta Bc]
      exact mul_le_mul_of_nonneg_right hNM (le_of_lt heta0)
    have h2 : N * M / (4 * eta) ≤ Bc ^ 2 / lam := by
      have hkey : N * M / (4 * eta) = N * M * Bc / lam := by
        rw [hetadef]
        field_simp
      rw [hkey]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hlam)
      nlinarith [hNM2, hBc0]
    calc N * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
          + (M / (4 * eta)) * ENormSq k u)
        = (N * M * CP ^ (k + 1) * eta) * ENormSq (k + 1) u
          + (N * M / (4 * eta)) * ENormSq k u := by ring
      _ ≤ (lam / 4) * ENormSq (k + 1) u + (Bc ^ 2 / lam) * ENormSq k u :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hE1) (mul_le_mul_of_nonneg_right h2 hE0)
  calc |∑ l : Fin k → ι,
        L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
            - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)|
      ≤ N * (M * eta * (CP ^ (k + 1) * ENormSq (k + 1) u)
          + (M / (4 * eta)) * ENormSq k u) :=
        le_trans hmain1 (le_trans hmain2 (le_of_eq hmain3))
    _ ≤ (lam / 4) * ENormSq (k + 1) u + (Bc ^ 2 / lam) * ENormSq k u := harm

end Work.Diff.STE
