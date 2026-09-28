import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.box_card
import Submission.Work.HP.Q44Child.CountDefs
import Submission.Work.Q44Child.roots_card_le

/-!
# The quartic zero bound (`Work.HP.Q44Child.quartic_zero_bound`)

A nonzero quartic form `f_a` in `5` variables has `O(T^4)` integral zeros of Euclidean
norm at most `T`.  This is proved here by an induction on the number of variables.

For a polynomial `f` in `s+1` variables we use `MvPolynomial.finSuccEquiv` to view it as a
univariate polynomial `p` over `MvPolynomial (Fin s) ℤ`: over each point `u ∈ ℤ^s` the fibre
`z ↦ f(z,u)` is `Polynomial.eval z (Polynomial.map (MvPolynomial.eval u) p)`.  Hence the box
points of `ℤ^{s+1}` on which `f` vanishes split into

* the fibres where `p` does not vanish identically: each contributes at most `4` points,
  since the fibre polynomial is nonzero of degree `≤ 4`;
* the fibres where `p` vanishes identically: the set of such `u` is contained in the zero set
  of any one nonzero coefficient of `p`, which is a polynomial in `s` variables of degree
  `≤ 4` — this is exactly the induction hypothesis.

Counting gives the recursion `C_{s+1} = 4·2^s + 2·C_s`, which is finite.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Work.HP.Q44Child

open MvPolynomial

/-! ## Elementary facts about the box -/

theorem mem_cbox {s M : ℕ} {x : Fin s → ℤ} :
    x ∈ cbox s M ↔ ∀ i, -(M : ℤ) ≤ x i ∧ x i ≤ (M : ℤ) := by
  simp [cbox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem tail_mem_cbox {s M : ℕ} {x : Fin (s + 1) → ℤ} (h : x ∈ cbox (s + 1) M) :
    Fin.tail x ∈ cbox s M := by
  rw [mem_cbox] at h ⊢
  intro i
  exact h i.succ

theorem cbox_card (s M : ℕ) : ((cbox s M).card : ℝ) = (2 * (M : ℝ) + 1) ^ s := by
  have h := (Work.HP.box_card (ι := Fin s) M).1
  simpa [cbox, Fintype.card_fin] using h

/-! ## The coefficient vector as a polynomial over `ℤ` -/

theorem coeff_formZ {d n : ℕ} (a : Mon d n → ℤ) (m : Mon d n) :
    (formZ a).coeff m.toFinsupp = a m := by
  simp only [formZ, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    rw [if_neg]
    intro hc
    exact hm' (Work.HP.Mon_toFinsupp_injective hc)
  · intro h; exact absurd (Finset.mem_univ m) h

theorem eval_formZ {d n : ℕ} (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    MvPolynomial.eval x (formZ a) = Work.HP.formEval d n a x := by
  simp only [formZ, Work.HP.formEval, Work.HP.veronese, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.eval_monomial]
  have key : (m.toFinsupp.prod fun i e => x i ^ e) = ∏ i, x i ^ (m.1 i : ℕ) := by
    rw [Finsupp.prod]
    refine (Finset.prod_subset (Finset.subset_univ _) ?_).trans (Finset.prod_congr rfl ?_)
    · intro i _ hi
      rw [Finsupp.notMem_support_iff.1 hi]
      simp
    · intro i _
      rw [Work.HP.Mon_toFinsupp_apply]
  rw [key]
  simp only [Int.cast_id]

theorem formZ_basic {d n : ℕ} (a : Mon d n → ℤ) :
    (formZ a = 0 ↔ a = 0) ∧ (formZ a).totalDegree ≤ d := by
  constructor
  · refine ⟨fun h => ?_, fun h => by simp [h, formZ]⟩
    funext m
    have hc := congrArg (fun p : MvPolynomial (Fin (n + 1)) ℤ => p.coeff m.toFinsupp) h
    simpa [coeff_formZ] using hc
  · have hsum : ∀ m : Mon d n, (m.toFinsupp.sum fun _ e => e) = d := by
      intro m
      rw [Finsupp.sum_fintype _ _ (fun i => rfl)]
      simpa [Work.HP.Mon_toFinsupp_apply] using m.2
    have hdeg : ∀ m ∈ (Finset.univ : Finset (Mon d n)),
        (MvPolynomial.monomial m.toFinsupp (a m)).totalDegree ≤ d := by
      intro m _
      by_cases h0 : a m = 0
      · rw [h0, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]; omega
      · rw [MvPolynomial.totalDegree_monomial m.toFinsupp h0]
        exact le_of_eq (hsum m)
    simpa [formZ] using MvPolynomial.totalDegree_finsetSum_le hdeg

/-! ## The univariate fibre: vanishing coefficients -/

theorem coeff_bad_subset (s M k : ℕ) (p : Polynomial (MvPolynomial (Fin s) ℤ)) :
    (cbox s M).filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0) ⊆
      (cbox s M).filter (fun u => MvPolynomial.eval u (p.coeff k) = 0) := by
  intro u hu
  rw [Finset.mem_filter] at hu ⊢
  refine ⟨hu.1, ?_⟩
  have h := congrArg (fun q : Polynomial ℤ => q.coeff k) hu.2
  simpa [MvPolynomial.coeff_eval_eq_eval_coeff] using h

/-! ## Fibre counting -/

theorem tail_fiber_count (s M : ℕ) (S : Finset (Fin (s + 1) → ℤ)) (T : Finset (Fin s → ℤ))
    (h1 : S ⊆ cbox (s + 1) M) (h2 : ∀ x ∈ S, Fin.tail x ∈ T) :
    S.card ≤ (2 * M + 1) * T.card := by
  have hIcc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]; omega
  have hmap : Set.MapsTo Fin.tail (↑S) (↑T) := fun x hx => h2 x hx
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc ∑ u ∈ T, (S.filter fun x => Fin.tail x = u).card
      ≤ ∑ u ∈ T, (2 * M + 1) := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hb : (S.filter fun x => Fin.tail x = u).card
            ≤ (Finset.Icc (-(M : ℤ)) (M : ℤ)).card := by
          refine Finset.card_le_card_of_injOn (fun x : Fin (s + 1) → ℤ => x 0) ?_ ?_
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_filter] at hx
            have hx1 := h1 hx.1
            rw [mem_cbox] at hx1
            exact Finset.mem_Icc.mpr (hx1 0)
          · intro x hx y hy hxy
            rw [Finset.mem_coe, Finset.mem_filter] at hx hy
            change x 0 = y 0 at hxy
            have hcons : Fin.cons (x 0) (Fin.tail x) = Fin.cons (y 0) (Fin.tail y) := by
              rw [hxy, hx.2, hy.2]
            rwa [Fin.cons_self_tail, Fin.cons_self_tail] at hcons
        rwa [hIcc] at hb
    _ = (2 * M + 1) * T.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        simp

theorem good_fiber_count (s M : ℕ) (f : MvPolynomial (Fin (s + 1)) ℤ)
    (hdeg : f.totalDegree ≤ 4) (S : Finset (Fin (s + 1) → ℤ)) (T : Finset (Fin s → ℤ))
    (h1 : S ⊆ cbox (s + 1) M) (h2 : ∀ x ∈ S, Fin.tail x ∈ T)
    (h3 : ∀ x ∈ S, MvPolynomial.eval x f = 0)
    (h4 : ∀ u ∈ T, Polynomial.map (MvPolynomial.eval u) (MvPolynomial.finSuccEquiv ℤ s f) ≠ 0) :
    S.card ≤ 4 * T.card := by
  have hmap : Set.MapsTo Fin.tail (↑S) (↑T) := fun x hx => h2 x hx
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc ∑ u ∈ T, (S.filter fun x => Fin.tail x = u).card
      ≤ ∑ u ∈ T, 4 := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hq : Polynomial.map (MvPolynomial.eval u) (MvPolynomial.finSuccEquiv ℤ s f) ≠ 0 :=
          h4 u hu
        have hqd : (Polynomial.map (MvPolynomial.eval u)
            (MvPolynomial.finSuccEquiv ℤ s f)).natDegree ≤ 4 := by
          calc (Polynomial.map (MvPolynomial.eval u)
                (MvPolynomial.finSuccEquiv ℤ s f)).natDegree
              ≤ (MvPolynomial.finSuccEquiv ℤ s f).natDegree := Polynomial.natDegree_map_le
            _ = MvPolynomial.degreeOf 0 f := MvPolynomial.natDegree_finSuccEquiv f
            _ ≤ f.totalDegree := MvPolynomial.degreeOf_le_totalDegree f 0
            _ ≤ 4 := hdeg
        refine le_trans (Finset.card_le_card_of_injOn (fun x : Fin (s + 1) → ℤ => x 0) ?_ ?_)
          (Work.Q44Child.roots_card_le _ hq hqd)
        · intro x hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          change x 0 ∈ (Polynomial.map (MvPolynomial.eval u)
            (MvPolynomial.finSuccEquiv ℤ s f)).roots.toFinset
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot.def]
          have hev : MvPolynomial.eval x f = Polynomial.eval (x 0)
              (Polynomial.map (MvPolynomial.eval (Fin.tail x)) (MvPolynomial.finSuccEquiv ℤ s f)) := by
            have := MvPolynomial.eval_eq_eval_mv_eval' (Fin.tail x) (x 0) f
            rwa [Fin.cons_self_tail] at this
          have h0 : MvPolynomial.eval x f = 0 := h3 x hx.1
          rw [hev, hx.2] at h0
          exact h0
        · intro x hx y hy hxy
          rw [Finset.mem_coe, Finset.mem_filter] at hx hy
          change x 0 = y 0 at hxy
          have hcons : Fin.cons (x 0) (Fin.tail x) = Fin.cons (y 0) (Fin.tail y) := by
            rw [hxy, hx.2, hy.2]
          rwa [Fin.cons_self_tail, Fin.cons_self_tail] at hcons
    _ = 4 * T.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        simp

/-! ## The univariate base case -/

theorem eval_injective_fin_zero (u : Fin 0 → ℤ) : Function.Injective (MvPolynomial.eval u) := by
  rw [← MvPolynomial.aeval_eq_eval u, MvPolynomial.aeval_injective_iff_of_isEmpty]
  intro a b h
  simpa using h

theorem count_one (f : MvPolynomial (Fin 1) ℤ) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ 4) (M : ℕ) :
    Cnt 1 f M ≤ 4 := by
  set u₀ : Fin 0 → ℤ := fun i => i.elim0 with hu₀
  set q : Polynomial ℤ := Polynomial.map (MvPolynomial.eval u₀)
      (MvPolynomial.finSuccEquiv ℤ 0 f) with hq
  have hqne : q ≠ 0 := by
    rw [hq]
    refine (Polynomial.map_ne_zero_iff (eval_injective_fin_zero u₀)).mpr ?_
    intro h
    exact hf ((MvPolynomial.finSuccEquiv ℤ 0).injective h)
  have hqdeg : q.natDegree ≤ 4 := by
    rw [hq]
    calc (Polynomial.map (MvPolynomial.eval u₀)
          (MvPolynomial.finSuccEquiv ℤ 0 f)).natDegree
        ≤ (MvPolynomial.finSuccEquiv ℤ 0 f).natDegree := Polynomial.natDegree_map_le
      _ = MvPolynomial.degreeOf 0 f := MvPolynomial.natDegree_finSuccEquiv f
      _ ≤ f.totalDegree := MvPolynomial.degreeOf_le_totalDegree f 0
      _ ≤ 4 := hdeg
  simp only [Cnt]
  refine le_trans (Finset.card_le_card_of_injOn (fun x : Fin 1 → ℤ => x 0) ?_ ?_)
    (Work.Q44Child.roots_card_le q hqne hqdeg)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    change x 0 ∈ q.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqne, Polynomial.IsRoot.def]
    have hev : MvPolynomial.eval x f = Polynomial.eval (x 0)
        (Polynomial.map (MvPolynomial.eval (Fin.tail x)) (MvPolynomial.finSuccEquiv ℤ 0 f)) := by
      have := MvPolynomial.eval_eq_eval_mv_eval' (Fin.tail x) (x 0) f
      rwa [Fin.cons_self_tail] at this
    have htail : (Fin.tail x : Fin 0 → ℤ) = u₀ := Subsingleton.elim _ _
    rw [htail] at hev
    have h0 : MvPolynomial.eval x f = 0 := hx.2
    rwa [hev, ← hq] at h0
  · intro x hx y hy hxy
    change x 0 = y 0 at hxy
    funext i
    fin_cases i
    exact hxy

/-! ## The induction step -/

theorem step_aux (n : ℕ) {C : ℝ} (hC : 0 < C)
    (ih : ∀ (g : MvPolynomial (Fin (n + 1)) ℤ), g ≠ 0 → g.totalDegree ≤ 4 → ∀ M : ℕ,
      ((Cnt (n + 1) g M : ℕ) : ℝ) ≤ C * ((M : ℝ) + 1) ^ n)
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ 4) (M : ℕ) :
    ((Cnt (n + 2) f M : ℕ) : ℝ) ≤ (4 * 2 ^ (n + 1) + 2 * C) * ((M : ℝ) + 1) ^ (n + 1) := by
  classical
  have hpf_ne : MvPolynomial.finSuccEquiv ℤ (n + 1) f ≠ 0 := fun h =>
    hf ((MvPolynomial.finSuccEquiv ℤ (n + 1)).injective h)
  obtain ⟨k, hk⟩ : ∃ k, (MvPolynomial.finSuccEquiv ℤ (n + 1) f).coeff k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpf_ne (Polynomial.ext h)
  have hdegk : ((MvPolynomial.finSuccEquiv ℤ (n + 1) f).coeff k).totalDegree ≤ 4 := by
    have h1 := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f k hk
    have h2 : ((MvPolynomial.finSuccEquiv ℤ (n + 1) f).coeff k).totalDegree ≤ f.totalDegree :=
      (Nat.le_add_right _ _).trans h1
    exact h2.trans hdeg
  set X : Finset (Fin (n + 2) → ℤ) :=
    (cbox (n + 2) M).filter (fun x => MvPolynomial.eval x f = 0) with hX
  set Y : Finset (Fin (n + 2) → ℤ) := X.filter (fun x =>
    Polynomial.map (MvPolynomial.eval (Fin.tail x)) (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0)
    with hY
  set Z : Finset (Fin (n + 2) → ℤ) := X.filter (fun x =>
    ¬ (Polynomial.map (MvPolynomial.eval (Fin.tail x))
      (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0)) with hZ
  set G : Finset (Fin (n + 1) → ℤ) := (cbox (n + 1) M).filter (fun u =>
    Polynomial.map (MvPolynomial.eval u) (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0) with hG
  set B : Finset (Fin (n + 1) → ℤ) := (cbox (n + 1) M).filter (fun u =>
    MvPolynomial.eval u ((MvPolynomial.finSuccEquiv ℤ (n + 1) f).coeff k) = 0) with hB
  have hsplit : X.card ≤ Y.card + Z.card := by
    rw [hY, hZ]
    exact le_of_eq (Finset.card_filter_add_card_filter_not (s := X) (fun x : Fin (n + 2) → ℤ =>
      Polynomial.map (MvPolynomial.eval (Fin.tail x))
        (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0)).symm
  have hYb : (Y.card : ℝ) ≤ 4 * (2 * (M : ℝ) + 1) ^ (n + 1) := by
    have hsub1 : Y ⊆ cbox (n + 2) M := by
      intro x hx
      rw [hY, hX] at hx
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hsub2 : ∀ x ∈ Y, Fin.tail x ∈ G := by
      intro x hx
      rw [hY, hX] at hx
      have hq := (Finset.mem_filter.mp hx).2
      have hbox := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
      rw [hG]
      exact Finset.mem_filter.mpr ⟨tail_mem_cbox hbox, hq⟩
    have hsub3 : ∀ x ∈ Y, MvPolynomial.eval x f = 0 := by
      intro x hx
      rw [hY, hX] at hx
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hsub4 : ∀ u ∈ G, Polynomial.map (MvPolynomial.eval u)
        (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0 := by
      intro u hu
      rw [hG] at hu
      exact (Finset.mem_filter.mp hu).2
    have hgc := good_fiber_count (n + 1) M f hdeg Y G hsub1 hsub2 hsub3 hsub4
    have hGcard : ((G.card : ℕ) : ℝ) ≤ (2 * (M : ℝ) + 1) ^ (n + 1) := by
      have hle : G.card ≤ (cbox (n + 1) M).card := by
        rw [hG]; exact Finset.card_le_card (Finset.filter_subset _ _)
      calc ((G.card : ℕ) : ℝ) ≤ (((cbox (n + 1) M).card : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (2 * (M : ℝ) + 1) ^ (n + 1) := cbox_card (n + 1) M
    calc (Y.card : ℝ) ≤ ((4 * G.card : ℕ) : ℝ) := by exact_mod_cast hgc
      _ = 4 * (G.card : ℝ) := by push_cast; ring
      _ ≤ 4 * (2 * (M : ℝ) + 1) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hGcard (by norm_num)
  have hZb : (Z.card : ℝ) ≤ (2 * (M : ℝ) + 1) * (C * ((M : ℝ) + 1) ^ n) := by
    have hsub1 : Z ⊆ cbox (n + 2) M := by
      intro x hx
      rw [hZ, hX] at hx
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hsub2 : ∀ x ∈ Z, Fin.tail x ∈ B := by
      intro x hx
      rw [hZ, hX] at hx
      have hq : ¬ (Polynomial.map (MvPolynomial.eval (Fin.tail x))
          (MvPolynomial.finSuccEquiv ℤ (n + 1) f) ≠ 0) := (Finset.mem_filter.mp hx).2
      have hbox := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
      have hxB : Fin.tail x ∈ (cbox (n + 1) M).filter (fun u =>
          Polynomial.map (MvPolynomial.eval u) (MvPolynomial.finSuccEquiv ℤ (n + 1) f) = 0) :=
        Finset.mem_filter.mpr ⟨tail_mem_cbox hbox, not_not.mp hq⟩
      rw [hB]
      exact coeff_bad_subset (n + 1) M k _ hxB
    have htc := tail_fiber_count (n + 1) M Z B hsub1 hsub2
    have hBcard : ((B.card : ℕ) : ℝ) ≤ C * ((M : ℝ) + 1) ^ n := by
      have hBC : B.card = Cnt (n + 1) ((MvPolynomial.finSuccEquiv ℤ (n + 1) f).coeff k) M := by
        rw [hB]; rfl
      rw [hBC]
      exact ih _ hk hdegk M
    calc (Z.card : ℝ) ≤ (((2 * M + 1) * B.card : ℕ) : ℝ) := by exact_mod_cast htc
      _ = (2 * (M : ℝ) + 1) * (B.card : ℝ) := by push_cast; ring
      _ ≤ (2 * (M : ℝ) + 1) * (C * ((M : ℝ) + 1) ^ n) :=
          mul_le_mul_of_nonneg_left hBcard (by positivity)
  have hmain : (X.card : ℝ) ≤ (4 * 2 ^ (n + 1) + 2 * C) * ((M : ℝ) + 1) ^ (n + 1) := by
    have h2M : (2 * (M : ℝ) + 1) ≤ 2 * ((M : ℝ) + 1) := by linarith
    have hpow : (2 * (M : ℝ) + 1) ^ (n + 1) ≤ 2 ^ (n + 1) * ((M : ℝ) + 1) ^ (n + 1) := by
      have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * (M : ℝ) + 1) h2M (n + 1)
      rwa [mul_pow] at h
    have h1 : (X.card : ℝ) ≤ (Y.card : ℝ) + (Z.card : ℝ) := by
      have h2 : ((X.card : ℕ) : ℝ) ≤ ((Y.card + Z.card : ℕ) : ℝ) := by exact_mod_cast hsplit
      push_cast at h2 ⊢
      linarith
    have h3 : 4 * (2 * (M : ℝ) + 1) ^ (n + 1) ≤
        4 * (2 ^ (n + 1) * ((M : ℝ) + 1) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have h4 : (2 * (M : ℝ) + 1) * (C * ((M : ℝ) + 1) ^ n) ≤
        2 * C * ((M : ℝ) + 1) ^ (n + 1) := by
      have hstep : (2 * (M : ℝ) + 1) * (C * ((M : ℝ) + 1) ^ n) ≤
          (2 * ((M : ℝ) + 1)) * (C * ((M : ℝ) + 1) ^ n) :=
        mul_le_mul_of_nonneg_right h2M (by positivity)
      have heq : (2 * ((M : ℝ) + 1)) * (C * ((M : ℝ) + 1) ^ n) =
          2 * C * ((M : ℝ) + 1) ^ (n + 1) := by
        rw [pow_succ]; ring
      exact hstep.trans_eq heq
    calc (X.card : ℝ) ≤ 4 * (2 * (M : ℝ) + 1) ^ (n + 1) +
            (2 * (M : ℝ) + 1) * (C * ((M : ℝ) + 1) ^ n) := le_trans h1 (add_le_add hYb hZb)
      _ ≤ 4 * (2 ^ (n + 1) * ((M : ℝ) + 1) ^ (n + 1)) + 2 * C * ((M : ℝ) + 1) ^ (n + 1) :=
          add_le_add h3 h4
      _ = (4 * 2 ^ (n + 1) + 2 * C) * ((M : ℝ) + 1) ^ (n + 1) := by ring
  simp only [Cnt]
  exact hmain

/-! ## The induction -/

theorem count_all : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (f : MvPolynomial (Fin (n + 1)) ℤ), f ≠ 0 →
    f.totalDegree ≤ 4 → ∀ M : ℕ, ((Cnt (n + 1) f M : ℕ) : ℝ) ≤ C * ((M : ℝ) + 1) ^ n := by
  intro n
  induction n with
  | zero =>
      refine ⟨4, by norm_num, fun f hf hdeg M => ?_⟩
      have h := count_one f hf hdeg M
      have h4 : ((Cnt 1 f M : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h
      simpa using h4
  | succ n ih =>
      obtain ⟨C, hCpos, hC⟩ := ih
      refine ⟨4 * 2 ^ (n + 1) + 2 * C, by positivity, fun f hf hdeg M => ?_⟩
      exact step_aux n hCpos hC f hf hdeg M

/-! ## The quartic zero bound -/

theorem quartic_zero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Work.HP.Mon 4 4 → ℤ), a ≠ 0 → ∀ T : ℝ, 1 ≤ T →
      (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ Work.HP.formEval 4 4 a x = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ C * T ^ 4 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := count_all 4
  refine ⟨81 * C₀, by positivity, fun a ha T hT => ?_⟩
  set M : ℕ := ⌈T⌉₊ with hM
  have hTM : T ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil T
  have hform_ne : formZ a ≠ 0 := ((formZ_basic a).1.not).mpr ha
  have hform_deg : (formZ a).totalDegree ≤ 4 := (formZ_basic a).2
  have hsub : ({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ Work.HP.formEval 4 4 a x = 0} :
        Set (Fin 5 → ℤ))
      ⊆ ((cbox 5 M).filter (fun x => MvPolynomial.eval x (formZ a) = 0) :
        Finset (Fin 5 → ℤ)) := by
    intro x hx
    obtain ⟨hxT, hx0⟩ := hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_cbox]
      intro i
      have h1 : |(x i : ℝ)| ≤ (M : ℝ) :=
        le_trans (le_trans (Work.HP.abs_apply_le_eNorm x i) hxT) hTM
      have h2 : ((|x i| : ℤ) : ℝ) = |(x i : ℝ)| := Int.cast_abs
      have h3 : ((|x i| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by rw [h2]; push_cast; exact h1
      exact abs_le.mp (by exact_mod_cast h3)
    · rw [eval_formZ]; exact hx0
  have hcard : (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ Work.HP.formEval 4 4 a x = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (((cbox 5 M).filter (fun x => MvPolynomial.eval x (formZ a) = 0)).card : ℝ) := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    exact_mod_cast h1
  have hb : (((cbox 5 M).filter (fun x => MvPolynomial.eval x (formZ a) = 0)).card : ℝ)
      ≤ C₀ * ((M : ℝ) + 1) ^ 4 := by
    have h := hC₀ (formZ a) hform_ne hform_deg M
    simpa only [Cnt] using h
  have harith : ((M : ℝ) + 1) ^ 4 ≤ 81 * T ^ 4 := by
    have h1 : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (M : ℝ) + 1 ≤ 3 * T := by rw [hM]; linarith
    have h3 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
    calc ((M : ℝ) + 1) ^ 4 ≤ (3 * T) ^ 4 := pow_le_pow_left₀ h3 h2 4
      _ = 81 * T ^ 4 := by ring
  calc (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ Work.HP.formEval 4 4 a x = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (((cbox 5 M).filter (fun x => MvPolynomial.eval x (formZ a) = 0)).card : ℝ) := hcard
    _ ≤ C₀ * ((M : ℝ) + 1) ^ 4 := hb
    _ ≤ C₀ * (81 * T ^ 4) := mul_le_mul_of_nonneg_left harith hC₀pos.le
    _ = (81 * C₀) * T ^ 4 := by ring

end Work.HP.Q44Child
