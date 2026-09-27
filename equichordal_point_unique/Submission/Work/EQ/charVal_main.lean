import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.charVal_aux
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germC_step_algebra
import Submission.Work.EQ.germC_snd_deriv
import Submission.Work.EQ.germC_apply_ne
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.fan_step_deriv
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.walk_count

/-! Assembly of `Work.EQ.charVal_props` from the delegated inputs: `germC_leaf` (the principal
invariant leaf), `fan_step_deriv` (the one-step centre and derivative recursion), `walk_bounds`
(positivity, the potential inequality, the sign) and `walk_count` (exponential decay of the
weight with the number of non-principal letters). -/

namespace Work.EQ

open Complex

noncomputable section

/-- Weight product of a word read in the fan order (head first): the head letter uses the state
reached by the walk of the tail. -/
def rprod (a : ℝ) : List Bool → ℝ
  | [] => 1
  | c :: l => sgW a c (stAux l.reverse 0) * rprod a l

lemma rprod_cons (a : ℝ) (c : Bool) (l : List Bool) :
    rprod a (c :: l) = sgW a c (stAux l.reverse 0) * rprod a l := rfl

lemma rprod_eq_sgnAux (a : ℝ) (l : List Bool) : rprod a l = sgnAux a l.reverse 0 := by
  induction l with
  | nil => simp [rprod]
  | cons c l ih =>
    rw [rprod_cons, ih, List.reverse_cons, sgnAux_append]
    simp [mul_comm]

lemma stAux_cons_reverse (c : Bool) (l : List Bool) :
    stAux (c :: l).reverse 0 = stp c (stAux l.reverse 0) := by
  rw [List.reverse_cons, stAux_append]
  simp

/-- `λ(-1 + s/|x + a/2|)` agrees with the signed step weight, for `x = stCtr n`. -/
lemma lam_factor_eq_sgW {a : ℝ} (n : ℕ) (c : Bool) :
    eqLam a * (-1 + (if c then 1 else -1) / |stCtr n + a / 2|) = sgW a c n := by
  cases c <;> simp [sgW, upW, dnW, stQ] <;> ring

variable {a : ℝ}

/-- The interface of the stable germ used below: differentiability at `0` of both coordinates,
the value of the `y`-derivative, and the invariance of the principal leaf.  Derived from
`Work.EQ.germC_facts`. -/
lemma germC_diff_at_zero (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    DifferentiableAt ℂ (fun u => (germC a h u).1) 0 ∧
    DifferentiableAt ℂ (fun u => (germC a h u).2) 0 ∧
    deriv (fun u => (germC a h u).2) 0 = (((1 - a) / 2 : ℝ) : ℂ) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, u ∈ Metric.ball 0 δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) := by
  obtain ⟨ρ, hρ, hAn, -, hinv, -, hderiv⟩ := germC_facts ha0 ha1 hh
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρ
  have hd := (hAn 0 hmem).differentiableAt
  refine ⟨hd.fst, hd.snd, ?_, ⟨ρ, hρ, fun u hu => (hinv u hu).2⟩⟩
  rw [hderiv]

/-- The fan centre and the derivative of its second coordinate, by induction on the word. -/
lemma fan_aux (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r)
    (ε : List Bool) :
    DifferentiableAt ℂ (fun u => (fan a h ε u).1) 0 ∧
    DifferentiableAt ℂ (fun u => (fan a h ε u).2) 0 ∧
    fan a h ε 0 = ((stCtr (stAux ε.reverse 0) : ℂ), (0 : ℂ)) ∧
    deriv (fun u => (fan a h ε u).2) 0 =
      (rprod a ε : ℂ) * deriv (fun u => (germC a h u).2) 0 := by
  obtain ⟨wb1, wb2, wb3, wb4, wb5, wb6, wb7, wb8, wb9, wb10, wb11, wb12, wb13, wb14, wb15⟩ :=
    walk_bounds (a := a) ha0 ha1
  induction ε with
  | nil =>
    obtain ⟨hd1, hd2, hderiv, -⟩ := germC_diff_at_zero ha0 ha1 hh
    have h0 := germC_value ha0 ha1 hh
    refine ⟨hd1, hd2, ?_, ?_⟩
    · rw [show fan a h [] 0 = germC a h 0 from rfl, h0]
      norm_num
    · simp [rprod, fan]
  | cons c l ih =>
    obtain ⟨hd1, hd2, hc, hderiv⟩ := ih
    have hx : stCtr (stAux l.reverse 0) + a / 2 ≠ 0 := wb3 _
    have hstep := fan_step_deriv ha0 ha1 (h := h) l c hc hx hd1 hd2
    obtain ⟨hcentre, hd1', hd2', hderiv'⟩ := hstep
    refine ⟨hd1', hd2', ?_, ?_⟩
    · rw [hcentre, stAux_cons_reverse]
      congr 1
      rw [wb1 (stAux l.reverse 0) c]
    · rw [hderiv', hderiv, lam_factor_eq_sgW (stAux l.reverse 0) c, rprod_cons]
      push_cast
      ring

/-- `charVal` is the product of the signed step weights. -/
lemma charVal_eq_rprod (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) :
    charVal a h ε = (rprod a ε : ℂ) := by
  obtain ⟨-, -, -, hderiv⟩ := fan_aux ha0 ha1 hh ε
  obtain ⟨-, -, hd, -⟩ := germC_diff_at_zero ha0 ha1 hh
  have hD0 : deriv (fun u => (germC a h u).2) 0 ≠ 0 := by
    rw [hd]
    intro hcon
    have h2 : ((1 - a) / 2 : ℝ) = 0 := by
      have := congrArg Complex.re hcon
      simpa using this
    linarith
  rw [charVal, hderiv]
  exact mul_div_cancel_right₀ _ hD0

/-- A fan word whose centre is `A₁` has a closed walk. -/
lemma stAux_eq_zero_of_closed (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ε : List Bool}
    (hε : fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ))) : stAux ε.reverse 0 = 0 := by
  obtain ⟨-, -, hc, -⟩ := fan_aux ha0 ha1 hh ε
  rw [hc] at hε
  have h1 : (stCtr (stAux ε.reverse 0) : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
    have := congrArg Prod.fst hε
    simpa using this
  have h2 : stCtr (stAux ε.reverse 0) = (-1 / 2 : ℝ) := Complex.ofReal_inj.mp h1
  exact stCtr_eq_iff.mp h2

/-- For a closed word, the characteristic value is the (real) weight product of the reverse word. -/
lemma charVal_of_closed (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ε : List Bool}
    (hε : fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ))) :
    charVal a h ε = ((wtAux a ε.reverse 0 : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, wb14, wb15⟩ := walk_bounds (a := a) ha0 ha1
  have hclosed := stAux_eq_zero_of_closed ha0 ha1 hh hε
  rw [charVal_eq_rprod ha0 ha1 hh ε, rprod_eq_sgnAux, wb14 ε.reverse 0]
  have heven : Even (nsAux ε.reverse 0) := by
    have h := wb15 ε.reverse
    rw [hclosed, add_zero] at h
    exact h
  rw [heven.neg_one_pow, one_mul]

/-- The fan of an all-principal word is the germ itself, on the ball where the principal branch
inverts the germ step. -/
lemma fan_eq_germC_of_all_true (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {δ : ℝ}
    (hinv : ∀ u : ℂ, u ∈ Metric.ball 0 δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (l : List Bool) (hl : ∀ c ∈ l, c = true) :
    Set.EqOn (fan a h l) (germC a h) (Metric.ball 0 δ) := by
  obtain ⟨hL0, hL1⟩ := eqLam_pos' ha0 ha1, eqLam_lt_one' ha0 ha1
  induction l with
  | nil => intro u _; rfl
  | cons c l ih =>
    intro u hu
    have hc : c = true := hl c (by simp)
    have hmem : (eqLam a : ℂ) * u ∈ Metric.ball 0 δ := by
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      have h1 : ‖(eqLam a : ℂ) * u‖ = eqLam a * ‖u‖ := by
        have h2 : ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| := by simp
        rw [norm_mul, h2, abs_of_pos hL0]
      rw [h1]
      calc eqLam a * ‖u‖ ≤ 1 * ‖u‖ :=
            mul_le_mul_of_nonneg_right hL1.le (norm_nonneg u)
        _ = ‖u‖ := one_mul _
        _ < δ := hu
    have htail : ∀ c' ∈ l, c' = true := fun c' hc' => hl c' (by simp [hc'])
    rw [show fan a h (c :: l) u = invBranch a c (fan a h l ((eqLam a : ℂ) * u)) from rfl, hc,
      ih htail hmem, hinv u hu]

/-- Only finitely many characteristic values of returning words exceed a positive bound. -/
lemma finite_charVal_set (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (η : ℝ) (hη : 0 < η) :
    {μ : ℂ | ∃ ε : List Bool, fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
      charVal a h ε = μ ∧ η ≤ ‖μ‖}.Finite := by
  obtain ⟨γ, hγ0, hγ1, hbnd⟩ := walk_count (a := a) ha0 ha1
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    walk_bounds (a := a) ha0 ha1
  obtain ⟨K, hK⟩ : ∃ K : ℕ, γ ^ K < η := exists_pow_lt_of_lt_one hη hγ1
  refine Set.Finite.subset ((finite_word_values a (2 * K)).image (fun v : ℝ => (v : ℂ))) ?_
  rintro μ ⟨ε, hε, rfl, hημ⟩
  have hcv := charVal_of_closed ha0 ha1 hh hε
  have hclosed := stAux_eq_zero_of_closed ha0 ha1 hh hε
  have hpos : 0 < wtAux a ε.reverse 0 := w10 ε.reverse 0
  have hnorm : η ≤ wtAux a ε.reverse 0 := by
    have h := hημ
    rw [hcv] at h
    have h2 : ‖((wtAux a ε.reverse 0 : ℝ) : ℂ)‖ = |wtAux a ε.reverse 0| := by simp
    rw [h2, abs_of_pos hpos] at h
    exact h
  have hb := hbnd ε.reverse hclosed
  have hcount : ε.reverse.count false ≤ K := by
    by_contra hlt
    push_neg at hlt
    have hle : γ ^ (ε.reverse.count false) ≤ γ ^ (K + 1) :=
      pow_le_pow_of_le_one hγ0.le hγ1.le (by omega)
    have hK' : γ ^ (K + 1) < η := by
      have h2 : γ ^ (K + 1) ≤ γ ^ K := pow_le_pow_of_le_one hγ0.le hγ1.le (Nat.le_succ K)
      linarith
    linarith
  refine ⟨wtAux a ε.reverse 0, ⟨redAux 0 ε.reverse, ?_, ?_⟩, hcv.symm⟩
  · rw [length_redAux]
    have := nsAux_le_two_mul_count hclosed
    omega
  · rw [wtAux_redAux a ha0 ha1]

end

end Work.EQ
