/-
# `Work.FTS.PhiStar.FlatW_psiDiv` — the flat `𝒲^{7,∞}`-bound on the divided profile `ψ/sin 2θ`

The target of this file is

`∃ C, 0 < C ∧ ∀ α ψ, 0 < α → α ≤ 1/4 → AngModel α ψ → FlatW 7 (fun z θ => ψ θ / sin 2θ) C`,

i.e. the *uniform in `α ∈ (0,1/4]`* flat bound on the angular model `ψ` divided by `sin 2θ`.
Since `FlatW 7 f` only probes `∂_z^k` and `D_θ^i ∂_θ` of `f`, and the function
`(z,θ) ↦ ψ θ / sin 2θ` is `z`-independent, everything reduces to two families of
`θ`-bounds:

* `|ψ θ / sin 2θ| ≤ C` — the divided profile itself; and
* `|D_θ^i (∂_θ(ψ/sin 2θ))| ≤ C` for `i ≤ 6` — the `D_θ`-iterates of its derivative.

Both are obtained from the *first-order* structure of the angular model.  Writing
`W = ψ/sin 2θ` and `p = W'`, the equation `Lzero1 ψ = Γ̄` becomes, in `D_θ = sin 2θ ∂_θ`
form (`PsiDivS2Ode`, `DerivConstPhi`),

`D_θ p = A·p - Γ̄`,  `A = 6 sin²θ - 4 cos²θ`,

whose first integral is `sin²θ cos³θ · p - Gzero α θ / 2 = const`.  The constant is pinned
down to `0` by the endpoint condition `ψ 0 = 0` with continuity (`PsiDivS2EqPfun`) — this
is the step that identifies `p` with the *regular* solution `Pfun α θ / sin²θ`, hence gives
`|p| ≤ 500` (`Pfun_div_sin_sq_le`).  The `D_θ`-iterates of `p` are then bounded inductively
from the recursion `D_θ^{i+1}p = Σ_j C(i,j) (D_θ^{i-j}A)(D_θ^j p) - D_θ^i Γ̄`
(`LopIterRecursion` + the explicit bound sequence `LopBdAux` below), and the additive
constant in `W` is fixed by the moment condition `∫ ψ sinθcos²θ = 0` (`Wdiv_bound`).

The auxiliary lemmas used here (and proved in the sibling files of this directory) are
`PsiDivS2Ode`, `LopIterRecursion`, `LopAuxBounds`, `DerivConstPhi`, `PsiDivS2EqPfun`,
`Wdiv_bound`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Psi0_exists
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.PsiDivS2Ode
import Submission.Work.FTS.PhiStar.LopIterRecursion
import Submission.Work.FTS.PhiStar.LopAuxBounds
import Submission.Work.FTS.PhiStar.DerivConstPhi
import Submission.Work.FTS.PhiStar.PsiDivS2EqPfun
import Submission.Work.FTS.PhiStar.Wdiv_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The divided profile and its derivative -/

/-- The divided angular profile `W θ = ψ θ / sin 2θ`. -/
abbrev Wdiv (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => ψ θ / Real.sin (2 * θ)

/-- Its `θ`-derivative `p = W'`. -/
abbrev Pdiv (ψ : ℝ → ℝ) : ℝ → ℝ := deriv (Wdiv ψ)

/-! ## A function with vanishing derivative on the open interval is constant -/

/-- If `h` is differentiable on `(0,π/2)` and `h' ≡ 0` there, then `h` is constant there
(Fundamental Theorem of Calculus on `[θ, π/4]`). -/
lemma exists_const_of_deriv_eq_zero {h : ℝ → ℝ}
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), DifferentiableAt ℝ h θ)
    (hz : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv h θ = 0) :
    ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), h θ = c := by
  refine ⟨h (Real.pi / 4), fun θ hθ => ?_⟩
  have h4 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rcases le_total θ (Real.pi / 4) with hle | hle
    · rw [Set.uIcc_of_le hle]
      intro x hx
      exact ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, h4.2]⟩
    · rw [Set.uIcc_of_ge hle]
      intro x hx
      exact ⟨by linarith [h4.1, hx.1], by linarith [hx.2, hθ.2]⟩
  have hII : IntervalIntegrable (deriv h) volume θ (Real.pi / 4) :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr
      (fun x hx => (hz x (hsub (Set.uIoc_subset_uIcc hx))).symm)
  have hFTC := intervalIntegral.integral_deriv_eq_sub (f := h) (a := θ) (b := Real.pi / 4)
    (fun x hx => hdiff x (hsub hx)) hII
  have hzero : (∫ y in θ..(Real.pi / 4), deriv h y) = 0 := by
    have h1 : (∫ y in θ..(Real.pi / 4), deriv h y)
        = ∫ y in θ..(Real.pi / 4), (0 : ℝ) :=
      intervalIntegral.integral_congr (fun x hx => hz x (hsub hx))
    rw [h1, intervalIntegral.integral_zero]
  linarith [hFTC, hzero]

/-! ## An explicit (uniform) bound sequence for the `Lop`-iterates

`Work.FTS.PhiStar.LopIterRecursion` gives, for a solution of `Lop f = A·f - g` on the open
interval, the binomial expansion of the iterates.  For the final constant of `FlatW_psiDiv`
to be independent of `(α,ψ)` the *sequence* of bounds has to be an explicit function of the
data bounds `Ka`, `Kg` and the base bound `M`; `LopBdAux` below is exactly that sequence. -/

/-- The explicit sequence of bounds generated by the recursion
`Lop^{n+1} f = ∑_{j≤n} C(n,j)·(Lop^{n-j}A)·(Lop^j f) - Lop^n g`. -/
noncomputable def LopBdAux (Ka Kg : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℕ → ℝ :=
  Nat.rec (Function.update (fun _ : ℕ => 0) 0 M)
    (fun k b => Function.update b (k + 1)
      ((∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * (Ka (k - j) * b j))) + Kg k)) n

/-- The level-`6` bound, the one used by the transfer to `FlatW 7`. -/
noncomputable def LopBd (Ka Kg : ℕ → ℝ) (M : ℝ) (i : ℕ) : ℝ := LopBdAux Ka Kg M 6 i

lemma LopBdAux_zero (Ka Kg : ℕ → ℝ) (M : ℝ) :
    LopBdAux Ka Kg M 0 = Function.update (fun _ : ℕ => 0) 0 M := rfl

lemma LopBdAux_succ (Ka Kg : ℕ → ℝ) (M : ℝ) (n : ℕ) :
    LopBdAux Ka Kg M (n + 1) = Function.update (LopBdAux Ka Kg M n) (n + 1)
      ((∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j))) + Kg n) := rfl

/-- Non-negativity of the bound sequence. -/
lemma LopBdAux_nonneg {Ka Kg : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hKa0 : ∀ j, 0 ≤ Ka j) (hKg0 : ∀ j, 0 ≤ Kg j) :
    ∀ n i, 0 ≤ LopBdAux Ka Kg M n i := by
  intro n
  induction n with
  | zero =>
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [LopBdAux_zero, Function.update_self]
        exact hM
      · rw [LopBdAux_zero, Function.update_of_ne hi]
  | succ n ih =>
      intro i
      by_cases hi : i = n + 1
      · subst hi
        rw [LopBdAux_succ, Function.update_self]
        exact add_nonneg
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKa0 _) (ih j)))
          (hKg0 n)
      · rw [LopBdAux_succ, Function.update_of_ne hi]
        exact ih i

/-- The bound sequence dominates the `Lop`-iterates of a solution of `Lop f = A·f - g`. -/
lemma LopBdAux_bound {f A g : ℝ → ℝ} {Ka Kg : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M)
    (hKa0 : ∀ j, 0 ≤ Ka j) (hKg0 : ∀ j, 0 ≤ Kg j)
    (hKa : ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |(Work.Spaces.Lop^[j]) A θ| ≤ Ka j)
    (hKg : ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |(Work.Spaces.Lop^[j]) g θ| ≤ Kg j)
    (hrec : ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i + 1]) f θ
        = (∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
          - (Work.Spaces.Lop^[i]) g θ) :
    ∀ n ≤ 6, ∀ i ≤ n, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) f θ| ≤ LopBdAux Ka Kg M n i := by
  intro n
  induction n with
  | zero =>
      intro _ i hi θ hθ
      have hi0 : i = 0 := by omega
      subst hi0
      rw [LopBdAux_zero, Function.update_self]
      simpa using hMf θ hθ
  | succ n ih =>
      intro hn i hi θ hθ
      rcases lt_or_eq_of_le hi with hlt | heq
      · rw [LopBdAux_succ, Function.update_of_ne (show i ≠ n + 1 by omega)]
        exact ih (by omega) i (by omega) θ hθ
      · subst heq
        rw [LopBdAux_succ, Function.update_self, hrec n θ hθ]
        have h1 : |∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ)|
            ≤ ∑ j ∈ Finset.range (n + 1),
                (n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
          intro j hj
          have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hnj : n - j ≤ 6 := by omega
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose j))]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hKa (n - j) hnj θ hθ) (ih (by omega) j hjle θ hθ)
              (abs_nonneg _) (hKa0 _))
            (Nat.cast_nonneg (n.choose j))
        have h2 : |(Work.Spaces.Lop^[n]) g θ| ≤ Kg n := hKg n (by omega) θ hθ
        calc |(∑ j ∈ Finset.range (n + 1),
                  (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
                - (Work.Spaces.Lop^[n]) g θ|
              ≤ |∑ j ∈ Finset.range (n + 1),
                  (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ)|
                + |(Work.Spaces.Lop^[n]) g θ| := abs_sub _ _
          _ ≤ (∑ j ∈ Finset.range (n + 1),
                (n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j)) + Kg n := by
              linarith

/-! ## The transfer to `FlatW` for a `z`-independent function -/

/-- For a `θ`-only function `g`: a bound on `g` together with bounds on the `D_θ`-iterates of
`∂_θ g` up to order `6` give `FlatW 7 (fun z θ => g θ) C`. -/
lemma flatW_of_theta_only {g : ℝ → ℝ} {C CW CB : ℝ}
    (hW : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ CW)
    (hB : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (deriv g) θ| ≤ CB)
    (hC0 : 0 ≤ C) (hWle : CW ≤ C) (hBle : CB ≤ C) :
    Work.FTS.VocabO2.FlatW 7 (fun z θ => g θ) C := by
  intro z θ hz hθ hθ2
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases k with _ | k
    · simpa using le_trans (hW θ hθm) hWle
    · rw [Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ g k]
      simp only [mul_zero, abs_zero]
      exact hC0
  · intro k i hki
    have hpth : Work.Spaces.pth (fun z θ => g θ) = fun _ θ => deriv g θ := by
      funext z θ
      rfl
    rcases k with _ | k
    · have hi : i ≤ 6 := by omega
      rw [hpth, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only (deriv g) i]
      simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
      exact le_trans (hB i hi θ hθm) hBle
    · rw [hpth, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only (deriv g) i,
        Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ (Work.Spaces.dthU^[i] (deriv g)) k]
      simp only [mul_zero, abs_zero]
      exact hC0

/-! ## The main theorem -/

theorem FlatW_psiDiv : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.PhiStar.AngModel α ψ →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => ψ θ / Work.Construction.s2 θ) C := by
  obtain ⟨K, hK0, hKgam, hKA⟩ := LopAuxBounds
  have hKd : (0 : ℝ) ≤ ∑ i ∈ Finset.range 7, LopBd K K 500 i :=
    Finset.sum_nonneg fun i _ => LopBdAux_nonneg (by norm_num) hK0 hK0 6 i
  refine ⟨(∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1, ?_, ?_⟩
  · have h2 : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
    linarith
  · intro α ψ hα hα4 hang
    -- the honest `C^∞`-smoothness of `ψ` on the open interval
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      hang.smooth.of_le (by
        rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
        exact_mod_cast le_top)
    have hψeq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ :=
      fun θ hθ => hang.eq θ hθ
    -- smoothness of the divided profile on the open interval
    have hWsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' : ℝ => ψ θ' / Real.sin (2 * θ'))
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro n
      have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      exact (hsm n).div hsin (fun t ht => ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
          (by linarith [ht.2, Real.pi_pos])))
    -- (1) the first-order equation for the derivative of the divided profile
    have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Spaces.Lop (Pdiv ψ) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * Pdiv ψ θ
          - Work.FTS.VocabO.GamBar α θ :=
      PsiDivS2Ode hsm hψeq
    -- (2) the first integral is constant
    have hderivzero : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) θ = 0 :=
      DerivConstPhi (le_of_lt hα) hsm (PsiDivS2Ode hsm hψeq)
    have hdiffh : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) θ := by
      have hdw : ContDiffOn ℝ 1 (deriv (Wdiv ψ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hWsm 2).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      have hsc : ContDiffOn ℝ 1 (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3)
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have hG : ContDiffOn ℝ 1 (Work.FTS.PhiStar.Gzero α) (Set.Ioo 0 (Real.pi / 2)) :=
        (contDiffOn_Gzero α (le_of_lt hα)).of_le (by norm_num)
      have h1 : ContDiffOn ℝ 1 (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) (Set.Ioo 0 (Real.pi / 2)) :=
        (hsc.mul hdw).sub (hG.div_const 2)
      intro θ hθ
      exact (h1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    obtain ⟨cc, hcc⟩ := exists_const_of_deriv_eq_zero hdiffh hderivzero
    have hconst : ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Real.sin θ ^ 2 * Real.cos θ ^ 3 * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          - Work.FTS.PhiStar.Gzero α θ / 2 = c :=
      ⟨cc, fun θ hθ => hcc θ hθ⟩
    -- (3) the derivative is the explicit regular solution
    have hpfun : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2 :=
      PsiDivS2EqPfun hα hα4 hsm hang.cont hang.bdry0 hconst
    -- (4) the flat bound on the divided profile
    have hdiffW : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => ψ θ' / Real.sin (2 * θ')) θ := by
      intro θ hθ
      exact ((hWsm 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    have hWb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ / Real.sin (2 * θ)| ≤ 500 * Real.pi :=
      Wdiv_bound hα hα4 hang.moment hang.bdry0 hang.bdry1 hdiffW hpfun
    -- (5) the `D_θ`-bounds for the derivative
    have hsmP : ∀ n : ℕ, ContDiffOn ℝ n (Pdiv ψ) (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      (hWsm (n + 1)).deriv_of_isOpen isOpen_Ioo (m := n) (by simp)
    have hsmA : ∀ n : ℕ, ContDiffOn ℝ n
        (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) := fun n => by fun_prop
    have hsmG : ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.VocabO.GamBar α)
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro n
      have hGam : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (contDiffOn_Gam α).of_le (by exact_mod_cast le_top)
      have hsub : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α
          - (5 / 4) * Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hGam.div_const _).sub (by fun_prop)
      exact hsub
    have hrecLop : ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.Lop^[i + 1]) (Pdiv ψ) θ
          = (∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j])
                (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ
                * (Work.Spaces.Lop^[j]) (Pdiv ψ) θ))
            - (Work.Spaces.Lop^[i]) (Work.FTS.VocabO.GamBar α) θ :=
      LopIterRecursion hsmP hsmA hsmG hode
    have hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Pdiv ψ θ| ≤ 500 := by
      intro θ hθ
      have h1 := hpfun θ hθ
      have h2 := Pfun_div_sin_sq_le α hα hα4 (θ := θ)
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [show Pdiv ψ θ = deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ from rfl, h1]
      exact h2
    have hLopBd : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i]) (Pdiv ψ) θ| ≤ LopBd K K 500 i :=
      LopBdAux_bound (M := 500) (Ka := K) (Kg := K) (by norm_num) hMf hK0 hK0 hKA
        (hKgam α hα hα4) hrecLop 6 le_rfl
    -- (6) the transfer
    have hCBle : (∑ i ∈ Finset.range 7, LopBd K K 500 i)
        ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by
      have : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
      linarith
    have hCWle : 500 * Real.pi
        ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by linarith [hKd]
    have hC0 : (0 : ℝ) ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by
      have h2 : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
      linarith
    have hB : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i]) (deriv (Wdiv ψ)) θ|
          ≤ ∑ i ∈ Finset.range 7, LopBd K K 500 i := by
      intro i hi θ hθ
      have hmem : i ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
      exact le_trans (hLopBd i hi θ hθ)
        (Finset.single_le_sum (fun j _ => LopBdAux_nonneg (by norm_num) hK0 hK0 6 j) hmem)
    have hFlat := flatW_of_theta_only (g := Wdiv ψ) (CW := 500 * Real.pi)
      (CB := ∑ i ∈ Finset.range 7, LopBd K K 500 i) hWb hB hC0 hCWle hCBle
    simpa only [Wdiv, Work.Construction.s2] using hFlat

end Work.FTS.PhiStar
