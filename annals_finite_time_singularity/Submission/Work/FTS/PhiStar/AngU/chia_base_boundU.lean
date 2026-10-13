import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux
import Submission.Work.FTS.PhiStar.LinvFlat.Lop_iter_sin_cos_bound
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.AngU

open scoped Real Topology
open Filter Set

/-- `NbUU Cd Ms b = Cd + ∑_{a<b} C(b-1,a)·Ms·Cd`: the bound produced by the Leibniz expansion of
`Lop^[b] W = Lop^[b-1] (s2 · W')` from `|W'| ≤ Cd` and `|Lop^a s2| ≤ Ms`. -/
private def NbUU (Cd Ms : ℝ) (b : ℕ) : ℝ :=
  Cd + ∑ a ∈ Finset.range b, ((b - 1).choose a : ℝ) * (Ms * Cd)

private lemma NbUU_nonneg {Cd Ms : ℝ} (hCd : 0 ≤ Cd) (hMs : 0 ≤ Ms) (b : ℕ) :
    0 ≤ NbUU Cd Ms b := by
  refine add_nonneg hCd (Finset.sum_nonneg (fun a _ => ?_))
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hMs hCd)

private lemma NbUU_zero (Cd Ms : ℝ) : NbUU Cd Ms 0 = Cd := by
  simp [NbUU]

private lemma NbUU_succ (Cd Ms : ℝ) (b : ℕ) :
    NbUU Cd Ms (b + 1)
      = Cd + ∑ a ∈ Finset.range (b + 1), ((b.choose a : ℝ) * (Ms * Cd)) := by
  simp only [NbUU, Nat.add_sub_cancel]

/-- The `U`-form of `chia_base_bound`: the bounds on `Lop`-iterates of `chia ψ 0` are derived
directly from the hypotheses on `ψ / sin 2θ` and its `Lop`-derivatives, without passing through
`FlatW`. -/
theorem chia_base_boundU (Cd Ms : ℝ) (hCd : 0 ≤ Cd) (hMs : 0 ≤ Ms) :
    ∃ B : ℕ → ℝ, (∀ i : ℕ, 0 ≤ B i) ∧ ∀ (ψ : ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2))) →
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ / Work.Construction.s2 θ| ≤ Cd) →
      (∀ d : ℕ, d ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[d]) (deriv (fun θ' => ψ θ' / Work.Construction.s2 θ')) θ| ≤ Cd) →
      (∀ r : ℕ, r ≤ 6 → ∀ θ : ℝ, |(Work.Spaces.Lop^[r]) Work.Construction.s2 θ| ≤ Ms) →
      ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ| ≤ B i := by
  refine ⟨fun i => ∑ a ∈ Finset.range (i + 1),
      (i.choose a : ℝ) * (Ms * NbUU Cd Ms (i - a)),
    fun i => Finset.sum_nonneg (fun a _ =>
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hMs (NbUU_nonneg hCd hMs _))), ?_⟩
  intro ψ hsm hWbd0 hW'bd0 hMsb
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- the `z`-free angular profile `W = ψ / sin 2θ`
  set W : ℝ → ℝ := fun θ => ψ θ / Work.Construction.s2 θ with hWdef
  -- `sin 2θ > 0` and `s2 ≠ 0` on the open interval
  have hsinpos : ∀ x : ℝ, 0 < x → x < Real.pi / 2 → 0 < Real.sin (2 * x) := by
    intro x hx1 hx2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs2ne : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Construction.s2 x ≠ 0 := by
    intro x hx
    rw [show Work.Construction.s2 x = Real.sin (2 * x) from rfl]
    exact ne_of_gt (hsinpos x hx.1 hx.2)
  -- smoothness of `s2` and of `W` at every order
  have hs2smN : ∀ n : ℕ,
      ContDiffOn ℝ n Work.Construction.s2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro n
    rw [show Work.Construction.s2 = (fun θ : ℝ => Real.sin (2 * θ)) from rfl]
    fun_prop
  have hs2sm : ContDiffOn ℝ 9 Work.Construction.s2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hs2smN 9
  have hWsmN : ∀ n : ℕ, ContDiffOn ℝ n W (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro n
    rw [hWdef]
    exact ContDiffOn.div (hsm n) (hs2smN n) (fun x hx => hs2ne x hx)
  have hWsm : ContDiffOn ℝ 9 W (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hWsmN 9
  have hW'sm : ContDiffOn ℝ 9 (deriv W) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hWsmN 10).deriv_of_isOpen hIoo (by norm_num)
  -- the two inputs, directly from the hypotheses
  have hWbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |W θ| ≤ Cd := by
    intro θ hθ
    simpa only [hWdef] using hWbd0 θ hθ
  have hW'bd : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (deriv W) θ| ≤ Cd := by
    intro i hi θ hθ
    simpa only [hWdef] using hW'bd0 i hi θ hθ
  -- bounds on the `Lop`-iterates of `s2`
  have hMs2 : ∀ a : ℕ, a ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ| ≤ Ms := by
    intro a ha θ _
    exact hMsb a ha θ
  -- bounds on the `Lop`-iterates of `W`, by the Leibniz rule applied to `Lop W = s2 · W'`
  have hLopW : ∀ b : ℕ, b ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[b]) W θ| ≤ NbUU Cd Ms b := by
    intro b hb θ hθ
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      rw [NbUU_zero, Function.iterate_zero_apply]
      exact hWbd θ hθ
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
      have hLeib := Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9 hIoo hs2sm hW'sm b'
        (by omega) hθ
      have heq : (Work.Spaces.Lop^[b' + 1]) W θ
          = ∑ a ∈ Finset.range (b' + 1), ((b'.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) Work.Construction.s2 θ
                * (Work.Spaces.Lop^[b' - a]) (deriv W) θ)) := by
        rw [Function.iterate_succ_apply]
        exact hLeib
      have hmain : |(Work.Spaces.Lop^[b' + 1]) W θ|
          ≤ ∑ a ∈ Finset.range (b' + 1), (b'.choose a : ℝ) * (Ms * Cd) := by
        rw [heq]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun a ha => ?_))
        have ha6 : a ≤ 6 := by
          have := Finset.mem_range.mp ha
          omega
        have hb'a6 : b' - a ≤ 6 := by omega
        have hXY : |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ
            * (Work.Spaces.Lop^[b' - a]) (deriv W) θ| ≤ Ms * Cd := by
          rw [abs_mul]
          exact mul_le_mul (hMs2 a ha6 θ hθ) (hW'bd (b' - a) hb'a6 θ hθ)
            (abs_nonneg _) hMs
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (b'.choose a))]
        exact mul_le_mul_of_nonneg_left hXY (Nat.cast_nonneg _)
      rw [NbUU_succ]
      exact le_trans hmain (le_add_of_nonneg_left hCd)
  -- the main expansion: `Lop^[i] (chia ψ 0) = Lop^[i] (s2 · W)` by Leibniz
  have hchia : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ|
        ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (Ms * NbUU Cd Ms (i - a)) := by
    intro i hi θ hθ
    have hch : Work.FTS.PhiStar.FlatWAux.chia ψ 0 = Work.Construction.s2 * W := by
      rw [Work.FTS.PhiStar.FlatWAux.chia_eq, Work.FTS.PhiStar.FlatWAux.Wt_zero, hWdef]
      rfl
    have hexp : (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ
        = ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℝ) *
            ((Work.Spaces.Lop^[a]) Work.Construction.s2 θ * (Work.Spaces.Lop^[i - a]) W θ)) := by
      rw [hch]
      exact Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9 hIoo hs2sm hWsm i (by omega) hθ
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun a ha => ?_))
    have ha6 : a ≤ 6 := by
      have := Finset.mem_range.mp ha
      omega
    have hia6 : i - a ≤ 6 := by omega
    have hXY : |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ
        * (Work.Spaces.Lop^[i - a]) W θ| ≤ Ms * NbUU Cd Ms (i - a) := by
      rw [abs_mul]
      exact mul_le_mul (hMs2 a ha6 θ hθ) (hLopW (i - a) hia6 θ hθ) (abs_nonneg _) hMs
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose a))]
    exact mul_le_mul_of_nonneg_left hXY (Nat.cast_nonneg _)
  intro i hi θ hθ
  exact hchia i hi θ hθ

end Work.FTS.PhiStar.AngU
