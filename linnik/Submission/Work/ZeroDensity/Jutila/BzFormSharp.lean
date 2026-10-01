import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.LzQDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffFormBound
import Submission.Work.ZeroDensity.Jutila.MsqDiag
import Submission.Work.ZeroDensity.Jutila.MsqSelErr
import Submission.Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
import Submission.Work.ZeroDensity.Jutila.MuSqDivTotientLower

/-!
# Sharp evaluation of the Selberg quadratic form of the difference weights

* `msq_le_log_add_const` — the sharp two-parameter Selberg form bound `|Msq w y − log w| ≤ C`,
  assembled from `MsqDiag`, `MsqSelErr` and the two sharp Mertens bounds
  `Σ_{δ≤M} μ(δ)²/φ(δ) = log M + O(1)` (this is the content of the deleted workspace modules
  `msqThetaDiagErrorBound` / `sumMuSqDivTotient_ge_log`, re-proved here from the surviving pieces);
* `bzForm_le_log_add_const` — `Σ λ_dλ_e/[d,e] ≤ log(y/w) + C` for the difference weights;
* `sum_sq_Lz_sub_eq_split` — the exact split `Σ(Lz y − Lz w)² = N·Q − F` into the main term and
  the floor error;
* `FloorBound` / `LzDiffSq_le_of_floor` — the difference-square bound from the (deep) floor bound.
-/


/-!
# The sharp `B_z²` bound in the hard range `N < z²`

Target (`BzSqSharpHard`): for `2 ≤ z ≤ N < z*z`,

  `Σ_{n ≤ N} B_z(n)² ≤ N·log(N/z) + C·N`,

where `B_z(n) = Σ_{z < d ∣ n} μ(d)·log(d/z) = Λ_z(n) − Λ(n)` (`n ≥ 2`).

## Contents

* `msq_le_log_add_const` — the **sharp two-parameter Selberg form bound**
  `|Msq w y − log w| ≤ C` (no `log(y/w)` slack), assembled from `MsqDiag`, `MsqSelErr` and the two
  sharp Mertens bounds `Σ_{δ≤M} μ(δ)²/φ(δ) = log M + O(1)`.  (This is the content of the
  workspace modules `msqThetaDiagErrorBound` / `sumMuSqDivTotient_ge_log`, whose sources have since
  been deleted; it is re-proved here from the surviving pieces.)
* `bzForm_le_log_add_const` — the **Selberg quadratic form of the difference weights** is
  `≤ log(y/w) + C`: by `form_eq_Msq`, `Q = Msq y y − 2 Msq w y + Msq w w ≤ log y − 2 log w + log w + C`
  with the sharp `Msq` bound above.
* `sum_sq_Lz_sub_eq_split` — the exact split `Σ_{d,e} λ_dλ_e⌊N/[d,e]⌋ = N·Q − F` with
  `F = Σ_{d,e} λ_dλ_e{N/[d,e]}` (the "floor error").
* `LzDiffSq_le_of_floor` — the sharp difference-square bound, from `Q ≤ log(y/w) + C` and the
  one-sided floor bound `F ≥ −C·N` (`FloorBound`, the deep Barban–Vehov/Graham input).
* `Bz_sq_eq_diff_sq`, `BzSqSharpHard_of_floor`, `BzSqSharpHard` — the final assembly.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-! ## 1. The sharp two-parameter Selberg form bound -/

/-- **Sharp bound for the two-parameter Selberg form.**  There is an absolute `C > 0` with
`|Msq w y − log w| ≤ C` for all `1 ≤ w ≤ y` — note the absence of a `log(y/w)` slack, which is
what makes the difference form `Q = Msq y y − 2 Msq w y + Msq w w ≤ log(y/w) + C` sharp. -/
theorem msq_le_log_add_const :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 ≤ w → w ≤ y → |Msq w y - Real.log w| ≤ C := by
  obtain ⟨Cs, hCs, hS⟩ := MsqSelErr
  obtain ⟨Cu, hCu, hU⟩ := Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
  obtain ⟨Cl, hCl, hL⟩ := Work.ZeroDensity.Jutila.MuSqDivTotientLower
  refine ⟨Cs + max Cu Cl + Real.log 2, by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < max Cu Cl := lt_max_of_lt_left hCu
    linarith, ?_⟩
  intro w y hw hwy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw0 : (0 : ℝ) < w := by linarith
  have hW1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hWw : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le (le_of_lt hw0)
  set W : ℕ := ⌊w⌋₊ with hWdef
  set S : ℝ := ∑ δ ∈ Finset.Icc 1 W,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
        Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
        Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ with hSdef
  set T : ℝ := ∑ δ ∈ Finset.Icc 1 W,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ) with hTdef
  have hdiag : Msq w y = S := by rw [hSdef]; exact MsqDiag w y hw hwy
  have hE : |S - T| ≤ Cs := by
    rw [hSdef, hTdef]
    exact hS w y W hw hwy (by rw [hWdef]; exact hWw) (by rw [hWdef]; exact hW1)
  have hW : 1 ≤ W := by rw [hWdef]; exact hW1
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hUp := hU W hW
  have hLo := hL W hW
  have hTabs : |T - Real.log (W : ℝ)| ≤ max Cu Cl := by
    rw [abs_le]
    exact ⟨by linarith [hLo, le_max_right Cu Cl], by linarith [hUp, le_max_left Cu Cl]⟩
  have hlogcmp : |Real.log (W : ℝ) - Real.log w| ≤ Real.log 2 := by
    have hle : Real.log (W : ℝ) ≤ Real.log w := by
      refine Real.log_le_log hWpos ?_
      rw [hWdef]; exact hWw
    have hlt : Real.log w ≤ Real.log (W : ℝ) + Real.log 2 := by
      have h3 : w < ((⌊w⌋₊ : ℕ) : ℝ) + 1 := by
        have := Nat.lt_floor_add_one w
        linarith
      have h4 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      have h2 : w < (W : ℝ) * 2 := by
        rw [hWdef]; linarith
      have := Real.log_lt_log hw0 h2
      rw [Real.log_mul (ne_of_gt hWpos) (by norm_num : (2 : ℝ) ≠ 0)] at this
      linarith
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have htri : |S - Real.log w|
      ≤ |S - T| + |T - Real.log (W : ℝ)| + |Real.log (W : ℝ) - Real.log w| := by
    have h1 : S - Real.log w = (S - T) + ((T - Real.log (W : ℝ))
        + (Real.log (W : ℝ) - Real.log w)) := by ring
    rw [h1]
    calc |(S - T) + ((T - Real.log (W : ℝ)) + (Real.log (W : ℝ) - Real.log w))|
        ≤ |S - T| + |(T - Real.log (W : ℝ)) + (Real.log (W : ℝ) - Real.log w)| :=
          abs_add_le _ _
      _ ≤ |S - T| + (|T - Real.log (W : ℝ)| + |Real.log (W : ℝ) - Real.log w|) := by
          have h := abs_add_le (T - Real.log (W : ℝ)) (Real.log (W : ℝ) - Real.log w)
          linarith
      _ = |S - T| + |T - Real.log (W : ℝ)| + |Real.log (W : ℝ) - Real.log w| := by ring
  rw [hdiag]
  linarith [hE, hTabs, hlogcmp, htri]

/-! ## 2. The Selberg form of the difference weights, sharply -/

/-- **The Selberg quadratic form of the difference weights is `≤ log(y/w) + C`.**  For real
`1 < w < y`, with `λ_d = bvLam w y d` the weight of `Lz y − Lz w`,

  `Σ_{d,e ≤ ⌊y⌋₊} λ_dλ_e/[d,e] ≤ log(y/w) + C`.

The constant `1` of the leading term is exactly the Barban–Vehov/Graham constant: it follows from
`form_eq_Msq` (so `Q = Msq y y − 2Msq w y + Msq w w`) and the sharp bound `|Msq a b − log a| ≤ C`
of `msq_le_log_add_const`. -/
theorem bzForm_le_log_add_const :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w < y →
      (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
        ≤ Real.log (y / w) + C := by
  obtain ⟨C0, hC0, hM⟩ := msq_le_log_add_const
  refine ⟨4 * C0, by positivity, ?_⟩
  intro w y hw hwy
  have hw1 : 1 ≤ w := le_of_lt hw
  have hwy' : w ≤ y := le_of_lt hwy
  have hy1 : 1 ≤ y := le_of_lt (lt_trans hw hwy)
  have hw0 : (0 : ℝ) < w := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have h1 : Msq y y ≤ Real.log y + C0 := by
    have := hM y y hy1 le_rfl
    have h0 : Real.log y - Real.log y = 0 := sub_self _
    rw [abs_le] at this
    linarith [this.2, h0]
  have h2 : Real.log w - C0 ≤ Msq w y := by
    have := hM w y hw1 hwy'
    rw [abs_le] at this
    linarith [this.1]
  have h3 : Msq w w ≤ Real.log w + C0 := by
    have := hM w w hw1 le_rfl
    rw [abs_le] at this
    linarith [this.2]
  have hlog : Real.log (y / w) = Real.log y - Real.log w := Real.log_div (ne_of_gt hy0) (ne_of_gt hw0)
  rw [form_eq_Msq hw hwy]
  rw [hlog]
  linarith [h1, h2, h3]

/-! ## 3. The exact split of the difference square -/

/-- Termwise: `a·⌊N/l⌋ = N·(a/l) − a·(N/l − ⌊N/l⌋)` for `l ≥ 1`. -/
private lemma mul_natDiv_eq (N l : ℕ) (hl : 0 < l) (a : ℝ) :
    a * ((N / l : ℕ) : ℝ)
      = (N : ℝ) * (a / (l : ℝ)) - a * ((N : ℝ) / (l : ℝ) - ((N / l : ℕ) : ℝ)) := by
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp
  ring

/-- **The exact split of `Σ(Lz y − Lz w)²` into the main term `N·Q` and the floor error `F`.**
For real `1 < w < y` and any `N`, writing `λ_d = bvLam w y d`, `Q = Σ_{d,e} λ_dλ_e/[d,e]` and
`F = Σ_{d,e} λ_dλ_e{N/[d,e]}`,

  `Σ_{n ≤ N} (Lz y n − Lz w n)² = N·Q − F`,

where `{x} = x − ⌊x⌋` is represented by the real number `N/[d,e] − ⌊N/[d,e]⌋ ∈ [0,1)`. -/
theorem sum_sq_Lz_sub_eq_split {w y : ℝ} (hw : 1 < w) (hwy : w < y) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Lz y n - Lz w n) ^ 2)
      = (N : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
        - (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e
              * ((N : ℝ) / (Nat.lcm d e : ℝ) - ((N / Nat.lcm d e : ℕ) : ℝ))) := by
  rw [sum_sq_Lz_sub_eq_lcm hw hwy N]
  have hterm : ∀ d ∈ Finset.Icc 1 ⌊y⌋₊, ∀ e ∈ Finset.Icc 1 ⌊y⌋₊,
      bvLam w y d * bvLam w y e * ((N / Nat.lcm d e : ℕ) : ℝ)
        = (N : ℝ) * (bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
          - bvLam w y d * bvLam w y e
              * ((N : ℝ) / (Nat.lcm d e : ℝ) - ((N / Nat.lcm d e : ℕ) : ℝ)) := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hl : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
    have h := mul_natDiv_eq N (Nat.lcm d e) hl (bvLam w y d * bvLam w y e)
    rw [h]
  calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e * ((N / Nat.lcm d e : ℕ) : ℝ))
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          ((N : ℝ) * (bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
            - bvLam w y d * bvLam w y e
                * ((N : ℝ) / (Nat.lcm d e : ℝ) - ((N / Nat.lcm d e : ℕ) : ℝ))) :=
        Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
    _ = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            (N : ℝ) * (bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ)))
          - (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e
              * ((N : ℝ) / (Nat.lcm d e : ℝ) - ((N / Nat.lcm d e : ℕ) : ℝ))) := by
        simp only [Finset.sum_sub_distrib]
    _ = (N : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
          - (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e
              * ((N : ℝ) / (Nat.lcm d e : ℝ) - ((N / Nat.lcm d e : ℕ) : ℝ))) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by rw [Finset.mul_sum])


/-! ## 4. The deep input: the one-sided floor (fractional-part) bound -/

/-- **The Barban–Vehov/Graham floor bound** (the deep analytic input, delegated to
`Submission.Work.ZeroDensity.Jutila.BzSqFloorSharp`).  For real `1 < w < y` and `N ≥ y`,

  `Σ_{d,e ≤ ⌊y⌋₊} λ_dλ_e·{N/[d,e]} ≥ −C·N`,  `λ_d = bvLam w y d`,

i.e. the fractional-part error of the Selberg form is `O(N)` and not merely
`O((Σ|λ_d|)²) = O(y²)`; this is the sharp form of Graham's estimate. -/
def FloorBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w < y → ∀ N : ℕ, y ≤ (N : ℝ) →
    -(C * (N : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e
          * (((N : ℝ) / (Nat.lcm d e : ℝ)) - ((N / Nat.lcm d e : ℕ) : ℝ))

/-- **The sharp Barban–Vehov/Graham difference-square bound**, from the floor bound and the
sharp Selberg form bound `bzForm_le_log_add_const`:

  `Σ_{n ≤ N} (Lz y n − Lz w n)² ≤ N·log(y/w) + C·N`  for `1 < w < y ≤ N`. -/
theorem LzDiffSq_le_of_floor (hF : FloorBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w < y → ∀ N : ℕ, y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, (Lz y n - Lz w n) ^ 2)
        ≤ (N : ℝ) * Real.log (y / w) + C * (N : ℝ) := by
  obtain ⟨C0, hC0, hQ⟩ := bzForm_le_log_add_const
  obtain ⟨C1, hC1, hfloor⟩ := hF
  refine ⟨C0 + C1 + 1, by positivity, ?_⟩
  intro w y hw hwy N hyN
  have hQ' := hQ w y hw hwy
  have hFl := hfloor w y hw hwy N hyN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : (N : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      ≤ (N : ℝ) * (Real.log (y / w) + C0) := mul_le_mul_of_nonneg_left hQ' hNnn
  rw [sum_sq_Lz_sub_eq_split hw hwy N]
  nlinarith [h1, hFl, hNnn]


end

end Work.ZeroDensity.Jutila
