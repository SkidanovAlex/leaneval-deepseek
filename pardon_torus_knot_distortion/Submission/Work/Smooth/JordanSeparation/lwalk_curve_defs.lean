import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic

/-!
# The polygon of a lattice walk as a continuous periodic curve

`LWalk.polyG` is the polygon of a lattice walk `W`, parametrised affinely over `[0, W.n]`;
`LWalk.polyF` is the same parametrised over `[0, 2π]`; `LWalk.curve` is the resulting
`2π`-periodic continuous curve, built with `AddCircle.liftIco`.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- The period `2π` is positive (as a `Fact`, so that the `AddCircle` API applies). -/
instance fact_two_pi_pos : Fact (0 < 2 * (Real.pi : ℝ)) := ⟨by positivity⟩

namespace LWalk

/-- The parameter `u` clamped to `[0, W.n]`. -/
def cl (W : LWalk) (u : ℝ) : ℝ := max 0 (min u (W.n : ℝ))

theorem cl_nonneg {W : LWalk} (u : ℝ) : 0 ≤ W.cl u := le_max_left _ _

theorem cl_le {W : LWalk} (u : ℝ) : W.cl u ≤ (W.n : ℝ) :=
  max_le (Nat.cast_nonneg _) (min_le_right _ _)

/-- The polygon of the walk, parametrised affinely over `[0, W.n]`. -/
def polyG (W : LWalk) (u : ℝ) : ℂ :=
  W.pt (Nat.floor (W.cl u)) +
    (((W.cl u) - (Nat.floor (W.cl u)) : ℝ) : ℂ) *
      (W.pt (min (Nat.floor (W.cl u) + 1) W.n) - W.pt (Nat.floor (W.cl u)))

theorem polyG_zero {W : LWalk} : W.polyG 0 = W.pt 0 := by
  have h0 : W.cl 0 = 0 := by simp [cl]
  have hf : Nat.floor (0 : ℝ) = 0 := by simp
  simp [polyG, h0, hf]

theorem polyG_n {W : LWalk} : W.polyG (W.n : ℝ) = W.pt 0 := by
  have h0 : W.cl (W.n : ℝ) = (W.n : ℝ) := by simp [cl]
  have hfl : Nat.floor ((W.n : ℝ)) = W.n := Nat.floor_natCast W.n
  rw [polyG, h0, hfl]
  simp [W.pt_last]

theorem polyG_eq_of_mem_Icc {W : LWalk} {k : ℕ} (hk : k < W.n) {u : ℝ}
    (hu : u ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    W.polyG u = W.pt k + ((u - (k : ℝ) : ℝ) : ℂ) * (W.pt (k + 1) - W.pt k) := by
  have hk1 : k + 1 ≤ W.n := hk
  have hcl : W.cl u = u := by
    rw [cl]
    have h0 : (0 : ℝ) ≤ u := le_trans (Nat.cast_nonneg k) hu.1
    have hupper : u ≤ (W.n : ℝ) := by
      have h : ((k : ℝ) + 1) ≤ (W.n : ℝ) := by exact_mod_cast hk1
      linarith [hu.2]
    rw [min_eq_left hupper, max_eq_right h0]
  rcases lt_or_eq_of_le hu.2 with hlt | heq
  · have hfloor : Nat.floor u = k :=
      Nat.floor_eq_on_Ico (R := ℝ) k u ⟨hu.1, by linarith⟩
    rw [polyG, hcl, hfloor]
    rw [min_eq_left hk1]
  · have hu' : u = (k : ℝ) + 1 := heq
    have hfloor : Nat.floor u = k + 1 := by
      rw [hu', show ((k:ℝ) + 1) = ((k+1:ℕ):ℝ) by push_cast; ring]
      exact Nat.floor_natCast (R := ℝ) (k + 1)
    rw [polyG, hcl, hfloor]
    have hsub : u - ((k + 1 : ℕ) : ℝ) = 0 := by push_cast; linarith
    rw [hsub, Complex.ofReal_zero, zero_mul, add_zero]
    have hk' : u - (k : ℝ) = 1 := by linarith
    rw [hk']
    simp

theorem continuousOn_polyG {W : LWalk} : ContinuousOn W.polyG (Set.Icc 0 (W.n : ℝ)) := by
  have key : ∀ m : ℕ, m ≤ W.n → ContinuousOn W.polyG (Set.Icc (0:ℝ) (m:ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h : Set.Icc (0:ℝ) ((0:ℕ):ℝ) = ({(0:ℝ)} : Set ℝ) := by
        rw [Nat.cast_zero, Set.Icc_self]
      rw [h]
      exact continuousOn_singleton W.polyG 0
    | succ m ih =>
      intro hm
      have hm' : m ≤ W.n := le_trans (Nat.le_succ m) hm
      have hmm : m < W.n := Nat.lt_of_succ_le hm
      rw [← Set.Icc_union_Icc_eq_Icc (show (0:ℝ) ≤ (m:ℝ) by positivity)
        (show (m:ℝ) ≤ ((m+1:ℕ):ℝ) by push_cast; linarith)]
      refine (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨ih hm', ?_⟩
      refine ContinuousOn.congr (f := fun u : ℝ => W.pt m + ((u - (m:ℝ) : ℝ) : ℂ) *
        (W.pt (m+1) - W.pt m)) ?_ (fun u hu => ?_)
      · fun_prop
      · refine W.polyG_eq_of_mem_Icc hmm ?_
        rw [Nat.cast_add, Nat.cast_one] at hu
        exact hu
  exact key W.n le_rfl

/-- The polygon of the walk, parametrised affinely over `[0, 2π]`. -/
def polyF (W : LWalk) (s : ℝ) : ℂ :=
  W.polyG ((W.n : ℝ) * (max 0 (min s (2 * Real.pi))) / (2 * Real.pi))

theorem continuousOn_polyF {W : LWalk} : ContinuousOn W.polyF (Set.Icc 0 (2 * Real.pi)) := by
  refine ContinuousOn.comp (g := W.polyG) W.continuousOn_polyG ?_ ?_
  · fun_prop
  · intro s hs
    simp only [Set.mem_Icc] at hs ⊢
    rw [min_eq_left hs.2, max_eq_right hs.1]
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg W.n) hs.1) hpi.le
    · rw [div_le_iff₀ hpi]
      nlinarith [hs.2, Nat.cast_nonneg (α := ℝ) W.n]

theorem polyF_zero {W : LWalk} : W.polyF 0 = W.pt 0 := by
  simp only [polyF]
  rw [show max 0 (min (0:ℝ) (2*Real.pi)) = 0 from by
    rw [min_eq_left (by positivity : (0:ℝ) ≤ 2*Real.pi), max_eq_right le_rfl]]
  rw [mul_zero, zero_div]
  exact W.polyG_zero

theorem polyF_two_pi {W : LWalk} : W.polyF (2 * Real.pi) = W.pt 0 := by
  simp only [polyF]
  rw [show max 0 (min (2*Real.pi) (2*Real.pi)) = 2*Real.pi from by
    rw [min_self, max_eq_right (by positivity : (0:ℝ) ≤ 2*Real.pi)]]
  rw [mul_div_cancel_right₀ _ (by positivity : (2:ℝ) * Real.pi ≠ 0)]
  exact W.polyG_n

/-- The polygon of the walk, as a `2π`-periodic continuous curve. -/
def curve (W : LWalk) (t : ℝ) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0 W.polyF (t : AddCircle (2 * Real.pi))

theorem continuous_curve {W : LWalk} : Continuous W.curve := by
  have hf : W.polyF 0 = W.polyF (2 * Real.pi) := by
    rw [W.polyF_zero, W.polyF_two_pi]
  have h1 := AddCircle.liftIco_zero_continuous hf W.continuousOn_polyF
  have h2 : Continuous (fun t : ℝ => (t : AddCircle (2 * Real.pi))) :=
    AddCircle.continuous_mk' (2 * Real.pi)
  exact h1.comp h2

theorem periodic_curve {W : LWalk} : Function.Periodic W.curve (2 * Real.pi) := by
  intro t
  show AddCircle.liftIco (2 * Real.pi) 0 W.polyF ((t + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi))
    = AddCircle.liftIco (2 * Real.pi) 0 W.polyF (t : AddCircle (2 * Real.pi))
  rw [AddCircle.coe_add_period (2 * Real.pi) t]

end LWalk

end

end Work.Smooth.JordanSeparation
