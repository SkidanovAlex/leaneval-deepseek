import Mathlib
import Submission.Work.WilG5.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG5.Cell

/-- The open unit cube is open in the product topology. -/
lemma isOpen_openCube (μ : ℕ) : IsOpen (WilkiesDesign.openCube μ) := by
  have h : WilkiesDesign.openCube μ =
      ⋂ i : Fin μ, {x : Fin μ → ℝ | x i ∈ Set.Ioo (0:ℝ) 1} := by
    ext x; simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

/-- Clause 5 of a `CellPar` datum says the free coordinates `y ∘ e` of a point `y ∈ κ` lie in the
open `d`-cube; clause 6 then says the parametrisation is locally surjective with `v` ranging over
the *whole* open cube.  Joining the full open neighbourhood in the free coordinates with the
fixed coordinates obtained by extending a nearby point of `ℝ^m` (using the injection `f` into the
free indices `e`) yields: the projection of `κ` to any `m` of its free coordinates is open around
every projected point, so its interior is nonempty. -/
theorem cellpar_proj_interior {n d m : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n}
    {R : Set (Fin (d + n) → ℝ)} (hpar : Work.WilG5.CellPar n κ d e R) (hne : κ.Nonempty)
    (f : Fin m ↪ Fin d) :
    (interior ((fun x : Fin n → ℝ => fun i : Fin m => x (e (f i))) '' κ)).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  -- the free coordinates of `y` lie in the open `d`-cube
  have hu : (fun i : Fin d => y (e i)) ∈ WilkiesDesign.openCube d :=
    hpar.2.2.2.2.1 y hy
  -- hence the projection `p` of `y` lies in the open `m`-cube
  have hp_cube : (fun i : Fin m => y (e (f i))) ∈ WilkiesDesign.openCube m :=
    fun i => hu (f i)
  -- a sup-metric ball around `p` contained in the open `m`-cube
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    (Metric.isOpen_iff.1 (isOpen_openCube m)) (fun i => y (e (f i))) hp_cube
  -- clause 6 with tolerance `1`: a uniform `ε` around `y ∘ e`
  obtain ⟨ε, hε_pos, hε⟩ := hpar.2.2.2.2.2 y hy 1 one_pos
  set δ : ℝ := min ε ρ with hδ
  have hδ_pos : 0 < δ := lt_min hε_pos hρ_pos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδρ : δ ≤ ρ := min_le_right _ _
  -- the ball of radius `δ` around `p` is contained in the image of `κ`
  have hball_sub : Metric.ball (fun i : Fin m => y (e (f i))) δ ⊆
      (fun x : Fin n → ℝ => fun i : Fin m => x (e (f i))) '' κ := by
    intro w hw
    rw [Metric.mem_ball] at hw
    have hw_dist_lt : ∀ j : Fin m, dist (w j) (y (e (f j))) < δ := by
      intro j
      have h := dist_le_pi_dist w (fun i : Fin m => y (e (f i))) j
      linarith
    have hw_cube : w ∈ WilkiesDesign.openCube m :=
      hρ (Metric.mem_ball.2 (lt_of_lt_of_le hw hδρ))
    -- extend `w` to a point `v` of the open `d`-cube, agreeing with `w` on `e ∘ f`
    set v : Fin d → ℝ :=
      fun i => if h : ∃ j : Fin m, f j = i then w h.choose else y (e i) with hv
    have hv_apply : ∀ j : Fin m, v (f j) = w j := by
      intro j
      have hex : ∃ j' : Fin m, f j' = f j := ⟨j, rfl⟩
      simp only [hv]
      rw [dite_eq_left hex]
      exact congrArg w (f.injective (Classical.choose_spec hex))
    have hv_cube : v ∈ WilkiesDesign.openCube d := by
      intro i
      simp only [hv]
      by_cases h : ∃ j : Fin m, f j = i
      · rw [dite_eq_left h]; exact hw_cube (Classical.choose h)
      · rw [dite_eq_right h]; exact hu i
    have hv_close : ∀ i : Fin d, |v i - y (e i)| < ε := by
      intro i
      simp only [hv]
      by_cases h : ∃ j : Fin m, f j = i
      · rw [dite_eq_left h]
        have hh := hw_dist_lt (Classical.choose h)
        rw [Real.dist_eq] at hh
        have h2 : y (e (f (Classical.choose h))) = y (e i) :=
          congrArg (fun k => y (e k)) (Classical.choose_spec h)
        rw [h2] at hh
        linarith
      · rw [dite_eq_right h]
        simp only [sub_self, abs_zero]
        exact hε_pos
    -- clause 6 produces a point `z ∈ κ` with the prescribed free coordinates `v`
    obtain ⟨z, hzR, _, hzfree⟩ := hε v hv_cube hv_close
    have hzκ : z ∈ κ := hpar.1 v hv_cube z hzR
    refine ⟨z, hzκ, ?_⟩
    funext i
    change z (e (f i)) = w i
    rw [hzfree (f i), hv_apply i]
  -- the ball is open and nonempty, so the interior is nonempty
  refine ⟨(fun i : Fin m => y (e (f i))), interior_maximal hball_sub Metric.isOpen_ball ?_⟩
  rw [Metric.mem_ball, dist_self]
  exact hδ_pos

end Work.WilG5.Cell
