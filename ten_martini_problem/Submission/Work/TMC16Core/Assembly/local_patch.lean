import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.poisson_bound
import Submission.Work.TMC16Core.Assembly.RegWin

/-!
# `local_patch`: the localised Poisson iteration of AJ §9.1

This is the local patching/decay estimate used by the glue of component C16.  Given a formal
solution `u` of the almost Mathieu equation `H u = E u`, a "zone" `[a,b]` on which every site
is `(γ,g)`-regular in the sense of `RegWin` with a window of at most `D` sites, and an a priori
bound `‖u‖ ≤ M` on the enlarged zone `[a-D-1, b+D+1]`, one gets, for every `n : ℕ`,

`‖u y‖ ≤ M · 2ⁿ · exp (-(γ · min (d(y) - n) (n·g)))`,   `d(y) = min (y-a) (b-y) + 1`.

The proof is the induction described in `C16_CLOSE_LEAD` (L4): expand `u y` through the Poisson
formula `u y = -G(y,x₁) u(x₁-1) - G(y,x₂) u(x₂+1)` on the regularity window, and iterate on the
two exit sites, which either leave the zone (and are then controlled by `hM`) or lie inside it
(and are then controlled by the induction hypothesis, at a smaller value of `d`, the deficit
being paid for by the margin `g`).
-/

namespace Work.TMC16Core.Assembly

/-- One patching step, **inside** case: the exit site lies in the zone, so the induction
hypothesis applies.  The deficit `d - 1 - gap` of the level function at the exit site is paid
for by the Green decay `exp (-(γ·gap))`. -/
private lemma patch_exp_in {γ g d dz gap uz M : ℝ} {n : ℕ}
    (hM : 0 ≤ M) (hγ : 0 < γ) (hgap : g ≤ gap) (hdz : d - 1 - gap ≤ dz)
    (huz : uz ≤ M * 2 ^ n * Real.exp (-(γ * min (dz - (n : ℝ)) ((n : ℝ) * g)))) :
    Real.exp (-(γ * gap)) * uz ≤
      M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hMn : (0 : ℝ) ≤ M * 2 ^ n := mul_nonneg hM h2n
  have hkey : min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤
      gap + min (dz - (n : ℝ)) ((n : ℝ) * g) := by
    rw [add_comm gap, ← min_add_add_right]
    apply le_min
    · have h : min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤ d - ((n : ℝ) + 1) :=
        min_le_left _ _
      linarith
    · have h : min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤ ((n : ℝ) + 1) * g :=
        min_le_right _ _
      nlinarith
  have hexp : Real.exp (-(γ * gap)) * Real.exp (-(γ * min (dz - (n : ℝ)) ((n : ℝ) * g))) ≤
      Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul : γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤
        γ * gap + γ * min (dz - (n : ℝ)) ((n : ℝ) * g) := by
      have h := mul_le_mul_of_nonneg_left hkey (le_of_lt hγ)
      rw [mul_add] at h
      exact h
    linarith
  calc Real.exp (-(γ * gap)) * uz
      ≤ Real.exp (-(γ * gap)) *
          (M * 2 ^ n * Real.exp (-(γ * min (dz - (n : ℝ)) ((n : ℝ) * g)))) :=
        mul_le_mul_of_nonneg_left huz (Real.exp_nonneg _)
    _ = M * 2 ^ n *
          (Real.exp (-(γ * gap)) * Real.exp (-(γ * min (dz - (n : ℝ)) ((n : ℝ) * g)))) := by
        ring
    _ ≤ M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) :=
        mul_le_mul_of_nonneg_left hexp hMn

/-- One patching step, **outside** case: the exit site leaves the zone and is controlled by the
a priori bound `M`.  Then the margin `d - 1 ≤ gap` is all that is needed, since
`min (d - (n+1)) ((n+1)·g) ≤ d - 1 ≤ gap`. -/
private lemma patch_exp_out {γ g d gap uz M : ℝ} {n : ℕ}
    (hM : 0 ≤ M) (hγ : 0 < γ) (hd : d - 1 ≤ gap) (huz : uz ≤ M) :
    Real.exp (-(γ * gap)) * uz ≤
      M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hgap' : min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤ gap := by
    have h : min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g) ≤ d - ((n : ℝ) + 1) :=
      min_le_left _ _
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hE : 0 ≤ Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) :=
    Real.exp_nonneg _
  have hexp : Real.exp (-(γ * gap)) ≤
      Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hgap' (le_of_lt hγ)
    linarith
  calc Real.exp (-(γ * gap)) * uz
      ≤ Real.exp (-(γ * gap)) * M := mul_le_mul_of_nonneg_left huz (Real.exp_nonneg _)
    _ ≤ Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) * M :=
        mul_le_mul_of_nonneg_right hexp hM
    _ ≤ M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
        have h2 : Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g)))
            ≤ 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
          calc Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g)))
              = 1 * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
                rw [one_mul]
            _ ≤ 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) :=
                mul_le_mul_of_nonneg_right h2n hE
        calc Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) * M
            ≤ (2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g)))) * M :=
              mul_le_mul_of_nonneg_right h2 hM
          _ = M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
              ring

/-- Dispatcher for one term of the Poisson expansion: given the Green bound at rate `γ` over a
gap `gap`, and either the a priori bound (`d - 1 ≤ gap` and `uz ≤ M`) or the induction
hypothesis at a deeper level (`d - 1 - gap ≤ dz`), the product is bounded by
`M · 2ⁿ · exp (-(γ · min (d - (n+1)) ((n+1)·g)))`. -/
private lemma patch_term {γ g d dz gap Gz uz M : ℝ} {n : ℕ}
    (hM : 0 ≤ M) (hγ : 0 < γ) (huz0 : 0 ≤ uz) (hgap : g ≤ gap)
    (hGz : Gz ≤ Real.exp (-(γ * gap)))
    (huz : (d - 1 ≤ gap ∧ uz ≤ M) ∨
      (d - 1 - gap ≤ dz ∧
        uz ≤ M * 2 ^ n * Real.exp (-(γ * min (dz - (n : ℝ)) ((n : ℝ) * g))))) :
    Gz * uz ≤ M * 2 ^ n * Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) := by
  refine le_trans (mul_le_mul_of_nonneg_right hGz huz0) ?_
  rcases huz with ⟨hd1, huzM⟩ | ⟨hdz, huzE⟩
  · exact patch_exp_out hM hγ hd1 huzM
  · exact patch_exp_in hM hγ hgap hdz huzE

theorem local_patch {α lam θ : ℝ} {E : ℂ} {u : ℤ → ℂ} {a b : ℤ} {γ g M : ℝ} {D : ℕ}
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u)
    (hγ : 0 < γ) (hg : 1 ≤ g) (hM0 : 0 ≤ M)
    (hM : ∀ z : ℤ, a - (D : ℤ) - 1 ≤ z → z ≤ b + (D : ℤ) + 1 → ‖u z‖ ≤ M)
    (hreg : ∀ y : ℤ, a ≤ y → y ≤ b → ∃ K : ℕ, K ≤ D ∧ Work.TMC16Core.Assembly.RegWin α lam θ E γ g K y) :
    ∀ (n : ℕ) (y : ℤ), a ≤ y → y ≤ b →
      ‖u y‖ ≤ M * 2 ^ n * Real.exp (-(γ * min
        ((((min (y - a) (b - y) : ℤ) : ℝ) + 1) - (n : ℝ)) ((n : ℝ) * g))) := by
  intro n
  induction n with
  | zero =>
      intro y ha hyb
      have hmin : min ((((min (y - a) (b - y) : ℤ) : ℝ) + 1) - ((0 : ℕ) : ℝ))
          (((0 : ℕ) : ℝ) * g) = 0 := by
        rw [Nat.cast_zero, sub_zero, zero_mul]
        apply min_eq_right
        have hz : (0 : ℤ) ≤ min (y - a) (b - y) := le_min (by omega) (by omega)
        have h : (0 : ℝ) ≤ ((min (y - a) (b - y) : ℤ) : ℝ) := by exact_mod_cast hz
        linarith
      rw [hmin]
      simpa using hM y (by omega) (by omega)
  | succ n ih =>
      intro y ha hyb
      set d : ℝ := ((min (y - a) (b - y) : ℤ) : ℝ) + 1 with hddef
      push_cast
      set Ee : ℝ := Real.exp (-(γ * min (d - ((n : ℝ) + 1)) (((n : ℝ) + 1) * g))) with hEedef
      obtain ⟨K, hKD, hK⟩ := hreg y ha hyb
      obtain ⟨x₁, hx1y, hyx2, hgap1, hgap2, hdet, hG1, hG2⟩ := hK
      have hKD' : (K : ℤ) ≤ (D : ℤ) := by exact_mod_cast hKD
      have hdet' : (dirMat α lam (θ + (x₁ : ℝ) * α) E
          ((x₁ + (K : ℤ) - 1 - x₁ + 1).toNat)).det ≠ 0 := by
        have h1 : x₁ + (K : ℤ) - 1 - x₁ + 1 = (K : ℤ) := by ring
        rw [h1, Int.toNat_natCast]
        exact hdet
      have hp := Work.TMC16Core.Basic.poisson_bound (α := α) (lam := lam) (θ := θ) (E := E)
        (u := u) (x₁ := x₁) (x₂ := x₁ + (K : ℤ) - 1) (y := y) hsol hdet' hx1y hyx2
      -- ## left term
      have hA : ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y x₁‖ * ‖u (x₁ - 1)‖ ≤ M * 2 ^ n * Ee := by
        have ht := patch_term (d := d) (dz := ((min (x₁ - 1 - a) (b - (x₁ - 1)) : ℤ) : ℝ) + 1)
          (gap := ((y - x₁ : ℤ) : ℝ))
          (Gz := ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y x₁‖)
          (uz := ‖u (x₁ - 1)‖) (γ := γ) (g := g) (M := M) (n := n)
          hM0 hγ (norm_nonneg _) hgap1 (le_of_lt hG1) (by
            by_cases hz : a ≤ x₁ - 1 ∧ x₁ - 1 ≤ b
            · right
              refine ⟨?_, ih (x₁ - 1) hz.1 hz.2⟩
              rw [hddef]
              have h : (min (y - a) (b - y) - (y - x₁) - 1 : ℤ) ≤
                  min (x₁ - 1 - a) (b - (x₁ - 1)) := by omega
              have h' : ((min (y - a) (b - y) - (y - x₁) - 1 : ℤ) : ℝ)
                  ≤ ((min (x₁ - 1 - a) (b - (x₁ - 1)) : ℤ) : ℝ) := by exact_mod_cast h
              push_cast at h' ⊢
              linarith
            · left
              refine ⟨?_, hM (x₁ - 1) ?_ ?_⟩
              · rw [hddef]
                have hle : x₁ - 1 ≤ b := by omega
                have hnle : ¬ (a ≤ x₁ - 1) := fun h => hz ⟨h, hle⟩
                have h : min (y - a) (b - y) ≤ y - x₁ := by omega
                have h' : ((min (y - a) (b - y) : ℤ) : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) :=
                  by exact_mod_cast h
                linarith
              · omega
              · omega)
        rw [← hEedef] at ht
        exact ht
      -- ## right term
      have hB : ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y (x₁ + (K : ℤ) - 1)‖
          * ‖u ((x₁ + (K : ℤ) - 1) + 1)‖ ≤ M * 2 ^ n * Ee := by
        have ht := patch_term (d := d)
          (dz := ((min ((x₁ + (K : ℤ) - 1) + 1 - a) (b - ((x₁ + (K : ℤ) - 1) + 1)) : ℤ) : ℝ) + 1)
          (gap := ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ))
          (Gz := ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y (x₁ + (K : ℤ) - 1)‖)
          (uz := ‖u ((x₁ + (K : ℤ) - 1) + 1)‖) (γ := γ) (g := g) (M := M) (n := n)
          hM0 hγ (norm_nonneg _) hgap2 (le_of_lt hG2) (by
            by_cases hz : a ≤ (x₁ + (K : ℤ) - 1) + 1 ∧ (x₁ + (K : ℤ) - 1) + 1 ≤ b
            · right
              refine ⟨?_, ih ((x₁ + (K : ℤ) - 1) + 1) hz.1 hz.2⟩
              rw [hddef]
              have h : (min (y - a) (b - y) - (x₁ + (K : ℤ) - 1 - y) - 1 : ℤ) ≤
                  min ((x₁ + (K : ℤ) - 1) + 1 - a) (b - ((x₁ + (K : ℤ) - 1) + 1)) := by omega
              have h' : ((min (y - a) (b - y) - (x₁ + (K : ℤ) - 1 - y) - 1 : ℤ) : ℝ)
                  ≤ ((min ((x₁ + (K : ℤ) - 1) + 1 - a)
                        (b - ((x₁ + (K : ℤ) - 1) + 1)) : ℤ) : ℝ) := by exact_mod_cast h
              push_cast at h' ⊢
              linarith
            · left
              refine ⟨?_, hM ((x₁ + (K : ℤ) - 1) + 1) ?_ ?_⟩
              · rw [hddef]
                have hge : a ≤ (x₁ + (K : ℤ) - 1) + 1 := by omega
                have hnle : ¬ ((x₁ + (K : ℤ) - 1) + 1 ≤ b) := fun h => hz ⟨hge, h⟩
                have h : min (y - a) (b - y) ≤ x₁ + (K : ℤ) - 1 - y := by omega
                have h' : ((min (y - a) (b - y) : ℤ) : ℝ) ≤ ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ) :=
                  by exact_mod_cast h
                linarith
              · omega
              · omega)
        rw [← hEedef] at ht
        exact ht
      have hsum : M * 2 ^ n * Ee + M * 2 ^ n * Ee = M * 2 ^ (n + 1) * Ee := by
        rw [pow_succ]; ring
      exact le_trans hp (le_trans (add_le_add hA hB) (le_of_eq hsum))

end Work.TMC16Core.Assembly
