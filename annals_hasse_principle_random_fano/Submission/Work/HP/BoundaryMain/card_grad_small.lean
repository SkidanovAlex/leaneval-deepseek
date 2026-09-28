import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.GradDecomp.gradF_decomp
import Submission.Work.HP.GradCount.ncard_int_interval
import Submission.Work.HP.GradCount.ncard_spec_le
import Submission.Work.HP.LatRecurse.ncard_fiber_le
import Submission.Work.HP.Q44Child.ncard_range_le_prod
import Submission.Work.HP.BoundaryMain.bm_defs
import Submission.Work.HP.BoundaryMain.exists_coord_ge
import Submission.Work.HP.BoundaryMain.fiber_ncard_le
import Submission.Work.HP.BoundaryMain.grad_fiber_ncard
import Submission.Work.HP.BoundaryMain.grad_fiber_finite
import Submission.Work.HP.BoundaryMain.ncard_free_box

set_option autoImplicit false

noncomputable section

open Classical Finset

open scoped BigOperators

namespace Work.HP.BoundaryMain

open Work.HP

/-- Coordinate bound for the Euclidean norm of an integer vector. -/
theorem abs_apply_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  have h : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  calc |(v i : ℝ)| = Real.sqrt ((v i : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
    _ = eNorm v := rfl

/-- The pair `(a ∘ smon j, zeroSInt a)` determines `a`. -/
theorem smon_zeroSInt_injective (d n : ℕ) (hd1 : 1 ≤ d) (j : Fin (n + 1)) :
    Function.Injective (fun a : Mon d n → ℤ =>
      ((fun i => a (smon d n hd1 j i)), zeroSInt d n hd1 j a)) := by
  intro a a' h
  funext m
  have h1 : (fun i => a (smon d n hd1 j i)) = (fun i => a' (smon d n hd1 j i)) :=
    congrArg Prod.fst h
  have h2 : zeroSInt d n hd1 j a = zeroSInt d n hd1 j a' := congrArg Prod.snd h
  by_cases hm : m ∈ Sset d n hd1 j
  · simp only [Sset, Set.mem_range] at hm
    obtain ⟨i, hmi⟩ := hm
    have := congrFun h1 i
    rw [← hmi]
    exact this
  · have hza : zeroSInt d n hd1 j a m = a m := by simp only [zeroSInt, hm, ↓reduceIte]
    have hza' : zeroSInt d n hd1 j a' m = a' m := by simp only [zeroSInt, hm, ↓reduceIte]
    have := congrFun h2 m
    rw [hza, hza'] at this
    exact this

/-- **Counting forms with a small gradient at a point, uniformly in the point.** For every point
`y` of norm at least `1/2`, and every fixed `C > 0`, the integer coefficient vectors of norm `≤ A`
whose gradient at `y` has norm at most `C` number at most `O(A^{N-n-1})`, where `N = NN d n` is the
number of degree-`d` monomials in `n+1` variables; the constant is independent of `y`.

(At such a `y` some coordinate satisfies `|y j| ≥ 1/(2√(n+1))`; the `n+1` coefficients of the
special monomials `x_j^{d-1}x_i` are then each confined to an interval of length `O(1)` by the
`n+1` inequalities `‖∇f_a(y)‖ ≤ C`, leaving `N-n-1` free coordinates.)

Useful ingredients already in the workspace: `Work.HP.GradDecomp.gradF_decomp`,
`Work.HP.GradCount.ncard_spec_le`, `Work.HP.GradCount.ncard_int_interval`,
`Work.HP.LatRecurse.ncard_fiber_le`, `Work.HP.Q44Child.ncard_range_le_prod`. -/
theorem card_grad_small (d n : ℕ) (hd : 2 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (y : Fin (n + 1) → ℝ), 1 / 2 ≤ rNorm y → ∀ A : ℝ, 1 ≤ A →
      ((({a : Mon d n → ℤ | eNorm a ≤ A ∧ rNorm (gradVec d n (toR a) y) ≤ C} : Set _).ncard : ℝ)
        ≤ K * A ^ (NN d n - (n + 1))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdRpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set s : ℝ := 1 / (2 * Real.sqrt ((n : ℝ) + 1)) with hs
  have hs_pos : 0 < s := by rw [hs]; positivity
  set m : ℕ := NN d n - (n + 1) with hm
  refine ⟨(2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) * 3 ^ m,
    ?_, ?_⟩
  · have h1 : 0 < 2 * C / s ^ (d - 1) + 2 := by positivity
    have h2 : 0 < 2 * C / ((d : ℝ) * s ^ (d - 1)) + 2 := by
      have : 0 < (d : ℝ) * s ^ (d - 1) := by positivity
      positivity
    positivity
  · intro y hy A hA
    obtain ⟨j, hj⟩ := exists_coord_ge n y hy
    have hjpos : 0 < |y j| := lt_of_lt_of_le hs_pos hj
    have hyj : y j ≠ 0 := abs_pos.mp hjpos
    have hspow : 0 < s ^ (d - 1) := pow_pos hs_pos _
    have hypow : 0 < |y j| ^ (d - 1) := pow_pos hjpos _
    set B : ℝ := (2 * C / |y j| ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * |y j| ^ (d - 1)) + 2)
      with hB
    have hBpos : 0 < B := by
      rw [hB]
      have h1 : 0 < 2 * C / |y j| ^ (d - 1) + 2 := by positivity
      have h2 : 0 < 2 * C / ((d : ℝ) * |y j| ^ (d - 1)) + 2 := by
        have : 0 < (d : ℝ) * |y j| ^ (d - 1) := by positivity
        positivity
      positivity
    set S : Set (Mon d n → ℤ) := {a | eNorm a ≤ A ∧ rNorm (gradVec d n (toR a) y) ≤ C} with hS
    set Φ : (Mon d n → ℤ) → (Fin (n + 1) → ℤ) × (Mon d n → ℤ) :=
      fun a => ((fun i => a (smon d n hd1 j i)), zeroSInt d n hd1 j a) with hΦ
    have hΦinj : Function.Injective Φ := by
      rw [hΦ]; exact smon_zeroSInt_injective d n hd1 j
    -- the fibre bound
    have hfiber : ∀ f : Mon d n → ℤ,
        (({c : Fin (n + 1) → ℤ | (c, f) ∈ Φ '' S} : Set _).ncard : ℝ) ≤ B := by
      intro f
      set Ff : Set (Fin (n + 1) → ℤ) := {c | ∃ a : Mon d n → ℤ,
          rNorm (gradVec d n (toR a) y) ≤ C ∧
          (fun i => a (smon d n hd1 j i)) = c ∧
          zeroSInt d n hd1 j a = f} with hFf
      have hsub : ({c : Fin (n + 1) → ℤ | (c, f) ∈ Φ '' S} : Set _) ⊆ Ff := by
        rintro c ⟨a, haS, hΦa⟩
        rw [hS] at haS
        obtain ⟨_, hgrad⟩ := haS
        refine ⟨a, hgrad, ?_, ?_⟩
        · have := congrArg Prod.fst hΦa
          simpa only [hΦ] using this
        · have := congrArg Prod.snd hΦa
          simpa only [hΦ] using this
      have hfin : Ff.Finite := grad_fiber_finite d n hd1 hd C y j hyj f
      have hle1 : (({c : Fin (n + 1) → ℤ | (c, f) ∈ Φ '' S} : Set _).ncard : ℝ) ≤
          (Ff.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      have hle2 : (Ff.ncard : ℝ) ≤ B := grad_fiber_ncard d n hd1 hd C hC y j hyj f
      exact hle1.trans hle2
    have hmain1 : ((Φ '' S).ncard : ℝ) ≤ B * (((Φ '' S).image Prod.snd).ncard : ℝ) :=
      fiber_ncard_le (Φ '' S) B hfiber
    -- the free part lives in a box
    set Box : Set (Mon d n → ℤ) := {g | (∀ mm, mm ∈ Sset d n hd1 j → g mm = 0) ∧
        (∀ mm, mm ∉ Sset d n hd1 j → |g mm| ≤ (Nat.floor A : ℤ))} with hBox
    have himgsub : (Φ '' S).image Prod.snd ⊆ Box := by
      rintro g ⟨p, hp, hpg⟩
      obtain ⟨a, haS, hpa⟩ := hp
      have haS' : eNorm a ≤ A ∧ rNorm (gradVec d n (toR a) y) ≤ C := by
        rw [hS] at haS; exact haS
      obtain ⟨heNorm, _⟩ := haS'
      rw [← hpg, ← hpa]
      have hval : Prod.snd (Φ a) = zeroSInt d n hd1 j a := rfl
      rw [hval]
      show (∀ mm, mm ∈ Sset d n hd1 j → zeroSInt d n hd1 j a mm = 0) ∧
        (∀ mm, mm ∉ Sset d n hd1 j → |zeroSInt d n hd1 j a mm| ≤ (Nat.floor A : ℤ))
      refine ⟨?_, ?_⟩
      · intro mm hmm; simp only [zeroSInt, hmm, ↓reduceIte]
      · intro mm hmm
        simp only [zeroSInt, hmm, ↓reduceIte]
        have hle : |(a mm : ℝ)| ≤ A := le_trans (abs_apply_le_eNorm a mm) heNorm
        have hnat : (a mm).natAbs ≤ Nat.floor A := by
          apply Nat.le_floor
          rw [Nat.cast_natAbs, Int.cast_abs]
          exact hle
        calc |a mm| = ((a mm).natAbs : ℤ) := (Nat.cast_natAbs (n := a mm) (α := ℤ)).symm
          _ ≤ (Nat.floor A : ℤ) := by exact_mod_cast hnat
    have hbox := ncard_free_box d n hd1 j A hA
    have himgle : (((Φ '' S).image Prod.snd).ncard : ℝ) ≤ (2 * A + 1) ^ m := by
      have h2 : (((Φ '' S).image Prod.snd).ncard : ℝ) ≤ ((Box : Set (Mon d n → ℤ)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard himgsub hbox.1
      exact h2.trans hbox.2
    -- `B` versus its uniform upper bound
    have hBBmax : B ≤ (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) := by
      rw [hB]
      have hsle : s ^ (d - 1) ≤ |y j| ^ (d - 1) :=
        pow_le_pow_left₀ (le_of_lt hs_pos) hj (d - 1)
      have h2C : (0 : ℝ) ≤ 2 * C := by linarith
      have e1 : 2 * C / |y j| ^ (d - 1) + 2 ≤ 2 * C / s ^ (d - 1) + 2 := by
        have := div_le_div_of_nonneg_left h2C hspow hsle
        linarith
      have e2 : 2 * C / ((d : ℝ) * |y j| ^ (d - 1)) + 2 ≤
          2 * C / ((d : ℝ) * s ^ (d - 1)) + 2 := by
        have hdspos : 0 < (d : ℝ) * s ^ (d - 1) := by positivity
        have hdle : (d : ℝ) * s ^ (d - 1) ≤ (d : ℝ) * |y j| ^ (d - 1) :=
          mul_le_mul_of_nonneg_left hsle (le_of_lt hdRpos)
        have := div_le_div_of_nonneg_left h2C hdspos hdle
        linarith
      have h1n : (2 * C / |y j| ^ (d - 1) + 2) ^ n ≤ (2 * C / s ^ (d - 1) + 2) ^ n :=
        pow_le_pow_left₀ (by positivity) e1 n
      exact mul_le_mul h1n e2 (by positivity) (by positivity)
    have hstep1 : (S.ncard : ℝ) ≤ B * (((Φ '' S).image Prod.snd).ncard : ℝ) := by
      rw [Set.ncard_image_of_injective S hΦinj] at hmain1
      exact hmain1
    have hstep2 : B * (((Φ '' S).image Prod.snd).ncard : ℝ) ≤ B * (2 * A + 1) ^ m :=
      mul_le_mul_of_nonneg_left himgle (le_of_lt hBpos)
    have hstep3 : B * (2 * A + 1) ^ m ≤
        (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) *
          (2 * A + 1) ^ m :=
      mul_le_mul_of_nonneg_right hBBmax (by positivity)
    have hstep4 : (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) *
          (2 * A + 1) ^ m ≤
        (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) *
          (3 * A) ^ m := by
      have hbase : 2 * A + 1 ≤ 3 * A := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hbase m) (by positivity)
    calc (S.ncard : ℝ)
        ≤ B * (((Φ '' S).image Prod.snd).ncard : ℝ) := hstep1
      _ ≤ B * (2 * A + 1) ^ m := hstep2
      _ ≤ (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) *
            (2 * A + 1) ^ m := hstep3
      _ ≤ (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) *
            (3 * A) ^ m := hstep4
      _ = (2 * C / s ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * s ^ (d - 1)) + 2) * 3 ^ m
            * A ^ m := by rw [mul_pow]; ring

end Work.HP.BoundaryMain
