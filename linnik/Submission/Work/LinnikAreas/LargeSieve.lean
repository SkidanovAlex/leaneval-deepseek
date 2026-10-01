import Mathlib
import Submission.Work.LinnikAreas.fiber_card_le
import Submission.Work.LinnikAreas.norm_sum_sq_le_card_mul

/-!
# The large sieve inequality for Dirichlet characters (Heath-Brown 1992, §2)

For every `q ≥ 1`, `N ≥ 0` and every sequence `a : ℕ → ℂ`,

`∑_{χ mod q} ‖∑_{n < N} a n · χ(n)‖² ≤ (q + N) · ∑_{n < N} ‖a n‖²`.

The proof runs through the exact orthogonality (Parseval) identity for the Dirichlet characters
mod `q`: writing `g r = ∑_{n < N, n ≡ r mod q} a n` for the fiber of `n ↦ (n : ZMod q)`, one has

`∑_χ ‖∑_r g r · χ r‖² = φ(q) · ∑_{r ∈ (ZMod q)ˣ} ‖g r‖²`,

because the second orthogonality relation `∑_χ χ r · conj(χ s) = φ(q)·[r = s, r unit]` kills all
off-diagonal terms.  The plain Cauchy–Schwarz bound `‖g r‖² ≤ m_r · ∑_{n ≡ r} ‖a n‖²`, with `m_r`
the number of `n < N` congruent to `r`, together with the crude counting estimate `m_r ≤ ⌈N/q⌉`,
then gives `φ(q)·⌈N/q⌉ · ∑_n ‖a n‖² ≤ (q+N) · ∑_n ‖a n‖²`.
-/

namespace Work.LinnikAreas

open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- **The large sieve inequality** for Dirichlet characters mod `q`. -/
theorem LargeSieve (q N : ℕ) [NeZero q] (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.range N, a n * χ (n : ZMod q)‖ ^ 2)
      ≤ ((q : ℝ) + N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  classical
  -- ## The exact orthogonality / Parseval identity for Dirichlet characters mod `q`.
  have hparseval : ∀ f : ZMod q → ℂ,
      (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2)
        = (q.totient : ℝ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), ‖f r‖ ^ 2 := by
    intro f
    -- Second orthogonality relation, in `star` form.
    have horth : ∀ r s : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ r * star (χ s))
        = if r = s ∧ IsUnit r then (q.totient : ℂ) else 0 := by
      intro r s
      by_cases hr : IsUnit r
      · have hiff : (r = s ∧ IsUnit r) ↔ (r = s) := by simp [hr]
        rw [if_congr hiff rfl rfl]
        -- `conj (χ s) = χ⁻¹ s`, then reindex `χ ↦ χ⁻¹`
        have hstep : ∀ χ : DirichletCharacter ℂ q, χ r * star (χ s) = χ r * χ⁻¹ s := by
          intro χ; rw [MulChar.star_apply' χ s]
        rw [Finset.sum_congr rfl (fun χ _ => hstep χ)]
        have hb : (∑ χ : DirichletCharacter ℂ q, χ r * χ⁻¹ s)
            = ∑ χ : DirichletCharacter ℂ q, χ⁻¹ r * χ s :=
          Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
            (Function.Involutive.bijective (fun x : DirichletCharacter ℂ q => inv_inv x))
            (fun χ => χ r * χ⁻¹ s) (fun ψ => ψ⁻¹ r * ψ s) (fun χ => by rw [inv_inv])
        rw [hb]
        -- `χ⁻¹ r = (χ r)⁻¹ = χ r⁻¹` since `r` is a unit
        have hc : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ r = χ r⁻¹ := by
          intro χ
          rw [MulChar.inv_apply_eq_inv']
          apply inv_eq_of_mul_eq_one_right
          rw [← map_mul, ZMod.mul_inv_of_unit r hr, map_one]
        rw [Finset.sum_congr rfl (fun χ _ => by rw [hc χ])]
        exact DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q) hr s
      · rw [if_neg (fun h => hr h.2)]
        refine Finset.sum_eq_zero (fun χ _ => ?_)
        rw [MulChar.map_nonunit χ hr, zero_mul]
    -- `‖z‖²` as the complex number `z * conj z`
    have hpt : ∀ z : ℂ, ((‖z‖^2 : ℝ) : ℂ) = z * star z := by
      intro z
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    -- The complex double sum collapses to the unit-diagonal by `horth`.
    have hmain : (∑ χ : DirichletCharacter ℂ q,
          (∑ r : ZMod q, f r * χ r) * star (∑ r : ZMod q, f r * χ r))
        = (q.totient : ℂ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r),
            ((‖f r‖^2 : ℝ) : ℂ) := by
      calc (∑ χ : DirichletCharacter ℂ q,
            (∑ r : ZMod q, f r * χ r) * star (∑ r : ZMod q, f r * χ r))
          = ∑ χ : DirichletCharacter ℂ q, ∑ r : ZMod q, ∑ s : ZMod q,
              (f r * χ r) * (star (f s) * star (χ s)) := by
            refine Finset.sum_congr rfl (fun χ _ => ?_)
            have hs : star (∑ r : ZMod q, f r * χ r)
                = ∑ s : ZMod q, star (f s) * star (χ s) := by
              rw [star_sum]
              exact Finset.sum_congr rfl (fun s _ => by rw [star_mul, mul_comm])
            rw [hs, Finset.sum_mul_sum]
        _ = ∑ r : ZMod q, ∑ s : ZMod q, ∑ χ : DirichletCharacter ℂ q,
              (f r * χ r) * (star (f s) * star (χ s)) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)
        _ = ∑ r : ZMod q, ∑ s : ZMod q,
              f r * star (f s) * (if r = s ∧ IsUnit r then (q.totient : ℂ) else 0) := by
            refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
            rw [Finset.sum_congr rfl (fun χ _ => show (f r * χ r) * (star (f s) * star (χ s))
                  = (f r * star (f s)) * (χ r * star (χ s)) by ring),
              ← Finset.mul_sum, horth r s]
        _ = ∑ r : ZMod q, if IsUnit r then f r * star (f r) * (q.totient : ℂ) else 0 := by
            refine Finset.sum_congr rfl (fun r _ => ?_)
            by_cases hr : IsUnit r
            · rw [if_pos hr]
              rw [Finset.sum_eq_single r
                (fun s _ hs => by rw [if_neg (fun h => hs h.1.symm), mul_zero])
                (fun h => absurd (Finset.mem_univ r) h)]
              simp [hr]
            · rw [if_neg hr]
              refine Finset.sum_eq_zero (fun s _ => ?_)
              rw [if_neg (fun h => hr h.2), mul_zero]
        _ = ∑ r ∈ Finset.univ.filter (fun r => IsUnit r),
              f r * star (f r) * (q.totient : ℂ) := by
            rw [Finset.sum_filter]
        _ = (q.totient : ℂ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), f r * star (f r) := by
            rw [← Finset.sum_mul, mul_comm]
        _ = (q.totient : ℂ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r),
              ((‖f r‖^2 : ℝ) : ℂ) := by
            congr 1
            exact Finset.sum_congr rfl (fun r _ => (hpt (f r)).symm)
    have hcast : ((∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2 : ℝ) : ℂ)
        = ∑ χ : DirichletCharacter ℂ q,
            (∑ r : ZMod q, f r * χ r) * star (∑ r : ZMod q, f r * χ r) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun χ _ => hpt _)
    refine Complex.ofReal_injective ?_
    rw [hcast, hmain, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  -- ## Fiber decomposition of the ℕ-indexed character sum.
  set g : ZMod q → ℂ :=
    fun r => ∑ n ∈ (Finset.range N).filter (fun n : ℕ => ((n:ℕ) : ZMod q) = r), a n with hg
  set W : ZMod q → ℝ :=
    fun r => ∑ n ∈ (Finset.range N).filter (fun n : ℕ => ((n:ℕ) : ZMod q) = r), ‖a n‖ ^ 2
    with hW
  set cnt : ZMod q → ℕ :=
    fun r => ((Finset.range N).filter (fun n : ℕ => ((n:ℕ) : ZMod q) = r)).card with hcnt
  have hfib : ∀ χ : DirichletCharacter ℂ q,
      (∑ n ∈ Finset.range N, a n * χ (n : ZMod q)) = ∑ r : ZMod q, g r * χ r := by
    intro χ
    have key : (∑ n ∈ Finset.range N, a n * χ (n : ZMod q))
        = ∑ r : ZMod q,
            (∑ n ∈ (Finset.range N).filter (fun n : ℕ => ((n:ℕ) : ZMod q) = r), a n) * χ r := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range N) (t := Finset.univ)
          (g := fun n : ℕ => ((n : ℕ) : ZMod q)) (f := fun n => a n * χ (n : ZMod q))
          (fun i _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2])
    simpa [hg] using key
  have hcomput : (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.range N, a n * χ (n : ZMod q)‖ ^ 2)
      = (q.totient : ℝ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), ‖g r‖ ^ 2 := by
    simp_rw [hfib]
    exact hparseval g
  rw [hcomput]
  have hWnn : ∀ r, 0 ≤ W r := by
    intro r; rw [hW]; exact Finset.sum_nonneg (fun n _ => by positivity)
  -- ## Cauchy–Schwarz on each residue class.
  have hg_le : ∀ r, ‖g r‖ ^ 2 ≤ (cnt r : ℝ) * W r := by
    intro r
    have := norm_sum_sq_le_card_mul ((Finset.range N).filter (fun n : ℕ => ((n:ℕ) : ZMod q) = r)) a
    simpa [hg, hW, hcnt] using this
  have hqne : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  -- ## The counting bound `φ(q) · m_r ≤ q + N`.
  have hphi_m : ∀ r, (q.totient : ℝ) * (cnt r : ℝ) ≤ (q : ℝ) + (N : ℝ) := by
    intro r
    have h1 : (cnt r : ℝ) ≤ (((N + q - 1) / q : ℕ) : ℝ) := by
      rw [hcnt]; exact_mod_cast fiber_card_le q N r
    have h2 : (((N + q - 1) / q : ℕ) : ℝ) ≤ ((N + q - 1 : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    have h3 : ((N + q - 1 : ℕ) : ℝ) ≤ (q : ℝ) + (N : ℝ) := by
      rw [← Nat.cast_add, add_comm q N]; exact_mod_cast Nat.sub_le (N + q) 1
    have h4 : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hc0 : (0:ℝ) ≤ (cnt r : ℝ) := by positivity
    have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
    calc (q.totient : ℝ) * (cnt r : ℝ)
        ≤ (q : ℝ) * (cnt r : ℝ) := mul_le_mul_of_nonneg_right h4 hc0
      _ ≤ (q : ℝ) * ((((N + q - 1) / q : ℕ)) : ℝ) := mul_le_mul_of_nonneg_left h1 hq0
      _ ≤ (q : ℝ) * (((N + q - 1 : ℕ) : ℝ) / (q : ℝ)) := mul_le_mul_of_nonneg_left h2 hq0
      _ = ((N + q - 1 : ℕ) : ℝ) := by rw [mul_comm (q:ℝ)]; exact div_mul_cancel₀ _ hqne
      _ ≤ (q : ℝ) + (N : ℝ) := h3
  have hsum_ext : ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), (cnt r : ℝ) * W r
      ≤ ∑ r : ZMod q, (cnt r : ℝ) * W r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro x _ _
    exact mul_nonneg (by positivity) (hWnn x)
  have hWsum : ∑ r : ZMod q, W r = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
    rw [hW]
    exact (Finset.sum_fiberwise_of_maps_to (s := Finset.range N) (t := Finset.univ)
        (g := fun n : ℕ => ((n : ℕ) : ZMod q)) (f := fun n => ‖a n‖ ^ 2)
        (fun i _ => Finset.mem_univ _))
  -- ## Assembly.
  calc (q.totient : ℝ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), ‖g r‖ ^ 2
      ≤ (q.totient : ℝ) * ∑ r ∈ Finset.univ.filter (fun r => IsUnit r), (cnt r : ℝ) * W r := by
        gcongr with r _
        exact hg_le r
    _ ≤ (q.totient : ℝ) * ∑ r : ZMod q, (cnt r : ℝ) * W r := by
        exact mul_le_mul_of_nonneg_left hsum_ext (by positivity)
    _ = ∑ r : ZMod q, (q.totient : ℝ) * ((cnt r : ℝ) * W r) := by rw [Finset.mul_sum]
    _ ≤ ∑ r : ZMod q, ((q : ℝ) + N) * W r := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hphi_m r) (hWnn r)
    _ = ((q : ℝ) + N) * ∑ r : ZMod q, W r := by rw [Finset.mul_sum]
    _ = ((q : ℝ) + N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by rw [hWsum]

end Work.LinnikAreas
