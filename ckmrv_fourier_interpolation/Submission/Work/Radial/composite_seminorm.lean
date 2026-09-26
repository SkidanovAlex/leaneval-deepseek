import Mathlib
import Submission.Work.Radial.Basic
import Submission.Work.Radial.quad_iteratedFDeriv_bound

noncomputable section

namespace Work.Radial

open scoped ContDiff
open Set

/-- Norm bound on the `n`-th term of the Taylor composition of two formal multilinear
series, given uniform bounds on the norms of all terms up to order `n`. -/
lemma norm_taylorComp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (A B : ℝ) (hB : 1 ≤ B)
    (q : FormalMultilinearSeries ℝ ℝ ℂ) (p : FormalMultilinearSeries ℝ E ℝ)
    (hq : ∀ j : ℕ, j ≤ n → ‖q j‖ ≤ A) (hp : ∀ m : ℕ, m ≤ n → ‖p m‖ ≤ B) :
    ‖q.taylorComp p n‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) * A * B ^ n := by
  have heq : q.taylorComp p n
      = ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c := rfl
  rw [heq]
  calc ‖∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c‖
      ≤ ∑ c : OrderedFinpartition n, ‖q.compAlongOrderedFinpartition p c‖ :=
        norm_sum_le Finset.univ _
    _ ≤ ∑ _c : OrderedFinpartition n, A * B ^ n := by
        apply Finset.sum_le_sum
        intro c _
        calc ‖q.compAlongOrderedFinpartition p c‖
            = ‖c.compAlongOrderedFinpartition (q c.length) (fun i => p (c.partSize i))‖ := rfl
          _ ≤ ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ :=
              c.norm_compAlongOrderedFinpartition_le _ _
          _ ≤ A * B ^ n := by
              have h1 : ‖q c.length‖ ≤ A := hq _ c.length_le
              have h2 : ∏ i : Fin c.length, ‖p (c.partSize i)‖ ≤ B ^ n := by
                calc ∏ i : Fin c.length, ‖p (c.partSize i)‖
                    ≤ ∏ _i : Fin c.length, B := by
                      apply Finset.prod_le_prod₀
                      · intro i _; exact norm_nonneg _
                      · intro i _; exact hp _ (c.partSize_le i)
                  _ = B ^ c.length := by
                      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                  _ ≤ B ^ n := pow_le_pow_right₀ hB c.length_le
              exact mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)
    _ = (Fintype.card (OrderedFinpartition n) : ℝ) * (A * B ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (OrderedFinpartition n) : ℝ) * A * B ^ n := by ring

theorem composite_seminorm (n : ℕ) [NeZero n] (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → ℂ) (L : ℝ),
      ContDiffOn ℝ ⊤ Ψ (Set.Ici 0) →
      (∀ j : ℕ, j ≤ l → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ (k + 2 * l) * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖ ≤ L) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x‖ ≤ C * L
    := by
  refine ⟨(4:ℝ)^l * (Fintype.card (OrderedFinpartition l) : ℝ), by positivity, ?_⟩
  intro Ψ L hΨ hL x
  -- `L` is nonnegative, since the `0`-th derivative inequality at `t = 0` reads `‖Ψ 0‖ ≤ L`.
  have hL0 : 0 ≤ L := by
    have h := hL 0 (Nat.zero_le l) 0 (le_refl 0)
    have h2 : ‖iteratedDerivWithin 0 Ψ (Set.Ici (0:ℝ)) (0:ℝ)‖ ≤ L := by simpa using h
    exact le_trans (norm_nonneg _) h2
  -- Faà di Bruno for `Ψ ∘ (‖·‖²)` on the domain `[0,∞)`.
  have hkey : iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x
      = (ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2)).taylorComp
          (ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x) l := by
    have hcomp := iteratedFDerivWithin_comp (𝕜 := ℝ) (s := Set.univ) (t := Set.Ici (0:ℝ))
      (f := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) (g := Ψ) (x := x) (n := ⊤) (i := l)
      (hΨ.contDiffWithinAt (sq_nonneg ‖x‖))
      (contDiffWithinAt_univ.mpr ((contDiff_norm_sq ℝ (n := ⊤)).contDiffAt))
      (uniqueDiffOn_Ici 0) uniqueDiffOn_univ (mem_univ x) (fun y _ => sq_nonneg ‖y‖) le_top
    rw [iteratedFDerivWithin_univ] at hcomp
    exact hcomp
  -- Uniform bound on the `q`-terms, coming from the hypothesis on `Ψ`.
  have hq : ∀ j : ℕ, j ≤ l →
      ‖ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2) j‖
        ≤ L / (1 + ‖x‖^2)^(k+2*l) := by
    intro j hj
    have hqj : ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2) j
        = iteratedFDerivWithin ℝ j Ψ (Set.Ici 0) (‖x‖^2) := rfl
    rw [hqj, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    rw [le_div_iff₀ (by positivity)]
    have h := hL j hj (‖x‖^2) (sq_nonneg ‖x‖)
    have h' : ‖iteratedDerivWithin j Ψ (Set.Ici 0) (‖x‖^2)‖ * (1 + ‖x‖^2)^(k+2*l) ≤ L := by
      rw [mul_comm]; exact h
    exact h'
  -- Uniform bound on the `p`-terms, coming from the quadratic nature of `‖·‖²`.
  have hp : ∀ m : ℕ, m ≤ l →
      ‖ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m‖
        ≤ 2*(1+‖x‖)^2 := by
    intro m _
    have hpm : ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m
        = iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) x := by
      rw [show ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m
            = iteratedFDerivWithin ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x
            from rfl, iteratedFDerivWithin_univ]
    rw [hpm]
    exact norm_iteratedFDeriv_norm_sq_le m x
  have hnorm : ‖iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x‖
      ≤ (Fintype.card (OrderedFinpartition l) : ℝ)
          * (L / (1 + ‖x‖^2)^(k+2*l)) * (2*(1+‖x‖)^2)^l := by
    rw [hkey]
    exact norm_taylorComp_le l (L / (1 + ‖x‖^2)^(k+2*l)) (2*(1+‖x‖)^2)
      (by nlinarith [norm_nonneg x]) _ _ hq hp
  -- The elementary numerical inequality `‖x‖^k * (2(1+‖x‖)^2)^l ≤ 4^l * (1+‖x‖^2)^(k+2l)`.
  have hmain : ‖x‖^k * (2*(1+‖x‖)^2)^l ≤ 4^l * (1 + ‖x‖^2)^(k+2*l) := by
    have hx1 : ‖x‖ ≤ 1 + ‖x‖^2 := by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1/2)]
    have hxk : ‖x‖^k ≤ (1 + ‖x‖^2)^k := pow_le_pow_left₀ (norm_nonneg x) hx1 k
    have hB_le : (2*(1+‖x‖)^2)^l ≤ 4^l * (1 + ‖x‖^2)^l := by
      have h1 : (1 + ‖x‖)^2 ≤ 2*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
      calc (2*(1+‖x‖)^2)^l
          = 2^l * ((1+‖x‖)^2)^l := by rw [mul_pow]
        _ ≤ 2^l * (2*(1+‖x‖^2))^l :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 l) (by positivity)
        _ = 2^l * (2^l * (1 + ‖x‖^2)^l) := by rw [mul_pow]
        _ = ((2:ℝ)^l * 2^l) * (1 + ‖x‖^2)^l := by ring
        _ = 4^l * (1 + ‖x‖^2)^l := by
              rw [show (2:ℝ)^l * 2^l = 4^l from by rw [← mul_pow]; norm_num]
    calc ‖x‖^k * (2*(1+‖x‖)^2)^l
        ≤ (1 + ‖x‖^2)^k * (4^l * (1 + ‖x‖^2)^l) :=
          mul_le_mul hxk hB_le (by positivity) (by positivity)
      _ = 4^l * (1 + ‖x‖^2)^(k+l) := by
          rw [show (1 + ‖x‖^2)^k * (4^l * (1 + ‖x‖^2)^l)
                = 4^l * ((1 + ‖x‖^2)^k * (1 + ‖x‖^2)^l) from by ring, ← pow_add]
      _ ≤ 4^l * (1 + ‖x‖^2)^(k+2*l) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by linarith [sq_nonneg ‖x‖]) (by omega)
  have hDle : ‖x‖^k * (2*(1+‖x‖)^2)^l / (1 + ‖x‖^2)^(k+2*l) ≤ 4^l := by
    rw [div_le_iff₀ (by positivity)]
    exact hmain
  calc ‖x‖^k * ‖iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x‖
      ≤ ‖x‖^k * ((Fintype.card (OrderedFinpartition l) : ℝ)
            * (L / (1 + ‖x‖^2)^(k+2*l)) * (2*(1+‖x‖)^2)^l) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (Fintype.card (OrderedFinpartition l) : ℝ) * L
          * (‖x‖^k * (2*(1+‖x‖)^2)^l / (1 + ‖x‖^2)^(k+2*l)) := by ring
    _ ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * L * 4^l := by
          apply mul_le_mul_of_nonneg_left hDle
          exact mul_nonneg (Nat.cast_nonneg _) hL0
    _ = ((4:ℝ)^l * (Fintype.card (OrderedFinpartition l) : ℝ)) * L := by ring

end Work.Radial
