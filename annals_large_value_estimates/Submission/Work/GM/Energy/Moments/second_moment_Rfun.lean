import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# GM Lemma 11.5: the discrete second moment of `R`

This file proves `Work.GM.Energy.Moments.second_moment_Rfun`. The whole content is the
elementary (but not entirely trivial) identity

  `Σ_{n₁,n₂∈[M,2M]} ‖R(n₁/n₂)‖²  =  Σ_{t₁,t₂∈W} ‖Σ_{n∈[M,2M]} n^{i(t₁-t₂)}‖²`

together with a reindexing of the double sum over `W × W` as a sum over `Fin |W|`.
The right-hand side is then exactly the left-hand side of Heath-Brown's theorem
(`Submission.GM.HBStatement`) applied with the coefficients `a ≡ 1`, `R = |W|` and
`N = M`; the sequence `t : Fin |W| → ℝ` enumerating `W` is `W.equivFin.symm`.

The two expansions of a squared modulus use `‖z‖² = normSq z = (z * conj z).re` and
the elementary complex-power identity (for `x > 0`, `σ`, `τ ∈ ℝ`)

  `x^{iτ} · conj (x^{iσ}) = x^{i(τ-σ)}`,

which is proved from `z ^ w = exp (w * log z)` for positive real `z`. -/

namespace Work.GM.Energy.Moments

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- For a positive real `x` and complex `w`, `x ^ w = exp (w * log x)` (the logarithm
of a positive real is real). -/
private lemma cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℂ)) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- Conjugation inverts the (purely imaginary) exponent of a positive real base. -/
private lemma conj_cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ w) = (x : ℂ) ^ ((starRingEnd ℂ) w) := by
  rw [cpow_ofReal_pos hx, cpow_ofReal_pos hx, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal]

/-- `x^{iσ} · conj (y^{iσ}) = (x/y)^{iσ}` for positive reals `x, y`. -/
private lemma cpow_div_conj {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (σ : ℝ) :
    ((x : ℂ)) ^ (Complex.I * ((σ : ℂ))) * (starRingEnd ℂ) (((y : ℂ)) ^ (Complex.I * ((σ : ℂ))))
      = (((x / y : ℝ)) : ℂ) ^ (Complex.I * ((σ : ℂ))) := by
  rw [conj_cpow_ofReal_pos hy]
  rw [cpow_ofReal_pos hx, cpow_ofReal_pos hy, ← Complex.exp_add]
  rw [cpow_ofReal_pos (div_pos hx hy)]
  congr 1
  rw [Real.log_div hx.ne' hy.ne', Complex.ofReal_sub]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `x^{iτ} · conj (x^{iσ}) = x^{i(τ-σ)}` for a positive real `x`. -/
private lemma cpow_same_conj {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ((x : ℂ)) ^ (Complex.I * ((a : ℂ))) * (starRingEnd ℂ) (((x : ℂ)) ^ (Complex.I * ((b : ℂ))))
      = ((x : ℂ)) ^ (Complex.I * (((a - b : ℝ)) : ℂ)) := by
  rw [conj_cpow_ofReal_pos hx]
  have h1 : (starRingEnd ℂ) (Complex.I * (b : ℂ)) = -(Complex.I * (b : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [h1, ← Complex.cpow_add (x := ((x:ℂ))) (Complex.I * (a:ℂ)) (-(Complex.I * (b:ℂ)))
    (by exact_mod_cast hx.ne')]
  congr 1
  push_cast; ring

/-- Expansion of `‖R(v)‖²` for `v > 0` into a double sum over `W × W`. -/
private lemma normSq_Rfun {W : Finset ℝ} {v : ℝ} (hv : 0 < v) :
    Complex.normSq (Submission.GM.Rfun W v)
      = (∑ t ∈ W, ∑ s ∈ W, ((v : ℂ)) ^ (Complex.I * (((t - s : ℝ)) : ℂ))).re := by
  have hR : Submission.GM.Rfun W v = ∑ t ∈ W, ((v : ℂ)) ^ (Complex.I * ((t : ℂ))) := by
    unfold Submission.GM.Rfun
    simp_rw [abs_of_pos hv]
  rw [hR]
  rw [show Complex.normSq (∑ t ∈ W, ((v : ℂ)) ^ (Complex.I * ((t : ℂ))))
      = ((∑ t ∈ W, ((v : ℂ)) ^ (Complex.I * ((t : ℂ))))
          * (starRingEnd ℂ) (∑ t ∈ W, ((v : ℂ)) ^ (Complex.I * ((t : ℂ))))).re
      from by rw [Complex.mul_conj, Complex.ofReal_re],
      map_sum (starRingEnd ℂ) _ W, Finset.sum_mul_sum]
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro t ht
  apply Finset.sum_congr rfl; intro s hs
  rw [cpow_same_conj hv]

/-- Expansion of the squared modulus of the Dirichlet polynomial `Σ_{n ∈ [M,2M]} n^{iσ}`
into a double sum (the exponent `σ` is allowed to be any real number). -/
private lemma normSq_poly {M : ℕ} (hM : 1 ≤ M) (σ : ℝ) :
    Complex.normSq (∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))
      = (∑ n ∈ Finset.Icc M (2*M), ∑ m ∈ Finset.Icc M (2*M),
          (((n : ℂ) / (m : ℂ))) ^ (Complex.I * ((σ : ℂ)))).re := by
  have h1 : (∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))
        * (starRingEnd ℂ) (∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))
      = ∑ n ∈ Finset.Icc M (2*M), ∑ m ∈ Finset.Icc M (2*M),
          (((n : ℂ) / (m : ℂ))) ^ (Complex.I * ((σ : ℂ))) := by
    rw [map_sum (starRingEnd ℂ) _ _, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    apply Finset.sum_congr rfl; intro m hm
    have hn1 : 1 ≤ n := le_trans hM (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := le_trans hM (Finset.mem_Icc.mp hm).1
    have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    simpa [Complex.ofReal_natCast] using cpow_div_conj hn' hm' σ
  rw [show Complex.normSq (∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))
      = ((∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))
          * (starRingEnd ℂ) (∑ n ∈ Finset.Icc M (2*M), ((n : ℂ)) ^ (Complex.I * ((σ : ℂ))))).re
      from by rw [Complex.mul_conj, Complex.ofReal_re], h1]

/-- Reindexing a sum over `Fin W.card` along the enumeration `W.equivFin.symm`. -/
private lemma sum_equivFin {W : Finset ℝ} {A : Type*} [AddCommMonoid A] (f : ℝ → A) :
    (∑ i : Fin W.card, f ((W.equivFin.symm i : ↥W) : ℝ)) = ∑ x ∈ W, f x := by
  rw [← Finset.sum_coe_sort W f]
  exact Equiv.sum_comp W.equivFin.symm (fun x : ↥W => f (x : ℝ))

/-- Reindexing a double sum over `Fin W.card × Fin W.card` along `W.equivFin.symm`. -/
private lemma sum_equivFin₂ {W : Finset ℝ} {A : Type*} [AddCommMonoid A] (f : ℝ → ℝ → A) :
    (∑ i : Fin W.card, ∑ j : Fin W.card,
        f ((W.equivFin.symm i : ↥W) : ℝ) ((W.equivFin.symm j : ↥W) : ℝ))
      = ∑ x ∈ W, ∑ y ∈ W, f x y := by
  have h2 : ∀ i : Fin W.card,
      (∑ j : Fin W.card, f ((W.equivFin.symm i : ↥W) : ℝ) ((W.equivFin.symm j : ↥W) : ℝ))
        = ∑ y ∈ W, f ((W.equivFin.symm i : ↥W) : ℝ) y := fun i =>
    sum_equivFin (f ((W.equivFin.symm i : ↥W) : ℝ))
  simp only [h2]
  exact sum_equivFin (fun x => ∑ y ∈ W, f x y)

/-- Interchange of the pair of summations over `P × R` and `Q × S`. -/
private lemma sum_swap_four {A : Type*} [AddCommMonoid A] (P R : Finset ℝ) (Q S : Finset ℕ)
    (F : ℕ → ℕ → ℝ → ℝ → A) :
    (∑ x ∈ P, ∑ y ∈ R, ∑ n ∈ Q, ∑ m ∈ S, F n m x y)
      = ∑ n ∈ Q, ∑ m ∈ S, ∑ x ∈ P, ∑ y ∈ R, F n m x y := by
  have h1 : ∀ x ∈ P, (∑ y ∈ R, ∑ n ∈ Q, ∑ m ∈ S, F n m x y)
      = ∑ n ∈ Q, ∑ y ∈ R, ∑ m ∈ S, F n m x y := fun x _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ x ∈ P, ∀ n ∈ Q, (∑ y ∈ R, ∑ m ∈ S, F n m x y)
      = ∑ m ∈ S, ∑ y ∈ R, F n m x y := fun x _ n _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun n hn => h2 x hx n hn))]
  rw [Finset.sum_comm]
  have h3 : ∀ n ∈ Q, (∑ x ∈ P, ∑ m ∈ S, ∑ y ∈ R, F n m x y)
      = ∑ m ∈ S, ∑ x ∈ P, ∑ y ∈ R, F n m x y := fun n _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h3]

/-- **GM Lemma 11.5** (discrete second moment): for any `M ≥ 1`,
`Σ_{n₁,n₂∈[M,2M]} ‖R(n₁/n₂)‖² ⪅ |W|²M + |W|M² + |W|^{5/4}T^{1/2}M`; this is Heath-Brown's
theorem (`hHB`) applied with `a ≡ 1`, since
`Σ_{n₁,n₂}‖R(n₁/n₂)‖² = Σ_{t₁,t₂∈W} ‖Σ_{n∈[M,2M]} n^{i(t₁-t₂)}‖²`. -/
theorem second_moment_Rfun (hHB : Submission.GM.HBStatement) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T →
    ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        ≤ C * T ^ ε * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
  obtain ⟨C, hCpos, hbound⟩ := hHB ε hε
  refine ⟨C, hCpos, ?_⟩
  intro M hM T hT W hW hsep
  set t : Fin W.card → ℝ := fun i => ((W.equivFin.symm i : ↥W) : ℝ) with htdef
  have htmem : ∀ i, t i ∈ Set.Icc 0 T := fun i => hW _ (W.equivFin.symm i).2
  have htsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j| := by
    intro i j hij
    refine hsep _ (W.equivFin.symm i).2 _ (W.equivFin.symm j).2 ?_
    intro h
    exact hij (W.equivFin.symm.injective (Subtype.ext h))
  have hb := hbound M hM T hT (fun _ => (1 : ℂ)) (fun n => by simp) W.card t htmem htsep
  have hkey : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      = ∑ i : Fin W.card, ∑ j : Fin W.card,
          ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ))‖ ^ 2 := by
    have hpos : ∀ n ∈ Finset.Icc M (2 * M), (0 : ℝ) < (n : ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := le_trans hM (Finset.mem_Icc.mp hn).1
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hleft : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        = (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M), ∑ x ∈ W, ∑ y ∈ W,
            (((n1 : ℂ) / (n2 : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re := by
      have hpt : ∀ n1 ∈ Finset.Icc M (2 * M), ∀ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2
            = (∑ x ∈ W, ∑ y ∈ W,
                (((n1 : ℂ) / (n2 : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re := by
        intro n1 hn1 n2 hn2
        rw [← Complex.normSq_eq_norm_sq, normSq_Rfun (div_pos (hpos n1 hn1) (hpos n2 hn2))]
        simp only [Complex.ofReal_div, Complex.ofReal_natCast]
      rw [show (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
            = ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
                (∑ x ∈ W, ∑ y ∈ W,
                  (((n1 : ℂ) / (n2 : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re from by
            apply Finset.sum_congr rfl; intro n1 hn1
            apply Finset.sum_congr rfl; intro n2 hn2
            exact hpt n1 hn1 n2 hn2]
      simp only [Complex.re_sum]
    have hright : (∑ i : Fin W.card, ∑ j : Fin W.card,
        ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ))‖ ^ 2)
        = (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M), ∑ x ∈ W, ∑ y ∈ W,
            (((n1 : ℂ) / (n2 : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re := by
      have hstep1 : (∑ i : Fin W.card, ∑ j : Fin W.card,
          ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ))‖ ^ 2)
          = ∑ x ∈ W, ∑ y ∈ W,
              ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((x - y : ℝ)) : ℂ))‖ ^ 2 := by
        rw [htdef]
        exact sum_equivFin₂ (fun x y => ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((x - y : ℝ)) : ℂ))‖ ^ 2)
      have hstep2 : (∑ x ∈ W, ∑ y ∈ W,
            ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((x - y : ℝ)) : ℂ))‖ ^ 2)
          = (∑ x ∈ W, ∑ y ∈ W, ∑ n ∈ Finset.Icc M (2 * M), ∑ m ∈ Finset.Icc M (2 * M),
              (((n : ℂ) / (m : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re := by
        have hpt : ∀ x y : ℝ,
            ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((x - y : ℝ)) : ℂ))‖ ^ 2
              = (∑ n ∈ Finset.Icc M (2 * M), ∑ m ∈ Finset.Icc M (2 * M),
                  (((n : ℂ) / (m : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re := by
          intro x y
          simp only [one_mul]
          rw [← Complex.normSq_eq_norm_sq, normSq_poly hM (x - y)]
        rw [show (∑ x ∈ W, ∑ y ∈ W,
              ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (((x - y : ℝ)) : ℂ))‖ ^ 2)
            = ∑ x ∈ W, ∑ y ∈ W,
                (∑ n ∈ Finset.Icc M (2 * M), ∑ m ∈ Finset.Icc M (2 * M),
                  (((n : ℂ) / (m : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ)))).re from by
            apply Finset.sum_congr rfl; intro x _
            apply Finset.sum_congr rfl; intro y _
            exact hpt x y]
        simp only [Complex.re_sum]
      rw [hstep1, hstep2]
      exact congrArg Complex.re (sum_swap_four W W (Finset.Icc M (2 * M)) (Finset.Icc M (2 * M))
        (fun n m x y => ((n : ℂ) / (m : ℂ)) ^ (Complex.I * (((x - y : ℝ)) : ℂ))))
    rw [hleft, hright]
  rw [hkey]
  exact hb

end Work.GM.Energy.Moments
