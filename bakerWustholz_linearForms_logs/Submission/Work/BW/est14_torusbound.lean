import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est14_defs
import Submission.Work.BW.split_aux
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! BW §14, torus factor of one summand of `g^{(J)}`.

`g^{(J)}(z;t) = Q^{(J)}(z, α'^z;t)` is a sum over the index set `AuxIdx r h D₀ D` of a
coefficient (the `φ(p(λ))·Π·u(h)^{t₀}·Θ`-factor, handled elsewhere) times the torus factor

  `estTorus J (lamP …) z λ = ∏_j (e^{z·lamP_j})^{λ_j/2^J}`.

Here we only bound that torus factor. With `‖e^w‖ = e^{Re w} ≤ e^{‖w‖}` and
`‖w^k‖ = ‖w‖^k = e^{k·Re w}` for `k : ℕ`,

  `‖estTorus J (lamP…) z λ‖ = exp(Σ_j (λ_j/2^J)·Re(z·lamP_j))`
                            `≤ exp(‖z‖ · Σ_j (λ_j/2^J)·‖lamP_j‖)`.

BW §11 gives `hmod α'_j (lamP_j) ≤ σ_j`, hence `‖lamP_j‖ ≤ d·σ_j` (`d = [K:ℚ]`), and
`D_j = [D/(r d σ_j)]`, so `λ_j ≤ D_j` gives `λ_j‖lamP_j‖ ≤ D_j·d·σ_j ≤ D/r`
(since `D_j ≤ D/(r d σ_j)`). Summing over the `r` indices and dividing by `2^J`:

  `Σ_j (λ_j/2^J)·‖lamP_j‖ ≤ (1/2^J)·Σ_j D_j·d·σ_j ≤ D/2^J`,

and multiplying by `‖z‖` gives `‖estTorus J (lamP…) z λ‖ ≤ exp(‖z‖·D/2^J)`. -/

namespace Work.BW

/-- The torus factor is bounded by the exponential of the (scaled) sum of `‖z‖‖ℓ_j‖`:
`‖∏_j (e^{zℓ_j})^{n_j/2^J}‖ ≤ exp(Σ_j (n_j/2^J)‖z‖‖ℓ_j‖)`, the `n_j/2^J` being natural
quotients on both sides. -/
lemma estTorus_norm_le {r : ℕ} (J : ℕ) (ℓ : Fin r → ℂ) (z : ℂ) (n : Fin r → ℕ) :
    ‖estTorus J ℓ z n‖ ≤
      Real.exp (∑ j, (((n j / 2 ^ J : ℕ) : ℝ) * (‖z‖ * ‖ℓ j‖))) := by
  rw [estTorus, norm_prod]
  have h₂ : ∀ j : Fin r,
      ‖(Complex.exp (z * ℓ j)) ^ (n j / 2 ^ J)‖
        = Real.exp (((n j / 2 ^ J : ℕ) : ℝ) * ((z * ℓ j).re)) := by
    intro j
    rw [norm_pow, Complex.norm_exp]
    exact (Real.exp_nat_mul ((z * ℓ j).re) (n j / 2 ^ J)).symm
  rw [Finset.prod_congr rfl (fun j _ => h₂ j)]
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro j _
  have hre : (z * ℓ j).re ≤ ‖z‖ * ‖ℓ j‖ := by
    calc (z * ℓ j).re ≤ ‖z * ℓ j‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖ℓ j‖ := norm_mul _ _
  exact mul_le_mul_of_nonneg_left hre (Nat.cast_nonneg _)

/-- BW §11: from `BH`, the determination `lamP_j` of `log α'_j` satisfies
`‖lamP_j‖ ≤ d·σ_j`, `d = [K:ℚ]`. Indeed `‖lamP_j‖/d ≤ hmod α'_j (lamP_j) ≤ σ_j`. -/
lemma norm_lamP_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (j : Fin r) :
    ‖lamP φ α v L j‖ ≤ (dK K : ℝ) * σ j := by
  obtain ⟨-, -, -, -, -, hσ, -, -⟩ := H.hBH
  have hd : 0 < (dK K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have h1 : ‖lamP φ α v L j‖ / (dK K : ℝ) ≤ hmod (α' j) (lamP φ α v L j) := by
    rw [hmod]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : ‖lamP φ α v L j‖ ≤ hmod (α' j) (lamP φ α v L j) * (dK K : ℝ) := by
    rw [div_le_iff₀ hd] at h1
    exact h1
  calc ‖lamP φ α v L j‖ ≤ hmod (α' j) (lamP φ α v L j) * (dK K : ℝ) := h2
    _ ≤ σ j * (dK K : ℝ) := mul_le_mul_of_nonneg_right (hσ j) (le_of_lt hd)
    _ = (dK K : ℝ) * σ j := by ring

/-- `D_j·d·σ_j ≤ D/r` from `D_j = [D/(r d σ_j)]` and `σ_j ≥ 1/d`. -/
lemma pDj_mul_sigma_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (j : Fin r) :
    (pDj r d σ j : ℝ) * ((d : ℝ) * σ j) ≤ pD r d σ / r := by
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hσpos : 0 < σ j :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (d : ℝ)) (hσ j)
  have hden : 0 < (r : ℝ) * (d : ℝ) * σ j := mul_pos (mul_pos hrpos hdpos) hσpos
  have h1 := pDj_le hr hd σ hσ j
  rw [le_div_iff₀ hden] at h1
  rw [le_div_iff₀ hrpos]
  nlinarith [h1]

/-- The torus factor of one summand of `g^{(J)}` is bounded by `exp(‖z‖ D / 2^J)`: `∏_j |e^{z·lamP_j}|^{λ_j/2^J} ≤ exp(‖z‖ Σ_j (λ_j/2^J)‖lamP_j‖)`, and `Σ_j D_j σ_j ≤ D/d`, `‖lamP_j‖ ≤ d σ_j` (BW §11), `λ_j ≤ D_j`. -/
theorem est14_torusbound {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (z : ℂ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))‖ ≤
      Real.exp (‖z‖ * acD K σ / 2 ^ J) := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := Module.finrank_pos (R := ℚ) (M := K)
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hfac : ∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * (‖z‖ * ‖lamP φ α v L j‖))
      = ‖z‖ * ∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hstep : ∀ j : Fin r,
      ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖)
        ≤ ((pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j)) / (2 : ℝ) ^ J := by
    intro j
    have hlam : (lm.2.2 j : ℕ) ≤ pDj r (dK K) σ j := Nat.lt_succ_iff.mp (lm.2.2 j).isLt
    have hk : (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) ≤ (pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J := by
      calc (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ)
          ≤ (((pDj r (dK K) σ j) / 2 ^ J : ℕ) : ℝ) := by
            exact_mod_cast (Nat.div_le_div_right hlam)
        _ ≤ (pDj r (dK K) σ j : ℝ) / ((2 ^ J : ℕ) : ℝ) := Nat.cast_div_le
        _ = (pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J := by rw [Nat.cast_pow]; norm_num
    calc ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖)
        ≤ ((pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J) * ((dK K : ℝ) * σ j) :=
          mul_le_mul hk (norm_lamP_le H j) (norm_nonneg (lamP φ α v L j)) (by positivity)
      _ = ((pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j)) / (2 : ℝ) ^ J := by ring
  have hsum : (∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖))
      ≤ pD r (dK K) σ / (2 : ℝ) ^ J := by
    calc ∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖)
        ≤ ∑ j, ((pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j)) / (2 : ℝ) ^ J :=
          Finset.sum_le_sum (fun j _ => hstep j)
      _ = (∑ j, (pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j)) / (2 : ℝ) ^ J := by
          rw [Finset.sum_div]
      _ ≤ pD r (dK K) σ / (2 : ℝ) ^ J := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          calc ∑ j, (pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j)
              ≤ ∑ _j : Fin r, pD r (dK K) σ / (r : ℝ) :=
                Finset.sum_le_sum (fun j _ => pDj_mul_sigma_le hr hd σ hσ j)
            _ = (r : ℝ) * (pD r (dK K) σ / (r : ℝ)) := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ = pD r (dK K) σ := by
                have hr0 : (r : ℝ) ≠ 0 := by positivity
                field_simp
  calc ‖estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))‖
      ≤ Real.exp (∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * (‖z‖ * ‖lamP φ α v L j‖))) :=
        estTorus_norm_le J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
    _ = Real.exp (‖z‖ * ∑ j, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * ‖lamP φ α v L j‖)) := by
        rw [hfac]
    _ ≤ Real.exp (‖z‖ * (pD r (dK K) σ / (2 : ℝ) ^ J)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (norm_nonneg z))
    _ = Real.exp (‖z‖ * acD K σ / 2 ^ J) := by
        congr 1
        rw [show acD K σ = pD r (dK K) σ from rfl]
        ring

end Work.BW
