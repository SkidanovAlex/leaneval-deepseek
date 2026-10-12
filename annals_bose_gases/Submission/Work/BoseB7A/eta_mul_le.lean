import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Statements
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.eta_mul_le` — `η` and the `K`-monomials are small at small `t`

At FS's §10 parameter point (`FSParamsView E`) every scalar is a monomial in
`X = (μa³)^{1/323}` (`Work.BoseB7.FSParamsVals`):

* `K_ℓ = X^{-3/2}`, `K_L = X^{-21/2}`, `𝓁 = X^{97/2}`, `M = 48`,
* `dil E c = (μa³)^c = X^{323c}`,

so the decay factor of `χ̂` on `P_H^q` is

`η = (K_ℓ^{-2}𝓁)^{⌊M/2⌋} = (X^{103/2})^{24} = X^{1236}`,

and the four quantities of the request are monomials with **positive** exponent in
`X`:

| quantity | value |
|---|---|
| `η` | `X^{1236}` |
| `η 𝓁² K_ℓ^{3/2} K_L³ (μa³)^{1/4}` | `X^{1380}` |
| `η² (μa³)^{1/2} K_ℓ³ K_L⁶` | `X^{2566}` |
| `η (K_ℓK_L)^{3/2}` | `X^{1218}` |

Since `X = t^{1/323} → 0` as `t → 0⁺`, all four are `≤ c` for `t ≤ t₀(c)`.
The proof computes the four monomials exactly (`eta_eq`, `eta_prod2`,
`eta_prod3`, `eta_prod4`), reduces the request to the single bound
`X^{1218} ≤ c` (monotonicity of `fsXp t ·` in the exponent for `t ≤ 1`, every
exponent being `≥ 1218`), and obtains the latter from
`fsXp_le_of_pos_exp`.

The hypothesis `b₀ ≤ E.b` is not used (it is part of the interface of the
request; the asymptotic statement needs only the smallness of `t`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7 Work.BoseBox

/-! ## 1. A general smallness fact for `fsXp` -/

/-- **`fsXp t A → 0` as `t → 0⁺` for `A > 0`**, with an explicit threshold:
for `t ≤ min 1 (c^{323/A})` one has `fsXp t A = t^{A/323} ≤ c`. -/
lemma fsXp_le_of_pos_exp {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → fsXp t A ≤ c := by
  refine ⟨min 1 (c ^ (323 / A)), lt_min one_pos (Real.rpow_pos_of_pos hc _), ?_⟩
  intro t ht hle
  have h1 : t ≤ c ^ (323 / A) := le_trans hle (min_le_right _ _)
  calc fsXp t A = t ^ (A / 323) := rfl
    _ ≤ (c ^ (323 / A)) ^ (A / 323) :=
        Real.rpow_le_rpow ht.le h1 (by positivity)
    _ = c ^ ((323 / A) * (A / 323)) := (Real.rpow_mul hc.le _ _).symm
    _ = c ^ (1 : ℝ) := by
        congr 1
        field_simp
    _ = c := Real.rpow_one c

/-! ## 2. The four monomials, in the `fsXp` normal form -/

/-- `η = (K_ℓ^{-2}𝓁)^{⌊M/2⌋} = (X^{103/2})^{24} = X^{1236}`. -/
lemma eta_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (h : FSParamsView E) : eta E = fsXp h.t 1236 := by
  have ht := h.t_pos
  have hMt : Mt E = 24 := by rw [Mt, h.intM_eq, mValue]; norm_num
  have hKl : E.Kl ^ (-(2 : ℝ)) = fsXp h.t 3 := by
    rw [Kl_val E h]
    rw [show (fsXp h.t (-(3 / 2))) ^ (-(2 : ℝ)) = fsXp h.t (-(3 / 2) * -(2)) from
      fsXp_rpow ht.le _ _]
    congr 1
    norm_num
  rw [eta, hMt, hKl, lille_val E h]
  rw [show fsXp h.t 3 * fsXp h.t (97 / 2) = fsXp h.t (3 + 97 / 2) from fsXp_mul ht _ _]
  rw [show fsXp h.t (3 + 97 / 2) = fsXp h.t (103 / 2) by congr 1; norm_num]
  rw [show (fsXp h.t (103 / 2)) ^ (24 : ℝ) = fsXp h.t (103 / 2 * 24) from fsXp_rpow ht.le _ _]
  congr 1
  norm_num

/-- `η 𝓁² K_ℓ^{3/2} K_L³ (μa³)^{1/4} = X^{1380}`. -/
lemma eta_prod2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (h : FSParamsView E) :
    eta E * E.lille ^ 2 * E.Kl ^ ((3 : ℝ) / 2) * E.KL ^ 3 * dil E (1 / 4) =
      fsXp h.t 1380 := by
  have ht := h.t_pos
  rw [eta_eq E h, lille_val E h, Kl_val E h, KL_val E h, dil_val E h (1 / 4)]
  rw [show (fsXp h.t (97 / 2)) ^ 2 = fsXp h.t ((97 / 2) * 2) from fsXp_pow ht.le _ _]
  rw [show (fsXp h.t (-(3 / 2))) ^ ((3 : ℝ) / 2) =
      fsXp h.t (-(3 / 2) * ((3 : ℝ) / 2)) from fsXp_rpow ht.le _ _]
  rw [show (fsXp h.t (-(21 / 2))) ^ 3 = fsXp h.t ((-(21 / 2)) * 3) from fsXp_pow ht.le _ _]
  rw [show fsXp h.t 1236 * fsXp h.t ((97 / 2) * 2) =
      fsXp h.t (1236 + (97 / 2) * 2) from fsXp_mul ht _ _]
  rw [show fsXp h.t (1236 + (97 / 2) * 2) * fsXp h.t (-(3 / 2) * ((3 : ℝ) / 2)) =
      fsXp h.t (1236 + (97 / 2) * 2 + -(3 / 2) * ((3 : ℝ) / 2)) from fsXp_mul ht _ _]
  rw [show fsXp h.t (1236 + (97 / 2) * 2 + -(3 / 2) * ((3 : ℝ) / 2)) *
        fsXp h.t ((-(21 / 2)) * 3) =
      fsXp h.t (1236 + (97 / 2) * 2 + -(3 / 2) * ((3 : ℝ) / 2) + (-(21 / 2)) * 3)
        from fsXp_mul ht _ _]
  rw [show fsXp h.t (1236 + (97 / 2) * 2 + -(3 / 2) * ((3 : ℝ) / 2) + (-(21 / 2)) * 3) *
        fsXp h.t (323 * (1 / 4)) =
      fsXp h.t (1236 + (97 / 2) * 2 + -(3 / 2) * ((3 : ℝ) / 2) + (-(21 / 2)) * 3 +
        323 * (1 / 4)) from fsXp_mul ht _ _]
  congr 1
  norm_num

/-- `η² (μa³)^{1/2} K_ℓ³ K_L⁶ = X^{2566}`. -/
lemma eta_prod3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (h : FSParamsView E) :
    eta E ^ 2 * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 = fsXp h.t 2566 := by
  have ht := h.t_pos
  rw [eta_eq E h, dil_val E h (1 / 2), Kl_val E h, KL_val E h]
  rw [show (fsXp h.t 1236) ^ 2 = fsXp h.t (1236 * 2) from fsXp_pow ht.le _ _]
  rw [show (fsXp h.t (-(3 / 2))) ^ 3 = fsXp h.t ((-(3 / 2)) * 3) from fsXp_pow ht.le _ _]
  rw [show (fsXp h.t (-(21 / 2))) ^ 6 = fsXp h.t ((-(21 / 2)) * 6) from fsXp_pow ht.le _ _]
  rw [show fsXp h.t (1236 * 2) * fsXp h.t (323 * (1 / 2)) =
      fsXp h.t (1236 * 2 + 323 * (1 / 2)) from fsXp_mul ht _ _]
  rw [show fsXp h.t (1236 * 2 + 323 * (1 / 2)) * fsXp h.t ((-(3 / 2)) * 3) =
      fsXp h.t (1236 * 2 + 323 * (1 / 2) + (-(3 / 2)) * 3) from fsXp_mul ht _ _]
  rw [show fsXp h.t (1236 * 2 + 323 * (1 / 2) + (-(3 / 2)) * 3) *
        fsXp h.t ((-(21 / 2)) * 6) =
      fsXp h.t (1236 * 2 + 323 * (1 / 2) + (-(3 / 2)) * 3 + (-(21 / 2)) * 6)
        from fsXp_mul ht _ _]
  congr 1
  norm_num

/-- `η (K_ℓK_L)^{3/2} = X^{1236-18} = X^{1218}`. -/
lemma eta_prod4 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (h : FSParamsView E) :
    eta E * (E.Kl * E.KL) ^ ((3 : ℝ) / 2) = fsXp h.t 1218 := by
  have ht := h.t_pos
  rw [eta_eq E h]
  have hKlKL : E.Kl * E.KL = fsXp h.t (-12) := by
    rw [Kl_val E h, KL_val E h]
    rw [show fsXp h.t (-(3 / 2)) * fsXp h.t (-(21 / 2)) =
        fsXp h.t (-(3 / 2) + -(21 / 2)) from fsXp_mul ht _ _]
    congr 1
    norm_num
  rw [hKlKL]
  rw [show (fsXp h.t (-12)) ^ ((3 : ℝ) / 2) = fsXp h.t (-12 * (3 / 2)) from
    fsXp_rpow ht.le _ _]
  rw [show fsXp h.t 1236 * fsXp h.t (-12 * (3 / 2)) =
      fsXp h.t (1236 + -12 * (3 / 2)) from fsXp_mul ht _ _]
  congr 1
  norm_num

/-! ## 3. The requested bound -/

theorem eta_mul_le (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b →
        (Work.BoseB7A.eta E ≤ c) ∧
        (Work.BoseB7A.eta E * E.lille ^ 2 * E.Kl ^ ((3 : ℝ) / 2) * E.KL ^ 3 *
          Work.BoseB7.dil E (1 / 4) ≤ c) ∧
        (Work.BoseB7A.eta E ^ 2 * Work.BoseB7.dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 ≤ c) ∧
        (Work.BoseB7A.eta E * (E.Kl * E.KL) ^ ((3 : ℝ) / 2) ≤ c) := by
  obtain ⟨t₁, ht₁, h₁⟩ := fsXp_le_of_pos_exp (A := 1218) (by norm_num) hc
  refine ⟨min t₁ 1, lt_min ht₁ one_pos, ?_⟩
  intro Mode _ _ E hv hle _
  have ht := hv.t_pos
  have ht₁' : hv.t ≤ t₁ := le_trans hle (min_le_left _ _)
  have ht1 : hv.t ≤ 1 := le_trans hle (min_le_right _ _)
  have hsmall : fsXp hv.t 1218 ≤ c := h₁ hv.t ht ht₁'
  have hmono : ∀ A : ℝ, 1218 ≤ A → fsXp hv.t A ≤ c := fun A hA =>
    le_trans (fsXp_le_fsXp ht ht1 hA) hsmall
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eta_eq E hv]; exact hmono 1236 (by norm_num)
  · rw [eta_prod2 E hv]; exact hmono 1380 (by norm_num)
  · rw [eta_prod3 E hv]; exact hmono 2566 (by norm_num)
  · rw [eta_prod4 E hv]; exact hmono 1218 (by norm_num)

end Work.BoseB7A
