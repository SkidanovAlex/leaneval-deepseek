import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_pair_bound_left
import Submission.Work.LT.lr_pair_bound_right
import Submission.Work.LT.lr_MA_form
import Submission.Work.LT.lr_MB_form
import Submission.Work.LT.lr_M0_layerConst_form
import Submission.Work.LT.lr_M0_cross_const
import Submission.Work.LT.lr_M0_layer_sum_zero

set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-! ## Layer bookkeeping for the vertex operator `M₀`

`Vtx G = Fin 2 × Fin 2 × G` splits into four "layers" `(α,β) : Fin 2 × Fin 2`, each an
isomorphic copy of `G`.  The `A`-move `nA` flips `α` and keeps `β`, the `B`-move `nB` flips `β`
and keeps `α`, so `M₀` respects the layer decomposition.  We split a function `h` into its
layer-constant part `m0LayerConst h` and its layer-mean-zero part `m0LayerMZ h`; the two are
orthogonal and `M₀`-invariant, and the quadratic form is the sum of the two pieces. -/

/-- The mean of `h` on the layer `(α,β)`. -/
noncomputable def m0LayerMean (h : Vtx G → ℝ) (α β : Fin 2) : ℝ :=
  (∑ g, h (α, β, g)) / (Fintype.card G : ℝ)

/-- The layer-constant part of `h`. -/
noncomputable def m0LayerConst (h : Vtx G → ℝ) : Vtx G → ℝ :=
  fun v => m0LayerMean h v.1 v.2.1

/-- The layer-mean-zero part of `h`. -/
noncomputable def m0LayerMZ (h : Vtx G → ℝ) : Vtx G → ℝ :=
  fun v => h v - m0LayerConst h v

/-- A sum over the vertex set is an iterated sum over the four layers and the group. -/
lemma m0Sum_Vtx (f : Vtx G → ℝ) :
    (∑ v : Vtx G, f v) = ∑ α : Fin 2, ∑ β : Fin 2, ∑ g : G, f (α, β, g) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

/-- The layer means of a zero-sum function add up to zero. -/
lemma m0LayerMean_sum_zero (h : Vtx G → ℝ) (hh : ∑ v : Vtx G, h v = 0) :
    ∑ α : Fin 2, ∑ β : Fin 2, m0LayerMean h α β = 0 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := G); exact_mod_cast this.ne'
  have h3 : (Fintype.card G : ℝ) * (∑ α, ∑ β, m0LayerMean h α β) = ∑ v : Vtx G, h v := by
    rw [m0Sum_Vtx]; simp only [m0LayerMean]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro α _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro β _
    rw [mul_div_cancel₀ _ hcard]
  rw [hh] at h3
  exact (mul_eq_zero.mp h3).resolve_left hcard

/-- Every layer of the layer-mean-zero part sums to zero. -/
lemma m0LayerMZ_sum_zero (h : Vtx G → ℝ) (α β : Fin 2) :
    ∑ g : G, m0LayerMZ h (α, β, g) = 0 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := G); exact_mod_cast this.ne'
  have hsub : ∀ g : G, m0LayerMZ h (α, β, g) = h (α, β, g) - m0LayerMean h α β := by
    intro g; simp only [m0LayerMZ, m0LayerConst]
  rw [Finset.sum_congr rfl (fun g _ => hsub g)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℝ) * m0LayerMean h α β = ∑ g, h (α, β, g) := by
    rw [m0LayerMean]; field_simp
  rw [this, sub_self]

/-- A function with zero layer sums is orthogonal to every layer-constant function. -/
lemma m0Sum_mul_layer (u : Vtx G → ℝ) (E : Fin 2 → Fin 2 → ℝ)
    (hu : ∀ α β, ∑ g, u (α, β, g) = 0) :
    (∑ v : Vtx G, u v * E v.1 v.2.1) = 0 := by
  rw [m0Sum_Vtx]
  have h1 : ∀ α β, (∑ g : G, u (α, β, g) * E α β) = 0 := by
    intro α β; rw [← Finset.sum_mul, hu α β, zero_mul]
  simp only [h1, Finset.sum_const_zero]

/-- `ℓ²`-mass grouped by the four layers, `A`-pair first. -/
lemma m0Sum_sq_alpha (f : Vtx G → ℝ) :
    (∑ v : Vtx G, f v ^ 2)
      = ∑ α : Fin 2, ((∑ g, f (α, 0, g) ^ 2) + ∑ g, f (α, 1, g) ^ 2) := by
  rw [m0Sum_Vtx]
  apply Finset.sum_congr rfl; intro α _
  rw [Fin.sum_univ_two]

/-- `ℓ²`-mass grouped by the four layers, `B`-pair first. -/
lemma m0Sum_sq_beta (f : Vtx G → ℝ) :
    (∑ v : Vtx G, f v ^ 2)
      = ∑ β : Fin 2, ((∑ g, f (0, β, g) ^ 2) + ∑ g, f (1, β, g) ^ 2) := by
  rw [m0Sum_Vtx, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro β _
  rw [Fin.sum_univ_two]

/-- `M₀` is additive in its argument. -/
lemma m0_add (A B : Fin Δ → G) (h₁ h₂ : Vtx G → ℝ) :
    M0 A B (h₁ + h₂) = M0 A B h₁ + M0 A B h₂ := by
  funext v
  simp only [M0, Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- The decomposition of `h` into layer-constant and layer-mean-zero parts. -/
lemma m0_self_eq (h : Vtx G → ℝ) : h = m0LayerConst h + m0LayerMZ h := by
  funext v; simp only [m0LayerMZ, Pi.add_apply]; ring

/-- `M₀` written with the two one-sided averages separated. -/
lemma m0_sum_split (A B : Fin Δ → G) (h : Vtx G → ℝ) (hΔ : 0 < Δ) :
    (∑ v, h v * M0 A B h v)
      = (1/2) * ((∑ v, h v * ((∑ i, h (nA A v i)) / (Δ : ℝ)))
          + (∑ v, h v * ((∑ j, h (nB B v j)) / (Δ : ℝ)))) := by
  have hΔne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ.ne'
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [M0]
  field_simp

/-- The `A`-half of the quadratic form of `M₀` is bounded by `μ‖h‖²` for layer-mean-zero `h`,
by Cauchy–Schwarz applied layer-pair by layer-pair (`lr_MA_form` + `lr_pair_bound_left`). -/
lemma m0_A_part (A : Fin Δ → G) (μ : ℝ) (hμ : 0 ≤ μ) (hA : leftExpander A μ)
    (h : Vtx G → ℝ) (hh : ∀ α β, ∑ g, h (α, β, g) = 0) :
    (∑ v, h v * ((∑ i, h (nA A v i)) / (Δ : ℝ))) ≤ μ * ∑ v, h v ^ 2 := by
  have hper : ∀ β : Fin 2,
      2 * (∑ g, h (0, β, g) * ((∑ i, h (1, β, A i * g)) / (Δ : ℝ)))
        ≤ μ * ((∑ g, h (0, β, g) ^ 2) + ∑ g, h (1, β, g) ^ 2) :=
    fun β => lr_pair_bound_left (G := G) (Δ := Δ) A μ hμ hA
      (fun g : G => h (0, β, g)) (fun g : G => h (1, β, g)) (hh 1 β)
  calc (∑ v, h v * ((∑ i, h (nA A v i)) / (Δ : ℝ)))
      = 2 * ∑ β, (∑ g, h (0, β, g) * ((∑ i, h (1, β, A i * g)) / (Δ : ℝ))) :=
        lr_MA_form A h
    _ = ∑ β, 2 * (∑ g, h (0, β, g) * ((∑ i, h (1, β, A i * g)) / (Δ : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ β, μ * ((∑ g, h (0, β, g) ^ 2) + ∑ g, h (1, β, g) ^ 2) :=
        Finset.sum_le_sum (fun β _ => hper β)
    _ = μ * ∑ β, ((∑ g, h (0, β, g) ^ 2) + ∑ g, h (1, β, g) ^ 2) := by rw [Finset.mul_sum]
    _ = μ * ∑ v, h v ^ 2 := by rw [m0Sum_sq_beta h]

/-- The `B`-half of the quadratic form of `M₀`. -/
lemma m0_B_part (B : Fin Δ → G) (μ : ℝ) (hμ : 0 ≤ μ) (hB : rightExpander B μ)
    (h : Vtx G → ℝ) (hh : ∀ α β, ∑ g, h (α, β, g) = 0) :
    (∑ v, h v * ((∑ j, h (nB B v j)) / (Δ : ℝ))) ≤ μ * ∑ v, h v ^ 2 := by
  have hper : ∀ α : Fin 2,
      2 * (∑ g, h (α, 0, g) * ((∑ j, h (α, 1, g * B j)) / (Δ : ℝ)))
        ≤ μ * ((∑ g, h (α, 0, g) ^ 2) + ∑ g, h (α, 1, g) ^ 2) :=
    fun α => lr_pair_bound_right (G := G) (Δ := Δ) B μ hμ hB
      (fun g : G => h (α, 0, g)) (fun g : G => h (α, 1, g)) (hh α 1)
  calc (∑ v, h v * ((∑ j, h (nB B v j)) / (Δ : ℝ)))
      = 2 * ∑ α, (∑ g, h (α, 0, g) * ((∑ j, h (α, 1, g * B j)) / (Δ : ℝ))) :=
        lr_MB_form B h
    _ = ∑ α, 2 * (∑ g, h (α, 0, g) * ((∑ j, h (α, 1, g * B j)) / (Δ : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ α, μ * ((∑ g, h (α, 0, g) ^ 2) + ∑ g, h (α, 1, g) ^ 2) :=
        Finset.sum_le_sum (fun α _ => hper α)
    _ = μ * ∑ α, ((∑ g, h (α, 0, g) ^ 2) + ∑ g, h (α, 1, g) ^ 2) := by rw [Finset.mul_sum]
    _ = μ * ∑ v, h v ^ 2 := by rw [m0Sum_sq_alpha h]

/-- Spectral bound for `M₀` on layer-mean-zero functions. -/
lemma m0_mz_bound (A B : Fin Δ → G) (μ : ℝ) (hμ : 0 ≤ μ) (hA : leftExpander A μ)
    (hB : rightExpander B μ) (h : Vtx G → ℝ) (hh : ∀ α β, ∑ g, h (α, β, g) = 0)
    (hΔ : 0 < Δ) :
    (∑ v, h v * M0 A B h v) ≤ μ * ∑ v, h v ^ 2 := by
  rw [m0_sum_split A B h hΔ]
  have h1 := m0_A_part A μ hμ hA h hh
  have h2 := m0_B_part B μ hμ hB h hh
  linarith

/-- **Spectral gap of the vertex operator** `M₀ = ½(M_A + M_B)`. For a mean-zero function
`h : Vtx G → ℝ` the quadratic form of one random step of the vertex walk (`M0 A B h v` averages
`h` over the `Δ` A-neighbours and the `Δ` B-neighbours of `v`) is at most `μ` times the `ℓ²` norm
squared. Mathematically: `h = h_const + h_mz` (layer-constants plus per-layer-mean-zero); on
layer-constants `M₀` has eigenvalues `1,0,0,-1` and the `1`-eigenvector is the constant function,
which is excluded by `Σ h = 0` (so the constants contribute `≤ 0 ≤ μ·‖·‖²`); on the
per-layer-mean-zero part `M0 ≤ ½(M_A + M_B)` gives `⟨h,M₀h⟩ ≤ μ‖h‖²` from `leftExpander A μ` and
`rightExpander B μ` via Cauchy–Schwarz. -/
theorem lr_spectral_M0 {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G) (μ : ℝ)
    (hA : leftExpander A μ) (hB : rightExpander B μ) (hμ : 0 ≤ μ) :
    ∀ h : Vtx G → ℝ, (∑ v, h v) = 0 →
      ∑ v, h v * M0 A B h v ≤ μ * ∑ v, h v ^ 2 := by
  classical
  intro h hh
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔpos
  · subst hΔ0
    have hz : ∀ v : Vtx G, M0 A B h v = 0 := by intro v; simp [M0]
    have h0 : (∑ v : Vtx G, h v * M0 A B h v) = 0 :=
      Finset.sum_eq_zero (fun v _ => by rw [hz v, mul_zero])
    rw [h0]
    exact mul_nonneg hμ (Finset.sum_nonneg (fun v _ => sq_nonneg (h v)))
  · have hmz : ∀ α β, ∑ g, m0LayerMZ h (α, β, g) = 0 := fun α β => m0LayerMZ_sum_zero h α β
    have hcsum : ∑ α, ∑ β, m0LayerMean h α β = 0 := m0LayerMean_sum_zero h hh
    -- the layer-constant and layer-mean-zero parts are orthogonal
    have horth : (∑ v, m0LayerConst h v * m0LayerMZ h v) = 0 := by
      have h1 : (∑ v, m0LayerMZ h v * m0LayerConst h v) = 0 :=
        m0Sum_mul_layer (m0LayerMZ h) (m0LayerMean h) hmz
      rwa [Finset.sum_congr rfl (fun v _ => mul_comm (m0LayerMZ h v) (m0LayerConst h v))] at h1
    -- Pythagoras: the mean-zero part has the smaller `ℓ²`-mass
    have hmzsq : (∑ v, m0LayerMZ h v ^ 2) ≤ ∑ v, h v ^ 2 := by
      have hp : ∀ v : Vtx G,
          h v ^ 2 = m0LayerConst h v ^ 2 + m0LayerMZ h v ^ 2
            + 2 * (m0LayerConst h v * m0LayerMZ h v) := by
        intro v
        have hv : h v = m0LayerConst h v + m0LayerMZ h v := by
          simp only [m0LayerMZ]; ring
        rw [hv]; ring
      have hexp : (∑ v, h v ^ 2) = (∑ v, m0LayerConst h v ^ 2) + ∑ v, m0LayerMZ h v ^ 2 := by
        calc (∑ v, h v ^ 2)
            = ∑ v, (m0LayerConst h v ^ 2 + m0LayerMZ h v ^ 2
                + 2 * (m0LayerConst h v * m0LayerMZ h v)) :=
              Finset.sum_congr rfl (fun v _ => hp v)
          _ = (∑ v, m0LayerConst h v ^ 2) + (∑ v, m0LayerMZ h v ^ 2)
                + 2 * ∑ v, m0LayerConst h v * m0LayerMZ h v := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = (∑ v, m0LayerConst h v ^ 2) + ∑ v, m0LayerMZ h v ^ 2 := by
              rw [horth]; ring
      linarith [Finset.sum_nonneg (fun v (_ : v ∈ Finset.univ) => sq_nonneg (m0LayerConst h v))]
    -- `M₀` splits along the layer decomposition
    have hM0lin : M0 A B h = M0 A B (m0LayerConst h) + M0 A B (m0LayerMZ h) := by
      conv_lhs => rw [m0_self_eq h]
      exact m0_add A B (m0LayerConst h) (m0LayerMZ h)
    have hstep1 : (∑ v, h v * M0 A B h v)
        = (∑ v, m0LayerConst h v * M0 A B h v) + (∑ v, m0LayerMZ h v * M0 A B h v) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      have hv : h v = m0LayerConst h v + m0LayerMZ h v := by
        simp only [m0LayerMZ]; ring
      rw [hv]; ring
    have hstep2a : (∑ v, m0LayerConst h v * M0 A B h v)
        = (∑ v, m0LayerConst h v * M0 A B (m0LayerConst h) v)
          + (∑ v, m0LayerConst h v * M0 A B (m0LayerMZ h) v) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      rw [hM0lin]; simp only [Pi.add_apply]; ring
    have hstep2b : (∑ v, m0LayerMZ h v * M0 A B h v)
        = (∑ v, m0LayerMZ h v * M0 A B (m0LayerConst h) v)
          + (∑ v, m0LayerMZ h v * M0 A B (m0LayerMZ h) v) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      rw [hM0lin]; simp only [Pi.add_apply]; ring
    -- the two cross terms vanish
    have hM0mz : (∑ v, m0LayerConst h v * M0 A B (m0LayerMZ h) v) = 0 := by
      have h1 : (∑ v, M0 A B (m0LayerMZ h) v * m0LayerConst h v) = 0 :=
        m0Sum_mul_layer (M0 A B (m0LayerMZ h)) (m0LayerMean h)
          (fun α β => lr_M0_layer_sum_zero A B (m0LayerMZ h) hmz α β)
      rwa [Finset.sum_congr rfl (fun v _ => mul_comm (M0 A B (m0LayerMZ h) v)
        (m0LayerConst h v))] at h1
    have hcross2 : (∑ v, m0LayerMZ h v * M0 A B (m0LayerConst h) v) = 0 :=
      lr_M0_cross_const A B (m0LayerMean h) (m0LayerMZ h) hmz
    -- layer-constants contribute at most `0`
    have hconst : (∑ v, m0LayerConst h v * M0 A B (m0LayerConst h) v) ≤ 0 :=
      lr_M0_layerConst_form A B (m0LayerMean h) hcsum
    have hb := m0_mz_bound A B μ hμ hA hB (m0LayerMZ h) hmz hΔpos
    have hsteps : (∑ v, h v * M0 A B h v)
        = (∑ v, m0LayerConst h v * M0 A B (m0LayerConst h) v)
          + ∑ v, m0LayerMZ h v * M0 A B (m0LayerMZ h) v := by
      rw [hstep1, hstep2a, hstep2b, hM0mz, hcross2]; ring
    rw [hsteps]
    have h1 := mul_le_mul_of_nonneg_left hmzsq hμ
    linarith

end Work.LT
