import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_mixing_count
import Submission.Work.LT.lr_walk_mean_zero

namespace Work.LT

open scoped BigOperators

/-! ## Bipartite expander mixing for the right walk `x ↦ (g ↦ avg_j x (g * B j))`

The main mathematical content is the general mixing inequality `lrMixing_general`: for *arbitrary*
real functions `f h` on the group,

`∑_g f g · (∑_j h (g * B j)) ≤ Δ (∑_g f g)(∑_g h g)/|G| + μ Δ √((∑_g f g²)(∑_g h g²))`.

It is proved by splitting `f` and `h` into their mean plus a mean-zero part, using that the walk
preserves mean zero (`lr_walk_mean_zero`), Cauchy–Schwarz (`lrMixing_cauchy_schwarz`) and the ℓ²
contraction hypothesis `rightExpander B μ`. The target `lr_mixing` is the case where `f`, `h` are
the indicator functions of two finsets, using `lr_mixing_count` (the edge count is the bilinear
form `∑_g 1_S g ∑_j 1_T (g * B j)`). -/

/-! ### Two elementary indicator sums -/

lemma lrMixing_indicator_sum {G : Type} [Fintype G] [DecidableEq G] (S : Finset G) :
    (∑ g : G, (if g ∈ S then (1:ℝ) else 0)) = (S.card : ℝ) := by
  classical
  have hf : (Finset.univ.filter (fun g : G => g ∈ S)) = S := by ext g; simp
  rw [Finset.sum_boole (p := fun g => g ∈ S) (s := (Finset.univ : Finset G)), hf]

lemma lrMixing_indicator_sum_sq {G : Type} [Fintype G] [DecidableEq G] (S : Finset G) :
    (∑ g : G, (if g ∈ S then (1:ℝ) else 0) ^ 2) = (S.card : ℝ) := by
  classical
  have h1 : ∀ g : G, (if g ∈ S then (1:ℝ) else 0) ^ 2 = (if g ∈ S then (1:ℝ) else 0) := by
    intro g; by_cases hg : g ∈ S <;> simp [hg]
  rw [Finset.sum_congr rfl (fun g _ => h1 g), lrMixing_indicator_sum S]

/-! ### Variance of the centred version of a function -/

/-- Splitting off the mean never increases the sum of squares:
`∑_g (x g - mean x)² ≤ ∑_g (x g)²`. -/
lemma lrMixing_centered_sq_le {G : Type} [Fintype G] [Nonempty G] (x : G → ℝ) :
    (∑ g, (x g - (∑ g, x g) / (Fintype.card G : ℝ)) ^ 2) ≤ ∑ g, x g ^ 2 := by
  classical
  set n : ℝ := (Fintype.card G : ℝ) with hn
  have hnpos : 0 < n := by
    have h1 : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos (α := G)
    rwa [← hn] at h1
  have hnne : n ≠ 0 := ne_of_gt hnpos
  set c : ℝ := (∑ g, x g) / n with hc
  have hcn : c * n = ∑ g, x g := by rw [hc]; field_simp
  have hkey : (∑ g, (x g - c) ^ 2) = (∑ g, x g ^ 2) - c * (∑ g, x g) := by
    calc (∑ g, (x g - c) ^ 2) = ∑ g, (x g ^ 2 - 2*c*x g + c^2) := by
          apply Finset.sum_congr rfl; intro g _; ring
      _ = (∑ g, x g ^ 2) - 2*c*(∑ g, x g) + n*c^2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
              Finset.card_univ]
          simp only [nsmul_eq_mul, hn]
      _ = (∑ g, x g ^ 2) - c * (∑ g, x g) := by
          rw [show n * c ^ 2 = c * (c * n) from by ring, hcn]; ring
  calc (∑ g, (x g - (∑ g, x g) / (Fintype.card G : ℝ)) ^ 2) = ∑ g, (x g - c) ^ 2 := by rw [hc, hn]
    _ = (∑ g, x g ^ 2) - c * (∑ g, x g) := hkey
    _ ≤ ∑ g, x g ^ 2 := by
        have hcc : 0 ≤ c * (∑ g, x g) := by rw [← hcn]; nlinarith [hnpos, sq_nonneg c]
        linarith

/-! ### Cauchy–Schwarz against the expansion hypothesis -/

/-- The spectral hypothesis, read as an estimate on a bilinear form: for mean-zero `b`,
`∑_g a g · (∑_j b (g * B j))/Δ ≤ μ √((∑_g a g²)(∑_g b g²))`. -/
lemma lrMixing_cauchy_schwarz {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hB : rightExpander B μ) (a b : G → ℝ) (hb : ∑ g, b g = 0) :
    (∑ g, a g * ((∑ j, b (g * B j)) / (Δ : ℝ)))
      ≤ μ * Real.sqrt ((∑ g, a g ^ 2) * (∑ g, b g ^ 2)) := by
  classical
  have hPb : (∑ g, ((∑ j, b (g * B j)) / (Δ : ℝ)) ^ 2) ≤ μ ^ 2 * ∑ g, b g ^ 2 := hB b hb
  have hA : 0 ≤ ∑ g, a g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg (a g))
  have hB2 : 0 ≤ ∑ g, b g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg (b g))
  have hC : 0 ≤ μ ^ 2 * ∑ g, b g ^ 2 := mul_nonneg (sq_nonneg μ) hB2
  have hsq : (∑ g, a g * ((∑ j, b (g * B j)) / (Δ : ℝ))) ^ 2
      ≤ (∑ g, a g ^ 2) * (∑ g, ((∑ j, b (g * B j)) / (Δ : ℝ)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ a _
  calc (∑ g, a g * ((∑ j, b (g * B j)) / (Δ : ℝ)))
      ≤ |∑ g, a g * ((∑ j, b (g * B j)) / (Δ : ℝ))| := le_abs_self _
    _ = Real.sqrt ((∑ g, a g * ((∑ j, b (g * B j)) / (Δ : ℝ))) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ g, a g ^ 2) * (∑ g, ((∑ j, b (g * B j)) / (Δ : ℝ)) ^ 2)) :=
        Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt ((∑ g, a g ^ 2) * (μ ^ 2 * ∑ g, b g ^ 2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPb hA)
    _ = μ * Real.sqrt ((∑ g, a g ^ 2) * (∑ g, b g ^ 2)) := by
        rw [Real.sqrt_mul hA (μ ^ 2 * ∑ g, b g ^ 2),
            Real.sqrt_mul (sq_nonneg μ) (∑ g, b g ^ 2),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hμ,
            Real.sqrt_mul hA (∑ g, b g ^ 2)]
        ring

/-! ### The general mixing inequality -/

/-- **Expander mixing for the right walk.** For arbitrary real functions `f`, `h` on the finite
group,
`∑_g f g · ∑_j h (g * B j) ≤ Δ (∑_g f g)(∑_g h g)/|G| + μ Δ √((∑_g f g²)(∑_g h g²))`. -/
theorem lrMixing_general {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hB : rightExpander B μ) (f h : G → ℝ) :
    (∑ g, f g * (∑ j, h (g * B j)))
      ≤ (Δ : ℝ) * (∑ g, f g) * (∑ g, h g) / (Fintype.card G : ℝ)
        + μ * (Δ : ℝ) * Real.sqrt ((∑ g, f g ^ 2) * (∑ g, h g ^ 2)) := by
  classical
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔpos
  · subst hΔ0; simp
  have hΔne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔpos.ne'
  set n : ℝ := (Fintype.card G : ℝ) with hn
  have hnpos : 0 < n := by
    have h1 : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos (α := G)
    rwa [← hn] at h1
  have hnne : n ≠ 0 := ne_of_gt hnpos
  set cf : ℝ := (∑ g, f g) / n with hcf
  set ch : ℝ := (∑ g, h g) / n with hch
  have hcf' : (Fintype.card G : ℝ) * cf = ∑ g, f g := by
    rw [hcf]; field_simp; rw [← hn]; ring
  have hch' : (Fintype.card G : ℝ) * ch = ∑ g, h g := by
    rw [hch]; field_simp; rw [← hn]; ring
  set f' : G → ℝ := fun g => f g - cf with hf'
  set h' : G → ℝ := fun g => h g - ch with hh'
  set P : G → ℝ := fun g => (∑ j, h' (g * B j)) / (Δ : ℝ) with hP
  have hh'0 : ∑ g, h' g = 0 := by
    rw [hh', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul, hch']; ring
  have hf'0 : ∑ g, f' g = 0 := by
    rw [hf', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul, hcf']; ring
  have hP0 : ∑ g, P g = 0 := lr_walk_mean_zero B h' hh'0
  have hcs : ∑ g, f' g * P g ≤ μ * Real.sqrt ((∑ g, f' g ^ 2) * (∑ g, h' g ^ 2)) :=
    lrMixing_cauchy_schwarz B μ hμ hB f' h' hh'0
  have hf2 : ∑ g, f' g ^ 2 ≤ ∑ g, f g ^ 2 := by
    have hh := lrMixing_centered_sq_le (G := G) f
    simpa only [hf', hcf, hn] using hh
  have hh2 : ∑ g, h' g ^ 2 ≤ ∑ g, h g ^ 2 := by
    have hh := lrMixing_centered_sq_le (G := G) h
    simpa only [hh', hch, hn] using hh
  -- the walk of `h` is `Δ` times the walk of its centred version, plus the mean of `h`
  have hPh : ∀ g, (∑ j, h (g * B j)) = (Δ : ℝ) * (P g + ch) := by
    intro g
    have h1 : ∀ j : Fin Δ, h (g * B j) = h' (g * B j) + ch := by
      intro j; rw [hh']; ring
    calc (∑ j, h (g * B j)) = ∑ j, (h' (g * B j) + ch) :=
          Finset.sum_congr rfl (fun j _ => h1 j)
      _ = (∑ j, h' (g * B j)) + (Δ : ℝ) * ch := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
      _ = (Δ : ℝ) * (P g + ch) := by
          rw [hP]; field_simp
  have hsumP : ∑ g, f g * P g = ∑ g, f' g * P g := by
    have h1 : ∀ g, f g = f' g + cf := by intro g; rw [hf']; ring
    calc ∑ g, f g * P g = ∑ g, (f' g + cf) * P g :=
          Finset.sum_congr rfl (fun g _ => by rw [h1 g])
      _ = ∑ g, (f' g * P g + cf * P g) := by
          apply Finset.sum_congr rfl; intro g _; ring
      _ = (∑ g, f' g * P g) + cf * (∑ g, P g) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ g, f' g * P g := by rw [hP0]; ring
  have hsum : (∑ g, f g * (∑ j, h (g * B j)))
      = (Δ : ℝ) * ((∑ g, f' g * P g) + ch * (∑ g, f g)) := by
    calc ∑ g, f g * (∑ j, h (g * B j))
        = ∑ g, f g * ((Δ : ℝ) * (P g + ch)) :=
          Finset.sum_congr rfl (fun g _ => by rw [hPh g])
      _ = (Δ : ℝ) * ∑ g, f g * (P g + ch) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
      _ = (Δ : ℝ) * ((∑ g, f g * P g) + ch * (∑ g, f g)) := by
          congr 1
          calc ∑ g, f g * (P g + ch) = ∑ g, (f g * P g + ch * f g) := by
                apply Finset.sum_congr rfl; intro g _; ring
            _ = (∑ g, f g * P g) + ch * (∑ g, f g) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Δ : ℝ) * ((∑ g, f' g * P g) + ch * (∑ g, f g)) := by rw [hsumP]
  rw [hsum]
  have hbound : (∑ g, f' g * P g) ≤ μ * Real.sqrt ((∑ g, f g ^ 2) * (∑ g, h g ^ 2)) := by
    refine le_trans hcs ?_
    have hfA : (0:ℝ) ≤ ∑ g, f g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg (f g))
    have hsq : (∑ g, f' g ^ 2) * (∑ g, h' g ^ 2) ≤ (∑ g, f g ^ 2) * (∑ g, h g ^ 2) :=
      mul_le_mul hf2 hh2 (Finset.sum_nonneg (fun g _ => sq_nonneg (h' g))) hfA
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hμ
  calc (Δ : ℝ) * ((∑ g, f' g * P g) + ch * (∑ g, f g))
      ≤ (Δ : ℝ) * (μ * Real.sqrt ((∑ g, f g ^ 2) * (∑ g, h g ^ 2)) + ch * (∑ g, f g)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hbound]
    _ = (Δ : ℝ) * (∑ g, f g) * (∑ g, h g) / n
          + μ * (Δ : ℝ) * Real.sqrt ((∑ g, f g ^ 2) * (∑ g, h g ^ 2)) := by
        rw [hch]; field_simp; ring

/-! ### The target: edges between two vertex sets -/

/-- **Bipartite expander mixing for the right walk of `B`.** If the walk `x ↦ (g ↦ avg_j x (g * B j))`
contracts mean-zero functions by `μ` (i.e. `rightExpander B μ`), then the number of edges with tail
in `S` and head in `T` is at most `Δ |S| |T| / |G| + μ Δ √(|S| |T|)`. -/
theorem lr_mixing {G : Type} [Group G] [Fintype G] [DecidableEq G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hB : rightExpander B μ) (S T : Finset G) :
    ((S.sum fun g => (Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      ≤ (Δ : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card G : ℝ)
        + μ * (Δ : ℝ) * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  classical
  have hgen : (∑ g, (if g ∈ S then (1:ℝ) else 0) * (∑ j, (if g * B j ∈ T then (1:ℝ) else 0)))
      ≤ (Δ : ℝ) * (∑ g, (if g ∈ S then (1:ℝ) else 0)) * (∑ g, (if g ∈ T then (1:ℝ) else 0))
          / (Fintype.card G : ℝ)
        + μ * (Δ : ℝ) * Real.sqrt (((∑ g, (if g ∈ S then (1:ℝ) else 0) ^ 2))
            * ((∑ g, (if g ∈ T then (1:ℝ) else 0) ^ 2))) := by
    simpa using lrMixing_general (G := G) B μ hμ hB (fun g => (if g ∈ S then (1:ℝ) else 0))
      (fun g => (if g ∈ T then (1:ℝ) else 0))
  rw [lr_mixing_count B S T]
  refine le_trans hgen ?_
  rw [lrMixing_indicator_sum S, lrMixing_indicator_sum_sq S,
      lrMixing_indicator_sum T, lrMixing_indicator_sum_sq T]

end Work.LT
