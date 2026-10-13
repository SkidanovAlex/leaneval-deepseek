import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilkiesI

theorem ImageBallEq {μ n : ℕ} (e : Fin μ ↪ Fin n) {U : Set (Fin μ → ℝ)} {ψ : (Fin μ → ℝ) → (Fin n → ℝ)} (hsec : ∀ t ∈ U, ψ t ∘ e = t) {V : Set (Fin n → ℝ)} {p : Fin n → ℝ} {δ : ℝ} (hgraph : V ∩ {x : Fin n → ℝ | ∀ i, |x i - p i| < δ} = ψ '' U) {t₀ : Fin μ → ℝ} (ht₀ : t₀ ∈ U) (hψt₀ : ψ t₀ = p) {η : ℝ} (hη : 0 < η) (hball : Metric.ball t₀ η ⊆ U) : V ∩ {x : Fin n → ℝ | ∀ i, |x i - p i| < δ} ∩ {x : Fin n → ℝ | ∀ j, |x (e j) - p (e j)| < η} = ψ '' Metric.ball t₀ η := by
  ext x
  constructor
  · -- `x` lies in the graph piece, hence is `ψ t` for some `t ∈ U`; the `e`-box
    -- condition forces `t` to lie in the ball around `t₀`.
    rintro ⟨⟨hV, hA⟩, hB⟩
    have hx : x ∈ ψ '' U := by rw [← hgraph]; exact ⟨hV, hA⟩
    obtain ⟨t, htU, htx⟩ := hx
    refine ⟨t, ?_, htx⟩
    rw [Metric.mem_ball, dist_pi_lt_iff hη]
    intro j
    have h1 : x (e j) = t j := by
      rw [← htx]
      simpa using congr_fun (hsec t htU) j
    have h2 : p (e j) = t₀ j := by
      rw [← hψt₀]
      simpa using congr_fun (hsec t₀ ht₀) j
    simpa [Real.dist_eq, h1, h2] using hB j
  · -- Conversely `ψ t` for `t` in the ball lies in the graph piece (since `t ∈ U`)
    -- and its `e`-coordinates are those of `t`.
    rintro ⟨t, ht, htx⟩
    subst htx
    have htU : t ∈ U := hball ht
    have hmem : ψ t ∈ V ∩ {x : Fin n → ℝ | ∀ i, |x i - p i| < δ} := by
      rw [hgraph]; exact ⟨t, htU, rfl⟩
    refine ⟨⟨hmem.1, hmem.2⟩, ?_⟩
    intro j
    have h1 : ψ t (e j) = t j := by simpa using congr_fun (hsec t htU) j
    have h2 : p (e j) = t₀ j := by
      rw [← hψt₀]
      simpa using congr_fun (hsec t₀ ht₀) j
    have htd : dist t t₀ < η := Metric.mem_ball.mp ht
    have : dist (t j) (t₀ j) < η := lt_of_le_of_lt (dist_le_pi_dist t t₀ j) htd
    simpa [Real.dist_eq, h1, h2] using this

end Work.WilkiesI
