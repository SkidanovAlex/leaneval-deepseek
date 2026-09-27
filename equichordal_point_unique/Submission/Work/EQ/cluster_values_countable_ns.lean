import Mathlib
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.junction_values_countable_ns
import Submission.Work.EQ.H0_junction_value_of_cluster

/-!
# Step 5 of `H0_regular` in counting form

The assembly of Rychlik's step 5: for a small radius `δ`, the set of values `c₀ ≠ 0` that occur as
the common `ψ`-limit of chains of `⁰H` whose `ψ₁` cluster at every point of an uncountable subset
of an annulus of outer radius `< δ` is countable.

The two mathematical inputs are `Work.EQ.junction_values_countable` (the junction values of a fixed
tuple `(N, ε, η, s)` are countable) and `Work.EQ.H0_junction_value_of_cluster` (every such cluster
value is, up to a characteristic value, a junction value).  The logical trichotomy at the chosen
radius is `Work.EQ.fan_trichotomy'`.
-/

namespace Work.EQ.CVC

open Filter _root_.Topology

/-- The trichotomy predicate is monotone in the radius. -/
theorem FanTrich_mono {a : ℝ} {h : ℂ → ℂ} {δ δ' : ℝ} (hδ' : δ' ≤ δ) (H : FanTrich a h δ) :
    FanTrich a h δ' := by
  intro ε
  obtain ⟨φ, hφ, H⟩ := H ε
  refine ⟨φ, hφ, ?_⟩
  have hsub : Metric.ball (0 : ℂ) δ' ⊆ Metric.ball 0 δ := Metric.ball_subset_ball hδ'
  rcases H with ⟨ε₀, h1⟩ | ⟨ε₀, ε₁, s, C, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨ε₀, fun k => (h1 k).mono hsub⟩
  · exact Or.inr (Or.inl ⟨ε₀, ε₁, s, C, h1, h2, h3, h4, h5, h6, h7, h8.mono hsub⟩)
  · exact Or.inr (Or.inr ⟨h1, fun η hη => (h2 η hη).mono fun k hk u hu => hk u (hsub hu)⟩)

/-- **Step 5 of `H0_regular` (Rychlik (140)–(141)), counting form.** There is a radius `δ` such
that for every annulus `r₁ ≤ ‖z‖ ≤ r₂` with `r₂ < δ`, only countably many values `c₀ ≠ 0` arise
as the common `ψ`-limit of chains of `H0` whose `ψ₁` cluster at every point of an uncountable
subset of the annulus. -/
theorem cluster_values_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₂ < δ →
      {c₀ : ℂ | c₀ ≠ 0 ∧ ∃ (Z : Set ℂ) (X : ℂ → ℕ → ChainData), ¬ Z.Countable ∧
        (∀ z ∈ Z, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂) ∧ (∀ z ∈ Z, ∀ k, X z k ∈ H0 a h) ∧
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1) atTop (𝓝 z)) ∧
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1 * (X z k).2.2) atTop (𝓝 c₀))}.Countable := by
  obtain ⟨δ₁, hδ₁, hJ⟩ := JVC.junction_values_countable ha0 ha1 hh
  obtain ⟨δ₀, hδ₀, hjunc⟩ := H0_junction_value_of_cluster ha0 ha1 hh
  obtain ⟨δt, hδt, htri⟩ := fan_trichotomy' ha0 ha1 hh
  refine ⟨min (min δ₁ δ₀) δt, lt_min (lt_min hδ₁ hδ₀) hδt, fun {r₁ r₂} hr₁ hr₂ => ?_⟩
  set δ := min (min δ₁ δ₀) δt with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ hδ₀) hδt
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ0 : δ ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have htri' : FanTrich a h δ := FanTrich_mono (min_le_right _ _) htri
  let J : ℕ × List Bool × List Bool × List Bool → Set ℂ := fun p =>
    {c : ℂ | ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
          ‖((eqLam a : ℝ) : ℂ) ^ p.1 * (c / w)‖ < δ₁ ∧
          bwdP a p.2.2.2 (fan a h p.2.1 w) =
            eqMirror (fan a h p.2.2.1 (((eqLam a : ℝ) : ℂ) ^ p.1 * (c / w)))}.Countable}
  have hMc : (charValSet a h).Countable := countable_charValSet a h
  have : Countable (charValSet a h) := hMc.to_subtype
  refine Set.Countable.mono ?_ (Set.countable_iUnion fun p : ℕ × List Bool × List Bool × List Bool =>
    Set.countable_iUnion fun μ : charValSet a h × charValSet a h =>
      ((hJ p.1 p.2.1 p.2.2.1 p.2.2.2).image fun c => c / ((μ.1 : ℂ) * (μ.2 : ℂ))))
  rintro c₀ ⟨hc₀, Z, X, hZ, hZann, hX, hX1, hX2⟩
  obtain ⟨N, ε, η, s, μ₁, μ₂, hμ₁, hμ₂, hμ, hunc⟩ :=
    hjunc hδpos hδ0 htri' hc₀ hr₁ hr₂ hZ hZann X hX hX1 hX2
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨(N, ε, η, s), (⟨μ₁, hμ₁⟩, ⟨μ₂, hμ₂⟩), μ₁ * μ₂ * c₀, ?_, ?_⟩
  · intro hcount
    apply hunc
    refine hcount.mono ?_
    rintro w ⟨hw0, hw, hfar, hid⟩
    exact ⟨hw0, lt_of_lt_of_le hw hδ1, lt_of_lt_of_le hfar hδ1, hid⟩
  · show μ₁ * μ₂ * c₀ / (μ₁ * μ₂) = c₀
    exact mul_div_cancel_left₀ c₀ hμ

end Work.EQ.CVC
