import Submission.Work.ConeSwitch.A1Faithful
import Submission.Work.ConeSwitch.A2Consts
import Submission.Work.S12Faithful.Cone
import Submission.EFL.BigEdges
import Submission.EFL.LargeEdgeThm
import Submission.EFL.S12Mprev
import Submission.EFL.S12Step1Full
import Submission.EFL.OptCol

/-!
# §12, the faithful endgame

`ErdosFaberLovaszConjecture.eflStatement` from the paper's deep inputs, with the GKO input in
its *faithful* (existential-threshold) form `Work.Deep.GKO.GKOStatementFixed` rather than the
`σ`-pinned linear hierarchy of the old `GKOStatement`.

The point of the re-architecture is the *order* of the quantifiers: Corollary 10.13 has
thresholds `ν₀(p), ε₀(p)` depending on the density `p`, so the §12 parameters must be chosen
*after* those thresholds are known:

1. the Large Edge Theorem's hierarchy is walked by hand (`γ₂`, `δ`, `σ`, `γ`, `β`, `r₁`, `r₀`,
   `N₀`), each constant chosen below the corresponding threshold;
2. the A₂ density is `ρ := σ/2`, and Corollary 10.13 is applied at the density `p := ρ/4` of
   `G_final` itself, giving `η₀, ε₀`;
3. `γ`, `β`, `r₁`, `r₀` are chosen as mins with the thresholds `ε₀, η₀` and with `ρ`, so that
   the smallness bundle `S12A2Small` holds; the fullness parameter `ε ≲ M` produced by
   `Work.ConeSwitch.exists_A2_params` is then `≲ ε₀²`, which is exactly what the faithful
   Corollary 10.13 needs;
4. the case split is taken at that *free* `(ρ, ε)`: `IsFull 𝓗 ρ ε` gives the Type-A₂ branch
   (`Work.S12Faithful.s12_branch_A2_faithful`) and otherwise the Type-A₁ branch
   (`Work.ConeSwitch.s12_branch_A1_faithful`), whose reservoir is `IsReservoirTypeA1` and whose
   finishing is Vizing's theorem.  Both branches are parametric in `(ρ, ε)`, as in the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.ConeSwitch

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Sanity: the cone's GKO input is the `GKO` chapter's theorem.**

`ErdosFaberLovaszConjecture.GKOStatement` (`Submission/EFL/OptCol.lean`) is written out with
the *verbatim* body of `Work.Deep.GKO.GKOStatementFixed`, so the two `Prop`s are
definitionally equal: this `rfl` is the machine-checked evidence, and it is what lets the
`GKO` chapter's theorems (`Work.S12Faithful.optcol_corollary_faithful`, and hence the whole
assembly below) be applied to `hGKO` without a conversion lemma.  (The cone cannot *abbrev*
the chapter's definition, because the chapter imports `Submission.EFL.OptCol`.) -/
theorem gkoStatement_eq_fixed :
    ErdosFaberLovaszConjecture.GKOStatement = Work.Deep.GKO.GKOStatementFixed := rfl

/-- **Theorem 1.1 from the four deep inputs, with the faithful GKO input.** -/
theorem eflStatement_of_deep_faithful (hMR : MolloyReedStatement) (hK : KahnStatement)
    (hNib : NibbleStatementFixed) (hGKO : Work.Deep.GKO.GKOStatementFixed) :
    eflStatement := by
  classical
  refine eflStatement_of_bigEdges ?_
  -- ## 1. the hierarchy of Theorem 6.7
  set γ₂ : ℝ := (10 : ℝ) ^ (-30 : ℤ) with hγ₂def
  have hγ₂0 : 0 < γ₂ := by rw [hγ₂def]; positivity
  have hγ₂1 : γ₂ ≤ 1 := by rw [hγ₂def]; norm_num
  have hγ₂24 : γ₂ ≤ (10 : ℝ) ^ (-24 : ℤ) := by rw [hγ₂def]; norm_num
  obtain ⟨δ₀, hδ₀0, hδ₀γ₂, Hδ⟩ := largeEdgeThmStatement_of_deep hMR hK γ₂ hγ₂0 hγ₂1
  set δ : ℝ := min δ₀ (γ₂ / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0 (by linarith only [hγ₂0])
  have hδγ₂ : δ ≤ γ₂ / 2 := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨σ₀, hσ₀0, hσ₀δ, Hσ⟩ := Hδ δ hδ0 hδδ₀
  set σ : ℝ := min σ₀ (δ / 2) with hσdef
  have hσ0 : 0 < σ := lt_min hσ₀0 (by linarith only [hδ0])
  have hσδhalf : σ ≤ δ / 2 := min_le_right _ _
  have hσσ₀ : σ ≤ σ₀ := min_le_left _ _
  have hσδ : σ ≤ δ := by linarith only [hσδhalf, hδ0]
  obtain ⟨γ₁₀, hγ₁₀0, hγ₁₀σ, Hγ₁⟩ := Hσ σ hσ0 hσσ₀
  have hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ) := by
    have h1 : σ ≤ γ₂ / 2 := by linarith only [hσδhalf, hδγ₂]
    have h2 : γ₂ / 2 ≤ (10 : ℝ) ^ (-24 : ℤ) := by
      rw [hγ₂def]
      norm_num
    exact le_trans h1 h2
  -- ## 2. the A₂ density and the faithful Corollary 10.13 at `p = ρ/4`
  set ρ : ℝ := σ / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hσ100 : σ ≤ 1 / 100 := by
    have h1 : σ ≤ (10 : ℝ) ^ (-24 : ℤ) := hσ24
    norm_num at h1 ⊢
    linarith only [h1]
  have hρ100 : ρ ≤ 1 / 100 := by rw [hρdef]; linarith only [hσ100]
  have hp0 : 0 < ρ / 4 := by positivity
  have hp1 : ρ / 4 < 1 := by linarith only [hρ100]
  obtain ⟨η₀, ε₀, hη₀0, hε₀0, hε₀p, hcor₀⟩ :=
    Work.S12Faithful.optcol_corollary_faithful hGKO (ρ / 4) hp0 hp1
  -- ## 3. the constants, chosen below the thresholds
  set M : ℝ := min (min (ε₀ ^ 2 / 16) (ε₀ / (2 * 10 ^ 6)))
      (min (η₀ / 22) (min (ρ ^ 2 / 20) (ρ / 80))) with hMdef
  have hM0 : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  set γt : ℝ := min (min (min (min (1 / 2) (ρ / (4 * 10 ^ 6))) ((ρ / 30) ^ 2))
      ((ρ * M / (4 * 10 ^ 6)) ^ 2)) (σ ^ 10 / 10 ^ 250) with hγtdef
  have hγt0 : 0 < γt := by
    rw [hγtdef]
    refine lt_min (lt_min (lt_min (lt_min (by norm_num) ?_) ?_) ?_) (by positivity)
    · positivity
    · positivity
    · positivity
  set γ : ℝ := min γ₁₀ γt with hγdef
  have hγ0 : 0 < γ := lt_min hγ₁₀0 hγt0
  have hγγ₁₀ : γ ≤ γ₁₀ := min_le_left _ _
  have hγγt : γ ≤ γt := min_le_right _ _
  have hγt_le_half : γt ≤ 1 / 2 := by
    rw [hγtdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hγt_le_ρs : γt ≤ ρ / (4 * 10 ^ 6) := by
    rw [hγtdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hγt_le_30 : γt ≤ (ρ / 30) ^ 2 := by
    rw [hγtdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hγt_le_M : γt ≤ (ρ * M / (4 * 10 ^ 6)) ^ 2 := by
    rw [hγtdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hγt_le_σ : γt ≤ σ ^ 10 / 10 ^ 250 := by
    rw [hγtdef]; exact min_le_right _ _
  have hγ1 : γ ≤ 1 := le_trans hγγt (le_trans hγt_le_half (by norm_num))
  have hγρs : 10 ^ 6 * (2 * γ) ≤ ρ / 2 := by
    have h1 : γ ≤ ρ / (4 * 10 ^ 6) := le_trans hγγt hγt_le_ρs
    nlinarith only [h1]
  have h30 : 30 * Real.sqrt γ ≤ ρ := by
    have h1 : γ ≤ (ρ / 30) ^ 2 := le_trans hγγt hγt_le_30
    have h2 : Real.sqrt γ ≤ ρ / 30 := by
      calc Real.sqrt γ ≤ Real.sqrt ((ρ / 30) ^ 2) := Real.sqrt_le_sqrt h1
        _ = ρ / 30 := Real.sqrt_sq (by positivity)
    linarith only [h2]
  have hsmall₀ : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤
      min (min (ε₀ ^ 2 / 16) (ε₀ / (2 * 10 ^ 6)))
        (min (η₀ / 22) (min (ρ ^ 2 / 20) (ρ / 80))) := by
    have h1 : γ ≤ (ρ * M / (4 * 10 ^ 6)) ^ 2 := le_trans hγγt hγt_le_M
    have h2 : Real.sqrt γ ≤ ρ * M / (4 * 10 ^ 6) := by
      calc Real.sqrt γ ≤ Real.sqrt ((ρ * M / (4 * 10 ^ 6)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = ρ * M / (4 * 10 ^ 6) := Real.sqrt_sq (by positivity)
    rw [div_le_iff₀ hρ0]
    rw [hMdef] at h2
    nlinarith only [h2]
  have hγσ : γ ≤ σ ^ 10 / 10 ^ 250 := le_trans hγγt hγt_le_σ
  -- the remaining constants
  obtain ⟨β₀, hβ₀0, hβ₀γ, Hβ⟩ := Hγ₁ γ hγ0 hγγ₁₀
  set β : ℝ := min β₀ (min (γ ^ 2 / 16) (γ ^ 4 / 10 ^ 12)) with hβdef
  have hβ0 : 0 < β :=
    lt_min hβ₀0 (lt_min (div_pos (pow_pos hγ0 2) (by norm_num))
      (div_pos (pow_pos hγ0 4) (by norm_num)))
  have hββ₀ : β ≤ β₀ := min_le_left _ _
  have hβ_le_sq : β ≤ γ ^ 2 / 16 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hβ4 : β ≤ γ ^ 4 / 10 ^ 12 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hγsq_le_γ : γ ^ 2 ≤ γ := by
    have h1 : γ * γ ≤ γ * 1 := mul_le_mul_of_nonneg_left hγ1 hγ0.le
    nlinarith only [h1]
  have hβ1 : β ≤ 1 := by
    have h2 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ0.le hγ1
    nlinarith only [hβ_le_sq, h2]
  have hβγ : β ≤ γ := by
    have h1 : γ * γ ≤ 16 * γ := mul_le_mul_of_nonneg_right (by linarith only [hγ1]) hγ0.le
    nlinarith only [hβ_le_sq, h1]
  have hβsq : 8 * β ≤ γ ^ 2 := by nlinarith only [hβ_le_sq]
  obtain ⟨R₁, _hR₁0, HR₁⟩ := Hβ β hβ0 hββ₀
  set r₁ : ℕ := max R₁ (max 10 ⌈32 / β⌉₊) with hr₁def
  have hr₁R₁ : R₁ ≤ r₁ := le_max_left _ _
  have h10r₁ : 10 ≤ r₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hr₁2 : 2 ≤ r₁ := by omega
  have hceil₁ : (⌈32 / β⌉₊ : ℝ) ≤ (r₁ : ℝ) := by
    exact_mod_cast (le_trans (le_max_right _ _) (le_max_right _ _) : ⌈32 / β⌉₊ ≤ r₁)
  have hβr₁ : 32 ≤ β * (r₁ : ℝ) := by
    have h1 : 32 / β ≤ (⌈32 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (32 : ℝ) ≤ β * (⌈32 / β⌉₊ : ℝ) := by
      rw [div_le_iff₀ hβ0] at h1
      linarith only [h1]
    nlinarith only [hβ0, hceil₁, h2, Nat.cast_nonneg (α := ℝ) ⌈32 / β⌉₊]
  obtain ⟨R₀, _hR₀0, HR₀⟩ := HR₁ r₁ hr₁R₁
  set M₀ : ℕ := max 2 (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ + 2) with hM₀def
  set r₀ : ℕ := max R₀ M₀ with hr₀def
  have hr₀R₀ : R₀ ≤ r₀ := le_max_left _ _
  have hM₀r₀ : M₀ ≤ r₀ := le_max_right _ _
  have hr₀2 : 2 ≤ r₀ := by
    have h1 : 2 ≤ M₀ := le_max_left _ _
    omega
  have hceilr₀ : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) + 2 ≤ (r₀ : ℝ) := by
    have h3 : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ + 2 : ℕ) ≤ M₀ :=
      le_max_right _ _
    have h4 : M₀ ≤ r₀ := le_max_right _ _
    have h5 : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) + 2 ≤ (r₀ : ℝ) := by
      have h6 : ((⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ + 2 : ℕ) : ℝ) ≤ (r₀ : ℝ) :=
        by exact_mod_cast (le_trans h3 h4)
      push_cast at h6
      exact h6
    exact h5
  have hceilr₁ : (r₁ : ℝ) < (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) + 2 := by
    have h1 : (r₁ : ℝ) ≤ (r₁ : ℝ) / β := by
      rw [le_div_iff₀ hβ0]; nlinarith only [hβ1, h10r₁]
    have h2 : (r₁ : ℝ) / β ≤ max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β) := le_max_right _ _
    have h3 : max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β) ≤
        (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) := Nat.le_ceil _
    linarith only [h1, h2, h3]
  have hβr₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1) := by
    have h0 : (r₁ : ℝ) / β ≤ (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) :=
      le_trans (le_max_right _ _) (Nat.le_ceil _)
    have h1 : (r₁ : ℝ) ≤ (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) * β :=
      (div_le_iff₀ hβ0).mp h0
    have h2 : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) + 1 ≤ (r₀ : ℝ) := by
      linarith only [hceilr₀]
    nlinarith only [h1, h2, hβ0]
  have hγr₀ : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1) := by
    have h0 : 4 * (r₁ : ℝ) / γ ≤ (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) :=
      le_trans (le_max_left _ _) (Nat.le_ceil _)
    have h1 : 4 * (r₁ : ℝ) ≤ (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) * γ :=
      (div_le_iff₀ hγ0).mp h0
    have h2 : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) ≤ (r₀ : ℝ) - 2 := by
      linarith only [hceilr₀]
    have h3 : ((r₀ : ℝ) - 2) * γ < ((r₀ : ℝ) - 1) * γ := by nlinarith only [hγ0]
    have h4 : (⌈max (4 * (r₁ : ℝ) / γ) ((r₁ : ℝ) / β)⌉₊ : ℝ) * γ ≤ ((r₀ : ℝ) - 2) * γ :=
      mul_le_mul_of_nonneg_right h2 hγ0.le
    nlinarith only [h1, h3, h4, hγ0]
  have hr₁r₀ : r₁ < r₀ := by
    have h5 : (r₁ : ℝ) < (r₀ : ℝ) := by linarith only [hceilr₁, hceilr₀]
    exact_mod_cast h5
  obtain ⟨N₀, _hN₀pos, HN₀⟩ := HR₀ r₀ hr₀R₀
  -- ## 4. the numeric data and the two Step-2 producers
  obtain ⟨ε, ζ, η, ηr, hε0, hζ0, hη0, hηr0, hζε₀, hηη₀, hs⟩ :=
    Work.ConeSwitch.exists_A2_params (ρ := ρ) (γ := γ) (β := β) (r₁ := r₁) (r₀ := r₀)
      (ε₀ := ε₀) (η₀ := η₀) hρ0 hρ100 hε₀0 hη₀0 hγ0 hγ1 hβ0 hβγ hβsq hβ4 hγρs h30
      hr₁2 hr₀2 hr₁r₀ hβr₁ hβr₀ hγr₀ hsmall₀
  obtain ⟨ξ, hξ0, hdataN, hdata⟩ := Work.S12Faithful.exists_S12A2Data_of_small hK hs
  have hρ1 : ρ ≤ 1 := by linarith only [hρ100]
  obtain ⟨N₁, hA2⟩ := s12_step2_typeA2 (ρ := ρ) (ξ := ξ) hρ0 hρ1 hξ0
  obtain ⟨N₂, hA1⟩ := s12_step2_typeA1 (ρ := ρ) (ξ := ξ) hρ0 hρ1 hξ0
  obtain ⟨N₃, hN₃⟩ := exists_cvFinset_card_le
  obtain ⟨Ncor, hNcor⟩ := hcor₀ η ζ hη0 hηη₀ hζ0 hζε₀
  have hγ₂half : γ₂ / 2 ≤ γ₂ := by nlinarith only [hγ₂0]
  have hγγ₂ : γ ≤ γ₂ :=
    le_trans hγγ₁₀ (le_trans hγ₁₀σ (le_trans hσδ (le_trans hδγ₂ hγ₂half)))
  have hβsq₁ : β ≤ γ ^ 2 / 16 := hβ_le_sq
  have hδγ : δ ≤ γ₂ := le_trans hδγ₂ hγ₂half
  obtain ⟨NB, hNB⟩ :=
    s12_B_main (σ := σ) (γ := γ₂) (γ₁ := γ) (β := β) (δ := δ) (r₁ := r₁) (r₀ := r₀)
      hNib hK hβ0 hβγ hβsq₁ hβ4 hγσ hσ0 hσ24 hσδ hδ0
      hδγ hγ₂0 (by rw [hγ₂def])
      hr₁2 hr₀2 hr₁r₀ hβr₁ hβr₀ hγr₀
  -- ## 5. the endgame, for every large `n`
  refine ⟨max (nibbleThr r₁ (2 * β) (2 * γ) ε (ρ / 2) ξ)
      (max (nibbleThr r₁ (2 * β) (2 * γ) ε ρ ξ)
        (max hdataN (max N₀ (max N₁ (max N₂ (max N₃ (max Ncor (max NB (max ⌈4 / σ⌉₊ 1))))))))),
    ?_⟩
  intro n hn 𝓗 hlin hbigT
  have hbig2 : ∀ e ∈ 𝓗, 2 ≤ edgeSize e := fun e he => by
    rw [edgeSize_eq_ncard]
    obtain ⟨x, y, hx, hy, hxy⟩ := hbigT e he
    have h1 : 1 < e.ncard := (Set.one_lt_ncard (Set.toFinite e)).mpr ⟨x, hx, y, hy, hxy⟩
    omega
  have hThrA2 : nibbleThr r₁ (2 * β) (2 * γ) ε (ρ / 2) ξ ≤ n := by omega
  have hThrA1 : nibbleThr r₁ (2 * β) (2 * γ) ε ρ ξ ≤ n := by omega
  have hnD : hdataN ≤ n := by omega
  have hnN₀ : N₀ ≤ n := by omega
  have hnN₁ : N₁ ≤ n := by omega
  have hnN₂ : N₂ ≤ n := by omega
  have hnN₃ : N₃ ≤ n := by omega
  have hnNcor : Ncor ≤ n := by omega
  have hnNB : NB ≤ n := by omega
  have hnceil : (⌈4 / σ⌉₊ : ℕ) ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  rcases HN₀ n hnN₀ (medLarge 𝓗 r₁) (fun e => e.property.2)
    (ErdosFaberLovaszConjecture.IsLinear.medLarge hlin) with hNE | hE
  · -- ## Type A
    obtain ⟨φ, hA⟩ := isTypeA_of_nonExtremal_medLarge hNE
    have hd := hdata n hnD
    have hn1' : 1 ≤ n := hd.hm.hn1
    set U : Set (Fin n) := Vplus 𝓗 (1 - ε) with hUdef
    have hVcard := hN₃ n hnN₃ φ U
    have h3r : 3 ≤ r₁ := by omega
    have hε9A2 : 4 * (10 : ℝ) ^ (-9 : ℤ) * ε ≤ ρ / 2 := by
      have hc : (4 : ℝ) * 10 ^ (-9 : ℤ) = 4 / 10 ^ 9 := by norm_num [zpow_neg]
      rw [hc]
      have h20 := hd.h20ε
      nlinarith only [h20, hρ0, hρ1]
    have hMCA2 : Work.Deep.Nibble.MarginsConst r₁ (2 * β) (2 * γ) ε (ρ / 2) ξ :=
      marginsConst_of_bundle hd.hm.hnib h3r hε9A2
    have hNibP2 : NibblePointwise r₁ (2 * β) (2 * γ) ε (ρ / 2) ξ n :=
      nibbleAbove_nibbleThr hMCA2 hThrA2
    have hDgapρ : (Dparam n ρ : ℝ) ≤ (1 - ρ) * (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
      rw [Dparam]
      have h3 : (⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
        Nat.floor_le (by nlinarith only [hρ0, hρ1, hn0, hn1r])
      nlinarith only [h3, hρ0, hρ1, hn0, hn1r]
    have hmρ : S12Margins n r₁ r₀ β γ ρ ρ ξ ε (1 / 2) :=
      S12Margins.mono_rho_abs hd.hm (by linarith only [hρ0]) hρ1 hDgapρ
    have hε9A1 : 4 * (10 : ℝ) ^ (-9 : ℤ) * ε ≤ ρ := by
      have hc : (4 : ℝ) * 10 ^ (-9 : ℤ) = 4 / 10 ^ 9 := by norm_num [zpow_neg]
      rw [hc]
      have h20 := hd.h20ε
      nlinarith only [h20, hρ0, hρ1]
    have hMCA1 : Work.Deep.Nibble.MarginsConst r₁ (2 * β) (2 * γ) ε ρ ξ :=
      marginsConst_of_bundle hmρ.hnib h3r hε9A1
    have hNibP1 : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ ξ n :=
      nibbleAbove_nibbleThr hMCA1 hThrA1
    have hDlb : (1 - σ) * (n : ℝ) ≤ (Dparam n ρ : ℝ) := by
      have h2σ : (4 : ℝ) / σ ≤ (n : ℝ) := by
        have h2 : (4 : ℝ) / σ ≤ (⌈4 / σ⌉₊ : ℝ) := Nat.le_ceil _
        have h3 : (⌈4 / σ⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnceil
        linarith only [h2, h3]
      have h2σ' : (4 : ℝ) ≤ σ * (n : ℝ) := by
        have h := (div_le_iff₀ hσ0).mp h2σ
        linarith only [h]
      have hmain : (1 - σ) * (n : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) - 1 := by
        rw [hρdef]
        linarith only [h2σ', hσ0]
      have hfloor : (1 - ρ) * ((n : ℝ) - 1) - 1 < (Dparam n ρ : ℝ) := by
        rw [Dparam]
        have h := Nat.lt_floor_add_one ((1 - ρ) * ((n : ℝ) - 1))
        push_cast at h
        linarith only [h]
      linarith only [hmain, hfloor]
    by_cases hfull : IsFull 𝓗 ρ ε
    · -- ## Type A₂
      obtain ⟨R_res, -, hresA2, -, -, -⟩ :=
        hA2 n hnN₁ 𝓗 hlin φ U rfl hn1' hd.hε0 hfull hVcard mem_cvFinset_univ
          (by linarith only [hd.hεn3]) (by nlinarith only [hd.hεn3, hd.hε0]) hd.hρ100
          hd.hρn25 hd.h20ε hd.h20εξ hd.hξε hd.hξn
      obtain ⟨hRres_pow2, R_abs, Rreg, hRres_eq, hRabs, hRabs_low, hReg⟩ := hresA2
      have hRabs_sub : R_abs ⊆ R_res := by rw [hRres_eq]; exact Set.subset_union_left
      have hRabs_pow2 : R_abs ⊆ 𝓗.pow2 := fun e he =>
        hRres_pow2 (by rw [hRres_eq]; exact Or.inl he)
      have hcor : ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
          SelfLowerRegular 𝓖 Set.univ (ρ / 4) ζ →
          (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
          (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
            (hypergraphMaxDegree 𝓖 : ℝ)) → 𝓖.Colorable (hypergraphMaxDegree 𝓖) := by
        intro 𝓖 h2 hreg hdelta hcount
        exact hNcor n hnNcor 𝓖 h2 hreg hdelta hcount
      exact s12_branch_A2_faithful hNibP2 hd hDlb hlin hbig2 hUdef hA hfull hRres_pow2
        hRabs hRabs_low hRabs_sub hRabs_pow2 ⟨Rreg, hRres_eq, hReg⟩ hcor
    · -- ## Type A₁
      obtain ⟨R_res, R_abs, hresA1, hRabs, hRabs_sub, hRabs_pow2⟩ :=
        hA1 n hnN₂ 𝓗 hlin φ U rfl hn1' hVcard
      exact s12_branch_A1_faithful hNibP1 hd hDlb hlin hbig2 hUdef hA hfull hresA1
        hRabs hRabs_sub hRabs_pow2
  · -- ## Type B
    obtain ⟨φ, hB⟩ := isTypeB_of_extremal_medLarge hE
    exact hNB n hnNB 𝓗 hlin hbig2 ⟨φ, hB⟩

end

end Work.ConeSwitch
