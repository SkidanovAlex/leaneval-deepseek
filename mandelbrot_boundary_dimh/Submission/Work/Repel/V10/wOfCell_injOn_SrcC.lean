import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.chain_image_mem

namespace Work.Repel.V10

open MandelDim Complex Set Metric Filter Topology

/-- **`wOfCell` is injective on a §6 source region.**  `V.wOfCell (j,k,n) w =
V.wOf (ĥ^[j] (V.uOf (s·π w)) - k)` with `ĥ = R - β`.  If `P₁.φ` is injective on
`W 0 = ball cbase ρ` (the hypothesis `hW0` — this is exactly the v10 hypothesis `hinjφ₁` at
`ρ₁ = ρ`), then every step of the composite is injective on the relevant region:

* `w ↦ s·π w` is injective on `SrcC j k n ⊆ ball (wc j k + n) (1/2)`
  (`Work.Repel.piExp_injOn_ball_lift`) and `s ≠ 0` (`V.hs`);
* `V.uOf = (φ₁|_{Sm1})⁻¹` is injective (`V.uOf_unique`, `V.uOf_spec`, `V.Sm1_injOn`);
* `u ↦ ĥ^[j] u - k` is injective on the fibre `V.fib j k`: `IsChain.injOn_iterate` for `ĥ^[j]`
  on `W j`, transported by the `ℤ`-equivariance (`chainPre_iterate_add_int`), and it lands in
  `W 0` (`V.wOfCell_target_mem_Raw` / `chain_image_mem`);
* `V.wOf` is injective on `W 0` from `hW0`: `V.wOf u'` is the unique point of `ball wt₀ ρ₀` with
  `π`-image `P₁.φ u'/s` (`V.wOf_unique`, `V.wOf_spec`, `Work.Repel.piExp_injOn_ball_lift`), so
  `wOf u'₁ = wOf u'₂` forces `P₁.φ u'₁ = P₁.φ u'₂`, hence `u'₁ = u'₂`.

Consequence used downstream: `f^[N]` is injective on `P₀.φ '' SrcC j k n` whenever
`f^[N] (P₀.φ w) = P₀.φ (wOfCell (j,k,n) w)` on `SrcC j k n` (`ReturnData.hinj`). -/
theorem wOfCell_injOn_SrcC (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hW0 : Set.InjOn V.P₁.φ (V.W 0)) (hSm : V.fib j k ⊆ V.Sm1) :
    Set.InjOn (V.wOfCell (j, k, n)) (V.SrcC j k n) := by
  intro w₁ hw₁ w₂ hw₂ heq
  obtain ⟨hw₁Raw, hw₁ball⟩ := hw₁
  obtain ⟨hw₂Raw, hw₂ball⟩ := hw₂
  -- the level-1 sources of `w₁` and `w₂` lie in the shifted chain fibre
  have hfib₁ : V.uOf (V.s * MandelDim.piExp w₁) ∈ V.fib j k := V.uOfSrc_mem_fib hSm hw₁Raw
  have hfib₂ : V.uOf (V.s * MandelDim.piExp w₂) ∈ V.fib j k := V.uOfSrc_mem_fib hSm hw₂Raw
  -- `uOf` inverts `φ₁` there
  have hφu₁ : V.P₁.φ (V.uOf (V.s * MandelDim.piExp w₁)) = V.s * MandelDim.piExp w₁ :=
    (V.uOf_spec (Set.image_mono hSm hw₁Raw)).2
  have hφu₂ : V.P₁.φ (V.uOf (V.s * MandelDim.piExp w₂)) = V.s * MandelDim.piExp w₂ :=
    (V.uOf_spec (Set.image_mono hSm hw₂Raw)).2
  -- both chain walks land in `W 0`
  have ht₁ : (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
      - ((k : ℤ) : ℂ) ∈ V.W 0 := chain_image_mem V hfib₁
  have ht₂ : (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂))
      - ((k : ℤ) : ℂ) ∈ V.W 0 := chain_image_mem V hfib₂
  -- the π-images of the targets
  have hspec₁ : MandelDim.piExp (V.wOfCell (j, k, n) w₁)
      = V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
          - ((k : ℤ) : ℂ)) / V.s := (V.wOfCell_spec ht₁).2
  have hspec₂ : MandelDim.piExp (V.wOfCell (j, k, n) w₂)
      = V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂))
          - ((k : ℤ) : ℂ)) / V.s := (V.wOfCell_spec ht₂).2
  -- equal targets, so equal `φ₁`-images at level 0
  have hπeq : MandelDim.piExp (V.wOfCell (j, k, n) w₁)
      = MandelDim.piExp (V.wOfCell (j, k, n) w₂) := by rw [heq]
  have hφeq : V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
        - ((k : ℤ) : ℂ))
      = V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂))
        - ((k : ℤ) : ℂ)) := by
    rw [hspec₁, hspec₂] at hπeq
    exact (div_left_inj' V.hs).mp hπeq
  -- injectivity of `φ₁` on `W 0` (the hypothesis), then cancel the translation
  have ht₁_eq : (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
        - ((k : ℤ) : ℂ)
      = (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂))
        - ((k : ℤ) : ℂ) := hW0 ht₁ ht₂ hφeq
  have hiter_eq : (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
      = (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂)) := by
    have h := congrArg (fun z : ℂ => z + ((k : ℤ) : ℂ)) ht₁_eq
    simpa using h
  -- uniqueness of the shifted chain preimage
  obtain ⟨u₀, ⟨-, hu₀eq⟩, huniq⟩ :=
    chain_preimage_mem V.hIsChain V.hReq (j := j) (k := k)
      (u' := (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
        - ((k : ℤ) : ℂ)) ht₁
  have hUof₁ : V.uOf (V.s * MandelDim.piExp w₁) = u₀ :=
    huniq _ ⟨hfib₁, by
      show (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
        = ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
          - ((k : ℤ) : ℂ)) + ((k : ℤ) : ℂ)
      ring⟩
  have hUof₂ : V.uOf (V.s * MandelDim.piExp w₂) = u₀ :=
    huniq _ ⟨hfib₂, by
      show (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₂))
        = ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w₁))
          - ((k : ℤ) : ℂ)) + ((k : ℤ) : ℂ)
      rw [← hiter_eq]
      ring⟩
  have hUof : V.uOf (V.s * MandelDim.piExp w₁) = V.uOf (V.s * MandelDim.piExp w₂) :=
    hUof₁.trans hUof₂.symm
  -- hence `s * π w₁ = s * π w₂`, and `π` is injective on the source ball
  have hmul : V.s * MandelDim.piExp w₁ = V.s * MandelDim.piExp w₂ := by
    rw [← hφu₁, ← hφu₂, hUof]
  have hπ : MandelDim.piExp w₁ = MandelDim.piExp w₂ := mul_left_cancel₀ V.hs hmul
  have hinj := piExp_injOn_ball_lift (a := V.wc j k + ((n : ℤ) : ℂ)) (ρ := 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1 / 2)
  exact hinj hw₁ball hw₂ball hπ

end Work.Repel.V10
