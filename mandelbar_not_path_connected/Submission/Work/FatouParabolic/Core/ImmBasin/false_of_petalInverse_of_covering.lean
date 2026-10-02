/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# (Q4)–(Q6) of the corrected Fatou-parabolic design: the Liouville contradiction

If the immediate parabolic basin `Ω₀ = immBasin F z₀ p₀` is bounded and free of critical points,
and if the inverse Fatou coordinate `Φ` of the petal exists on the tail of every horizontal strip,
then `F` has a critical point in `Ω₀` — the design's contradiction.

The proof is the one of `NOTES_LEAD_mandelbar_gaps2.md` §2.1 (Q4)–(Q6):

* `exists_strip_lift` lifts `τ ↦ Φ (τ + n)` through the covering `F^[n]` of `Ω₀` on the deep
  strip `tailStrip (C - n) B`;
* `petalLift_eqOn` (in `ImmBasin/LiftTools.lean`) shows that any two such lifts agree on the
  intersection of their domains, so the lifts glue to a single function
  `Ψ τ := (lift of height |Im τ| + 1 at τ) τ` defined on **all** of `ℂ`;
* `differentiableOn_of_comp_iterate_eq` shows each lift is holomorphic, hence `Ψ` is entire;
* `Ψ` takes its values in the bounded set `Ω₀`, so it is bounded, hence constant by Liouville;
* but `Ψ` agrees with `Φ` on a tail strip, where `Φ` is injective — contradiction.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.exists_strip_lift
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.LiftTools
import Submission.Work.FatouParabolic.Core.ImmBasin.differentiableOn_of_comp_iterate_eq
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.exists_petalInverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core.ImmBasin

open Set Filter
open scoped Topology

noncomputable section

theorem false_of_petalInverse_of_covering {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hFdiff : Differentiable ℂ F)
    (hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n))
    (hbdd : Bornology.IsBounded (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hnocrit : ∀ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w ≠ 0)
    (hpetal : ∃ Φ : ℂ → ℂ, ∀ B : ℝ, 0 < B → ∃ C : ℝ,
      (∀ τ : ℂ, C < τ.re → |τ.im| < B →
        Φ τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧
        F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ) ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C B)) :
    False := by
  obtain ⟨Φ, hΦ⟩ := hpetal
  classical
  -- ## The canonical level of every height, and the strip hypothesis for `Φ`
  have hdata : ∀ B : ℝ, ∀ hB : 0 < B,
      ∃ C : ℝ, StripProp F z₀ p₀ Φ C B ∧ Set.InjOn Φ (tailStrip C B) :=
    fun B hB => hΦ B hB
  let Lvl : (B : ℝ) → 0 < B → ℝ := fun B hB => Classical.choose (hdata B hB)
  have Lvl_spec : ∀ (B : ℝ) (hB : 0 < B),
      StripProp F z₀ p₀ Φ (Lvl B hB) B ∧ Set.InjOn Φ (tailStrip (Lvl B hB) B) :=
    fun B hB => Classical.choose_spec (hdata B hB)
  -- ## The height, level and index functions of the glued function `Ψ`
  let Ht : ℂ → ℝ := fun τ => |τ.im| + 1
  have Ht_pos : ∀ τ : ℂ, 0 < Ht τ := fun τ => by
    have h : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
    simp only [Ht]; linarith
  let Lv : ℂ → ℝ := fun τ => Lvl (Ht τ) (Ht_pos τ)
  have Lv_spec : ∀ τ : ℂ, StripProp F z₀ p₀ Φ (Lv τ) (Ht τ) :=
    fun τ => (Lvl_spec (Ht τ) (Ht_pos τ)).1
  let Idx : ℂ → ℕ := fun τ => Classical.choose (exists_nat_gt (Lv τ - τ.re))
  have Idx_spec : ∀ τ : ℂ, Lv τ - ((Idx τ : ℕ) : ℝ) < τ.re := by
    intro τ
    have h := Classical.choose_spec (exists_nat_gt (Lv τ - τ.re))
    simp only [Idx]
    linarith
  -- the glued function: at `τ` use the lift of height `|Im τ| + 1` and level `Lv τ`
  let Ψ : ℂ → ℂ := fun τ => petalLift F z₀ p₀ hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ)
    (Lv_spec τ) (Idx τ) τ
  have hΨval : ∀ τ : ℂ, Ψ τ = petalLift F z₀ p₀ hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ)
      (Lv_spec τ) (Idx τ) τ := fun τ => rfl
  -- every value of `Ψ` lies in the (bounded) immediate basin
  have hΨmem : ∀ τ : ℂ, Ψ τ ∈ immBasin F z₀ p₀ := by
    intro τ
    rw [hΨval τ]
    refine petalLift_mem (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hΦ := Lv_spec τ)
      (Idx τ) ⟨Idx_spec τ, ?_⟩
    have h : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
    simp only [Ht]; linarith
  -- ## Each lift is holomorphic (`differentiableOn_of_comp_iterate_eq`)
  have hlift_diff : ∀ (C B : ℝ) (hB : 0 < B) (hΦ' : StripProp F z₀ p₀ Φ C B) (n : ℕ),
      DifferentiableOn ℂ (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ' n)
        (tailStrip (C - ((n : ℕ) : ℝ)) B) := by
    intro C B hB hΦ' n
    refine differentiableOn_of_comp_iterate_eq (n := n) hFdiff hmap hnocrit (isOpen_tailStrip _ _)
      (petalLift_continuousOn hB hΦ' n) (fun τ hτ => petalLift_mem hB hΦ' n hτ) ?_
      (fun τ hτ => petalLift_comp hB hΦ' n hτ)
    intro τ hτ
    have hmem : τ + (n : ℂ) ∈ tailStrip C B := by
      refine ⟨?_, ?_⟩
      · have h : (τ + (n : ℂ)).re = τ.re + (n : ℝ) := by simp
        rw [h]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [hτ.1]
      · have h : (τ + (n : ℂ)).im = τ.im := by simp
        rw [h]; exact hτ.2
    have hg : DifferentiableAt ℂ (fun σ : ℂ => σ + (n : ℂ)) τ :=
      differentiableAt_id.add_const _
    exact (((hΦ' (τ + (n : ℂ)) hmem.1 hmem.2).2.2).comp τ hg).differentiableWithinAt
  -- ## `Ψ` is entire
  have hΨdiff : Differentiable ℂ Ψ := by
    intro τ₀
    -- fixed data at `τ₀`
    set C₀ : ℝ := Lv τ₀ with hC₀def
    set B₀ : ℝ := Ht τ₀ with hB₀def
    set n₀ : ℕ := Idx τ₀ with hn₀def
    have hB₀pos : 0 < B₀ := by rw [hB₀def]; exact Ht_pos τ₀
    have hC₀spec : StripProp F z₀ p₀ Φ C₀ B₀ := by rw [hC₀def, hB₀def]; exact Lv_spec τ₀
    have hn₀spec : C₀ - ((n₀ : ℕ) : ℝ) < τ₀.re := by rw [hC₀def, hn₀def]; exact Idx_spec τ₀
    have hδpos : 0 < min (1 / 2 : ℝ) ((τ₀.re - (C₀ - ((n₀ : ℕ) : ℝ))) / 2) :=
      lt_min (by norm_num) (by linarith)
    -- on a small ball `Ψ` agrees with the fixed lift of height `B₀` and level `C₀`
    have hev : Ψ =ᶠ[𝓝 τ₀] (petalLift F z₀ p₀ hmap hcover Φ C₀ B₀ hB₀pos hC₀spec n₀) := by
      refine Filter.eventually_of_mem (Metric.ball_mem_nhds τ₀ hδpos) (fun τ hτ => ?_)
      rw [Metric.mem_ball] at hτ
      have hdist1 : dist τ τ₀ < 1 / 2 := lt_of_lt_of_le hτ (min_le_left _ _)
      have hdist2 : dist τ τ₀ < (τ₀.re - (C₀ - ((n₀ : ℕ) : ℝ))) / 2 :=
        lt_of_lt_of_le hτ (min_le_right _ _)
      have hre : C₀ - ((n₀ : ℕ) : ℝ) < τ.re := by
        have h1 : |τ.re - τ₀.re| ≤ dist τ τ₀ := by
          have h := Complex.abs_re_le_norm (τ - τ₀)
          rw [Complex.sub_re] at h
          rwa [Complex.dist_eq]
        have h2 : τ₀.re - τ.re ≤ dist τ τ₀ := by
          have := (abs_le.mp h1).1
          linarith
        linarith
      have him : |τ.im| < B₀ := by
        have h1 : |τ.im - τ₀.im| ≤ dist τ τ₀ := by
          have h := Complex.abs_im_le_norm (τ - τ₀)
          rw [Complex.sub_im] at h
          rwa [Complex.dist_eq]
        have h2 : |τ.im| - |τ₀.im| ≤ |τ.im - τ₀.im| := abs_sub_abs_le_abs_sub _ _
        have hB₀val : B₀ = |τ₀.im| + 1 := by rw [hB₀def]
        rw [hB₀val]
        linarith
      rw [hΨval τ]
      exact petalLift_eqOn (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hB' := hB₀pos)
        (hΦ := Lv_spec τ) (hΦ' := hC₀spec) (n := Idx τ) (n' := n₀)
        ⟨⟨Idx_spec τ, by simp only [Ht]; linarith [abs_nonneg τ.im]⟩, ⟨hre, him⟩⟩
    have hX₀ : DifferentiableAt ℂ (petalLift F z₀ p₀ hmap hcover Φ C₀ B₀ hB₀pos hC₀spec n₀)
        τ₀ :=
      (hlift_diff C₀ B₀ hB₀pos hC₀spec n₀).differentiableAt
        ((isOpen_tailStrip _ _).mem_nhds ⟨hn₀spec, by
          have hB₀val : B₀ = |τ₀.im| + 1 := by rw [hB₀def]
          rw [hB₀val]; linarith [abs_nonneg τ₀.im]⟩)
    exact hev.differentiableAt_iff.mpr hX₀
  -- ## `Ψ` is bounded
  have hΨbdd : Bornology.IsBounded (Set.range Ψ) :=
    hbdd.subset (fun z hz => by obtain ⟨τ, rfl⟩ := hz; exact hΨmem τ)
  -- ## `Ψ` agrees with `Φ` on the tail strip of height `1`
  set C₁ : ℝ := Lvl 1 one_pos with hC₁def
  have hC₁ : StripProp F z₀ p₀ Φ C₁ 1 ∧ Set.InjOn Φ (tailStrip C₁ 1) := by
    rw [hC₁def]; exact Lvl_spec 1 one_pos
  have hΨeq : ∀ τ ∈ tailStrip C₁ 1, Ψ τ = Φ τ := by
    intro τ hτ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, C₁ - ((m : ℕ) : ℝ) < τ.re := by
      obtain ⟨m, hm⟩ := exists_nat_gt (C₁ - τ.re)
      exact ⟨m, by linarith⟩
    rw [hΨval τ]
    have h1 : petalLift F z₀ p₀ hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ) (Lv_spec τ) (Idx τ) τ
        = petalLift F z₀ p₀ hmap hcover Φ C₁ 1 one_pos hC₁.1 m τ :=
      petalLift_eqOn (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hB' := one_pos)
        (hΦ := Lv_spec τ) (hΦ' := hC₁.1) (n := Idx τ) (n' := m)
        ⟨⟨Idx_spec τ, by simp only [Ht]; linarith [abs_nonneg τ.im]⟩,
          ⟨hm, by simpa using hτ.2⟩⟩
    have h2 : petalLift F z₀ p₀ hmap hcover Φ C₁ 1 one_pos hC₁.1 m τ = Φ τ :=
      petalLift_agree (hmap := hmap) (hcover := hcover) (hB := one_pos) (hΦ := hC₁.1) m hτ
    exact h1.trans h2
  -- ## Liouville, and the two distinct points of the tail strip
  have hconst := hΨdiff.apply_eq_apply_of_bounded hΨbdd
  have hτ₁ : ((C₁ + 1 : ℝ) : ℂ) ∈ tailStrip C₁ 1 := by
    refine ⟨?_, ?_⟩ <;> simp
  have hτ₂ : ((C₁ + 2 : ℝ) : ℂ) ∈ tailStrip C₁ 1 := by
    refine ⟨?_, ?_⟩ <;> simp
  have hne : ((C₁ + 1 : ℝ) : ℂ) ≠ ((C₁ + 2 : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    linarith
  refine hne (hC₁.2 hτ₁ hτ₂ ?_)
  have hc := hconst ((C₁ + 1 : ℝ) : ℂ) ((C₁ + 2 : ℝ) : ℂ)
  rwa [hΨeq _ hτ₁, hΨeq _ hτ₂] at hc

end

end Work.FatouParabolic.Core.ImmBasin
