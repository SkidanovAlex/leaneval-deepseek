import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set Metric

theorem ODE_solution_unique_Icc_left_of_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : E × E → E} {u₁ v₁ u₂ v₂ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hF : ContDiffAt ℝ 1 F (u₁ b, v₁ b))
    (h1c : ContinuousOn (fun t : ℝ => (u₁ t, v₁ t)) (Set.Icc a b))
    (h2c : ContinuousOn (fun t : ℝ => (u₂ t, v₂ t)) (Set.Icc a b))
    (h1d : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt (fun t : ℝ => (u₁ t, v₁ t))
      (v₁ t, F (u₁ t, v₁ t)) (Set.Iic t) t)
    (h2d : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt (fun t : ℝ => (u₂ t, v₂ t))
      (v₂ t, F (u₂ t, v₂ t)) (Set.Iic t) t)
    (hb : u₁ b = u₂ b ∧ v₁ b = v₂ b) :
    ∃ a' < b, Set.EqOn u₁ u₂ (Set.Icc a' b) ∧ Set.EqOn v₁ v₂ (Set.Icc a' b) := by
  -- Step 1: `F` is locally Lipschitz near the common point.
  obtain ⟨K, s, hs, hKs⟩ := hF.exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hs
  have hFlip : LipschitzOnWith K F (Metric.ball (u₁ b, v₁ b) r) := hKs.mono hrsub
  -- Step 2: the vector field `G x = (x.2, F x)` is Lipschitz there.
  have hGlip : LipschitzOnWith (K + 1) (fun x : E × E => (x.2, F x))
      (Metric.ball (u₁ b, v₁ b) r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hFb : dist (F x) (F y) ≤ (K : ℝ) * dist x y := hFlip.dist_le_mul x hx y hy
    have h2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
    have key : dist (x.2, F x) (y.2, F y) ≤ ((K : ℝ) + 1) * dist x y := by
      rw [Prod.dist_eq]
      have hd : (0 : ℝ) ≤ dist x y := dist_nonneg
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.2
      calc max (dist x.2 y.2) (dist (F x) (F y))
          ≤ max (dist x y) ((K : ℝ) * dist x y) := max_le_max h2 hFb
        _ ≤ ((K : ℝ) + 1) * dist x y := by
              apply max_le <;> nlinarith
    simpa using key
  -- Step 3: continuity near `b` gives a neighbourhood on which both solutions stay in the ball.
  have hbmem : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_rfl⟩
  have hc1 : ContinuousWithinAt (fun t : ℝ => (u₁ t, v₁ t)) (Set.Icc a b) b :=
    h1c.continuousWithinAt hbmem
  have hc2 : ContinuousWithinAt (fun t : ℝ => (u₂ t, v₂ t)) (Set.Icc a b) b :=
    h2c.continuousWithinAt hbmem
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := (Metric.continuousWithinAt_iff.mp hc1) r hr
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (Metric.continuousWithinAt_iff.mp hc2) r hr
  set L : ℝ := min (min δ₁ δ₂) ((b - a) / 2) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact lt_min (lt_min hδ₁pos hδ₂pos) (by linarith)
  have hLleδ : L ≤ min δ₁ δ₂ := by rw [hLdef]; exact min_le_left _ _
  have hLle : L ≤ (b - a) / 2 := by rw [hLdef]; exact min_le_right _ _
  have hbL : a < b - L := by have h := hLle; linarith
  have hmem1 : ∀ t ∈ Set.Ioc (b - L) b,
      (u₁ t, v₁ t) ∈ Metric.ball (u₁ b, v₁ b) r := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨by linarith [ht.1, hbL], ht.2⟩
    have h1 : b - t < L := by linarith [ht.1]
    have hdist : dist t b < min δ₁ δ₂ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2] : t - b ≤ 0), neg_sub]
      exact lt_of_lt_of_le h1 hLleδ
    have hlt : dist t b < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
    exact Metric.mem_ball.mpr (hδ₁ htIcc hlt)
  have hmem2 : ∀ t ∈ Set.Ioc (b - L) b,
      (u₂ t, v₂ t) ∈ Metric.ball (u₁ b, v₁ b) r := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨by linarith [ht.1, hbL], ht.2⟩
    have h1 : b - t < L := by linarith [ht.1]
    have hdist : dist t b < min δ₁ δ₂ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2] : t - b ≤ 0), neg_sub]
      exact lt_of_lt_of_le h1 hLleδ
    have hlt : dist t b < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
    have hb' : (u₂ b, v₂ b) = (u₁ b, v₁ b) := by rw [hb.1, hb.2]
    have h3 := hδ₂ htIcc hlt
    rw [hb'] at h3
    exact Metric.mem_ball.mpr h3
  -- Step 4: reverse time; the backward problem on `[b-L,b]` becomes forward on `[0,L]`.
  have hcont1 : ContinuousOn (fun τ : ℝ => (u₁ (b - τ), v₁ (b - τ))) (Set.Icc 0 L) := by
    have hgc : ContinuousOn (fun τ : ℝ => b - τ) (Set.Icc 0 L) :=
      (continuous_const.sub continuous_id).continuousOn
    have hm : Set.MapsTo (fun τ : ℝ => b - τ) (Set.Icc 0 L) (Set.Icc a b) := by
      intro τ hτ
      exact ⟨by linarith [hτ.2, hLle, hab], by linarith [hτ.1]⟩
    exact h1c.comp hgc hm
  have hcont2 : ContinuousOn (fun τ : ℝ => (u₂ (b - τ), v₂ (b - τ))) (Set.Icc 0 L) := by
    have hgc : ContinuousOn (fun τ : ℝ => b - τ) (Set.Icc 0 L) :=
      (continuous_const.sub continuous_id).continuousOn
    have hm : Set.MapsTo (fun τ : ℝ => b - τ) (Set.Icc 0 L) (Set.Icc a b) := by
      intro τ hτ
      exact ⟨by linarith [hτ.2, hLle, hab], by linarith [hτ.1]⟩
    exact h2c.comp hgc hm
  have hder1 : ∀ τ ∈ Set.Ico (0 : ℝ) L,
      HasDerivWithinAt (fun σ : ℝ => (u₁ (b - σ), v₁ (b - σ)))
        (-(v₁ (b - τ), F (u₁ (b - τ), v₁ (b - τ)))) (Set.Ici τ) τ := by
    intro τ hτ
    have ht : b - τ ∈ Set.Ioc a b :=
      ⟨by linarith [hτ.2, hLle, hab], by linarith [hτ.1]⟩
    have hh : HasDerivWithinAt (fun σ : ℝ => b - σ) (-1) (Set.Ici τ) τ :=
      ((hasDerivAt_id τ).const_sub b).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun σ : ℝ => b - σ) (Set.Ici τ) (Set.Iic (b - τ)) :=
      fun σ hσ => sub_le_sub_left hσ b
    have h := (h1d (b - τ) ht).scomp τ hh hmaps
    have h' : HasDerivWithinAt ((fun s : ℝ => (u₁ s, v₁ s)) ∘ fun σ : ℝ => b - σ)
        (-(v₁ (b - τ), F (u₁ (b - τ), v₁ (b - τ)))) (Set.Ici τ) τ := by
      simpa using h
    exact h'
  have hder2 : ∀ τ ∈ Set.Ico (0 : ℝ) L,
      HasDerivWithinAt (fun σ : ℝ => (u₂ (b - σ), v₂ (b - σ)))
        (-(v₂ (b - τ), F (u₂ (b - τ), v₂ (b - τ)))) (Set.Ici τ) τ := by
    intro τ hτ
    have ht : b - τ ∈ Set.Ioc a b :=
      ⟨by linarith [hτ.2, hLle, hab], by linarith [hτ.1]⟩
    have hh : HasDerivWithinAt (fun σ : ℝ => b - σ) (-1) (Set.Ici τ) τ :=
      ((hasDerivAt_id τ).const_sub b).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun σ : ℝ => b - σ) (Set.Ici τ) (Set.Iic (b - τ)) :=
      fun σ hσ => sub_le_sub_left hσ b
    have h := (h2d (b - τ) ht).scomp τ hh hmaps
    have h' : HasDerivWithinAt ((fun s : ℝ => (u₂ s, v₂ s)) ∘ fun σ : ℝ => b - σ)
        (-(v₂ (b - τ), F (u₂ (b - τ), v₂ (b - τ)))) (Set.Ici τ) τ := by
      simpa using h
    exact h'
  have hmem1' : ∀ τ ∈ Set.Ico (0 : ℝ) L,
      (u₁ (b - τ), v₁ (b - τ)) ∈ Metric.ball (u₁ b, v₁ b) r := by
    intro τ hτ
    exact hmem1 (b - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hmem2' : ∀ τ ∈ Set.Ico (0 : ℝ) L,
      (u₂ (b - τ), v₂ (b - τ)) ∈ Metric.ball (u₁ b, v₁ b) r := by
    intro τ hτ
    exact hmem2 (b - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hder1' : ∀ t ∈ Set.Ico (0 : ℝ) L,
      HasDerivWithinAt (fun σ : ℝ => (u₁ (b - σ), v₁ (b - σ)))
        ((fun (_ : ℝ) (x : E × E) => -((x.2, F x))) t
          ((fun σ : ℝ => (u₁ (b - σ), v₁ (b - σ))) t)) (Set.Ici t) t := by
    intro t ht
    simpa using hder1 t ht
  have hder2' : ∀ t ∈ Set.Ico (0 : ℝ) L,
      HasDerivWithinAt (fun σ : ℝ => (u₂ (b - σ), v₂ (b - σ)))
        ((fun (_ : ℝ) (x : E × E) => -((x.2, F x))) t
          ((fun σ : ℝ => (u₂ (b - σ), v₂ (b - σ))) t)) (Set.Ici t) t := by
    intro t ht
    simpa using hder2 t ht
  have ha0 : dist ((fun σ : ℝ => (u₁ (b - σ), v₁ (b - σ))) 0)
      ((fun σ : ℝ => (u₂ (b - σ), v₂ (b - σ))) 0) ≤ 0 := by
    simp [hb.1, hb.2]
  -- Step 5: apply the forward ODE uniqueness theorem.
  have hmain : ∀ τ ∈ Set.Icc (0 : ℝ) L,
      dist ((u₁ (b - τ), v₁ (b - τ))) ((u₂ (b - τ), v₂ (b - τ))) ≤ 0 := by
    intro τ hτ
    have h := dist_le_of_trajectories_ODE_of_mem
      (v := fun (_ : ℝ) (x : E × E) => -((x.2, F x)))
      (s := fun _ => Metric.ball (u₁ b, v₁ b) r)
      (K := K + 1)
      (f := fun σ : ℝ => (u₁ (b - σ), v₁ (b - σ)))
      (g := fun σ : ℝ => (u₂ (b - σ), v₂ (b - σ)))
      (a := 0) (b := L) (δ := 0)
      (fun _ _ => hGlip.neg) hcont1 hder1' hmem1' hcont2 hder2' hmem2'
      ha0 τ hτ
    simpa using h
  -- Step 6: conclude.
  refine ⟨b - L, by linarith, ?_, ?_⟩
  · intro t ht
    have hτ : b - t ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := hmain (b - t) hτ
    have hsub : b - (b - t) = t := by ring
    have h0 : dist ((u₁ (b - (b - t)), v₁ (b - (b - t))))
        ((u₂ (b - (b - t)), v₂ (b - (b - t)))) = 0 :=
      le_antisymm (by simpa using h) dist_nonneg
    rw [hsub] at h0
    exact congrArg Prod.fst (dist_eq_zero.mp h0)
  · intro t ht
    have hτ : b - t ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := hmain (b - t) hτ
    have hsub : b - (b - t) = t := by ring
    have h0 : dist ((u₁ (b - (b - t)), v₁ (b - (b - t))))
        ((u₂ (b - (b - t)), v₂ (b - (b - t)))) = 0 :=
      le_antisymm (by simpa using h) dist_nonneg
    rw [hsub] at h0
    exact congrArg Prod.snd (dist_eq_zero.mp h0)

end Commons.Analysis.ODE