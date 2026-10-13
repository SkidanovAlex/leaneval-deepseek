/-
# GalerkinFix — the τ-equicontinuity chapter (design §1.2, row `hProfileLip`)

The delivered bundle asked for a **uniform local Lipschitz bound** on the Galerkin profiles
(`hProfileLip`).  That input is not what the estimates give, and it is probably false: an `ℋ⁴`-ball
contains profiles `θ^s` with `α/20 < s < 1`, which are only `C^β` for `β < γ - 1 = α/10`
(`Submission/Work/FTS/N45_DESIGN_LEAD.md` §1.2).  What the compactness extraction actually uses is a
*modulus of continuity*, uniform in the truncation `n`, and that is exactly what the paper's
estimates provide:

* in the **space** variables, the scalar estimate of the paper (tex 1057, Corollary `Linfty`)
  `|g|_{C^β} ≤ C_β |g|_{ℋ²}` for every `β < γ - 1`: a uniform `ℋ²`-bound on the profiles gives a
  uniform modulus in `(z,θ)` (`Work.FTS.Galerkin.EquicontSpace`, defined in
  `Submission/Work/FTS/GalerkinFix/Defs.lean`);
* in the **fake time** variable `τ`, the estimate `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` of the paper
  (tex 1580) together with the pointwise bound of `Linf_H2`: a uniform pointwise bound on the
  *fake-time derivative* gives a uniform modulus in `τ` (`Work.FTS.Galerkin.EquicontTau`).

This module proves the combination: the two one-directional moduli give a joint modulus on every
rectangle of the slab (`profileEquicontBox_of_parts`), a modulus on every rectangle gives a modulus
on every compact subset of the slab (`profileEquicont_of_box`), and the mean value theorem in `τ`
turns pointwise bounds on `∂_τ` into `EquicontTau` (`equicontTau_box_of_derivBound`).

The *concrete* instantiation for the Galerkin families — `EquicontTau` from a uniform pointwise
bound on the projected vector field along the trajectory, i.e. the paper's
`|∂_τg|_{ℋ³} ≤ Cα²exp(-cτ)` — is
`Submission/Work/FTS/GalerkinFix/Equicont/equicontTau_of_galFam_fieldBound.lean`, and the
per-coefficient form of the design's "equicontinuity in `τ` of `τ ↦ IP(gₙ(τ), φ_k)`" is
`Submission/Work/FTS/GalerkinFix/Equicont/coeff_lipschitz_of_fieldBound.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalerkinFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalerkinFix

open Work.FTS.Galerkin (Slab box mem_box profileFam IsGalFam)

set_option autoImplicit false

/-! ## Coordinate bounds against the product metric on `ℝ × ℝ × ℝ` -/

theorem abs_fst_sub_le_dist (p q : ℝ × ℝ × ℝ) : |p.1 - q.1| ≤ dist p q := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact le_max_left _ _

theorem abs_snd_fst_sub_le_dist (p q : ℝ × ℝ × ℝ) : |p.2.1 - q.2.1| ≤ dist p q := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem abs_snd_snd_sub_le_dist (p q : ℝ × ℝ × ℝ) : |p.2.2 - q.2.2| ≤ dist p q := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem abs_fst_le_dist_zero (p : ℝ × ℝ × ℝ) : |p.1| ≤ dist p 0 := by
  have h := abs_fst_sub_le_dist p 0
  simpa using h

theorem abs_snd_fst_le_dist_zero (p : ℝ × ℝ × ℝ) : |p.2.1| ≤ dist p 0 := by
  have h := abs_snd_fst_sub_le_dist p 0
  simpa using h

theorem abs_snd_snd_le_dist_zero (p : ℝ × ℝ × ℝ) : |p.2.2| ≤ dist p 0 := by
  have h := abs_snd_snd_sub_le_dist p 0
  simpa using h

/-! ## The two one-directional moduli give the joint modulus on every box -/

/-- **`EquicontSpace` + `EquicontTau` give `ProfileEquicontBox`.**  On the rectangle
`[0,Z] × [0,π/2] × [0,T]` one goes from `p = (z,θ,τ)` to `q = (z',θ',τ')` in three steps, each
moving one coordinate and each covered by one of the two moduli (all intermediate points stay in the
rectangle, which is convex). -/
theorem profileEquicontBox_of_parts {G : ℕ → (ℝ × ℝ × ℝ) → ℝ}
    (hsp : Work.FTS.Galerkin.EquicontSpace G) (htau : Work.FTS.Galerkin.EquicontTau G) :
    Work.FTS.Galerkin.ProfileEquicontBox G := by
  intro Z T hZ hT ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hsp Z T hZ hT (ε / 3) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := htau Z T hZ hT (ε / 3) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun n p hp q hq hpq => ?_⟩
  rw [mem_box] at hp hq
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hpq₁ : dist p q ≤ δ₁ := le_trans hpq (min_le_left _ _)
  have hpq₂ : dist p q ≤ δ₂ := le_trans hpq (min_le_right _ _)
  have hz : |p.1 - q.1| ≤ δ₁ := le_trans (abs_fst_sub_le_dist p q) hpq₁
  have hth : |p.2.1 - q.2.1| ≤ δ₁ := le_trans (abs_snd_fst_sub_le_dist p q) hpq₁
  have hta : |p.2.2 - q.2.2| ≤ δ₂ := le_trans (abs_snd_snd_sub_le_dist p q) hpq₂
  have e1 : |G n (p.1, p.2.1, p.2.2) - G n (q.1, p.2.1, p.2.2)| ≤ ε / 3 :=
    hδ₁ n p.2.2 hp3 p.1 hp1 p.2.1 hp2 q.1 hq1 p.2.1 hp2 hz
      (by rw [sub_self, abs_zero]; exact hδ₁pos.le)
  have e2 : |G n (q.1, p.2.1, p.2.2) - G n (q.1, q.2.1, p.2.2)| ≤ ε / 3 :=
    hδ₁ n p.2.2 hp3 q.1 hq1 p.2.1 hp2 q.1 hq1 q.2.1 hq2
      (by rw [sub_self, abs_zero]; exact hδ₁pos.le) hth
  have e3 : |G n (q.1, q.2.1, p.2.2) - G n (q.1, q.2.1, q.2.2)| ≤ ε / 3 :=
    hδ₂ n q.1 hq1 q.2.1 hq2 p.2.2 hp3 q.2.2 hq3 hta
  have hpt : (G n p - G n q)
      = (G n (p.1, p.2.1, p.2.2) - G n (q.1, p.2.1, p.2.2))
        + (G n (q.1, p.2.1, p.2.2) - G n (q.1, q.2.1, p.2.2))
        + (G n (q.1, q.2.1, p.2.2) - G n (q.1, q.2.1, q.2.2)) := by
    rcases p with ⟨p1, p2, p3⟩
    rcases q with ⟨q1, q2, q3⟩
    simp only
    ring
  have h2 := abs_add_le
    ((G n (p.1, p.2.1, p.2.2) - G n (q.1, p.2.1, p.2.2))
      + (G n (q.1, p.2.1, p.2.2) - G n (q.1, q.2.1, p.2.2)))
    (G n (q.1, q.2.1, p.2.2) - G n (q.1, q.2.1, q.2.2))
  have h3 := abs_add_le (G n (p.1, p.2.1, p.2.2) - G n (q.1, p.2.1, p.2.2))
    (G n (q.1, p.2.1, p.2.2) - G n (q.1, q.2.1, p.2.2))
  rw [hpt]
  linarith

/-! ## A modulus on every box gives a modulus on every compact subset of the slab -/

/-- **`ProfileEquicontBox` gives the bundled compactness field `ProfileEquicont`.**  A compact
subset of the slab is contained in a rectangle `box C C` (`IsCompact.isBounded`); the extra freedom
of `ProfileEquicont` — the second point may be anywhere in `Slab` — is absorbed by enlarging the
rectangle by `1` and truncating the modulus below `1`. -/
theorem profileEquicont_of_box {G : ℕ → (ℝ × ℝ × ℝ) → ℝ}
    (h : Work.FTS.Galerkin.ProfileEquicontBox G) :
    Work.FTS.Galerkin.ProfileEquicont G := by
  intro K hK hKsub ε hε
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ × ℝ)).mp hK.isBounded
  have hr0 : ∀ p ∈ K, dist p 0 ≤ r := fun p hp => Metric.mem_closedBall.mp (hr hp)
  set C : ℝ := max r 0 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith [le_max_right r 0]
  have hrC : r + 1 ≤ C := by rw [hCdef]; linarith [le_max_left r 0]
  have hKC : ∀ p ∈ K, p ∈ box C C := by
    intro p hp
    have hp0 : dist p 0 ≤ r := hr0 p hp
    have hz := (Work.FTS.Galerkin.mem_Slab.mp (hKsub hp)).1
    have hth := (Work.FTS.Galerkin.mem_Slab.mp (hKsub hp)).2.1
    have hta := (Work.FTS.Galerkin.mem_Slab.mp (hKsub hp)).2.2
    have h1 : |p.1| ≤ r := le_trans (abs_fst_le_dist_zero p) hp0
    have h3 : |p.2.2| ≤ r := le_trans (abs_snd_snd_le_dist_zero p) hp0
    rw [mem_box]
    refine ⟨⟨hz, ?_⟩, hth, ⟨hta, ?_⟩⟩
    · rw [abs_of_nonneg hz] at h1
      linarith
    · rw [abs_of_nonneg hta] at h3
      linarith
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := h C C hCpos.le hCpos.le ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, fun n p hp q hq hpq => ?_⟩
  have hpq₀ : dist p q ≤ δ₀ := le_trans hpq (min_le_left _ _)
  have hpq₁ : dist p q ≤ 1 := le_trans hpq (min_le_right _ _)
  have hpbox : p ∈ box C C := hKC p hp
  have hqbox : q ∈ box C C := by
    rw [mem_box] at hpbox ⊢
    rw [Work.FTS.Galerkin.mem_Slab] at hq
    obtain ⟨hqz, hqth, hqta⟩ := hq
    have hp1 : p.1 ≤ r := by
      have h1 : |p.1| ≤ r := le_trans (abs_fst_le_dist_zero p) (hr0 p hp)
      rw [abs_of_nonneg hpbox.1.1] at h1
      exact h1
    have hp3 : p.2.2 ≤ r := by
      have h3 : |p.2.2| ≤ r := le_trans (abs_snd_snd_le_dist_zero p) (hr0 p hp)
      rw [abs_of_nonneg hpbox.2.2.1] at h3
      exact h3
    have hle1 : q.1 ≤ p.1 + 1 := by
      have h1 : |p.1 - q.1| ≤ dist p q := abs_fst_sub_le_dist p q
      have h2 : -(1:ℝ) ≤ p.1 - q.1 := (abs_le.mp (le_trans h1 hpq₁)).1
      linarith
    have hle3 : q.2.2 ≤ p.2.2 + 1 := by
      have h1 : |p.2.2 - q.2.2| ≤ dist p q := abs_snd_snd_sub_le_dist p q
      have h2 : -(1:ℝ) ≤ p.2.2 - q.2.2 := (abs_le.mp (le_trans h1 hpq₁)).1
      linarith
    exact ⟨⟨hqz, by linarith⟩, hqth, ⟨hqta, by linarith⟩⟩
  exact hδ₀ n p hpbox q hqbox hpq₀

/-! ## Pointwise bounds on the fake-time derivative give `EquicontTau` -/

/-- **A pointwise bound on `∂_τ` gives `EquicontTau`** (mean value theorem on `[0,T]`): if for every
`n` and every `(z,θ)` in the rectangle the curve `τ ↦ G n (z,θ,τ)` has within-derivative
`d n (z,θ,τ)` of absolute value at most `M` on `[0,T]`, then the family is `τ`-equicontinuous with
modulus `ε/(M+1)`. -/
theorem equicontTau_box_of_derivBound {G : ℕ → (ℝ × ℝ × ℝ) → ℝ}
    {d : ℕ → (ℝ × ℝ × ℝ) → ℝ} {Z T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hcont : ∀ (n : ℕ) (z θ : ℝ), z ∈ Set.Icc 0 Z → θ ∈ Set.Icc 0 (π / 2) →
      ContinuousOn (fun s : ℝ => G n (z, θ, s)) (Set.Icc 0 T))
    (hder : ∀ (n : ℕ) (z θ τ : ℝ), z ∈ Set.Icc 0 Z → θ ∈ Set.Icc 0 (π / 2) →
      τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (fun s : ℝ => G n (z, θ, s)) (d n (z, θ, τ)) (Set.Icc 0 T) τ)
    (hbd : ∀ (n : ℕ) (z θ τ : ℝ), z ∈ Set.Icc 0 Z → θ ∈ Set.Icc 0 (π / 2) →
      τ ∈ Set.Icc 0 T → |d n (z, θ, τ)| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ z ∈ Set.Icc 0 Z,
      ∀ θ ∈ Set.Icc 0 (π / 2), ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
        |t - s| ≤ δ → |G n (z, θ, t) - G n (z, θ, s)| ≤ ε := by
  intro ε hε
  refine ⟨ε / (M + 1), by positivity, fun n z hz θ hθ t ht s hs hts => ?_⟩
  have hM1 : 0 < M + 1 := by linarith
  have hcvx : Convex ℝ (Set.Icc 0 T) := convex_Icc 0 T
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc 0 T)
    (f := fun τ => G n (z, θ, τ)) (f' := fun τ => d n (z, θ, τ)) (C := M)
    (fun τ hτ => hder n z θ τ hz hθ hτ)
    (fun τ hτ => by
      have hb := hbd n z θ τ hz hθ hτ
      simpa [Real.norm_eq_abs] using hb)
    hcvx hs ht
  have hts' : ‖t - s‖ ≤ ε / (M + 1) := by
    rw [Real.norm_eq_abs]; exact hts
  have hkey : M * (ε / (M + 1)) ≤ ε := by
    have h1 : M * (ε / (M + 1)) = (M * ε) / (M + 1) := by ring
    rw [h1, div_le_iff₀ hM1]
    nlinarith
  calc |G n (z, θ, t) - G n (z, θ, s)| = ‖G n (z, θ, t) - G n (z, θ, s)‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ M * ‖t - s‖ := hmain
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hts' hM
    _ ≤ ε := hkey

end Work.FTS.GalerkinFix
