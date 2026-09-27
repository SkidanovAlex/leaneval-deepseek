import Mathlib

/-!
# The shear `(u, s) ↦ (u, (1 - χ u) * s + χ u * g s)` is an open map

This file proves `Work.Noncompact.CompressionTube.isOpenMap_shear`: for a continuous
`χ : E → ℝ` and a continuous `g : ℝ → ℝ` such that the "fiber map"
`s ↦ (1 - χ u) * s + χ u * g s` is strictly monotone for every `u : E`, the shear
`(u, s) ↦ (u, (1 - χ u) * s + χ u * g s)` is an open map of `E × ℝ`.

The proof is local: at a point `(u, s)`, the strict monotonicity of the fiber map at `u`
together with continuity of `u' ↦ φ u' a` at a fixed height `a` produces a product
neighbourhood `V ×ˢ Ioo (t - ε) (t + ε)` of the image which is contained in the image of any
prescribed product neighbourhood `U ×ˢ I` of `(u, s)`.  The interval `Ioo a b` of heights is
recovered from the heights `s ± δ` by the intermediate value theorem
(`Continuous.image_Ioo_of_strictMono`).
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- The shear map attached to a family of fiber maps `φ : E → ℝ → ℝ`. -/
private def shearMap {E : Type*} (φ : E → ℝ → ℝ) : E × ℝ → E × ℝ :=
  fun p => (p.1, φ p.1 p.2)

/-- If the fiber maps `φ u : ℝ → ℝ` are strictly monotone and continuous, and depend
continuously on the parameter `u` at every fixed height, then the shear `p ↦ (p.1, φ p.1 p.2)`
is an open map. -/
private lemma shear_isOpenMap_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ → ℝ)
    (hcont_param : ∀ a : ℝ, Continuous (fun u : E => φ u a))
    (hcont_s : ∀ u : E, Continuous (φ u))
    (hmono : ∀ u : E, StrictMono (φ u)) :
    IsOpenMap (shearMap φ) := by
  -- The pointwise statement: the image of any product neighbourhood `U ×ˢ I` of `(u, s)` is a
  -- neighbourhood of `(u, φ u s)`.
  have key : ∀ (u : E) (s : ℝ) (U : Set E) (I : Set ℝ),
      U ∈ 𝓝 u → IsOpen I → s ∈ I →
      (u, φ u s) ∈ interior (shearMap φ '' (U ×ˢ I)) := by
    intro u s U I hU hI hs
    -- an interval `Ioo (s - δ) (s + δ)` around `s` inside `I`
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs)
    rw [Real.ball_eq_Ioo] at hδsub
    have hsd : s - δ < s := by linarith
    have hsb : s < s + δ := by linarith
    have hps : φ u (s - δ) < φ u s := hmono u hsd
    have hst : φ u s < φ u (s + δ) := hmono u hsb
    -- a slack `ε` small enough that the strict inequalities survive
    set ε := min (φ u s - φ u (s - δ)) (φ u (s + δ) - φ u s) / 3 with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    have h3 : 3 * ε = min (φ u s - φ u (s - δ)) (φ u (s + δ) - φ u s) := by rw [hε]; ring
    have hεle1 : 3 * ε ≤ φ u s - φ u (s - δ) := by rw [h3]; exact min_le_left _ _
    have hεle2 : 3 * ε ≤ φ u (s + δ) - φ u s := by rw [h3]; exact min_le_right _ _
    have hpe : φ u (s - δ) + ε ≤ φ u s - ε := by linarith
    have hqe : φ u s + ε ≤ φ u (s + δ) - ε := by linarith
    -- the parameter-neighbourhood on which the inequalities persist
    set Vm : Set E := {u' | φ u' (s - δ) < φ u (s - δ) + ε} with hVm
    set Vp : Set E := {u' | φ u (s + δ) - ε < φ u' (s + δ)} with hVp
    have hVm_open : IsOpen Vm := by
      rw [hVm]; exact isOpen_Iio.preimage (hcont_param (s - δ))
    have hVp_open : IsOpen Vp := by
      rw [hVp]; exact isOpen_Ioi.preimage (hcont_param (s + δ))
    have huVm : u ∈ Vm := by
      rw [hVm]; exact lt_add_of_pos_right _ hεpos
    have huVp : u ∈ Vp := by
      rw [hVp]; exact sub_lt_self _ hεpos
    have hu_intU : u ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
    set V : Set E := Vm ∩ Vp ∩ interior U with hV
    have hV_open : IsOpen V := by
      rw [hV]; exact (hVm_open.inter hVp_open).inter isOpen_interior
    have hVU : V ⊆ U := by
      rw [hV]; intro x hx; exact interior_subset hx.2
    have huV : u ∈ V := by rw [hV]; exact ⟨⟨huVm, huVp⟩, hu_intU⟩
    -- the open box around the image
    set J : Set ℝ := Ioo (φ u s - ε) (φ u s + ε) with hJ
    have hJ_open : IsOpen J := by rw [hJ]; exact isOpen_Ioo
    have hOsub : V ×ˢ J ⊆ shearMap φ '' (U ×ˢ I) := by
      rintro ⟨u', t'⟩ h
      rw [Set.mem_prod] at h
      obtain ⟨hu'V, ht'J⟩ := h
      have hu'Vm : u' ∈ Vm := by rw [hV] at hu'V; exact hu'V.1.1
      have hu'Vp : u' ∈ Vp := by rw [hV] at hu'V; exact hu'V.1.2
      have hle1 : φ u' (s - δ) < φ u (s - δ) + ε := hu'Vm
      have hle2 : φ u (s + δ) - ε < φ u' (s + δ) := hu'Vp
      have ht1 : φ u s - ε < t' := ht'J.1
      have ht2 : t' < φ u s + ε := ht'J.2
      have h1 : φ u' (s - δ) < t' := by linarith
      have h2 : t' < φ u' (s + δ) := by linarith
      -- `t'` lies strictly between the two endpoint values, so it is attained in the open interval
      have hmem : t' ∈ (φ u') '' Ioo (s - δ) (s + δ) := by
        rw [Continuous.image_Ioo_of_strictMono (hcont_s u') (hmono u')]
        exact ⟨h1, h2⟩
      obtain ⟨s', hs'mem, hs'eq⟩ := hmem
      refine ⟨(u', s'), ?_, ?_⟩
      · rw [Set.mem_prod]; exact ⟨hVU hu'V, hδsub hs'mem⟩
      · simp only [shearMap]; rw [hs'eq]
    have hO_open : IsOpen (V ×ˢ J) := hV_open.prod hJ_open
    have huO : (u, φ u s) ∈ V ×ˢ J := by
      rw [Set.mem_prod]; exact ⟨huV, ⟨by linarith, by linarith⟩⟩
    exact interior_maximal hOsub hO_open huO
  rw [isOpenMap_iff_image_interior]
  intro s x hx
  rcases hx with ⟨⟨u, r⟩, hy, rfl⟩
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
  rw [← ball_prod_same] at hηsub
  have hkey := key u r (Metric.ball u η) (Metric.ball r η)
    (Metric.ball_mem_nhds u hηpos) Metric.isOpen_ball (Metric.mem_ball_self hηpos)
  exact interior_mono (Set.image_mono (hηsub.trans interior_subset)) hkey

theorem isOpenMap_shear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℝ) (g : ℝ → ℝ) (hχ : Continuous χ) (hg : Continuous g)
    (hmono : ∀ u : E, StrictMono fun s : ℝ => (1 - χ u) * s + χ u * g s) :
    IsOpenMap fun p : E × ℝ => (p.1, (1 - χ p.1) * p.2 + χ p.1 * g p.2) := by
  exact shear_isOpenMap_aux (fun u s => (1 - χ u) * s + χ u * g s)
    (fun a => by fun_prop) (fun u => by fun_prop) hmono

end Work.Noncompact.CompressionTube
