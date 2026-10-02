import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Set Filter Topology Function
open scoped Topology

theorem local_limits_of_cover {U : Set ℂ} (hUc : IsPreconnected U)
    {v : ℕ → ℂ → ℂ} {φ : ℕ → ℕ} {G : ℕ → Set ℂ}
    (hGopen : ∀ n, IsOpen (G n)) (hGne : ∀ n, (G n).Nonempty) (hcover : U = ⋃ n, G n)
    (hlim : ∀ k, (∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)) ∨
        TendstoLocallyUniformlyAtTop (fun n => v (φ n)) (G k)) :
    (∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop U) ∨
      TendstoLocallyUniformlyAtTop (fun n => v (φ n)) U := by
  classical
  have hAsubU : (⋃ k, ⋃ (_ : ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)),
      G k) ⊆ U := by
    intro z hz
    obtain ⟨k, _, hzk⟩ := mem_iUnion₂.mp hz
    rw [hcover]
    exact mem_iUnion.mpr ⟨k, hzk⟩
  have hBsubU : (⋃ k, ⋃ (_ : ¬ ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)),
      G k) ⊆ U := by
    intro z hz
    obtain ⟨k, _, hzk⟩ := mem_iUnion₂.mp hz
    rw [hcover]
    exact mem_iUnion.mpr ⟨k, hzk⟩
  -- The two "types" are mutually exclusive on intersecting members of the cover.
  have hcross : ∀ k j : ℕ, (G k ∩ G j).Nonempty →
      ¬ ((∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)) ∧
          TendstoLocallyUniformlyAtTop (fun n => v (φ n)) (G j)) := by
    rintro k j ⟨z, hzk, hzj⟩ ⟨⟨g, hg⟩, hinf⟩
    have h1 : Tendsto (fun n => v (φ n) z) atTop (𝓝 (g z)) := hg.tendsto_at hzk
    have h2 : ∀ R : ℝ, ∃ N, ∀ n ≥ N, R ≤ ‖v (φ n) z‖ := by
      intro R
      obtain ⟨N, hN⟩ := hinf {z} (by intro y hy; rw [mem_singleton_iff] at hy; subst hy; exact hzj)
        isCompact_singleton R
      exact ⟨N, fun n hn => hN n hn z rfl⟩
    obtain ⟨N, hN⟩ := h2 (‖g z‖ + 1)
    have hev : ∀ᶠ n in atTop, ‖v (φ n) z‖ < ‖g z‖ + 1 := by
      filter_upwards [h1.eventually (Metric.ball_mem_nhds (g z) zero_lt_one)] with n hn
      calc ‖v (φ n) z‖ = ‖(v (φ n) z - g z) + g z‖ := by ring_nf
        _ ≤ ‖v (φ n) z - g z‖ + ‖g z‖ := norm_add_le _ _
        _ = dist (v (φ n) z) (g z) + ‖g z‖ := by rw [dist_eq_norm]
        _ < 1 + ‖g z‖ := by linarith
        _ = ‖g z‖ + 1 := by ring
    obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_atTop.mpr ⟨N, fun n hn => hN n hn⟩)).exists
    linarith
  let A : Set ℂ := ⋃ k, ⋃ (_ : ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)), G k
  let B : Set ℂ := ⋃ k, ⋃ (_ : ¬ ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)), G k
  have hAopen : IsOpen A := isOpen_biUnion (fun k _ => hGopen k)
  have hBopen : IsOpen B := isOpen_biUnion (fun k _ => hGopen k)
  have hUAB : U ⊆ A ∪ B := by
    intro z hz
    rw [hcover] at hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    by_cases hP : ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)
    · exact Or.inl (mem_biUnion hP hk)
    · exact Or.inr (mem_biUnion hP hk)
  have hAB : A ∩ B = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    rintro ⟨z, hzA, hzB⟩
    obtain ⟨k, hkF, hzk⟩ := mem_iUnion₂.mp hzA
    obtain ⟨j, hjF, hzj⟩ := mem_iUnion₂.mp hzB
    exact hcross k j ⟨z, hzk, hzj⟩ ⟨hkF, (hlim j).resolve_left hjF⟩
  have hUint : U ∩ (A ∩ B) = ∅ := by rw [hAB, inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hUc A B hAopen hBopen hUAB hUint) with hUA | hUB
  · -- all members carry a finite locally uniform limit
    have hBempty : B = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      rintro ⟨z, hz⟩
      have hzA : z ∈ A := hUA (hBsubU hz)
      have hmem : z ∈ A ∩ B := ⟨hzA, hz⟩
      rw [hAB] at hmem
      exact hmem
    have hAllF : ∀ k, ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k) := by
      intro k
      by_contra hk
      obtain ⟨z, hz⟩ := hGne k
      have hzB : z ∈ B := mem_biUnion hk hz
      rw [hBempty] at hzB
      exact hzB
    choose gs hgs using hAllF
    let kz : ℂ → ℕ := fun z => if h : ∃ k, z ∈ G k then Classical.choose h else 0
    have hkz : ∀ z, (∃ k, z ∈ G k) → z ∈ G (kz z) := by
      intro z h
      have hk : kz z = Classical.choose h := by
        dsimp only [kz]
        exact dite_eq_left h
      rw [hk]
      exact Classical.choose_spec h
    let g : ℂ → ℂ := fun z => gs (kz z) z
    have hagree : ∀ k, Set.EqOn (gs k) g (G k) := by
      intro k z hz
      have hz' : z ∈ G (kz z) := hkz z ⟨k, hz⟩
      have huniq : gs (kz z) z = gs k z :=
        TendstoLocallyUniformlyOn.unique
          ((hgs (kz z)).mono (inter_subset_left : G (kz z) ∩ G k ⊆ G (kz z)))
          ((hgs k).mono (inter_subset_right : G (kz z) ∩ G k ⊆ G k))
          ⟨hz', hz⟩
      change gs k z = gs (kz z) z
      exact huniq.symm
    have hGkTLUO : ∀ k, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k) :=
      fun k => (hgs k).congr_right (hagree k)
    refine Or.inl ⟨g, ?_⟩
    rw [hcover]
    exact tendstoLocallyUniformlyOn_iUnion hGopen hGkTLUO
  · -- all members tend to infinity locally uniformly
    have hAllInf : ∀ k, TendstoLocallyUniformlyAtTop (fun n => v (φ n)) (G k) := by
      intro k
      by_contra hk
      have hkF : ∃ g, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k) :=
        (hlim k).resolve_right hk
      obtain ⟨z, hz⟩ := hGne k
      have hzU : z ∈ U := by rw [hcover]; exact mem_iUnion.mpr ⟨k, hz⟩
      have hzB : z ∈ B := hUB hzU
      obtain ⟨j, hjF, hzj⟩ := mem_iUnion₂.mp hzB
      exact hcross k j ⟨z, hz, hzj⟩ ⟨hkF, (hlim j).resolve_left hjF⟩
    refine Or.inr ?_
    intro K hKU hK R
    have hpt : ∀ z ∈ K, ∃ (k : ℕ) (ε : ℝ), 0 < ε ∧ Metric.closedBall z ε ⊆ G k := by
      intro z hz
      have hzU : z ∈ U := hKU hz
      rw [hcover] at hzU
      obtain ⟨k, hk⟩ := mem_iUnion.mp hzU
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hGopen k) z hk
      exact ⟨k, ε / 2, by linarith,
        (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
    choose! kk εε hpos hsub using hpt
    obtain ⟨t, htc, ht⟩ := hK.elim_nhds_subcover (fun z => Metric.ball z (εε z))
      (fun z hz => Metric.ball_mem_nhds z (hpos z hz))
    have hN : ∀ z ∈ t, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ Metric.closedBall z (εε z), R ≤ ‖v (φ n) y‖ :=
      fun z hz => hAllInf (kk z) (Metric.closedBall z (εε z)) (hsub z (htc z hz))
        (isCompact_closedBall z (εε z)) R
    choose! Nz hNz using hN
    refine ⟨t.sup Nz, fun n hn y hy => ?_⟩
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht hy)
    exact hNz z hzt n (le_trans (Finset.le_sup (s := t) (f := Nz) hzt) hn) y
      (Metric.ball_subset_closedBall hyz)

end Work.Normal
