import Mathlib
import Submission.Work.Repel.locally_inj_of_deriv_ne_zero

/-!
# Injectivity on a neighbourhood of a compact set

`Work.Repel.exists_open_injOn_of_compact`: a holomorphic map `φ` that is injective on a compact
set `K` and whose derivative does not vanish on `K` is injective on some open neighbourhood of `K`.

The proof is a compactness argument.  Since `K` is compact and sits in the open set `D`, some
`cthickening` `C` of `K` is compact and contained in `D`; in particular `φ` is continuous on `C`.

Let `B` be the set of *bad pairs* `(x, y) ∈ C × C` with `φ x = φ y` and `x ≠ y`.  We show that
`closure B` is disjoint from `K × K`.  Indeed, a point `p ∈ closure B ∩ (K × K)` is a limit of
bad pairs, so by continuity `φ p.1 = φ p.2`, and injectivity on `K` gives `p.1 = p.2 =: a`; but
then `locally_inj_of_deriv_ne_zero` (which uses `deriv φ a ≠ 0`) exhibits a ball around `a` on
which `φ` is injective, which `closure B` would have to meet — contradiction.

Now `closure B ⊆ C × C` is compact, `K × K` is compact, and the two are disjoint, so they have
disjoint thickenings: there is `δ > 0` with `thickening δ (closure B)` disjoint from
`thickening δ (K × K)`.  Taking `U` to be a small thickening of `K` (small enough that `U ⊆ C`
and `U ⊆ thickening δ K`), any two points `x, y ∈ U` with `φ x = φ y` are either equal or form a
bad pair lying in both thickenings, which is impossible.
-/

open Metric Filter
open scoped Topology

namespace Work.Repel

theorem exists_open_injOn_of_compact {φ : ℂ → ℂ} {D K : Set ℂ}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) (hdiff : DifferentiableOn ℂ φ D)
    (hinj : Set.InjOn φ K) (hloc : ∀ z ∈ K, deriv φ z ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ Set.InjOn φ U := by
  have hcontD : ContinuousOn φ D := hdiff.continuousOn
  -- A compact closed neighbourhood `C` of `K` contained in `D`.
  obtain ⟨R, hRpos, hRsub⟩ := hK.exists_cthickening_subset_open hD hKD
  obtain ⟨R₀, hR₀pos, hR₀comp⟩ := hK.exists_isCompact_cthickening
  set R₁ : ℝ := min R R₀ with hR₁
  have hR₁pos : 0 < R₁ := lt_min hRpos hR₀pos
  set C : Set ℂ := cthickening R₁ K with hC
  have hCsubR₀ : C ⊆ cthickening R₀ K := cthickening_mono (min_le_right R R₀) K
  have hCcomp : IsCompact C := hR₀comp.of_isClosed_subset isClosed_cthickening hCsubR₀
  have hCclosed : IsClosed C := hCcomp.isClosed
  have hCsubD : C ⊆ D := (cthickening_mono (min_le_left R R₀) K).trans hRsub
  -- The set of bad pairs inside `C × C`.
  set B : Set (ℂ × ℂ) := {p | p.1 ∈ C ∧ p.2 ∈ C ∧ φ p.1 = φ p.2 ∧ p.1 ≠ p.2} with hB
  have hBsub : B ⊆ C ×ˢ C := fun p hp => ⟨hp.1, hp.2.1⟩
  have hTsub : closure B ⊆ C ×ˢ C := closure_minimal hBsub (hCclosed.prod hCclosed)
  have hTcomp : IsCompact (closure B) :=
    (hCcomp.prod hCcomp).of_isClosed_subset isClosed_closure hTsub
  -- `closure B` is disjoint from `K × K`.
  have hTdisj : Disjoint (closure B) (K ×ˢ K) := by
    rw [Set.disjoint_left]
    intro p hpT hpK
    have hp1K : p.1 ∈ K := hpK.1
    have hp2K : p.2 ∈ K := hpK.2
    -- A limit of bad pairs has equal images.
    have heq : φ p.1 = φ p.2 := by
      obtain ⟨u, huB, hutend⟩ := mem_closure_iff_seq_limit.mp hpT
      have h1 : Tendsto (fun n => φ (u n).1) atTop (𝓝 (φ p.1)) :=
        ((hcontD.continuousAt (hD.mem_nhds (hKD hp1K))).tendsto).comp
          ((continuous_fst.tendsto p).comp hutend)
      have h2 : Tendsto (fun n => φ (u n).2) atTop (𝓝 (φ p.2)) :=
        ((hcontD.continuousAt (hD.mem_nhds (hKD hp2K))).tendsto).comp
          ((continuous_snd.tendsto p).comp hutend)
      have hfun : (fun n => φ (u n).1) = (fun n => φ (u n).2) := by
        funext n; exact (huB n).2.2.1
      rw [hfun] at h1
      exact tendsto_nhds_unique h1 h2
    have hp_eq : p.1 = p.2 := hinj hp1K hp2K heq
    -- Local injectivity at `p.1`, contradicting accumulation of bad pairs.
    obtain ⟨ρ, hρpos, hρinj⟩ :=
      locally_inj_of_deriv_ne_zero (hdiff.analyticAt (hD.mem_nhds (hKD hp1K)))
        (hloc p.1 hp1K)
    rw [Metric.mem_closure_iff] at hpT
    obtain ⟨q, hqB, hqdist⟩ := hpT ρ hρpos
    have hpq : max (dist p.1 q.1) (dist p.2 q.2) < ρ := by
      rwa [Prod.dist_eq] at hqdist
    have hq1 : q.1 ∈ ball p.1 ρ := by
      rw [mem_ball, dist_comm]
      exact lt_of_le_of_lt (le_max_left _ _) hpq
    have hq2 : q.2 ∈ ball p.1 ρ := by
      rw [mem_ball, dist_comm, hp_eq]
      exact lt_of_le_of_lt (le_max_right _ _) hpq
    have hqq : q.1 = q.2 := hρinj hq1 hq2 hqB.2.2.1
    exact hqB.2.2.2 hqq
  -- Separate the compact sets `closure B` and `K × K`.
  obtain ⟨δ, hδpos, hδdisj⟩ := hTdisj.exists_thickenings hTcomp (hK.prod hK).isClosed
  set r : ℝ := min R₁ δ with hr
  have hrpos : 0 < r := lt_min hR₁pos hδpos
  have hrR₁ : r ≤ R₁ := min_le_left _ _
  have hrδ : r ≤ δ := min_le_right _ _
  refine ⟨thickening r K, isOpen_thickening, self_subset_thickening hrpos K, ?_⟩
  intro x hx y hy hxy
  have hxC : x ∈ C := (thickening_subset_cthickening r K |>.trans
    (cthickening_mono hrR₁ K)) hx
  have hyC : y ∈ C := (thickening_subset_cthickening r K |>.trans
    (cthickening_mono hrR₁ K)) hy
  have hxδ : x ∈ thickening δ K := (thickening_mono hrδ K) hx
  have hyδ : y ∈ thickening δ K := (thickening_mono hrδ K) hy
  by_contra hne
  have hpB : (x, y) ∈ B := ⟨hxC, hyC, hxy, hne⟩
  have hpT : (x, y) ∈ closure B := subset_closure hpB
  have hprod : (x, y) ∈ thickening δ (K ×ˢ K) := by
    rw [Metric.mem_thickening_iff] at hxδ hyδ ⊢
    obtain ⟨a, haK, hxa⟩ := hxδ
    obtain ⟨b, hbK, hyb⟩ := hyδ
    exact ⟨(a, b), ⟨haK, hbK⟩, by rw [Prod.dist_eq]; exact max_lt hxa hyb⟩
  have hTδ : (x, y) ∈ thickening δ (closure B) :=
    self_subset_thickening hδpos (closure B) hpT
  exact (Set.disjoint_left.mp hδdisj) hTδ hprod

end Work.Repel
