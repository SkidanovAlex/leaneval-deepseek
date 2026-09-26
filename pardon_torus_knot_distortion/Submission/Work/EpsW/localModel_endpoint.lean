import Mathlib
import Submission.Work.EpsW.arcsWallFamily_aux
import Submission.Work.EpsW.exists_half_arc
import Submission.Work.EpsW.exists_half_level_param

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.Smooth.OneManifold

namespace Work.EpsW

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- The equator point lies in the wall trace. -/
theorem endpt_mem_Wset {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hhend : ∀ j : Fin n,
      arcEnd0 a j ∈ Work.BoxShrink.Core.sphereSet c σ s ∧
        arcEnd1 a j ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (p : Fin n × Fin 2) : endpt a p ∈ Wset P s c σ u := by
  have h := endpt_mem_closures ha hhend p
  rw [Wset_eq]
  refine Or.inl ⟨h.1, ?_⟩
  show c (σ 2) + u ≤ lvl σ (endpt a p)
  rw [h.2]

open LeanEval.KnotTheory.PardonDistortion in
/-- **The local model of the wall trace at an equator point.**  At an equator point `e = endpt a p` (a common endpoint of a slice arc and of the sphere trace, where the cutting plane meets the box sphere) the wall trace `Wset P s c σ u = P.carrier ∩ wall s c σ u` is locally the union of the *up half* of the sphere-trace curve through `e` (the half on which the level `y ↦ y (σ 2)` exceeds `c (σ 2) + u`, singled out by `hcross`) and the half of the slice arc of `a` starting at `e`.  These two arcs meet exactly at `e`, so the trace is locally an arc (`Work.EpsW.localArc_gluedPair`).

PROOF PLAN (also in the module docstring of `Submission/Work/EpsW/arcsWallFamily_aux.lean`):
1. `endpt_mem_closures` gives `e ∈ Gset P s c σ` with `lvl σ e = c (σ 2) + u`; `Gset_eq_iUnion`/`Gset_subset_iUnion` put `e` on a curve `Sl.c i₀`, and `gamma_fract_mul` reduces its parameter to `t₀ ∈ Ico 0 (2 π)`.
2. The crossings of `Sl.c i₀` are exactly the (finitely many) equator points: a crossing point lies in `Gset ∩ cutPlane = Set.range (endpt a)` by `range_endpt_eq_equator` + `heq`, `range (endpt a)` is finite, and `(Sl.c i₀).γ` is injective on `Ico 0 (2 π)`.  Feed this to `exists_isolated_levelSet` to get `δ₁ > 0` with `lvl σ ((Sl.c i₀).γ t) = c (σ 2) + u → |t - t₀| < δ₁ → t = t₀`.
3. On each side of `t₀` (within `δ := δ₁/2`) the level has constant sign (`sign_constant_of_no_zero`, `intermediate_value_Icc`), and the signs of the two sides are opposite by `hcross i₀ t₀ _` (points of both signs occur within `δ`, and they cannot be on the same side).  Hence with `d := if upRight then δ else -δ`, `f s := (Sl.c i₀).γ (t₀ + (1 - s) * d)` is an injective arc ending at `e`, whose image is the up half of the trace.
4. The slice half is `g s := a p.1 (if (p.2 : ℕ) = 0 then s / 2 else 1 - s / 2)`, an injective arc starting at `e`, and `Set.range f ∩ Set.range g = {e}` (using `hint` and the isolation of `t₀`).
5. `localArc_gluedPair f g` gives `O' ∋ e` open with `IsLocallyEuclidean (O' ∩ (range f ∪ range g))`.
6. Intersect `O'` with the complements of `otherArcs a p.1`, `otherCurves Sl i₀`, the local models of `exists_isOpen_localModel_periodic` and `exists_isOpen_localModel_arc` at `e`, to get `O ∩ Wset P s c σ u = O ∩ (range f ∪ range g)` via `Wset_eq`; finish with `IsLocallyEuclidean.inter_isOpen`. -/
theorem localModel_endpoint {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (hcross : ∀ (i : Sl.ι) (t : ℝ), (Sl.c i).γ t (σ 2) = c (σ 2) + u →
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ c (σ 2) + u < (Sl.c i).γ t' (σ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ (Sl.c i).γ t' (σ 2) < c (σ 2) + u))
    {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3))
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Work.EpsW.Sigset P s c σ u))
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcover : closure (Work.EpsW.Sigset P s c σ u) ⊆ ⋃ j, Set.range (a j))
    (hint : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1))
    (hhend : ∀ j : Fin n, Work.EpsW.arcEnd0 a j ∈ Work.BoxShrink.Core.sphereSet c σ s ∧
      Work.EpsW.arcEnd1 a j ∈ Work.BoxShrink.Core.sphereSet c σ s)
    (heq : ∀ q ∈ P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s ∩
        Work.BoxShrink.Core.cutPlane c σ u,
      ∃ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        ((x : ℝ) = 0 ∨ (x : ℝ) = 1) ∧ a j x = q)
    (p : Fin n × Fin 2) :
    ∃ O : Set R3, IsOpen O ∧ Work.EpsW.endpt a p ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean (O ∩ Work.EpsW.Wset P s c σ u) := by
  classical
  have he := endpt_mem_closures ha hhend p
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (Gset_subset_iUnion Sl he.1)
  obtain ⟨t', ht'⟩ := hi₀
  set t₀ : ℝ := 2 * Real.pi * Int.fract (t' / (2 * Real.pi)) with ht₀def
  have hγt₀ : (Sl.c i₀).γ t₀ = endpt a p := by
    rw [ht₀def, gamma_fract_mul (Sl.c i₀).periodic t']
    exact ht'
  have hLt₀ : lvl σ ((Sl.c i₀).γ t₀) = c (σ 2) + u := by rw [hγt₀]; exact he.2
  have hfin : ({t : ℝ | lvl σ ((Sl.c i₀).γ t) = c (σ 2) + u} ∩
      Set.Ico 0 (2 * Real.pi)).Finite := by
    refine Set.Finite.of_injOn (f := (Sl.c i₀).γ) (t := Set.range (endpt a)) ?_ ?_
      (Set.finite_range (endpt a))
    · intro t ht
      rw [range_endpt_eq_equator ha hhend heq]
      exact ⟨⟨(Sl.c i₀).mem t, Sl.mem i₀ t⟩, ht.1⟩
    · intro t ht t' ht' h
      exact Sl.simple i₀ ht.2 ht'.2 h
  obtain ⟨δ₁, hδ₁pos, hiso⟩ :=
    exists_isolated_levelSet (Sl.c i₀).periodic (Sl.simple i₀) (lvl σ) (c (σ 2) + u) t₀ hfin hLt₀
  set δ : ℝ := min (δ₁ / 2) (Real.pi / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδlt : δ < δ₁ := by
    have h1 : δ ≤ δ₁ / 2 := by rw [hδdef]; exact min_le_left _ _
    linarith
  have hδpi : δ < Real.pi := by
    have h1 : δ ≤ Real.pi / 4 := by rw [hδdef]; exact min_le_right _ _
    linarith [Real.pi_pos]
  have hLcont : Continuous (lvl σ) := Work.Topology.SphereSlicing.continuous_coordR3 (σ 2)
  obtain ⟨d, hdabs, hd⟩ := exists_half_level_param (Sl.c i₀).cont hLcont hδ₁pos hLt₀ hiso
    (hcross i₀ t₀ hLt₀).1 (hcross i₀ t₀ hLt₀).2 hδpos hδlt
  have hdne : d ≠ 0 := by rw [← abs_pos, hdabs]; exact hδpos
  let f : C(Work.Smooth.Plane.ArcInterval, R3) :=
    ⟨fun x => (Sl.c i₀).γ (t₀ + (1 - (x:ℝ)) * d), by
      apply (Sl.c i₀).cont.comp
      fun_prop⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : (Sl.c i₀).γ (t₀ + (1 - (x:ℝ)) * d) =
        (Sl.c i₀).γ (t₀ + (1 - (y:ℝ)) * d) := hxy
    have hlt : |(t₀ + (1 - (x:ℝ)) * d) - (t₀ + (1 - (y:ℝ)) * d)| < 2 * Real.pi := by
      have h1 : (t₀ + (1 - (x:ℝ)) * d) - (t₀ + (1 - (y:ℝ)) * d) = ((y:ℝ) - (x:ℝ)) * d := by
        ring
      rw [h1, abs_mul]
      have h2 : |(y:ℝ) - (x:ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [x.2.1, x.2.2, y.2.1, y.2.2]
      calc |(y:ℝ) - (x:ℝ)| * |d| ≤ 1 * |d| := mul_le_mul_of_nonneg_right h2 (abs_nonneg d)
        _ = δ := by rw [hdabs, one_mul]
        _ < 2 * Real.pi := by linarith [Real.pi_pos, hδpi]
    have h3 := eq_of_abs_sub_lt (Sl.c i₀).periodic (Sl.simple i₀) hlt hxy'
    have h4 : (1 - (x:ℝ)) * d = (1 - (y:ℝ)) * d := by linarith
    have h5 : (1 - (x:ℝ)) = (1 - (y:ℝ)) := mul_right_cancel₀ hdne h4
    exact Subtype.ext (by linarith)
  have hf1 : f 1 = endpt a p := by
    have h1 : ((1 : Work.Smooth.Plane.ArcInterval) : ℝ) = 1 := rfl
    show (Sl.c i₀).γ (t₀ + (1 - ((1 : Work.Smooth.Plane.ArcInterval) : ℝ)) * d) = endpt a p
    rw [h1, sub_self, zero_mul, add_zero]
    exact hγt₀
  have harcx : ((arcPar p.2 : Work.Smooth.Plane.ArcInterval) : ℝ) = 0 ∨
      ((arcPar p.2 : Work.Smooth.Plane.ArcInterval) : ℝ) = 1 := by
    have hp2 : (p.2 : ℕ) = 0 ∨ (p.2 : ℕ) = 1 := by have := p.2.isLt; omega
    rcases hp2 with h | h
    · left; simp [arcPar, h]
    · right; simp [arcPar, h]
  obtain ⟨g, K, hg_inj, hg0, hKclosed, heK, hKsub, hgint, hgsub⟩ :=
    exists_half_arc hinj p.1 (arcPar p.2) harcx
  have hg0' : g 0 = endpt a p := by simpa [endpt_apply] using hg0
  have hfg : f 1 = g 0 := by rw [hf1, hg0']
  have hfdisj : Set.range f ∩ Set.range g = {f 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzf, hzg⟩
      rw [Set.mem_singleton_iff]
      obtain ⟨x, hx⟩ := hzf
      obtain ⟨s', hs'⟩ := hzg
      have hzG : f x ∈ Gset P s c σ :=
        iUnion_subset_Gset Sl (Set.mem_iUnion.mpr ⟨i₀, ⟨_, rfl⟩⟩)
      rcases eq_or_ne s' 0 with hs | hs
      · rw [hs] at hs'
        rw [← hs', hg0', ← hf1]
      · exfalso
        obtain ⟨y, hy, hyeq⟩ := hgint s' hs
        have hz' : a p.1 y = f x := by rw [hyeq]; exact hs'.trans hx.symm
        have hsph : a p.1 y ∈ Work.BoxShrink.Core.sphereSet c σ s := by
          rw [hz']; exact hzG.2
        rcases hint p.1 y hsph with h | h
        · exact absurd h (ne_of_gt hy.1)
        · exact absurd h (ne_of_lt hy.2)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Set.mem_range_self 1, by rw [hfg]; exact Set.mem_range_self 0⟩
  obtain ⟨Oγ, hOγopen, hγOγ, hOγeq⟩ :=
    exists_isOpen_localModel_periodic (Sl.c i₀).cont (Sl.c i₀).periodic (Sl.simple i₀) t₀ δ hδpos
  obtain ⟨O', hO'open, hf1O', hO'loc⟩ := localArc_gluedPair hf_inj hg_inj hfg hfdisj
  have hAclosed : IsClosed (otherArcs a p.1) := by
    rw [otherArcs]
    exact isClosed_iUnion_of_finite fun j => (isCompact_range (a j.1).continuous).isClosed
  have hBclosed : IsClosed (otherCurves Sl i₀) := by
    rw [otherCurves]
    exact isClosed_iUnion_of_finite fun i => Work.InnermostDisk.isClosed_range_closedCurve (Sl.c i.1)
  set O : Set R3 := O' ∩ Oγ ∩ (otherArcs a p.1)ᶜ ∩ (otherCurves Sl i₀)ᶜ ∩ Kᶜ with hOdef
  have hOopen : IsOpen O := by
    rw [hOdef]
    exact (((hO'open.inter hOγopen).inter hAclosed.isOpen_compl).inter
      hBclosed.isOpen_compl).inter hKclosed.isOpen_compl
  have heO : endpt a p ∈ O := by
    rw [hOdef]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [← hf1]; exact hf1O'
    · rw [← hγt₀]; exact hγOγ
    · rintro h
      obtain ⟨j, hj⟩ := mem_otherArcs.mp h
      exact Set.disjoint_left.mp (hdisj j.2) hj ⟨arcPar p.2, rfl⟩
    · rintro h
      obtain ⟨i, hi⟩ := mem_otherCurves.mp h
      exact Set.disjoint_left.mp (Sl.disjoint i.2) hi ⟨t₀, hγt₀⟩
    · exact heK
  have exists_arc_param : ∀ t : ℝ, |t - t₀| < δ → 0 ≤ (t - t₀) * d →
      ∃ s : Work.Smooth.Plane.ArcInterval, t₀ + (1 - (s:ℝ)) * d = t := by
    intro t ht hprod
    have hq : (t - t₀) / d * d = t - t₀ := div_mul_cancel₀ _ hdne
    have hq0 : 0 ≤ (t - t₀) / d := by
      have h2 : (t - t₀) * d / d ^ 2 = (t - t₀) / d := by field_simp
      rw [← h2]
      exact div_nonneg hprod (sq_nonneg d)
    have hq1 : (t - t₀) / d < 1 := by
      have h3 : |(t - t₀) / d| < 1 := by
        rw [abs_div]
        rw [hdabs]
        rw [div_lt_one hδpos]
        exact ht
      rw [abs_lt] at h3
      exact h3.2
    refine ⟨⟨1 - (t - t₀) / d, by linarith, by linarith⟩, ?_⟩
    show t₀ + (1 - (1 - (t - t₀) / d)) * d = t
    rw [show (1 - (1 - (t - t₀) / d)) = (t - t₀) / d by ring, hq]
    ring
  have hEq : O ∩ Wset P s c σ u = O ∩ (Set.range f ∪ Set.range g) := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzO, hzW⟩
      rw [hOdef] at hzO
      obtain ⟨⟨⟨⟨hzO', hzOγ⟩, hzA⟩, hzB⟩, hzK⟩ := hzO
      refine ⟨by rw [hOdef]; exact ⟨⟨⟨⟨hzO', hzOγ⟩, hzA⟩, hzB⟩, hzK⟩, ?_⟩
      have hzW' : z ∈ (Gset P s c σ ∩ {y : R3 | c (σ 2) + u ≤ lvl σ y}) ∪
          Sigset P s c σ u := by rw [← Wset_eq]; exact hzW
      rcases hzW' with ⟨hzG, hzu⟩ | hzSig
      · have hzun : z ∈ ⋃ i : Sl.ι, Set.range (Sl.c i).γ := Gset_subset_iUnion Sl hzG
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzun
        have hii : i = i₀ := by
          by_contra hne
          exact hzB (mem_otherCurves.mpr ⟨⟨i, hne⟩, hi⟩)
        rw [hii] at hi
        have hzγ : z ∈ Oγ ∩ Set.range (Sl.c i₀).γ := ⟨hzOγ, hi⟩
        rw [hOγeq] at hzγ
        obtain ⟨t, ht, htz⟩ := hzγ
        have htabs : |t - t₀| < δ := by
          rw [Set.mem_Ioo] at ht
          rw [abs_lt]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hlev : c (σ 2) + u ≤ lvl σ ((Sl.c i₀).γ t) := by rw [htz]; exact hzu
        have hprod : 0 ≤ (t - t₀) * d := (hd t (le_of_lt htabs)).mp hlev
        obtain ⟨sq, hsq⟩ := exists_arc_param t htabs hprod
        refine Or.inl (Set.mem_range.mpr ⟨sq, ?_⟩)
        show (Sl.c i₀).γ (t₀ + (1 - (sq:ℝ)) * d) = z
        rw [hsq]; exact htz
      · have hzun : z ∈ ⋃ j : Fin n, Set.range (a j) := hcover (subset_closure hzSig)
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzun
        have hjj : j = p.1 := by
          by_contra hne
          exact hzA (mem_otherArcs.mpr ⟨⟨j, hne⟩, hj⟩)
        rw [hjj] at hj
        exact Or.inr (hKsub ⟨hj, hzK⟩)
    · rintro z ⟨hzO, hzfg⟩
      rcases hzfg with hzf | hzg
      · obtain ⟨sq, hsq⟩ := hzf
        refine ⟨hzO, ?_⟩
        rw [Wset_eq]
        refine Or.inl ⟨?_, ?_⟩
        · rw [← hsq]
          show (Sl.c i₀).γ (t₀ + (1 - (sq:ℝ)) * d) ∈ Gset P s c σ
          exact iUnion_subset_Gset Sl (Set.mem_iUnion.mpr ⟨i₀, ⟨_, rfl⟩⟩)
        · have hclose : |(t₀ + (1 - (sq:ℝ)) * d) - t₀| ≤ δ := by
            rw [show (t₀ + (1 - (sq:ℝ)) * d) - t₀ = (1 - (sq:ℝ)) * d by ring, abs_mul]
            have h1 : |1 - (sq:ℝ)| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith [sq.2.1, sq.2.2]
            calc |1 - (sq:ℝ)| * |d| ≤ 1 * |d| := mul_le_mul_of_nonneg_right h1 (abs_nonneg d)
              _ = δ := by rw [hdabs, one_mul]
          have hprod : 0 ≤ ((t₀ + (1 - (sq:ℝ)) * d) - t₀) * d := by
            rw [show (t₀ + (1 - (sq:ℝ)) * d) - t₀ = (1 - (sq:ℝ)) * d by ring]
            have h2 : 0 ≤ (1 : ℝ) - (sq:ℝ) := by linarith [sq.2.2]
            nlinarith [sq_nonneg d]
          rw [← hsq]
          show c (σ 2) + u ≤ lvl σ ((Sl.c i₀).γ (t₀ + (1 - (sq:ℝ)) * d))
          exact (hd _ hclose).mpr hprod
      · obtain ⟨sq, hsq⟩ := hzg
        refine ⟨hzO, ?_⟩
        rw [Wset_eq]
        rcases eq_or_ne sq 0 with hs | hs
        · have hmem := endpt_mem_closures ha hhend p
          refine Or.inl ⟨?_, ?_⟩
          · rw [← hsq, hs, hg0]; exact hmem.1
          · rw [← hsq, hs, hg0]
            show c (σ 2) + u ≤ lvl σ (endpt a p)
            rw [hmem.2]
        · obtain ⟨y, hy, hyeq⟩ := hgint sq hs
          refine Or.inr ?_
          rw [← hsq, ← hyeq]
          exact mem_Sigset_of_interior ha hint (ne_of_gt hy.1) (ne_of_lt hy.2)
  refine ⟨O, hOopen, heO, ?_⟩
  have hOsub : O ⊆ O' := by
    intro z hz
    rw [hOdef] at hz
    exact hz.1.1.1.1
  have hEq2 : O ∩ Wset P s c σ u = O ∩ (O' ∩ (Set.range f ∪ Set.range g)) := by
    rw [hEq, ← Set.inter_assoc, Set.inter_eq_left.mpr hOsub]
  rw [hEq2]
  exact IsLocallyEuclidean.inter_isOpen hO'loc hOopen



end

end Work.EpsW
