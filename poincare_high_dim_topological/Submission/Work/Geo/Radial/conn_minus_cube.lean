import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Geo.Radial.Basic
import Submission.Work.Geo.Radial.chartPush
import Submission.Work.Geo.Radial.exists_extension_of_homotopy
import Submission.Work.Geo.Radial.exists_chart_push_t2
import Submission.Work.Geo.Radial.exists_radial_push
import Submission.Work.Geo.Radial.exists_missing_point_t2

/-!
# Blueprint C1: the complement of a closed cube chart is `(n-3)`-connected

Area `A7` (`Geo/Radial+Conn-rel`), blueprint §3 `C1`.

`Work.Geo.Radial.conn_minus_cube` : for `M` a metric space, `c : PL.CubeChart n M`,
`0 < β < 1` and `j + 3 ≤ n`, if `M` is `j`-connected (`PL.ExtOverDisc M j`) then so is the
complement of the closed chart cube `c.toFun '' PL.closedCube β`.

Proof, following blueprint §3 C1 with the mesh/engulfing bookkeeping replaced by a purely radial
argument:

* choose `m`, `τ` with `0 < m ≤ β`, `β < τ < 1`, and the push parameters
  `ε₁ = β - m < τ + 2m < τ + 4m < τ + 8m`;
* extend `f` over the disc (`hM`), push its image off the open `τ`-cube with the chart push
  `h₁` built from `exists_radial_push`/`exists_chart_push_t2`
  (`chartPush_avoids_openCube`), which also keeps the complement of the cube inside itself
  (`chartPush_notMem_of_notMem`);
* use `exists_missing_point_t2` (dimension count `j + 1 < n`, Stone–Weierstrass + Sard) to move
  the image off the chart image of a small cube `ocubeAround q ε₂` with `|q i| ≤ m`, keeping the
  boundary values;
* push once more, now centred at the missed point `q` (`chartPush2_avoids_closedCube`), which
  moves the whole image off the closed `β`-cube;
* the two push families give homotopies `f ≃ (h₁ 1) ∘ f ≃ (h₂ 1)(h₁ 1) ∘ f` inside the
  complement, and the final map extends the last one, so `exists_extension_of_homotopy` (gluing
  the homotopy with the extension over the disc) produces the required extension of `f`.

`M` is assumed metric, as in the blueprint; `[T2Space M]` is what the two chart lemmas need and
is automatic here.
-/

open Set Metric
open scoped Topology
open ContinuousMap

namespace Work.Geo.Radial

theorem conn_minus_cube {n : ℕ} {M : Type*} [MetricSpace M] (c : PL.CubeChart n M) (β : ℝ)
    (h0 : 0 < β) (h1 : β < 1) (j : ℕ) (hj : j + 3 ≤ n) (hM : PL.ExtOverDisc M j) :
    PL.ExtOverDisc ↥((c.toFun '' PL.closedCube β)ᶜ) j := by
  classical
  intro f
  have hj' : j + 1 < n := by omega
  -- the `M`-valued boundary map
  let fM : C(Metric.sphere (0 : PL.E (j + 1)) 1, M) :=
    ⟨fun x => (f x : M), continuous_subtype_val.comp f.continuous⟩
  have hfM : ∀ x : Metric.sphere (0 : PL.E (j + 1)) 1, fM x ∉ c.toFun '' PL.closedCube β :=
    fun x => (f x).2
  obtain ⟨g₀, hg₀⟩ := hM fM
  -- parameters
  set m : ℝ := min β (1 - β) / 128 with hmdef
  have hm_pos : 0 < m := by
    rw [hmdef]; exact div_pos (lt_min h0 (by linarith)) (by norm_num)
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  have hmβ : m ≤ β := by
    rw [hmdef, div_le_iff₀ (by norm_num : (0:ℝ) < 128)]
    linarith [min_le_left β (1 - β), h0]
  have hmβ' : m < β := by
    rw [hmdef, div_lt_iff₀ (by norm_num : (0:ℝ) < 128)]
    linarith [min_le_left β (1 - β)]
  have hm128 : m ≤ (1 - β) / 128 := by
    rw [hmdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  set τ : ℝ := (1 + β) / 2 with hτdef
  have hβτ : β < τ := by rw [hτdef]; linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτpos : 0 < τ := lt_trans h0 hβτ
  have hβτ'₁ : β < τ + 8 * m := by linarith
  have hττ'₁ : τ < τ + 8 * m := by linarith
  have hτ'₁1 : τ + 8 * m < 1 := by
    have h2 : 8 * m ≤ 8 * ((1 - β) / 128) := by linarith
    have h3 : τ + 8 * ((1 - β) / 128) = (9 + 7 * β) / 16 := by rw [hτdef]; ring
    linarith
  have hβ'₂1 : β + 8 * m < 1 := by
    have h2 : 8 * m ≤ 8 * ((1 - β) / 128) := by linarith
    linarith
  have hββ'₂ : β < β + 8 * m := by linarith
  -- first radial push (centred at the origin)
  obtain ⟨H₁, hH₁c, hH₁0, hH₁fix, hH₁maps, hH₁push, hH₁lam⟩ :=
    exists_radial_push (0 : PL.E n) (ε := β - m) (R := τ + 2 * m) (S := τ + 4 * m)
      (by linarith) (by linarith) (by linarith)
  obtain ⟨h₁, hh₁c, hh₁0, hh₁id, hh₁chart⟩ :=
    exists_chart_push_t2 c (q := (0 : PL.E n)) (m := m) (S := τ + 4 * m) (τ := τ + 8 * m)
      (fun _ => by simpa using hm_nonneg)
      (by linarith) (by linarith) (by linarith) H₁ hH₁c hH₁0 hH₁fix hH₁maps
  -- the first chart push preserves the complement of the cube
  have hav₁s : ∀ s : unitInterval, ∀ p : M, p ∉ c.toFun '' PL.closedCube β →
      (h₁ s) p ∉ c.toFun '' PL.closedCube β := fun s p hp =>
    chartPush_notMem_of_notMem c (le_of_lt h0) h1 (q := (0 : PL.E n)) (m := m) (τ := τ + 8 * m)
      (fun _ => by simpa using hm_nonneg) hmβ hβτ'₁ (le_of_lt hτ'₁1)
      (fun y => hH₁lam s y) (hh₁id s) (hh₁chart s) hp
  -- and it moves the complement off the `τ`-cube
  have hav₁τ : ∀ p : M, p ∉ c.toFun '' PL.closedCube β →
      (h₁ 1) p ∉ c.toFun '' PL.openCube τ := fun p hp =>
    chartPush_avoids_openCube c h1 hm_nonneg (β := β) (τ := τ) (τ' := τ + 8 * m) (m := m)
      (ε := β - m) (R := τ + 2 * m) (by linarith) (by linarith) hττ'₁ (le_of_lt hτ'₁1)
      (fun y hy => hH₁push y hy) (hh₁id 1) (hh₁chart 1) hp
  -- the pushed extension and its boundary avoidance
  let g₁ : C(Metric.closedBall (0 : PL.E (j + 1)) 1, M) :=
    ⟨fun u => (h₁ 1) (g₀ u), (h₁ 1).continuous.comp g₀.continuous⟩
  have hg₁bound : ∀ x : Metric.sphere (0 : PL.E (j + 1)) 1,
      g₁ ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = (h₁ 1) (fM x) := by
    intro x
    show (h₁ 1) (g₀ ⟨x.1, _⟩) = (h₁ 1) (fM x)
    rw [hg₀ x]
  have hg₁avoid : ∀ x : Metric.sphere (0 : PL.E (j + 1)) 1,
      g₁ ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ ∉ c.toFun '' PL.openCube τ := by
    intro x
    rw [hg₁bound x]
    exact hav₁τ (fM x) (hfM x)
  -- move the image off a small chart cube
  obtain ⟨ĝ, hĝbound, q, hq, ε₂, hε₂pos, hε₂avoid⟩ :=
    exists_missing_point_t2 hj' c (β₂ := τ) (m := m) hm_pos (lt_of_le_of_lt hmβ hβτ) hτ1 g₁ hg₁avoid
  -- second radial push (centred at the missed point)
  set ε₂' : ℝ := min ε₂ ((β + m) / 2) with hε₂'def
  have hε₂'pos : 0 < ε₂' := by rw [hε₂'def]; exact lt_min hε₂pos (by linarith)
  have hε₂'le : ε₂' ≤ ε₂ := by rw [hε₂'def]; exact min_le_left _ _
  have hε₂'R : ε₂' < β + 2 * m := by
    rw [hε₂'def]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨H₂, hH₂c, hH₂0, hH₂fix, hH₂maps, hH₂push, hH₂lam⟩ :=
    exists_radial_push q (ε := ε₂') (R := β + 2 * m) (S := β + 4 * m)
      hε₂'pos hε₂'R (by linarith)
  obtain ⟨h₂, hh₂c, hh₂0, hh₂id, hh₂chart⟩ :=
    exists_chart_push_t2 c (q := q) (m := m) (S := β + 4 * m) (τ := β + 8 * m)
      hq (by linarith) (by linarith) (by linarith) H₂ hH₂c hH₂0 hH₂fix hH₂maps
  have hav₂ : ∀ p : M, p ∉ c.toFun '' ocubeAround q ε₂' →
      (h₂ 1) p ∉ c.toFun '' PL.closedCube β := fun p hp =>
    chartPush2_avoids_closedCube c h1 (q := q) hq (τ' := β + 8 * m) (R₂ := β + 2 * m) (ε := ε₂')
      (by linarith) (le_of_lt hβ'₂1) hββ'₂ (fun y hy => hH₂push y hy) (hh₂id 1) (hh₂chart 1) hp
  have hav₂c : ∀ s : unitInterval, ∀ p : M, p ∉ c.toFun '' PL.closedCube β →
      (h₂ s) p ∉ c.toFun '' PL.closedCube β := fun s p hp =>
    chartPush_notMem_of_notMem c (le_of_lt h0) h1 (q := q) (m := m) (τ := β + 8 * m)
      hq hmβ hββ'₂ (le_of_lt hβ'₂1) (fun y => hH₂lam s y) (hh₂id s) (hh₂chart s) hp
  -- the final extension, in `M`
  let g₂ : C(Metric.closedBall (0 : PL.E (j + 1)) 1, M) :=
    ⟨fun u => (h₂ 1) (ĝ u), (h₂ 1).continuous.comp ĝ.continuous⟩
  have hg₂avoid : ∀ u : Metric.closedBall (0 : PL.E (j + 1)) 1,
      g₂ u ∉ c.toFun '' PL.closedCube β := fun u =>
    hav₂ (ĝ u)
      (fun hmem => hε₂avoid u (Set.image_mono (ocubeAround_mono hε₂'le) hmem))
  -- the complement-valued maps
  let F₀ : C(Metric.sphere (0 : PL.E (j + 1)) 1, ↥((c.toFun '' PL.closedCube β)ᶜ)) := f
  let F₁ : C(Metric.sphere (0 : PL.E (j + 1)) 1, ↥((c.toFun '' PL.closedCube β)ᶜ)) :=
    ⟨fun x => ⟨(h₁ 1) (fM x), hav₁s 1 (fM x) (hfM x)⟩,
      Continuous.subtype_mk ((h₁ 1).continuous.comp fM.continuous) _⟩
  let F₂ : C(Metric.sphere (0 : PL.E (j + 1)) 1, ↥((c.toFun '' PL.closedCube β)ᶜ)) :=
    ⟨fun x => ⟨(h₂ 1) ((h₁ 1) (fM x)), hav₂ (h₁ 1 (fM x))
        (fun hmem => hε₂avoid ⟨x.1, Metric.sphere_subset_closedBall x.2⟩
          (by rw [hĝbound, hg₁bound]
              exact Set.image_mono (ocubeAround_mono hε₂'le) hmem))⟩,
      Continuous.subtype_mk (((h₂ 1).continuous.comp (h₁ 1).continuous).comp fM.continuous) _⟩
  let G₂ : C(Metric.closedBall (0 : PL.E (j + 1)) 1, ↥((c.toFun '' PL.closedCube β)ᶜ)) :=
    ⟨fun u => ⟨g₂ u, hg₂avoid u⟩, Continuous.subtype_mk g₂.continuous _⟩
  -- the two homotopies
  have Ht₁ : F₀.Homotopic F₁ := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × Metric.sphere (0 : PL.E (j + 1)) 1 =>
          ⟨(h₁ p.1) (fM p.2), hav₁s p.1 (fM p.2) (hfM p.2)⟩, ?_⟩ ?_ ?_⟩
    · refine Continuous.subtype_mk ?_ _
      fun_prop
    · intro x
      refine Subtype.ext ?_
      show (h₁ 0) (fM x) = fM x
      rw [hh₁0]
      rfl
    · intro x
      rfl
  have Ht₂ : F₁.Homotopic F₂ := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × Metric.sphere (0 : PL.E (j + 1)) 1 =>
          ⟨(h₂ p.1) ((h₁ 1) (fM p.2)),
            hav₂c p.1 ((h₁ 1) (fM p.2)) (hav₁s 1 (fM p.2) (hfM p.2))⟩, ?_⟩ ?_ ?_⟩
    · refine Continuous.subtype_mk ?_ _
      fun_prop
    · intro x
      refine Subtype.ext ?_
      show (h₂ 0) ((h₁ 1) (fM x)) = (h₁ 1) (fM x)
      rw [hh₂0]
      rfl
    · intro x
      rfl
  have hG₂ : ∀ x : Metric.sphere (0 : PL.E (j + 1)) 1,
      G₂ ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = F₂ x := by
    intro x
    refine Subtype.ext ?_
    show (h₂ 1) (ĝ ⟨x.1, _⟩) = (h₂ 1) ((h₁ 1) (fM x))
    rw [hĝbound x, hg₁bound x]
  obtain ⟨Φ, hΦ⟩ := exists_extension_of_homotopy (Ht₁.trans Ht₂) G₂ hG₂
  exact ⟨Φ, hΦ⟩
end Work.Geo.Radial
