import Mathlib
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite

/-!
# The clean exit out of a set with a flat frontier

This file proves the mathematical content of the "(c3)" step of the spine-recursion redesign: a
point of `interior S` lying in an open carrier `E`, whose component reaches the frontier of `S`, can
be joined to a point outside `S` by an arc which crosses the frontier of `S` **exactly once**, and
cleanly: the set of parameters at which the arc lies in `S` is an initial segment of `[0,1]`.

## Why this is the right notion

A level arc of the spine recursion has to cross the frontier `∂K (ℓ+1)`; the part of the arc lying
outside `K (ℓ+1)` is its *footprint* in the next shell, and it is this footprint which the next
level's arcs must avoid.  If the crossing is clean then the footprint is a **spike** (an arc
attached to the frontier with one free end), which is a harmless obstacle
(`escape_spikes_and_slits`); if the arc crosses several times, the footprint contains **crosscut**
pieces, which can cut off (and hence trap) the next level's start points.  So the whole remaining
difficulty of the level step is concentrated in the *flatness* of the frontier (see
`flat_frontier.lean`) and in the present lemma.

## The statement proved here

`exists_clean_exit_path`: let `E` be open, `S` a set, `p ∈ E ∩ interior S`, `z ∈ frontier S` with
`z ∈ closure (connectedComponentIn (E ∩ interior S) p)` — the component of `p` accumulates at the
frontier point `z` — and suppose the crossing at `z` is clean *inside* `E`
(`CleanCrossingIn E S z`).  Then there is a continuous `α` with `α 0 = p`, `α '' [0,1] ⊆ E`,
`α(Icc 0 s) ⊆ S` and `α t ∉ S` for `t > s`.

The proof is a concatenation: an arc inside the component (an open path-connected set, so arcs are
provided by `exists_arc_of_isPathConnected`) up to a point `p'` of the crossing neighbourhood `U`
of `z`, followed by the clean crossing arc from `p'` to a point `q' ∉ S` supplied by the flatness.
Every obstacle the application needs to avoid is hidden in `E`, so the arc avoids them
automatically.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **Clean crossing of a frontier inside a carrier `E`.**  There is an open set `U ⊆ E` around the
frontier point `z` such that any two points of `U`, one in `interior S` and one outside `S`, can be
joined by an *arc* in `U` meeting `S` in an initial segment of its parameter interval. -/
def CleanCrossingIn (E S : Set M) (z : M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ U ⊆ E ∧ z ∈ U ∧
    ∀ p ∈ U ∩ interior S, ∀ q ∈ U \ S,
      ∃ (s : ℝ) (α : ℝ → M), Continuous α ∧ α 0 = p ∧ α 1 = q ∧
        α '' Icc (0 : ℝ) 1 ⊆ U ∧ Set.InjOn α (Icc (0 : ℝ) 1) ∧ s ∈ Icc (0 : ℝ) 1 ∧
        (∀ t ∈ Icc (0 : ℝ) s, α t ∈ S) ∧ (∀ t ∈ Ioc s 1, α t ∉ S)

/-- **The clean exit.**  An arc from `p` leaving `S` exactly once, inside the carrier `E`, provided
the component of `p` in `E ∩ interior S` accumulates at the frontier point `z` and the crossing at
`z` is clean. -/
theorem exists_clean_exit_path {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {E S : Set M} (hE : IsOpen E) {p z : M}
    (hp : p ∈ E ∩ interior S) (hz : z ∈ frontier S)
    (hflat : CleanCrossingIn E S z)
    (hreach : z ∈ closure (connectedComponentIn (E ∩ interior S) p)) :
    ∃ (s : ℝ) (α : ℝ → M), Continuous α ∧ α 0 = p ∧ α '' Icc (0 : ℝ) 1 ⊆ E ∧
      s ∈ Icc (0 : ℝ) 1 ∧ (∀ t ∈ Icc (0 : ℝ) s, α t ∈ S) ∧ (∀ t ∈ Ioc s 1, α t ∉ S) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  obtain ⟨U, hUopen, hUE, hzU, hcross⟩ := hflat
  set R : Set M := connectedComponentIn (E ∩ interior S) p with hRdef
  have hpR : p ∈ R := by rw [hRdef]; exact mem_connectedComponentIn hp
  have hRsub : R ⊆ E ∩ interior S := by
    rw [hRdef]; exact connectedComponentIn_subset _ _
  have hRopen : IsOpen R := by
    rw [hRdef]; exact (hE.inter isOpen_interior).connectedComponentIn
  have hRpc : IsPreconnected R := by
    rw [hRdef]; exact isPreconnected_connectedComponentIn
  have hpath : IsPathConnected R :=
    hRopen.isConnected_iff_isPathConnected.mp ⟨⟨p, hpR⟩, hRpc⟩
  -- a point `p'` of the component inside the crossing neighbourhood, and `q' ∉ S` therein
  obtain ⟨p', hp'U, hp'R⟩ := mem_closure_iff_nhds.mp hreach U (hUopen.mem_nhds hzU)
  have hp'S : p' ∈ U ∩ interior S := ⟨hp'U, (hRsub hp'R).2⟩
  have hq'ne : (U \ S).Nonempty := by
    have hzcl : z ∈ closure (Sᶜ) := by
      rw [closure_compl]; exact hz.2
    exact mem_closure_iff_nhds.mp hzcl U (hUopen.mem_nhds hzU)
  obtain ⟨q', hq'U, hq'S⟩ := hq'ne
  -- the clean crossing arc from `p'` to `q'`
  obtain ⟨s, w, hwc, hw0, hw1, hwU, _hwInj, hs01, hwS, hwS'⟩ :=
    hcross p' hp'S q' ⟨hq'U, hq'S⟩
  -- an arc inside the component from `p` to `p'`
  obtain ⟨u, huc, hu0, hu1, huR⟩ : ∃ u : ℝ → M, Continuous u ∧ u 0 = p ∧ u 1 = p' ∧
      ∀ t ∈ Icc (0 : ℝ) 1, u t ∈ R := by
    rcases eq_or_ne p p' with h | h
    · exact ⟨fun _ => p, continuous_const, rfl, h, fun t ht => hpR⟩
    · obtain ⟨u, huc, _huinj, hu0, hu1, huR⟩ :=
        Work.Whitney.PathTools.exists_arc_of_isPathConnected (n := n) hRopen hpath hpR hp'R h
      exact ⟨u, huc, hu0, hu1, huR⟩
  -- the concatenation of the two arcs
  set α : ℝ → M := fun t : ℝ => if t ≤ 1 / 2 then u (2 * t) else w (2 * t - 1) with hαdef
  have hαle : ∀ t : ℝ, t ≤ 1 / 2 → α t = u (2 * t) := by
    intro t ht
    change (if t ≤ 1 / 2 then u (2 * t) else w (2 * t - 1)) = u (2 * t)
    rw [if_pos ht]
  have hαgt : ∀ t : ℝ, 1 / 2 < t → α t = w (2 * t - 1) := by
    intro t ht
    change (if t ≤ 1 / 2 then u (2 * t) else w (2 * t - 1)) = w (2 * t - 1)
    rw [if_neg (not_le.mpr ht)]
  have hcont : Continuous α := by
    rw [hαdef]
    refine Continuous.if_le (huc.comp (by fun_prop)) (hwc.comp (by fun_prop))
      continuous_id continuous_const ?_
    intro t ht
    have h1 : u (2 * t) = p' := by rw [ht]; norm_num; exact hu1
    have h2 : w (2 * t - 1) = p' := by rw [ht]; norm_num; exact hw0
    rw [h1, h2]
  set s' : ℝ := (1 + s) / 2 with hs'def
  have hs'0 : 0 ≤ s' := by rw [hs'def]; linarith [hs01.1]
  have hs'1 : s' ≤ 1 := by rw [hs'def]; linarith [hs01.2]
  have hs'half : (1 : ℝ) / 2 ≤ s' := by rw [hs'def]; linarith [hs01.1]
  have hle : ∀ t : ℝ, t ≤ s' → 2 * t - 1 ≤ s := by
    intro t ht
    have h2 : 2 * t ≤ 2 * s' := by linarith
    rw [hs'def] at h2
    linarith
  have hlt : ∀ t : ℝ, s' < t → s < 2 * t - 1 := by
    intro t ht
    have h2 : 2 * s' < 2 * t := by linarith
    rw [hs'def] at h2
    linarith
  refine ⟨s', α, hcont, ?_, ?_, ⟨hs'0, hs'1⟩, ?_, ?_⟩
  · rw [hαle 0 (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero, hu0]
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    by_cases h : t ≤ 1 / 2
    · rw [hαle t h]
      exact (hRsub (huR (2 * t) ⟨by linarith [ht.1], by linarith⟩)).1
    · rw [hαgt t (not_le.mp h)]
      exact hUE (hwU ⟨2 * t - 1, ⟨by linarith [ht.1, not_le.mp h], by linarith [ht.2]⟩, rfl⟩)
  · intro t ht
    by_cases h : t ≤ 1 / 2
    · rw [hαle t h]
      exact interior_subset ((hRsub (huR (2 * t) ⟨by linarith [ht.1], by linarith⟩)).2)
    · rw [hαgt t (not_le.mp h)]
      exact hwS (2 * t - 1) ⟨by linarith [not_le.mp h], hle t ht.2⟩
  · intro t ht
    rw [hαgt t (by linarith [ht.1, hs'half])]
    exact hwS' (2 * t - 1) ⟨hlt t ht.1, by linarith [ht.2]⟩

end Work.Noncompact.CompressionTube
