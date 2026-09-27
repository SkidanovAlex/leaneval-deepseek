import Mathlib
import Submission.Work.Drive.projLine_preconnected
import Submission.Work.Drive.sideAntisymmetry

namespace Work.Drive

open scoped Manifold ContDiff Topology

/-! REFEREE NOTE (prose, not code).  **The local constancy (`hn4`) of the side function of the chain route follows from the *branch form* of the cut dichotomy, with no mod-2 counting at all.**  This removes `hn4` from the residual list of `Submission/Work/Drive/SIDE_ANTISYMMETRY_STATUS.md` section 3, where it is listed as needing the surface-locality engine or the circle-frontier lane.

Setting.  `e u` is the side value `Work.Drive.sideOf Q (fun _ => c) ψ u`, i.e. the non-emptiness of the cut of the chart by the clamped sweep of the rotated plane `u · P₀`.  `Submission/Work/Drive/sideAntisymmetry.lean` exports the two *branches* of `Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine`: on the class line `L u` (the intersection of the two planes' class images, a nonempty projective line) the cut is empty when the chart's profile `FQ` is below the swept plane's profile `G`, and is the whole class-cut when `FQ` is above `G`.  Composing with `Work.Drive.side_eq_one_iff` this is exactly the hypothesis `hval` below: `e u = 1 ↔ ∀ q ∈ L u, G u q < 0`.  For `u ∈ Zc γ` the two profiles do not meet on `L u` (`hne` of the antisymmetry node, the disjointness of the two planes) — this is `hGne` at the point `u₀`.

Why local constancy is then immediate (and where each hypothesis is used).  Let `M := {(u,q) : q ∈ L u}` (closed, by `hLclosed`) in `UnitAddCircle × ℝP³`, let `S := {G < 0}` (open, by `hGcont`) and `B := {G > 0}`.  Then

  `{u : ∀ q ∈ L u, G u q < 0} = (π (M ∖ S))ᶜ`  and  `{u : ∀ q ∈ L u, 0 < G u q} = (π (M ∖ B))ᶜ`,

where `π` is the projection to the first factor: a point of `π (M ∖ S)` is a `u` carrying some `q ∈ L u` with `¬(G u q < 0)`, and conversely.  `M ∖ S` is closed in `M`, whose second factor `ℝP³` is compact, so `π` is a closed map on it and both sets are **open**, and they are disjoint.  Now:

* if `e u₀ = 1` then `hval u₀` gives `∀ q ∈ L u₀, G u₀ q < 0`, so `u₀` lies in the first open set, on which `hval` gives `e u = 1` — done;
* if `e u₀ ≠ 1` then `¬(∀ q ∈ L u₀, G u₀ q < 0)`, so some `q ∈ L u₀` has `0 ≤ G u₀ q`, and `hGne` upgrades this to `0 < G u₀ q`; since `L u₀` is preconnected (`hLpre`) and `G u₀` is continuous and nowhere zero on it, the sign of `G u₀` is constant on `L u₀`, hence `∀ q ∈ L u₀, 0 < G u₀ q`: `u₀` lies in the second open set, on which `e u ≠ 1` (as `L u` is nonempty, `hLne`), so `e u = 0 = e u₀` — done.

(The sign-constancy step is `IsPreconnected.subset_or_subset` applied to the two disjoint open sets `{G u₀ < 0}` and `{0 < G u₀}`, which cover `L u₀` by `hGne`.)  The only "geometric" inputs are therefore `hval` (the dichotomy, already on disk) and `hGne`/`hGcont`/`hLclosed` (continuity of the data, which the concrete chart supplies together with the same non-vanishing that the antisymmetry node consumes).  Non-vacuity: the intended instance has `L u = projLine (ker φ ⊓ ker φu)` (nonempty compact preconnected by `projLine_isCompact` and `isPreconnected_projLine_inf`), `G u q = FQ q - (the swept plane's profile at q)`, and `hval` from the branch exports. -/

private lemma isOpen_setOf_forall_of_isClosed_graph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace X] [CompactSpace Y]
    (L : X → Set Y)
    (hL : IsClosed {p : X × Y | p.2 ∈ L p.1})
    (P : X × Y → Prop) (hP : IsOpen {p : X × Y | P p}) :
    IsOpen {x : X | ∀ y ∈ L x, P (x, y)} := by
  have hK : IsCompact ({p : X × Y | p.2 ∈ L p.1} ∩ {p : X × Y | P p}ᶜ) :=
    (hL.inter hP.isClosed_compl).isCompact
  have him : IsClosed (Prod.fst '' ({p : X × Y | p.2 ∈ L p.1} ∩ {p : X × Y | P p}ᶜ)) :=
    (hK.image continuous_fst).isClosed
  have heq : {x : X | ∀ y ∈ L x, P (x, y)} =
      (Prod.fst '' ({p : X × Y | p.2 ∈ L p.1} ∩ {p : X × Y | P p}ᶜ))ᶜ := by
    ext x
    constructor
    · intro hx hxmem
      obtain ⟨p, ⟨hpL, hpP⟩, hp1⟩ := hxmem
      obtain rfl : x = p.1 := hp1.symm
      exact hpP (hx p.2 hpL)
    · intro hx y hy
      by_contra hPy
      exact hx ⟨(x, y), ⟨hy, hPy⟩, rfl⟩
  rw [heq]
  exact him.isOpen_compl

theorem sideOf_localconst_of_dichotomy
    (e : UnitAddCircle → ZMod 2)
    (L : UnitAddCircle → Set (Projectivization ℝ (Eucl 3)))
    (G : UnitAddCircle → Projectivization ℝ (Eucl 3) → ℝ)
    (u₀ : UnitAddCircle)
    (hLclosed : IsClosed {p : UnitAddCircle × Projectivization ℝ (Eucl 3) | p.2 ∈ L p.1})
    (hGcont : Continuous (Function.uncurry G))
    (hLpre : ∀ u, IsPreconnected (L u))
    (hLne : ∀ u, (L u).Nonempty)
    (hGne : ∀ q ∈ L u₀, G u₀ q ≠ 0)
    (hval : ∀ u, e u = 1 ↔ ∀ q ∈ L u, G u q < 0) :
    ∀ᶠ u in 𝓝 u₀, e u = e u₀ := by
  -- `ZMod 2` has exactly two elements, so `≠ 1` means `= 0`.
  have hz : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
  have hGcont' : Continuous (fun p : UnitAddCircle × Projectivization ℝ (Eucl 3) => G p.1 p.2) :=
    hGcont
  -- The two "good" sets: the chart profile is below / above the swept plane along the whole class
  -- line.  Each is the complement of the (closed) projection of a closed set of the compact space
  -- `UnitAddCircle × ℝP³`, hence open.
  have hOpen1 : IsOpen {u : UnitAddCircle | ∀ q ∈ L u, G u q < 0} :=
    isOpen_setOf_forall_of_isClosed_graph L hLclosed (fun p => G p.1 p.2 < 0)
      (isOpen_lt hGcont' continuous_const)
  have hOpen2 : IsOpen {u : UnitAddCircle | ∀ q ∈ L u, 0 < G u q} :=
    isOpen_setOf_forall_of_isClosed_graph L hLclosed (fun p => 0 < G p.1 p.2)
      (isOpen_lt continuous_const hGcont')
  by_cases h1 : e u₀ = 1
  · -- The side at `u₀` is `1`: the whole class line is below the swept plane; on that open set
    -- the dichotomy gives the side `1` everywhere.
    have hu₀A : u₀ ∈ {u : UnitAddCircle | ∀ q ∈ L u, G u q < 0} := (hval u₀).mp h1
    refine Filter.eventually_of_mem (hOpen1.mem_nhds hu₀A) ?_
    intro u hu
    rw [(hval u).mpr hu, h1]
  · -- The side at `u₀` is not `1`: some point of the class line is not below the swept plane,
    -- and since the two profiles do not meet there, it is strictly above; preconnectedness of the
    -- class line upgrades this to "strictly above everywhere".
    have hu₀B : u₀ ∈ {u : UnitAddCircle | ∀ q ∈ L u, 0 < G u q} := by
      have hnot : ¬ (∀ q ∈ L u₀, G u₀ q < 0) := fun h => h1 ((hval u₀).mpr h)
      obtain ⟨q₀, hq₀L, hq₀nlt⟩ : ∃ q ∈ L u₀, ¬ G u₀ q < 0 := by
        by_contra hc
        exact hnot (fun q hq => by_contra (fun h => hc ⟨q, hq, h⟩))
      have hq₀pos : 0 < G u₀ q₀ :=
        lt_of_le_of_ne (not_lt.mp hq₀nlt) (Ne.symm (hGne q₀ hq₀L))
      have hcont : Continuous (fun q : Projectivization ℝ (Eucl 3) => G u₀ q) :=
        hGcont'.comp (continuous_const.prodMk continuous_id)
      have hcover : L u₀ ⊆ {q : Projectivization ℝ (Eucl 3) | G u₀ q < 0} ∪ {q | 0 < G u₀ q} := by
        intro q hq
        rcases lt_trichotomy (G u₀ q) 0 with h | h | h
        · exact Or.inl h
        · exact absurd h (hGne q hq)
        · exact Or.inr h
      have hdisj : Disjoint {q : Projectivization ℝ (Eucl 3) | G u₀ q < 0} {q | 0 < G u₀ q} := by
        rw [Set.disjoint_left]
        intro q hA hB
        have hA' : G u₀ q < 0 := hA
        have hB' : 0 < G u₀ q := hB
        linarith
      rcases (hLpre u₀).subset_or_subset (isOpen_lt hcont continuous_const)
        (isOpen_lt continuous_const hcont) hdisj hcover with h | h
      · exact absurd (h hq₀L) (not_lt.mpr hq₀pos.le)
      · exact h
    refine Filter.eventually_of_mem (hOpen2.mem_nhds hu₀B) ?_
    intro u hu
    have hne1 : e u ≠ 1 := by
      intro hEu
      obtain ⟨q, hq⟩ := hLne u
      exact absurd ((hval u).mp hEu q hq) (not_lt.mpr (hu q hq).le)
    rw [hz (e u) hne1, hz (e u₀) h1]


end Work.Drive
