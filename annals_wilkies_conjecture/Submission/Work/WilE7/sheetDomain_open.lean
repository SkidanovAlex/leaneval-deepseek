import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.stratGraph
import Submission.Work.WilE7.ambientLocality

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Two elementary tools about `Fin.append`

`Fin.append x v` glues a `p`-tuple and a `q`-tuple into a `(p+q)`-tuple; we need that the first
projection inverts this gluing, and that the gluing depends continuously on its first argument as
soon as the second one does. -/

/-- `projFirst p q (Fin.append x v) = x`. -/
theorem projFirst_append {p q : ℕ} (x : Fin p → ℝ) (v : Fin q → ℝ) :
    WilkiesDesign.E.projFirst p q (Fin.append x v) = x := by
  funext i
  simp [WilkiesDesign.E.projFirst]

/-- If `y` is continuous on `s`, so is `x ↦ Fin.append x (y x)`. -/
theorem continuousOn_append {p q : ℕ} {s : Set (Fin p → ℝ)}
    {y : (Fin p → ℝ) → (Fin q → ℝ)} (hy : ContinuousOn y s) :
    ContinuousOn (fun x : Fin p → ℝ => Fin.append x (y x)) s := by
  rw [continuousOn_pi]
  intro i
  refine Fin.addCases (motive := fun i =>
    ContinuousOn (fun x : Fin p → ℝ => Fin.append x (y x) i) s) (fun i' => ?_) (fun j' => ?_) i
  · have h : (fun x : Fin p → ℝ => Fin.append x (y x) (Fin.castAdd q i')) = fun x => x i' := by
      funext x
      simp
    rw [h]
    exact (continuous_apply i').continuousOn
  · have h : (fun x : Fin p → ℝ => Fin.append x (y x) (Fin.natAdd p j')) = fun x => y x j' := by
      funext x
      simp
    rw [h]
    exact (continuousOn_pi.mp hy) j'

/-! ## The projection of a sheet is open in the chamber

Let `A = S.X.set ∩ π⁻¹'C` be the *sheet domain* — the points of the `Good` stratum `S` lying over
the chamber `C` — and let `Z` be the connected component of `z₀` in `A`.  We show that the
projection `π '' Z` is open in the subspace `C`; local connectedness of `C` (`hlocconn`) is the
only topological input besides the implicit function theorem.

At `z ∈ Z` with `π z = c` the graph lemma `stratGraph` (for `S.j = q` the equations of `S` have an
invertible fibrewise Jacobian, so the fibres of `S` are locally graphs over `ℝ^p`) gives an open
`U₁ ∋ c` and a continuous `y : U₁ → ℝ^q` with `y c = projSnd p q z` whose graph lies in the common
zero set of the equations `S.h`.  Locality of `S.X.set` at `z` (`hloc`, the "no foreign zeros near
`z`" property of the stratum) provides a neighbourhood `N` of `z` such that a zero of `S.h` inside
`N` belongs to `S.X.set`.  Continuity gives an open `U₂ ⊆ U₁` with `x ∈ U₂ → Fin.append x (y x) ∈ N`,
so the whole graph over `U₂ ∩ C` lies in `A`.  Now `hlocconn` supplies an open preconnected
`V ∋ c`, `V ⊆ U₂`, with `V ∩ C` preconnected; its image under the continuous graph map is a
preconnected subset of `A` containing both `z` (the image of `c`) and the point over every
`x ∈ V ∩ C`, so by maximality of the component it lies in `Z`, and hence
`x = π (Fin.append x (y x)) ∈ π '' Z`.  Thus `V` witnesses relative openness at `c`. -/

theorem sheetDomain_open
    {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (C : Set (Fin p → ℝ))
    (hloc : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p q z ∈ C →
      ∀ᶠ z' in nhds z,
        (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set)
    (hlocconn : ∀ c ∈ C, ∀ W : Set (Fin p → ℝ), IsOpen W → c ∈ W →
      ∃ V : Set (Fin p → ℝ), IsOpen V ∧ c ∈ V ∧ V ⊆ W ∧ IsPreconnected (V ∩ C))
    (z₀ : Fin (p + q) → ℝ) (hz₀ : z₀ ∈ S.X.set) (hz₀C : WilkiesDesign.E.projFirst p q z₀ ∈ C) :
    ∀ c ∈ Set.image (WilkiesDesign.E.projFirst p q)
        (connectedComponentIn (S.X.set ∩ {w : Fin (p + q) → ℝ |
          WilkiesDesign.E.projFirst p q w ∈ C}) z₀),
      ∃ U : Set (Fin p → ℝ), IsOpen U ∧ c ∈ U ∧ U ∩ C ⊆
        Set.image (WilkiesDesign.E.projFirst p q)
          (connectedComponentIn (S.X.set ∩ {w : Fin (p + q) → ℝ |
            WilkiesDesign.E.projFirst p q w ∈ C}) z₀) := by
  classical
  intro c hc
  -- the sheet domain `A` and the sheet `Z`
  set A : Set (Fin (p + q) → ℝ) :=
    S.X.set ∩ {w : Fin (p + q) → ℝ | WilkiesDesign.E.projFirst p q w ∈ C} with hA
  set Z : Set (Fin (p + q) → ℝ) := connectedComponentIn A z₀ with hZ
  have hcZ : c ∈ Set.image (WilkiesDesign.E.projFirst p q) Z := by
    rw [hZ, hA]
    exact hc
  rw [Set.mem_image] at hcZ
  obtain ⟨z, hzZ, hzc⟩ := hcZ
  -- `z` lies in the sheet domain
  have hzA : z ∈ A := connectedComponentIn_subset A z₀ hzZ
  have hzS : z ∈ S.X.set := by
    have h := hzA
    rw [hA] at h
    exact h.1
  have hzC : WilkiesDesign.E.projFirst p q z ∈ C := by
    have h := hzA
    rw [hA] at h
    exact h.2
  have hcC : c ∈ C := hzc ▸ hzC
  -- locality of `S.X.set` at `z`, as an open neighbourhood `N` of `z`
  obtain ⟨N, hNsub, hNopen, hzN⟩ := mem_nhds_iff.mp (hloc z hzS hzC)
  have hNprop : ∀ z' ∈ N, (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) →
      z' ∈ S.X.set := fun z' hz' => hNsub hz'
  -- the local graph of the stratum over the base at `c`
  obtain ⟨U₁, y, W, hU₁o, hcU₁, _hWo, _hzW, hyc, hycont, hysol, _hyuniq⟩ :=
    stratGraph S hGood hj z hzS
  -- the graph map, continuous on `U₁`
  have hgraph : ContinuousOn (fun x : Fin p → ℝ => Fin.append x (y x)) U₁ :=
    continuousOn_append hycont
  -- a smaller open `U₂ ∋ c` on which the graph lies inside `N`
  have hU₂open : IsOpen (U₁ ∩ (fun x : Fin p → ℝ => Fin.append x (y x)) ⁻¹' N) :=
    hgraph.isOpen_inter_preimage hU₁o hNopen
  have hcU₂ : c ∈ U₁ ∩ (fun x : Fin p → ℝ => Fin.append x (y x)) ⁻¹' N := by
    refine ⟨by rw [← hzc]; exact hcU₁, ?_⟩
    show Fin.append c (y c) ∈ N
    rw [← hzc]
    show Fin.append (WilkiesDesign.E.projFirst p q z) (y (WilkiesDesign.E.projFirst p q z)) ∈ N
    rw [hyc, append_proj z]
    exact hzN
  -- local connectedness of the chamber
  obtain ⟨V, hVo, hcV, hVsub, hVpre⟩ := hlocconn c hcC _ hU₂open hcU₂
  refine ⟨V, hVo, hcV, ?_⟩
  -- the graph over `V ∩ C` is a preconnected subset of `A` containing `z`
  have hVU₁ : V ⊆ U₁ := fun x hx => (hVsub hx).1
  have hgraphV : ContinuousOn (fun x : Fin p → ℝ => Fin.append x (y x)) (V ∩ C) :=
    (hgraph.mono hVU₁).mono Set.inter_subset_left
  have hpre : IsPreconnected ((fun x : Fin p → ℝ => Fin.append x (y x)) '' (V ∩ C)) :=
    hVpre.image _ hgraphV
  have hsubA : (fun x : Fin p → ℝ => Fin.append x (y x)) '' (V ∩ C) ⊆ A := by
    rintro w ⟨u, ⟨huV, huC⟩, rfl⟩
    have huU₁ : u ∈ U₁ := hVU₁ huV
    have huN : Fin.append u (y u) ∈ N := (hVsub huV).2
    have hzero : ∀ a : Fin S.j,
        WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append u (y u)) = 0 := hysol u huU₁
    have hSmem : Fin.append u (y u) ∈ S.X.set := hNprop _ huN hzero
    rw [hA]
    refine ⟨hSmem, ?_⟩
    show WilkiesDesign.E.projFirst p q (Fin.append u (y u)) ∈ C
    rw [projFirst_append u (y u)]
    exact huC
  have hzgraph : z ∈ (fun x : Fin p → ℝ => Fin.append x (y x)) '' (V ∩ C) := by
    refine ⟨c, ⟨hcV, hcC⟩, ?_⟩
    rw [← hzc]
    show Fin.append (WilkiesDesign.E.projFirst p q z) (y (WilkiesDesign.E.projFirst p q z)) = z
    rw [hyc]
    exact append_proj z
  have hsubZ : (fun x : Fin p → ℝ => Fin.append x (y x)) '' (V ∩ C) ⊆ Z := by
    have hcomp : (fun x : Fin p → ℝ => Fin.append x (y x)) '' (V ∩ C) ⊆
        connectedComponentIn A z := hpre.subset_connectedComponentIn hzgraph hsubA
    have hzZ' : z ∈ connectedComponentIn A z₀ := by
      have h := hzZ
      rw [hZ] at h
      exact h
    rw [hZ, connectedComponentIn_eq hzZ']
    exact hcomp
  -- conclusion
  rintro x ⟨hxV, hxC⟩
  exact ⟨Fin.append x (y x), hsubZ ⟨x, ⟨hxV, hxC⟩, rfl⟩, projFirst_append x (y x)⟩

end Work.WilE7
