import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Main
import Submission.Work.BoxShrink.PinchOff.IB.Separator
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.BoxShrink.PinchOff.exists_unbounded_component_compl_of_preconnected_compact
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top

/-!
# The complement of a set with compact preimage in the parameter plane spans everything

Let `P` be a parametrised torus, `E ⊆ ℝ³` a set of points of the surface, and let

  `Z = Xtilde P E = planePsi P ⁻¹' E ⊆ ℂ`

be its preimage in the parameter plane.  **If `Z` is closed and every preconnected subset of `Z`
is compact, and `Z ≠ ℂ`, then the region `P.carrier \ E` realises the whole of `H₁(T²;ℚ):**

  `WindingSpan P (P.carrier \ E) = ⊤`.

The hypothesis "every preconnected subset of `Z` is compact" is very strong: it forces `Z` to be
*totally disconnected* (if `Z` contained a nondegenerate continuum `C`, then `C` has a non-cut
point `p`, and `C \ {p}` would be a preconnected non-compact subset of `Z`).  Consequently `Zᶜ`
has an **unbounded** component `U` (`Zᶜ` is unbounded, and a compact totally disconnected set does
not separate the plane); this is the delegated input
`exists_unbounded_component_compl_of_preconnected_compact`.

By the uniqueness of the unbounded complementary domain of a closed set with compact components
(`unbounded_component_unique`, `IB/Separator.lean`) the component `U` is **invariant under the
period lattice**, so it contains paths from a point `z₀` to `z₀ + periodPt 1 0` and to
`z₀ + periodPt 0 1`.  Such paths produce closed curves of the torus of winding vectors `(1,0)` and
`(0,1)` inside `P.carrier \ E` (`exists_closedCurve_of_path`, `IB/Span.lean`), which are the two
generators of `ℚ² = H₁(T²;ℚ)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The parameter-plane preimage of `carrier \ E` is the complement of the preimage of `E`.** -/
theorem Xtilde_sdiff_carrier (P : Work.CoreTopology.ParamTorus) (E : Set R3) :
    Xtilde P (P.carrier \ E) = (Xtilde P E)ᶜ := by
  ext z
  simp only [mem_Xtilde, mem_sdiff, mem_compl_iff]
  exact ⟨fun h => h.2, fun h => ⟨planePsi_mem_carrier P z, h⟩⟩

/-- **The complement of a closed set whose preconnected subsets are single points has an unbounded
component.**

This is the "last mile" of the topological input: given that `Z` is totally disconnected (in the
sense that every preconnected subset is a subsingleton), the complement `Zᶜ` has an unbounded
component.  Indeed `Zᶜ` is unbounded (otherwise `Z` would contain the exterior of a ball, which is
preconnected and not a subsingleton), and if a component of `Zᶜ` were bounded it would have to be
separated from the rest by a compact preconnected subset of `Z` (`separator_of_closed`), which
would then be a single point: but a point does not separate the plane. -/
theorem exists_unbounded_component_compl_of_preconnected_subsingleton {Z : Set ℂ} (hZ : IsClosed Z)
    (hsub : ∀ S : Set ℂ, S ⊆ Z → IsPreconnected S → S.Subsingleton) (hne : Zᶜ.Nonempty) :
    ∃ z ∈ Zᶜ, ∀ R : ℝ, ∃ w ∈ connectedComponentIn Zᶜ z, R ≤ ‖w‖ := by
  classical
  -- Step 1: `Zᶜ` is unbounded.
  have hunb : ∀ R : ℝ, ∃ w ∈ Zᶜ, R ≤ ‖w‖ := by
    intro R
    by_contra h
    push_neg at h
    set r : ℝ := max R 0 + 1 with hr
    have hr0 : 0 ≤ r := by positivity
    have hRr : R < r := by
      have h1 : R ≤ max R 0 := le_max_left R 0
      rw [hr]; linarith
    have hsub' : {z : ℂ | r < ‖z‖} ⊆ Z := by
      intro z hz
      by_contra hzZ
      have h2 : ‖z‖ < R := h z hzZ
      simp only [Set.mem_ofPred_eq] at hz
      linarith
    have hpre : IsPreconnected {z : ℂ | r < ‖z‖} :=
      Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl r hr0
    have hss := hsub _ hsub' hpre
    have h1mem : ((r + 1 : ℝ) : ℂ) ∈ {z : ℂ | r < ‖z‖} := by
      simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ r + 1)]
      linarith
    have h2mem : ((r + 2 : ℝ) : ℂ) ∈ {z : ℂ | r < ‖z‖} := by
      simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ r + 2)]
      linarith
    have heq : ((r + 1 : ℝ) : ℂ) = ((r + 2 : ℝ) : ℂ) := hss h1mem h2mem
    have : r + 1 = r + 2 := Complex.ofReal_injective heq
    linarith
  -- Step 2: either all of `Zᶜ` lies in the component of a point, or a separation exists.
  obtain ⟨x, hx⟩ := hne
  by_cases hcase : ∃ y ∈ Zᶜ, y ∉ connectedComponentIn Zᶜ x
  · exfalso
    obtain ⟨y, hy, hyc⟩ := hcase
    obtain ⟨C, hCZ, _hCcl, hCpre, hxC, hyC, hCsep⟩ :=
      Work.BoxShrink.PinchOff.separator_of_closed hZ hx hy hyc
    have hsing : C.Subsingleton := hsub C hCZ hCpre
    rcases C.eq_empty_or_nonempty with hC0 | ⟨c, hcC⟩
    · -- `C = ∅` cannot separate
      rw [hC0, compl_empty] at hCsep
      exact hCsep ((isPreconnected_univ.subset_connectedComponentIn (Set.mem_univ x)
        (Set.subset_univ _)) (Set.mem_univ y))
    · -- `C = {c}`: the complement is the punctured plane, which is preconnected
      have hCsingle : C = {c} := by
        refine Subset.antisymm ?_ ?_
        · intro z hz
          have hzc : z = c := hsing hz hcC
          simp [hzc]
        · intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hcC
      have hxcli : x ∈ Cᶜ := fun h => hxC h
      have hcompl : IsPreconnected (Cᶜ : Set ℂ) := by
        rw [hCsingle]
        exact (isConnected_compl_singleton_of_one_lt_rank (by
          rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
          norm_num) c).isPreconnected
      exact hCsep ((hcompl.subset_connectedComponentIn hxcli (Subset.rfl)) hyC)
  · -- otherwise the component of `x` is all of `Zᶜ`
    push_neg at hcase
    exact ⟨x, hx, fun R => by
      obtain ⟨w, hw, hR⟩ := hunb R
      exact ⟨w, hcase w hw, hR⟩⟩

theorem windingSpan_sdiff_eq_top_of_compact_preimage (P : Work.CoreTopology.ParamTorus)
    (E : Set LeanEval.KnotTheory.PardonDistortion.R3)
    (hclosed : IsClosed (Work.BoxShrink.PinchOff.Xtilde P E))
    (hcomp : ∀ C : Set ℂ, IsPreconnected C → C ⊆ Work.BoxShrink.PinchOff.Xtilde P E → IsCompact C)
    (hne : (Work.BoxShrink.PinchOff.Xtilde P E : Set ℂ)ᶜ.Nonempty) :
    Work.SurgeryInvariance.WindingSpan P (P.carrier \ E) = ⊤ := by
  classical
  set Z : Set ℂ := Xtilde P E with hZdef
  set X : Set R3 := P.carrier \ E with hXdef
  -- the parameter-plane description of the region
  have hXt_eq : Xtilde P X = Zᶜ := by
    rw [hXdef, hZdef]
    exact Xtilde_sdiff_carrier P E
  have hZc_open : IsOpen (Zᶜ) := hclosed.isOpen_compl
  -- every component of `Z` is compact
  have hcomp_comp : ∀ z ∈ Z, IsCompact (connectedComponentIn Z z) :=
    fun z _ => hcomp _ isPreconnected_connectedComponentIn (connectedComponentIn_subset Z z)
  -- the unbounded component of the complement
  obtain ⟨z₀, hz₀Zc, hz₀unb⟩ :=
    exists_unbounded_component_compl_of_preconnected_compact hclosed
      (fun C hCZ hCpre => hcomp C hCpre hCZ) hne
  set U : Set ℂ := connectedComponentIn Zᶜ z₀ with hUdef
  have hUopen : IsOpen U := hZc_open.connectedComponentIn
  have hUpre : IsPreconnected U := isPreconnected_connectedComponentIn
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀Zc
  have hUsub : U ⊆ Zᶜ := connectedComponentIn_subset Zᶜ z₀
  -- `U` is invariant under the period lattice
  have hZcInv : ∀ z w : ℂ, w ∈ periodLattice → (z + w ∈ Zᶜ ↔ z ∈ Zᶜ) := by
    intro z w hw
    rw [mem_compl_iff, mem_compl_iff, hZdef]
    exact not_iff_not.mpr (Xtilde_add_periodLattice P E z w hw)
  have hUinv : ∀ w ∈ periodLattice, (fun y => y + w) '' U = U := by
    intro w hw
    have hzwZc : z₀ + w ∈ Zᶜ := (hZcInv z₀ w hw).mpr hz₀Zc
    have hcompw : connectedComponentIn Zᶜ (z₀ + w) = (fun y => y + w) '' U :=
      connectedComponentIn_add hZcInv hw hz₀Zc
    have hb2 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Zᶜ (z₀ + w), R ≤ ‖y‖ := by
      intro R
      obtain ⟨y, hy, hR⟩ := hz₀unb (R + ‖w‖)
      refine ⟨y + w, ?_, ?_⟩
      · rw [hcompw]
        exact ⟨y, hy, rfl⟩
      · have h1 : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
          calc ‖y‖ = ‖(y + w) - w‖ := by ring_nf
            _ ≤ ‖y + w‖ + ‖w‖ := norm_sub_le _ _
        linarith
    have heq : connectedComponentIn Zᶜ z₀ = connectedComponentIn Zᶜ (z₀ + w) :=
      unbounded_component_unique hclosed hcomp_comp hz₀Zc hzwZc hz₀unb hb2
    rw [hcompw] at heq
    exact heq.symm
  -- `U` is path connected
  have hUpc : ∀ a ∈ U, ∀ b ∈ U, JoinedIn U a b := by
    haveI : LocallyPathConnectedSpace ↥U := hUopen.locallyPathConnectedSpace
    haveI : PreconnectedSpace ↥U :=
      isPreconnected_iff_preconnectedSpace.mp hUpre
    intro a ha b hb
    rw [joinedIn_iff_joined ha hb, ← connectedComponent_eq_iff_joined,
      PreconnectedSpace.connectedComponent_eq_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  -- the loops of winding `(a, b)`
  have hloop : ∀ (a b : ℤ), ∃ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t, γ.γ t ∈ X) ∧ Work.SurgeryInvariance.windingOf P γ = (a, b) := by
    intro a b
    have hνmem : periodPt a b ∈ periodLattice := ⟨(a, b), rfl⟩
    have hmem : z₀ + periodPt a b ∈ U := by
      have h := hUinv (periodPt a b) hνmem
      rw [← h]
      exact ⟨z₀, hz₀U, rfl⟩
    obtain ⟨p, hp⟩ := hUpc z₀ hz₀U (z₀ + periodPt a b) hmem
    set c : ℝ → ℂ := fun t => p.extend (t / (2 * Real.pi)) with hcdef
    have hc : c 0 = z₀ := by
      change p.extend ((0 : ℝ) / (2 * Real.pi)) = z₀
      rw [zero_div]
      exact Path.extend_zero p
    have h2 : c (2 * Real.pi) = z₀ + periodPt a b := by
      change p.extend ((2 * Real.pi) / (2 * Real.pi)) = z₀ + periodPt a b
      rw [show (2 * Real.pi) / (2 * Real.pi) = 1 by field_simp, Path.extend_one]
    have hcmem : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), c t ∈ Xtilde P X := by
      intro t ht
      have ht1 : t / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg ht.1 (by positivity)
        · rw [div_le_one (by positivity)]
          exact ht.2
      change p.extend (t / (2 * Real.pi)) ∈ Xtilde P X
      rw [Path.extend_apply p ht1, hXt_eq]
      exact hUsub (hp ⟨t / (2 * Real.pi), ht1⟩)
    exact exists_closedCurve_of_path c
      (p.extend.continuous.comp (by fun_prop)) hc h2 hcmem
  -- the two generators of `ℚ²`
  have h1mem : (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P X := by
    obtain ⟨γ, hγ, hw⟩ := hloop 1 0
    refine Submodule.subset_span ⟨γ, hγ, ?_⟩
    rw [hw]
    norm_num
  have h2mem : (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P X := by
    obtain ⟨γ, hγ, hw⟩ := hloop 0 1
    refine Submodule.subset_span ⟨γ, hγ, ?_⟩
    rw [hw]
    norm_num
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = v.1 • (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) + v.2 • (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1mem) (Submodule.smul_mem _ _ h2mem)

end

end Work.BoxShrink.PinchOff
