import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.tower
import Submission.Work.BasinSC.Tower.tower_isOpen
import Submission.Work.BasinSC.Tower.tower_step

/-!
# Assembly of Lemma 5.2 (the immediate parabolic basin is simply connected)

Given the two Riemann–Hurwitz-lite steps
`simplyConnected_of_proper_holomorphic_no_crit` (no critical point) and
`simplyConnected_of_proper_holomorphic_one_crit` (one critical point), the connected components of
the tower levels `V n = {z | f₀^[n] z ∈ Ωp} ∩ B` are simply connected by induction; since every loop
of `B` lies in some `V n` (its image is compact and the tower exhausts `B`), every loop in `B` is
null-homotopic, so `Hom(π₁ B, ℝ) = 0` and `Work.Spine.Main` concludes.
-/

open Set Metric Filter Topology MandelDim
open scoped Topology

namespace Work.BasinSC

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- **The structural data of one step of the tower** (proved in `BasinSC/Tower/tower_step`). -/
def TowerStepData (f₀ : ℂ → ℂ) (B Ωp : Set ℂ) (n : ℕ) (x : ℂ) : Prop :=
  IsOpen (connectedComponentIn (tower f₀ B Ωp (n + 1)) x) ∧
  IsConnected (connectedComponentIn (tower f₀ B Ωp (n + 1)) x) ∧
  DifferentiableOn ℂ f₀ (connectedComponentIn (tower f₀ B Ωp (n + 1)) x) ∧
  Set.MapsTo f₀ (connectedComponentIn (tower f₀ B Ωp (n + 1)) x)
    (connectedComponentIn (tower f₀ B Ωp n) (f₀ x)) ∧
  (connectedComponentIn (tower f₀ B Ωp n) (f₀ x)) ⊆
    f₀ '' (connectedComponentIn (tower f₀ B Ωp (n + 1)) x) ∧
  (∀ K ⊆ connectedComponentIn (tower f₀ B Ωp n) (f₀ x), IsCompact K →
    IsCompact (connectedComponentIn (tower f₀ B Ωp (n + 1)) x ∩ f₀ ⁻¹' K))

/-- **The simply connectedness induction.**  If each step of the tower is a proper holomorphic map
with at most one critical point (the disjunction is the two Riemann–Hurwitz-lite steps), then every
component of every level of the tower is simply connected. -/
theorem components_simplyConnected (hF0 : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀)
    (hstep : ∀ n x, x ∈ tower f₀ B d.Ωp (n + 1) → TowerStepData f₀ B d.Ωp n x)
    (hstepsc : ∀ {V V' : Set ℂ}, IsOpen V → V.Nonempty → SimplyConnectedSpace ↥V →
      V ≠ Set.univ → IsOpen V' → IsConnected V' → ∀ {p : ℂ → ℂ}, DifferentiableOn ℂ p V' →
      Set.MapsTo p V' V → (V ⊆ p '' V') →
      (∀ K ⊆ V, IsCompact K → IsCompact (V' ∩ p ⁻¹' K)) →
      ((∀ z ∈ V', deriv p z ≠ 0) ∨
        (∃ c₀ ∈ V', deriv p c₀ = 0 ∧ ∀ z ∈ V', deriv p z = 0 → z = c₀)) →
      SimplyConnectedSpace ↥V') :
    ∀ n x, x ∈ tower f₀ B d.Ωp n →
      SimplyConnectedSpace ↥(connectedComponentIn (tower f₀ B d.Ωp n) x) := by
  obtain ⟨hgerm, hB, hcB, hcd, huniq⟩ := hF0
  have hzero : (0 : ℂ) ∉ ParabolicBasin f₀ D₀ :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgerm
  have hBbasin : B ⊆ ParabolicBasin f₀ D₀ := hB.2.2.1
  intro n
  induction n with
  | zero =>
      intro x hx
      have hxΩ : x ∈ d.Ωp := by
        have h := hx; rw [tower_zero (d := d) ⟨hgerm, hB, hcB, hcd, huniq⟩] at h; exact h
      have heq : connectedComponentIn (tower f₀ B d.Ωp 0) x = d.Ωp := by
        rw [tower_zero (d := d) ⟨hgerm, hB, hcB, hcd, huniq⟩]
        exact Set.Subset.antisymm (connectedComponentIn_subset _ _)
          (d.Ωp_conn.isPreconnected.subset_connectedComponentIn hxΩ subset_rfl)
      rw [heq]
      exact d.Ωp_sc
  | succ n ih =>
      intro x hx
      obtain ⟨hC'o, hC'c, hC'd, hmaps, hsurj, hprop⟩ := hstep n x hx
      set C' := connectedComponentIn (tower f₀ B d.Ωp (n + 1)) x with hC'def
      set C := connectedComponentIn (tower f₀ B d.Ωp n) (f₀ x) with hCdef
      have hxC' : x ∈ C' := mem_connectedComponentIn hx
      have hfx : f₀ x ∈ tower f₀ B d.Ωp n :=
        connectedComponentIn_subset _ _ (hmaps hxC')
      have hfxC : f₀ x ∈ C := mem_connectedComponentIn hfx
      have hCsc : SimplyConnectedSpace ↥C := ih (f₀ x) hfx
      have hCne : C.Nonempty := ⟨f₀ x, hfxC⟩
      have hCopen : IsOpen C := (Work.BasinSC.Tower.tower_isOpen (d := d) ⟨hgerm, hB, hcB, hcd, huniq⟩ n).connectedComponentIn
      have hCnotuniv : C ≠ Set.univ := by
        intro h
        have h0 : (0 : ℂ) ∈ C := h ▸ Set.mem_univ 0
        exact hzero (hBbasin (tower_subset_B (d := d) n
          (connectedComponentIn_subset _ _ h0)))
      refine hstepsc hCopen hCne hCsc hCnotuniv hC'o hC'c hC'd hmaps hsurj hprop ?_
      by_cases hcrit : ∃ z ∈ C', deriv f₀ z = 0
      · obtain ⟨z, hzC', hzd⟩ := hcrit
        have hzB : z ∈ B := tower_subset_B (d := d) (n + 1)
          (connectedComponentIn_subset _ _ hzC')
        refine Or.inr ⟨z, hzC', hzd, fun w hw hwd => ?_⟩
        have hwB : w ∈ B := tower_subset_B (d := d) (n + 1)
          (connectedComponentIn_subset _ _ hw)
        exact (huniq w hwB hwd).trans (huniq z hzB hzd).symm
      · exact Or.inl fun z hz hd => hcrit ⟨z, hz, hd⟩

/-- **A cover of the basin by the tower levels.**  Any loop in the basin lies in a single level
(the levels are open and increasing, and the image of the loop is compact). -/
lemma exists_level_of_path (hF0 : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀) {x : ↥B}
    (γ : Path x x) : ∃ N : ℕ, ∀ t : unitInterval, ((γ t : ↥B) : ℂ) ∈ tower f₀ B d.Ωp N := by
  have hcover : (Set.univ : Set unitInterval) ⊆
      ⋃ n, (fun t : unitInterval => ((γ t : ↥B) : ℂ)) ⁻¹' tower f₀ B d.Ωp n := by
    intro t _
    have ht : ((γ t : ↥B) : ℂ) ∈ B := (γ t).2
    have hex : ∃ n, ((γ t : ↥B) : ℂ) ∈ tower f₀ B d.Ωp n := by
      have h : ((γ t : ↥B) : ℂ) ∈ ⋃ n, tower f₀ B d.Ωp n := by
        rw [tower_exhaust (d := d) hF0]; exact ht
      simpa [Set.mem_iUnion] using h
    exact Set.mem_iUnion.mpr hex
  have hopen : ∀ n, IsOpen ((fun t : unitInterval => ((γ t : ↥B) : ℂ)) ⁻¹'
      tower f₀ B d.Ωp n) := fun n =>
    (Work.BasinSC.Tower.tower_isOpen (d := d) hF0 n).preimage (continuous_subtype_val.comp γ.continuous)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨s.sup id, fun t => ?_⟩
  have ht : t ∈ ⋃ n ∈ s, (fun t : unitInterval => ((γ t : ↥B) : ℂ)) ⁻¹' tower f₀ B d.Ωp n :=
    hs (Set.mem_univ t)
  rw [Set.mem_iUnion] at ht
  obtain ⟨n, ht⟩ := ht
  rw [Set.mem_iUnion] at ht
  obtain ⟨hns, hnt⟩ := ht
  exact tower_mono_le (d := d) (Finset.le_sup hns) hnt

/-- **Every loop in the basin is null-homotopic**, since it lies in a simply connected component of
some tower level. -/
theorem path_homotopic_refl (hF0 : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀)
    (hcomp : ∀ n x, x ∈ tower f₀ B d.Ωp n →
      SimplyConnectedSpace ↥(connectedComponentIn (tower f₀ B d.Ωp n) x))
    {x : ↥B} (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  obtain ⟨N, hN⟩ := exists_level_of_path hF0 d γ
  set V := tower f₀ B d.Ωp N with hVdef
  have hxV : ((x : ↥B) : ℂ) ∈ V := by rw [← γ.source]; exact hN 0
  set C : Set ℂ := connectedComponentIn V ((x : ↥B) : ℂ) with hCdef
  have hCV : C ⊆ V := connectedComponentIn_subset _ _
  have hCB : C ⊆ B := fun z hz => tower_subset_B (d := d) N (hCV hz)
  have hCsc : SimplyConnectedSpace ↥C := hcomp N _ hxV
  have hxC : ((x : ↥B) : ℂ) ∈ C := mem_connectedComponentIn hxV
  -- the range of the loop lies in `C`
  have hpre : IsPreconnected (Subtype.val '' (Set.range γ)) :=
    (isPreconnected_range γ.continuous).image _ continuous_subtype_val.continuousOn
  have hsub : Subtype.val '' (Set.range γ) ⊆ V := by
    rintro z ⟨b, ⟨t, rfl⟩, rfl⟩
    exact hN t
  have hxrange : ((x : ↥B) : ℂ) ∈ Subtype.val '' (Set.range γ) :=
    ⟨x, ⟨0, γ.source⟩, rfl⟩
  have hrange : ∀ t : unitInterval, ((γ t : ↥B) : ℂ) ∈ C := fun t =>
    IsPreconnected.subset_connectedComponentIn hpre hxrange hsub ⟨γ t, ⟨t, rfl⟩, rfl⟩
  -- regard the loop as a loop in `C`; it is null-homotopic there, hence in `B`
  obtain ⟨F, hFmem⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hCsc).2
    (((x : ↥B) : ℂ))
    { toContinuousMap :=
        ⟨fun t => ((γ t : ↥B) : ℂ), continuous_subtype_val.comp γ.continuous⟩
      source' := by simpa using congrArg Subtype.val γ.source
      target' := by simpa using congrArg Subtype.val γ.target }
    hrange
  refine ⟨{ toFun := fun t => ⟨F t, hCB (hFmem t)⟩
            map_zero_left := fun y => Subtype.ext (F.map_zero_left y)
            map_one_left := fun y => Subtype.ext (F.map_one_left y)
            prop' := by simp }⟩

/-- **Every homomorphism `π₁ B → ℝ` vanishes.** -/
theorem subsingleton_hom (hF0 : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀)
    (hcomp : ∀ n x, x ∈ tower f₀ B d.Ωp n →
      SimplyConnectedSpace ↥(connectedComponentIn (tower f₀ B d.Ωp n) x))
    (x₀ : ↥B) : Subsingleton (Additive (FundamentalGroup ↥B x₀) →+ ℝ) := by
  have hzero : ∀ φ : Additive (FundamentalGroup ↥B x₀) →+ ℝ, φ = 0 := by
    intro φ
    ext g
    induction g using Quotient.inductionOn with
    | _ γ =>
        have h1 : (Quotient.mk (Path.Homotopic.setoid x₀ x₀) γ : FundamentalGroup ↥B x₀) =
            (1 : FundamentalGroup ↥B x₀) :=
          Quotient.sound (path_homotopic_refl hF0 d hcomp γ)
        have h2 : (⟦γ⟧ : FundamentalGroup ↥B x₀) =
            Quotient.mk (Path.Homotopic.setoid x₀ x₀) γ := rfl
        rw [h2, h1]
        exact φ.map_zero
  exact ⟨fun φ ψ => by rw [hzero φ, hzero ψ]⟩

end

/-- **Lemma 5.2, conditional on the one-critical-point step.** -/
theorem basin_sc_of_steps
    (honeCrit : ∀ {V V' : Set ℂ}, IsOpen V → V.Nonempty → SimplyConnectedSpace ↥V →
      V ≠ Set.univ → IsOpen V' → IsConnected V' → ∀ {p : ℂ → ℂ}, DifferentiableOn ℂ p V' →
      Set.MapsTo p V' V → (V ⊆ p '' V') →
      (∀ K ⊆ V, IsCompact K → IsCompact (V' ∩ p ⁻¹' K)) →
      ∀ {c₀ : ℂ}, c₀ ∈ V' → deriv p c₀ = 0 → (∀ z ∈ V', deriv p z = 0 → z = c₀) →
      SimplyConnectedSpace ↥V') :
    BasinSCStatement := by
  intro f₀ D₀ B c d hF0
  have hBconn : IsConnected B := hF0.2.1.2.1
  have hstepsc : ∀ {V V' : Set ℂ}, IsOpen V → V.Nonempty → SimplyConnectedSpace ↥V →
      V ≠ Set.univ → IsOpen V' → IsConnected V' → ∀ {p : ℂ → ℂ}, DifferentiableOn ℂ p V' →
      Set.MapsTo p V' V → (V ⊆ p '' V') →
      (∀ K ⊆ V, IsCompact K → IsCompact (V' ∩ p ⁻¹' K)) →
      ((∀ z ∈ V', deriv p z ≠ 0) ∨
        (∃ c₀ ∈ V', deriv p c₀ = 0 ∧ ∀ z ∈ V', deriv p z = 0 → z = c₀)) →
      SimplyConnectedSpace ↥V' := by
    intro V V' hVo hVne hVsc hVproper hV'o hV'c p hp hmaps hsurj hprop hdisj
    rcases hdisj with hnc | ⟨c₀, hc₀, hdc, huniq⟩
    · exact simplyConnected_of_proper_holomorphic_no_crit hVo hVne hVsc hV'o hV'c hp hmaps hprop hnc
    · exact honeCrit hVo hVne hVsc hVproper hV'o hV'c hp hmaps hsurj hprop hc₀ hdc huniq
  have hstep : ∀ n x, x ∈ tower f₀ B d.Ωp (n + 1) → TowerStepData f₀ B d.Ωp n x :=
    fun n x hx => Work.BasinSC.Tower.tower_step (d := d) hF0 n x hx
  have hcomp := components_simplyConnected hF0 d hstep hstepsc
  have hloop : ∀ (x : ↥B) (γ : Path x x), γ.Homotopic (Path.refl x) :=
    fun x γ => path_homotopic_refl hF0 d hcomp γ
  haveI : LocallyPathConnectedSpace ↥B := hF0.2.1.1.locallyPathConnectedSpace
  haveI : ConnectedSpace ↥B := isConnected_iff_connectedSpace.mp hBconn
  haveI : PathConnectedSpace ↥B := PathConnectedSpace.of_locallyPathConnectedSpace
  exact (simply_connected_iff_loops_nullhomotopic).mpr ⟨inferInstance, hloop⟩

end Work.BasinSC