import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.BoxShrink.PinchOff.IB.Pieces
import Submission.Work.BoxShrink.PinchOff.IB.Components
import Submission.Work.BoxShrink.PinchOff.IB.Separator
import Submission.Work.BoxShrink.PinchOff.IB.Span

/-!
# The winding span of a region bounded by inessential simple curves

Let `X, Y` be two disjoint regions of the torus `F = P.carrier`, open in `F`, whose union is the
complement of a finite family of pairwise disjoint *simple* *inessential* closed curves `γ i`.
Then the winding span of `X` is `⊥` or `⊤`.

The proof works in the parameter plane `ℂ`.  Writing `Ct`, `Xt`, `Yt` for the preimages of the
curve family, of `X` and of `Y`, one has `Xt ∪ Yt = Ctᶜ`, with `Xt` and `Yt` open and closed in
`Ctᶜ`, and every connected component of `Ct` is compact (`components_compact`).  Hence `Ctᶜ` has at
most one unbounded component (`unbounded_component_unique`), which is invariant under the lattice
`2π(ℤ + iℤ)`.

* If `Xt` has an unbounded component `U`, then `U` is that invariant component, so both `z₀` and
  `z₀ + periodPt 1 0` (and `z₀ + periodPt 0 1`) lie in `U`, and `U` is path connected (it is an
  open component): the paths produce loops of `X` of winding `(1,0)` and `(0,1)`
  (`exists_closedCurve_of_path`), so the winding span is `⊤`.
* Otherwise every component of `Xt` is bounded, and the lift of any loop of `X` runs between two
  points of one bounded component differing by a lattice vector; boundedness forces that vector to
  vanish, so all loops of `X` have winding `0` and the winding span is `⊥`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The component of a point of a clopen subset is its component in the ambient set.**  If
`S ⊆ T`, `S` and `T \ S` are open, and `c ∈ S`, then the component of `c` in `T` is its component
in `S`. -/
theorem connectedComponentIn_of_clopen {S T : Set ℂ} (hST : S ⊆ T) (hSopen : IsOpen S)
    (hTopen : IsOpen (T \ S)) {c : ℂ} (hc : c ∈ S) :
    connectedComponentIn T c = connectedComponentIn S c := by
  apply Subset.antisymm
  · have hcT : c ∈ T := hST hc
    have hsub : connectedComponentIn T c ⊆ S ∪ (T \ S) := by
      intro z hz
      have hzT : z ∈ T := connectedComponentIn_subset T c hz
      by_cases hzS : z ∈ S
      · exact Or.inl hzS
      · exact Or.inr ⟨hzT, hzS⟩
    have hdisj : Disjoint S (T \ S) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      exact hz'.2 hz
    rcases (isPreconnected_connectedComponentIn (x := c) (F := T)).subset_or_subset
      hSopen hTopen hdisj hsub with h | h
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hcT) h
    · exact absurd hc (h (mem_connectedComponentIn hcT)).2
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hc) (fun z hz => hST (connectedComponentIn_subset S c hz))

/-- **The translate of a component of a lattice-invariant set.** -/
theorem connectedComponentIn_add {S : Set ℂ}
    (hS : ∀ z w : ℂ, w ∈ periodLattice → (z + w ∈ S ↔ z ∈ S)) {z w : ℂ}
    (hw : w ∈ periodLattice) (hz : z ∈ S) :
    connectedComponentIn S (z + w) = (fun y => y + w) '' connectedComponentIn S z := by
  have himg : (fun y : ℂ => y + w) '' S = S := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact (hS y' w hw).mpr hy'
    · intro hy
      exact ⟨y + (-w), (hS (y + (-w)) w hw).mp (by simpa using hy), by ring⟩
  have hhomeo := Homeomorph.image_connectedComponentIn (Homeomorph.addRight w) (s := S) hz
  rw [Homeomorph.coe_addRight w] at hhomeo
  rw [himg] at hhomeo
  exact hhomeo.symm

/-- **The winding span of a region of a torus whose boundary consists of inessential simple
curves is `⊥` or `⊤`.** -/
theorem windingSpan_bot_or_top_aux {P : Work.CoreTopology.ParamTorus} {X Y : Set R3} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨ Work.SurgeryInvariance.WindingSpan P X = ⊤ := by
  classical
  set C : Set R3 := ⋃ i, Set.range (γ i).γ with hCdef
  set Ct : Set ℂ := Xtilde P C with hCtdef
  set Xt : Set ℂ := Xtilde P X with hXtdef
  set Yt : Set ℂ := Xtilde P Y with hYtdef
  have hXdisjC : Disjoint X C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    have h1 : x ∈ P.carrier \ C := by rw [hcover]; exact Or.inl hx
    exact h1.2 hxC
  have hYdisjC : Disjoint Y C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    have h1 : x ∈ P.carrier \ C := by rw [hcover]; exact Or.inr hx
    exact h1.2 hxC
  have hXc : X ⊆ P.carrier := by
    intro x hx
    have h1 : x ∈ P.carrier \ C := by rw [hcover]; exact Or.inl hx
    exact h1.1
  have hYc : Y ⊆ P.carrier := by
    intro x hx
    have h1 : x ∈ P.carrier \ C := by rw [hcover]; exact Or.inr hx
    exact h1.1
  have hXt_open : IsOpen Xt := isOpen_Xtilde hXc hX
  have hYt_open : IsOpen Yt := isOpen_Xtilde hYc hY
  have hXYt : Disjoint Xt Yt := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact (Set.disjoint_left.mp hXY hz1) hz2
  have hpart : Xt ∪ Yt = Ctᶜ := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact fun hzC => (Set.disjoint_left.mp hXdisjC hz) hzC
      · exact fun hzC => (Set.disjoint_left.mp hYdisjC hz) hzC
    · intro hz
      have h1 : planePsi P z ∈ P.carrier \ C := ⟨planePsi_mem_carrier P z, hz⟩
      rw [hcover] at h1
      exact h1
  have hXt_sub : Xt ⊆ Ctᶜ := by rw [← hpart]; exact Set.subset_union_left
  have hYt_sub : Yt ⊆ Ctᶜ := by rw [← hpart]; exact Set.subset_union_right
  have hXtInv : ∀ z w : ℂ, w ∈ periodLattice → (z + w ∈ Xt ↔ z ∈ Xt) :=
    fun z w hw => Xtilde_add_periodLattice P X z w hw
  have hCtInv : ∀ z w : ℂ, w ∈ periodLattice → (z + w ∈ Ct ↔ z ∈ Ct) :=
    fun z w hw => Xtilde_add_periodLattice P C z w hw
  have hCcl : IsClosed C := by
    rw [hCdef]
    exact (isCompact_iUnion (fun i => isCompact_range_closedCurve (γ i))).isClosed
  have hCt_closed : IsClosed Ct := by
    rw [hCtdef]
    exact hCcl.preimage (continuous_planePsi P)
  have hcomp : ∀ z ∈ Ct, IsCompact (connectedComponentIn Ct z) :=
    components_compact hsimple hess hdisj
  have hunique : ∀ {x y : ℂ}, x ∉ Ct → y ∉ Ct →
      (∀ R : ℝ, ∃ w ∈ connectedComponentIn Ctᶜ x, R ≤ ‖w‖) →
      (∀ R : ℝ, ∃ w ∈ connectedComponentIn Ctᶜ y, R ≤ ‖w‖) →
      connectedComponentIn Ctᶜ x = connectedComponentIn Ctᶜ y :=
    fun hx hy hbx hby => unbounded_component_unique hCt_closed hcomp hx hy hbx hby
  have hXtComp : ∀ z ∈ Xt, connectedComponentIn Ctᶜ z = connectedComponentIn Xt z := by
    intro z hz
    refine connectedComponentIn_of_clopen hXt_sub hXt_open ?_ hz
    have hEq : Ctᶜ \ Xt = Yt := by
      ext w
      constructor
      · rintro ⟨hw, hwX⟩
        have h1 : w ∈ Xt ∪ Yt := by rw [hpart]; exact hw
        rcases h1 with h | h
        · exact absurd h hwX
        · exact h
      · intro hw
        exact ⟨hYt_sub hw, fun hwX => (Set.disjoint_left.mp hXYt hwX) hw⟩
    rw [hEq]
    exact hYt_open
  by_cases hcase : ∃ z ∈ Xt, ∀ R : ℝ, ∃ w ∈ connectedComponentIn Xt z, R ≤ ‖w‖
  · -- Case 1: `Xt` has an unbounded component
    obtain ⟨z₀, hz₀Xt, hz₀unb⟩ := hcase
    set U : Set ℂ := connectedComponentIn Xt z₀ with hUdef
    have hUopen : IsOpen U := hXt_open.connectedComponentIn
    have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀Xt
    have hUsubXt : U ⊆ Xt := connectedComponentIn_subset Xt z₀
    have hUinv : ∀ w ∈ periodLattice, (fun y => y + w) '' U = U := by
      intro w hw
      have hzwXt : z₀ + w ∈ Xt := (hXtInv z₀ w hw).mpr hz₀Xt
      have hcompw : connectedComponentIn Xt (z₀ + w) = (fun y => y + w) '' U :=
        connectedComponentIn_add hXtInv hw hz₀Xt
      have hz₀ct : z₀ ∉ Ct := fun h => hXt_sub hz₀Xt h
      have hzwct : z₀ + w ∉ Ct := fun h => hz₀ct ((hCtInv z₀ w hw).mp h)
      have hb1 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Ctᶜ z₀, R ≤ ‖y‖ := by
        intro R
        obtain ⟨y, hy, hR⟩ := hz₀unb R
        exact ⟨y, by rw [hXtComp z₀ hz₀Xt]; exact hy, hR⟩
      have hb2 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Ctᶜ (z₀ + w), R ≤ ‖y‖ := by
        intro R
        obtain ⟨y, hy, hR⟩ := hz₀unb (R + ‖w‖)
        refine ⟨y + w, ?_, ?_⟩
        · rw [hXtComp (z₀ + w) hzwXt, hcompw]
          exact ⟨y, hy, rfl⟩
        · have h1 : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
            calc ‖y‖ = ‖(y + w) - w‖ := by ring_nf
              _ ≤ ‖y + w‖ + ‖w‖ := norm_sub_le _ _
          linarith
      have heq : connectedComponentIn Ctᶜ z₀ = connectedComponentIn Ctᶜ (z₀ + w) :=
        hunique hz₀ct hzwct hb1 hb2
      rw [hXtComp z₀ hz₀Xt, hXtComp (z₀ + w) hzwXt, hcompw] at heq
      exact heq.symm
    -- `U` is path connected
    have hUpc : ∀ a ∈ U, ∀ b ∈ U, JoinedIn U a b := by
      haveI : LocallyPathConnectedSpace ↥U := hUopen.locallyPathConnectedSpace
      haveI : PreconnectedSpace ↥U :=
        isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
      intro a ha b hb
      rw [joinedIn_iff_joined ha hb, ← connectedComponent_eq_iff_joined,
        PreconnectedSpace.connectedComponent_eq_univ,
        PreconnectedSpace.connectedComponent_eq_univ]
    -- the two loops
    have hloop : ∀ (a b : ℤ), ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t, γ'.γ t ∈ X) ∧ Work.SurgeryInvariance.windingOf P γ' = (a, b) := by
      intro a b
      have hνmem : periodPt a b ∈ periodLattice := ⟨(a, b), rfl⟩
      have hmem : z₀ + periodPt a b ∈ U := by
        have h := hUinv (periodPt a b) hνmem
        rw [← h]
        exact ⟨z₀, hz₀U, rfl⟩
      obtain ⟨p, hp⟩ := hUpc z₀ hz₀U (z₀ + periodPt a b) hmem
      set c : ℝ → ℂ := fun t => p.extend (t / (2 * Real.pi)) with hcdef
      have hc : c 0 = z₀ := by
        change p.extend ((0:ℝ) / (2 * Real.pi)) = z₀
        rw [zero_div]
        exact Path.extend_zero p
      have h2 : c (2 * Real.pi) = z₀ + periodPt a b := by
        change p.extend ((2 * Real.pi) / (2 * Real.pi)) = z₀ + periodPt a b
        rw [show (2 * Real.pi) / (2 * Real.pi) = 1 by field_simp, Path.extend_one]
      have hcmem : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), c t ∈ Xtilde P X := by
        intro t ht
        have ht1 : t / (2 * Real.pi) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · exact div_nonneg ht.1 (by positivity)
          · rw [div_le_one (by positivity)]
            exact ht.2
        change p.extend (t / (2 * Real.pi)) ∈ Xtilde P X
        rw [Path.extend_apply p ht1]
        exact hUsubXt (hp ⟨t / (2 * Real.pi), ht1⟩)
      exact exists_closedCurve_of_path c
        (p.extend.continuous.comp (by fun_prop)) hc h2 hcmem
    have h1mem : (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) ∈ Work.SurgeryInvariance.WindingSpan P X := by
      obtain ⟨γ', hγ', hw⟩ := hloop 1 0
      refine Submodule.subset_span ⟨γ', hγ', ?_⟩
      rw [hw]
      norm_num
    have h2mem : (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) ∈ Work.SurgeryInvariance.WindingSpan P X := by
      obtain ⟨γ', hγ', hw⟩ := hloop 0 1
      refine Submodule.subset_span ⟨γ', hγ', ?_⟩
      rw [hw]
      norm_num
    right
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = v.1 • (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) + v.2 • (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1mem) (Submodule.smul_mem _ _ h2mem)
  · -- Case 2: every component of `Xt` is bounded
    left
    have hbdd : ∀ z ∈ Xt, ∃ R : ℝ, ∀ w ∈ connectedComponentIn Xt z, ‖w‖ ≤ R := by
      intro z hz
      by_contra h
      push_neg at h
      exact hcase ⟨z, hz, fun R => by
        obtain ⟨w, hw, hR⟩ := h R
        exact ⟨w, hw, le_of_lt hR⟩⟩
    have hzero : ∀ γ' : Work.CoreTopology.ClosedCurve P, (∀ t, γ'.γ t ∈ X) →
        Work.SurgeryInvariance.windingOf P γ' = (0, 0) := by
      intro γ' hγ'
      set L : Work.CoreTopology.LiftOf P γ' :=
        Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ') with hLdef
      set w : ℤ × ℤ := Work.SurgeryInvariance.windingOf P γ' with hwdef
      have hwend : Work.SurgeryInvariance.windingOf P γ' = L.winding :=
        Work.SurgeryInvariance.windingOf_eq P γ' L
      have hw_eq : w = L.winding := by rw [hwdef, hwend]
      have hpath_mem : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), liftMap L t ∈ Xt := by
        intro t ht
        show planePsi P (liftMap L t) ∈ X
        rw [planePsi_liftMap]
        exact hγ' t
      have h0mem : liftMap L 0 ∈ connectedComponentIn Xt (liftMap L 0) :=
        mem_connectedComponentIn (hpath_mem 0 ⟨le_refl 0, by positivity⟩)
      -- the two endpoints of the lifted loop lie in one component
      have himg_pre : IsPreconnected ((fun t : ℝ => liftMap L t) '' Set.Icc (0:ℝ) (2 * Real.pi)) :=
        isPreconnected_Icc.image _ (continuous_liftMap L).continuousOn
      have hsub : (fun t : ℝ => liftMap L t) '' Set.Icc (0:ℝ) (2 * Real.pi) ⊆ Xt := by
        rintro y ⟨t, ht, rfl⟩
        exact hpath_mem t ht
      have hsame : liftMap L (2 * Real.pi) ∈ connectedComponentIn Xt (liftMap L 0) :=
        (himg_pre.subset_connectedComponentIn ⟨0, ⟨le_refl 0, by positivity⟩, rfl⟩ hsub)
          ⟨2 * Real.pi, ⟨by positivity, le_refl _⟩, rfl⟩
      -- the shift
      have hshift : liftMap L (2 * Real.pi) = liftMap L 0 + periodPt w.1 w.2 := by
        have hspec := L.winding_spec
        have h1 : L.Θ (2 * Real.pi) = L.Θ 0 + (w.1 : ℝ) * (2 * Real.pi) := by
          rw [hw_eq]
          exact hspec.1
        have h2 : L.Φ (2 * Real.pi) = L.Φ 0 + (w.2 : ℝ) * (2 * Real.pi) := by
          rw [hw_eq]
          exact hspec.2
        apply Complex.ext <;> simp [liftMap, h1, h2, periodPt]
      obtain ⟨R, hR⟩ := hbdd (liftMap L 0) (hpath_mem 0 ⟨le_refl 0, by positivity⟩)
      -- the component is invariant under the shift
      have hshmem : periodPt w.1 w.2 ∈ periodLattice := ⟨(w.1, w.2), rfl⟩
      have hWin : (fun y => y + periodPt w.1 w.2) '' (connectedComponentIn Xt (liftMap L 0))
          = connectedComponentIn Xt (liftMap L 0) := by
        have hcompw := connectedComponentIn_add hXtInv hshmem
          (hpath_mem 0 ⟨le_refl 0, by positivity⟩)
        rw [← hshift] at hcompw
        rw [← hcompw, connectedComponentIn_eq hsame]
      have hiter : ∀ m : ℕ,
          liftMap L 0 + (m : ℂ) * periodPt w.1 w.2 ∈ connectedComponentIn Xt (liftMap L 0) := by
        intro m
        induction m with
        | zero => simpa using h0mem
        | succ m ih =>
            have hmem_image : liftMap L 0 + (m : ℂ) * periodPt w.1 w.2 + periodPt w.1 w.2
                ∈ (fun y => y + periodPt w.1 w.2) '' (connectedComponentIn Xt (liftMap L 0)) :=
              ⟨liftMap L 0 + (m : ℂ) * periodPt w.1 w.2, ih, rfl⟩
            have hmem_W : liftMap L 0 + (m : ℂ) * periodPt w.1 w.2 + periodPt w.1 w.2
                ∈ connectedComponentIn Xt (liftMap L 0) := hWin ▸ hmem_image
            have heq : liftMap L 0 + ((m : ℂ) + 1) * periodPt w.1 w.2
                = liftMap L 0 + (m : ℂ) * periodPt w.1 w.2 + periodPt w.1 w.2 := by ring
            push_cast
            rw [heq]
            exact hmem_W
      have hshzero : periodPt w.1 w.2 = 0 := by
        by_contra hne
        have hpos : (0:ℝ) < ‖periodPt w.1 w.2‖ := norm_pos_iff.mpr hne
        obtain ⟨m, hm⟩ := exists_nat_gt ((R + ‖liftMap L 0‖) / ‖periodPt w.1 w.2‖)
        have hbound := hR _ (hiter m)
        have hnorm : ‖(m : ℂ) * periodPt w.1 w.2‖ = (m : ℝ) * ‖periodPt w.1 w.2‖ := by
          rw [norm_mul, Complex.norm_natCast]
        have hlow : (m : ℝ) * ‖periodPt w.1 w.2‖ - ‖liftMap L 0‖
            ≤ ‖liftMap L 0 + (m : ℂ) * periodPt w.1 w.2‖ := by
          have h1 : ‖(m : ℂ) * periodPt w.1 w.2‖ ≤
              ‖liftMap L 0 + (m : ℂ) * periodPt w.1 w.2‖ + ‖liftMap L 0‖ := by
            calc ‖(m : ℂ) * periodPt w.1 w.2‖
                = ‖(liftMap L 0 + (m : ℂ) * periodPt w.1 w.2) - liftMap L 0‖ := by ring_nf
              _ ≤ ‖liftMap L 0 + (m : ℂ) * periodPt w.1 w.2‖ + ‖liftMap L 0‖ := norm_sub_le _ _
          rw [hnorm] at h1
          linarith
        have hgt : R < (m : ℝ) * ‖periodPt w.1 w.2‖ - ‖liftMap L 0‖ := by
          rw [div_lt_iff₀ hpos] at hm
          linarith
        linarith
      have hwzero : w = (0, 0) := by
        by_contra hne
        exact (periodPt_ne_zero hne) hshzero
      exact hwzero
    rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_eq_bot]
    rintro v ⟨γ', hγ', rfl⟩
    rw [hzero γ' hγ']
    simp

end

end Work.BoxShrink.PinchOff
