import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Main
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.EpsW.arcLiftPieces

/-!
# The wall dichotomy with boundary arcs

(...)
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.BoxShrink.PinchOff

namespace Work.EpsW

noncomputable section

/-- **The winding-span dichotomy for a region whose wall is a closed set with compact lifted
components.**  Let `C ⊆ ℝ³` be closed, with every connected component of its lift
`Xtilde P C ⊆ ℂ` compact, and let the complement of `C` in the surface `F = P.carrier` be split
into two pieces `X`, `Y` which are open in `F`.  Then the winding span of `X` is `⊥` or `⊤`.

This is Pardon's dichotomy without any hypothesis on the shape of `C`.  The proof is Pardon's
parameter-plane argument: `Ctᶜ = Xt ∪ Yt` is a clopen splitting of the complement of `Ct`, so the
components of `Xt` are components of `Ctᶜ`; since `Ct` is closed with compact components, `Ctᶜ` has
at most one unbounded component, which is invariant under the period lattice.  If `Xt` has an
unbounded component it is that invariant component, and lattice translates of a point of it can be
joined inside it, producing loops of `X` with winding vectors `(1,0)` and `(0,1)`; otherwise every
component of `Xt` is bounded and no loop of `X` has nonzero winding. -/
theorem windingSpan_bot_or_top_of_closed_of_components_compact {P : Work.CoreTopology.ParamTorus}
    {C X Y : Set R3} (hCcl : IsClosed C)
    (hcompC : ∀ z ∈ Xtilde P C, IsCompact (connectedComponentIn (Xtilde P C) z))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ C = X ∪ Y) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P X = ⊤ := by
  classical
  set Ct : Set ℂ := Xtilde P C with hCtdef
  set Xt : Set ℂ := Xtilde P X with hXtdef
  set Yt : Set ℂ := Xtilde P Y with hYtdef
  have hCt_closed : IsClosed Ct := hCcl.preimage (continuous_planePsi P)
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
  have hcomp : ∀ z ∈ Ct, IsCompact (connectedComponentIn Ct z) := hcompC
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

/-- **Components of a union of two closed disjoint sets with compact components are compact.** -/
theorem components_compact_union_of_closed_disjoint {S T : Set ℂ}
    (hScl : IsClosed S) (hTcl : IsClosed T) (hdisj : Disjoint S T)
    (hS : ∀ z ∈ S, IsCompact (connectedComponentIn S z))
    (hT : ∀ z ∈ T, IsCompact (connectedComponentIn T z)) :
    ∀ z ∈ S ∪ T, IsCompact (connectedComponentIn (S ∪ T) z) := by
  have hkey : ∀ {u v : Set ℂ}, IsClosed u → IsClosed v → Disjoint u v →
      (∀ z ∈ u, IsCompact (connectedComponentIn u z)) → ∀ z ∈ u,
      connectedComponentIn (u ∪ v) z = connectedComponentIn u z := by
    intro u v hu hv huv _ z hzu
    have hpre : IsPreconnected (connectedComponentIn (u ∪ v) z) :=
      isPreconnected_connectedComponentIn
    have h2 := (isPreconnected_iff_subset_of_disjoint_closed.mp hpre) u v hu hv
      (connectedComponentIn_subset (u ∪ v) z) (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨-, hyu, hyv⟩
        exact Set.disjoint_left.mp huv hyu hyv)
    apply Subset.antisymm
    · rcases h2 with h | h
      · have h3 : connectedComponentIn (u ∪ v) z ⊆ connectedComponentIn u z :=
          hpre.subset_connectedComponentIn (mem_connectedComponentIn (Or.inl hzu)) h
        exact h3
      · exact absurd (h (mem_connectedComponentIn (Or.inl hzu)))
          (Set.disjoint_left.mp huv hzu)
    · exact (isPreconnected_connectedComponentIn (x := z) (F := u)).subset_connectedComponentIn
        (mem_connectedComponentIn hzu)
        (show connectedComponentIn u z ⊆ u ∪ v from
          fun y hy => Or.inl (connectedComponentIn_subset u z hy))
  intro z hz
  rcases hz with hzS | hzT
  · rw [hkey hScl hTcl hdisj hS z hzS]
    exact hS z hzS
  · have h1 : connectedComponentIn (S ∪ T) z = connectedComponentIn (T ∪ S) z := by
      rw [Set.union_comm]
    rw [h1, hkey hTcl hScl hdisj.symm hT z hzT]
    exact hT z hzT

/-- **The wall dichotomy in the presence of boundary arcs.**  If the complement of the union of a
finite family of pairwise disjoint simple *inessential* closed curves `γ i` of the surface
`F = P.carrier` and a finite family of pairwise disjoint arcs `a j` of the surface (disjoint from
the curves) is split into two pieces `X`, `Y` open in `F`, then the winding span of `X` is `⊥`
or `⊤`.

The arcs contribute to the wall but not to the conclusion: the only thing needed about them is
that the lifts of the wall to the parameter plane still have compact connected components, which
holds for an injective arc because its lift pieces are compact and disjoint.  With that in hand
the dichotomy `windingSpan_bot_or_top_of_closed_of_components_compact` applies to the wall. -/
theorem wallWithBoundaryDichotomy {P : Work.CoreTopology.ParamTorus} {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3} {n m : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    {a : Fin m → ContinuousMap Work.Smooth.Plane.ArcInterval LeanEval.KnotTheory.PardonDistortion.R3}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (harcinj : ∀ j, Function.Injective (a j))
    (harcmem : ∀ (j : Fin m) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier)
    (harcdisj : Pairwise fun j j' : Fin m => Disjoint (Set.range (a j)) (Set.range (a j')))
    (harcdisjc : ∀ j i, Disjoint (Set.range (a j)) (Set.range (γ i).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ ((⋃ i, Set.range (γ i).γ) ∪ (⋃ j, Set.range (a j))) = X ∪ Y) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P X = ⊤ := by
  classical
  set A : Set R3 := ⋃ i, Set.range (γ i).γ with hA
  set B : Set R3 := ⋃ j, Set.range (a j) with hB
  set C : Set R3 := A ∪ B with hC
  -- the wall is compact, hence closed
  have hAcomp : IsCompact A := by
    rw [hA]
    exact isCompact_iUnion (fun i => isCompact_range_closedCurve (γ i))
  have hBcomp : IsCompact B := by
    rw [hB]
    exact isCompact_iUnion (fun j =>
      (Set.image_univ (f := (a j : Work.Smooth.Plane.ArcInterval → R3)).symm ▸
        isCompact_univ.image (a j).continuous))
  have hCcomp : IsCompact C := by
    rw [hC]
    exact hAcomp.union hBcomp
  have hCcl : IsClosed C := hCcomp.isClosed
  -- the lift of the wall splits as the lift of the curves plus the lift of the arcs
  have hAcl : IsClosed (Work.BoxShrink.PinchOff.Xtilde P A) :=
    hAcomp.isClosed.preimage (continuous_planePsi P)
  have hBcl : IsClosed (Work.BoxShrink.PinchOff.Xtilde P B) :=
    hBcomp.isClosed.preimage (continuous_planePsi P)
  have hdisjAB : Disjoint (Work.BoxShrink.PinchOff.Xtilde P A)
      (Work.BoxShrink.PinchOff.Xtilde P B) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : planePsi P z ∈ A := hz1
    have h2 : planePsi P z ∈ B := hz2
    rw [hA] at h1
    rw [hB] at h2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h2
    exact Set.disjoint_left.mp (harcdisjc j i) hj hi
  have hsplit : Work.BoxShrink.PinchOff.Xtilde P C =
      Work.BoxShrink.PinchOff.Xtilde P A ∪ Work.BoxShrink.PinchOff.Xtilde P B := by
    rw [hC]
    exact Set.preimage_union
  have hcompA : ∀ z ∈ Work.BoxShrink.PinchOff.Xtilde P A,
      IsCompact (connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P A) z) := by
    rw [hA]
    exact Work.BoxShrink.PinchOff.components_compact hsimple hess hdisj
  have hcompB : ∀ z ∈ Work.BoxShrink.PinchOff.Xtilde P B,
      IsCompact (connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P B) z) := by
    rw [hB]
    exact components_compact_preimage_arcs_local (P := P) (m := m) (a := a) harcinj harcmem harcdisj
  have hcomp : ∀ z ∈ Work.BoxShrink.PinchOff.Xtilde P C,
      IsCompact (connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P C) z) := by
    rw [hsplit]
    exact components_compact_union_of_closed_disjoint hAcl hBcl hdisjAB hcompA hcompB
  refine windingSpan_bot_or_top_of_closed_of_components_compact (P := P) (C := C)
    (X := X) (Y := Y) hCcl hcomp hX hY hXY ?_
  rw [hC]
  exact hcover

end

end Work.EpsW
