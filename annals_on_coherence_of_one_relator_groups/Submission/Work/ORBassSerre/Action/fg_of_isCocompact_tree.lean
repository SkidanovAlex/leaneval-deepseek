import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientReverse
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ORBassSerre.Action

open Quiver

universe u v w

/-- A universe-correct copy of the type of edge orbits of a `G`-graph (the library's
`Work.ORBassSerre.orbitE` fixes its universe level in a way that makes it awkward to use). -/
abbrev EdgeOrbit (G : Type u) (V : Type v) [Group G] [Quiver V] [MulAction G V]
    [Quiver.HasReverse V] [Work.ORBassSerre.GraphAction G V] : Type _ :=
  MulAction.orbitRel.Quotient G (Quiver.Total V)

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## Basic rewriting lemmas for the action on arrows -/

theorem smul_left_total (g : G) (u : Quiver.Total V) : (g • u).left = g • u.left :=
  GraphAction.smul_left g u

theorem smul_right_total (g : G) (u : Quiver.Total V) : (g • u).right = g • u.right :=
  GraphAction.smul_right g u

/-! ## Representatives of vertex and edge orbits -/

/-- A chosen representative vertex of a vertex orbit. -/
noncomputable def orbitRepV (A : Work.ORBassSerre.orbitV G V) : V := Quotient.out A

theorem orbitRepV_mk (A : Work.ORBassSerre.orbitV G V) :
    Quotient.mk'' (orbitRepV (G := G) (V := V) A) = A :=
  Quotient.out_eq A

/-- A chosen representative arrow of an edge orbit. -/
noncomputable def orbitRepE (E : EdgeOrbit G V) : Quiver.Total V := Quotient.out E

theorem orbitRepE_mk (E : EdgeOrbit G V) : Quotient.mk'' (orbitRepE (G := G) (V := V) E) = E :=
  Quotient.out_eq E

/-! ## Recovering group elements from orbit equalities -/

/-- Two vertices with the same orbit are related by a group element. -/
theorem exists_smul_of_mk_eq {x y : V}
    (h : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = Quotient.mk'' y) :
    ∃ g : G, g • x = y := by
  have h' : MulAction.orbitRel G V x y := Quotient.exact h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h')
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-- Two arrows with the same orbit are related by a group element. -/
theorem exists_smulTotal_of_mk_eq {u w : Quiver.Total V}
    (h : (Quotient.mk'' u : EdgeOrbit G V) = Quotient.mk'' w) :
    ∃ g : G, g • u = w := by
  have h' : MulAction.orbitRel G (Quiver.Total V) u w := Quotient.exact h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h')
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-- Arrows in the same orbit have sources in the same vertex orbit. -/
theorem mk_left_eq_of_mk_eq {u w : Quiver.Total V}
    (h : (Quotient.mk'' u : EdgeOrbit G V) = Quotient.mk'' w) :
    (Quotient.mk'' u.left : Work.ORBassSerre.orbitV G V) = Quotient.mk'' w.left := by
  obtain ⟨g, hg⟩ := exists_smulTotal_of_mk_eq (G := G) (V := V) h
  have hgl : w.left = g • u.left := by rw [← hg, smul_left_total]
  rw [hgl]
  refine Eq.symm ?_
  exact Quotient.sound ⟨g, rfl⟩

/-- Arrows in the same orbit have targets in the same vertex orbit. -/
theorem mk_right_eq_of_mk_eq {u w : Quiver.Total V}
    (h : (Quotient.mk'' u : EdgeOrbit G V) = Quotient.mk'' w) :
    (Quotient.mk'' u.right : Work.ORBassSerre.orbitV G V) = Quotient.mk'' w.right := by
  obtain ⟨g, hg⟩ := exists_smulTotal_of_mk_eq (G := G) (V := V) h
  have hgr : w.right = g • u.right := by rw [← hg, smul_right_total]
  rw [hgr]
  refine Eq.symm ?_
  exact Quotient.sound ⟨g, rfl⟩

/-! ## The edge elements -/

/-- The vertex orbit of the source of the representative arrow of an edge orbit. -/
noncomputable def srcE (E : EdgeOrbit G V) : Work.ORBassSerre.orbitV G V :=
  Quotient.mk'' (orbitRepE (G := G) (V := V) E).left

/-- The vertex orbit of the target of the representative arrow of an edge orbit. -/
noncomputable def tgtE (E : EdgeOrbit G V) : Work.ORBassSerre.orbitV G V :=
  Quotient.mk'' (orbitRepE (G := G) (V := V) E).right

theorem exists_alphaE (E : EdgeOrbit G V) :
    ∃ g : G, g • orbitRepV (srcE (G := G) (V := V) E) =
      (orbitRepE (G := G) (V := V) E).left :=
  exists_smul_of_mk_eq (G := G) (V := V)
    (x := orbitRepV (srcE (G := G) (V := V) E)) (y := (orbitRepE (G := G) (V := V) E).left)
    (orbitRepV_mk (G := G) (V := V) (srcE (G := G) (V := V) E))

/-- An element carrying the representative vertex of the source orbit of `E` to the source of
the representative arrow of `E`. -/
noncomputable def alphaE (E : EdgeOrbit G V) : G :=
  Classical.choose (exists_alphaE (G := G) (V := V) E)

theorem alphaE_spec (E : EdgeOrbit G V) :
    alphaE (G := G) (V := V) E • orbitRepV (srcE (G := G) (V := V) E) =
      (orbitRepE (G := G) (V := V) E).left :=
  Classical.choose_spec (exists_alphaE (G := G) (V := V) E)

theorem exists_betaE (E : EdgeOrbit G V) :
    ∃ g : G, g • orbitRepV (tgtE (G := G) (V := V) E) =
      (orbitRepE (G := G) (V := V) E).right :=
  exists_smul_of_mk_eq (G := G) (V := V)
    (x := orbitRepV (tgtE (G := G) (V := V) E)) (y := (orbitRepE (G := G) (V := V) E).right)
    (orbitRepV_mk (G := G) (V := V) (tgtE (G := G) (V := V) E))

/-- An element carrying the representative vertex of the target orbit of `E` to the target of
the representative arrow of `E`. -/
noncomputable def betaE (E : EdgeOrbit G V) : G :=
  Classical.choose (exists_betaE (G := G) (V := V) E)

theorem betaE_spec (E : EdgeOrbit G V) :
    betaE (G := G) (V := V) E • orbitRepV (tgtE (G := G) (V := V) E) =
      (orbitRepE (G := G) (V := V) E).right :=
  Classical.choose_spec (exists_betaE (G := G) (V := V) E)

/-- The edge element of an edge orbit: the group element relating the two chosen vertex
representatives to the representative arrow. -/
noncomputable def edgeElt (E : EdgeOrbit G V) : G :=
  (alphaE (G := G) (V := V) E)⁻¹ * betaE (G := G) (V := V) E

/-- The canonical lift of the representative arrow of `E`, i.e. the arrow with orbit `E`
starting at the chosen representative of the source orbit. -/
noncomputable def edgeLift (E : EdgeOrbit G V) : Quiver.Total V :=
  (alphaE (G := G) (V := V) E)⁻¹ • orbitRepE (G := G) (V := V) E

theorem edgeLift_left (E : EdgeOrbit G V) :
    (edgeLift (G := G) (V := V) E).left = orbitRepV (srcE (G := G) (V := V) E) := by
  show ((alphaE (G := G) (V := V) E)⁻¹ • orbitRepE (G := G) (V := V) E).left =
    orbitRepV (srcE (G := G) (V := V) E)
  rw [smul_left_total, ← alphaE_spec, inv_smul_smul]

theorem edgeLift_right (E : EdgeOrbit G V) :
    (edgeLift (G := G) (V := V) E).right =
      edgeElt (G := G) (V := V) E • orbitRepV (tgtE (G := G) (V := V) E) := by
  show ((alphaE (G := G) (V := V) E)⁻¹ • orbitRepE (G := G) (V := V) E).right =
    edgeElt (G := G) (V := V) E • orbitRepV (tgtE (G := G) (V := V) E)
  rw [smul_right_total, ← betaE_spec, ← mul_smul, edgeElt]

theorem edgeLift_orbit (E : EdgeOrbit G V) :
    (Quotient.mk'' (edgeLift (G := G) (V := V) E) : EdgeOrbit G V) = E := by
  have h1 : (Quotient.mk'' (edgeLift (G := G) (V := V) E) : EdgeOrbit G V) =
      Quotient.mk'' (orbitRepE (G := G) (V := V) E) := by
    show (Quotient.mk'' ((alphaE (G := G) (V := V) E)⁻¹ •
        orbitRepE (G := G) (V := V) E) : EdgeOrbit G V) =
      Quotient.mk'' (orbitRepE (G := G) (V := V) E)
    exact Quotient.sound ⟨(alphaE (G := G) (V := V) E)⁻¹, rfl⟩
  rw [h1, orbitRepE_mk]

/-! ## The main theorem -/

/-- A group acting cocompactly on a non-empty tree with finitely generated vertex stabilisers is
finitely generated (the finitely generated form of the Bass--Serre structure result for groups
acting on trees). -/
theorem fg_of_isCocompact_tree {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (hT : Work.ORBassSerre.IsTree V) (hcc : Work.ORBassSerre.IsCocompact G V)
    (hstab : ∀ v : V, Group.FG (MulAction.stabilizer G v)) :
    Group.FG G := by
  classical
  rw [Group.fg_def]
  refine Subgroup.isMulFG_iff.mpr ?_
  haveI hfinV : Finite (Work.ORBassSerre.orbitV G V) := hcc.1
  haveI hfinE : Finite (EdgeOrbit G V) := hcc.2
  haveI : Fintype (Work.ORBassSerre.orbitV G V) := Fintype.ofFinite _
  haveI : Fintype (EdgeOrbit G V) := Fintype.ofFinite _
  -- Finite generating sets of the vertex stabilisers of the chosen representatives.
  have hstab' : ∀ A : Work.ORBassSerre.orbitV G V,
      (MulAction.stabilizer G (orbitRepV (G := G) (V := V) A)).FG :=
    fun A => (Group.fg_iff_subgroup_fg _).mp (hstab (orbitRepV A))
  let genStab : Work.ORBassSerre.orbitV G V → Finset G := fun A => Classical.choose (Subgroup.isMulFG_iff.mp (hstab' A))
  have genStab_spec : ∀ A : Work.ORBassSerre.orbitV G V,
      Subgroup.closure ((genStab A : Finset G) : Set G) =
        MulAction.stabilizer G (orbitRepV (G := G) (V := V) A) :=
    fun A => Classical.choose_spec (Subgroup.isMulFG_iff.mp (hstab' A))
  -- The finite generating set.
  set X : Finset G := (Finset.univ.biUnion genStab) ∪
    (Finset.univ.image (edgeElt (G := G) (V := V))) with hX
  set H : Subgroup G := Subgroup.closure (X : Set G) with hH
  -- (a) Each chosen vertex stabiliser is contained in `H`.
  have hstab_le : ∀ A : Work.ORBassSerre.orbitV G V,
      MulAction.stabilizer G (orbitRepV (G := G) (V := V) A) ≤ H := by
    intro A
    have hsub : ((genStab A : Finset G) : Set G) ⊆ (X : Set G) := by
      intro g hg
      rw [hX]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨A, Finset.mem_univ A, hg⟩)
    rw [← genStab_spec A, hH]
    exact Subgroup.closure_mono hsub
  -- (b) Each edge element lies in `H`.
  have hedge_mem : ∀ E : EdgeOrbit G V, edgeElt (G := G) (V := V) E ∈ H := by
    intro E
    rw [hH]
    refine Subgroup.subset_closure ?_
    rw [hX]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨E, Finset.mem_univ E, rfl⟩)
  -- (c) `H` is transitive on every vertex orbit.
  have htrans : ∀ v : V, ∃ h : G, h ∈ H ∧ h • orbitRepV (G := G) (V := V) (Quotient.mk'' v) = v := by
    set W : Set V := {v | ∃ h : G, h ∈ H ∧ h • orbitRepV (G := G) (V := V) (Quotient.mk'' v) = v} with hW
    have hWclosed : ∀ ⦃a b : V⦄, a ∈ W → (a ⟶ b) → b ∈ W := by
      intro a b ha f
      obtain ⟨h, hhH, hha⟩ := ha
      let u : Quiver.Total V := Quiver.Total.mk a b f
      let E : EdgeOrbit G V := Quotient.mk'' u
      let F : Quiver.Total V := h⁻¹ • u
      let L : Quiver.Total V := edgeLift (G := G) (V := V) E
      -- the sources of `F` and `L` both equal the chosen representative of the orbit of `a`
      have hFleft : F.left = orbitRepV (G := G) (V := V) (Quotient.mk'' a) := by
        show (h⁻¹ • u).left = orbitRepV (G := G) (V := V) (Quotient.mk'' a)
        rw [smul_left_total]
        rw [show u.left = a from rfl]
        conv_lhs => rw [← hha]
        exact inv_smul_smul h (orbitRepV (G := G) (V := V) (Quotient.mk'' a))
      have hsrcE : srcE (G := G) (V := V) E = Quotient.mk'' a := by
        have hmk : (Quotient.mk'' (orbitRepE (G := G) (V := V) E) : EdgeOrbit G V) =
            Quotient.mk'' u := by
          change (Quotient.mk'' (orbitRepE E) : EdgeOrbit G V) = E
          exact orbitRepE_mk E
        have hleft := mk_left_eq_of_mk_eq (G := G) (V := V) hmk
        rw [show srcE (G := G) (V := V) E =
          (Quotient.mk'' (orbitRepE E).left : Work.ORBassSerre.orbitV G V) from rfl, hleft]
      have htgtE : tgtE (G := G) (V := V) E = Quotient.mk'' b := by
        have hmk : (Quotient.mk'' (orbitRepE (G := G) (V := V) E) : EdgeOrbit G V) =
            Quotient.mk'' u := by
          change (Quotient.mk'' (orbitRepE E) : EdgeOrbit G V) = E
          exact orbitRepE_mk E
        have hright := mk_right_eq_of_mk_eq (G := G) (V := V) hmk
        rw [show tgtE (G := G) (V := V) E =
          (Quotient.mk'' (orbitRepE E).right : Work.ORBassSerre.orbitV G V) from rfl, hright]
      have hLleft : L.left = orbitRepV (G := G) (V := V) (Quotient.mk'' a) := by
        show (edgeLift (G := G) (V := V) E).left = orbitRepV (G := G) (V := V) (Quotient.mk'' a)
        rw [edgeLift_left, hsrcE]
      have hForbit : (Quotient.mk'' F : EdgeOrbit G V) = E := by
        show (Quotient.mk'' (h⁻¹ • u) : EdgeOrbit G V) = E
        change (Quotient.mk'' (h⁻¹ • u) : EdgeOrbit G V) = Quotient.mk'' u
        exact Quotient.sound ⟨h⁻¹, rfl⟩
      have hLorbit : (Quotient.mk'' L : EdgeOrbit G V) = E :=
        edgeLift_orbit (G := G) (V := V) E
      -- `F` is the translate of `L` by an element of `H`
      have hstep : ∃ g : G, g ∈ H ∧ F = g • L := by
        have hEq : (Quotient.mk'' L : EdgeOrbit G V) = Quotient.mk'' F :=
          hLorbit.trans hForbit.symm
        obtain ⟨g, hg⟩ := exists_smulTotal_of_mk_eq (G := G) (V := V) hEq
        refine ⟨g, ?_, hg.symm⟩
        have hfix : g ∈ MulAction.stabilizer G (orbitRepV (srcE (G := G) (V := V) E)) := by
          rw [MulAction.mem_stabilizer_iff, hsrcE]
          calc g • orbitRepV (G := G) (V := V) (Quotient.mk'' a) = g • L.left := by rw [hLleft]
            _ = (g • L).left := (smul_left_total g L).symm
            _ = F.left := by rw [hg]
            _ = orbitRepV (G := G) (V := V) (Quotient.mk'' a) := hFleft
        exact hstab_le (srcE (G := G) (V := V) E) hfix
      obtain ⟨g₀, hg₀H, hg₀eq⟩ := hstep
      refine ⟨h * g₀ * edgeElt (G := G) (V := V) E, ?_, ?_⟩
      · exact H.mul_mem (H.mul_mem hhH hg₀H) (hedge_mem E)
      · have hu_eq : u = (h * g₀) • L := by
          have hFL : h⁻¹ • u = g₀ • L := hg₀eq
          calc u = h • (h⁻¹ • u) := (smul_inv_smul h u).symm
            _ = h • (g₀ • L) := by rw [hFL]
            _ = (h * g₀) • L := by rw [mul_smul]
        have hLright : L.right =
            edgeElt (G := G) (V := V) E • orbitRepV (tgtE (G := G) (V := V) E) :=
          edgeLift_right (G := G) (V := V) E
        have huright : u.right =
            (h * g₀ * edgeElt (G := G) (V := V) E) • orbitRepV (G := G) (V := V) (Quotient.mk'' b) := by
          calc u.right = ((h * g₀) • L).right := by rw [hu_eq]
            _ = (h * g₀) • L.right := smul_right_total (h * g₀) L
            _ = (h * g₀) • (edgeElt (G := G) (V := V) E •
                  orbitRepV (tgtE (G := G) (V := V) E)) := by rw [hLright]
            _ = (h * g₀ * edgeElt (G := G) (V := V) E) •
                  orbitRepV (tgtE (G := G) (V := V) E) := by rw [← mul_smul]
            _ = (h * g₀ * edgeElt (G := G) (V := V) E) •
                  orbitRepV (G := G) (V := V) (Quotient.mk'' b) := by rw [htgtE]
        rw [← huright]
    have hWpath : ∀ {a b : V}, a ∈ W → Quiver.Path a b → b ∈ W := by
      intro a b ha p
      induction p with
      | nil => exact ha
      | cons p e ih => exact hWclosed ih e
    intro v
    have hbase : orbitRepV (G := G) (V := V) (Quotient.mk'' v) ∈ W :=
      ⟨1, H.one_mem, by rw [one_smul, orbitRepV_mk]⟩
    obtain ⟨p⟩ := hT.1 (orbitRepV (G := G) (V := V) (Quotient.mk'' v)) v
    exact hWpath hbase p
  -- (d) Hence `H` contains everything.
  have hHtop : H = ⊤ := by
    refine le_antisymm le_top ?_
    intro g _
    let v₀ : V := Classical.arbitrary V
    let A₀ : Work.ORBassSerre.orbitV G V := Quotient.mk'' v₀
    obtain ⟨h, hhH, hh⟩ := htrans (g • orbitRepV (G := G) (V := V) A₀)
    have hs : (Quotient.mk'' (g • orbitRepV (G := G) (V := V) A₀) :
        Work.ORBassSerre.orbitV G V) =
        Quotient.mk'' (orbitRepV (G := G) (V := V) A₀) :=
      Quotient.sound ⟨g, rfl⟩
    have hmk : (Quotient.mk'' (g • orbitRepV (G := G) (V := V) A₀) :
        Work.ORBassSerre.orbitV G V) = A₀ :=
      hs.trans (orbitRepV_mk (G := G) (V := V) A₀)
    rw [hmk] at hh
    have hgmem : h⁻¹ * g ∈ H := by
      refine hstab_le A₀ ?_
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hh, inv_smul_smul]
    have hmul : h * (h⁻¹ * g) ∈ H := H.mul_mem hhH hgmem
    rw [mul_inv_cancel_left] at hmul
    exact hmul
  exact ⟨X, by rw [← hH]; exact hHtop⟩

end Work.ORBassSerre.Action
