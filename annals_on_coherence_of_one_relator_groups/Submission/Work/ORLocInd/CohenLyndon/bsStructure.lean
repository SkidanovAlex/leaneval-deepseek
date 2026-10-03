import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.Action.Structure.Phi_surjective
import Submission.Work.ORLocInd.CohenLyndon.bsSetup
import Submission.Work.ORLocInd.CohenLyndon.bsLiftData
import Submission.Work.ORLocInd.CohenLyndon.bsJunctionBacktrack
import Submission.Work.ORLocInd.CohenLyndon.bsGeodesicLift

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **Bass--Serre structure theorem.** Let the group `Γ` act on a non-empty tree `V` without inversions and with all edge stabilisers trivial, and suppose that the quotient graph `V/Γ` is again a tree.  Then `Γ` is the free product of the stabilisers of a set of representatives `x i` of the vertex orbits.

This is the standard Bass--Serre structure theorem.  The classical proof: `V` is the Bass--Serre tree of the graph of groups `V/Γ` (trivial edge groups since edge stabilisers are trivial), and the fundamental group of a graph of groups whose underlying graph is a tree is the free product of the vertex groups.

The hypothesis `[Nonempty V]` is essential and cannot be dropped: for `V = ∅` all four hypotheses are vacuous (the empty graph is a "tree" by the connectedness/reduced-path definition used here) and the conclusion would force `Γ` to be trivial.

Useful existing machinery in this workspace:
* `Work.ORBassSerre.Action.Quotient.qpath_exists_lift`: every path in the quotient graph lifts to `V`;
* `Work.ORBassSerre.Action.Structure.{BSPresentation, BSWalk, BSReduction}`: the walk proof of the same statement in the finitely presented / cocompact case — in particular `BSWalk.elt_eq_one_of_reduced_closed` (a reduced closed path word whose image in `G` is trivial is trivial) is the engine for injectivity, and `BSReduction.exists_reduced` shows that every element is represented by a *reduced* closed path word.  Porting these to the general (non-cocompact, non-finitely-presented) setting — drop `[Fintype (orbitV Γ V)]`, `[Fintype (orbitE Γ V)]` and `PresData` — is one route;
* `Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree`.

A suggested decomposition: (1) the natural map `∗_i Stab (x i) → Γ` is surjective, i.e. `Subgroup.closure (⋃ i, (Stab (x i) : Set Γ)) = ⊤`; (2) it is injective (a Bass--Serre normal form / reduced-word argument using that `V/Γ` is a tree). -/
theorem bsStructure {Γ : Type u} {V : Type u} [Group Γ] [Quiver.{u, u} V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    [Nonempty V]
    (hT : Work.ORBassSerre.IsTree V) (hninv : Work.ORBassSerre.ActsWithoutInversions Γ V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer Γ e = ⊥)
    (hquot : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV Γ V)) :
    ∃ (Ω : Type u) (x : Ω → V),
      (∀ v : V, ∃ i : Ω, ∃ g : Γ, v = g • x i) ∧
      (∀ i j : Ω, (∃ g : Γ, x i = g • x j) → i = j) ∧
      ∃ e : Monoid.CoprodI (fun i : Ω => ↥(MulAction.stabilizer Γ (x i))) ≃* Γ,
        ∀ (i : Ω) (z : ↥(MulAction.stabilizer Γ (x i))),
          e (Monoid.CoprodI.of z) = (z : Γ) := by
  classical
  obtain ⟨x, hx, L, hL, hLrev⟩ := bsLiftData (Γ := Γ) (V := V) hT hninv hquot
  let hLend : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B := fun A B e => (hL A B e).2
  let hLorb : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      Quotient.mk'' (L A B e) = e.1 := fun A B e => (hL A B e).1
  have hGL : ∀ (A B : Work.ORBassSerre.orbitV Γ V),
      hT.geodesic (x A) (x B) = liftPath x L hLend A (hquot.geodesic A B) :=
    fun A B => bsGeodesicLift hT hquot x L hLend hLorb A B
  let G : Work.ORBassSerre.orbitV Γ V → Type u := fun A => ↥(MulAction.stabilizer Γ (x A))
  let φ : Monoid.CoprodI G →* Γ :=
    Monoid.CoprodI.lift (fun A => (MulAction.stabilizer Γ (x A)).subtype)
  have hφapp : ∀ (A : Work.ORBassSerre.orbitV Γ V) (z : G A),
      φ (Monoid.CoprodI.of z) = (z : Γ) := by
    intro A z
    rw [Monoid.CoprodI.lift_of]
    rfl
  have hgen : Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV Γ V,
      (MulAction.stabilizer Γ (x A) : Set Γ)) = ⊤ := by
    have h := Work.ORBassSerre.Action.Structure.closure_lifts_top_aux (G := Γ) (V := V) hT x hx
      (fun _ => (1 : Γ))
      (fun E => L (Work.ORBassSerre.Action.srcE E) (Work.ORBassSerre.Action.tgtE E)
        ⟨E, Work.ORBassSerre.Action.orbitRepE E,
          Work.ORBassSerre.Action.orbitRepE_mk E, rfl, rfl⟩)
      (fun E => (hL _ _ _).1) (fun E => (hL _ _ _).2.1)
      (fun E => by rw [(hL _ _ _).2.2, one_smul])
    have h2 : Subgroup.closure (Set.range (fun _ : Work.ORBassSerre.orbitE Γ V => (1 : Γ)))
        = ⊥ := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro a ⟨_, rfl⟩
        simp
      · exact bot_le
    rw [Subgroup.closure_union, h2, sup_bot_eq] at h
    exact h
  have hsurj : Function.Surjective φ := by
    have hle : Subgroup.closure (⋃ A, (MulAction.stabilizer Γ (x A) : Set Γ)) ≤ φ.range := by
      rw [Subgroup.closure_le]
      rintro g hg
      rw [Set.mem_iUnion] at hg
      obtain ⟨A, hgA⟩ := hg
      exact ⟨Monoid.CoprodI.of ⟨g, hgA⟩, hφapp A ⟨g, hgA⟩⟩
    rw [hgen] at hle
    exact MonoidHom.range_eq_top.mp (le_antisymm le_top hle)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    set w : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.equiv p with hw
    have hwprod : w.prod = p := Monoid.CoprodI.Word.equiv.left_inv p
    by_cases hemp : w.toList = []
    · have hwempty : w = Monoid.CoprodI.Word.empty :=
        Monoid.CoprodI.Word.ext (by rw [hemp]; rfl)
      rw [← hwprod, hwempty, Monoid.CoprodI.Word.prod_empty]
    · exfalso
      have hnpos : 0 < w.toList.length := by
        rcases Nat.eq_zero_or_pos w.toList.length with h | h
        · exact absurd (List.eq_nil_of_length_eq_zero h) hemp
        · exact h
      let lf : ℕ → Sigma G :=
        fun j => w.toList.get ⟨j % w.toList.length, Nat.mod_lt j hnpos⟩
      let Aj : ℕ → Work.ORBassSerre.orbitV Γ V := fun j => (lf j).1
      let gj : ℕ → Γ := fun j => ((lf j).2 : Γ)
      have hmem : ∀ j, lf j ∈ w.toList := fun j => List.get_mem _ _
      have hgmem : ∀ j, gj j ∈ MulAction.stabilizer Γ (x (Aj j)) := fun j => (lf j).2.2
      have hne : ∀ j, gj j ≠ 1 := by
        intro j h1
        exact w.ne_one (lf j) (hmem j) (Subtype.ext h1)
      have hmod : ∀ j, (j + w.toList.length) % w.toList.length
          = j % w.toList.length := by
        intro j
        rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
      have hlfper : ∀ j, lf (j + w.toList.length) = lf j := by
        intro j
        simp only [lf]
        exact congrArg (w.toList.get) (Fin.ext (hmod j))
      have hAper : ∀ j, Aj (j + w.toList.length) = Aj j :=
        fun j => congrArg Sigma.fst (hlfper j)
      have hget : ∀ j (hj : j < w.toList.length), lf j = w.toList[j] := by
        intro j hj
        simp only [lf]
        exact congrArg (w.toList.get) (Fin.ext (Nat.mod_eq_of_lt hj))
      have hAne : ∀ j, j + 1 < w.toList.length → Aj j ≠ Aj (j + 1) := by
        intro j hj h
        have hchain := (List.isChain_iff_getElem.mp w.chain_ne) j hj
        have h1 : (w.toList[j]).1 = (w.toList[j + 1]).1 := by
          have h2 : (lf j).1 = (lf (j + 1)).1 := h
          rwa [hget j (by omega), hget (j + 1) hj] at h2
        exact hchain h1
      let hs : ℕ → Γ := fun j => Nat.rec 1 (fun k ih => ih * gj k) j
      have hs_zero : hs 0 = 1 := rfl
      have hs_succ : ∀ j, hs (j + 1) = hs j * gj j := fun j => rfl
      have hs_prod : ∀ j, j ≤ w.toList.length →
          hs j = φ (List.prod ((w.toList.take j).map
            (fun l : Sigma G => Monoid.CoprodI.of l.2))) := by
        intro j hj
        induction j with
        | zero => rfl
        | succ k ih =>
          have hk : k < w.toList.length := by omega
          have htake : w.toList.take (k + 1) = w.toList.take k ++ [w.toList[k]] := by
            rw [List.take_succ, List.getElem?_eq_getElem hk]
            rfl
          rw [hs_succ k, ih (by omega), htake, List.map_append,
            List.prod_append, map_mul]
          rw [show List.prod (List.map (fun l : Sigma G => Monoid.CoprodI.of l.2)
              [w.toList[k]]) = Monoid.CoprodI.of (w.toList[k]).2 from rfl, hφapp]
          congr 1
          have h3 : gj k = ((w.toList[k]).2 : Γ) := by
            have h4 : lf k = w.toList[k] := hget k hk
            exact congrArg (fun l : Sigma G => ((l.2 : G l.1) : Γ)) h4
          rw [h3]
      have hsn : hs w.toList.length = 1 := by
        rw [hs_prod w.toList.length le_rfl, List.take_length]
        rw [show List.prod ((w.toList.map (fun l : Sigma G => Monoid.CoprodI.of l.2)))
            = Monoid.CoprodI.Word.prod w from rfl, hwprod]
        exact hp
      let zv : ℕ → V := fun j => hs j • x (Aj j)
      have hzv_succ : ∀ j, zv (j + 1) = hs j • (gj j • x (Aj (j + 1))) := by
        intro j
        show hs (j + 1) • x (Aj (j + 1)) = hs j • (gj j • x (Aj (j + 1)))
        rw [hs_succ, mul_smul]
      have hzv_self : ∀ j, gj j • x (Aj j) = x (Aj j) :=
        fun j => MulAction.mem_stabilizer_iff.mp (hgmem j)
      have hzvj : ∀ j, zv j = hs (j + 1) • x (Aj j) := by
        intro j
        show hs j • x (Aj j) = hs (j + 1) • x (Aj j)
        rw [hs_succ, mul_smul, hzv_self]
      have hpiece_inj : ∀ j, zv j = zv (j + 1) → Aj j = Aj (j + 1) := by
        intro j h
        have h1 : x (Aj j) = gj j • x (Aj (j + 1)) := by
          have h2 : hs j • x (Aj j) = hs j • (gj j • x (Aj (j + 1))) := by
            calc hs j • x (Aj j) = hs (j + 1) • x (Aj j) := by
                  rw [hs_succ, mul_smul, hzv_self]
              _ = zv j := (hzvj j).symm
              _ = zv (j + 1) := h
              _ = hs j • (gj j • x (Aj (j + 1))) := hzv_succ j
          simpa using congrArg (fun w : V => (hs j)⁻¹ • w) h2
        calc Aj j = (Quotient.mk'' (x (Aj j)) : Work.ORBassSerre.orbitV Γ V) :=
              (hx (Aj j)).symm
          _ = Quotient.mk'' (gj j • x (Aj (j + 1))) := by rw [h1]
          _ = Quotient.mk'' (x (Aj (j + 1))) := orbitV_mk_smul (Γ := Γ) (gj j) _
          _ = Aj (j + 1) := hx (Aj (j + 1))
      have hpiece_ne : ∀ j, j + 1 < w.toList.length → zv j ≠ zv (j + 1) :=
        fun j hj h => hAne j hj (hpiece_inj j h)
      have hzv_per : zv w.toList.length = zv 0 := by
        show hs w.toList.length • x (Aj w.toList.length) = hs 0 • x (Aj 0)
        have hA0 : x (Aj w.toList.length) = x (Aj 0) := by
          rw [show w.toList.length = 0 + w.toList.length from (Nat.zero_add _).symm, hAper 0]
        rw [hsn, hA0, hs_zero, one_smul]
      -- the key step: a closed walk of geodesics with no repeated consecutive vertices
      have key : ∀ m : ℕ, 1 ≤ m → m ≤ w.toList.length → zv m = zv 0 →
          (∀ j, j < m → zv j ≠ zv (j + 1)) → False := by
        intro m hm hmn hcl hne'
        have hred : ∀ j, j < m → (hT.geodesic (zv j) (zv (j + 1))).IsReduced :=
          fun j _ => hT.geodesic_isReduced _ _
        have hpos : ∀ j, j < m → 0 < (hT.geodesic (zv j) (zv (j + 1))).length :=
          fun j hj => geodesic_length_pos hT (hne' j hj)
        obtain ⟨j, hj, x', f, u', v', hd1, hd2⟩ :=
          bsJunctionBacktrack (V := V) hT m hm zv
            (fun j => hT.geodesic (zv j) (zv (j + 1))) hred hpos hcl
        have hj' : j < m := by omega
        have hd1' : hT.geodesic (zv j) (zv (j + 1)) = u'.cons f := hd1
        have hd2' : hT.geodesic (zv (j + 1)) (zv (j + 2))
            = (Quiver.reverse f).toPath.comp v' := hd2
        have hlen1 : 0 < (hT.geodesic (zv j) (zv (j + 1))).length := hpos j hj'
        have hlen2 : 0 < (hT.geodesic (zv (j + 1)) (zv (j + 2))).length := hpos (j + 1) hj
        have hlen2' : 0 < (hT.geodesic (zv (j + 2)) (zv (j + 1))).length := by
          rw [← geodesic_reverse hT (zv (j + 1)) (zv (j + 2))]
          rw [Work.ORBassSerre.Tree.Geodesic.length_reverse]
          exact hlen2
        have hlen2'' : 0 < ((hT.geodesic (zv (j + 1)) (zv (j + 2))).reverse).length := by
          rw [Work.ORBassSerre.Tree.Geodesic.length_reverse]
          exact hlen2
        -- the last arrow of the `j`-th piece and of the reversed `(j+1)`-st piece
        have hl1 : lastTotal (hT.geodesic (zv j) (zv (j + 1))) hlen1 = ⟨x', zv (j + 1), f⟩ := by
          calc lastTotal (hT.geodesic (zv j) (zv (j + 1))) hlen1
              = lastTotal (u'.cons f) (by rw [← hd1']; exact hlen1) :=
                lastTotal_congr hd1' hlen1 _
            _ = ⟨x', zv (j + 1), f⟩ := rfl
        have hrev : (hT.geodesic (zv (j + 1)) (zv (j + 2))).reverse
            = v'.reverse.comp f.toPath := by
          rw [hd2', reverse_toPath_comp, Quiver.reverse_reverse]
        have hl2rev : lastTotal ((hT.geodesic (zv (j + 1)) (zv (j + 2))).reverse) hlen2''
            = ⟨x', zv (j + 1), f⟩ := by
          calc lastTotal ((hT.geodesic (zv (j + 1)) (zv (j + 2))).reverse) hlen2''
              = lastTotal (v'.reverse.comp f.toPath) (by rw [← hrev]; exact hlen2'') :=
                lastTotal_congr hrev hlen2'' _
            _ = ⟨x', zv (j + 1), f⟩ := lastTotal_comp_toPath v'.reverse f _
        have hbridge : lastTotal ((hT.geodesic (zv (j + 1)) (zv (j + 2))).reverse) hlen2''
            = lastTotal (hT.geodesic (zv (j + 2)) (zv (j + 1))) hlen2' :=
          lastTotal_congr (geodesic_reverse hT (zv (j + 1)) (zv (j + 2))) hlen2'' hlen2'
        have hl2 : lastTotal (hT.geodesic (zv (j + 2)) (zv (j + 1))) hlen2'
            = ⟨x', zv (j + 1), f⟩ := by
          rw [← hbridge]; exact hl2rev
        -- the base geodesics are nonempty
        have hbase1 : 0 < (hT.geodesic (x (Aj j)) (x (Aj (j + 1)))).length := by
          rw [← length_geodesic_of_eq_smul (hT := hT) (a := x (Aj j)) (b := x (Aj (j + 1)))
            (a' := zv j) (b' := zv (j + 1)) (hs (j + 1)) (hzvj j).symm rfl]
          exact hlen1
        have hA1 : Aj j ≠ Aj (j + 1) := by
          intro hh
          have h0 : (hT.geodesic (x (Aj j)) (x (Aj (j + 1)))).length = 0 := by
            rw [hh, hT.geodesic_self]
            rfl
          omega
        have hb2 : hs (j + 2) • x (Aj (j + 1)) = zv (j + 1) := by
          show hs (j + 2) • x (Aj (j + 1)) = hs (j + 1) • x (Aj (j + 1))
          rw [hs_succ, mul_smul, hzv_self (j + 1)]
        by_cases hAA : Aj (j + 1) = Aj (j + 2)
        · -- then the `(j+1)`-st piece would be empty
          exfalso
          have h0 : (hT.geodesic (x (Aj (j + 1))) (x (Aj (j + 2)))).length = 0 := by
            rw [hAA, hT.geodesic_self]
            rfl
          have hbase2' : 0 < (hT.geodesic (x (Aj (j + 1))) (x (Aj (j + 2)))).length := by
            rw [← length_geodesic_of_eq_smul (hT := hT) (a := x (Aj (j + 1))) (b := x (Aj (j + 2)))
              (a' := zv (j + 1)) (b' := zv (j + 2)) (hs (j + 2)) hb2 rfl]
            exact hlen2
          omega
        · have hq1 : 0 < (hquot.geodesic (Aj j) (Aj (j + 1))).length :=
            geodesic_length_pos hquot hA1
          have hq2 : 0 < (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))).length :=
            geodesic_length_pos hquot (Ne.symm hAA)
          have id1 := lastTotal_geodesic_lift (hT := hT) (hquot := hquot) (x := x) (L := L)
            (hL := hLend) (hGL := hGL) (A := Aj j) (B := Aj (j + 1)) hq1 (hs (j + 1))
            (a := zv j) (b := zv (j + 1)) (hzvj j).symm rfl hlen1
          have id2 := lastTotal_geodesic_lift (hT := hT) (hquot := hquot) (x := x) (L := L)
            (hL := hLend) (hGL := hGL) (A := Aj (j + 2)) (B := Aj (j + 1)) hq2 (hs (j + 2))
            (a := zv (j + 2)) (b := zv (j + 1)) rfl hb2 hlen2'
          have heq : hs (j + 1) • L (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2
              = hs (j + 2) • L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2 := by
            rw [← id1, hl1, ← hl2, id2]
          have hsm : hs (j + 1) • (gj (j + 1) • L
                (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2)
              = hs (j + 2) • L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2 := by
            rw [show hs (j + 2) = hs (j + 1) * gj (j + 1) from hs_succ (j + 1)]
            exact (mul_smul (hs (j + 1)) (gj (j + 1))
              (L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2)).symm
          have heq2 : L (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2
              = gj (j + 1) • L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2 :=
            MulAction.injective (hs (j + 1)) (heq.trans hsm.symm)
          have horb : (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2.1
              = (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2.1 := by
            have h := congrArg (fun t : Quiver.Total V =>
              (Quotient.mk'' t : Work.ORBassSerre.orbitE Γ V)) heq2
            rw [hLorb (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).1 (Aj (j + 1))
                (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2, orbit_mk_smul,
              hLorb (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1 (Aj (j + 1))
                (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2] at h
            exact h
          have hE1 : (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).1
              = (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1 := by
            have h := congrArg (Work.ORBassSerre.Action.srcE (G := Γ) (V := V)) horb
            rw [srcE_hom (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2,
              srcE_hom (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2] at h
            exact h
          have hT12 : L (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).1 (Aj (j + 1))
                (lastHom (hquot.geodesic (Aj j) (Aj (j + 1))) hq1).2
              = L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1 (Aj (j + 1))
                (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2 := by
            refine total_eq_of_isTree hT ?_ ?_
            · rw [(hLend _ _ _).1, (hLend _ _ _).1]
              exact congrArg x hE1
            · rw [(hLend _ _ _).2, (hLend _ _ _).2]
          have hg1 : gj (j + 1) = 1 := by
            have hfin : gj (j + 1) • L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                  (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2
                = L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                  (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2 := by
              rw [← heq2, hT12]
            have hmem2 : gj (j + 1) ∈ MulAction.stabilizer Γ
                (L (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).1
                  (Aj (j + 1)) (lastHom (hquot.geodesic (Aj (j + 2)) (Aj (j + 1))) hq2).2) :=
              hfin
            rw [hedge] at hmem2
            simpa using hmem2
          exact hne (j + 1) hg1
      -- the closed walk: `zv` is periodic of period `w.toList.length`
      by_cases hn1 : w.toList.length = 1
      · have h1 : gj 0 = 1 := by
          have h2 : hs 1 = 1 := by rw [← hn1]; exact hsn
          rw [show hs 1 = hs 0 * gj 0 from hs_succ 0, hs_zero, one_mul] at h2
          exact h2
        exact hne 0 h1
      · have hn2 : 2 ≤ w.toList.length := by omega
        by_cases hcase : zv (w.toList.length - 1) = zv 0
        · refine key (w.toList.length - 1) (by omega) (by omega) hcase (fun j hj => ?_)
          exact hpiece_ne j (by omega)
        · refine key w.toList.length (by omega) le_rfl hzv_per (fun j hj => ?_)
          rcases Nat.lt_or_eq_of_le (by omega : j + 1 ≤ w.toList.length) with hlt | heq
          · exact hpiece_ne j hlt
          · have hj' : j = w.toList.length - 1 := by omega
            rw [hj', show w.toList.length - 1 + 1 = w.toList.length from by omega, hzv_per]
            exact hcase
  refine ⟨Work.ORBassSerre.orbitV Γ V, x, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨g, hg⟩ := Work.ORBassSerre.Action.exists_smul_of_mk_eq (G := Γ) (V := V)
      (x := x (Quotient.mk'' v)) (y := v) ((hx (Quotient.mk'' v)).trans rfl)
    exact ⟨Quotient.mk'' v, g, hg.symm⟩
  · intro A B h
    obtain ⟨g, hg⟩ := h
    exact (hx A).symm.trans ((congrArg Quotient.mk'' hg).trans
      ((orbitV_mk_smul (Γ := Γ) g (x B)).trans (hx B)))
  · refine ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, ?_⟩
    intro A z
    exact hφapp A z

end Work.ORLocInd.CohenLyndon
