import Mathlib
import Submission.Work.RatHurewicz.SphereSuspDefs
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval Topology.Homotopy
open Work.StemsB (PathSpace evalOne)

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-!
# A connector on the ambient space trivialises the relative homotopy groups

Let `i : C(A,X)` be an inclusion (or any map) and suppose that the *ambient* space `X` carries a
**connector** (`Work.RatHurewicz.Connector`): a continuous choice of paths between any two points of
`X`, degenerating on the diagonal, `c : X × X × I → X` with `c (p,q,0) = p`, `c (p,q,1) = q` and
`c (p,p,t) = p`.

The homotopy fibre `E = homotopyFibre i a₀` of `i` over `a₀` is the space of pairs `(a,γ)` with `γ` a
path in `X` from `i a₀` to `i a`.  Using the connector, the projection `E → A`, `(a,γ) ↦ a`, admits
the section `a ↦ (a, c (i a₀, i a, ·))`, and the interpolating homotopy
`(a,γ,s) ↦ (a, t ↦ c (γ t, c (i a₀, i a, ·) t, s))` — well defined and continuous thanks to the
diagonal property — shows that the projection is a homotopy equivalence.  Hence the homotopy groups
of `E` are those of `A`: the relative groups of the pair vanish as soon as those of `A` do.

The connector is used on the *ambient* space `X` only, so no hypothesis at all is imposed on `A`;
this is what allows the statement to be applied to a pair `(B, B ∩ C)` in a sphere with `B` a disc
(`B ∩ C ≃ Sⁿ` is not contractible, so it carries no connector of its own).
-/

section Connector

variable (hc : Connector X)

/-- The path from `p` to `q` supplied by the connector, as a continuous map `I → X`. -/
def connPathCM (p q : X) : C(I, X) where
  toFun t := hc.c (p, q, t)
  continuous_toFun :=
    hc.c.continuous.comp
      (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id))

@[simp] theorem connPathCM_apply (p q : X) (t : I) : connPathCM hc p q t = hc.c (p, q, t) := rfl

theorem connPathCM_zero (p q : X) : connPathCM hc p q 0 = p := hc.zero p q

theorem connPathCM_one (p q : X) : connPathCM hc p q 1 = q := hc.one p q

theorem connPathCM_self (p : X) (t : I) : connPathCM hc p p t = p := hc.diag p t

theorem continuous_connPathCM_left (q : X) : Continuous fun p : X => connPathCM hc p q := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact hc.c.continuous.comp
    (Continuous.prodMk continuous_fst (Continuous.prodMk continuous_const continuous_snd))

theorem continuous_connPathCM_right (p : X) : Continuous fun q : X => connPathCM hc p q := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact hc.c.continuous.comp
    (Continuous.prodMk continuous_const (Continuous.prodMk continuous_fst continuous_snd))

end Connector

section Fibre

variable (i : C(A, X)) (a₀ : A)

/-- The `A`-coordinate of a point of the homotopy fibre, as a continuous map. -/
theorem continuous_homotopyFibre_val : Continuous fun p : homotopyFibre i a₀ => p.1.1 :=
  continuous_fst.comp continuous_subtype_val

/-- The path component of a point of the homotopy fibre, as a continuous map. -/
theorem continuous_homotopyFibre_pathCM :
    Continuous fun p : homotopyFibre i a₀ => p.1.2.1 :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

/-- A point of the homotopy fibre starts its path at the base point. -/
theorem homotopyFibre_path_zero (p : homotopyFibre i a₀) : p.1.2.1 0 = i a₀ := p.1.2.2

/-- A point of the homotopy fibre ends its path at its `A`-coordinate. -/
theorem homotopyFibre_path_one (p : homotopyFibre i a₀) : p.1.2.1 1 = i p.1.1 := p.2

end Fibre

section ConnectorSection

variable (hc : Connector X) (i : C(A, X)) (a₀ : A)

/-- The section of the projection `homotopyFibre i a₀ → A` given by the connector: the point `a`
is sent to `(a, c (i a₀, i a, ·))`. -/
def connSection (a : A) : homotopyFibre i a₀ :=
  ⟨(a, ⟨connPathCM hc (i a₀) (i a), hc.zero (i a₀) (i a)⟩), hc.one (i a₀) (i a)⟩

@[simp] theorem connSection_fst (a : A) : (connSection hc i a₀ a).1.1 = a := rfl

theorem continuous_connSection : Continuous fun a : A => connSection hc i a₀ a := by
  refine Continuous.subtype_mk (Continuous.prodMk continuous_id ?_)
    (fun a => hc.one (i a₀) (i a))
  exact Continuous.subtype_mk ((continuous_connPathCM_right hc (i a₀)).comp i.continuous)
    (fun a => hc.zero (i a₀) (i a))

/-- The interpolating path of the connector homotopy, as a continuous map `I → X`. -/
def connHomotopyCM (x : homotopyFibre i a₀ × I) : C(I, X) where
  toFun t := hc.c (x.1.1.2.1 t, connPathCM hc (i a₀) (i x.1.1.1) t, x.2)
  continuous_toFun :=
    hc.c.continuous.comp (Continuous.prodMk (x.1.1.2.1).continuous
      (Continuous.prodMk (connPathCM hc (i a₀) (i x.1.1.1)).continuous continuous_const))

@[simp] theorem connHomotopyCM_apply (x : homotopyFibre i a₀ × I) (t : I) :
    connHomotopyCM hc i a₀ x t
      = hc.c (x.1.1.2.1 t, connPathCM hc (i a₀) (i x.1.1.1) t, x.2) := rfl

theorem connHomotopyCM_zero (x : homotopyFibre i a₀ × I) :
    connHomotopyCM hc i a₀ x 0 = i a₀ := by
  rw [connHomotopyCM_apply, connPathCM_zero, homotopyFibre_path_zero i a₀ x.1]
  exact hc.diag (i a₀) x.2

/-- The interpolating path, as an element of the path space of `X` based at `i a₀`. -/
def connHomotopyPathSpace (x : homotopyFibre i a₀ × I) : PathSpace X (i a₀) :=
  ⟨connHomotopyCM hc i a₀ x, connHomotopyCM_zero hc i a₀ x⟩

theorem continuous_connHomotopyVal :
    Continuous fun q : (homotopyFibre i a₀ × I) × I =>
      hc.c (q.1.1.1.2.1 q.2, connPathCM hc (i a₀) (i q.1.1.1.1) q.2, q.1.2) := by
  refine hc.c.continuous.comp (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_))
  · exact continuous_eval.comp (((continuous_homotopyFibre_pathCM i a₀).comp
      (continuous_fst.comp continuous_fst)).prodMk continuous_snd)
  · exact continuous_eval.comp (((continuous_connPathCM_right hc (i a₀)).comp
      (i.continuous.comp ((continuous_homotopyFibre_val i a₀).comp
        (continuous_fst.comp continuous_fst)))).prodMk continuous_snd)
  · exact continuous_snd.comp continuous_fst

theorem continuous_connHomotopyPathSpace :
    Continuous fun x : homotopyFibre i a₀ × I => connHomotopyPathSpace hc i a₀ x := by
  change Continuous fun x : homotopyFibre i a₀ × I =>
    (⟨connHomotopyCM hc i a₀ x, connHomotopyCM_zero hc i a₀ x⟩ :
      {γ : C(I, X) // γ 0 = i a₀})
  refine Continuous.subtype_mk ?_ (fun x => connHomotopyCM_zero hc i a₀ x)
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_connHomotopyVal hc i a₀

/-- The endpoint of the interpolating path. -/
theorem connHomotopyPathSpace_end (x : homotopyFibre i a₀ × I) :
    (evalOne X (i a₀)) (connHomotopyPathSpace hc i a₀ x) = i x.1.1.1 := by
  show connHomotopyCM hc i a₀ x 1 = i x.1.1.1
  rw [connHomotopyCM_apply, connPathCM_one, homotopyFibre_path_one i a₀ x.1]
  exact hc.diag (i x.1.1.1) x.2

/-- The homotopy of the fibre `E → A`: at parameter `0` the identity, at parameter `1` the
section `connSection`. -/
def connHomotopyFun (x : homotopyFibre i a₀ × I) : homotopyFibre i a₀ :=
  ⟨(x.1.1.1, connHomotopyPathSpace hc i a₀ x),
    connHomotopyPathSpace_end hc i a₀ x⟩

theorem continuous_connHomotopyFun : Continuous (connHomotopyFun hc i a₀) := by
  refine Continuous.subtype_mk
    (Continuous.prodMk ((continuous_homotopyFibre_val i a₀).comp continuous_fst) ?_)
    (fun x => connHomotopyPathSpace_end hc i a₀ x)
  exact continuous_connHomotopyPathSpace hc i a₀

theorem connHomotopyFun_zero (x : homotopyFibre i a₀) :
    connHomotopyFun hc i a₀ (x, 0) = x := by
  refine Subtype.ext ?_
  refine Prod.ext rfl ?_
  refine Subtype.ext ?_
  refine ContinuousMap.ext ?_
  intro t
  show hc.c (x.1.2.1 t, connPathCM hc (i a₀) (i x.1.1) t, (0 : I)) = x.1.2.1 t
  rw [hc.zero]

theorem connHomotopyFun_one (x : homotopyFibre i a₀) :
    connHomotopyFun hc i a₀ (x, 1) = connSection hc i a₀ x.1.1 := by
  refine Subtype.ext ?_
  refine Prod.ext rfl ?_
  refine Subtype.ext ?_
  refine ContinuousMap.ext ?_
  intro t
  show hc.c (x.1.2.1 t, connPathCM hc (i a₀) (i x.1.1) t, (1 : I))
    = connPathCM hc (i a₀) (i x.1.1) t
  rw [hc.one]

/-- **The homotopy fibre of `i : A → X` is homotopy equivalent to `A` when `X` carries a
connector.**  The homotopy equivalence is the projection `(a,γ) ↦ a`, with inverse the section
`a ↦ (a, c (i a₀, i a, ·))`. -/
def relPiHomotopyEquiv : ContinuousMap.HomotopyEquiv (homotopyFibre i a₀) A where
  toFun := homotopyFibreFst i a₀
  invFun := ⟨connSection hc i a₀, continuous_connSection hc i a₀⟩
  left_inv := ⟨{
    toContinuousMap := {
      toFun := fun p : I × homotopyFibre i a₀ =>
        connHomotopyFun hc i a₀ (p.2, unitInterval.symm p.1)
      continuous_toFun := (continuous_connHomotopyFun hc i a₀).comp
        (continuous_snd.prodMk (unitInterval.continuous_symm.comp continuous_fst)) }
    map_zero_left := fun x => by
      show connHomotopyFun hc i a₀ (x, unitInterval.symm (0 : I)) = connSection hc i a₀ x.1.1
      rw [unitInterval.symm_zero]
      exact connHomotopyFun_one hc i a₀ x
    map_one_left := fun x => by
      show connHomotopyFun hc i a₀ (x, unitInterval.symm (1 : I)) = x
      rw [unitInterval.symm_one]
      exact connHomotopyFun_zero hc i a₀ x }⟩
  right_inv := by
    have h : (homotopyFibreFst i a₀).comp
        (⟨connSection hc i a₀, continuous_connSection hc i a₀⟩ : C(A, homotopyFibre i a₀))
        = ContinuousMap.id A := by
      ext a
      rfl
    rw [h]

include hc in
/-- **A connector on the ambient space turns the connectivity of `A` into the vanishing of the
relative groups.**  Indeed the homotopy fibre of `i` is homotopy equivalent to `A`
(`relPiHomotopyEquiv`), so its homotopy groups are those of `A`. -/
theorem relPiVanishingOfConnector (e : ℕ)
    (hA : Subsingleton (HomotopyGroup (Fin e) A a₀)) :
    Subsingleton (RelHomotopyGroup i a₀ e) := by
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    let e0 := HomotopyGroup.pi0EquivZerothHomotopy (X := A) (x := a₀)
    have hZ : Subsingleton (ZerothHomotopy A) :=
      ⟨fun x y => e0.symm.injective (hA.allEq (e0.symm x) (e0.symm y))⟩
    have hZE : Subsingleton (ZerothHomotopy (homotopyFibre i a₀)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv (relPiHomotopyEquiv hc i a₀) hZ
    refine ⟨fun x y => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := homotopyFibre i a₀)
      (x := homotopyFibreBasepoint i a₀)).injective (hZE.allEq _ _)
  · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (e' + 1))
      (relPiHomotopyEquiv hc i a₀) (homotopyFibreBasepoint i a₀)
    have hbase : (relPiHomotopyEquiv hc i a₀).toFun (homotopyFibreBasepoint i a₀) = a₀ := rfl
    have htarget : Subsingleton (HomotopyGroup (Fin (e' + 1)) A
        ((relPiHomotopyEquiv hc i a₀).toFun (homotopyFibreBasepoint i a₀))) := by
      rw [hbase]
      exact hA
    refine ⟨fun x y => ?_⟩
    exact me.injective (htarget.allEq (me x) (me y))

end ConnectorSection

end

end Work.RatHurewicz
