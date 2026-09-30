import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.StemsB.PiMap

/-!
# The two descriptions of the pair `(B, B ∩ C)`

The hypotheses of `Work.RatHurewicz.excisionRelPiVanishing` are stated in terms of the inclusion
`interInclLeft B C : ↥(B ∩ C) ↪ ↥B` of the *subtype* `B ∩ C` of `X` into the subtype `B` of `X`.
The machinery of `Submission/Work/RatHurewicz/Triad/` works with the pair seen from inside `↥B`,
i.e. with the subset `interB B C = {y : ↥B | (y : X) ∈ B ∩ C}` of `↥B` and the inclusion
`setIncl (interB B C) : ↥(interB B C) ↪ ↥B`.

The two inclusions are the same map up to the canonical identification of `↥(B ∩ C)` with
`↥(interB B C)`, so their homotopy fibres are the same space up to the shape of the subtype.  This
file records the transfer of the vanishing of the relative groups between the two models: it is what
allows the single-basepoint hypotheses of the target to be fed to the restricted compression
criterion `Work.RatHurewicz.compressRelBd_of_relPiVanishing`, which is stated for `setIncl`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X}

/-- The subset of `↥B` whose elements are the points of `B ∩ C`. -/
def interB (B C : Set X) : Set ↥B := {y | (y : X) ∈ B ∩ C}

/-- The base point of `↥(interB B C)` attached to a point `a ∈ B ∩ C`. -/
def interBPoint (a : ↥(B ∩ C)) : ↥(interB B C) := ⟨⟨a.1, a.2.1⟩, a.2⟩

@[simp]
theorem interBPoint_coe (a : ↥(B ∩ C)) :
    ((interBPoint a : ↥(interB B C)) : ↥B) = interInclLeft B C a := rfl

@[simp]
theorem setIncl_interB_point (a : ↥(B ∩ C)) :
    setIncl (interB B C) (interBPoint a) = interInclLeft B C a := rfl

@[simp]
theorem setIncl_interB_of_point {a : ↥(B ∩ C)} (q : ↥(interB B C)) :
    setIncl (interB B C) q = (q.1 : ↥B) := rfl

/-- **The comparison of the two models of the pair `(B, B∩C)`**: the "same data" map from the
homotopy fibre of `B ∩ C ↪ B` (with `B ∩ C` the subtype of `X`) to the homotopy fibre of
`interB B C ↪ ↥B`. -/
def fibreCompare (a : ↥(B ∩ C)) :
    C(homotopyFibre (interInclLeft B C) a, homotopyFibre (setIncl (interB B C)) (interBPoint a)) where
  toFun p := ⟨(interBPoint p.1.1, p.1.2), by
    have hp := p.2
    simp only [setIncl, interInclLeft] at hp ⊢
    exact hp⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact Continuous.subtype_mk
        ((interInclLeft B C).continuous.comp (continuous_fst.comp continuous_subtype_val)) _
    · fun_prop

/-- The inverse comparison, on the underlying data. -/
def fibreCompareInv (a : ↥(B ∩ C)) :
    C(homotopyFibre (setIncl (interB B C)) (interBPoint a),
      homotopyFibre (interInclLeft B C) a) where
  toFun q := ⟨(⟨q.1.1.1.1, q.1.1.2⟩, q.1.2), by
    have hq := q.2
    simp only [setIncl, interInclLeft] at hq ⊢
    exact hq⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · fun_prop
    · fun_prop

theorem fibreCompare_comp_inv (a : ↥(B ∩ C)) :
    (fibreCompare a).comp (fibreCompareInv a) = ContinuousMap.id _ := by
  ext q
  rfl

theorem inv_comp_fibreCompare (a : ↥(B ∩ C)) :
    (fibreCompareInv a).comp (fibreCompare a) = ContinuousMap.id _ := by
  ext p
  rfl

theorem fibreCompare_basepoint (a : ↥(B ∩ C)) :
    fibreCompare a (homotopyFibreBasepoint (interInclLeft B C) a)
      = homotopyFibreBasepoint (setIncl (interB B C)) (interBPoint a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rfl

theorem fibreCompareInv_basepoint (a : ↥(B ∩ C)) :
    fibreCompareInv a (homotopyFibreBasepoint (setIncl (interB B C)) (interBPoint a))
      = homotopyFibreBasepoint (interInclLeft B C) a := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- **The vanishing of the relative groups transfers between the two models of the pair
`(B, B ∩ C)`.** -/
theorem subsingleton_relPiVanishing_interB {a : ↥(B ∩ C)} {k : ℕ}
    (h : Subsingleton (RelHomotopyGroup (interInclLeft B C) a k)) :
    Subsingleton (RelHomotopyGroup (setIncl (interB B C)) (interBPoint a) k) := by
  have hsec : ∀ q : homotopyFibre (setIncl (interB B C)) (interBPoint a),
      fibreCompare a (fibreCompareInv a q) = q := fun q =>
    congrArg (fun f : C(_, _) => f q) (fibreCompare_comp_inv a)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `π₀`: the comparison is surjective, and a surjective image of a connected space is connected
    subst hk
    haveI : PathConnectedSpace (homotopyFibre (interInclLeft B C) a) :=
      pathConnectedSpace_of_subsingleton_pi_zero (homotopyFibreBasepoint (interInclLeft B C) a) h
    haveI : PathConnectedSpace (homotopyFibre (setIncl (interB B C)) (interBPoint a)) :=
      PathConnectedSpace.mk ⟨homotopyFibreBasepoint (setIncl (interB B C)) (interBPoint a)⟩
        (fun u v => by
          obtain ⟨γ⟩ := PathConnectedSpace.joined (fibreCompareInv a u) (fibreCompareInv a v)
          exact ⟨(γ.map (fibreCompare a).continuous).cast (hsec u).symm (hsec v).symm⟩)
    let ex := HomotopyGroup.pi0EquivZerothHomotopy
      (X := homotopyFibre (setIncl (interB B C)) (interBPoint a))
      (x := homotopyFibreBasepoint (setIncl (interB B C)) (interBPoint a))
    exact ⟨fun u v => ex.injective (Subsingleton.elim (ex u) (ex v))⟩
  · -- positive degrees: the comparison has a section, so its `πmap` is surjective up to the
    -- transport of the base point
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    set bp := homotopyFibreBasepoint (setIncl (interB B C)) (interBPoint a) with hbp
    have hcompw : ∀ w : HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (setIncl (interB B C)) (interBPoint a)) bp,
        homotopyGroupCast (hsec bp) k'
          (πmap ((fibreCompare a).comp (fibreCompareInv a)) k' bp w) = w := by
      intro w
      have h1 := πmap_congr (fibreCompare_comp_inv a) k' bp w
      rw [πmap_id_apply] at h1
      rw [show congrArg (fun k => k bp) (fibreCompare_comp_inv a) = hsec bp from
        Subsingleton.elim _ _] at h1
      exact h1
    have hsurj : Function.Surjective (fun w : HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (interInclLeft B C) a) (fibreCompareInv a bp) =>
        homotopyGroupCast (hsec bp) k'
          (πmap (fibreCompare a) k' (fibreCompareInv a bp) w)) := by
      intro u
      refine ⟨πmap (fibreCompareInv a) k' bp (homotopyGroupCast (hsec bp).symm k' u), ?_⟩
      beta_reduce
      have h2 := hcompw (homotopyGroupCast (hsec bp).symm k' u)
      rw [show πmap ((fibreCompare a).comp (fibreCompareInv a)) k' bp
            (homotopyGroupCast (hsec bp).symm k' u)
          = πmap (fibreCompare a) k' (fibreCompareInv a bp)
            (πmap (fibreCompareInv a) k' bp (homotopyGroupCast (hsec bp).symm k' u))
        from πmap_comp_apply (fibreCompareInv a) (fibreCompare a) k' bp _] at h2
      rw [h2]
      exact (homotopyGroupCast (hsec bp) k').apply_symm_apply u
    have hsub : Subsingleton (HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (interInclLeft B C) a) (fibreCompareInv a bp)) := by
      rw [fibreCompareInv_basepoint a]
      exact h
    have hmain : Subsingleton (HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (setIncl (interB B C)) (interBPoint a)) bp) := by
      rw [← hsec bp]
      exact ⟨fun u v => by
        obtain ⟨u', hu'⟩ := hsurj u
        obtain ⟨v', hv'⟩ := hsurj v
        rw [← hu', ← hv']
        exact congrArg (fun w => homotopyGroupCast (hsec bp) k'
          (πmap (fibreCompare a) k' (fibreCompareInv a bp) w)) (hsub.elim u' v')⟩
    exact hmain

end

end Work.RatHurewicz
