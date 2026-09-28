import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.StemsB.PiMap

/-!
# The two descriptions of the pair `(C, B ∩ C)`

This is the mirror image of `Submission/Work/RatHurewicz/excisionSubtypeBridge.lean`: the
hypotheses of `Work.RatHurewicz.excisionRelPiVanishing` for the second piece `C` of the triad are
stated for the inclusion `interInclRight B C : ↥(B ∩ C) ↪ ↥C`, while the compression criterion
`Work.RatHurewicz.compressRelBd_of_relPiVanishing` is stated for `setIncl` of a subset of `↥C`.
The vanishing of the relative groups transfers between the two models, exactly as for `(B, B∩C)`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X}

/-- The subset of `↥C` whose elements are the points of `B ∩ C`. -/
def interC (B C : Set X) : Set ↥C := {y | (y : X) ∈ B ∩ C}

/-- The base point of `↥(interC B C)` attached to a point `a ∈ B ∩ C`. -/
def interCPoint (a : ↥(B ∩ C)) : ↥(interC B C) := ⟨⟨a.1, a.2.2⟩, a.2⟩

@[simp]
theorem interCPoint_coe (a : ↥(B ∩ C)) :
    ((interCPoint a : ↥(interC B C)) : ↥C) = interInclRight B C a := rfl

@[simp]
theorem setIncl_interC_point (a : ↥(B ∩ C)) :
    setIncl (interC B C) (interCPoint a) = interInclRight B C a := rfl

@[simp]
theorem setIncl_interC_of_point {a : ↥(B ∩ C)} (q : ↥(interC B C)) :
    setIncl (interC B C) q = (q.1 : ↥C) := rfl

/-- **The comparison of the two models of the pair `(B, B∩C)`**: the "same data" map from the
homotopy fibre of `B ∩ C ↪ B` (with `B ∩ C` the subtype of `X`) to the homotopy fibre of
`interC B C ↪ ↥C`. -/
def fibreCompareC (a : ↥(B ∩ C)) :
    C(homotopyFibre (interInclRight B C) a, homotopyFibre (setIncl (interC B C)) (interCPoint a)) where
  toFun p := ⟨(interCPoint p.1.1, p.1.2), by
    have hp := p.2
    simp only [setIncl, interInclRight] at hp ⊢
    exact hp⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact Continuous.subtype_mk
        ((interInclRight B C).continuous.comp (continuous_fst.comp continuous_subtype_val)) _
    · fun_prop

/-- The inverse comparison, on the underlying data. -/
def fibreCompareCInvC (a : ↥(B ∩ C)) :
    C(homotopyFibre (setIncl (interC B C)) (interCPoint a),
      homotopyFibre (interInclRight B C) a) where
  toFun q := ⟨(⟨q.1.1.1.1, q.1.1.2⟩, q.1.2), by
    have hq := q.2
    simp only [setIncl, interInclRight] at hq ⊢
    exact hq⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · fun_prop
    · fun_prop

theorem fibreCompareC_comp_inv (a : ↥(B ∩ C)) :
    (fibreCompareC a).comp (fibreCompareCInvC a) = ContinuousMap.id _ := by
  ext q
  rfl

theorem inv_comp_fibreCompareC (a : ↥(B ∩ C)) :
    (fibreCompareCInvC a).comp (fibreCompareC a) = ContinuousMap.id _ := by
  ext p
  rfl

theorem fibreCompareC_basepoint (a : ↥(B ∩ C)) :
    fibreCompareC a (homotopyFibreBasepoint (interInclRight B C) a)
      = homotopyFibreBasepoint (setIncl (interC B C)) (interCPoint a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rfl

theorem fibreCompareCInvC_basepoint (a : ↥(B ∩ C)) :
    fibreCompareCInvC a (homotopyFibreBasepoint (setIncl (interC B C)) (interCPoint a))
      = homotopyFibreBasepoint (interInclRight B C) a := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- **The vanishing of the relative groups transfers between the two models of the pair
`(B, B ∩ C)`.** -/
theorem subsingleton_relPiVanishing_interC {a : ↥(B ∩ C)} {k : ℕ}
    (h : Subsingleton (RelHomotopyGroup (interInclRight B C) a k)) :
    Subsingleton (RelHomotopyGroup (setIncl (interC B C)) (interCPoint a) k) := by
  have hsec : ∀ q : homotopyFibre (setIncl (interC B C)) (interCPoint a),
      fibreCompareC a (fibreCompareCInvC a q) = q := fun q =>
    congrArg (fun f : C(_, _) => f q) (fibreCompareC_comp_inv a)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `π₀`: the comparison is surjective, and a surjective image of a connected space is connected
    subst hk
    haveI : PathConnectedSpace (homotopyFibre (interInclRight B C) a) :=
      pathConnectedSpace_of_subsingleton_pi_zero (homotopyFibreBasepoint (interInclRight B C) a) h
    haveI : PathConnectedSpace (homotopyFibre (setIncl (interC B C)) (interCPoint a)) :=
      PathConnectedSpace.mk ⟨homotopyFibreBasepoint (setIncl (interC B C)) (interCPoint a)⟩
        (fun u v => by
          obtain ⟨γ⟩ := PathConnectedSpace.joined (fibreCompareCInvC a u) (fibreCompareCInvC a v)
          exact ⟨(γ.map (fibreCompareC a).continuous).cast (hsec u).symm (hsec v).symm⟩)
    let ex := HomotopyGroup.pi0EquivZerothHomotopy
      (X := homotopyFibre (setIncl (interC B C)) (interCPoint a))
      (x := homotopyFibreBasepoint (setIncl (interC B C)) (interCPoint a))
    exact ⟨fun u v => ex.injective (Subsingleton.elim (ex u) (ex v))⟩
  · -- positive degrees: the comparison has a section, so its `πmap` is surjective up to the
    -- transport of the base point
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    set bp := homotopyFibreBasepoint (setIncl (interC B C)) (interCPoint a) with hbp
    have hcompw : ∀ w : HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (setIncl (interC B C)) (interCPoint a)) bp,
        homotopyGroupCast (hsec bp) k'
          (πmap ((fibreCompareC a).comp (fibreCompareCInvC a)) k' bp w) = w := by
      intro w
      have h1 := πmap_congr (fibreCompareC_comp_inv a) k' bp w
      rw [πmap_id_apply] at h1
      rw [show congrArg (fun k => k bp) (fibreCompareC_comp_inv a) = hsec bp from
        Subsingleton.elim _ _] at h1
      exact h1
    have hsurj : Function.Surjective (fun w : HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (interInclRight B C) a) (fibreCompareCInvC a bp) =>
        homotopyGroupCast (hsec bp) k'
          (πmap (fibreCompareC a) k' (fibreCompareCInvC a bp) w)) := by
      intro u
      refine ⟨πmap (fibreCompareCInvC a) k' bp (homotopyGroupCast (hsec bp).symm k' u), ?_⟩
      beta_reduce
      have h2 := hcompw (homotopyGroupCast (hsec bp).symm k' u)
      rw [show πmap ((fibreCompareC a).comp (fibreCompareCInvC a)) k' bp
            (homotopyGroupCast (hsec bp).symm k' u)
          = πmap (fibreCompareC a) k' (fibreCompareCInvC a bp)
            (πmap (fibreCompareCInvC a) k' bp (homotopyGroupCast (hsec bp).symm k' u))
        from πmap_comp_apply (fibreCompareCInvC a) (fibreCompareC a) k' bp _] at h2
      rw [h2]
      exact (homotopyGroupCast (hsec bp) k').apply_symm_apply u
    have hsub : Subsingleton (HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (interInclRight B C) a) (fibreCompareCInvC a bp)) := by
      rw [fibreCompareCInvC_basepoint a]
      exact h
    have hmain : Subsingleton (HomotopyGroup (Fin (k' + 1))
        (homotopyFibre (setIncl (interC B C)) (interCPoint a)) bp) := by
      rw [← hsec bp]
      exact ⟨fun u v => by
        obtain ⟨u', hu'⟩ := hsurj u
        obtain ⟨v', hv'⟩ := hsurj v
        rw [← hu', ← hv']
        exact congrArg (fun w => homotopyGroupCast (hsec bp) k'
          (πmap (fibreCompareC a) k' (fibreCompareCInvC a bp) w)) (hsub.elim u' v')⟩
    exact hmain

end

end Work.RatHurewicz
