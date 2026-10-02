import Mathlib
import Submission.Work.RatHurewicz.Cofibre.ConeShrink
import Submission.Work.RatHurewicz.Cofibre.URetractEqv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homotopy `cofibreU ι ≃ E`

The collapse `cofibreURetract : ↥(cofibreU ι) → E` and the inclusion `cofibreUIncl` satisfy
`retract ∘ incl = id`; here we build the other homotopy, shrinking the height of the half-open cone
inside `cofibreU ι`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The `E`-branch of the raw shrink map: the constant path at the point. -/
def uShrinkF (ι : C(F, E)) : C(E, C(unitInterval, ↥(cofibreU ι))) where
  toFun x := ContinuousMap.const unitInterval (cofibreUIncl ι x)
  continuous_toFun :=
    ContinuousMap.continuous_of_continuous_uncurry _
      ((cofibreUIncl ι).continuous.comp continuous_fst)

@[simp]
theorem uShrinkF_apply (ι : C(F, E)) (x : E) (s : unitInterval) :
    ((uShrinkF ι x) s : cofibre ι) = cofibreIncl ι x := rfl

/-- The cone-branch of the raw shrink map, on the half-open cone. -/
def uShrinkG (ι : C(F, E)) : C(↥(coneLtHalfSet (F := F)), C(unitInterval, ↥(cofibreU ι))) where
  toFun y :=
    ⟨fun s => ⟨cofibreInclCone ι (coneShrinkC (F := F) y s).1,
        (mem_cofibreU_coneIncl_iff ι (coneShrinkC (F := F) y s).1).mpr
          (coneShrinkC (F := F) y s).2⟩,
      Continuous.subtype_mk ((cofibreInclCone ι).continuous.comp
        (continuous_subtype_val.comp (coneShrinkC (F := F) y).continuous)) _⟩
  continuous_toFun := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : ↥(coneLtHalfSet (F := F)) × unitInterval =>
      (⟨cofibreInclCone ι (coneShrinkC (F := F) p.1 p.2).1,
        (mem_cofibreU_coneIncl_iff ι (coneShrinkC (F := F) p.1 p.2).1).mpr
          (coneShrinkC (F := F) p.1 p.2).2⟩ : ↥(cofibreU ι)))
    exact Continuous.subtype_mk
      (f := fun p : ↥(coneLtHalfSet (F := F)) × unitInterval =>
        (cofibreInclCone ι (coneShrinkC (F := F) p.1 p.2).1 : cofibre ι))
      ((cofibreInclCone ι).continuous.comp (continuous_subtype_val.comp
        (ContinuousMap.uncurry (coneShrinkC (F := F))).continuous))
      (fun p => (mem_cofibreU_coneIncl_iff ι (coneShrinkC (F := F) p.1 p.2).1).mpr
        (coneShrinkC (F := F) p.1 p.2).2)

@[simp]
theorem uShrinkG_apply (ι : C(F, E)) (y : ↥(coneLtHalfSet (F := F))) (s : unitInterval) :
    (uShrinkG ι y s : cofibre ι) = cofibreInclCone ι (coneShrinkC (F := F) y s).1 := by
  show ((⟨cofibreInclCone ι (coneShrinkC (F := F) y s).1,
    (mem_cofibreU_coneIncl_iff ι (coneShrinkC (F := F) y s).1).mpr
      (coneShrinkC (F := F) y s).2⟩ : ↥(cofibreU ι)) : cofibre ι)
    = cofibreInclCone ι (coneShrinkC (F := F) y s).1
  rfl

/-- The raw curried shrink map, on all of `E ⊕ Cone F` (junk outside the half-open cone). -/
def uShrinkFun (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    E ⊕ Work.Stems.Cone F → C(unitInterval, ↥(cofibreU ι)) := by
  classical
  exact Sum.elim (uShrinkF ι)
    (fun y => if h : y ∈ coneLtHalfSet (F := F) then uShrinkG ι ⟨y, h⟩
      else ContinuousMap.const unitInterval ⟨cofibreIncl ι e₀, cofibreIncl_mem_cofibreU ι e₀⟩)

@[simp]
theorem uShrinkFun_inl (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) (x : E) :
    uShrinkFun ι e₀ (Sum.inl x) = uShrinkF ι x := rfl

theorem uShrinkFun_inr (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (y : Work.Stems.Cone F) (hy : y ∈ coneLtHalfSet (F := F)) :
    uShrinkFun ι e₀ (Sum.inr y) = uShrinkG ι ⟨y, hy⟩ := by
  rw [uShrinkFun]
  exact dif_pos hy

/-- The raw curried shrink map on the preimage of `cofibreU ι`. -/
def uShrinkRaw (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι),
      C(unitInterval, ↥(cofibreU ι))) where
  toFun a := uShrinkFun ι e₀ a.1
  continuous_toFun :=
    continuous_of_sumPiecewise ι (isOpen_coneLtHalfSet (F := F)) (uShrinkF ι) (uShrinkG ι)
      (fun _ => rfl) (fun y hy => uShrinkFun_inr ι e₀ y hy) (preimage_cofibreU ι)

@[simp]
theorem uShrinkRaw_apply (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι)) :
    uShrinkRaw ι e₀ a = uShrinkFun ι e₀ a.1 := rfl

/-- The raw map is constant on the classes of the gluing relation inside the preimage. -/
theorem uShrinkFun_eq_of_eqvGen (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    {a b : E ⊕ Work.Stems.Cone F} (h : Relation.EqvGen (cofibreRel ι) a b)
    (ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι)
    (hb : b ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) :
    uShrinkFun ι e₀ a = uShrinkFun ι e₀ b := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hz : coneHeight (Work.Stems.coneIncl z) < cofibreHalf := by
      rw [coneHeight_coneIncl]; exact cofibreHalf_pos
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rw [uShrinkFun_inl, uShrinkFun_inr ι e₀ _ hz, uShrinkF_apply, uShrinkG_apply,
      coneShrinkC_base]
    exact cofibreIncl_coneIncl ι z
  | refl a => rfl
  | symm a b hab ih =>
    have ha' : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
      (cofibreEqvGen_mem_U ι hab).mpr ha
    exact (ih ha' ha).symm
  | trans a b c hab hbc ihab ihbc =>
    have hb' : b ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
      (cofibreEqvGen_mem_U ι hab).mp ha
    exact (ihab ha hb').trans (ihbc hb' hb)

/-- Well-definedness of the descent along the restricted quotient map. -/
theorem uShrinkRaw_factors (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    Function.FactorsThrough (uShrinkRaw ι e₀) (cofibreUQuot ι) := by
  intro a b hab
  have h : (Quotient.mk'' a.1 : cofibre ι) = Quotient.mk'' b.1 := congrArg Subtype.val hab
  exact uShrinkFun_eq_of_eqvGen ι e₀ (Quotient.exact h) a.2 b.2

/-- The descended curried shrink map. -/
def uShrinkQuot (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    C(↥(cofibreU ι), C(unitInterval, ↥(cofibreU ι))) :=
  Topology.IsQuotientMap.lift (isQuotientMap_cofibreUQuot ι) (uShrinkRaw ι e₀)
    (uShrinkRaw_factors ι e₀)

/-- **The shrink homotopy** of the half-open cone, as a map out of `↥(cofibreU ι) × I`. -/
def uShrink (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    C(↥(cofibreU ι) × unitInterval, ↥(cofibreU ι)) :=
  (uShrinkQuot ι e₀).uncurry

@[simp]
theorem uShrink_apply (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (z : ↥(cofibreU ι)) (s : unitInterval) :
    uShrink ι e₀ (z, s) = (uShrinkQuot ι e₀ z) s := rfl

theorem uShrinkQuot_eq (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι)) :
    uShrinkQuot ι e₀ (cofibreUQuot ι a) = uShrinkRaw ι e₀ a :=
  congrFun (congrArg (fun k : C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
      cofibreU ι), C(unitInterval, ↥(cofibreU ι))) =>
      (⇑k : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) →
        C(unitInterval, ↥(cofibreU ι))))
    (Topology.IsQuotientMap.lift_comp (isQuotientMap_cofibreUQuot ι) (uShrinkRaw ι e₀)
      (uShrinkRaw_factors ι e₀))) a

theorem uShrink_zero_aux (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (b : E ⊕ Work.Stems.Cone F) (hb : b ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
      cofibreU ι) :
    uShrink ι e₀ (cofibreUQuot ι ⟨b, hb⟩, 0) = cofibreUQuot ι ⟨b, hb⟩ := by
  rw [uShrink_apply, uShrinkQuot_eq ι e₀ ⟨b, hb⟩, uShrinkRaw_apply]
  apply Subtype.ext
  rcases b with x | y
  · show ((uShrinkFun ι e₀ (Sum.inl x)) 0 : cofibre ι) = Quotient.mk'' (Sum.inl x)
    rw [uShrinkFun_inl, uShrinkF_apply]
    rfl
  · have hy : y ∈ coneLtHalfSet (F := F) := by
      have h := hb
      rw [Set.mem_preimage, mem_cofibreU_iff] at h
      show coneHeight y < cofibreHalf
      simpa only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inr] using h
    show ((uShrinkFun ι e₀ (Sum.inr y)) 0 : cofibre ι) = Quotient.mk'' (Sum.inr y)
    rw [uShrinkFun_inr ι e₀ y hy, uShrinkG_apply, coneShrinkC_zero]
    rfl

theorem uShrink_zero (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (z : ↥(cofibreU ι)) : uShrink ι e₀ (z, 0) = z := by
  obtain ⟨a, ha⟩ := (isQuotientMap_cofibreUQuot ι).surjective z
  subst ha
  exact uShrink_zero_aux ι e₀ a.1 a.2

theorem uShrink_one_aux (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (b : E ⊕ Work.Stems.Cone F) (hb : b ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
      cofibreU ι) :
    uShrink ι e₀ (cofibreUQuot ι ⟨b, hb⟩, 1)
      = cofibreUIncl ι (cofibreURetract ι e₀ (cofibreUQuot ι ⟨b, hb⟩)) := by
  rw [uShrink_apply, uShrinkQuot_eq ι e₀ ⟨b, hb⟩, uShrinkRaw_apply,
    show (cofibreUQuot ι ⟨b, hb⟩ : ↥(cofibreU ι)) = ⟨Quotient.mk'' b, hb⟩ from Subtype.ext rfl,
    cofibreURetract_mk ι e₀ b hb]
  apply Subtype.ext
  rcases b with x | y
  · show ((uShrinkFun ι e₀ (Sum.inl x)) 1 : cofibre ι)
      = (cofibreUIncl ι (uRetractFun ι e₀ (Sum.inl x)) : cofibre ι)
    rw [uShrinkFun_inl, uShrinkF_apply]
    rfl
  · have hy : y ∈ coneLtHalfSet (F := F) := by
      have h := hb
      rw [Set.mem_preimage, mem_cofibreU_iff] at h
      show coneHeight y < cofibreHalf
      simpa only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inr] using h
    obtain ⟨p, hp⟩ := exists_coneRestrictMk_eq (F := F) ⟨y, hy⟩
    show ((uShrinkFun ι e₀ (Sum.inr y)) 1 : cofibre ι)
      = (cofibreUIncl ι (uRetractFun ι e₀ (Sum.inr y)) : cofibre ι)
    rw [uShrinkFun_inr ι e₀ y hy, uShrinkG_apply]
    rw [show (uRetractFun ι e₀ (Sum.inr y)) = coneBaseLtHalf ι ⟨y, hy⟩ from by
      rw [uRetractFun]; exact dif_pos hy]
    rw [cofibreUIncl_apply]
    rw [← hp, coneShrinkC_one_restrictMk]
    rw [show (coneBaseLtHalf ι (coneRestrictMk (F := F) p)) = ι p.1.1 from
      coneBaseLtHalf_coneMk ι p.1 _]
    exact (cofibreIncl_coneIncl ι p.1.1).symm

theorem uShrink_one (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (z : ↥(cofibreU ι)) :
    uShrink ι e₀ (z, 1) = cofibreUIncl ι (cofibreURetract ι e₀ z) := by
  obtain ⟨a, ha⟩ := (isQuotientMap_cofibreUQuot ι).surjective z
  subst ha
  exact uShrink_one_aux ι e₀ a.1 a.2

/-- The shrink homotopy with the time variable first, as required by `ContinuousMap.Homotopy`. -/
def uShrinkSwap (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    C(unitInterval × ↥(cofibreU ι), ↥(cofibreU ι)) :=
  ⟨fun p => uShrink ι e₀ (p.2, p.1), (uShrink ι e₀).continuous.comp
    (continuous_snd.prodMk continuous_fst)⟩

@[simp]
theorem uShrinkSwap_apply (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (t : unitInterval) (z : ↥(cofibreU ι)) :
    uShrinkSwap ι e₀ (t, z) = uShrink ι e₀ (z, t) := rfl

/-- **The homotopy equivalence `↥(cofibreU ι) ≃ E`.** -/
def cofibreUHomotopyEquiv (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    ContinuousMap.HomotopyEquiv ↥(cofibreU ι) E where
  toFun := cofibreURetract ι e₀
  invFun := cofibreUIncl ι
  left_inv := by
    refine ContinuousMap.Homotopic.symm
      ⟨ContinuousMap.Homotopy.mk (uShrinkSwap ι e₀)
        (fun z => uShrink_zero ι e₀ z) (fun z => uShrink_one ι e₀ z)⟩
  right_inv := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × E => cofibreURetract ι e₀ (cofibreUIncl ι p.2),
        (cofibreURetract ι e₀).continuous.comp
          ((cofibreUIncl ι).continuous.comp continuous_snd)⟩ (fun x => rfl) ?_⟩
    intro x
    show cofibreURetract ι e₀ (cofibreUIncl ι x) = x
    exact congrFun (congrArg (fun k : C(E, E) => ⇑k)
      (cofibreURetract_comp_cofibreUIncl ι e₀)) x

end

end Work.RatHurewicz
