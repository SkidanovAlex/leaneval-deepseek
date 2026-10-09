import Mathlib
import Submission.NK.HassePrinciple.IdeleCocycleLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

section Aux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Orbit representatives of the places

For the construction of the splitting idèle we choose, for each place `v` of `L`, a place
`basePlace v` in the `Gal(L/K)`-orbit of `v` together with an element `orbitRep v` of `Gal(L/K)`
moving `basePlace v` to `v`.  The choice is made once and for all (using `Quotient.out` on the
orbit quotient), so that `basePlace` is constant on orbits: `basePlace (g • v) = basePlace v`.
-/

/-- A chosen representative of the `Gal(L/K)`-orbit of a place. -/
def basePlace (v : Place L) : Place L :=
  (Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v).out

theorem basePlace_rel (v : Place L) :
    (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) (basePlace (K := K) v) v :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (α := Place L)
    (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v))

/-- `basePlace` is constant on `Gal(L/K)`-orbits. -/
theorem basePlace_smul (g : L ≃ₐ[K] L) (v : Place L) :
    basePlace (K := K) (g • v) = basePlace (K := K) v := by
  have h : Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) (g • v) =
      Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v :=
    Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))
  simp only [basePlace]
  rw [h]

/-- The orbit of a place is finite. -/
theorem orbit_finite (b : Place L) : (MulAction.orbit (L ≃ₐ[K] L) b).Finite := by
  have h : MulAction.orbit (L ≃ₐ[K] L) b = Set.range (fun g : L ≃ₐ[K] L => g • b) := rfl
  rw [h]
  exact Set.finite_range _

theorem basePlace_exists (v : Place L) : ∃ g : L ≃ₐ[K] L, g • v = basePlace (K := K) v :=
  MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (basePlace_rel v))

/-- A Galois element moving `v` to the orbit representative of `v`. -/
noncomputable def orbitMove (v : Place L) : L ≃ₐ[K] L := Classical.choose (basePlace_exists v)

theorem orbitMove_spec (v : Place L) : orbitMove (K := K) v • v = basePlace (K := K) v := by
  show Classical.choose (basePlace_exists v) • v = basePlace (K := K) v
  exact Classical.choose_spec (basePlace_exists v)

/-- A Galois element moving the orbit representative of `v` to `v`. -/
noncomputable def orbitRep (v : Place L) : L ≃ₐ[K] L := (orbitMove (K := K) v)⁻¹

theorem orbitRep_spec (v : Place L) : orbitRep (K := K) v • basePlace (K := K) v = v := by
  rw [orbitRep, ← orbitMove_spec v, inv_smul_smul]

/-! ## Elementary transport lemmas

The local field `L_v` is a family of types indexed by the places, so comparing elements at
propositionally equal places involves transports.  The following lemmas record the few facts
about them that the main computation needs. -/

/-- Transport of units of local fields along an equality of places, as a function. -/
def castFun {a b : Place L} (h : a = b) : (Place.localField L a)ˣ → (Place.localField L b)ˣ :=
  fun x => h ▸ x

theorem cast_symm_cast {a b : Place L} (h : a = b) (z : (Place.localField L a)ˣ) :
    h.symm ▸ (h ▸ z) = z := by cases h; rfl

/-- Transports along two proofs of the same equality of places agree (proof irrelevance). -/
theorem eqRec_congr {α : Type*} {F : α → Type*} {a b : α} (h h' : a = b) (x : F a) :
    h ▸ x = h' ▸ x :=
  eq_of_heq ((eqRec_heq h x).trans (eqRec_heq h' x).symm)

theorem cast_cast {a b c : Place L} (h : a = b) (h' : b = c) (x : (Place.localField L a)ˣ) :
    h' ▸ (h ▸ x) = (h.trans h') ▸ x := by cases h; cases h'; rfl

theorem cast_mul {a b : Place L} (h : a = b) (x y : (Place.localField L a)ˣ) :
    h ▸ (x * y) = (h ▸ x) * (h ▸ y) := by cases h; rfl

/-- The action `actVal` commutes with transport of its argument in the place. -/
theorem actVal_cast {γ : L ≃ₐ[K] L} {a b : Place L} (h : a = b)
    (x : (Place.localField L a)ˣ) :
    actVal γ b (h ▸ x) = (congrArg (fun p => γ • p) h) ▸ actVal γ a x := by
  cases h; rfl

theorem mem_localUnits_of_eq {a b : Place L} (h : a = b) (x : (Place.localField L a)ˣ) :
    x ∈ Place.localUnits L a ↔ (h ▸ x) ∈ Place.localUnits L b := by cases h; rfl

/-- The value of `γ • x` at a place `V` with `γ • w = V`, in terms of `actVal`. -/
theorem smul_apply_eq_of_eq {γ : L ≃ₐ[K] L} {w V : Place L} (e : γ • w = V) (x : Idele L) :
    (γ • x) V = e ▸ actVal γ w (x w) :=
  (units_transport e (γ • x)).symm.trans
    (congrArg (fun z => e ▸ z) (smul_apply_smul_place γ w x))

theorem smul_onePlace_apply (g : L ≃ₐ[K] L) (w : Place L) (u : (Place.localField L w)ˣ) :
    (g • onePlace w u) (g • w) = actVal g w u := by
  rw [smul_apply_smul_place, onePlace_apply_self]

theorem smul_onePlace_apply_of_eq {g : L ≃ₐ[K] L} {w V : Place L}
    (e : g • w = V) (u : (Place.localField L w)ˣ) :
    (g • onePlace w u) V = e ▸ actVal g w u :=
  (units_transport e (g • onePlace w u)).symm.trans
    (congrArg (fun z => e ▸ z) (smul_onePlace_apply g w u))

theorem smul_onePlace_apply_ne {g : L ≃ₐ[K] L} {w V : Place L} (h : V ≠ g • w)
    (u : (Place.localField L w)ˣ) : (g • onePlace w u) V = 1 := by
  rw [Idele.smul_apply]
  have h' : g⁻¹ • V ≠ w := fun he => h (by rw [← he, smul_inv_smul])
  rw [onePlace_apply_ne h' u, map_one]

/-- A translate of `onePlace` has local units as components. -/
theorem smul_onePlace_mem_localUnits {g : L ≃ₐ[K] L} {w : Place L}
    {u : (Place.localField L w)ˣ} (hu : u ∈ Place.localUnits L w) (V : Place L) :
    (g • onePlace w u) V ∈ Place.localUnits L V := by
  by_cases h : V = g • w
  · rw [smul_onePlace_apply_of_eq h.symm u]
    exact (mem_localUnits_of_eq h.symm (actVal g w u)).mp
      ((Place.localRingEquiv_mem_localUnits g w u).mp hu)
  · rw [smul_onePlace_apply_ne h u]
    exact Subgroup.one_mem _

/-- The value of `actVal` on a stabiliser element, using the Hilbert 90 relation. -/
theorem actVal_stabilizer_eq_of {c : (L ≃ₐ[K] L) → Idele L} {w₀ : Place L}
    {u : (Place.localField L w₀)ˣ}
    (hu : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀,
      c σ.1 w₀ = Units.map (localAut w₀ σ).toMonoidHom u / u)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀) :
    actVal σ.1 w₀ u =
      (MulAction.mem_stabilizer_iff.mp σ.2).symm ▸ (c σ.1 w₀ * u) := by
  have hσ : σ.1 • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp σ.2
  have h := actVal_stabilizer w₀ σ u
  have hmap : Units.map (localAut w₀ σ).toMonoidHom u = c σ.1 w₀ * u := by
    rw [hu σ, div_eq_mul_inv]
    group
  calc actVal σ.1 w₀ u = hσ.symm ▸ (hσ ▸ actVal σ.1 w₀ u) := (cast_symm_cast hσ _).symm
    _ = hσ.symm ▸ Units.map (localAut w₀ σ).toMonoidHom u := by rw [h]
    _ = hσ.symm ▸ (c σ.1 w₀ * u) := by rw [hmap]

theorem div_apply_idele {K' : Type} [Field K'] [NumberField K'] (x y : Idele K')
    (v : Place K') : (x / y) v = x v / y v := by simp [div_eq_mul_inv]

theorem smul_div_idele (g : L ≃ₐ[K] L) (x y : Idele L) : g • (x / y) = (g • x) / (g • y) := by
  show (MulDistribMulAction.toMulAut (L ≃ₐ[K] L) (Idele L) g) (x / y) = _
  rw [map_div]
  rfl

/-! ## The local computation

The heart of the proof: replacing the representative used at a place by another element mapping
the chosen base place to the same place changes the corresponding local contribution only by the
cocycle.  This is the computation in which Hilbert 90 for the decomposition group enters. -/

theorem component_eq_of_stabilizer {c : (L ≃ₐ[K] L) → Idele L} {w₀ : Place L}
    {u : (Place.localField L w₀)ˣ}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g)
    (hu : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀,
      c σ.1 w₀ = Units.map (localAut w₀ σ).toMonoidHom u / u)
    (γ : L ≃ₐ[K] L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀) {V : Place L}
    (e : γ • w₀ = V) :
    (((γ * σ.1) • onePlace w₀ u) / c (γ * σ.1)) V =
      ((γ • onePlace w₀ u) / c γ) V := by
  have hσ : σ.1 • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp σ.2
  have e' : (γ * σ.1) • w₀ = V := by rw [mul_smul, hσ]; exact e
  let B : γ • (σ.1 • w₀) = (γ * σ.1) • w₀ := (mul_smul γ σ.1 w₀).symm
  let A : γ • w₀ = γ • (σ.1 • w₀) := congrArg (fun p => γ • p) hσ.symm
  let Y : γ • w₀ = V := A.trans (B.trans e')
  have key : e' ▸ actVal (γ * σ.1) w₀ u = (γ • c σ.1) V * (e ▸ actVal γ w₀ u) := by
    have h1 : e' ▸ actVal (γ * σ.1) w₀ u
        = (B.trans e') ▸ actVal γ (σ.1 • w₀) (actVal σ.1 w₀ u) :=
      (congrArg (castFun e') (actVal_comp γ σ.1 w₀ u)).trans (cast_cast B e' _)
    have h2 : (B.trans e') ▸ actVal γ (σ.1 • w₀) (actVal σ.1 w₀ u)
        = (B.trans e') ▸ actVal γ (σ.1 • w₀) (hσ.symm ▸ (c σ.1 w₀ * u)) :=
      congrArg (castFun (B.trans e'))
        (congrArg (fun z : (Place.localField L (σ.1 • w₀))ˣ => actVal γ (σ.1 • w₀) z)
          (actVal_stabilizer_eq_of hu σ))
    have h3 : (B.trans e') ▸ actVal γ (σ.1 • w₀) (hσ.symm ▸ (c σ.1 w₀ * u))
        = (B.trans e') ▸ (A ▸ actVal γ w₀ (c σ.1 w₀ * u)) :=
      congrArg (castFun (B.trans e')) (actVal_cast hσ.symm (c σ.1 w₀ * u))
    have h4 : (B.trans e') ▸ (A ▸ actVal γ w₀ (c σ.1 w₀ * u))
        = Y ▸ actVal γ w₀ (c σ.1 w₀ * u) := cast_cast A (B.trans e') _
    have h5 : Y ▸ actVal γ w₀ (c σ.1 w₀ * u)
        = Y ▸ (actVal γ w₀ (c σ.1 w₀) * actVal γ w₀ u) :=
      congrArg (castFun Y) (actVal_mul γ w₀ (c σ.1 w₀) u)
    have h6 : Y ▸ (actVal γ w₀ (c σ.1 w₀) * actVal γ w₀ u)
        = (Y ▸ actVal γ w₀ (c σ.1 w₀)) * (Y ▸ actVal γ w₀ u) := cast_mul Y _ _
    have h7 : Y ▸ actVal γ w₀ (c σ.1 w₀) = (γ • c σ.1) V :=
      (eqRec_congr (F := fun p => (Place.localField L p)ˣ) Y e (actVal γ w₀ (c σ.1 w₀))).trans
        (smul_apply_eq_of_eq e (c σ.1)).symm
    have h8 : Y ▸ actVal γ w₀ u = e ▸ actVal γ w₀ u :=
      eqRec_congr (F := fun p => (Place.localField L p)ˣ) Y e (actVal γ w₀ u)
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (by rw [h7, h8]))))))
  rw [div_apply_idele, div_apply_idele, smul_onePlace_apply_of_eq e' u,
    smul_onePlace_apply_of_eq e u,
    show c (γ * σ.1) V = (γ • c σ.1) V * c γ V by rw [hc γ σ.1, Idele.mul_apply],
    key, div_eq_div_iff_mul_eq_mul]
  rw [mul_comm ((γ • c σ.1) V) (e ▸ actVal γ w₀ u), mul_assoc]

/-! ## The splitting idèle -/

/-- The local contribution at a place: the local solution at the orbit representative,
transported to the place, divided by the cocycle. -/
noncomputable def localPiece {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) : Idele L :=
  (orbitRep (K := K) v) • onePlace (basePlace (K := K) v)
      (localSol hc (basePlace (K := K) v)) / c (orbitRep (K := K) v)

theorem localPiece_apply {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) :
    localPiece hc v v = (((orbitRep (K := K) v) • onePlace (basePlace (K := K) v)
      (localSol hc (basePlace (K := K) v))) / c (orbitRep (K := K) v)) v := rfl

/-- The places at which the splitting idèle can fail to be a local unit form a finite set. -/
theorem badSet_y_finite (c : (L ≃ₐ[K] L) → Idele L) :
    ({v : Place L | basePlace (K := K) v ∈ badSet (K := K) c} ∪
      {v : Place L | c (orbitRep (K := K) v) v ∉ Place.localUnits L v}).Finite := by
  have h1 : {v : Place L | basePlace (K := K) v ∈ badSet (K := K) c} ⊆
      ⋃ b ∈ badSet (K := K) c, MulAction.orbit (L ≃ₐ[K] L) b := by
    intro v hv
    refine Set.mem_iUnion.mpr ⟨basePlace (K := K) v, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (basePlace_rel (K := K) v))
    exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  have hfin1 : (⋃ b ∈ badSet (K := K) c, MulAction.orbit (L ≃ₐ[K] L) b).Finite :=
    Set.Finite.biUnion (badSet_finite (K := K) c) (fun b _ => orbit_finite (K := K) b)
  have h2 : {v : Place L | c (orbitRep (K := K) v) v ∉ Place.localUnits L v} ⊆
      ⋃ g : L ≃ₐ[K] L, {v : Place L | c g v ∉ Place.localUnits L v} := by
    intro v hv
    exact Set.mem_iUnion.mpr ⟨orbitRep (K := K) v, hv⟩
  have hfin2 : (⋃ g : L ≃ₐ[K] L, {v : Place L | c g v ∉ Place.localUnits L v}).Finite := by
    rw [← Set.biUnion_univ]
    exact Set.Finite.biUnion Set.finite_univ (fun g _ => by
      have hg : ∀ᶠ v in Filter.cofinite, c g v ∈ Place.localUnits L v := (c g).2
      rw [Filter.eventually_cofinite] at hg
      exact hg)
  exact (hfin1.subset h1).union (hfin2.subset h2)

/-- The components of the splitting idèle are local units at all but finitely many places. -/
theorem eventually_localPiece_mem {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) :
    ∀ᶠ v in Filter.cofinite, localPiece hc v v ∈ Place.localUnits L v := by
  rw [Filter.eventually_cofinite]
  refine (badSet_y_finite c).subset ?_
  intro v hv
  by_contra hnot
  have hb : basePlace (K := K) v ∉ badSet (K := K) c := fun h => hnot (Or.inl h)
  have hc' : c (orbitRep (K := K) v) v ∈ Place.localUnits L v := by
    by_contra h
    exact hnot (Or.inr h)
  exact hv (by
    rw [localPiece_apply, div_apply_idele]
    exact Subgroup.div_mem _ (smul_onePlace_mem_localUnits (K := K)
      (g := orbitRep (K := K) v)
      (localSol_mem_localUnits hc (basePlace (K := K) v) hb) v) hc')

/-- **The splitting idèle** of a multiplicative `1`-cocycle. -/
noncomputable def coboundary {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) : Idele L :=
  ⟨fun v => localPiece hc v v, eventually_localPiece_mem hc⟩

theorem coboundary_apply {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) :
    coboundary hc v = localPiece hc v v := rfl

/-! ## The cocycle identity for the splitting idèle -/

theorem arith {G : Type*} [CommGroup G] (X Y cg cγ c₂ : G) (h : Y / c₂ = X / cγ) :
    X / (cγ / cg) = cg * (Y / c₂) := by
  rw [h, div_div_eq_mul_div, ← mul_div_assoc cg X cγ, mul_comm X cg]

/-- The local contributions at a place computed with two different coset representatives agree. -/
theorem component_at {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (g : L ≃ₐ[K] L) (w : Place L) :
    ((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) (g • w)
      / (c (orbitRep (K := K) (g • w))) (g • w)
    = ((g * orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) (g • w)
      / (c (g * orbitRep (K := K) w)) (g • w) := by
  have hγ : (g * orbitRep (K := K) w) • basePlace (K := K) w = g • w := by
    rw [mul_smul, orbitRep_spec]
  have h₂ : orbitRep (K := K) (g • w) • basePlace (K := K) w = g • w := by
    rw [← basePlace_smul (K := K) g w]
    exact orbitRep_spec (g • w)
  have hσ : ((g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w))
      • basePlace (K := K) w = basePlace (K := K) w := by
    rw [mul_smul, h₂, ← hγ, inv_smul_smul]
  let σ : MulAction.stabilizer (L ≃ₐ[K] L) (basePlace (K := K) w) :=
    ⟨(g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w), hσ⟩
  have hmul : (g * orbitRep (K := K) w) * σ.1 = orbitRep (K := K) (g • w) := by
    show (g * orbitRep (K := K) w)
      * ((g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w)) =
        orbitRep (K := K) (g • w)
    group
  have h := component_eq_of_stabilizer (w₀ := basePlace (K := K) w)
    (u := localSol hc (basePlace (K := K) w)) (V := g • w) hc
    (localSol_spec hc (basePlace (K := K) w)) (g * orbitRep (K := K) w) σ hγ
  rw [hmul] at h
  rwa [div_apply_idele, div_apply_idele] at h

/-- **The splitting idèle is a coboundary**: `g • y = c g * y` componentwise. -/
theorem actVal_coboundary_eq {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (g : L ≃ₐ[K] L) (w : Place L) :
    actVal g w (coboundary hc w) = c g (g • w) * coboundary hc (g • w) := by
  have hstep : actVal g w (coboundary hc w) = (g • localPiece hc w) (g • w) := by
    rw [coboundary_apply]
    exact (smul_apply_smul_place g w (localPiece hc w)).symm
  have hg1 : g • localPiece hc w = ((g * orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
      (localSol hc (basePlace (K := K) w))) / (g • c (orbitRep (K := K) w)) := by
    show g • (((orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) / c (orbitRep (K := K) w)) = _
    rw [smul_div_idele, smul_smul]
  have hden : (g • c (orbitRep (K := K) w)) (g • w)
      = (c (g * orbitRep (K := K) w)) (g • w) / (c g) (g • w) := by
    have h1 : c (g * orbitRep (K := K) w) (g • w)
        = (g • c (orbitRep (K := K) w)) (g • w) * (c g) (g • w) := by
      rw [hc g (orbitRep (K := K) w), Idele.mul_apply]
    rw [h1, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hy : coboundary hc (g • w) = ((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) w)
      (localSol hc (basePlace (K := K) w)) / c (orbitRep (K := K) (g • w))) (g • w) := by
    rw [coboundary_apply]
    show (((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) (g • w))
        (localSol hc (basePlace (K := K) (g • w)))) / c (orbitRep (K := K) (g • w))) (g • w) = _
    rw [basePlace_smul]
  rw [hstep, hg1, hy, div_apply_idele, div_apply_idele, hden]
  rw [component_at hc g w]
  rw [div_div_eq_mul_div, ← mul_div_assoc, mul_comm]

end Aux

open NK.GlobalCFT in
/-- **Hilbert 90 for the idèles**: every multiplicative `1`-cocycle of `Gal(L/K)` with values in
the idèle group `𝕀_L` is a coboundary. -/
theorem exists_idele_coboundary_of_isMulCocycle {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {c : (L ≃ₐ[K] L) → NK.GlobalCFT.Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) :
    ∃ y : NK.GlobalCFT.Idele L, ∀ g : L ≃ₐ[K] L, g • y / y = c g := by
  refine ⟨coboundary hc, fun g => ?_⟩
  have hmain : g • coboundary hc = c g * coboundary hc := by
    refine Idele.ext fun v => ?_
    rw [Idele.mul_apply]
    have hv : g • (g⁻¹ • v) = v := smul_inv_smul g v
    have hkey := actVal_coboundary_eq hc g (g⁻¹ • v)
    calc (g • coboundary hc) v
        = hv ▸ ((g • coboundary hc) (g • (g⁻¹ • v))) :=
          (units_transport hv (g • coboundary hc)).symm
      _ = hv ▸ actVal g (g⁻¹ • v) (coboundary hc (g⁻¹ • v)) :=
          congrArg (castFun hv) (smul_apply_smul_place g (g⁻¹ • v) (coboundary hc))
      _ = hv ▸ (c g (g • (g⁻¹ • v)) * coboundary hc (g • (g⁻¹ • v))) :=
          congrArg (castFun hv) hkey
      _ = (hv ▸ c g (g • (g⁻¹ • v))) * (hv ▸ coboundary hc (g • (g⁻¹ • v))) :=
          cast_mul hv _ _
      _ = c g v * coboundary hc v := by
          rw [units_transport hv (c g), units_transport hv (coboundary hc)]
  rw [hmain, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]

end NK.HassePrinciple
