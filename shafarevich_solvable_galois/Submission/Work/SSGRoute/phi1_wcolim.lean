import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.inflHIn_add
import Submission.Work.SSGRoute.inflHIn_eq_inflTrivIn
import Submission.Work.SSGRoute.inflHIn_refl
import Submission.Work.SSGRoute.inflHIn_trans
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phiAt_level_infl

/-! Guidance: read `PHI1_REALIZATION_STATUS.md` (this lane) and `DESIGN_FIX.md` §1.

# The `W`-system of the E5s realisation: the index of the gluing

The realisation step glues the level functionals `λ_L : W_L → H²(Gal(L/k),C_L)` into one
functional on the direct limit `V = colim_L H²(Gal(L/k),𝔽_p)`.  This file provides the index of the
gluing:

* `inflHInHom` — the level inflation `inflHIn` as a bundled additive map (from the delegated
  `inflHIn_add`);
* `wc_Wsub L = (δ_L).range` (an `AddSubgroup` of `H²(Gal(L/k),𝔽_p)`) and the type `Wsys L = ↥(wc_Wsub L)`;
* `wStep : W_L →+ W_{L'}` (value `inflHIn h w`; membership in `im δ_{L'}` is `deltaHom_inflHIn`),
  its functoriality `wStep_self`/`wStep_map` (from `inflHIn_refl`/`inflHIn_trans`) and the
  `DirectedSystem` instance;
* `Wcolim`, its canonical maps, its vanishing criterion and its induction principle.

The statement is specialised to the case occurring at the call site of E5s: `S.X₁` is
*definitionally* the trivial module `Rep.trivial Coeff G (ZMod p)`
(`Work.SSGRoute.exists_trivial_sub_shortExact` with `e = Iso.refl`), so `δ_L` lands in
`LevelCoh p L = H²(Gal(L/k),𝔽_p)` definitionally (the restriction of the trivial module is the
trivial module, by `rfl`). -/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [IsGalois k K]

/-- **The bundled level inflation** `H^n(Gal(L/k),M) → H^n(Gal(L'/k),M)`. -/
def inflHInHom (M : Rep.{0} Coeff (K ≃ₐ[k] K)) {L L' : IntermediateField K Ω} [NumberField L]
    [NumberField L'] [FiniteDimensional k L] [FiniteDimensional k L'] [IsGalois k L]
    [IsGalois k L'] (h : L ≤ L') (n : ℕ) :
    extH (Rep.res (galRes k K L) M) n →+ extH (Rep.res (galRes k K L') M) n where
  toFun y := inflHIn (k := k) (K := K) h y
  map_zero' := by
    have h0 := inflHIn_add (k := k) (K := K) M h
      (0 : extH (Rep.res (galRes k K L) M) n) (0 : extH (Rep.res (galRes k K L) M) n)
    rw [add_zero] at h0
    have h1 := congrArg (fun t : extH (Rep.res (galRes k K L') M) n =>
      t - inflHIn (k := k) (K := K) h (0 : extH (Rep.res (galRes k K L) M) n)) h0
    simpa using h1.symm
  map_add' x y := inflHIn_add (k := k) (K := K) M h x y

@[simp] theorem inflHInHom_apply (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    {L L' : IntermediateField K Ω} [NumberField L] [NumberField L'] [FiniteDimensional k L]
    [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L'] (h : L ≤ L') (n : ℕ)
    (y : extH (Rep.res (galRes k K L) M) n) :
    inflHInHom (k := k) (K := K) M h n y = inflHIn (k := k) (K := K) h y := rfl

section WSys

variable (p : ℕ) [Fact p.Prime] (M M₂ : Rep.{0} Coeff (K ≃ₐ[k] K))
  (i : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ M) (π : M ⟶ M₂) (hh : i ≫ π = 0)
  (hS : (ShortComplex.mk i π hh).ShortExact)

/-- The short exact sequence `0 → 𝔽_p → M → M₂ → 0`. -/
abbrev sxS : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) := ShortComplex.mk i π hh

/-- **The `W`-system**: `W_L = im (δ_L : H¹(Gal(L/k),M₂) → H²(Gal(L/k),𝔽_p))`. -/
abbrev wc_Wsub (L : Lvl k K Ω) :=
  (deltaHom (k := k) (K := K) (L := L.1) (sxS p M M₂ i π hh) hS).range

/-- The underlying type of `W_L`. -/
abbrev Wsys (L : Lvl k K Ω) : Type _ := wc_Wsub p M M₂ i π hh hS L

/-- **The transition map of the `W`-system**: inflation of the `δ`-images along `L ≤ L'`. -/
def wStep (L L' : Lvl k K Ω) (h : L ≤ L') :
    Wsys p M M₂ i π hh hS L →+ Wsys p M M₂ i π hh hS L' :=
  AddMonoidHom.codRestrict
    ((inflHInHom (k := k) (K := K) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
        (show L.1 ≤ L'.1 from h) 2).comp (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L)))
    (wc_Wsub p M M₂ i π hh hS L') (by
      intro w
      obtain ⟨j, hj⟩ := AddMonoidHom.mem_range.mp w.2
      refine ⟨inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j, ?_⟩
      rw [deltaHom_inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h)
          (sxS p M M₂ i π hh) hS j, hj]
      show inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h)
          (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)
        = ((inflHInHom (k := k) (K := K) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
            (show L.1 ≤ L'.1 from h) 2).comp
          (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L))) w
      rw [AddMonoidHom.comp_apply, inflHInHom_apply])

theorem wStep_apply (L L' : Lvl k K Ω) (h : L ≤ L')
    (w : Wsys p M M₂ i π hh hS L) :
    AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L') (wStep p M M₂ i π hh hS L L' h w)
      = inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h)
          (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w) := by
  exact inflHInHom_apply (k := k) (K := K) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (show L.1 ≤ L'.1 from h) 2 (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)

/-- The `map_self` axiom of the `W`-system. -/
theorem wStep_self (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    wStep p M M₂ i π hh hS L L le_rfl w = w := by
  apply Subtype.ext
  show AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) (wStep p M M₂ i π hh hS L L le_rfl w)
    = AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w
  rw [wStep_apply]
  exact inflHIn_refl (k := k) (K := K) (L := L.1)
    (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)

/-- The `map_map` axiom of the `W`-system. -/
theorem wStep_map (L L' L'' : Lvl k K Ω) (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    (w : Wsys p M M₂ i π hh hS L) :
    wStep p M M₂ i π hh hS L' L'' h₂ (wStep p M M₂ i π hh hS L L' h₁ w)
      = wStep p M M₂ i π hh hS L L'' (h₁.trans h₂) w := by
  apply Subtype.ext
  show AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L'')
      (wStep p M M₂ i π hh hS L' L'' h₂ (wStep p M M₂ i π hh hS L L' h₁ w))
    = AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L'')
      (wStep p M M₂ i π hh hS L L'' (h₁.trans h₂) w)
  rw [wStep_apply, wStep_apply, wStep_apply]
  exact inflHIn_trans (k := k) (K := K) (show L.1 ≤ L'.1 from h₁)
    (show L'.1 ≤ L''.1 from h₂) (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)

/-- **The `W`-system is a directed system.** -/
instance wDirectedSystem :
    DirectedSystem (fun L : Lvl k K Ω => Wsys p M M₂ i π hh hS L)
      (fun L L' h => wStep p M M₂ i π hh hS L L' h) where
  map_self := fun L w => wStep_self p M M₂ i π hh hS L w
  map_map := fun {kt jt it} (hij : it ≤ jt) (hjk : jt ≤ kt) (w : Wsys p M M₂ i π hh hS it) =>
    wStep_map p M M₂ i π hh hS it jt kt hij hjk w

/-- The transition maps of the `W`-system are additive homomorphisms: the `ZeroHomClass` instance
used by `DirectLimit`, stated directly (build speed: the generic search over `∀ L L', L ≤ L' → …`
explores unrelated morphism classes for minutes). -/
instance wZeroHomClass (L L' : Lvl k K Ω) :
    ZeroHomClass (Wsys p M M₂ i π hh hS L →+ Wsys p M M₂ i π hh hS L')
      (Wsys p M M₂ i π hh hS L) (Wsys p M M₂ i π hh hS L') :=
  AddMonoidHomClass.toZeroHomClass

/-- The `AddHomClass` instance used by `DirectLimit` (see `wZeroHomClass`). -/
instance wAddHomClass (L L' : Lvl k K Ω) :
    AddHomClass (Wsys p M M₂ i π hh hS L →+ Wsys p M M₂ i π hh hS L')
      (Wsys p M M₂ i π hh hS L) (Wsys p M M₂ i π hh hS L') :=
  AddMonoidHomClass.toAddHomClass

/-- The `FunLike` instance of the transition maps, stated directly (see `wZeroHomClass`). -/
instance wFunLike (L L' : Lvl k K Ω) :
    FunLike (Wsys p M M₂ i π hh hS L →+ Wsys p M M₂ i π hh hS L')
      (Wsys p M M₂ i π hh hS L) (Wsys p M M₂ i π hh hS L') :=
  AddMonoidHom.instFunLike

/-- The `ZeroHomClass` instance of additive maps out of a component (used by `DirectLimit.lift`). -/
instance wZeroHomClassTo {A : Type} [AddCommMonoid A] (L : Lvl k K Ω) :
    ZeroHomClass (Wsys p M M₂ i π hh hS L →+ A) (Wsys p M M₂ i π hh hS L) A :=
  AddMonoidHomClass.toZeroHomClass

/-- The `AddHomClass` instance of additive maps out of a component (used by `DirectLimit.lift`). -/
instance wAddHomClassTo {A : Type} [AddCommMonoid A] (L : Lvl k K Ω) :
    AddHomClass (Wsys p M M₂ i π hh hS L →+ A) (Wsys p M M₂ i π hh hS L) A :=
  AddMonoidHomClass.toAddHomClass

/-- **`Wcolim = colim_L W_L`**, the direct limit of the `δ`-images. -/
abbrev Wcolim : Type _ :=
  DirectLimit (fun L : Lvl k K Ω => Wsys p M M₂ i π hh hS L)
    (fun L L' h => wStep p M M₂ i π hh hS L L' h)

/-- The canonical map `W_L → Wcolim`. -/
def Wcolim.of (L : Lvl k K Ω) :
    Wsys p M M₂ i π hh hS L →+ Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS where
  toFun w := ⟦⟨L, w⟩⟧
  map_zero' := (DirectLimit.zero_def L).symm
  map_add' x y := (DirectLimit.add_def L x y).symm

@[simp] theorem Wcolim.of_zero (L : Lvl k K Ω) :
    Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L (0 : Wsys p M M₂ i π hh hS L) = 0 := map_zero _

/-- The colimit relation of the `W`-system. -/
theorem Wcolim.of_wStep {L L' : Lvl k K Ω} (h : L ≤ L') (w : Wsys p M M₂ i π hh hS L) :
    Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L' (wStep p M M₂ i π hh hS L L' h w)
      = Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w :=
  Quotient.sound ⟨L', le_rfl, h,
    wStep_self p M M₂ i π hh hS L' (wStep p M M₂ i π hh hS L L' h w)⟩

/-- An element of `Wcolim` vanishes iff it vanishes at a higher level. -/
theorem Wcolim.of_eq_zero_iff (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w = 0
      ↔ ∃ (L' : Lvl k K Ω) (h : L ≤ L'), wStep p M M₂ i π hh hS L L' h w = 0 := by
  constructor
  · intro hw
    have heq : (⟦⟨L, w⟩⟧ : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS)
        = ⟦⟨L, (0 : Wsys p M M₂ i π hh hS L)⟩⟧ :=
      hw.trans (Wcolim.of_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L).symm
    obtain ⟨j, hw', hz', heq'⟩ := Quotient.exact heq
    exact ⟨j, hw', heq'.trans (map_zero (wStep p M M₂ i π hh hS L j hz'))⟩
  · rintro ⟨L', h, hz⟩
    rw [← Wcolim.of_wStep (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS h w, hz]
    exact Wcolim.of_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L'

/-- Induction on `Wcolim`. -/
protected theorem Wcolim.induction {C : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS → Prop}
    (ih : ∀ (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L),
      C (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w))
    (x : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS) : C x :=
  DirectLimit.induction (f := fun L L' h => wStep p M M₂ i π hh hS L L' h) (fun L w => ih L w) x


/-! ## The universal property of `Wcolim` and the canonical map to the level colimit -/

/-- **The universal property of `Wcolim`**: a compatible family of additive maps out of the
components induces one out of the direct limit. -/
noncomputable def Wcolim.lift {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, Wsys p M M₂ i π hh hS L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (w : Wsys p M M₂ i π hh hS L),
      g L' (wStep p M M₂ i π hh hS L L' h w) = g L w) :
    Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS →+ A where
  toFun := DirectLimit.lift (fun L L' h => wStep p M M₂ i π hh hS L L' h) (fun L => g L)
    (fun L L' h w => (hg L L' h w).symm)
  map_zero' := by
    simpa only using
      DirectLimit.lift_zero (f := fun L L' h => wStep p M M₂ i π hh hS L L' h)
        (g := fun L => g L) (fun L L' h w => (hg L L' h w).symm)
  map_add' x y := by
    simpa only using
      DirectLimit.lift_add (f := fun L L' h => wStep p M M₂ i π hh hS L L' h)
        (g := fun L => g L) (fun L L' h w => (hg L L' h w).symm) x y

@[simp] theorem Wcolim.lift_of {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, Wsys p M M₂ i π hh hS L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (w : Wsys p M M₂ i π hh hS L),
      g L' (wStep p M M₂ i π hh hS L L' h w) = g L w)
    (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    Wcolim.lift (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS g hg
        (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w) = g L w := rfl

/-- **The canonical map `Wcolim → V`**: the `δ`-images inside the level colimit.  This is the map
whose image is `W = ⋃_L W_L ⊆ V`; the functional `λ` of the realisation step is defined on it. -/
noncomputable def iota :
    Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS →+
      LevelCohLimit (k := k) (K := K) (Ω := Ω) p :=
  Wcolim.lift (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
    (g := fun L => (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L).comp
      (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L)))
    (hg := by
      intro L L' h w
      show LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L'
          (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L')
            (wStep p M M₂ i π hh hS L L' h w))
        = LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L
            (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)
      rw [wStep_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L L' h w]
      erw [inflHIn_eq_inflTrivIn (k := k) (K := K) p (show L.1 ≤ L'.1 from h)]
      rw [← LevelCohLimit.of_levelMap (k := k) (K := K) (Ω := Ω) p h
        (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)]
      rfl)

@[simp] theorem iota_of (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
        (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w)
      = LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L
          (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w) :=
  Wcolim.lift_of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS _ _ L w

/-- **`iota` is injective** (and this needs no class-field-theoretic input).  If the class of `w`
dies in the level colimit, then it dies at a higher level and *there* it is the inflation of `w`;
but `inflHIn` on the trivial module is `inflTrivIn`, so `w` itself dies after inflation, i.e. `w`
is killed by the transition map of the `W`-system, hence is zero in `Wcolim`. -/
theorem iota_injective :
    Function.Injective (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS) := by
  intro u v huv
  have hz : iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS (u - v) = 0 :=
    (map_sub _ u v).trans (sub_eq_zero.mpr huv)
  have hzero : u - v = 0 := by
    -- reduce to a statement about components
    refine Wcolim.induction (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
      (C := fun z => iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS z = 0 → z = 0)
      ?_ (u - v) hz
    intro L w hw
    rw [iota_of] at hw
    obtain ⟨L', hLL', hmap⟩ := (LevelCohLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) p
      L (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)).mp hw
    have hw' : wStep p M M₂ i π hh hS L L' hLL' w = 0 := by
      apply Subtype.ext
      show AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L')
        (wStep p M M₂ i π hh hS L L' hLL' w) = 0
      rw [wStep_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L L' hLL' w]
      erw [inflHIn_eq_inflTrivIn (k := k) (K := K) p (show L.1 ≤ L'.1 from hLL')]
      exact hmap
    exact (Wcolim.of_wStep (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS hLL' w).symm.trans
      ((congrArg (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L') hw').trans
        (Wcolim.of_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L'))
  exact sub_eq_zero.mp hzero

end WSys

end Work.SSGRoute
