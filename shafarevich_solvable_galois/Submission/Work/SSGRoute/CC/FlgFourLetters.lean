import Mathlib
import Submission.Work.SSGRoute.flg_defs
import Submission.Work.SSGRoute.CC.FlgFin4
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The four-letter (`p = 2`) case of the residual generation statement

Reduction of the target to the finite `Fin 4` computation `Work.SSGRoute.CC.flg_fin4_core`.
-/

namespace Work.SSGRoute.CC

open scoped BigOperators

set_option maxErrors 5000
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

abbrev AX (X : Type) : Type := MonoidAlgebra (ZMod 2) (FreeMonoid X)

/-- Composition of the letterwise maps on free monoids. -/
theorem freeMonoid_map_map {X Y Z : Type*} (f : Y → Z) (g : X → Y) (w : FreeMonoid X) :
    FreeMonoid.map f (FreeMonoid.map g w) = FreeMonoid.map (f ∘ g) w := by
  induction w using FreeMonoid.recOn with
  | one => simp only [map_one]
  | of_mul x w ih =>
      rw [map_mul (FreeMonoid.map g) (FreeMonoid.of x) w,
        map_mul (FreeMonoid.map f) (FreeMonoid.map g (FreeMonoid.of x)) (FreeMonoid.map g w),
        map_mul (FreeMonoid.map (f ∘ g)) (FreeMonoid.of x) w,
        FreeMonoid.map_of g x, FreeMonoid.map_of f (g x), FreeMonoid.map_of (f ∘ g) x, ih]
      rfl

/-- The letterwise image of a four-tuple of letters. -/
theorem flg_letters4_map {Y : Type} [DecidableEq Y] (f : Fin 4 → Y) (τ : Tp) :
    flg_letters4 (f τ.1, f τ.2.1, f τ.2.2.1, f τ.2.2.2) = (flg_letters4 τ).image f := by
  simp only [flg_letters4, Finset.image_union, Finset.image_insert, Finset.image_singleton]

/-- A four-tuple all of whose four letters occur is a permutation tuple. -/
theorem isPerm4_of_all_letters :
    ∀ τ : Tp, (∀ x : Fin 4, x ∈ flg_letters4 τ) → tvec τ = alpha1111 := by decide

section Transport

variable {X : Type} [DecidableEq X]

/-- The letter embedding `Fin 4 → X` given by the four letters. -/
def iota (a b c d : X) : Fin 4 → X := ![a, b, c, d]

/-- The retraction `X → Fin 4` attached to the four letters. -/
def gg (a b c d : X) : X → Fin 4 :=
  fun x => if x = a then 0 else if x = b then 1 else if x = c then 2 else 3

theorem gg_iota (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (i : Fin 4) :
    gg a b c d (iota a b c d i) = i := by
  fin_cases i <;> simp [gg, iota, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
    Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]

theorem iota_gg (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (x : X) (hx : x ∈ ({a, b, c, d} : Finset X)) :
    iota a b c d (gg a b c d x) = x := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [gg, iota, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
      Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]

theorem iota_injective (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : Function.Injective (iota a b c d) := by
  intro i j hij
  have h := congrArg (gg a b c d) hij
  rwa [gg_iota a b c d hab hcd hac had hbc hbd i,
    gg_iota a b c d hab hcd hac had hbc hbd j] at h

theorem iota_sg4 (a b c d : X) (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y) (ha : σ a = b)
    (hc : σ c = d) (i : Fin 4) : iota a b c d (sg4 i) = σ (iota a b c d i) := by
  have h1 : σ b = a := by rw [← ha, hσ a]
  have h2 : σ d = c := by rw [← hc, hσ c]
  fin_cases i <;>
    simp [iota, sg4_0, sg4_1, sg4_2, sg4_3, ha, hc, h1, h2]

/-- The algebra map `A(Fin 4) → A(X)` induced by the four letters. -/
def inclA (a b c d : X) : AX (Fin 4) →ₐ[ZMod 2] AX X :=
  MonoidAlgebra.lift (ZMod 2) (AX X) (FreeMonoid (Fin 4))
    (FreeMonoid.lift fun i : Fin 4 =>
      MonoidAlgebra.of (ZMod 2) (FreeMonoid X) (FreeMonoid.of (iota a b c d i)))

/-- The algebra map `A(X) → A(Fin 4)` killing all letters outside `{a,b,c,d}`. -/
def retrA (a b c d : X) : AX X →ₐ[ZMod 2] AX (Fin 4) :=
  MonoidAlgebra.lift (ZMod 2) (AX (Fin 4)) (FreeMonoid X)
    (FreeMonoid.lift fun x : X =>
      MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)) (FreeMonoid.of (gg a b c d x)))

theorem inclA_of (a b c d : X) (w : FreeMonoid (Fin 4)) :
    inclA a b c d (MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)) w)
      = MonoidAlgebra.of (ZMod 2) (FreeMonoid X) (FreeMonoid.map (iota a b c d) w) := by
  induction w using FreeMonoid.recOn with
  | one => simp only [map_one]
  | of_mul i w ih =>
      rw [map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4))),
          map_mul (FreeMonoid.map (iota a b c d)), FreeMonoid.map_of,
          map_mul (inclA a b c d)]
      rw [show inclA a b c d (MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)) (FreeMonoid.of i))
          = MonoidAlgebra.of (ZMod 2) (FreeMonoid X) (FreeMonoid.of (iota a b c d i)) from by
        simp only [inclA, MonoidAlgebra.lift_of, FreeMonoid.lift_eval_of]]
      rw [ih, ← map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid X))]

theorem retrA_of (a b c d : X) (w : FreeMonoid X) :
    retrA a b c d (MonoidAlgebra.of (ZMod 2) (FreeMonoid X) w)
      = MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)) (FreeMonoid.map (gg a b c d) w) := by
  induction w using FreeMonoid.recOn with
  | one => simp only [map_one]
  | of_mul x w ih =>
      rw [map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid X)),
          map_mul (FreeMonoid.map (gg a b c d)), FreeMonoid.map_of,
          map_mul (retrA a b c d)]
      rw [show retrA a b c d (MonoidAlgebra.of (ZMod 2) (FreeMonoid X) (FreeMonoid.of x))
          = MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4))
              (FreeMonoid.of (gg a b c d x)) from by
        simp only [retrA, MonoidAlgebra.lift_of, FreeMonoid.lift_eval_of]]
      rw [ih, ← map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)))]

theorem inclA_single (a b c d : X) (i : Fin 4) :
    inclA a b c d (MonoidAlgebra.single (FreeMonoid.of i) (1 : ZMod 2))
      = MonoidAlgebra.single (FreeMonoid.of (iota a b c d i)) 1 := by
  rw [← MonoidAlgebra.of_apply (ZMod 2) (FreeMonoid (Fin 4)) (FreeMonoid.of i),
    ← MonoidAlgebra.of_apply (ZMod 2) (FreeMonoid X) (FreeMonoid.of (iota a b c d i)),
    inclA_of, FreeMonoid.map_of]

theorem retrA_inclA (a b c d : X) (hι : ∀ i : Fin 4, gg a b c d (iota a b c d i) = i)
    (z : AX (Fin 4)) : retrA a b c d (inclA a b c d z) = z := by
  refine MonoidAlgebra.induction_on
    (motive := fun z => retrA a b c d (inclA a b c d z) = z) z ?_ ?_ ?_
  · intro w
    rw [inclA_of a b c d w, retrA_of a b c d (FreeMonoid.map (iota a b c d) w),
      freeMonoid_map_map (gg a b c d) (iota a b c d) w,
      show (gg a b c d ∘ iota a b c d) = id from funext hι, FreeMonoid.map_id]
    rfl
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]

theorem inclA_injective (a b c d : X) (hι : ∀ i : Fin 4, gg a b c d (iota a b c d i) = i) :
    Function.Injective (inclA a b c d) := by
  intro x y hxy
  have hx := retrA_inclA a b c d hι x
  have hy := retrA_inclA a b c d hι y
  rw [hxy] at hx
  rw [← hx]
  exact hy

theorem inclA_brk4 (a b c d : X) (t : Tp) :
    inclA a b c d (brk4 (Fin 4) t)
      = brk4 X (iota a b c d t.1, iota a b c d t.2.1, iota a b c d t.2.2.1,
          iota a b c d t.2.2.2) := by
  simp only [brk4, brk, map_add, map_mul, inclA_single]

theorem inclA_sgA (a b c d : X) (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y) (ha : σ a = b)
    (hc : σ c = d)
    (hισ : ∀ i : Fin 4, iota a b c d (sg4 i) = σ (iota a b c d i))
    (σA : AX X →ₗ[ZMod 2] AX X) (hmul : ∀ a b, σA (a * b) = σA a * σA b)
    (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1) :
    ∀ z : AX (Fin 4), inclA a b c d (sgA z) = σA (inclA a b c d z) := by
  intro z
  refine MonoidAlgebra.induction_on
    (motive := fun z => inclA a b c d (sgA z) = σA (inclA a b c d z)) z ?_ ?_ ?_
  · intro w
    rw [show sgA (MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4)) w)
        = MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 4))
            (FreeMonoid.map (fun i => sg4 i) w) from
      sigmaA_of (Fin 4) sg4 sgA sgA_mul sgA_one (fun i => sgA_gen i 1) w,
      inclA_of a b c d, inclA_of a b c d]
    rw [show σA (MonoidAlgebra.of (ZMod 2) (FreeMonoid X)
          (FreeMonoid.map (iota a b c d) w))
        = MonoidAlgebra.of (ZMod 2) (FreeMonoid X)
            (FreeMonoid.map (fun x => σ x) (FreeMonoid.map (iota a b c d) w)) from
      sigmaA_of X σ σA hmul hone hgen (FreeMonoid.map (iota a b c d) w),
      freeMonoid_map_map (iota a b c d) (fun i => sg4 i) w,
      freeMonoid_map_map (fun x => σ x) (iota a b c d) w,
      show (iota a b c d ∘ fun i => sg4 i) = ((fun x => σ x) ∘ iota a b c d) from
        funext hισ]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]

theorem inclA_mem_Wsub (a b c d : X) {y : AX (Fin 4)} (hy : y ∈ Wsub (Fin 4)) :
    inclA a b c d y ∈ Wsub X := by
  have hle : Wsub (Fin 4) ≤ Submodule.comap (inclA a b c d).toLinearMap (Wsub X) := by
    rw [Wsub]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span
      ⟨(iota a b c d t.1, iota a b c d t.2.1, iota a b c d t.2.2.1, iota a b c d t.2.2.2),
        (inclA_brk4 a b c d t).symm⟩
  exact hle hy

theorem inclA_mem_Tsub (a b c d : X) {y : AX (Fin 4)} (hy : y ∈ Tsub (Fin 4)) :
    inclA a b c d y ∈ Tsub X := by
  have hgen : ∀ p : Fin 4 × Fin 4,
      inclA a b c d (MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
          * MonoidAlgebra.single (FreeMonoid.of p.1) 1
        + (MonoidAlgebra.single (FreeMonoid.of p.2) 1
            * MonoidAlgebra.single (FreeMonoid.of p.1) 1
          + MonoidAlgebra.single (FreeMonoid.of p.1) 1
            * MonoidAlgebra.single (FreeMonoid.of p.2) 1))
        = MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.1)) (1 : ZMod 2)
            * MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.1)) 1
          + (MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.2)) 1
              * MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.1)) 1
            + MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.1)) 1
              * MonoidAlgebra.single (FreeMonoid.of (iota a b c d p.2)) 1) := by
    intro p
    simp only [map_add, map_mul, inclA_single]
  have hle : Tsub (Fin 4) ≤ Submodule.comap (inclA a b c d).toLinearMap (Tsub X) := by
    rw [Tsub]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact Submodule.subset_span ⟨(iota a b c d p.1, iota a b c d p.2), (hgen p).symm⟩
  exact hle hy

theorem inclA_mem_THspan (a b c d : X) (σA : AX X →ₗ[ZMod 2] AX X)
    (hsg : ∀ z : AX (Fin 4), inclA a b c d (sgA z) = σA (inclA a b c d z))
    {z : AX (Fin 4)} (hz : z ∈ THspanX (Fin 4) sgA) :
    inclA a b c d z ∈ flgThetaSpan X σA := by
  have hkey : ∀ u0 : {u : AX (Fin 4) // u ∈ Tsub (Fin 4)},
      (inclA a b c d (u0 : AX (Fin 4))) * σA (inclA a b c d (u0 : AX (Fin 4)))
        + σA (inclA a b c d (u0 : AX (Fin 4))) * (inclA a b c d (u0 : AX (Fin 4)))
      = inclA a b c d ((u0 : AX (Fin 4)) * sgA (u0 : AX (Fin 4))
          + sgA (u0 : AX (Fin 4)) * (u0 : AX (Fin 4))) := by
    intro u0
    simp only [map_add, map_mul, hsg]
  have hle : THspanX (Fin 4) sgA ≤ Submodule.comap (inclA a b c d).toLinearMap
      (flgThetaSpan X σA) := by
    rw [THspanX]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u0, rfl⟩
    exact Submodule.subset_span
      ⟨⟨inclA a b c d (u0 : AX (Fin 4)), inclA_mem_Tsub a b c d u0.2⟩, hkey u0⟩
  exact hle hz

/-- If `u` is supported on words with letter set `T`, it lies in the span of the `brk4`'s of the
four-tuples with letter set `T`. -/
theorem mem_span_of_support (u : AX X) (hu : u ∈ Wsub X) (T : Finset X)
    (hs : ∀ w : FreeMonoid X, u.coeff w ≠ 0 → flg_letters w = T) :
    u ∈ Submodule.span (ZMod 2)
      {y : AX X | ∃ t : X × X × X × X, flg_letters4 t = T ∧ brk4 X t = y} := by
  have hmap : Submodule.map (flg_proj X T) (Wsub X)
      ≤ Submodule.span (ZMod 2)
        {y : AX X | ∃ t : X × X × X × X, flg_letters4 t = T ∧ brk4 X t = y} := by
    rw [Wsub, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, ⟨t, rfl⟩, rfl⟩
    rw [flg_proj_brk4]
    split_ifs with hh
    · exact Submodule.subset_span ⟨t, hh, rfl⟩
    · exact Submodule.zero_mem _
  have hfixproj : flg_proj X T u = u := by
    ext w
    rw [flg_proj_apply]
    by_cases h : flg_letters w = T
    · rw [if_pos h]
    · rw [if_neg h, eq_comm]
      by_contra hc
      exact h (hs w hc)
  have hmem := hmap (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
  rwa [hfixproj] at hmem

end Transport

section Main

theorem flg_four_letters (X : Type) [DecidableEq X] (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y)
    (a b c d : X) (ha : σ a = b) (hc : σ c = d)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1)
    (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hu : u ∈ Wsub X) (hfix : σA u = u)
    (hsupp : ∀ w : FreeMonoid X, u.coeff w ≠ 0 →
      (∀ y ∈ w.toList, y = a ∨ y = b ∨ y = c ∨ y = d) ∧
      a ∈ w.toList ∧ b ∈ w.toList ∧ c ∈ w.toList ∧ d ∈ w.toList) :
    ∃ w ∈ Wsub X, u - (w + σA w) ∈ flgThetaSpan X σA := by
  classical
  set T : Finset X := {a, b, c, d} with hT
  have hgg : ∀ i : Fin 4, gg a b c d (iota a b c d i) = i :=
    gg_iota a b c d hab hcd hac had hbc hbd
  have hιgg : ∀ x ∈ T, iota a b c d (gg a b c d x) = x := by
    intro x hx
    rw [hT] at hx
    exact iota_gg a b c d hab hcd hac had hbc hbd x hx
  have hιinj : Function.Injective (iota a b c d) :=
    iota_injective a b c d hab hcd hac had hbc hbd
  have hισ : ∀ i : Fin 4, iota a b c d (sg4 i) = σ (iota a b c d i) :=
    iota_sg4 a b c d σ hσ ha hc
  have hsg := inclA_sgA a b c d σ hσ ha hc hισ σA hmul hone hgen
  have hletters : ∀ w : FreeMonoid X, u.coeff w ≠ 0 → flg_letters w = T := by
    intro w hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := hsupp w hw
    rw [hT]
    ext y
    simp only [flg_letters, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hy => h1 y hy,
      fun hy => hy.elim (fun h => h.symm ▸ h2)
        (fun h => h.elim (fun h => h.symm ▸ h3)
          (fun h => h.elim (fun h => h.symm ▸ h4) (fun h => h.symm ▸ h5)))⟩
  have hspan := mem_span_of_support u hu T hletters
  have hle : Submodule.span (ZMod 2)
      {y : AX X | ∃ t : X × X × X × X, flg_letters4 t = T ∧ brk4 X t = y}
      ≤ Submodule.map (inclA a b c d).toLinearMap Vperm := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨t, ht, rfl⟩
    have ht1 : t.1 ∈ T := ht ▸ (by simp [flg_letters4])
    have ht2 : t.2.1 ∈ T := ht ▸ (by simp [flg_letters4])
    have ht3 : t.2.2.1 ∈ T := ht ▸ (by simp [flg_letters4])
    have ht4 : t.2.2.2 ∈ T := ht ▸ (by simp [flg_letters4])
    set τ : Tp := (gg a b c d t.1, gg a b c d t.2.1, gg a b c d t.2.2.1, gg a b c d t.2.2.2)
      with hτdef
    have hτmem : ∀ x : Fin 4, x ∈ flg_letters4 τ := by
      intro x
      have hiff : (flg_letters4 τ).image (iota a b c d) = T := by
        rw [← flg_letters4_map (iota a b c d) τ]
        show flg_letters4 (iota a b c d (gg a b c d t.1), iota a b c d (gg a b c d t.2.1),
              iota a b c d (gg a b c d t.2.2.1), iota a b c d (gg a b c d t.2.2.2)) = T
        rw [hιgg t.1 ht1, hιgg t.2.1 ht2, hιgg t.2.2.1 ht3, hιgg t.2.2.2 ht4]
        rw [show (t.1, t.2.1, t.2.2.1, t.2.2.2) = t from
          Prod.ext rfl (Prod.ext rfl (Prod.ext rfl rfl))]
        exact ht
      have hxT : iota a b c d x ∈ T := by
        rw [hT]
        fin_cases x <;> simp [iota]
      have him : iota a b c d x ∈ (flg_letters4 τ).image (iota a b c d) := by
        rw [hiff]; exact hxT
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp him
      rwa [hιinj hzx] at hz
    refine Submodule.mem_map.mpr ⟨brk4 (Fin 4) τ, ?_, ?_⟩
    · exact Submodule.subset_span ⟨⟨τ, isPerm4_of_all_letters τ hτmem⟩, rfl⟩
    · show inclA a b c d (brk4 (Fin 4) τ) = brk4 X t
      rw [inclA_brk4]
      show brk4 X (iota a b c d (gg a b c d t.1), iota a b c d (gg a b c d t.2.1),
            iota a b c d (gg a b c d t.2.2.1), iota a b c d (gg a b c d t.2.2.2)) = brk4 X t
      rw [hιgg t.1 ht1, hιgg t.2.1 ht2, hιgg t.2.2.1 ht3, hιgg t.2.2.2 ht4]
  have hstepB : u ∈ Submodule.map (inclA a b c d).toLinearMap Vperm := hle hspan
  obtain ⟨v, hv, hvu⟩ := hstepB
  have hvu' : inclA a b c d v = u := hvu
  have hfixv : sgA v = v := by
    apply inclA_injective a b c d hgg
    rw [hsg v, hvu', hfix, ← hvu']
  obtain ⟨w0, hw0, hres⟩ := flg_fin4_core v hv hfixv
  refine ⟨inclA a b c d w0, inclA_mem_Wsub a b c d hw0, ?_⟩
  have hmem := inclA_mem_THspan a b c d σA hsg hres
  have hgoal : inclA a b c d (v - (w0 + sgA w0))
      = u - (inclA a b c d w0 + σA (inclA a b c d w0)) := by
    rw [map_sub, map_add, hvu', hsg w0]
  rwa [hgoal] at hmem

end Main

end

end Work.SSGRoute.CC
