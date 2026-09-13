import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

/-!
# The distance distribution of the Grassmannian

Fix a subspace `L` of a finite `𝔽₂`-space `V` with `finrank L = ℓ`.  We count the
`ℓ₀`-dimensional subspaces `L'` of `V` with `finrank (L ⊓ L') = j`:

`2 ^ ((ℓ - j) * (ℓ₀ - j)) * [ℓ choose j]_2 * [(finrank V - ℓ) choose (ℓ₀ - j)]_2`.

The proof passes through the association scheme of the Gaussian binomial distribution:
the map `L' ↦ (L ⊓ L', (L + L')/L)` has fibres which are the complements of `L/J` inside
`(L+L')/J`, and complements of a subspace `U` in `W` are in bijection with linear maps
`W ⧸ U → U`.
-/

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem map_mkQ_inf_of_le (J : Submodule K V) {A B : Submodule K V} (hA : J ≤ A) (hB : J ≤ B) :
    Submodule.map J.mkQ (A ⊓ B) =
      Submodule.map J.mkQ A ⊓ Submodule.map J.mkQ B := by
  apply le_antisymm
  · exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
  · rw [← Submodule.map_comap_eq_self (f := J.mkQ)
        (q := Submodule.map J.mkQ A ⊓ Submodule.map J.mkQ B) (by simp)]
    congr 1
    rw [Submodule.comap_inf, Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.mpr hA, sup_eq_right.mpr hB]

theorem map_mkQ_eq_bot_iff (J : Submodule K V) (X : Submodule K V) :
    Submodule.map J.mkQ X = ⊥ ↔ X ≤ J := by
  constructor
  · intro h
    have h1 : J ⊔ X = J := by
      have := congrArg (Submodule.comap J.mkQ) h
      rwa [Submodule.comap_map_mkQ, Submodule.comap_bot, Submodule.ker_mkQ] at this
    exact sup_eq_left.mp h1
  · intro h
    rw [eq_bot_iff]
    calc Submodule.map J.mkQ X ≤ Submodule.map J.mkQ J := Submodule.map_mono h
      _ = ⊥ := Submodule.mkQ_map_self J

theorem finrank_map_mkQ_add_finrank_inf [Module.Finite K V] (L L' : Submodule K V) :
    Module.finrank K ↥L' = Module.finrank K ↥(Submodule.map L.mkQ L') +
      Module.finrank K ↥(L ⊓ L') := by
  classical
  let g : ↥L' →ₗ[K] (V ⧸ L) := L.mkQ.comp L'.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g = Submodule.map L.mkQ L' := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker g = Submodule.comap L'.subtype L := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hkerfin : Module.finrank K (LinearMap.ker g) = Module.finrank K ↥(L ⊓ L') := by
    rw [hker]
    show Module.finrank K ↥(Submodule.comap L'.subtype L) = Module.finrank K ↥(L ⊓ L')
    rw [← Submodule.finrank_map_subtype_eq L' (Submodule.comap L'.subtype L),
      Submodule.map_comap_subtype, inf_comm]
  rw [hrange, hkerfin] at hrn
  exact hrn.symm

variable [Fintype K]

theorem card_linearMap {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W] :
    Nat.card (V →ₗ[K] W) = (Nat.card K) ^ (Module.finrank K V * Module.finrank K W) := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := V →ₗ[K] W)]
  congr 1
  exact Module.finrank_linearMap K K V W

noncomputable def projectionsEquiv {W : Type*} [AddCommGroup W] [Module K W]
    (U : Submodule K W) :
    {f : W →ₗ[K] U // ∀ x : U, f x = x} ≃ (W ⧸ U →ₗ[K] U) := by
  classical
  let U0 := Classical.choose (Submodule.exists_isCompl U)
  have hU0 : IsCompl U U0 := Classical.choose_spec (Submodule.exists_isCompl U)
  let p0 : W →ₗ[K] U := U.projectionOnto U0 hU0
  have hp0 : ∀ x : U, p0 x = x := fun x => Submodule.projectionOnto_apply_left hU0 x
  refine
    { toFun := fun f => U.liftQ ((f : W →ₗ[K] U) - p0) (by
        intro x hx
        simp only [LinearMap.mem_ker, LinearMap.sub_apply]
        rw [f.2 ⟨x, hx⟩, hp0 ⟨x, hx⟩, sub_self])
      invFun := fun g => ⟨p0 + g.comp U.mkQ, by
        intro x
        show p0 x + (g.comp U.mkQ) x = x
        have hx0 : U.mkQ (x : W) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact x.2
        rw [show (g.comp U.mkQ) x = 0 from by rw [LinearMap.comp_apply, hx0, map_zero]]
        rw [add_zero]
        exact hp0 x⟩
      left_inv := fun f => by
        apply Subtype.ext
        ext x
        simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.liftQ_apply,
          LinearMap.sub_apply, Submodule.mkQ_apply]
        abel
      right_inv := fun g => by
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := U.mkQ_surjective x
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
          Submodule.liftQ_apply, Submodule.mkQ_apply]
        abel }

theorem card_isCompl {W : Type*} [AddCommGroup W] [Module K W] [Module.Finite K W]
    (U : Submodule K W) :
    Nat.card {C : Submodule K W // IsCompl C U} =
      (Nat.card K) ^ ((Module.finrank K W - Module.finrank K U) * Module.finrank K U) := by
  classical
  rw [Nat.card_congr ((Equiv.subtypeEquivRight (fun C => isCompl_comm)).trans
    (Submodule.isComplEquivProj U))]
  rw [Nat.card_congr (projectionsEquiv U)]
  rw [card_linearMap (V := W ⧸ U) (W := U)]
  congr 1
  rw [Submodule.finrank_quotient]

/-! ### Fiber machinery -/

section Fiber

variable (J L : Submodule K V) (hJL : J ≤ L) (N : Submodule K (V ⧸ L))

noncomputable def fiberEquivAbstract :
    {M : Submodule K V // J ≤ M ∧ M ⊓ L = J ∧ M ⊔ L = Submodule.comap L.mkQ N} ≃
    {C : Submodule K (V ⧸ J) // C ⊓ Submodule.map J.mkQ L = ⊥ ∧
      C ⊔ Submodule.map J.mkQ L = Submodule.map J.mkQ (Submodule.comap L.mkQ N)} := by
  classical
  have hJM_fun : ∀ C : Submodule K (V ⧸ J), J ≤ Submodule.comap J.mkQ C := by
    intro C
    rw [← Submodule.map_le_iff_le_comap, Submodule.mkQ_map_self]
    exact bot_le
  refine
    { toFun := fun M => ⟨Submodule.map J.mkQ M.1, ?_, ?_⟩
      invFun := fun C => ⟨Submodule.comap J.mkQ C.1, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← map_mkQ_inf_of_le J M.2.1 hJL, M.2.2.1, Submodule.mkQ_map_self]
  · rw [← Submodule.map_sup, M.2.2.2]
  · exact hJM_fun C.1
  · have hJM := hJM_fun C.1
    have hmap : Submodule.map J.mkQ (Submodule.comap J.mkQ C.1) = C.1 :=
      Submodule.map_comap_eq_self (by simp)
    have h1 : Submodule.map J.mkQ (Submodule.comap J.mkQ C.1 ⊓ L) = ⊥ := by
      rw [map_mkQ_inf_of_le J hJM hJL, hmap, C.2.1]
    have h2 : Submodule.comap J.mkQ C.1 ⊓ L ≤ J := (map_mkQ_eq_bot_iff J _).mp h1
    exact le_antisymm h2 (le_inf hJM hJL)
  · have hJM := hJM_fun C.1
    have hmap : Submodule.map J.mkQ (Submodule.comap J.mkQ C.1) = C.1 :=
      Submodule.map_comap_eq_self (by simp)
    have h1 : Submodule.map J.mkQ (Submodule.comap J.mkQ C.1 ⊔ L) =
        Submodule.map J.mkQ (Submodule.comap L.mkQ N) := by
      rw [Submodule.map_sup, hmap, C.2.2]
    have h2 : Submodule.comap J.mkQ (Submodule.map J.mkQ
        (Submodule.comap J.mkQ C.1 ⊔ L)) =
        Submodule.comap J.mkQ (Submodule.map J.mkQ (Submodule.comap L.mkQ N)) := by rw [h1]
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at h2
    rw [sup_eq_right.mpr (hJM.trans le_sup_left),
        sup_eq_right.mpr (hJL.trans (Submodule.le_comap_mkQ L N))] at h2
    exact h2
  · intro M
    apply Subtype.ext
    show Submodule.comap J.mkQ (Submodule.map J.mkQ M.1) = M.1
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr M.2.1]
  · intro C
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

end Fiber

section Compl

variable {J : Submodule K V}

noncomputable def complEquiv (W U : Submodule K (V ⧸ J)) (hUW : U ≤ W) :
    {C : Submodule K (V ⧸ J) // C ⊓ U = ⊥ ∧ C ⊔ U = W} ≃
    {C : Submodule K ↥W // IsCompl C (Submodule.comap W.subtype U)} := by
  classical
  have hmapW : ∀ (C : Submodule K (V ⧸ J)) (hC : C ≤ W),
      Submodule.map W.subtype (Submodule.comap W.subtype C) = C := by
    intro C hC
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hC]
  have hmapU : Submodule.map W.subtype (Submodule.comap W.subtype U) = U := hmapW U hUW
  refine
    { toFun := fun C => ⟨Submodule.comap W.subtype C.1, ?_, ?_⟩
      invFun := fun C' => ⟨C'.1.map W.subtype, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [disjoint_iff, ← Submodule.comap_inf, C.2.1, Submodule.comap_bot, Submodule.ker_subtype]
  · have hCW : C.1 ≤ W := le_sup_left.trans (le_of_eq C.2.2)
    have hX : Submodule.map W.subtype (Submodule.comap W.subtype C.1 ⊔
        Submodule.comap W.subtype U) = W := by
      rw [Submodule.map_sup, hmapW C.1 hCW, hmapU, C.2.2]
    rw [codisjoint_iff, ← Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W)
      (Submodule.comap W.subtype C.1 ⊔ Submodule.comap W.subtype U), hX,
      Submodule.comap_subtype_self]
  · have hC' : C'.1 ⊓ Submodule.comap W.subtype U = ⊥ := disjoint_iff.mp C'.2.disjoint
    have h1 : Submodule.map W.subtype (C'.1 ⊓ Submodule.comap W.subtype U) = ⊥ := by
      rw [hC', Submodule.map_bot]
    rw [Submodule.map_inf W.subtype (Submodule.subtype_injective W)] at h1
    rw [hmapU] at h1
    exact h1
  · have h1 : Submodule.map W.subtype (C'.1 ⊔ Submodule.comap W.subtype U) = W := by
      rw [codisjoint_iff.mp C'.2.codisjoint, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_sup] at h1
    rw [hmapU] at h1
    exact h1
  · intro C
    apply Subtype.ext
    exact hmapW C.1 (le_sup_left.trans (le_of_eq C.2.2))
  · intro C'
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W) C'.1

end Compl

section FiberFull

variable (J L : Submodule K V) (hJL : J ≤ L) (N : Submodule K (V ⧸ L))

noncomputable def fiberEquivCompl :
    {M : Submodule K V // J ≤ M ∧ M ⊓ L = J ∧ M ⊔ L = Submodule.comap L.mkQ N} ≃
    {C : Submodule K ↥(Submodule.map J.mkQ (Submodule.comap L.mkQ N)) //
      IsCompl C (Submodule.comap (Submodule.map J.mkQ (Submodule.comap L.mkQ N)).subtype
        (Submodule.map J.mkQ L))} :=
  (fiberEquivAbstract J L hJL N).trans
    (complEquiv (V := V) (J := J) (Submodule.map J.mkQ (Submodule.comap L.mkQ N))
      (Submodule.map J.mkQ L) (Submodule.map_mono (Submodule.le_comap_mkQ L N)))

noncomputable def fiberL'Equiv :
    {L' : Submodule K V // L ⊓ L' = J ∧ Submodule.map L.mkQ L' = N} ≃
    {M : Submodule K V // J ≤ M ∧ M ⊓ L = J ∧ M ⊔ L = Submodule.comap L.mkQ N} := by
  refine Equiv.subtypeEquivRight ?_
  intro L'
  constructor
  · rintro ⟨hinf, hmap⟩
    exact ⟨hinf ▸ inf_le_right, by rw [inf_comm]; exact hinf, by
      rw [sup_comm, ← Submodule.comap_map_mkQ, hmap]⟩
  · rintro ⟨hJ, hinf, hsup⟩
    have h1 : Submodule.map L.mkQ (L ⊔ L') = Submodule.map L.mkQ L' := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    exact ⟨by rw [inf_comm]; exact hinf, by
      rw [← h1, sup_comm, hsup, Submodule.map_comap_eq_self (by simp)]⟩

end FiberFull

theorem card_compl_fiber (L J : Submodule K V) (N : Submodule K (V ⧸ L)) (hJL : J ≤ L)
    [Module.Finite K V] :
    Nat.card {C : Submodule K ↥(Submodule.map J.mkQ (Submodule.comap L.mkQ N)) //
        IsCompl C (Submodule.comap (Submodule.map J.mkQ (Submodule.comap L.mkQ N)).subtype
          (Submodule.map J.mkQ L))} =
      (Nat.card K) ^ ((Module.finrank K ↥L - Module.finrank K ↥J) * Module.finrank K ↥N) := by
  classical
  rw [card_isCompl]
  congr 1
  have hJS : J ≤ Submodule.comap L.mkQ N := hJL.trans (Submodule.le_comap_mkQ L N)
  have e1 : Module.finrank K ↥(Submodule.map J.mkQ (Submodule.comap L.mkQ N)) =
      Module.finrank K ↥(Submodule.comap L.mkQ N) - Module.finrank K ↥J :=
    finrank_map_mkQ_of_le J (Submodule.comap L.mkQ N) hJS
  have e2 : Module.finrank K ↥(Submodule.comap L.mkQ N) =
      Module.finrank K ↥N + Module.finrank K ↥L := finrank_comap_mkQ_eq_add L N
  have e3 : Module.finrank K (Submodule.comap (Submodule.map J.mkQ (Submodule.comap L.mkQ N)).subtype
      (Submodule.map J.mkQ L)) = Module.finrank K ↥(Submodule.map J.mkQ L) :=
    LinearEquiv.finrank_eq (Submodule.submoduleOfEquivOfLe
      (Submodule.map_mono (Submodule.le_comap_mkQ L N)))
  have e4 : Module.finrank K ↥(Submodule.map J.mkQ L) =
      Module.finrank K ↥L - Module.finrank K ↥J := finrank_map_mkQ_of_le J L hJL
  have hmono : Module.finrank K ↥J ≤ Module.finrank K ↥L := Submodule.finrank_mono hJL
  have hfac : (Module.finrank K ↥(Submodule.map J.mkQ (Submodule.comap L.mkQ N)) -
      Module.finrank K (Submodule.comap (Submodule.map J.mkQ (Submodule.comap L.mkQ N)).subtype
        (Submodule.map J.mkQ L))) = Module.finrank K ↥N := by
    rw [e1, e3, e2]
    omega
  rw [hfac, e3, e4, mul_comm]

section Count

variable [Module.Finite K V] (L : Submodule K V) (ℓ₀ j : ℕ)

/-- The set of `ℓ₀`-dimensional subspaces of `V` meeting `L` in a `j`-dimensional subspace. -/
abbrev GrFiberSet : Type _ :=
  {L' : Submodule K V // Module.finrank K ↥L' = ℓ₀ ∧ Module.finrank K ↥(L ⊓ L') = j}

/-- The `j`-dimensional subspaces of `L`. -/
abbrev JSet : Type _ := {J : Submodule K V // J ≤ L ∧ Module.finrank K ↥J = j}

/-- The `(ℓ₀-j)`-dimensional subspaces of `V ⧸ L`. -/
abbrev NSet : Type _ := {N : Submodule K (V ⧸ L) // Module.finrank K ↥N = ℓ₀ - j}

/-- The fiber map sending `L'` to the pair `(L ⊓ L', (L + L')/L)`. -/
def fiberMap (hjℓ₀ : j ≤ ℓ₀) (a : GrFiberSet L ℓ₀ j) : JSet L j × NSet L ℓ₀ j :=
  (⟨L ⊓ a.1, inf_le_left, a.2.2⟩,
   ⟨Submodule.map L.mkQ a.1, by
      have h := finrank_map_mkQ_add_finrank_inf L a.1
      have key : Module.finrank K ↥(Submodule.map L.mkQ a.1) +
          Module.finrank K ↥(L ⊓ a.1) = ℓ₀ := by
        rw [← h]
        exact a.2.1
      rw [Nat.eq_sub_of_add_eq key, a.2.2]⟩)

variable {L ℓ₀ j}

/-- The fiber of `fiberMap` over a pair `(J, N)` is the set of `L'` with `L ⊓ L' = J` and
`L + L' = π ⁻¹ N`. -/
noncomputable def fiberEquiv (hjℓ₀ : j ≤ ℓ₀) (p : JSet L j × NSet L ℓ₀ j) :
    {a : GrFiberSet L ℓ₀ j // fiberMap L ℓ₀ j hjℓ₀ a = p} ≃
    {L' : Submodule K V // L ⊓ L' = p.1.1 ∧ Submodule.map L.mkQ L' = p.2.1} where
  toFun a := ⟨a.1.1, by
      have h := congrArg (fun q : JSet L j × NSet L ℓ₀ j => q.1.1) a.2
      simpa [fiberMap] using h, by
      have h := congrArg (fun q : JSet L j × NSet L ℓ₀ j => q.2.1) a.2
      simpa [fiberMap] using h⟩
  invFun x := ⟨⟨x.1, by
      have h := finrank_map_mkQ_add_finrank_inf L x.1
      have hmap : Module.finrank K ↥(Submodule.map L.mkQ x.1) =
          Module.finrank K ↥p.2.1 := by rw [x.2.2]
      have hinf : Module.finrank K ↥(L ⊓ x.1) = Module.finrank K ↥p.1.1 := by rw [x.2.1]
      rw [h, hmap, hinf, p.2.2, p.1.2.2]
      omega, by rw [x.2.1]; exact p.1.2.2⟩,
    Prod.ext (Subtype.ext (by simpa [fiberMap] using x.2.1))
      (Subtype.ext (by simpa [fiberMap] using x.2.2))⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

end Count

theorem card_submodule_finrank_inf_eq_aux [Finite V] [Module.Finite K V]
    (L : Submodule K V) (ℓ ℓ₀ j : ℕ)
    (hL : Module.finrank K L = ℓ) (hjℓ : j ≤ ℓ) (hjℓ₀ : j ≤ ℓ₀)
    (hℓ₀ : ℓ₀ ≤ Module.finrank K V) :
    Nat.card {L' : Submodule K V // Module.finrank K L' = ℓ₀ ∧
        Module.finrank K ↥(L ⊓ L') = j} =
      (Nat.card K) ^ ((ℓ - j) * (ℓ₀ - j)) *
        Nat.card {W : Submodule K ↥L // Module.finrank K W = j} *
        Nat.card {W : Submodule K (V ⧸ L) // Module.finrank K W = ℓ₀ - j} := by
  classical
  haveI : Fintype (Submodule K V) := Fintype.ofFinite _
  haveI : Finite (V ⧸ L) := Finite.of_surjective L.mkQ L.mkQ_surjective
  haveI : Fintype (V ⧸ L) := Fintype.ofFinite _
  haveI : Fintype (Submodule K (V ⧸ L)) := Fintype.ofFinite _
  haveI hJ : Fintype (JSet L j) := Fintype.ofFinite _
  haveI hN : Fintype (NSet L ℓ₀ j) := Fintype.ofFinite _
  haveI : Fintype (JSet L j × NSet L ℓ₀ j) := inferInstance
  have key : ∀ p : JSet L j × NSet L ℓ₀ j,
      Nat.card {a : GrFiberSet L ℓ₀ j //
          fiberMap L ℓ₀ j hjℓ₀ a = p} =
        (Nat.card K) ^ ((ℓ - j) * (ℓ₀ - j)) := by
    intro p
    rw [Nat.card_congr (fiberEquiv hjℓ₀ p)]
    rw [Nat.card_congr (fiberL'Equiv p.1.1 L p.2.1)]
    rw [Nat.card_congr (fiberEquivCompl p.1.1 L p.1.2.1 p.2.1)]
    rw [card_compl_fiber L p.1.1 p.2.1 p.1.2.1]
    rw [p.1.2.2, p.2.2, hL]
  have hcard : Nat.card (JSet L j) =
      Nat.card {W : Submodule K ↥L // Module.finrank K W = j} :=
    card_submodule_le_finrank_eq L j
  change Nat.card (GrFiberSet L ℓ₀ j) = _
  calc Nat.card (GrFiberSet L ℓ₀ j)
      = Nat.card (Σ p : JSet L j × NSet L ℓ₀ j,
          {a : GrFiberSet L ℓ₀ j // fiberMap L ℓ₀ j hjℓ₀ a = p}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (fiberMap L ℓ₀ j hjℓ₀)).symm
    _ = ∑ p : JSet L j × NSet L ℓ₀ j,
          Nat.card {a : GrFiberSet L ℓ₀ j //
            fiberMap L ℓ₀ j hjℓ₀ a = p} :=
        Nat.card_sigma
    _ = ∑ _p : JSet L j × NSet L ℓ₀ j,
          (Nat.card K) ^ ((ℓ - j) * (ℓ₀ - j)) :=
        Finset.sum_congr rfl (fun p _ => key p)
    _ = Nat.card (JSet L j × NSet L ℓ₀ j) *
          (Nat.card K) ^ ((ℓ - j) * (ℓ₀ - j)) := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
    _ = (Nat.card K) ^ ((ℓ - j) * (ℓ₀ - j)) *
          Nat.card {W : Submodule K ↥L // Module.finrank K W = j} *
          Nat.card {W : Submodule K (V ⧸ L) // Module.finrank K W = ℓ₀ - j} := by
        rw [Nat.card_prod, hcard]
        ring


/-- **The distance distribution of the Grassmannian / the association scheme of the
Gaussian binomial distribution.**  Fix a subspace `L` of a finite `𝔽₂`-space `V` with
`finrank L = ℓ`.  The number of `ℓ₀`-dimensional subspaces `L'` of `V` with
`finrank (L ⊓ L') = j` is
`2 ^ ((ℓ - j) * (ℓ₀ - j)) * [ℓ choose j]_2 * [(finrank V - ℓ) choose (ℓ₀ - j)]_2`,
where `[n choose m]_2` is written as the number of `m`-dimensional subspaces of `𝔽₂ⁿ`. -/
theorem card_submodule_finrank_inf_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (L : Submodule (ZMod 2) V) (ℓ ℓ₀ j : ℕ)
    (hL : Module.finrank (ZMod 2) L = ℓ) (hjℓ : j ≤ ℓ) (hjℓ₀ : j ≤ ℓ₀)
    (hℓ₀ : ℓ₀ ≤ Module.finrank (ZMod 2) V) :
    Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ₀ ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = j} =
      2 ^ ((ℓ - j) * (ℓ₀ - j)) *
        Nat.card {W : Submodule (ZMod 2) (Fin ℓ → ZMod 2) //
          Module.finrank (ZMod 2) W = j} *
        Nat.card {W : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) V - ℓ) → ZMod 2) //
          Module.finrank (ZMod 2) W = ℓ₀ - j} := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Finite (V ⧸ L) := Finite.of_surjective L.mkQ L.mkQ_surjective
  rw [card_submodule_finrank_inf_eq_aux L ℓ ℓ₀ j hL hjℓ hjℓ₀ hℓ₀]
  rw [Nat.card_zmod]
  congr 1
  · rw [card_submodule_finrank_eq_of_finrank_eq (K := ZMod 2) (V := ↥L)
      (V' := Fin ℓ → ZMod 2) (ℓ := j)
      (by rw [hL, Module.finrank_pi, Fintype.card_fin])]
  · rw [card_submodule_finrank_eq_of_finrank_eq (K := ZMod 2) (V := V ⧸ L)
      (V' := Fin (Module.finrank (ZMod 2) V - ℓ) → ZMod 2) (ℓ := ℓ₀ - j)
      (by rw [Submodule.finrank_quotient, hL, Module.finrank_pi, Fintype.card_fin])]

end

end Commons.LinearAlgebra.Submodule