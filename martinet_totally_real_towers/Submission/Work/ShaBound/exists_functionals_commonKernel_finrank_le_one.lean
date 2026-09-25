import Mathlib

/-!
# Choosing functionals with small common kernel

Over a field `K`, a finite family `f : ι → V →ₗ[K] K` of linear functionals on a vector space `V`
has common kernel `⨅ i, (f i).ker`.  This file proves that as soon as the dimension of `V` is at
most `card ι + 1`, the family can be chosen so that this common kernel has dimension at most `1`.

The proof is elementary linear algebra.  It rests on the auxiliary fact that a finite-dimensional
space of dimension at most `card ι` embeds linearly into the coordinate space `ι → K`: one maps a
basis injectively into the coordinate directions using an embedding `Fin (finrank K X) ↪ ι`, and
the dual basis functionals `b.coord j` separate points (`Module.Basis.forall_coord_eq_zero_iff`).
-/

namespace Work.ShaBound

open Module

/-- **A finite-dimensional space of dimension at most `card ι` embeds into `ι → K`.**

Given an embedding of the index set of a basis of `X` into `ι`, the coordinate functionals
`b.coord j` indexed by `ι` (extended by `0` off the image, which is what `Function.invFun`
produces) separate points of `X`; collecting them into one linear map gives an injection
`X →ₗ[K] (ι → K)`. -/
theorem exists_injective_linearMap_pi
    {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {ι : Type} [Fintype ι] (h : Module.finrank K X ≤ Fintype.card ι) :
    ∃ L : X →ₗ[K] (ι → K), Function.Injective L := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank K X) with hm0 | hmpos
  · -- `X` is a subsingleton, so the zero map is injective
    have hsub : Subsingleton X := Module.finrank_zero_iff.mp hm0
    exact ⟨0, fun x y _ => hsub.elim x y⟩
  · have hne : Nonempty (Fin (Module.finrank K X)) := Fin.pos_iff_nonempty.mp hmpos
    -- an embedding of the basis index set into `ι`
    let e : Fin (Module.finrank K X) ↪ ι :=
      (Fin.castLEEmb h).trans ((Fintype.equivFin ι).symm.toEmbedding)
    let b := Module.finBasis K X
    -- the coordinate functionals, re-indexed by `ι`
    let f : ι → X →ₗ[K] K := fun i => b.coord (Function.invFun e i)
    refine ⟨LinearMap.pi f, ?_⟩
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_pi, Submodule.eq_bot_iff]
    intro x hx
    have hfe : ∀ j, f (e j) = b.coord j := by
      intro j
      dsimp only [f]
      rw [Function.leftInverse_invFun e.injective j]
    have hz : ∀ j, b.coord j x = 0 := by
      intro j
      have h1 : x ∈ (f (e j)).ker := (Submodule.mem_iInf _).mp hx (e j)
      rw [LinearMap.mem_ker] at h1
      rwa [hfe j] at h1
    exact (Module.Basis.forall_coord_eq_zero_iff b).mp hz

/-- Over a field, functionals indexed by a finite type of cardinality `n` on a vector space of dimension at most `n + 1` can be chosen with common kernel of dimension at most `1`. -/
theorem exists_functionals_commonKernel_finrank_le_one
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] (h : Module.finrank K V ≤ Fintype.card ι + 1) :
    ∃ f : ι → V →ₗ[K] K, Module.finrank K ↥(⨅ i, (f i).ker : Submodule K V) ≤ 1 := by
  classical
  by_cases hle : Module.finrank K V ≤ Fintype.card ι
  · -- `V` itself embeds into `ι → K`, so the common kernel is trivial
    obtain ⟨L, hL⟩ := exists_injective_linearMap_pi (K := K) (X := V) (ι := ι) hle
    refine ⟨fun i => (LinearMap.proj i).comp L, ?_⟩
    have h1 : (⨅ i, ((LinearMap.proj i).comp L).ker) = LinearMap.ker L := by
      rw [← LinearMap.ker_pi, LinearMap.pi_proj_comp]
    rw [h1, LinearMap.ker_eq_bot.mpr hL]
    simp
  · -- otherwise `finrank K V = card ι + 1`: kill one line first, then embed the quotient
    have hpos : 0 < Module.finrank K V := by omega
    have hnt : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hWfin : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv
    have hquot : Module.finrank K (V ⧸ (K ∙ v)) ≤ Fintype.card ι := by
      have h1 := Submodule.finrank_quotient_add_finrank (K ∙ v)
      rw [hWfin] at h1
      omega
    obtain ⟨Φ, hΦ⟩ :=
      exists_injective_linearMap_pi (K := K) (X := V ⧸ (K ∙ v)) (ι := ι) hquot
    refine ⟨fun i => (LinearMap.proj i).comp (Φ.comp (Submodule.mkQ (K ∙ v))), ?_⟩
    have hker : LinearMap.ker (Φ.comp (Submodule.mkQ (K ∙ v))) = K ∙ v := by
      rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hΦ, Submodule.comap_bot, Submodule.ker_mkQ]
    have h1 : (⨅ i, ((LinearMap.proj i).comp (Φ.comp (Submodule.mkQ (K ∙ v)))).ker) =
        LinearMap.ker (Φ.comp (Submodule.mkQ (K ∙ v))) := by
      rw [← LinearMap.ker_pi, LinearMap.pi_proj_comp]
    rw [h1, hker]
    exact hWfin.le

end Work.ShaBound
