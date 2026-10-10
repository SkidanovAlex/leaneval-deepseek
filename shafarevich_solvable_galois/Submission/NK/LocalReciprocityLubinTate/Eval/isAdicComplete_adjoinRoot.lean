import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AdicCompletion.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Eval

universe u v w

/-- A linear map sends `I ^ n • ⊤` into `I ^ n • ⊤`. -/
lemma map_mem_pow_smul_top {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) {x : M} (hx : x ∈ (I ^ n • ⊤ : Submodule A M)) :
    f x ∈ (I ^ n • ⊤ : Submodule A N) := by
  have h : (I ^ n • ⊤ : Submodule A M) ≤ (I ^ n • ⊤ : Submodule A N).comap f := by
    rw [Submodule.smul_le]
    intro r hr y _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr trivial
  exact h hx

/-- For a finitely supported function, membership in `I ^ n • ⊤` is coordinatewise
membership in `I ^ n`. -/
lemma mem_pow_smul_top_finsupp_iff {A : Type u} [CommRing A] {I : Ideal A} {ι : Type v}
    {n : ℕ} (g : ι →₀ A) :
    g ∈ (I ^ n • ⊤ : Submodule A (ι →₀ A)) ↔
      ∀ i, g i ∈ (I ^ n : Submodule A A) := by
  constructor
  · intro h i
    have h' := map_mem_pow_smul_top (I := I) (n := n) (f := Finsupp.lapply (R := A) (M := A) i) h
    rw [Finsupp.lapply_apply] at h'
    simpa using h'
  · intro h
    rw [← Finsupp.sum_single g]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hs : Finsupp.single i (g i) = g i • (Finsupp.single i (1 : A)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs]
    exact Submodule.smul_mem_smul (h i) trivial

/-- A finitely generated free module over an `I`-adically complete ring, indexed by a
finite type, is `I`-adically complete. -/
theorem isAdicComplete_finsupp {A : Type u} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    {ι : Type v} [Fintype ι] : IsAdicComplete I (ι →₀ A) := by
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun g hg => ?_⟩ }
  · ext i
    refine IsHausdorff.haus (I := I) (M := A) (inferInstance : IsHausdorff I A) (x i) fun n => ?_
    have hmem : (Finsupp.lapply (R := A) (M := A) i) x ∈ (I ^ n • ⊤ : Submodule A A) :=
      map_mem_pow_smul_top (I := I) (n := n) (f := Finsupp.lapply (R := A) (M := A) i)
        (SModEq.zero.mp (hx n))
    rw [Finsupp.lapply_apply] at hmem
    exact SModEq.zero.mpr hmem
  · have hcoord : ∀ i : ι, ∃ L : A, ∀ n, g n i ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] :=
      fun i => IsPrecomplete.prec (I := I) (M := A) (inferInstance : IsPrecomplete I A)
        (f := fun n => g n i)
        (fun {m n} hmn => by
          have hsub : (Finsupp.lapply (R := A) (M := A) i) (g m) ≡
              (Finsupp.lapply (R := A) (M := A) i) (g n) [SMOD (I ^ m • ⊤ : Submodule A A)] := by
            rw [SModEq.sub_mem, ← map_sub]
            exact map_mem_pow_smul_top (I := I) (n := m) (f := Finsupp.lapply (R := A) (M := A) i)
              (SModEq.sub_mem.mp (hg hmn))
          simpa [Finsupp.lapply_apply] using hsub)
    let Lfun : ι → A := fun i => Classical.choose (hcoord i)
    have hLfun : ∀ i n, g n i - Lfun i ∈ (I ^ n : Submodule A A) := fun i n =>
      show g n i - Classical.choose (hcoord i) ∈ (I ^ n : Submodule A A) from
        by simpa using SModEq.sub_mem.mp (Classical.choose_spec (hcoord i) n)
    have hfin : (Function.support Lfun).Finite :=
      Set.Finite.subset Set.finite_univ (Set.subset_univ _)
    refine ⟨Finsupp.ofSupportFinite Lfun hfin, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_smul_top_finsupp_iff]
    intro i
    have hcoe : (Finsupp.ofSupportFinite Lfun hfin) i = Lfun i :=
      congrFun Finsupp.ofSupportFinite_coe i
    rw [Finsupp.sub_apply, hcoe]
    exact hLfun i n

/-- Adic completeness transports across a linear equivalence. -/
theorem isAdicComplete_of_linearEquiv {A : Type u} [CommRing A] {I : Ideal A}
    {M : Type v} {N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : IsAdicComplete I N) : IsAdicComplete I M := by
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun g hg => ?_⟩ }
  · have h0 : e x = 0 :=
      IsHausdorff.haus h.toIsHausdorff (e x) fun n =>
        SModEq.zero.mpr
          (map_mem_pow_smul_top (I := I) (n := n) (f := (e : M →ₗ[A] N))
            (SModEq.zero.mp (hx n)))
    exact e.injective (by rw [h0, map_zero])
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => e (g n))
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact map_mem_pow_smul_top (I := I) (n := m) (f := (e : M →ₗ[A] N))
          (SModEq.sub_mem.mp (hg hmn)))
    refine ⟨e.symm L, fun n => ?_⟩
    have h1 : e.symm (e (g n) - L) ∈ (I ^ n • ⊤ : Submodule A M) :=
      map_mem_pow_smul_top (I := I) (n := n) (f := (e.symm : N →ₗ[A] M))
        (SModEq.sub_mem.mp (hL n))
    have h2 : e.symm (e (g n) - L) = g n - e.symm L := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [SModEq.sub_mem, ← h2]
    exact h1

theorem isAdicComplete_adjoinRoot {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : Polynomial A) (hf : f.Monic) : IsAdicComplete I (AdjoinRoot f) :=
  isAdicComplete_of_linearEquiv (M := AdjoinRoot f) (N := Fin f.natDegree →₀ A)
    (AdjoinRoot.powerBasisAux' hf).repr
    (isAdicComplete_finsupp (A := A) (I := I) (ι := Fin f.natDegree))

end NK.LocalReciprocityLubinTate.Eval
