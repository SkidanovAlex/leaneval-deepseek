import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_iff
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_trans

set_option maxHeartbeats 1000000

namespace Commons.LinearAlgebra.Matrix

open Module

local notation "𝔽₂" => ZMod 2

/-!
# A rank-decomposition pair for a "disjoint" configuration of matrices

The paper *An analogue of Bonami's Lemma for functions on spaces of linear maps, and
2-2 Games* (arXiv:2209.04243) defines the partial order `X ≤ Y ↔ rank Y = rank X + rank (Y - X)`
on `L(W,V)` and proves (Lemma `lem:F1`) that if `X = Y + Z` with
`Im Y ∩ Im Z ∩ Im X = {0}` and `ker Y + ker Z + ker X = W`, then there is a pair
`Y' ≤ Y`, `Z' ≤ Z` with `Y' + Z' = X`.

This file formalises that existence statement.  The construction is explicit: writing
`A = Y.mulVecLin`, `B = Z.mulVecLin`, `C = X.mulVecLin = A + B`, one defines `Y'` as the
unique linear map that agrees with `A` on `ker B` and vanishes on `ker A + ker C` (and `Z'`
symmetrically).  The hypotheses guarantee this is well defined, and the two rank identities
follow from the first isomorphism theorem for linear maps.

The supporting lemmas are general facts about finite-dimensional vector spaces.
-/

section General

/-- **Sufficient criterion for additivity of ranks.**
If `ker f + ker g = ⊤` and `Im f ∩ Im g = ⊥`, then `rank (f + g) = rank f + rank g`. -/
theorem finrank_range_add_of_ker_sup_of_inf_bot {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (f g : V →ₗ[K] W)
    (hker : LinearMap.ker f ⊔ LinearMap.ker g = ⊤)
    (hinf : LinearMap.range f ⊓ LinearMap.range g = ⊥) :
    Module.finrank K (LinearMap.range (f + g)) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
  have hf : LinearMap.range f ≤ LinearMap.range (f + g) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.mp (show v ∈ LinearMap.ker f ⊔ LinearMap.ker g by rw [hker]; trivial)
    refine ⟨b, ?_⟩
    have h1 : f v = f b := by rw [← hab, map_add, LinearMap.mem_ker.mp ha, zero_add]
    have h2 : (f + g) b = f b := by rw [LinearMap.add_apply, LinearMap.mem_ker.mp hb, add_zero]
    rw [h2, h1]
  have hg : LinearMap.range g ≤ LinearMap.range (f + g) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.mp (show v ∈ LinearMap.ker f ⊔ LinearMap.ker g by rw [hker]; trivial)
    refine ⟨a, ?_⟩
    have h1 : g v = g a := by rw [← hab, map_add, LinearMap.mem_ker.mp hb, add_zero]
    have h2 : (f + g) a = g a := by rw [LinearMap.add_apply, LinearMap.mem_ker.mp ha, zero_add]
    rw [h2, h1]
  have hrange : LinearMap.range (f + g) = LinearMap.range f ⊔ LinearMap.range g :=
    le_antisymm (LinearMap.range_add_le f g) (sup_le hf hg)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  rw [hinf, finrank_bot, add_zero] at hdim
  rw [hrange, hdim]

/-- The image of the kernel of a linear map is trivial. -/
theorem map_ker_eq_bot' {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) : Submodule.map f (LinearMap.ker f) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact LinearMap.mem_ker.mp hx

/-- Extension of a linear map from a submodule `S` to the whole space, killing `T`,
when `S ⊔ T = ⊤` and `S ⊓ T ≤ ker A`:

there is `A'` with `A' = A` on `S`, `T ≤ ker A'`, and the kernels/ranges of `A'` and `A - A'`
are described by `S`, `T` and `ker A`. -/
theorem exists_linearMap_eqOn_of_sup_eq_top {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S T : Submodule K V) (hST : S ⊔ T = ⊤) (A : V →ₗ[K] W)
    (h : S ⊓ T ≤ LinearMap.ker A) :
    ∃ A' : V →ₗ[K] W,
      (∀ s, s ∈ S → A' s = A s) ∧
      T ≤ LinearMap.ker A' ∧
      LinearMap.ker A' = T ⊔ (S ⊓ LinearMap.ker A) ∧
      LinearMap.range A' = Submodule.map A S ∧
      LinearMap.range (A - A') = Submodule.map A T ∧
      LinearMap.ker (A - A') = S ⊔ (T ⊓ LinearMap.ker A) := by
  classical
  let Fst : (↥S × ↥T) →ₗ[K] V := S.subtype.comp (LinearMap.fst K ↥S ↥T)
  let Snd : (↥S × ↥T) →ₗ[K] V := T.subtype.comp (LinearMap.snd K ↥S ↥T)
  let σ : (↥S × ↥T) →ₗ[K] V := Fst + Snd
  have hσ : Function.Surjective σ := by
    intro v
    obtain ⟨s, hs, t, ht, hst⟩ :=
      Submodule.mem_sup.mp (show v ∈ S ⊔ T by rw [hST]; trivial)
    refine ⟨(⟨s, hs⟩, ⟨t, ht⟩), ?_⟩
    show Fst (⟨s, hs⟩, ⟨t, ht⟩) + Snd (⟨s, hs⟩, ⟨t, ht⟩) = v
    simp only [Fst, Snd, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      Submodule.subtype_apply]
    exact hst
  let Ψ : (↥S × ↥T) →ₗ[K] W := A.comp Fst
  have hkerΨ : LinearMap.ker σ ≤ LinearMap.ker Ψ := by
    intro p hp
    have hp' : (Fst p + Snd p) = 0 := hp
    have hp2 : ((p.1 : V) + (p.2 : V)) = 0 := by
      simpa only [Fst, Snd, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Submodule.subtype_apply] using hp'
    have hmem : (p.1 : V) ∈ S ⊓ T := by
      refine ⟨p.1.2, ?_⟩
      have : (p.1 : V) = -(p.2 : V) := by
        rw [eq_neg_iff_add_eq_zero]; exact hp2
      rw [this]; exact T.neg_mem p.2.2
    have hA0 : A (p.1 : V) = 0 := LinearMap.mem_ker.mp (h hmem)
    rw [LinearMap.mem_ker]
    show A (p.1 : V) = 0
    exact hA0
  let A' : V →ₗ[K] W := (Submodule.liftQ (LinearMap.ker σ) Ψ hkerΨ).comp
    ((LinearMap.quotKerEquivOfSurjective σ hσ).symm : V →ₗ[K] (↥S × ↥T) ⧸ LinearMap.ker σ)
  have hkey : ∀ s, s ∈ S → A' s = A s := by
    intro s hs
    have hp : σ (⟨s, hs⟩, 0) = s := by
      show Fst (⟨s, hs⟩, 0) + Snd (⟨s, hs⟩, 0) = s
      simp only [Fst, Snd, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Submodule.subtype_apply, Submodule.coe_zero, add_zero]
    have hsymm : (LinearMap.quotKerEquivOfSurjective σ hσ).symm s =
        Submodule.Quotient.mk (⟨s, hs⟩, 0) := by
      have h0 := LinearMap.quotKerEquivOfSurjective_symm_apply (f := σ) hσ (⟨s, hs⟩, 0)
      rw [hp] at h0
      exact h0
    rw [show A' s = (Submodule.liftQ (LinearMap.ker σ) Ψ hkerΨ)
          ((LinearMap.quotKerEquivOfSurjective σ hσ).symm s) from rfl,
      hsymm, Submodule.liftQ_apply]
    rfl
  have hT0 : ∀ t, t ∈ T → A' t = 0 := by
    intro t ht
    have hp : σ (0, ⟨t, ht⟩) = t := by
      show Fst (0, (⟨t, ht⟩ : ↥T)) + Snd (0, ⟨t, ht⟩) = t
      simp only [Fst, Snd, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Submodule.subtype_apply, Submodule.coe_zero, zero_add]
    have hsymm : (LinearMap.quotKerEquivOfSurjective σ hσ).symm t =
        Submodule.Quotient.mk (0, ⟨t, ht⟩) := by
      have h0 := LinearMap.quotKerEquivOfSurjective_symm_apply (f := σ) hσ (0, ⟨t, ht⟩)
      rw [hp] at h0
      exact h0
    rw [show A' t = (Submodule.liftQ (LinearMap.ker σ) Ψ hkerΨ)
          ((LinearMap.quotKerEquivOfSurjective σ hσ).symm t) from rfl,
      hsymm, Submodule.liftQ_apply]
    simp [Ψ, Fst]
  have hA'T : T ≤ LinearMap.ker A' := fun t ht => LinearMap.mem_ker.mpr (hT0 t ht)
  refine ⟨A', hkey, hA'T, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro w hw
      have hw0 : A' w = 0 := hw
      obtain ⟨s, hs, t, ht, hst⟩ :=
        Submodule.mem_sup.mp (show w ∈ S ⊔ T by rw [hST]; trivial)
      have hAs : A s = 0 := by
        have h1 : A' (s + t) = 0 := by rw [hst]; exact hw0
        rw [map_add, hkey s hs, hT0 t ht, add_zero] at h1
        exact h1
      rw [← hst]
      exact Submodule.mem_sup.mpr ⟨t, ht, s, Submodule.mem_inf.mpr ⟨hs, hAs⟩, add_comm t s⟩
    · rw [sup_le_iff]
      refine ⟨hA'T, ?_⟩
      intro s hs
      rw [Submodule.mem_inf] at hs
      rw [LinearMap.mem_ker, hkey s hs.1, LinearMap.mem_ker.mp hs.2]
  · apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      obtain ⟨s, hs, t, ht, hst⟩ :=
        Submodule.mem_sup.mp (show w ∈ S ⊔ T by rw [hST]; trivial)
      refine Submodule.mem_map.mpr ⟨s, hs, ?_⟩
      rw [← hst, map_add, hkey s hs, hT0 t ht, add_zero]
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨s, hkey s hs⟩
  · apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      obtain ⟨s, hs, t, ht, hst⟩ :=
        Submodule.mem_sup.mp (show w ∈ S ⊔ T by rw [hST]; trivial)
      refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
      rw [← hst, LinearMap.sub_apply, map_add, map_add, hkey s hs, hT0 t ht, add_zero]
      abel
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, by rw [LinearMap.sub_apply, hT0 t ht, sub_zero]⟩
  · apply le_antisymm
    · intro w hw
      have hw0 : (A - A') w = 0 := hw
      obtain ⟨s, hs, t, ht, hst⟩ :=
        Submodule.mem_sup.mp (show w ∈ S ⊔ T by rw [hST]; trivial)
      have hAt : A t = 0 := by
        have h1 : (A - A') (s + t) = 0 := by rw [hst]; exact hw0
        rw [LinearMap.sub_apply, map_add, map_add, hkey s hs, hT0 t ht, add_zero] at h1
        have h2 : A s + A t = A s := sub_eq_zero.mp h1
        have h3 : A s + A t = A s + 0 := by rw [add_zero]; exact h2
        exact add_left_cancel h3
      rw [← hst]
      exact Submodule.mem_sup.mpr ⟨s, hs, t, Submodule.mem_inf.mpr ⟨ht, hAt⟩, rfl⟩
    · rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · intro s hs
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hkey s hs, sub_self]
      · intro t ht
        rw [Submodule.mem_inf] at ht
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hT0 t ht.1, LinearMap.mem_ker.mp ht.2, sub_zero]

end General

section Matrix

/-- The rank of a sum of two matrices is the sum of their ranks when their kernels span and
their ranges are disjoint. -/
theorem rank_add_eq_rank_add_rank {m n : ℕ} (P Q : Matrix (Fin m) (Fin n) 𝔽₂)
    (hker : LinearMap.ker P.mulVecLin ⊔ LinearMap.ker Q.mulVecLin = ⊤)
    (hinf : LinearMap.range P.mulVecLin ⊓ LinearMap.range Q.mulVecLin = ⊥) :
    (P + Q).rank = P.rank + Q.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact finrank_range_add_of_ker_sup_of_inf_bot P.mulVecLin Q.mulVecLin hker hinf

/-- `mulVecLin` commutes with subtraction. -/
theorem mulVecLin_sub {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n K) : (M - N).mulVecLin = M.mulVecLin - N.mulVecLin := by
  ext v
  simp only [Matrix.mulVecLin_apply, LinearMap.sub_apply, Matrix.sub_mulVec]

/-- If `C = A + B` and `Im A ∩ Im B ∩ Im C = {0}` then
`ker B ⊓ (ker A + ker C) ≤ ker A`. -/
theorem inf_sup_ker_le_of {m n : ℕ} (A B C : (Fin m → 𝔽₂) →ₗ[𝔽₂] (Fin n → 𝔽₂))
    (hC : C = A + B) (h1 : LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C = ⊥) :
    LinearMap.ker B ⊓ (LinearMap.ker A ⊔ LinearMap.ker C) ≤ LinearMap.ker A := by
  intro w hw
  rw [Submodule.mem_inf] at hw
  obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp hw.2
  rw [LinearMap.mem_ker]
  have hBw : B w = 0 := LinearMap.mem_ker.mp hw.1
  have hCc : C c = 0 := LinearMap.mem_ker.mp hc
  have hAu : A u = 0 := LinearMap.mem_ker.mp hu
  have hBw' : B u + B c = 0 := by rw [← map_add, huc]; exact hBw
  have hCc' : A c + B c = 0 := by rw [hC, LinearMap.add_apply] at hCc; exact hCc
  have hAc : A c = B u := by
    rw [eq_neg_of_add_eq_zero_left hCc', ← eq_neg_of_add_eq_zero_left hBw']
  have hAw : A w = B u := by rw [← huc, map_add, hAu, zero_add, hAc]
  have hAr : A w ∈ LinearMap.range A := ⟨w, rfl⟩
  have hBr : A w ∈ LinearMap.range B := ⟨u, hAw.symm⟩
  have hCr : A w ∈ LinearMap.range C :=
    ⟨u, by rw [hC, LinearMap.add_apply, hAu, zero_add, hAw.symm]⟩
  have hmem : A w ∈ LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hAr, hBr⟩, hCr⟩
  rw [h1] at hmem
  simpa using hmem

/-- If `C = A + B` and `Im A ∩ Im B ∩ Im C = {0}` then
`A '' ker B` and `A '' ker C` are disjoint. -/
theorem map_ker_inf_map_ker_eq_bot_of {m n : ℕ} (A B C : (Fin m → 𝔽₂) →ₗ[𝔽₂] (Fin n → 𝔽₂))
    (hC : C = A + B) (h1 : LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C = ⊥) :
    Submodule.map A (LinearMap.ker B) ⊓ Submodule.map A (LinearMap.ker C) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨⟨b, hb, hvb⟩, ⟨c, hc, hvc⟩⟩
  have hBc : B c = -v := by
    have hc0 : C c = 0 := LinearMap.mem_ker.mp hc
    rw [hC, LinearMap.add_apply, hvc] at hc0
    exact eq_neg_of_add_eq_zero_right hc0
  have hBr : v ∈ LinearMap.range B := ⟨-c, by rw [map_neg, hBc, neg_neg]⟩
  have hCr : v ∈ LinearMap.range C :=
    ⟨b, by rw [hC, LinearMap.add_apply, hvb, LinearMap.mem_ker.mp hb, add_zero]⟩
  have hAr : v ∈ LinearMap.range A := ⟨b, hvb⟩
  have hmem : v ∈ LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hAr, hBr⟩, hCr⟩
  rw [h1] at hmem
  simpa using hmem

end Matrix

theorem exists_plLE_pair_of_disjoint {n m : ℕ} (X Y Z : Matrix (Fin n) (Fin m) (ZMod 2))
    (h : Y + Z = X)
    (h1 : LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin ⊓ LinearMap.range X.mulVecLin = ⊥)
    (h2 : LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin = ⊤) :
    ∃ Y' Z' : Matrix (Fin n) (Fin m) (ZMod 2),
      Y.rank = Y'.rank + (Y - Y').rank ∧ Z.rank = Z'.rank + (Z - Z').rank ∧ Y' + Z' = X := by
  classical
  have hC : X.mulVecLin = Y.mulVecLin + Z.mulVecLin := by rw [← h, Matrix.mulVecLin_add]
  have hC' : X.mulVecLin = Z.mulVecLin + Y.mulVecLin := by rw [hC, add_comm]
  have h1' : LinearMap.range Z.mulVecLin ⊓ LinearMap.range Y.mulVecLin ⊓
      LinearMap.range X.mulVecLin = ⊥ := by
    rw [show LinearMap.range Z.mulVecLin ⊓ LinearMap.range Y.mulVecLin =
      LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin from inf_comm _ _]
    exact h1
  -- kernels spanning, as required by the extension lemma
  have hST_Y : LinearMap.ker Z.mulVecLin ⊔
      (LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin) = ⊤ := by
    rw [← h2]; ac_rfl
  have hST_Z : LinearMap.ker Y.mulVecLin ⊔
      (LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin) = ⊤ := by
    rw [← h2]; ac_rfl
  -- the two extensions
  obtain ⟨Y'Lin, hYs, hY'T, hYker, hYrange, hYdiffer, hYdker⟩ :=
    exists_linearMap_eqOn_of_sup_eq_top (LinearMap.ker Z.mulVecLin)
      (LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin) hST_Y Y.mulVecLin
      (inf_sup_ker_le_of Y.mulVecLin Z.mulVecLin X.mulVecLin hC h1)
  obtain ⟨Z'Lin, hZs, hZ'T, hZker, hZrange, hZdiffer, hZdker⟩ :=
    exists_linearMap_eqOn_of_sup_eq_top (LinearMap.ker Y.mulVecLin)
      (LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin) hST_Z Z.mulVecLin
      (inf_sup_ker_le_of Z.mulVecLin Y.mulVecLin X.mulVecLin hC' h1')
  have hY'T0 : ∀ t, t ∈ LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin → Y'Lin t = 0 :=
    fun t ht => LinearMap.mem_ker.mp (hY'T ht)
  have hZ'T0 : ∀ t, t ∈ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin → Z'Lin t = 0 :=
    fun t ht => LinearMap.mem_ker.mp (hZ'T ht)
  -- matrices attached to the extensions
  let Y' : Matrix (Fin n) (Fin m) 𝔽₂ := Matrix.toLin'.symm Y'Lin
  let Z' : Matrix (Fin n) (Fin m) 𝔽₂ := Matrix.toLin'.symm Z'Lin
  have hY'lin : Y'.mulVecLin = Y'Lin := by
    rw [← Matrix.toLin'_apply']
    exact LinearEquiv.apply_symm_apply Matrix.toLin' Y'Lin
  have hZ'lin : Z'.mulVecLin = Z'Lin := by
    rw [← Matrix.toLin'_apply']
    exact LinearEquiv.apply_symm_apply Matrix.toLin' Z'Lin
  have hdiffY : (Y - Y').mulVecLin = Y.mulVecLin - Y'Lin := by rw [mulVecLin_sub, hY'lin]
  have hdiffZ : (Z - Z').mulVecLin = Z.mulVecLin - Z'Lin := by rw [mulVecLin_sub, hZ'lin]
  refine ⟨Y', Z', ?_, ?_, ?_⟩
  · -- rank decomposition for Y
    have hkerY : LinearMap.ker Y'.mulVecLin ⊔ LinearMap.ker (Y - Y').mulVecLin = ⊤ := by
      rw [hY'lin, hdiffY]
      have hk1 : LinearMap.ker Y'Lin =
          LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin := by
        rw [hYker, sup_eq_left.mpr (le_trans inf_le_right le_sup_left)]
      have hk2 : LinearMap.ker (Y.mulVecLin - Y'Lin) =
          LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker Y.mulVecLin := by
        rw [hYdker, inf_eq_right.mpr le_sup_left]
      rw [hk1, hk2, eq_top_iff, ← h2, sup_le_iff, sup_le_iff]
      exact ⟨⟨le_trans le_sup_left le_sup_left, le_trans le_sup_left le_sup_right⟩,
        le_trans le_sup_right le_sup_left⟩
    have hinfY : LinearMap.range Y'.mulVecLin ⊓ LinearMap.range (Y - Y').mulVecLin = ⊥ := by
      rw [hY'lin, hdiffY]
      have hr2 : LinearMap.range (Y.mulVecLin - Y'Lin) =
          Submodule.map Y.mulVecLin (LinearMap.ker X.mulVecLin) := by
        rw [hYdiffer, Submodule.map_sup, map_ker_eq_bot', bot_sup_eq]
      rw [hYrange, hr2]
      exact map_ker_inf_map_ker_eq_bot_of Y.mulVecLin Z.mulVecLin X.mulVecLin hC h1
    have key := rank_add_eq_rank_add_rank Y' (Y - Y') hkerY hinfY
    rwa [show Y' + (Y - Y') = Y from by abel] at key
  · -- rank decomposition for Z
    have hkerZ : LinearMap.ker Z'.mulVecLin ⊔ LinearMap.ker (Z - Z').mulVecLin = ⊤ := by
      rw [hZ'lin, hdiffZ]
      have hk1 : LinearMap.ker Z'Lin =
          LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin := by
        rw [hZker, sup_eq_left.mpr (le_trans inf_le_right le_sup_left)]
      have hk2 : LinearMap.ker (Z.mulVecLin - Z'Lin) =
          LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin := by
        rw [hZdker, inf_eq_right.mpr le_sup_left]
      rw [hk1, hk2, eq_top_iff, ← h2, sup_le_iff, sup_le_iff]
      exact ⟨⟨le_trans le_sup_left le_sup_right, le_trans le_sup_left le_sup_left⟩,
        le_trans le_sup_right le_sup_left⟩
    have hinfZ : LinearMap.range Z'.mulVecLin ⊓ LinearMap.range (Z - Z').mulVecLin = ⊥ := by
      rw [hZ'lin, hdiffZ]
      have hr2 : LinearMap.range (Z.mulVecLin - Z'Lin) =
          Submodule.map Z.mulVecLin (LinearMap.ker X.mulVecLin) := by
        rw [hZdiffer, Submodule.map_sup, map_ker_eq_bot', bot_sup_eq]
      rw [hZrange, hr2]
      exact map_ker_inf_map_ker_eq_bot_of Z.mulVecLin Y.mulVecLin X.mulVecLin hC' h1'
    have key := rank_add_eq_rank_add_rank Z' (Z - Z') hkerZ hinfZ
    rwa [show Z' + (Z - Z') = Z from by abel] at key
  · -- the pair sums to X
    have hsumLin : Y'Lin + Z'Lin = X.mulVecLin := by
      apply LinearMap.ext
      intro w
      obtain ⟨u, hu, c, hc, huc⟩ :=
        Submodule.mem_sup.mp (show w ∈ LinearMap.ker Y.mulVecLin ⊔
          LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin by rw [h2]; trivial)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
      have hw_eq : w = b + (a + c) := by rw [← huc, ← hab]; abel
      have hw_eq' : w = a + (b + c) := by rw [← huc, ← hab]; abel
      have hac : (a + c) ∈ LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin :=
        Submodule.add_mem_sup ha hc
      have hbc : (b + c) ∈ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin :=
        Submodule.add_mem_sup hb hc
      have hYw : Y'Lin w = Y.mulVecLin b := by
        rw [hw_eq, map_add, hYs b hb, hY'T0 (a + c) hac, add_zero]
      have hZw : Z'Lin w = Z.mulVecLin a := by
        rw [hw_eq', map_add, hZs a ha, hZ'T0 (b + c) hbc, add_zero]
      rw [LinearMap.add_apply, hYw, hZw]
      have key : X.mulVecLin w = Y.mulVecLin b + Z.mulVecLin a := by
        have ha0 : Y.mulVecLin a = 0 := LinearMap.mem_ker.mp ha
        have hb0 : Z.mulVecLin b = 0 := LinearMap.mem_ker.mp hb
        have hc0 : Y.mulVecLin c + Z.mulVecLin c = 0 := by
          have hcx := LinearMap.mem_ker.mp hc
          rwa [hC, LinearMap.add_apply] at hcx
        rw [hw_eq, hC, LinearMap.add_apply]
        simp only [map_add, ha0, hb0, zero_add]
        rw [show (Y.mulVecLin b + Y.mulVecLin c) + (Z.mulVecLin a + Z.mulVecLin c) =
            (Y.mulVecLin b + Z.mulVecLin a) + (Y.mulVecLin c + Z.mulVecLin c) from by abel,
          hc0, add_zero]
      rw [key]
    have hsum : Y' + Z' = X := by
      show Matrix.toLin'.symm Y'Lin + Matrix.toLin'.symm Z'Lin = X
      rw [← map_add, hsumLin, ← Matrix.toLin'_apply']
      exact LinearEquiv.symm_apply_apply Matrix.toLin' X
    exact hsum

end Commons.LinearAlgebra.Matrix