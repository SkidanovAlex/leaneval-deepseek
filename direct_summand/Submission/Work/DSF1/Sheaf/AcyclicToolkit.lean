import Mathlib
import ChallengeDeps

/-!
# Toolkit for the "acyclic resolution computes the right derived functor" lemma

Vocabulary shared by `Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution` and the
lemmas delegated for it:

* `singlePlusObj C M` — the one-term complex `M[0]` as a bounded below cochain complex;
* `syz K n` — the `n`-th syzygy of an `ℕ`-indexed cochain complex `K`, i.e. the kernel of the
  differential `K.d n (n+1)`;
* `syzIncl K n`, `syzProj K n`, `syzSES K n` — the maps and the short complex
  `0 → syz K n → K.X n → syz K (n+1) → 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.DSF1.Sheaf

universe u v w x

/-- The one-term complex `M[0]` (all terms but the degree `0` term are zero), as an object of
the category of bounded below cochain complexes. -/
noncomputable def singlePlusObj (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] (M : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩

section Syz

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ)

/-- The `n`-th syzygy of an `ℕ`-indexed cochain complex: the kernel of `K.d n (n+1)`. -/
noncomputable def syz (n : ℕ) : C := Limits.kernel (K.d n (n+1))

/-- The inclusion of the `n`-th syzygy into `K.X n`. -/
noncomputable def syzIncl (n : ℕ) : syz K n ⟶ K.X n :=
  Limits.kernel.ι (K.d n (n+1))

/-- The projection `K.X n → syz K (n+1)`, the corestriction of the differential. -/
noncomputable def syzProj (n : ℕ) : K.X n ⟶ syz K (n+1) :=
  Limits.kernel.lift (K.d (n+1) (n+2)) (K.d n (n+1)) (HomologicalComplex.d_comp_d K n (n+1) (n+2))

@[reassoc (attr := simp)]
lemma syzProj_comp_syzIncl (n : ℕ) :
    syzProj K n ≫ syzIncl K (n+1) = K.d n (n+1) :=
  Limits.kernel.lift_ι _ _ _

/-- The short complex `0 → syz K n → K.X n → syz K (n+1) → 0`. -/
noncomputable def syzSES (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (syzIncl K n) (syzProj K n) (by
    change Limits.kernel.ι (K.d n (n+1)) ≫
      Limits.kernel.lift (K.d (n+1) (n+2)) (K.d n (n+1))
        (HomologicalComplex.d_comp_d K n (n+1) (n+2)) = 0
    rw [← cancel_mono (Limits.kernel.ι (K.d (n+1) (n+2))), Category.assoc,
      Limits.kernel.lift_ι, Limits.kernel.condition, zero_comp])

@[simp]
lemma syzSES_f (n : ℕ) : (syzSES K n).f = syzIncl K n := rfl

@[simp]
lemma syzSES_g (n : ℕ) : (syzSES K n).g = syzProj K n := rfl

@[simp]
lemma syzSES_X₂ (n : ℕ) : (syzSES K n).X₂ = K.X n := rfl

@[simp]
lemma syzSES_X₁ (n : ℕ) : (syzSES K n).X₁ = syz K n := rfl

@[simp]
lemma syzSES_X₃ (n : ℕ) : (syzSES K n).X₃ = syz K (n+1) := rfl

end Syz

end Work.DSF1.Sheaf
