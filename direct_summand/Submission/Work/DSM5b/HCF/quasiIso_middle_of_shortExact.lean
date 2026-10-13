import Mathlib
import Submission.Work.DSM5b.HCF.Complex

/-!
# The five lemma for the middle term of a short exact sequence of complexes

Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` says that for a morphism
`φ : S₁ ⟶ S₂` of short exact short complexes of homological complexes, if `φ.τ₁` and
`φ.τ₂` are quasi-isomorphisms then so is `φ.τ₃`.  Here we prove the *complementary*
statement, with the roles of `τ₂` and `τ₃` interchanged: if `φ.τ₁` and `φ.τ₃` are
quasi-isomorphisms then so is `φ.τ₂`.

The proof is a five-lemma chase on the long exact homology sequences of `S₁` and `S₂`
(`ShortExact.homology_exact₁/₂/₃`, naturality `HomologySequence.δ_naturality`), phrased
in terms of the four-term *windows* of the long exact sequence:

* the window `H^{q}(X₁) → H^{q}(X₂) → H^{q}(X₃) → H^{q+1}(X₁)` (`homSeqWinE`, "E" for the
  epimorphism of the sequence `H^{q}(X₂) → H^{q}(X₃)`): the four-lemma
  `Abelian.epi_of_epi_of_epi_of_mono` gives that `H^{q}(φ.τ₂)` is an epimorphism whenever
  `H^{q}(φ.τ₁)` and `H^{q}(φ.τ₃)` are epimorphisms and `H^{q+1}(φ.τ₁)` is a monomorphism;

* the window `H^{q}(X₃) → H^{q+1}(X₁) → H^{q+1}(X₂) → H^{q+1}(X₃)` (`homSeqWinM`, "M" for
  the monomorphism `H^{q+1}(X₁) → H^{q+1}(X₂)`): the four-lemma
  `Abelian.mono_of_epi_of_mono_of_mono` gives that `H^{q+1}(φ.τ₂)` is a monomorphism
  whenever `H^{q}(φ.τ₃)` is an epimorphism and `H^{q+1}(φ.τ₁)`, `H^{q+1}(φ.τ₃)` are
  monomorphisms.  This needs the connecting map, hence `q + 1 ≥ 1`.

Degree `0` is special for the monomorphism part: there is no `H^{-1}` to invoke, and the
three-term window `H^0(X₁) → H^0(X₂) → H^0(X₃)` (`homSeqWin0`) is used instead, with
`Abelian.mono_of_mono_of_mono_of_mono`; the extra input `H^0(S₂.X₁) → H^0(S₂.X₂)` is a
monomorphism because in degree `0` there are no boundaries, which is
`HomologicalComplex.mono_homologyMap_of_mono_of_not_rel`.

Everything is proved for an arbitrary abelian category `C` (with `ℕ`-indexed cochain
complexes, so that the outgoing differentials exist in every degree); the statement
needed downstream is the specialisation to `C = ModuleCat R`.
-/

namespace Work.DSM5b.HCF

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

universe u v w

-- Allow the definitional unfolding of the windows and of the induced maps
-- (used by `rw`/`refine` in the four-lemma applications below).
set_option backward.isDefEq.respectTransparency false

section Windows

variable {C : Type v} [Category.{w} C] [Abelian C]

/-- The four-term window `H^q(X₁) → H^q(X₂) → H^q(X₃) → H^{q+1}(X₁)` of the long exact
homology sequence of a short exact short complex of cochain complexes. -/
noncomputable def homSeqWinE (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact)
    (q : ℕ) : ComposableArrows C 3 :=
  mk₃ (HomologicalComplex.homologyMap S.f q) (HomologicalComplex.homologyMap S.g q)
    (hS.δ q (q+1) (by simp))

/-- The four-term window `H^q(X₃) → H^{q+1}(X₁) → H^{q+1}(X₂) → H^{q+1}(X₃)` of the long
exact homology sequence of a short exact short complex of cochain complexes. -/
noncomputable def homSeqWinM (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact)
    (q : ℕ) : ComposableArrows C 3 :=
  mk₃ (hS.δ q (q+1) (by simp)) (HomologicalComplex.homologyMap S.f (q+1))
    (HomologicalComplex.homologyMap S.g (q+1))

/-- The three-term window `H^0(X₁) → H^0(X₂) → H^0(X₃)` of the long exact homology
sequence, used to handle degree `0`. -/
noncomputable def homSeqWin0 (S : ShortComplex (CochainComplex C ℕ)) : ComposableArrows C 2 :=
  mk₂ (HomologicalComplex.homologyMap S.f 0) (HomologicalComplex.homologyMap S.g 0)

@[simp]
lemma homSeqWinE_map'_0_1 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 0 ≤ 1) (hk : 1 ≤ 3) :
    (homSeqWinE S hS q).map' 0 1 hij hk = HomologicalComplex.homologyMap S.f q := rfl

@[simp]
lemma homSeqWinE_map'_1_2 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 1 ≤ 2) (hk : 2 ≤ 3) :
    (homSeqWinE S hS q).map' 1 2 hij hk = HomologicalComplex.homologyMap S.g q := rfl

@[simp]
lemma homSeqWinE_map'_2_3 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 2 ≤ 3) (hk : 3 ≤ 3) :
    (homSeqWinE S hS q).map' 2 3 hij hk = hS.δ q (q+1) (by simp) := rfl

@[simp]
lemma homSeqWinM_map'_0_1 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 0 ≤ 1) (hk : 1 ≤ 3) :
    (homSeqWinM S hS q).map' 0 1 hij hk = hS.δ q (q+1) (by simp) := rfl

@[simp]
lemma homSeqWinM_map'_1_2 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 1 ≤ 2) (hk : 2 ≤ 3) :
    (homSeqWinM S hS q).map' 1 2 hij hk = HomologicalComplex.homologyMap S.f (q+1) := rfl

@[simp]
lemma homSeqWinM_map'_2_3 (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ)
    (hij : 2 ≤ 3) (hk : 3 ≤ 3) :
    (homSeqWinM S hS q).map' 2 3 hij hk = HomologicalComplex.homologyMap S.g (q+1) := rfl

@[simp]
lemma homSeqWin0_map'_0_1 (S : ShortComplex (CochainComplex C ℕ))
    (hij : 0 ≤ 1) (hk : 1 ≤ 2) :
    (homSeqWin0 S).map' 0 1 hij hk = HomologicalComplex.homologyMap S.f 0 := rfl

@[simp]
lemma homSeqWin0_map'_1_2 (S : ShortComplex (CochainComplex C ℕ))
    (hij : 1 ≤ 2) (hk : 2 ≤ 2) :
    (homSeqWin0 S).map' 1 2 hij hk = HomologicalComplex.homologyMap S.g 0 := rfl

/-- The three-term window `H^0(X₁) → H^0(X₂) → H^0(X₃)` is exact. -/
lemma homSeqWin0_exact (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) :
    (homSeqWin0 S).Exact := by
  rw [homSeqWin0]
  exact (hS.homology_exact₂ 0).exact_toComposableArrows

/-- The four-term window `H^q(X₁) → H^q(X₂) → H^q(X₃) → H^{q+1}(X₁)` is exact. -/
lemma homSeqWinE_exact (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ) :
    (homSeqWinE S hS q).Exact := by
  rw [homSeqWinE]
  refine exact_of_δ₀ ?_ ?_
  · exact (hS.homology_exact₂ q).exact_toComposableArrows
  · exact (hS.homology_exact₃ q (q+1) (by simp)).exact_toComposableArrows

/-- The four-term window `H^q(X₃) → H^{q+1}(X₁) → H^{q+1}(X₂) → H^{q+1}(X₃)` is exact. -/
lemma homSeqWinM_exact (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) (q : ℕ) :
    (homSeqWinM S hS q).Exact := by
  rw [homSeqWinM]
  refine exact_of_δ₀ ?_ ?_
  · exact (hS.homology_exact₁ q (q+1) (by simp)).exact_toComposableArrows
  · exact (hS.homology_exact₂ (q+1)).exact_toComposableArrows

/-- The morphism of four-term windows `homSeqWinE S₁ hS₁ q ⟶ homSeqWinE S₂ hS₂ q` induced
by a morphism `φ : S₁ ⟶ S₂` of short exact short complexes of cochain complexes. -/
noncomputable def homSeqWinE_hom {S₁ S₂ : ShortComplex (CochainComplex C ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (q : ℕ) :
    homSeqWinE S₁ hS₁ q ⟶ homSeqWinE S₂ hS₂ q :=
  homMk₃ (HomologicalComplex.homologyMap φ.τ₁ q) (HomologicalComplex.homologyMap φ.τ₂ q)
    (HomologicalComplex.homologyMap φ.τ₃ q) (HomologicalComplex.homologyMap φ.τ₁ (q+1))
    (by rw [homSeqWinE_map'_0_1, homSeqWinE_map'_0_1,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₁₂])
    (by rw [homSeqWinE_map'_1_2, homSeqWinE_map'_1_2,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₂₃])
    (by rw [homSeqWinE_map'_2_3, homSeqWinE_map'_2_3]
        exact HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ q (q+1) (by simp))

/-- The morphism of four-term windows `homSeqWinM S₁ hS₁ q ⟶ homSeqWinM S₂ hS₂ q` induced
by a morphism `φ : S₁ ⟶ S₂` of short exact short complexes of cochain complexes. -/
noncomputable def homSeqWinM_hom {S₁ S₂ : ShortComplex (CochainComplex C ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (q : ℕ) :
    homSeqWinM S₁ hS₁ q ⟶ homSeqWinM S₂ hS₂ q :=
  homMk₃ (HomologicalComplex.homologyMap φ.τ₃ q) (HomologicalComplex.homologyMap φ.τ₁ (q+1))
    (HomologicalComplex.homologyMap φ.τ₂ (q+1)) (HomologicalComplex.homologyMap φ.τ₃ (q+1))
    (by rw [homSeqWinM_map'_0_1, homSeqWinM_map'_0_1]
        exact HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ q (q+1) (by simp))
    (by rw [homSeqWinM_map'_1_2, homSeqWinM_map'_1_2,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₁₂])
    (by rw [homSeqWinM_map'_2_3, homSeqWinM_map'_2_3,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₂₃])

/-- The morphism of three-term windows `homSeqWin0 S₁ ⟶ homSeqWin0 S₂` induced by a
morphism `φ : S₁ ⟶ S₂` of short exact short complexes of cochain complexes. -/
noncomputable def homSeqWin0_hom {S₁ S₂ : ShortComplex (CochainComplex C ℕ)} (φ : S₁ ⟶ S₂) :
    homSeqWin0 S₁ ⟶ homSeqWin0 S₂ :=
  homMk₂ (HomologicalComplex.homologyMap φ.τ₁ 0) (HomologicalComplex.homologyMap φ.τ₂ 0)
    (HomologicalComplex.homologyMap φ.τ₃ 0)
    (by rw [homSeqWin0_map'_0_1, homSeqWin0_map'_0_1,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₁₂])
    (by rw [homSeqWin0_map'_1_2, homSeqWin0_map'_1_2,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        φ.comm₂₃])

end Windows

/-- **Five-term exactness for the middle term of a short exact sequence of complexes** (general
abelian-category form):  if `φ : S₁ ⟶ S₂` is a morphism of short exact short complexes of
`ℕ`-indexed cochain complexes and the induced maps on the first and third terms are
quasi-isomorphisms, then so is the map on the middle term. -/
theorem quasiIso_middle_of_shortExact_gen {C : Type v} [Category.{w} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h1i : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₁ i) :=
    fun i => (quasiIsoAt_iff_isIso_homologyMap φ.τ₁ i).1 (h₁.quasiIsoAt i)
  have h3i : ∀ i, IsIso (HomologicalComplex.homologyMap φ.τ₃ i) :=
    fun i => (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ i).1 (h₃.quasiIsoAt i)
  have hmono : Mono (HomologicalComplex.homologyMap φ.τ₂ q) := by
    rcases q with _ | m
    · -- degree `0`: the three-term window, no connecting map is available
      have hmf : Mono S₂.f := hS₂.mono_f
      have h10 : IsIso (HomologicalComplex.homologyMap φ.τ₁ 0) := h1i 0
      have h30 : IsIso (HomologicalComplex.homologyMap φ.τ₃ 0) := h3i 0
      have hfr : Mono (HomologicalComplex.homologyMap S₂.f 0) :=
        HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f 0
          (fun i hi => Nat.succ_ne_zero i hi)
      refine Abelian.mono_of_mono_of_mono_of_mono (homSeqWin0_hom φ)
        (homSeqWin0_exact S₁ hS₁) hfr ?_ ?_
      · show Mono (HomologicalComplex.homologyMap φ.τ₁ 0)
        infer_instance
      · show Mono (HomologicalComplex.homologyMap φ.τ₃ 0)
        infer_instance
    · -- degree `m + 1`: the window through the connecting map `H^m(X₃) → H^{m+1}(X₁)`
      have hm : IsIso (HomologicalComplex.homologyMap φ.τ₃ m) := h3i m
      have hm1 : IsIso (HomologicalComplex.homologyMap φ.τ₁ (m+1)) := h1i (m+1)
      have hm1' : IsIso (HomologicalComplex.homologyMap φ.τ₃ (m+1)) := h3i (m+1)
      refine Abelian.mono_of_epi_of_mono_of_mono (homSeqWinM_hom φ hS₁ hS₂ m)
        (homSeqWinM_exact S₁ hS₁ m) (homSeqWinM_exact S₂ hS₂ m) ?_ ?_ ?_
      · show Epi (HomologicalComplex.homologyMap φ.τ₃ m)
        infer_instance
      · show Mono (HomologicalComplex.homologyMap φ.τ₁ (m+1))
        infer_instance
      · show Mono (HomologicalComplex.homologyMap φ.τ₃ (m+1))
        infer_instance
  have hepi : Epi (HomologicalComplex.homologyMap φ.τ₂ q) := by
    have h1q : IsIso (HomologicalComplex.homologyMap φ.τ₁ q) := h1i q
    have h3q : IsIso (HomologicalComplex.homologyMap φ.τ₃ q) := h3i q
    have h1q1 : IsIso (HomologicalComplex.homologyMap φ.τ₁ (q+1)) := h1i (q+1)
    refine Abelian.epi_of_epi_of_epi_of_mono (homSeqWinE_hom φ hS₁ hS₂ q)
      (homSeqWinE_exact S₁ hS₁ q) (homSeqWinE_exact S₂ hS₂ q) ?_ ?_ ?_
    · show Epi (HomologicalComplex.homologyMap φ.τ₁ q)
      infer_instance
    · show Epi (HomologicalComplex.homologyMap φ.τ₃ q)
      infer_instance
    · show Mono (HomologicalComplex.homologyMap φ.τ₁ (q+1))
      infer_instance
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap φ.τ₂ q)

/-- **Five-term exactness for the middle term of a short exact sequence of complexes.**  If
`φ : S₁ ⟶ S₂` is a morphism of short exact short complexes of cochain complexes of `R`-modules and
the induced maps on the first and third terms are quasi-isomorphisms, then so is the map on the
middle term.  (The `τ₃` version, `HomologicalComplex.HomologySequence.quasiIso_τ₃`, is in Mathlib;
this is the complementary `τ₂` version, needed for the size filtration of the chart complex.)

Route: use the long exact homology sequences of `S₁` and `S₂`
(`CategoryTheory.ShortComplex.ShortExact.homology_exact₁/₂/₃`, `δ`, `δ_naturality`, `δ_comp`,
`comp_δ`) and the four-term windows of the long exact sequence, together with the four lemmas
`Abelian.epi_of_epi_of_epi_of_mono`, `Abelian.mono_of_epi_of_mono_of_mono` and (in degree `0`)
`Abelian.mono_of_mono_of_mono_of_mono`; at degree `0` the map `H^0(S₂.X₁) → H^0(S₂.X₂)` is a
monomorphism for a different reason (no boundaries in degree `0`), namely
`HomologicalComplex.mono_homologyMap_of_mono_of_not_rel`.  Conclude with
`quasiIsoAt_iff_isIso_homologyMap` and `QuasiIso` (both root-level). -/
theorem quasiIso_middle_of_shortExact {R : Type u} [CommRing R]
    {S₁ S₂ : CategoryTheory.ShortComplex (CochainComplex (ModuleCat R) ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ :=
  quasiIso_middle_of_shortExact_gen φ hS₁ hS₂ h₁ h₃

end Work.DSM5b.HCF
