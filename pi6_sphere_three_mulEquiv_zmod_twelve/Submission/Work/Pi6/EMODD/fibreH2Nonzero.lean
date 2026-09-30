import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMODD.Defs
import Submission.Work.Pi6.EMODD.fibreOfMpathQ
import Submission.Work.Pi6.EMODD.hgenFibre
import Submission.Work.Pi6.EMODD.hmapTwoNeZero
import Submission.Work.Pi6.SQASM.dualityNonzero
import Submission.Work.Pi6.SQASM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The fibre inclusion of the mapping-path fibration is non-zero on `H²(-;𝕜)`

`Work.Pi6.EMODD.fibreH2Nonzero`: for a based map `r : T → X` from a range model of `K(ℤ,2)` to a
range model of `K(ℤ/2,2)` through `N ≥ 10` which is non-trivial on `π₂`, the inclusion
`ι : F → mpath r` of the fibre of the Serre fibration `Work.Serre.mpathQ r` induces a non-zero map
on `H²(-;𝕜)` in degree `2`, for every field `𝕜` of characteristic `≠ 2`.

The argument has three steps.

* `hgenFibreTen`: in the same situation with `N ≥ 10`, the fibre inclusion is `±2` on the
  generators of `H₂(-;ℤ) ≅ ℤ`.  This is `Work.Pi6.EMODD.hgenFibre` (stated for `11 ≤ N`) with the
  bound weakened to `10 ≤ N`; the proof only ever uses `N` through
  `Work.Pi6.EMODD.fibreOfMpathQ`, which is available as soon as `10 ≤ N`, so the proof body is the
  same (both spaces are range models of `K(ℤ,2)` through `9`, Hurewicz is an isomorphism in degree
  `2`, and the long exact sequence of `mpathQ r` identifies `π₂(ι)` with the kernel `2ℤ` of the
  surjection `π₂(T) ≅ ℤ ↠ π₂(X) ≅ ℤ/2`).

* `Work.Pi6.EMODD.hmapTwoNeZero`: a map of `K(ℤ,2)`-range models carrying a generator of
  `H₂(-;ℤ)` to twice a generator stays non-zero after base change to `𝕜`, since `(2 : 𝕜) ≠ 0`.

* `Work.Pi6.SQASM.dualityNonzero`: over a field the Kronecker pairing is a bijection, so `cmap` is
  zero exactly when `hmap` is; here it converts the non-vanishing on `H₂(-;𝕜)` into the
  non-vanishing on `H²(-;𝕜)`.

(Note `cmap`/`hmap` are morphisms of `ModuleCat`, so the auxiliary `moduleCatHom_ne_zero_iff`
translates between a morphism being non-zero and its underlying function being non-zero.)
-/

open scoped Topology

namespace Work.Pi6.EMODD

noncomputable section

/-- A morphism of `ModuleCat` is non-zero if and only if its underlying function is non-zero
(equivalently: morphisms of `ModuleCat` are equal as soon as their underlying functions are). -/
lemma moduleCatHom_ne_zero_iff {R : Type} [Ring R] {M N : ModuleCat R} (f : M ⟶ N) :
    f ≠ 0 ↔ f.hom ≠ 0 := by
  constructor
  · intro hf h0
    exact hf (ModuleCat.hom_ext (by rw [h0, ModuleCat.hom_zero]))
  · intro hf h0
    exact hf (by rw [h0]; simp)

/-- **The fibre inclusion of the mapping-path fibration of `r : K(ℤ,2)-model → K(ℤ/2,2)-model` is
`×2` on `H₂ = ℤ`, in the range `N ≥ 10`.**

This is `Work.Pi6.EMODD.hgenFibre` with the range hypothesis weakened from `11 ≤ N` to `10 ≤ N`:
the only use of `N` in that proof is the call `Work.Pi6.EMODD.fibreOfMpathQ N (by omega) ...`, whose
hypothesis is `10 ≤ N`.  So `F = mpathFibre r k₀` and `mpath r` are range models of `K(ℤ,2)`
(through `N - 1 ≥ 9` and `N ≥ 10` respectively), the Hurewicz map is an isomorphism in degree `2`,
and the long exact homotopy sequence of `mpathQ r` shows that `π₂(ι)` is injective with image the
kernel `2ℤ` of the surjection `π₂(T) ≅ ℤ ↠ π₂(X) ≅ ℤ/2`; hence `ι` sends a generator `zF` of
`H₂(F;ℤ) ≅ ℤ` to `±2` times a generator `zT` of `H₂(mpath r;ℤ) ≅ ℤ`, normalised to `+2` by
replacing `zF` by `-zF` if necessary. -/
theorem hgenFibreTen (N : ℕ) (hN : 10 ≤ N) {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
    (r : C(T, X)) (k₀ : T)
    (hT : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N T k₀)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X (r k₀))
    (hπ : ∃ a : HomotopyGroup (Fin 2) T k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1) :
    ∃ (zF : Work.Pi6.HR ℤ (Work.Pi6.EMODD.mpathFibre r k₀) 2)
      (zT : Work.Pi6.HR ℤ (Work.Serre.mpath r) 2),
      (∀ z : Work.Pi6.HR ℤ (Work.Pi6.EMODD.mpathFibre r k₀) 2, ∃! n : ℤ, z = n • zF) ∧
      (∀ z : Work.Pi6.HR ℤ (Work.Serre.mpath r) 2, ∃! n : ℤ, z = n • zT) ∧
      (Work.Pi6.hmap ℤ (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
        (Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀))) 2).hom zF = (2 : ℤ) • zT := by
  classical
  -- ## The fibre and the total space are range models of `K(ℤ,2)`
  obtain ⟨hF, -, hMp⟩ := Work.Pi6.EMODD.fibreOfMpathQ N (by omega) r k₀ hT hX hπ
  -- ## Hurewicz is an isomorphism in degree `2` for both
  have hconnF : ∀ i : ℕ, i < 2 →
      Subsingleton (HomotopyGroup (Fin i) (mpathFibre r k₀) (mpathFibrePt r k₀)) :=
    fun i hi => hF.2 i (by omega) (Or.inl hi)
  have hconnM : ∀ i : ℕ, i < 2 →
      Subsingleton (HomotopyGroup (Fin i) (Serre.mpath r) (mpathPt r k₀)) :=
    fun i hi => hMp.2 i (by omega) (Or.inl hi)
  have hbijF := Work.Stems.hurewicz_first_degree 2 (by norm_num) (mpathFibrePt r k₀) hconnF
  have hbijM := Work.Stems.hurewicz_first_degree 2 (by norm_num) (mpathPt r k₀) hconnM
  -- ## `π₂` of both spaces is infinite cyclic
  obtain ⟨eF⟩ := hF.1
  obtain ⟨eM⟩ := hMp.1
  -- ## The long exact sequence of the Serre fibration `mpathQ r`
  have heX : HomotopyGroup (Fin 2) X (r k₀) ≃* Multiplicative (ZMod 2) := hX.1.some
  have hsurj : Function.Surjective (Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)) :=
    Work.Pi6.EMODD.FibreAux.surjective_piTwo_mpathQ r k₀ heX hπ
  have hserre : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ r) :=
    Work.Serre.mpathQ_isSerreFibration r
  have hLES : Work.StemsB.FibrationLES (Work.Serre.mpathQ r) (mpathPt r k₀) :=
    Work.StemsB.fibrationLES_of_isSerreFibration (Work.Serre.mpathQ r) hserre (mpathPt r k₀)
  obtain ⟨d0, hex0, -, -⟩ := hLES 0
  -- ## The abstract computation on `π₂`
  obtain ⟨k, hk, hval⟩ := HgenFibreAux.piTwoValue
    (Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
      (Work.Serre.mpathQ r (mpathPt r k₀))) 1 (mpathFibrePt r k₀))
    (Work.StemsB.πmap (Work.Serre.mpathQ r) 1 (mpathPt r k₀)) hex0 hsurj eF eM heX
  refine ⟨Work.Stems.hurewiczMapN 2 (by norm_num) (mpathFibrePt r k₀)
            ((eF.symm (Multiplicative.ofAdd 1)) ^ k),
          Work.Stems.hurewiczMapN 2 (by norm_num) (mpathPt r k₀)
            (eM.symm (Multiplicative.ofAdd 1)), ?_, ?_, ?_⟩
  · exact Work.Pi6.EMODD.hurewiczGenerates (mpathFibrePt r k₀) hbijF _
      (Work.Pi6.EMODD.generatorZpow eF k hk)
  · have hgenT : ∀ a : HomotopyGroup (Fin 2) (Serre.mpath r) (mpathPt r k₀),
        ∃! m : ℤ, a = (eM.symm (Multiplicative.ofAdd 1)) ^ m := by
      have h := Work.Pi6.EMODD.generatorZpow eM 1 (Or.inl rfl)
      rw [show ((eM.symm (Multiplicative.ofAdd 1)) ^ (1 : ℤ))
          = eM.symm (Multiplicative.ofAdd 1) from zpow_one _] at h
      exact h
    exact Work.Pi6.EMODD.hurewiczGenerates (mpathPt r k₀) hbijM _ hgenT
  · -- Naturality of the Hurewicz map converts the statement on `H₂` into one on `π₂`
    have key : (Work.Pi6.hmap ℤ (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
          (Work.Serre.mpathQ r (mpathPt r k₀))) 2).hom
        (Work.Stems.hurewiczMapN 2 (by norm_num) (mpathFibrePt r k₀)
          ((eF.symm (Multiplicative.ofAdd 1)) ^ k))
      = Work.Stems.hurewiczMapN 2 (by norm_num) (mpathPt r k₀)
        (HomotopyGroup.map (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
          (Work.Serre.mpathQ r (mpathPt r k₀)))
          ((eF.symm (Multiplicative.ofAdd 1)) ^ k)) := by
      rw [Work.Stems.hurewiczMapN_eq_hurewiczMap 2 (by norm_num) (mpathFibrePt r k₀),
        Work.Stems.hurewiczMapN_eq_hurewiczMap 2 (by norm_num) (mpathPt r k₀)]
      exact (Work.Stems.hurewiczMap_natural 2 (by norm_num)
        (Work.StemsB.fibreIncl (Work.Serre.mpathQ r) (Work.Serre.mpathQ r (mpathPt r k₀)))
        ((eF.symm (Multiplicative.ofAdd 1)) ^ k)).symm
    rw [key,
      show HomotopyGroup.map (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
          (Work.Serre.mpathQ r (mpathPt r k₀)))
          ((eF.symm (Multiplicative.ofAdd 1)) ^ k)
        = Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
            (Work.Serre.mpathQ r (mpathPt r k₀))) 1 (mpathFibrePt r k₀)
            ((eF.symm (Multiplicative.ofAdd 1)) ^ k) from rfl,
      hval]
    exact Work.Pi6.EMODD.hurewiczMapN_zpow (mpathPt r k₀)
      (eM.symm (Multiplicative.ofAdd 1)) 2

theorem fibreH2Nonzero (𝕜 : Type) [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (N : ℕ) (hN : 10 ≤ N)
    {T X : Type} [TopologicalSpace T] [TopologicalSpace X] (r : ContinuousMap T X) (k₀ : T)
    (hT : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N T k₀)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X (r k₀))
    (hπ : ∃ a : HomotopyGroup (Fin 2) T k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1) :
    (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
      (Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀))) 2).hom ≠ 0 := by
  classical
  set ι : C(mpathFibre r k₀, Work.Serre.mpath r) :=
    Work.StemsB.fibreIncl (Work.Serre.mpathQ r) (Work.Serre.mpathQ r (mpathPt r k₀)) with hι
  -- ## Step 1: the fibre inclusion is `×2` on integral `H₂`
  obtain ⟨zF, zT, hzF, hzT, hσ⟩ := hgenFibreTen N hN r k₀ hT hX hπ
  -- ## Step 2: `F` and `mpath r` are range models of `K(ℤ,2)` through `9`
  obtain ⟨hF, -, hMp⟩ := Work.Pi6.EMODD.fibreOfMpathQ N hN r k₀ hT hX hπ
  have hF9 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 9 (mpathFibre r k₀)
      (mpathFibrePt r k₀) :=
    Work.Pi6.SQASM.isEMSpaceUpTo_mono (A := ℤ) (m := 2) (N := 9) (N' := N - 1)
      (by norm_num) (by omega) (mpathFibrePt r k₀) hF
  have hMp9 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 9 (Work.Serre.mpath r)
      (mpathPt r k₀) :=
    Work.Pi6.SQASM.isEMSpaceUpTo_mono (A := ℤ) (m := 2) (N := 9) (N' := N)
      (by norm_num) (by omega) (mpathPt r k₀) hMp
  -- ## Step 3: base change to `𝕜` keeps the map non-zero on `H₂`
  have hne : (Work.Pi6.hmap 𝕜 ι 2).hom ≠ 0 :=
    Work.Pi6.EMODD.hmapTwoNeZero 𝕜 h2 ι (mpathFibrePt r k₀) hF9 hMp9 ⟨zF, zT, hzF, hzT, hσ⟩
  -- ## Step 4: Kronecker duality converts this into the statement on `H²`
  have hne' : Work.Pi6.hmap 𝕜 ι 2 ≠ 0 := (moduleCatHom_ne_zero_iff _).mpr hne
  have hcm : Work.Pi6.cmap 𝕜 ι 2 ≠ 0 := (Work.Pi6.SQASM.dualityNonzero 𝕜 ι 2).mpr hne'
  exact (moduleCatHom_ne_zero_iff _).mp hcm

end

end Work.Pi6.EMODD
