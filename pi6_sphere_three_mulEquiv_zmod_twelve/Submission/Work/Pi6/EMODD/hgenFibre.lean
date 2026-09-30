import Mathlib
import Submission.Work.Pi6.EMODD.Defs
import Submission.Work.Pi6.EMODD.fibreOfMpathQ
import Submission.Work.Pi6.EMODD.hurewiczGenerates
import Submission.Work.Pi6.EMODD.generatorZpow
import Submission.Work.Pi6.EMODD.kerTwoZmodTwo
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.fibrationLES_of_serre
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The fibre inclusion of the mapping-path fibration is `×2` on `H₂`

This file proves `Work.Pi6.EMODD.hgenFibre`: for the mapping path fibration of a map
`r : T → X` from a range model of `K(ℤ,2)` to a range model of `K(ℤ/2,2)` (through `N ≥ 11`) which
is non-trivial on `π₂`, the fibre inclusion `ι : F → mpath r` is multiplication by `2` on the
generators of `H₂(-;ℤ) ≅ ℤ`.

The pieces:

* `HgenFibreAux.zpow_symm_ofAdd`, `HgenFibreAux.generator_expand`: bookkeeping for the generator
  `e.symm (Multiplicative.ofAdd 1)` of a group isomorphic to `ℤ`.
* `HgenFibreAux.piTwoValue`: the abstract group-theoretic core.  Given `MulExact ι q` with `q`
  surjective onto a group isomorphic to `ℤ/2` (so that `ker q` is the subgroup of even elements,
  `Work.Pi6.EMODD.kerTwoZmodTwo`), the element `ι (gF)` is `gT^{±2}`; hence `ι (gF^k) = gT^2` for
  `k = ±1`.
* the main theorem assembles this with the long exact homotopy sequence
  (`Work.StemsB.FibrationLES`), the Hurewicz isomorphism in degree `2`
  (`Work.Stems.hurewicz_first_degree`, `Work.Pi6.EMODD.hurewiczGenerates`) and its naturality
  (`Work.Stems.hurewiczMap_natural`).
-/

open scoped Topology

namespace Work.Pi6.EMODD

namespace HgenFibreAux

noncomputable section

/-- For a multiplicative equivalence `e : G ≃* Multiplicative ℤ`, the preimage of `ofAdd m` is the
`m`-th power of the generator `e.symm (ofAdd 1)`. -/
theorem zpow_symm_ofAdd {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (m : ℤ) :
    e.symm (Multiplicative.ofAdd m) = (e.symm (Multiplicative.ofAdd 1)) ^ m := by
  rw [show (e.symm (Multiplicative.ofAdd 1)) ^ m
      = e.symm ((Multiplicative.ofAdd (1 : ℤ)) ^ m) from (map_zpow e.symm _ _).symm,
    Work.Pi6.EMODD.FibreAux.ofAdd_one_zpow_int]

/-- Every element of `G` is the `(e y).toAdd`-th power of the generator `e.symm (ofAdd 1)`. -/
theorem generator_expand {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (y : G) :
    y = (e.symm (Multiplicative.ofAdd 1)) ^ ((e y).toAdd) := by
  rw [← zpow_symm_ofAdd e ((e y).toAdd), ofAdd_toAdd, MulEquiv.symm_apply_apply]

/-- **The abstract core of the computation.**  Let `ι : G →* E` and `q : E →* B` be homomorphisms
with `MulExact ι q`, `q` surjective, `G ≅ ℤ`, `E ≅ ℤ` and `B ≅ ℤ/2`.  Then `ι` sends the generator
of `G` to `±2` times the generator of `E`; consequently `ι (gF^k) = gT^2` for a suitable sign
`k = ±1`.

Proof: `ι (gF)` lies in `ker q`, which `Work.Pi6.EMODD.kerTwoZmodTwo` identifies with the even
elements, so `ι (gF) = gT^n` with `2 ∣ n`; on the other hand `gT^2 ∈ ker q = range ι`, so
`gT^2 = ι (gF^m) = gT^{nm}` and `n * m = 2`.  Thus `n = 2k` with `k m = 1`, i.e. `k = ±1`, and then
`ι (gF^k) = gT^{n k} = gT^{2 k^2} = gT^2`. -/
theorem piTwoValue {G E B : Type*} [Group G] [Group E] [Group B]
    (ι : G →* E) (q : E →* B) (hex : Function.MulExact ι q) (hq : Function.Surjective q)
    (eG : G ≃* Multiplicative ℤ) (eE : E ≃* Multiplicative ℤ)
    (eB : B ≃* Multiplicative (ZMod 2)) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      ι ((eG.symm (Multiplicative.ofAdd 1)) ^ k)
        = (eE.symm (Multiplicative.ofAdd 1)) ^ (2 : ℤ) := by
  classical
  have hdiv : (2 : ℤ) ∣ (eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd :=
    (kerTwoZmodTwo q hq eE eB _).mp ((hex _).mpr ⟨_, rfl⟩)
  have hstep2 : ∃ m : ℤ,
      (eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd * m = 2 := by
    have hy2 : (eE ((eE.symm (Multiplicative.ofAdd 1)) ^ (2 : ℤ))).toAdd = 2 := by
      rw [map_zpow, MulEquiv.apply_symm_apply, Work.Pi6.EMODD.FibreAux.ofAdd_one_zpow_int,
        toAdd_ofAdd]
    have hqy : q ((eE.symm (Multiplicative.ofAdd 1)) ^ (2 : ℤ)) = 1 :=
      (kerTwoZmodTwo q hq eE eB _).mpr (by rw [hy2])
    obtain ⟨x, hx⟩ := (hex _).mp hqy
    refine ⟨(eG x).toAdd, ?_⟩
    have ha : ι (eG.symm (Multiplicative.ofAdd 1))
        = (eE.symm (Multiplicative.ofAdd 1))
            ^ ((eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd) :=
      generator_expand eE _
    have hx' : ι x = (ι (eG.symm (Multiplicative.ofAdd 1))) ^ ((eG x).toAdd) := by
      conv_lhs => rw [generator_expand eG x]
      rw [map_zpow]
    have h1 : (eE.symm (Multiplicative.ofAdd 1)) ^ (2 : ℤ)
        = (eE.symm (Multiplicative.ofAdd 1))
            ^ ((eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd * (eG x).toAdd) := by
      calc (eE.symm (Multiplicative.ofAdd 1)) ^ (2 : ℤ)
          = ι x := hx.symm
        _ = (ι (eG.symm (Multiplicative.ofAdd 1))) ^ ((eG x).toAdd) := hx'
        _ = ((eE.symm (Multiplicative.ofAdd 1))
              ^ ((eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd)) ^ ((eG x).toAdd) := by
              conv_lhs => rw [ha]
        _ = (eE.symm (Multiplicative.ofAdd 1))
              ^ ((eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd * (eG x).toAdd) := by
              rw [← zpow_mul]
    have h2 := congrArg (fun y => (eE y).toAdd) h1
    simp only [map_zpow, MulEquiv.apply_symm_apply, Work.Pi6.EMODD.FibreAux.ofAdd_one_zpow_int,
      toAdd_ofAdd] at h2
    exact h2.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (eE (ι (eG.symm (Multiplicative.ofAdd 1)))).toAdd = 2 * k := hdiv
  have hk1 : k = 1 ∨ k = -1 := by
    obtain ⟨m, hm⟩ := hstep2
    rw [hk] at hm
    have hkm : k * m = 1 := by
      have h : 2 * (k * m) = 2 * 1 := by rw [← mul_assoc, mul_one]; exact hm
      exact mul_left_cancel₀ (by norm_num) h
    exact Int.eq_one_or_neg_one_of_mul_eq_one hkm
  refine ⟨k, hk1, ?_⟩
  rw [map_zpow, generator_expand eE (ι (eG.symm (Multiplicative.ofAdd 1))), hk, ← zpow_mul]
  congr 1
  rcases hk1 with h | h <;> rw [h] <;> ring

end

end HgenFibreAux

/-- **The fibre inclusion of the mapping-path fibration of `r : K(ℤ,2)-model → K(ℤ/2,2)-model` is `×2` on `H₂ = ℤ`.**

With `r : T → X` as in `Work.Pi6.EMODD.fibreOfMpathQ` (range `N ≥ 11` so that the fibre is a `K(ℤ,2)`-model through `10`), the fibre inclusion `ι = Work.StemsB.fibreIncl (Work.Serre.mpathQ r) (Work.Serre.mpathQ r (mpathPt r k₀))` induces on integral `H₂` the map sending a generator `zF` of `H₂(F;ℤ) ≅ ℤ` to `±2` times a generator `zT` of `H₂(T;ℤ) ≅ ℤ`, normalised so that the factor is `+2` (replace `zF` by `-zF` if necessary).

(Route: both `F` and `T` are `2`-connected range models of `K(ℤ,2)`, so the Hurewicz map is an isomorphism in degree `2` (`Work.Stems.hurewicz_first_degree`) and is natural (`Work.Stems.hurewiczMap_natural`); the long exact homotopy sequence `Work.StemsB.FibrationLES` of `mpathQ r` shows that the image of `π₂(ι)` is the kernel of the surjection `π₂(T) ≅ ℤ ↠ π₂(X) ≅ ℤ/2`, i.e. `2ℤ`, and `π₂(ι)` is injective, so on generators it is multiplication by `±2`.) -/
theorem hgenFibre (N : ℕ) (hN : 11 ≤ N) {T X : Type} [TopologicalSpace T] [TopologicalSpace X]
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

end Work.Pi6.EMODD
