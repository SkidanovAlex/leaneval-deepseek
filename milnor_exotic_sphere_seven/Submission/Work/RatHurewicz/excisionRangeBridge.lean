import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.Triad.Assembly
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The comparison map is a homeomorphism onto its range

The last step in the assembly of `Work.RatHurewicz.excisionRelPiVanishing` passes from the
compression property of the pair `(F, range ι)` (Puppe's theorem
`Work.RatHurewicz.triadCompression`) to the bijectivity of `πmap ι` in the range, where
`ι = excisionComparison B C x₀ : F_B → F` (`F_B = homotopyFibre (interInclLeft B C) x₀` and
`F = homotopyFibre (setIncl C) …`).

This file provides the ingredients: the comparison map is injective and has a continuous section
`rangeSection` on its range (both are the "same data" maps, using
`Work.RatHurewicz.Triad.mem_range_excisionComparison_iff`), the corestriction
`rangeFactorization : F_B → range ι` is a homeomorphism (its inverse is `rangeSection`), and hence
`πmap rangeFactorization` is bijective.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB
open Work.RatHurewicz.Triad

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)}

/-- The range of the comparison map, as a type. -/
abbrev ERange (B C : Set X) (x₀ : ↥(B ∩ C)) : Type := ↥(Set.range (excisionComparison B C x₀))

theorem rangeCM_mem (B C : Set X) (x₀ : ↥(B ∩ C)) (q : ERange B C x₀ × I) :
    Fpath q.1.1 q.2 ∈ B :=
  (mem_range_excisionComparison_iff q.1.1).mp q.1.2 q.2

/-- The evaluation of the path of a point of the range, as a continuous map into `↥B`. -/
def rangeCM (B C : Set X) (x₀ : ↥(B ∩ C)) : C(ERange B C x₀ × I, ↥B) where
  toFun q := ⟨Fpath q.1.1 q.2, rangeCM_mem B C x₀ q⟩
  continuous_toFun := by
    have h1 : Continuous fun q : ERange B C x₀ × I => (FpathCMap X C (x₀ : X)) q.1.1 :=
      (FpathCMap X C (x₀ : X)).continuous.comp
        ((continuous_subtype_val : Continuous (Subtype.val : ERange B C x₀ → Ffibre X C (x₀ : X))).comp
          continuous_fst)
    exact Continuous.subtype_mk
      (f := fun q : ERange B C x₀ × I => Fpath q.1.1 q.2)
      (continuous_eval.comp (h1.prodMk continuous_snd)) (rangeCM_mem B C x₀)

@[simp] theorem rangeCM_coe (p : ERange B C x₀) (t : I) :
    ((rangeCM B C x₀ (p, t) : ↥B) : X) = Fpath p.1 t := rfl

theorem rangeSectionFst_mem (B C : Set X) (x₀ : ↥(B ∩ C)) (p : ERange B C x₀) :
    Fpath p.1 1 ∈ B ∩ C :=
  ⟨(mem_range_excisionComparison_iff p.1).mp p.2 1, (Fpath_one p.1).symm ▸ Fendpoint_mem p.1⟩

/-- The first coordinate of the section: the endpoint of the path, as a point of `B ∩ C`. -/
def rangeSectionFst (B C : Set X) (x₀ : ↥(B ∩ C)) : C(ERange B C x₀, ↥(B ∩ C)) where
  toFun p := ⟨Fpath p.1 1, rangeSectionFst_mem B C x₀ p⟩
  continuous_toFun := by
    have hfst : Continuous fun p : ERange B C x₀ => (FpathCMap X C (x₀ : X)) p.1 1 :=
      (continuous_eval_const (1 : I)).comp
        ((FpathCMap X C (x₀ : X)).continuous.comp
          (continuous_subtype_val : Continuous (Subtype.val : ERange B C x₀ → Ffibre X C (x₀ : X))))
    exact Continuous.subtype_mk
      (f := fun p : ERange B C x₀ => Fpath p.1 1) hfst (rangeSectionFst_mem B C x₀)

@[simp] theorem rangeSectionFst_coe (p : ERange B C x₀) :
    ((rangeSectionFst B C x₀ p : ↥(B ∩ C)) : X) = Fpath p.1 1 := rfl

theorem rangeSectionPath_mem (B C : Set X) (x₀ : ↥(B ∩ C)) (p : ERange B C x₀) :
    (rangeCM B C x₀).curry p (0 : I) = interInclLeft B C x₀ := by
  refine Subtype.ext ?_
  show Fpath p.1 0 = (x₀ : X)
  exact Fpath_zero p.1

/-- The path coordinate of the section. -/
def rangeSectionPath (B C : Set X) (x₀ : ↥(B ∩ C)) :
    C(ERange B C x₀, PathSpace ↥B (interInclLeft B C x₀)) where
  toFun p := ⟨(rangeCM B C x₀).curry p, rangeSectionPath_mem B C x₀ p⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (f := fun p : ERange B C x₀ => (rangeCM B C x₀).curry p)
      (rangeCM B C x₀).curry.continuous (rangeSectionPath_mem B C x₀)

theorem rangeSection_mem (B C : Set X) (x₀ : ↥(B ∩ C)) (p : ERange B C x₀) :
    (evalOne ↥B (interInclLeft B C x₀)) (rangeSectionPath B C x₀ p)
      = interInclLeft B C (rangeSectionFst B C x₀ p) := by
  show ((rangeCM B C x₀) (p, (1 : I)) : ↥B) = interInclLeft B C (rangeSectionFst B C x₀ p)
  refine Subtype.ext ?_
  show Fpath p.1 1 = ((rangeSectionFst B C x₀ p : ↥(B ∩ C)) : X)
  rfl

/-- **The continuous section of the comparison map on its range.** -/
def rangeSection (B C : Set X) (x₀ : ↥(B ∩ C)) : C(ERange B C x₀, Fbase B C x₀) where
  toFun p := ⟨(rangeSectionFst B C x₀ p, rangeSectionPath B C x₀ p), rangeSection_mem B C x₀ p⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (f := fun p : ERange B C x₀ => (rangeSectionFst B C x₀ p, rangeSectionPath B C x₀ p))
      ?_ (rangeSection_mem B C x₀)
    exact (rangeSectionFst B C x₀).continuous.prodMk (rangeSectionPath B C x₀).continuous

/-- The section is a right inverse of the comparison map (as a map into its range). -/
theorem excisionComparison_rangeSection (p : ERange B C x₀) :
    excisionComparison B C x₀ (rangeSection B C x₀ p) = p.1 := by
  refine Ffibre_ext ?_ ?_
  · rw [fst_excisionComparison]
    show Fpath p.1 1 = (((p.1).1).1 : X)
    exact Fpath_one p.1
  · rw [Fpath_excisionComparison]
    ext t
    show (((rangeSectionPath B C x₀ p).1) t : X) = Fpath p.1 t
    rfl

/-! ## The corestriction to the range -/

/-- The comparison map, with codomain restricted to its range. -/
def rangeFactorization (B C : Set X) (x₀ : ↥(B ∩ C)) : C(Fbase B C x₀, ERange B C x₀) where
  toFun p := Set.rangeFactorization (excisionComparison B C x₀) p
  continuous_toFun := Continuous.subtype_mk (excisionComparison B C x₀).continuous _

@[simp] theorem rangeFactorization_apply (p : Fbase B C x₀) :
    (rangeFactorization B C x₀ p).1 = excisionComparison B C x₀ p := rfl

/-- Two elements of `F_B` with the same end point and the same path agree. -/
theorem Fbase_ext {r r' : Fbase B C x₀} (h1 : (r.1.1 : X) = (r'.1.1 : X))
    (h2 : r.1.2 = r'.1.2) : r = r' := by
  refine Subtype.ext ?_
  refine Prod.ext ?_ ?_
  · exact Subtype.ext h1
  · exact h2

/-- The section is a left inverse of the corestriction of the comparison map. -/
theorem rangeSection_rangeFactorization (p : Fbase B C x₀) :
    rangeSection B C x₀ (rangeFactorization B C x₀ p) = p := by
  refine Fbase_ext ?_ ?_
  · show Fpath (rangeFactorization B C x₀ p).1 1 = ((p.1.1 : ↥(B ∩ C)) : X)
    rw [rangeFactorization_apply, Fpath_one]
    rfl
  · show rangeSectionPath B C x₀ (rangeFactorization B C x₀ p) = p.1.2
    apply Subtype.ext
    show (rangeCM B C x₀).curry (rangeFactorization B C x₀ p) = p.1.2.1
    ext t
    show Fpath (rangeFactorization B C x₀ p).1 t = ((p.1.2.1 t : ↥B) : X)
    rw [rangeFactorization_apply, Fpath_excisionComparison p]
    rfl

/-- The comparison map is injective (it has a section on its range). -/
theorem excisionComparison_injective : Function.Injective (excisionComparison B C x₀) := by
  intro p q hpq
  have hp : rangeFactorization B C x₀ p = rangeFactorization B C x₀ q := Subtype.ext hpq
  have h1 := congrArg (rangeSection B C x₀) hp
  exact (rangeSection_rangeFactorization p).symm.trans
    (h1.trans (rangeSection_rangeFactorization q))

/-- Transport of the homotopy groups along an equality of base points is natural for `πmap`. -/
theorem πmap_homotopyGroupCast {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) {x x' : X} (h : x = x')
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    πmap f n x' (homotopyGroupCast h n a)
      = homotopyGroupCast (congrArg f h) n (πmap f n x a) := by
  cases h
  simp [homotopyGroupCast]

/-! ## Bijectivity of the corestriction on homotopy groups -/

/-- **The corestriction of the comparison map to its range is a homotopy equivalence**, hence
induces isomorphisms on all homotopy groups. -/
theorem bijective_πmap_rangeFactorization (k : ℕ) :
    Function.Bijective (πmap (rangeFactorization B C x₀) k
      (homotopyFibreBasepoint (interInclLeft B C) x₀)) := by
  set bp := homotopyFibreBasepoint (interInclLeft B C) x₀ with hbp
  have hsr : ∀ p : Fbase B C x₀, rangeSection B C x₀ (rangeFactorization B C x₀ p) = p :=
    rangeSection_rangeFactorization
  have hrs : ∀ p : ERange B C x₀,
      rangeFactorization B C x₀ (rangeSection B C x₀ p) = p :=
    fun p => Subtype.ext (excisionComparison_rangeSection p)
  have hscomp : (rangeSection B C x₀).comp (rangeFactorization B C x₀)
      = ContinuousMap.id (Fbase B C x₀) := ContinuousMap.ext hsr
  have hrcomp : (rangeFactorization B C x₀).comp (rangeSection B C x₀)
      = ContinuousMap.id (ERange B C x₀) := ContinuousMap.ext hrs
  have hsbp : rangeSection B C x₀ (rangeFactorization B C x₀ bp) = bp := hsr bp
  have hkey : ∀ w : HomotopyGroup (Fin (k + 1)) (Fbase B C x₀) bp,
      homotopyGroupCast hsbp k
        (πmap (rangeSection B C x₀) k (rangeFactorization B C x₀ bp)
          (πmap (rangeFactorization B C x₀) k bp w)) = w := by
    intro w
    have h1 := πmap_congr hscomp k bp w
    have hid : πmap (ContinuousMap.id (Fbase B C x₀)) k bp w = w := πmap_id_apply k bp w
    rw [hid] at h1
    rw [show congrArg (fun l : C(Fbase B C x₀, Fbase B C x₀) => l bp) hscomp = hsbp from
      Subsingleton.elim _ _] at h1
    have h2 := πmap_comp_apply (rangeFactorization B C x₀) (rangeSection B C x₀) k bp w
    rw [h2] at h1
    exact h1
  constructor
  · intro u v huv
    have hu := hkey u
    have hv := hkey v
    rw [huv] at hu
    exact hu.symm.trans hv
  · intro z
    have ha : πmap (rangeFactorization B C x₀) k bp
        (homotopyGroupCast hsbp k
          (πmap (rangeSection B C x₀) k (rangeFactorization B C x₀ bp) z))
        = homotopyGroupCast (congrArg (rangeFactorization B C x₀) hsbp) k
          (πmap (rangeFactorization B C x₀) k (rangeSection B C x₀ (rangeFactorization B C x₀ bp))
            (πmap (rangeSection B C x₀) k (rangeFactorization B C x₀ bp) z)) :=
      πmap_homotopyGroupCast (rangeFactorization B C x₀) k hsbp _
    have hb : homotopyGroupCast (congrArg (rangeFactorization B C x₀) hsbp) k
          (πmap (rangeFactorization B C x₀) k (rangeSection B C x₀ (rangeFactorization B C x₀ bp))
            (πmap (rangeSection B C x₀) k (rangeFactorization B C x₀ bp) z)) = z := by
      have hcp := πmap_comp_apply (rangeSection B C x₀) (rangeFactorization B C x₀) k
        (rangeFactorization B C x₀ bp) z
      rw [← hcp]
      have hb' := πmap_congr hrcomp k (rangeFactorization B C x₀ bp) z
      have hid : πmap (ContinuousMap.id (ERange B C x₀)) k
          (rangeFactorization B C x₀ bp) z = z :=
        πmap_id_apply k (rangeFactorization B C x₀ bp) z
      rw [hid] at hb'
      rw [show congrArg (rangeFactorization B C x₀) hsbp
          = congrArg (fun l : C(ERange B C x₀, ERange B C x₀) =>
              l (rangeFactorization B C x₀ bp)) hrcomp from Subsingleton.elim _ _]
      exact hb'
    refine ⟨homotopyGroupCast hsbp k
      (πmap (rangeSection B C x₀) k (rangeFactorization B C x₀ bp) z), ?_⟩
    exact ha.trans hb

end

end Work.RatHurewicz
