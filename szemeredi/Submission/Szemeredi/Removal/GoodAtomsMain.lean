import Mathlib
import Submission.Szemeredi.Removal.GoodAtoms
import Submission.Szemeredi.Removal.Pd
import Submission.Commons.Combinatorics.Hypergraph.lev_biUnion_powerset

/-!
# Good atoms for the full regularity lemma

Instantiates the abstract good-atom API (`Submission.Szemeredi.Removal.GoodAtoms`)
for the output of the corrected full regularity lemma (`RegOK2`).
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

theorem lev_eq_biUnion (Hd : Finset (Finset ι)) (n : ℕ) :
    lev Hd n = Hd.biUnion (fun e => e.powerset.filter (fun f => f.card + n = e.card)) :=
  Commons.Combinatorics.Hypergraph.lev_biUnion_powerset Hd n

theorem mem_lev_iff {Hd : Finset (Finset ι)} {n : ℕ} {f : Finset ι} :
    f ∈ lev Hd n ↔ ∃ e ∈ Hd, f ⊆ e ∧ f.card + n = e.card := by
  rw [lev_eq_biUnion]
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]

/-- A subset of an edge of a `d`-uniform hypergraph lies in the appropriate level. -/
theorem subset_mem_lev {Hd : Finset (Finset ι)} {d : ℕ} (hd : ∀ e ∈ Hd, e.card = d)
    {e f : Finset ι} (he : e ∈ Hd) (hf : f ⊆ e) : f ∈ lev Hd (d - f.card) := by
  rw [mem_lev_iff]
  refine ⟨e, he, hf, ?_⟩
  have h2 : f.card ≤ d := by
    have h3 := Finset.card_le_card hf
    rw [hd e he] at h3
    exact h3
  rw [hd e he]
  exact Nat.add_sub_cancel' h2

/-- The boundary of a face of level `j` lies in level `j - 1`. -/
theorem del_subset_lev {Hd : Finset (Finset ι)} {e : Finset ι} {j d : ℕ}
    (he : e ∈ lev Hd (d - j)) : del e ⊆ lev Hd (d - j + 1) := by
  have h : lev Hd (d - j + 1) = (lev Hd (d - j)).biUnion del := by
    have h1 : d - j + 1 = (d - j) + 1 := by omega
    rw [h1, lev_succ]
    rfl
  rw [h]
  exact Finset.subset_biUnion_of_mem del he

/-- A helper form of `del_subset_lev` with the level index `j - 1`. -/
theorem del_subset_lev' {Hd : Finset (Finset ι)} {e : Finset ι} {j d : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j ≤ d) (he : e ∈ lev Hd (d - j)) :
    del e ⊆ lev Hd (d - (j - 1)) := by
  have h2 : d - j + 1 = d - (j - 1) := by omega
  rw [← h2]
  exact del_subset_lev he

theorem sub_one_lt_of {j d : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ d) : j - 1 < d := by omega

/-- The boundary of a face consists of proper subsets. -/
theorem del_subset_proper {e f : Finset ι} (hf : f ∈ del e) : f ⊂ e := by
  rw [mem_del] at hf
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hf.1, ?_⟩
  intro hfe
  have hc := hf.2
  rw [hfe] at hc
  omega

/-- The σ-algebra attached to a face `f` (of level `f.card`). -/
noncomputable def algOf (d : ℕ) (Bd : Finset ι → SigAlg (Pt V))
    (B : ℕ → Finset ι → SigAlg (Pt V)) (f : Finset ι) : SigAlg (Pt V) :=
  edgeAlg (V := V) Bd B d f.card f

/-- An assignment of an atom of the level-`f.card` σ-algebra to every face. -/
def AtomSys (d : ℕ) (Hd : Finset (Finset ι)) (Bd : Finset ι → SigAlg (Pt V))
    (B : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V)) : Prop :=
  ∀ f, f ∈ Hd.biUnion (fun e => e.powerset) → A f ∈ (algOf (V := V) d Bd B f).atoms

theorem IsMeas_of_mem_atoms {P : SigAlg (Pt V)} {Ae : Finset (Pt V)}
    (h : Ae ∈ P.atoms) : P.IsMeas Ae := by
  obtain ⟨x, rfl⟩ := SigAlg.mem_atoms.mp h
  exact SigAlg.isMeas_block P x

/-- The boundary algebras of a face, indexed by the boundary. -/
abbrev bdryAlg (B : ℕ → Finset ι → SigAlg (Pt V)) (j : ℕ) (e : Finset ι) :
    {f : Finset ι // f ∈ del e} → SigAlg (Pt V) :=
  fun f => B (j - 1) f.val

/-- The lower-order algebras of a face, indexed by the proper subsets. -/
abbrev lowAlg (B : ℕ → Finset ι → SigAlg (Pt V)) (e : Finset ι) :
    {f : Finset ι // f ⊂ e} → SigAlg (Pt V) :=
  fun f => B f.val.card f.val

/-- The join over a subtype-indexed family is the join over the corresponding finset. -/
theorem iInf_image_eq {κ : Type*} (s : Finset κ) (R : κ → SigAlg (Pt V)) :
    SigAlg.iInf (fun f : {f : κ // f ∈ s} => R f.val) Finset.univ = SigAlg.iInf R s := by
  rw [show (Finset.univ : Finset {f : κ // f ∈ s}) = s.attach from Finset.attach_eq_univ.symm]
  exact SigAlg.ext (fun x => Finset.inf_attach s (fun i => (R i).block x))

/-- The bad set of an atom: a largeness-bad part together with a regularity-bad part. -/
noncomputable abbrev badSetOf (d : ℕ) (Bd : Finset ι → SigAlg (Pt V))
    (B B' : ℕ → Finset ι → SigAlg (Pt V)) (M : ℕ → ℕ) (F : ℕ → ℕ)
    (j : ℕ) (e : Finset ι) (Ae : Finset (Pt V)) : Finset (Pt V) :=
  LBadSet F M j Ae (bdryAlg (V := V) B j e)
    ∪ RBadSet F M j Ae (bdryAlg (V := V) B j e) (bdryAlg (V := V) B' j e)
        (lowAlg (V := V) B e)

/-- Tao's good-atom conditions at a single face. -/
def GoodAt (d : ℕ) (Bd : Finset ι → SigAlg (Pt V))
    (B B' : ℕ → Finset ι → SigAlg (Pt V)) (M : ℕ → ℕ) (F : ℕ → ℕ)
    (A : Finset ι → Finset (Pt V)) (j : ℕ) (e : Finset ι) : Prop :=
  LargeOk F M j (fun f : {f : Finset ι // f ∈ del e} => A f.val) (A e) ∧
  RegOk F M j (fun f : {f : Finset ι // f ⊂ e} => A f.val) (A e)
    (bdryAlg (V := V) B j e) (bdryAlg (V := V) B' j e)

/-- **Most atoms are good** (Tao, Lemma 3.2), instantiated for the output of the
corrected full regularity lemma.  The two inputs `href` (coarse refines fine) and
`hpy` (the energy gap) are exactly the two `RegOK2` conjuncts at level `j`; they
are passed explicitly so that this lemma (and hence the counting lemma built on
it) does not have to manipulate the a priori bound `MbddF` appearing in `RegOK2`. -/
theorem good_atom_bad_le {d : ℕ} {Bd : Finset ι → SigAlg (Pt V)}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {j : ℕ} {e : Finset ι} {Ae : Finset (Pt V)}
    (hF1 : 1 ≤ F (M j))
    (href : ∀ f : {f : Finset ι // f ∈ del e},
      (bdryAlg (V := V) B j e f).Refines (bdryAlg (V := V) B' j e f))
    (hpy : (SigAlg.iInf (bdryAlg (V := V) B' j e) Finset.univ).energy (SigAlg.indicator Ae)
      ≤ (SigAlg.iInf (bdryAlg (V := V) B j e) Finset.univ).energy (SigAlg.indicator Ae)
        + (1 / (F (M j))) ^ 2) :
    avg (fun x => SigAlg.indicator Ae x
        * SigAlg.indicator (badSetOf (V := V) d Bd B B' M F j e Ae) x)
      ≤ 1 / Real.log (F (M j)) + 1 / (F (M j)) := by
  classical
  have hL := avg_indicator_lBad_le F M j Ae (bdryAlg (V := V) B j e) hF1
  have hRr := avg_indicator_rBad_le F M j Ae (bdryAlg (V := V) B j e)
    (bdryAlg (V := V) B' j e) (lowAlg (V := V) B e) hF1 href hpy
  exact avg_indicator_bad_le F M j Ae (bdryAlg (V := V) B j e) (bdryAlg (V := V) B' j e)
    (lowAlg (V := V) B e) hF1 hL hRr

/-- The version of `good_atom_bad_le` with `href` and `hpy` derived from `RegOK2`. -/
theorem good_atom_bad_le_RegOK2 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ d) {e : Finset ι} (he : e ∈ lev Hd (d - j))
    {Ae : Finset (Pt V)} (hAe : Ae ∈ (edgeAlg (V := V) Bd B d j e).atoms)
    (hF1 : 1 ≤ F (M j)) :
    avg (fun x => SigAlg.indicator Ae x
        * SigAlg.indicator (badSetOf (V := V) d Bd B B' M F j e Ae) x)
      ≤ 1 / Real.log (F (M j)) + 1 / (F (M j)) := by
  classical
  obtain ⟨_hMd, _hMbdd, _hrec, _hBc, hBB', _hB'c, _hBcx, henerg, _hdisc⟩ := hR
  refine good_atom_bad_le (d := d) (Bd := Bd) (M := M) (e := e) (Ae := Ae) hF1 (fun f => ?_) ?_
  · exact hBB' (j - 1) (sub_one_lt_of hj1 hj2) f.val (del_subset_lev' hj1 hj2 he f.2)
  · have hJ1 := iInf_image_eq (V := V) (del e) (fun i : Finset ι => B' (j - 1) i)
    have hJ2 := iInf_image_eq (V := V) (del e) (fun i : Finset ι => B (j - 1) i)
    rw [hJ1, hJ2]
    exact henerg j hj1 hj2 e he Ae (IsMeas_of_mem_atoms hAe)

end Szemeredi.Removal
