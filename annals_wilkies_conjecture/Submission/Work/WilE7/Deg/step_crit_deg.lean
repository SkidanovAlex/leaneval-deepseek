import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.FiberCutCover
import Submission.Work.WilE7.Deg.Bounds
import Submission.Work.WilE7.critSet_deg_bound_Sdeg
import Submission.Work.WilE7.semiPf_normalize_exists

namespace Work.WilE7.Deg

open WilkiesDesign WilkiesDesign.E

/-! ## The critical step of the degree-tracking fibre-cut recursion

The children of a `Good` stratum `S` (with `S.j < m`) in the *critical* case come from the
`E5`-stratifications of the fibre-critical sets `critSet S l`, `l : Fin m`, restricted to the
strata that carry a `CritWitnessAt` point (so that `CritDrop` applies).  The only subtlety in the
degree bookkeeping is that the hypothesis `hCDeg` bounds the degree of `critSet S l` only for a
*normalised* stratum (`S.X.basics.length ≤ S.X.deg + 1`).  Since the set `critSet S l` does not
change when the `basics` list of `S.X` is normalised (`redBasics`), we may stratify the
`critSet` of the normalised copy of `S` instead: the sets are the same, hence coverage,
`CritWitnessAt` and `CritDrop` all still apply, while the degree bound is available. -/

/-- Normalising the `basics` list of a semi-Pfaffian set does not change its set. -/
theorem redBasics_set {k : ℕ} (X : SemiPf k) :
    (⟨X.r, X.c, redBasics X⟩ : SemiPf k).set = X.set := by
  ext z
  simp only [SemiPf.set, Set.mem_ofPred_eq]
  exact and_congr_right (fun _ => exists_holds_redBasics X z)

theorem step_crit_deg
    {n m : ℕ} (hCD : Work.WilE7.CritDrop) (hCW : Work.WilE7.CritWitness)
    {A A5 D Ab : ℕ} {q5 qc qd : Polynomial ℕ}
    (hE5A : ∀ (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ A →
      ∃ L : List (WilkiesDesign.E.Stratum n m),
        L.length ≤ q5.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ A5 ∧ S.Good ∧ S.deg ≤ q5.eval X.deg) ∧
        X.set = (⋃ S ∈ L, S.X.set))
    (hCDeg : ∀ (S : WilkiesDesign.E.Stratum n m), S.X.fmt ≤ A → S.j ≤ m →
      S.X.basics.length ≤ S.X.deg + 1 → ∀ l : Fin m,
      (Work.WilE7.critSet S l).deg ≤ qc.eval S.deg)
    (hm : m ≤ Ab)
    (S : WilkiesDesign.E.Stratum n m) (hSG : S.Good) (hSf : S.X.fmt ≤ A)
    (hSd : S.deg ≤ qd.eval D) (hSne : S.X.set.Nonempty) (hSlt : S.j < m) :
    ∃ Cs : List (WilkiesDesign.E.Stratum n m),
      (∀ S' ∈ Cs, S'.Good) ∧ (∀ S' ∈ Cs, S'.X.fmt ≤ A5) ∧
      (∀ S' ∈ Cs, S'.deg ≤ (q5.comp (qc.comp qd)).eval D) ∧
      Cs.length ≤ Ab * (q5.comp (qc.comp qd)).eval D ∧
      (∀ S' ∈ Cs, S'.X.set.Nonempty) ∧
      (∀ S' ∈ Cs, S'.X.set ⊆ S.X.set) ∧
      (∀ S' ∈ Cs, S.j < S'.j) ∧
      (WilkiesDesign.E.projFirst n m '' S.X.set \
          WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set)
        ⊆ ⋃ S' ∈ Cs, WilkiesDesign.E.projFirst n m '' S'.X.set) ∧
      ((⋃ S' ∈ Cs, WilkiesDesign.E.projFirst n m '' S'.X.set) ⊆
        WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set)) := by
  classical
  -- A normalised copy of `S`: same set, same format, degree no larger, `basics` normalised.
  let Xn : SemiPf (n + m) := ⟨S.X.r, S.X.c, redBasics S.X⟩
  let Sn : Stratum n m := ⟨Xn, S.j, S.h⟩
  have hXn_set : Xn.set = S.X.set := redBasics_set S.X
  have hSX : Sn.X.set = S.X.set := hXn_set
  have hSn_fmt : Sn.X.fmt ≤ A := hSf
  have hSn_jle : Sn.j ≤ m := good_j_le S hSG hSne
  have hSn_len : Sn.X.basics.length ≤ Sn.X.deg + 1 :=
    redBasics_length_le_deg_add_one S.X
  have hSn_deg_le : Sn.deg ≤ S.deg := by
    have h1 : Sn.X.deg ≤ S.X.deg := redBasics_deg_le S.X
    simp only [Stratum.deg]
    exact Nat.add_le_add h1 le_rfl
  -- The two `critSet`s have the same underlying set.
  have hcrit_eq : ∀ l : Fin m, (critSet Sn l).set = (critSet S l).set := by
    intro l
    rw [critSet_set, critSet_set, hSX]
  -- The degree bound of `hCDeg`, available for the normalised copy.
  have hcritdeg : ∀ l : Fin m, (critSet Sn l).deg ≤ qc.eval (qd.eval D) := by
    intro l
    calc (critSet Sn l).deg ≤ qc.eval Sn.deg := hCDeg Sn hSn_fmt hSn_jle hSn_len l
      _ ≤ qc.eval (qd.eval D) := eval_mono_eval (hSn_deg_le.trans hSd)
  -- The stratification of `critSet Sn l` by `E5`.
  have hcf : ∀ l : Fin m, (critSet Sn l).fmt ≤ A := by
    intro l
    rw [critSet_fmt]
    exact hSn_fmt
  let critL : Fin m → List (Stratum n m) := fun l => (hE5A (critSet Sn l) (hcf l)).choose
  have hcritL : ∀ l : Fin m,
      (∀ T ∈ critL l, T.X.fmt ≤ A5 ∧ T.Good ∧ T.deg ≤ q5.eval (critSet Sn l).deg) ∧
      (critSet Sn l).set = (⋃ T ∈ critL l, T.X.set) :=
    fun l => (hE5A (critSet Sn l) (hcf l)).choose_spec.2
  have hcritL_len : ∀ l : Fin m, (critL l).length ≤ q5.eval (critSet Sn l).deg :=
    fun l => (hE5A (critSet Sn l) (hcf l)).choose_spec.1
  -- The uniform bound.
  set Bound : ℕ := (q5.comp (qc.comp qd)).eval D with hBound
  have hevalbound : ∀ l : Fin m, q5.eval (critSet Sn l).deg ≤ Bound := by
    intro l
    rw [hBound]
    calc q5.eval (critSet Sn l).deg ≤ q5.eval (qc.eval (qd.eval D)) := eval_mono_eval (hcritdeg l)
      _ = (q5.comp (qc.comp qd)).eval D := by
            rw [← eval_comp_eval qc qd D]
            exact (eval_comp_eval q5 (qc.comp qd) D).symm
  have hchilddeg : ∀ l : Fin m, ∀ T ∈ critL l, T.deg ≤ Bound := by
    intro l T hT
    exact ((hcritL l).1 T hT).2.2.trans (hevalbound l)
  -- The children: for every `l`, the strata of `critL l` that are non-empty and carry the
  -- `CritWitnessAt` point (which is exactly what `CritDrop` needs).
  let Cs : List (Stratum n m) := (List.finRange m).flatMap
      (fun l => (critL l).filter (fun T => T.X.set.Nonempty ∧ CritWitnessAt S l T))
  have mem_Cs : ∀ T ∈ Cs, ∃ l : Fin m, T ∈ critL l ∧ T.X.set.Nonempty ∧ CritWitnessAt S l T := by
    intro T hT
    simp only [Cs, List.mem_flatMap] at hT
    obtain ⟨l, -, hTl⟩ := hT
    obtain ⟨hTl', hprop⟩ := List.mem_filter.mp hTl
    exact ⟨l, hTl', (of_decide_eq_true hprop).1, (of_decide_eq_true hprop).2⟩
  -- `T.X.set` is always contained in `(critSet Sn l).set`.
  have subset_crit : ∀ (l : Fin m) (T : Stratum n m), T ∈ critL l →
      T.X.set ⊆ (critSet Sn l).set := by
    intro l T hT
    rw [(hcritL l).2]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hz⟩⟩
  refine ⟨Cs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨l, hl, -⟩ := mem_Cs T hT
    exact ((hcritL l).1 T hl).2.1
  · intro T hT
    obtain ⟨l, hl, -⟩ := mem_Cs T hT
    exact ((hcritL l).1 T hl).1
  · intro T hT
    obtain ⟨l, hl, -⟩ := mem_Cs T hT
    exact hchilddeg l T hl
  · -- length
    have h1 : Cs.length ≤ (List.map (fun _ : Fin m => Bound) (List.finRange m)).sum := by
      simp only [Cs, List.length_flatMap]
      apply List.sum_le_sum
      intro l _
      exact (List.length_filter_le _ (critL l)).trans ((hcritL_len l).trans (hevalbound l))
    have h2 : (List.map (fun _ : Fin m => Bound) (List.finRange m)).sum = m * Bound := by
      simp
    rw [h2] at h1
    exact h1.trans (Nat.mul_le_mul_right Bound hm)
  · intro T hT
    obtain ⟨l, hl, hne, -⟩ := mem_Cs T hT
    exact hne
  · intro T hT
    obtain ⟨l, hl, -⟩ := mem_Cs T hT
    exact (subset_crit l T hl).trans ((critSet_subset Sn l).trans (le_of_eq hSX))
  · intro T hT
    obtain ⟨l, hl, -, hwit⟩ := mem_Cs T hT
    have hsubT : T.X.set ⊆ (critSet S l).set := by
      rw [← hcrit_eq l]
      exact subset_crit l T hl
    exact hCD n m S T hSG ((hcritL l).1 T hl).2.1 l hSlt hsubT hwit
  · -- coverage of the "closed fibre" part of `π(S.X.set)`
    intro x hx
    obtain ⟨hxS, hxf⟩ := hx
    obtain ⟨z0, hz0, hz0x⟩ := hxS
    have hne : (fiber S.X.set x).Nonempty := ⟨projSnd n m z0, by
      show Fin.append x (projSnd n m z0) ∈ S.X.set
      rw [← hz0x, append_projFirst_projSnd]
      exact hz0⟩
    obtain ⟨l, z, hzcrit, hzx, w, hw, hwcomp, hwne⟩ := hCW n m S hSG hSlt x hxf hne
    have hzmem : z ∈ (critSet Sn l).set := by
      rw [hcrit_eq l]; exact hzcrit
    rw [(hcritL l).2] at hzmem
    simp only [Set.mem_iUnion] at hzmem
    obtain ⟨T, hT, hzT⟩ := hzmem
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · refine List.mem_flatMap.mpr ⟨l, List.mem_finRange l, ?_⟩
      refine List.mem_filter.mpr ⟨hT, ?_⟩
      refine decide_eq_true ⟨⟨z, hzT⟩, ?_⟩
      refine ⟨z, hzT, w, ?_, ?_, hwne⟩
      · rw [hzx]; exact hw
      · rw [hzx]; exact hwcomp
    · exact ⟨z, hzT, hzx⟩
  · -- no growth
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨T, hT, hxT⟩ := hx
    obtain ⟨z, hz, hzx⟩ := hxT
    obtain ⟨l, hl, -⟩ := mem_Cs T hT
    have hTsub : T.X.set ⊆ S.X.set :=
      (subset_crit l T hl).trans ((critSet_subset Sn l).trans (le_of_eq hSX))
    exact ⟨z, subset_fiberClosure S.X.set (hTsub hz), hzx⟩

end Work.WilE7.Deg
