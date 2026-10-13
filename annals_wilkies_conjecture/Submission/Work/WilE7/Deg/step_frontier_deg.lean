import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.FiberCutCover
import Submission.Work.WilE7.Deg.Bounds

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.Deg

/-- **The frontier step, with degree bookkeeping.**

Given a `Good` stratum `S` of format `≤ A` and degree `≤ qd.eval D`, the `E6`-frontier
`fiberClosure S.X.set \ S.X.set` (`hE6A`) is `E5`-stratified (`hE5B`, at the format bound `A6`);
the non-empty members of that stratification form the list `Fs` of frontier children.  Each child
is `Good`, has format `≤ A5b`, degree at most `(q5b.comp (q6.comp qd)).eval D`, and fibre
codimension strictly larger than that of `S` (`FrontierDrop`); the projections of the children
cover the part of `π(S.X.set)` lying over the frontier and stay inside `π(fiberClosure S.X.set)`.

Nothing but the two frozen `E5`/`E6` interfaces and the dimension drop is used: this is the pure
bookkeeping of the frontier branch of the fibre-cutting recursion. -/
theorem step_frontier_deg
    {n m : ℕ} (hFD : Work.WilE7.FrontierDrop)
    {A A6 A5b D : ℕ} {q6 q5b qd : Polynomial ℕ}
    (hE6A : ∀ (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ A →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (n + m),
        Y'.fmt ≤ A6 ∧ Y'.deg ≤ q6.eval X.deg ∧
        Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (hE5B : ∀ (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ A6 →
      ∃ L : List (WilkiesDesign.E.Stratum n m),
        L.length ≤ q5b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ A5b ∧ S.Good ∧ S.deg ≤ q5b.eval X.deg) ∧
        X.set = (⋃ S ∈ L, S.X.set))
    (S : WilkiesDesign.E.Stratum n m) (hSG : S.Good) (hSf : S.X.fmt ≤ A)
    (hSd : S.deg ≤ qd.eval D) :
    ∃ Fs : List (WilkiesDesign.E.Stratum n m),
      (∀ S' ∈ Fs, S'.Good) ∧ (∀ S' ∈ Fs, S'.X.fmt ≤ A5b) ∧
      (∀ S' ∈ Fs, S'.deg ≤ (q5b.comp (q6.comp qd)).eval D) ∧
      Fs.length ≤ (q5b.comp (q6.comp qd)).eval D ∧
      (∀ S' ∈ Fs, S'.X.set.Nonempty) ∧
      (∀ S' ∈ Fs, S'.X.set ⊆ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set) ∧
      (∀ S' ∈ Fs, S.j < S'.j) ∧
      (WilkiesDesign.E.projFirst n m '' S.X.set ∩
          WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set)
        ⊆ ⋃ S' ∈ Fs, WilkiesDesign.E.projFirst n m '' S'.X.set) ∧
      ((⋃ S' ∈ Fs, WilkiesDesign.E.projFirst n m '' S'.X.set) ⊆
        WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set)) := by
  classical
  -- the `E6`-frontier of `S.X`, together with its degree bound
  obtain ⟨Y, Y', hY'fmt, hY'deg, hYset, hY'set⟩ := hE6A S.X hSf
  -- the `E5`-stratification of the frontier
  obtain ⟨L, hLlen, hLprops, hLset⟩ := hE5B Y' hY'fmt
  -- degree transfer: `S.deg ≤ qd.eval D` bounds the degree of the stratum's own semi-Pfaffian set
  have hSXdeg : S.X.deg ≤ qd.eval D := by
    have := hSd; unfold WilkiesDesign.E.Stratum.deg at this; omega
  have hY'degD : Y'.deg ≤ (q6.comp qd).eval D := by
    calc Y'.deg ≤ q6.eval S.X.deg := hY'deg
      _ ≤ q6.eval (qd.eval D) := eval_mono_eval (q := q6) hSXdeg
      _ = (q6.comp qd).eval D := (eval_comp_eval q6 qd D).symm
  -- monotonicity of `q5b.eval`, applied to the degree of the frontier
  have hle5 : ∀ {d : ℕ}, d ≤ (q6.comp qd).eval D →
      q5b.eval d ≤ (q5b.comp (q6.comp qd)).eval D := by
    intro d hd
    rw [eval_comp_eval q5b (q6.comp qd) D]
    exact eval_mono_eval (q := q5b) hd
  -- the frontier children: the non-empty members of the stratification
  let Fs : List (WilkiesDesign.E.Stratum n m) := L.filter (fun S' => S'.X.set.Nonempty)
  have mem_Fs : ∀ S' : WilkiesDesign.E.Stratum n m,
      S' ∈ Fs ↔ S' ∈ L ∧ S'.X.set.Nonempty := by
    intro S'
    show S' ∈ L.filter _ ↔ _
    rw [List.mem_filter]
    exact ⟨fun h => ⟨h.1, of_decide_eq_true h.2⟩, fun h => ⟨h.1, decide_eq_true h.2⟩⟩
  have hsub6 : ∀ S' ∈ Fs, S'.X.set ⊆ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set := by
    intro S' hS'
    have hSL : S' ∈ L := ((mem_Fs S').mp hS').1
    have h1 : S'.X.set ⊆ Y'.set := by
      rw [hLset]
      intro z hz
      exact Set.mem_iUnion.mpr ⟨S', Set.mem_iUnion.mpr ⟨hSL, hz⟩⟩
    rw [hY'set] at h1
    exact h1
  refine ⟨Fs, ?_, ?_, ?_, ?_, ?_, hsub6, ?_, ?_, ?_⟩
  · -- every child is `Good`
    intro S' hS'
    exact (hLprops S' ((mem_Fs S').mp hS').1).2.1
  · -- formats
    intro S' hS'
    exact (hLprops S' ((mem_Fs S').mp hS').1).1
  · -- degrees
    intro S' hS'
    exact le_trans (hLprops S' ((mem_Fs S').mp hS').1).2.2 (hle5 hY'degD)
  · -- the number of children
    calc Fs.length ≤ L.length := List.length_filter_le _ _
      _ ≤ q5b.eval Y'.deg := hLlen
      _ ≤ (q5b.comp (q6.comp qd)).eval D := hle5 hY'degD
  · -- non-emptiness
    intro S' hS'
    exact ((mem_Fs S').mp hS').2
  · -- the dimension drop
    intro S' hS'
    exact hFD n m S S' hSG ((hLprops S' ((mem_Fs S').mp hS').1).2.1) (hsub6 S' hS')
      ((mem_Fs S').mp hS').2
  · -- coverage of `π(S.X.set) ∩ π(fiberClosure S.X.set \ S.X.set)`
    intro x hx
    have hxu : x ∈ WilkiesDesign.E.projFirst n m ''
        (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set) := hx.2
    have hEq : WilkiesDesign.E.fiberClosure S.X.set \ S.X.set = (⋃ S' ∈ L, S'.X.set) := by
      rw [← hY'set, hLset]
    rw [hEq] at hxu
    simp only [Set.mem_image, Set.mem_iUnion] at hxu
    obtain ⟨z, ⟨S', hS'L, hzS'⟩, hxz⟩ := hxu
    refine Set.mem_iUnion.mpr ⟨S', Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact (mem_Fs S').mpr ⟨hS'L, ⟨z, hzS'⟩⟩
    · exact ⟨z, hzS', hxz⟩
  · -- no growth
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨S', hS'Fs, hxS'⟩ := hx
    rw [Set.mem_image] at hxS'
    obtain ⟨z, hzS', hxz⟩ := hxS'
    exact ⟨z, (hsub6 S' hS'Fs hzS').1, hxz⟩

end Work.WilE7.Deg
