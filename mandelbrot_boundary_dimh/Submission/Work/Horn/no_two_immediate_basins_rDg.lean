import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Horn.no_two_immediate_basins_rDg`

The last, purely logical step of the `q = 1` argument in Shishikura's Lemma 5.4: **two disjoint
immediate parabolic basins cannot both contain a critical point when all critical points of the
map (inside its domain `Dg`) have the same image `w`**.

The mathematics is one line: an immediate basin `B` of `g` satisfies `g '' B ⊆ B`
(`IsImmediateBasin`), so the image `g z = w` of any critical point `z ∈ B` is again in `B`; the two
basins being disjoint, they cannot share `w`.

The only non-trivial point is that the hypothesis `hval` is stated for `z ∈ Dg`, so we need
`B ⊆ Dg`.  This follows from `B ⊆ ParabolicBasin g Dg` together with the *zeroth* iterate:
a basin point `z` has a neighbourhood `U ∈ 𝓝 z` with `g^[0] '' U ⊆ Dg`, i.e. `U ⊆ Dg`, and then
`z ∈ U`.
-/

namespace Work.Horn

open MandelDim Set

noncomputable section

/-- An immediate basin is contained in the domain of definition of the map: a basin point `z` has a
neighbourhood on which the zeroth iterate (the identity) stays inside `Dg`. -/
theorem subset_domain_of_immediateBasin {f : ℂ → ℂ} {D B : Set ℂ}
    (hB : MandelDim.IsImmediateBasin f D B) : B ⊆ D := by
  intro z hz
  obtain ⟨U, hU, hiter, _⟩ := hB.2.2.1 hz
  exact hiter 0 (mem_of_mem_nhds hU)

/-- **Two disjoint immediate basins with a common critical value are impossible.**  Every immediate
basin is forward invariant, so the value `w` of a critical point of `B i` lies in `B i`; two
disjoint basins would then both contain `w`. -/
theorem no_two_immediate_basins_rDg {g : ℂ → ℂ} {Dg : Set ℂ} {q : ℕ} {w : ℂ}
    (B : Fin q → Set ℂ) (h2 : 2 ≤ q)
    (hB : ∀ i, MandelDim.IsImmediateBasin g Dg (B i))
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j))
    (hcv : ∀ i, ∃ z ∈ B i, deriv g z = 0)
    (hval : ∀ z ∈ Dg, deriv g z = 0 → g z = w) :
    False := by
  set i0 : Fin q := ⟨0, by omega⟩ with hi0
  set i1 : Fin q := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by
    intro h
    have hval' : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp [hi0, hi1] at hval'
  obtain ⟨z, hz, hdz⟩ := hcv i0
  obtain ⟨z', hz', hdz'⟩ := hcv i1
  have hsub0 : B i0 ⊆ Dg := subset_domain_of_immediateBasin (hB i0)
  have hsub1 : B i1 ⊆ Dg := subset_domain_of_immediateBasin (hB i1)
  have hm0 : MapsTo g (B i0) (B i0) := (hB i0).2.2.2.2.1
  have hm1 : MapsTo g (B i1) (B i1) := (hB i1).2.2.2.2.1
  have h1 : w ∈ B i0 := by rw [← hval z (hsub0 hz) hdz]; exact hm0 hz
  have h1' : w ∈ B i1 := by rw [← hval z' (hsub1 hz') hdz']; exact hm1 hz'
  exact (hdisj i0 i1 h01).le_bot ⟨h1, h1'⟩

end

end Work.Horn
