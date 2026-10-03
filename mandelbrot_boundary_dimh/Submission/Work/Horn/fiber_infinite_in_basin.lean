import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.pushdown_basin_surj

/-!
# `Work.Horn.fiber_infinite_in_basin` — the fibres of the horn map inside its basin

`Work.Horn.inf_u` (Prop. 5.3's "infinite degree") transported through `pushdown`: every fibre of
`g = pushdown d.E` over a nonzero point of its parabolic basin is infinite.  This is the input that
makes `MandelDim.IsImmediateBasin (pushdown d.E) D_g B` unattainable (its properness clause would
force those fibres to be compact, hence finite).  See `NOTES_SESSION12.md`.
-/

namespace Work.Horn

open Filter Topology
open scoped Topology

noncomputable section

/-! ## The fibre obstruction: the second conjunct's `IsImmediateBasin` is unattainable

`Work.Horn.inf_u` (Prop. 5.3's "infinite degree") says that every fibre of the lifted horn map
`E` inside `BuOf d B` has infinite `π`-image.  Transported through `pushdown`, this makes every
fibre of `g = pushdown d.E` inside the *basin* infinite, in the strong sense that the whole fibre
inside the domain `D_g` sits in the basin (`Work.Horn.basin_basic_Dg` gives backward invariance).
Since `MandelDim.IsImmediateBasin` demands that `B ∩ g ⁻¹' L` be compact for compact `L ⊆ B`, and a
fibre of a non-constant holomorphic function is discrete, an infinite fibre can never be compact.
-/

/-- **The fibre of a nonzero basin point of `g = pushdown d.E` is infinite.**  This is the
transported form of `Work.Horn.inf_u` (Prop. 5.3's infinite degree). -/
theorem pushdown_fiber_infinite_in_basin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {w : ℂ} (hw0 : w ≠ 0)
    (hw : w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :
    ((MandelDim.pushdown d.E) ⁻¹' {w} ∩ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))).Infinite := by
  classical
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨-, -, hBuT, -, hupO, -, hsubO⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
  have hBu_eq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hupO
  obtain ⟨-, -, hback⟩ := basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo
  set y : ℂ := Complex.log w / (2 * Real.pi * Complex.I) with hy
  have hyw : MandelDim.piExp y = w := MandelDim.piExp_log_div w hw0
  have hinf := inf_u f₀ D₀ B c d hsetup y
  refine Set.Infinite.mono ?_ hinf
  rintro ζ ⟨w', hw', rfl⟩
  obtain ⟨hwu, hwE⟩ := hw'
  have hzDg : MandelDim.piExp w' ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
    Or.inr ⟨w', Or.inl (by rw [hBu_eq]; exact hwu), rfl⟩
  have hgz : MandelDim.pushdown d.E (MandelDim.piExp w') = w := by
    rw [pushdown_piExp_on_Bu d hBuT (fun u hu => hsubO (Or.inl hu)) hwu, hwE, hyw]
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hgz
  · exact hback (MandelDim.piExp w') hzDg (by rw [hgz]; exact hw)

end

end Work.Horn
