import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.Top.rayPt_injOn
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELAssembly.pot_iterate
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

/-- `Work.EL.F c = (Tantibar c)^[10]`, the tenth iterate of the mandelbar map. -/
lemma F_eq_tantibar_ten (c : ℂ) : Work.EL.F c = (Tantibar c)^[10] := by
  rw [show Work.EL.F c = Work.ELNest.F c from rfl, Work.ELNest.F_eq_tantibar]

/-- `F c` maps the filled Julia set into itself. -/
lemma F_mem_K {c : ℂ} {x : ℂ} (hx : x ∈ Work.EL.K c) : Work.EL.F c x ∈ Work.EL.K c := by
  rw [F_eq_tantibar_ten]
  exact Work.ParamRays.BoundedOrbit.shift hx 10

/-- **`F c` on a ray point**: it carries `rayPt θ t` to `rayPt (T^[10] θ) (t ^ 1024)`. -/
lemma F_rayPt {c : ℂ} (d : Work.EL.RootParabolic c) {θ t : ℝ} (ht : 1 < t) :
    Work.EL.F c (Work.EL.rayPt d.hN θ t)
      = Work.EL.rayPt d.hN ((Work.EL.T)^[10] θ) (t ^ (1024 : ℕ)) := by
  rw [F_eq_tantibar_ten, Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht 10]
  norm_num

/-- `T^[10] θ = fract (1024 θ)` lies in `[0, 1)`. -/
lemma T10_mem_Ico (θ : ℝ) : (Work.EL.T)^[10] θ ∈ Set.Ico (0 : ℝ) 1 := by
  rw [Work.ELNest.T_iterate_ten]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The potential is multiplied by `1024` under `F c`. -/
lemma pot_F_eq {c : ℂ} (d : Work.EL.RootParabolic c) (z : ℂ) :
    Work.EL.pot d.hN (Work.EL.F c z) = 1024 * Work.EL.pot d.hN z := by
  have h := Work.ELAssembly.pot_iterate d 10 z
  rw [F_eq_tantibar_ten]
  simp only [h]
  norm_num

/-- The ray point of the reference angle `midNear ps` is the ray point of its fractional part:
the rays are `1`-periodic in the angle. -/
lemma rayPt_midNear_fract {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (t : ℝ) :
    Work.EL.rayPt hN (Work.EL.midNear ps) t
      = Work.EL.rayPt hN (Int.fract (Work.EL.midNear ps)) t := by
  have hsplit : Work.EL.midNear ps
      = Int.fract (Work.EL.midNear ps) + (⌊Work.EL.midNear ps⌋ : ℝ) := by
    have h := Int.fract_add_floor (Work.EL.midNear ps); linarith
  conv_lhs => rw [hsplit]
  exact Work.ELTop.rayPt_add_int hN (Int.fract (Work.EL.midNear ps)) t ⌊Work.EL.midNear ps⌋

/-- **The fibre of `F c` over the reference point `v₀` meets the level-`(n+1)` region in at most
one point.**  `v₀ = rayPt (midNear [P0, N.Qp n]) (Real.sqrt (Qlev L n))` is the reference ray point
of the level-`n` region `V = polyRegion [P0, N.Qp n] (Qlev L n)` (`Work.ELTop.seed_mem_polyRegion`),
and the statement is that `(U ∩ (F c) ⁻¹' {v₀}).Subsingleton` for
`U = polyRegion [P0, N.Qp (n+1)] (Qlev L (n+1))`.

Reason: `v₀ ∉ K c`, so every `x ∈ U` with `F c x = v₀` lies off `K c`, and then the region
description `Work.ELTop.mem_polyRegion_iff_of_notMem_K` gives that the external angle `αₓ` of `x`
avoids all closed far arcs of `[P0, N.Qp (n+1)]`, while `T^[10] αₓ ≡ midNear [P0, N.Qp n]`
(because `F` multiplies angles by `1024` on the escaping set, and the external angle of `v₀` is
`midNear [P0, N.Qp n]`).  Two such angles `αₓ`, `α_y` therefore satisfy the hypothesis of the
one-fibre condition `I.one` (`∃ k, T^[10] α = midNear [P0, N.Qp n] + k`), which yields
`∃ k, αₓ = α_y + k`; and the common level `exp (pot x) = exp (pot y)` is forced by
`(exp (pot x))^1024 = (exp (pot y))^1024 = Real.sqrt (Qlev L n)` (all levels are `> 1`).  Hence
`x = y`. -/
theorem pullQ_fib {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ) :
    (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)) ∩
      (Work.EL.F c) ⁻¹' (singleton (Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n])
        (Real.sqrt (Work.ELNest.Qlev L n))))).Subsingleton := by
  have hR : 1 < Work.ELNest.Qlev L n := (Work.ELNest.Qlev_facts I.hL n).1
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts I.hL (n + 1)).1
  have hC' : Work.Top.IsJordanCurve
      (Work.EL.polyCurve [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm (n + 1)) hR'
  intro x hx y hy
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  obtain ⟨hxU, hxF⟩ := hx
  obtain ⟨hyU, hyF⟩ := hy
  have hvK : Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n])
      (Real.sqrt (Work.ELNest.Qlev L n)) ∉ Work.EL.K c :=
    Work.EL.rayPt_notMem_K d.hN (Work.ELTop.one_lt_sqrt hR)
  have hxK : x ∉ Work.EL.K c := fun h => hvK (hxF ▸ F_mem_K h)
  have hyK : y ∉ Work.EL.K c := fun h => hvK (hyF ▸ F_mem_K h)
  obtain ⟨harcx, -⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN
    Work.TopJordan.jordanForm [P0, N.Qp (n + 1)] (hadm (n + 1)) hR' hC' hxK).mp hxU
  obtain ⟨harcy, -⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN
    Work.TopJordan.jordanForm [P0, N.Qp (n + 1)] (hadm (n + 1)) hR' hC' hyK).mp hyU
  -- the angle of a preimage of `v₀` is carried by `T^[10]` to `midNear`, modulo `1`
  have key : ∀ {w : ℂ}, w ∉ Work.EL.K c →
      Work.EL.F c w = Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n])
        (Real.sqrt (Work.ELNest.Qlev L n)) →
      ∃ k : ℤ, (Work.EL.T)^[10] (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w)
        = Work.EL.midNear [P0, N.Qp n] + k := by
    intro w hwK hwF
    have ht : 1 < Real.exp (Work.EL.pot d.hN w) := Work.ELTop.one_lt_exp_pot d.hN hwK
    have harg : Work.EL.rayPt d.hN
        (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w)
        (Real.exp (Work.EL.pot d.hN w)) = w := Work.ELTop.rayPt_extAngle_exp_pot d.hN hwK
    have h1 : Work.EL.rayPt d.hN
          ((Work.EL.T)^[10] (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w))
          ((Real.exp (Work.EL.pot d.hN w)) ^ (1024 : ℕ))
        = Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n])
            (Real.sqrt (Work.ELNest.Qlev L n)) := by
      rw [← F_rayPt d ht, harg]
      exact hwF
    rw [rayPt_midNear_fract d.hN [P0, N.Qp n]] at h1
    obtain ⟨hang, -⟩ := Work.Top.rayPt_injOn d.hN (T10_mem_Ico _).1 (T10_mem_Ico _).2
      (Int.fract_nonneg _) (Int.fract_lt_one _)
      (one_lt_pow₀ ht (by norm_num)) (Work.ELTop.one_lt_sqrt hR) h1
    refine ⟨-⌊Work.EL.midNear [P0, N.Qp n]⌋, ?_⟩
    rw [hang]
    have h2 := Int.fract_add_floor (Work.EL.midNear [P0, N.Qp n])
    push_cast
    linarith
  obtain ⟨kx, hθx⟩ := key hxK hxF
  obtain ⟨ky, hθy⟩ := key hyK hyF
  -- the one-fibre condition `I.one`
  obtain ⟨k, hk⟩ := I.one n
    (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) x)
    (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y)
    (fun P hP => harcx P hP) (fun P hP => harcy P hP) ⟨kx, hθx⟩ ⟨ky, hθy⟩
  -- the potentials agree because `F c x = F c y = v₀`
  have hpot : Work.EL.pot d.hN x = Work.EL.pot d.hN y := by
    have h1 : Work.EL.pot d.hN (Work.EL.F c x) = Work.EL.pot d.hN (Work.EL.F c y) := by
      rw [hxF, hyF]
    rw [pot_F_eq, pot_F_eq] at h1
    linarith
  have hptx : x = Work.EL.rayPt d.hN
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) x) (Real.exp (Work.EL.pot d.hN x)) :=
    (Work.ELTop.rayPt_extAngle_exp_pot d.hN hxK).symm
  have hpty : y = Work.EL.rayPt d.hN
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y) (Real.exp (Work.EL.pot d.hN y)) :=
    (Work.ELTop.rayPt_extAngle_exp_pot d.hN hyK).symm
  rw [hptx, hpty, hk, hpot]
  exact Work.ELTop.rayPt_add_int d.hN
    (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y) (Real.exp (Work.EL.pot d.hN y)) k

end

end Work.ELAssembly
