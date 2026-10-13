import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.aeHtermOpen
import Submission.Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.aeI1CwBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "IP" => Work.FTS.EllipticEst.AngSecond.IP

/-!
# `Prop/i1_bare_hh` — the `I₁` lower bound of Step 2, with the second-order mixed honesty

Target: `∃ C > 0, ∀ α u G, AeData α u G → HkMem α 0 (z ∂_z u) → HkMem α 0 (z ∂_z∂_θθ u) →
  -C α² (⟨U,U⟩ + √⟨U,U⟩√⟨B,B⟩) ≤ α² ⟨Q,B⟩` with `U = z ∂_z u`,
`B = ∂_θθ u`, `Q = z² ∂_zz u` and `⟨g,h⟩ = AngSecond.IP g h = ∫_z∫_θ g h w²σ`.

The three inputs are all *proved* in the workspace:

* `H2W.WeakAux.I1ZibpOpenAbs` — the radial integration by parts, whose hypothesis list is
  exactly `AeData` plus the two honesties `HkMem α 0 (z ∂_z u)`,
  `HkMem α 0 (z ∂_z∂_θθ u)`;
* `TT.aeHtermOpen` — the angular `θ`-integration by parts of the slices of `U`, with the
  *same* mixed honesty as hypothesis, giving
  `⟨U, z∂_z∂_θθu⟩ ≤ C₁⟨U,U⟩`;
* `remov.AeI1CSPiece` — the Cauchy–Schwarz bound for the drift term.

The only content of this file is the assembly, namely the arithmetic
`⟨Q,B⟩ ≥ -C₁⟨U,U⟩ - 2√⟨U,U⟩√⟨B,B⟩ ≥ -(C₁+2)(⟨U,U⟩ + √⟨U,U⟩√⟨B,B⟩)`.
-/

/-- The final arithmetic step: from `P ≥ -C·A - 2√A√B`, `A ≥ 0` and `0 < C` one has
`-(C+2)·α²·(A + √A√B) ≤ α²·P`, because `2A + C√A√B ≥ 0`. -/
private theorem arith_ibh (C α A B P : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hP : - C * A - 2 * (Real.sqrt A * Real.sqrt B) ≤ P) :
    - (C + 2) * α ^ 2 * (A + Real.sqrt A * Real.sqrt B) ≤ α ^ 2 * P := by
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hmul : 0 ≤ Real.sqrt A * Real.sqrt B := mul_nonneg hsA hsB
  have hkey : - (C + 2) * (A + Real.sqrt A * Real.sqrt B) ≤ P := by
    nlinarith [hC, hA, hmul, hP]
  calc - (C + 2) * α ^ 2 * (A + Real.sqrt A * Real.sqrt B)
      = α ^ 2 * (- (C + 2) * (A + Real.sqrt A * Real.sqrt B)) := by ring
    _ ≤ α ^ 2 * P := mul_le_mul_of_nonneg_left hkey (sq_nonneg α)

theorem i1_bare_hh : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
      - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
                (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.EllipticEst.TT.aeHtermOpen
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro α u G hA hU hH
  -- ## (Z) the radial integration by parts
  have hZ₀ := Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs α u
    (Work.FTS.EllipticEst.H2W.Ae.AeData.hα hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.hα4 hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA) hU
    (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hH
  have hZ : IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        (Work.Spaces.pthIter 2 u)
      = - IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
        - IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ) := by
    have h1 : IP (Work.Spaces.Dz u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
        = IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) := rfl
    have h2 : IP (Work.Spaces.Dz u)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.Spaces.pthIter 2 u z θ)
        = IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ) :=
      Work.FTS.EllipticEst.AngSecond.IP_congr (fun _ _ => rfl) (fun z θ => by
        simp only [Work.FTS.EllipticEst.AngSecond.cw])
    rw [hZ₀, h1, h2]
  -- ## (M) the angular pairing bound `⟨U, z∂_z∂_θθu⟩ ≤ C₁⟨U,U⟩`
  have hHr := hC₁ α u G hA hU hH
  have hHr' : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
            Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => z * Work.Spaces.pz u z θ))
        + C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ) := hHr
  have hUH : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz u z θ) := by
    have hnn : (0 : ℝ) ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
        Work.Spaces.HkSq α 0
          (Work.Spaces.pth (fun z θ => z * Work.Spaces.pz u z θ)) :=
      mul_nonneg (div_nonneg (by linarith [Work.Spaces.eta_lt_one])
        (by linarith [Work.Spaces.eta_pos])) (Work.Spaces.HkSq_nonneg α 0 _)
    linarith [hHr', hnn]
  -- ## (CS) the Cauchy–Schwarz bound for the drift term
  --
  -- `AngAWeak.aeI1CwBound` is the `H2W.Ae.AeData`-class Cauchy–Schwarz of the drift term in the
  -- order `IP (cw·U) B`; here we need it in the order `IP U (cw·B)` produced by the radial
  -- integration by parts, so we swap the two slots of the pairing.
  have hcs₀ := Work.FTS.EllipticEst.AngAWeak.aeI1CwBound hA hU
  have hcs₁ : IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * (z * Work.Spaces.pz u z θ)) (Work.Spaces.pthIter 2 u)
      ≤ 2 * Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
          * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)) := hcs₀
  have hswap : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      = IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * (z * Work.Spaces.pz u z θ)) (Work.Spaces.pthIter 2 u) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [Work.FTS.EllipticEst.AngSecond.cw]
    ring
  have hcs' : - IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      ≥ - 2 * (Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
          * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u))) := by
    rw [hswap]
    linarith [hcs₁]
  -- ## the assembly
  have hP : - C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
          (fun z θ => z * Work.Spaces.pz u z θ)
        - 2 * (Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          (Work.Spaces.pthIter 2 u) := by
    rw [hZ]
    linarith [hUH, hcs']
  exact arith_ibh C₁ α
    (IP (fun z θ => z * Work.Spaces.pz u z θ) (fun z θ => z * Work.Spaces.pz u z θ))
    (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u))
    (IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u))
    hC₁pos
    (Work.FTS.EllipticEst.AngSecond.IP_self_nonneg (fun z θ => z * Work.Spaces.pz u z θ))
    hP

end

end Work.FTS.EllipticEst.Prop
