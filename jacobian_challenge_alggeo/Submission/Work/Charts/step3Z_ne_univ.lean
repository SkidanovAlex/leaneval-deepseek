import Mathlib
import Submission.Work.GCBasics.Basic
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.landsIn_Wp_of_linEquiv
import Submission.Work.Charts.exists_V_of_landsIn_Wp
import Submission.Work.Charts.addMor_landsIn_Wp_of_landsIn_omega
import Submission.Work.Charts.genericPoint_mem_V
import Submission.Work.Charts.RochData_exists_effective_deg
import Submission.Work.Charts.exists_lift_bcSch

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area CH — route B, step (S)1: `Z_x ≠ S_κ`

The first of the three inputs of step (S) of route B
(`Submission/Work/NOTES_LEAD_jacobian_charts3.md` §1, (S)1): for **every** point `x` of
`S = Sym^g C` (not only the closed ones) the closed set

  `Z_x := b_x⁻¹(W′)ᶜ ⊆ S_κ`  (`step3Z`, for `b_x := step3b x = add(x ∘ snd, fst)`)

is not all of `S_κ`, i.e. there is a point `u` of `S_κ` whose image `b_x u` lies in the open
`W′ = dom ρ ∩ ρ⁻¹(V)`.

The witness is exactly the one of the design, and it needs only the generic point of `S`
(no closedness of `x`, no finite residue field):

* pick `u₀ ∈ S_κ` over the generic point `η_S` of `S` (`bcFst` is surjective); its residue
  field `L = κ(u₀)` is an extension of `κ(x)` (through `bcSnd`) *and* of `κ(η_S)`;
* `y := u₀ ≫ fst` is an `L`-point of `S` over `η_S`, hence lands in the chart `V`
  (`genericPoint_mem_V`);
* Riemann–Roch (`RochData_exists_effective_deg`, i.e. RR7 with the degree preserved) applied
  to `divOf y − divOf (x_L) + g·P₀` — a divisor of degree `g` — produces an effective `E′`
  of degree `g` with `E′ ~ divOf y − divOf (x_L) + g·P₀`; by `divOf_complete`, `E′ = divOf e′`
  for some `e′ ∈ S(L)`;
* lifting `e′` and the point `q := u₀ ≫ snd` of `Spec κ(x)` to `u ∈ S_κ`
  (`exists_lift_bcSch`) we get `b_x u = add(x_L, e′)`, and
  `divOf (b_x u) − g·P₀ ~ divOf e′ + divOf (x_L) − g·P₀ ~ divOf y`, with `y ∈ V`;
* CRIT (`landsIn_Wp_of_linEquiv`) puts `b_x u ∈ W′`, so `u ∉ Z_x`.

The statement of `step3Z_ne_univ` is unconditional in `x`; the closing argument of the design
uses only `Z_x ≠ S_κ` (and, for `U_x ≠ ∅`, the discreteness of the fibres of the finite
`fst`, which is where closedness of `x` enters).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

/-- If `E` represents the class of `D - A`, then `A + E` represents the class of `D`. -/
private theorem linEquiv_add_of_sub {K : Type u} [Field K] {C : Curve K}
    [Work.SpecLin.DivBase C] {F : Type u} [Field F] [Algebra K F] {D A E : Dv C F}
    (h : LinEquiv C (D - A) E) : LinEquiv C D (A + E) := by
  have h1 := h.add A
  have h2 : D - A + A = D := by abel
  have h3 : E + A = A + E := by abel
  rwa [h2, h3] at h1

/-- **Step (S)1 of route B**, in the form in which the construction of `u₀` is separated
from the argument: given a field `L` with a point `q` of `Spec κ(x)` over `L` and a point `y`
of `S = Sym^g C` over `L` landing in the chart `V`, the set `Z_x = b_x⁻¹(W′)ᶜ` is not all of
`S_κ`. -/
private theorem step3Z_ne_univ_aux {K : Type u} [Field K] {C : Curve K}
    [Work.SpecLin.DivBase C] (R : RochData C) (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (G : Step3Geo R symGeom)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : BNDataAt R symGeom)
    (x : ((symGeom R.g).S).left)
    {P0Div : Dv C K} (hP0 : Ddeg C K P0Div = 1)
    (ha : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt ((symGeom (R.g + R.g)).S) F),
      (symGeom R.g).divOf (ptComp p a) = (R.g : ℤ) • pullK C P0Div)
    (L : Type u) [Field L] [Algebra K L]
    (q : FPt (specOf K (resField ((symGeom R.g).S) x)) L)
    (y : FPt ((symGeom R.g).S) L)
    (hyV : RPt.LandsIn y d.V) :
    step3Z R symGeom D G x a d ≠ Set.univ := by
  classical
  set A : Dv C L := (symGeom R.g).divOf (q ≫ resPt ((symGeom R.g).S) x) with hA
  set A' : Dv C L := A - (R.g : ℤ) • pullK C P0Div with hA'
  set D₀ : Dv C L := (symGeom R.g).divOf y - A' with hD₀
  have hAdeg : Ddeg C L A = (R.g : ℤ) := (symGeom R.g).divOf_deg _
  have hP0L : Ddeg C L (pullK C P0Div) = 1 := by
    rw [show pullK C P0Div
      = Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K L) P0Div from rfl,
      Work.Charts.Ddeg_bc, hP0]
  have hydeg : Ddeg C L ((symGeom R.g).divOf y) = (R.g : ℤ) := (symGeom R.g).divOf_deg y
  have hdeg₀ : Ddeg C L D₀ = (R.g : ℤ) := by
    rw [hD₀, hA', Ddeg_sub, Ddeg_sub, hydeg, hAdeg, Ddeg_smul, hP0L]
    ring
  obtain ⟨E', hE'eff, hE'deg, hE'lin⟩ :=
    RochData_exists_effective_deg R D₀ (by rw [hdeg₀])
  obtain ⟨e', he'⟩ := (symGeom R.g).divOf_complete E' hE'eff (hE'deg.trans hdeg₀)
  obtain ⟨p, hp_fst, hp_snd⟩ :=
    exists_lift_bcSch ((symGeom R.g).S) (resField ((symGeom R.g).S) x) L e' q
  have hdiv : (symGeom (R.g + R.g)).divOf (p ≫ step3b R symGeom D x)
      = A + (symGeom R.g).divOf e' := by
    rw [step3b, Work.Domain.Resid.addMor_divOf (addMap_divOf := D.addMap_divOf)]
    rw [show p ≫ (bcSnd ((symGeom R.g).S) (resField ((symGeom R.g).S) x)
          ≫ resPt ((symGeom R.g).S) x) = q ≫ resPt ((symGeom R.g).S) x from by
      rw [← Category.assoc, hp_snd]]
    rw [hp_fst, hA]
  have hlin : LinEquiv C ((symGeom R.g).divOf y)
      ((symGeom (R.g + R.g)).divOf (p ≫ step3b R symGeom D x)
        - (R.g : ℤ) • pullK C P0Div) := by
    rw [hdiv, he']
    rw [hD₀] at hE'lin
    have hkey : LinEquiv C ((symGeom R.g).divOf y) (A' + E') := linEquiv_add_of_sub hE'lin
    rw [hA'] at hkey
    convert hkey using 1 <;> abel
  have hcrit : RPt.LandsIn (p ≫ step3b R symGeom D x) (Wp R symGeom D G a d) :=
    landsIn_Wp_of_linEquiv R symGeom D G a ha d (p ≫ step3b R symGeom D x) y hyV hlin
  intro hZ
  have hz : p.left (IsLocalRing.closedPoint L) ∉ step3Z R symGeom D G x a d := by
    rw [mem_step3Z]
    intro hc
    exact hc (by
      rw [RPt.landsIn_iff, Over.comp_left, Scheme.Hom.comp_apply] at hcrit
      exact hcrit)
  exact hz (hZ ▸ Set.mem_univ _)

open CategoryTheory in
theorem step3Z_ne_univ {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C) (I : Work.Charts.Step3Data R)
    (x : ((I.symGeom R.g).S).left) :
    Work.Charts.step3Z R I.symGeom I.resid I.geo x I.a I.d ≠ Set.univ := by
  classical
  letI : Work.SpecLin.SymGeom C R.g := I.symGeom R.g
  let S : Sch K := (I.symGeom R.g).S
  haveI hInt_g : IsIntegral S.left := I.geo.integral_g
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : (bcSch S (resField S x)).left,
      (bcFst S (resField S x)).left u₀ = genericPoint S.left :=
    surjective_bcFst S (resField S x) (genericPoint S.left)
  let q : FPt (specOf K (resField S x)) (resField (bcSch S (resField S x)) u₀) :=
    resPt (bcSch S (resField S x)) u₀ ≫ bcSnd S (resField S x)
  let y : FPt S (resField (bcSch S (resField S x)) u₀) :=
    resPt (bcSch S (resField S x)) u₀ ≫ bcFst S (resField S x)
  have hyV : RPt.LandsIn y I.d.V := by
    rw [show y = resPt (bcSch S (resField S x)) u₀ ≫ bcFst S (resField S x) from rfl]
    rw [RPt.landsIn_preimage, Work.GCBasics.resPt_landsIn_iff, Scheme.Hom.mem_preimage, hu₀]
    exact genericPoint_mem_V I.d
  exact step3Z_ne_univ_aux R I.symGeom I.resid I.geo I.a I.d x I.hP0 I.ha
    (resField (bcSch S (resField S x)) u₀) q y hyV

end

end Work.Charts
