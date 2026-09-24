import Mathlib
import Submission.Work.SimplyConnected.ABS.windingHomFromLogCover

/-!
# The logarithmic étale space is evenly covered over every point

For `ℓ : Y → ℂ` continuous and nowhere vanishing, the logarithmic étale space

  `logSpace ℓ = {p : Y × ℂ // Complex.exp p.2 = ℓ p.1}`

projects to `Y` as a covering map: every `y : Y` is evenly covered, with fibre
`logProj ℓ ⁻¹' {y}`.

The proof is the statement that the pull-back of an evenly covered point is evenly covered
(`isEvenlyCovered_pullback`): the log space is the pull-back of the exponential covering
`exp : ℂ → ℂ*` along `ℓ' : Y → ℂ*`, `y ↦ ⟨ℓ y, hne y⟩`, and the fibre of the exponential
covering over `ℓ' y` is canonically homeomorphic to the fibre of `logProj ℓ` over `y`.
-/

open Topology

namespace Work.Analysis.RiemannSurface

/-- **Pull-back of an evenly covered point.**  If `b : X` is evenly covered by `f` with fibre `I`,
and `g` is continuous with `g y = b`, then `y` is evenly covered by the projection of the
pull-back `{q : Y × Z // f q.2 = g q.1}` with the same fibre `I` (the trivializations of `f` pull
back verbatim). -/
theorem isEvenlyCovered_pullback {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Z → X} {g : Y → X} {b : X} {I : Type*} [TopologicalSpace I]
    (hf : IsEvenlyCovered f b I) (hg : Continuous g) {y : Y} (hy : g y = b) :
    IsEvenlyCovered (fun q : {q : Y × Z // f q.2 = g q.1} => q.1.1) y I := by
  obtain ⟨hI, U, hbU, hU, -, H, hH⟩ := hf
  let PB : Type _ := {q : Y × Z // f q.2 = g q.1}
  let pj : PB → Y := fun q => q.1.1
  have hpj : Continuous pj := continuous_fst.comp continuous_subtype_val
  have hW : IsOpen (g ⁻¹' U) := hU.preimage hg
  let D : Type _ := ↥(pj ⁻¹' (g ⁻¹' U))
  -- membership bookkeeping
  have hmemW : ∀ q : D, g (pj q.1) ∈ U := fun q => q.2
  have hmemF : ∀ q : D, f (q.1.1.2) ∈ U := by
    intro q
    rw [(q.1).2]
    exact hmemW q
  -- the two components of the trivialization of the pull-back
  let p1 : D → ↥(g ⁻¹' U) := fun q => ⟨pj q.1, hmemW q⟩
  have hp1 : Continuous p1 :=
    Continuous.subtype_mk (hpj.comp continuous_subtype_val) hmemW
  let p2 : D → ↥(f ⁻¹' U) := fun q => ⟨q.1.1.2, hmemF q⟩
  have hval2 : Continuous fun q : D => q.1.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hp2 : Continuous p2 := Continuous.subtype_mk hval2 hmemF
  -- the components of the inverse
  let uu : ↥(g ⁻¹' U) × I → ↥U × I := fun v => (⟨g v.1.1, v.1.2⟩, v.2)
  have hmemV : ∀ v : ↥(g ⁻¹' U) × I, g v.1.1 ∈ U := fun v => v.1.2
  have hgv : Continuous fun v : ↥(g ⁻¹' U) × I => g v.1.1 :=
    hg.comp (continuous_subtype_val.comp continuous_fst)
  have huu : Continuous uu :=
    Continuous.prodMk (Continuous.subtype_mk hgv hmemV) continuous_snd
  let zz : ↥(g ⁻¹' U) × I → Z := fun v => (H.symm (uu v)).1
  have hzz : Continuous zz := continuous_subtype_val.comp (H.symm.continuous.comp huu)
  have hpc : ∀ v : ↥(g ⁻¹' U) × I, f (zz v) = g v.1.1 := by
    intro v
    have h := hH (H.symm (uu v))
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm
  let qq : ↥(g ⁻¹' U) × I → PB := fun v => ⟨(v.1.1, zz v), hpc v⟩
  have hqq : Continuous qq :=
    Continuous.subtype_mk (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) hzz)
      hpc
  let iv : ↥(g ⁻¹' U) × I → D := fun v => ⟨qq v, v.1.2⟩
  have hiv : Continuous iv := Continuous.subtype_mk hqq fun v => v.1.2
  let hHom : D ≃ₜ (g ⁻¹' U) × I :=
  { toFun := fun q => (p1 q, (H (p2 q)).2)
    invFun := iv
    left_inv := by
      intro q
      have hcomp : g (p1 q) = (((H (p2 q)).1 : ↥U) : X) := by
        rw [hH]
        exact ((q.1).2).symm
      have hu : uu (p1 q, (H (p2 q)).2) = H (p2 q) :=
        Prod.ext (Subtype.ext hcomp) rfl
      have hz : zz (p1 q, (H (p2 q)).2) = q.1.1.2 := by
        show (H.symm (uu (p1 q, (H (p2 q)).2))).1 = q.1.1.2
        rw [hu, Homeomorph.symm_apply_apply]
      exact Subtype.ext (Subtype.ext (Prod.ext rfl hz))
    right_inv := by
      intro v
      have hp2v : p2 (iv v) = H.symm (uu v) := Subtype.ext rfl
      have h1 : p1 (iv v) = v.1 := rfl
      have h2 : (H (p2 (iv v))).2 = v.2 := by
        rw [hp2v, Homeomorph.apply_symm_apply]
      exact Prod.ext h1 h2
    continuous_toFun := Continuous.prodMk hp1 (continuous_snd.comp (H.continuous.comp hp2))
    continuous_invFun := hiv }
  exact ⟨hI, g ⁻¹' U, by rw [Set.mem_preimage, hy]; exact hbU, hW, hW.preimage hpj, hHom,
    fun q => rfl⟩

/-- **The projection of the logarithmic étale space is evenly covered over every point.** -/
theorem isEvenlyCovered_logProj {Y : Type*} [TopologicalSpace Y] (ℓ : Y → ℂ)
    (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0) (y : Y) :
    IsEvenlyCovered (Work.SimplyConnected.ABS.logProj ℓ) y
      (Work.SimplyConnected.ABS.logProj ℓ ⁻¹' {y}) := by
  classical
  let expC : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  let ℓ' : Y → {z : ℂ // z ≠ 0} := fun y' => ⟨ℓ y', hne y'⟩
  have hℓ' : Continuous ℓ' := hℓ.subtype_mk fun y' => hne y'
  let PB : Type _ := {q : Y × ℂ // expC q.2 = ℓ' q.1}
  -- the pull-back of the exponential covering along `ℓ'`
  have hcov : IsEvenlyCovered (fun q : PB => q.1.1) y (expC ⁻¹' {ℓ' y}) :=
    isEvenlyCovered_pullback (f := expC) (g := ℓ') (b := ℓ' y)
      (Complex.isCoveringMap_exp (ℓ' y)) hℓ' rfl
  -- the two total spaces are canonically homeomorphic
  have hΦfwd : ∀ z : ↥(Work.SimplyConnected.ABS.logSpace ℓ), expC z.1.2 = ℓ' z.1.1 :=
    fun z => Subtype.ext z.2
  have hΦbwd : ∀ q : PB, Complex.exp q.1.2 = ℓ q.1.1 :=
    fun q => congrArg (Subtype.val : {z : ℂ // z ≠ 0} → ℂ) q.2
  let Φ : ↥(Work.SimplyConnected.ABS.logSpace ℓ) ≃ₜ PB :=
  { toFun := fun z => ⟨z.1, hΦfwd z⟩
    invFun := fun q => ⟨q.1, hΦbwd q⟩
    left_inv := fun z => Subtype.ext rfl
    right_inv := fun q => Subtype.ext rfl
    continuous_toFun := Continuous.subtype_mk continuous_subtype_val hΦfwd
    continuous_invFun := Continuous.subtype_mk continuous_subtype_val hΦbwd }
  have h1 : IsEvenlyCovered (Work.SimplyConnected.ABS.logProj ℓ) y (expC ⁻¹' {ℓ' y}) :=
    hcov.comp_homeomorph Φ
  -- the fibre over `ℓ' y` of `exp` is the fibre over `y` of the log cover
  have hfibFwd : ∀ z : (expC ⁻¹' {ℓ' y}), Complex.exp z.1 = ℓ y :=
    fun z => congrArg (Subtype.val : {z : ℂ // z ≠ 0} → ℂ) z.2
  have hfibBwd : ∀ q : ↥(Work.SimplyConnected.ABS.logProj ℓ ⁻¹' {y}),
      expC q.1.1.2 = ℓ' y :=
    fun q => Subtype.ext (q.1.2.trans (congrArg ℓ q.2))
  have hfibVal : Continuous fun q : ↥(Work.SimplyConnected.ABS.logProj ℓ ⁻¹' {y}) =>
      q.1.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  let fib : (expC ⁻¹' {ℓ' y}) ≃ₜ ↥(Work.SimplyConnected.ABS.logProj ℓ ⁻¹' {y}) :=
  { toFun := fun z => ⟨⟨(y, z.1), hfibFwd z⟩, rfl⟩
    invFun := fun q => ⟨q.1.1.2, hfibBwd q⟩
    left_inv := fun z => Subtype.ext rfl
    right_inv := fun q => Subtype.ext (Subtype.ext (Prod.ext q.2.symm rfl))
    continuous_toFun :=
      Continuous.subtype_mk (Continuous.subtype_mk
        (Continuous.prodMk continuous_const continuous_subtype_val) hfibFwd) (fun z => rfl)
    continuous_invFun := Continuous.subtype_mk hfibVal hfibBwd }
  exact h1.of_fiber_homeomorph fib

/-- **The projection of the logarithmic étale space is a covering map.**  Immediate from
`isEvenlyCovered_logProj`; this is the hypothesis consumed by
`Work.SimplyConnected.ABS.exists_windingHom`. -/
theorem isCoveringMap_logProj {Y : Type*} [TopologicalSpace Y] (ℓ : Y → ℂ)
    (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0) :
    IsCoveringMap (Work.SimplyConnected.ABS.logProj ℓ) :=
  fun y => isEvenlyCovered_logProj ℓ hℓ hne y

end Work.Analysis.RiemannSurface
