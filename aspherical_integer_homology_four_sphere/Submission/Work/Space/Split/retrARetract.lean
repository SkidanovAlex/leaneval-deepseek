import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrABasic
import Submission.Work.Space.Split.retrAUnroll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology
open unitInterval

namespace Work.Space

/-- Continuity out of `X × Σ i, E i` is checked on the pieces. -/
theorem continuous_prod_sigma {ι : Type _} {E : ι → Type _} [∀ i, TopologicalSpace (E i)]
    {X Z : Type _} [TopologicalSpace X] [TopologicalSpace Z] {F : X × (Σ i, E i) → Z} :
    Continuous F ↔ ∀ i, Continuous (fun y : X × E i => F (y.1, ⟨i, y.2⟩)) := by
  refine ⟨fun h i => h.comp (continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd)),
    ?_⟩
  intro h
  rw [continuous_def]
  intro U hU
  rw [isOpen_prod_iff]
  rintro x y hxy
  obtain ⟨i, yi⟩ := y
  have h1 : IsOpen ((fun y : X × E i => F (y.1, ⟨i, y.2⟩)) ⁻¹' U) := (h i).isOpen_preimage U hU
  rw [isOpen_prod_iff] at h1
  obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := h1 x yi hxy
  refine ⟨A, Sigma.mk i '' B, hA, isOpenMap_sigmaMk _ hB, hxA, ⟨yi, hyB, rfl⟩, ?_⟩
  rintro ⟨x', y'⟩ ⟨hx', hy'⟩
  obtain ⟨b, hb, rfl⟩ := hy'
  exact hAB (show (x', b) ∈ A ×ˢ B from ⟨hx', hb⟩)


/-- Continuity out of `X × (Y ⊕ Z)` is checked on the two pieces. -/
theorem continuous_prod_sum {X Y Z W : Type _} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W] {F : X × (Y ⊕ Z) → W} :
    Continuous F ↔ Continuous (fun p : X × Y => F (p.1, Sum.inl p.2)) ∧
      Continuous (fun p : X × Z => F (p.1, Sum.inr p.2)) := by
  refine ⟨fun h => ⟨h.comp (continuous_fst.prodMk (continuous_inl.comp continuous_snd)),
      h.comp (continuous_fst.prodMk (continuous_inr.comp continuous_snd))⟩, ?_⟩
  rintro ⟨h1, h2⟩
  rw [continuous_def]
  intro U hU
  rw [isOpen_prod_iff]
  rintro x (y | y) hxy
  · have h1o : IsOpen ((fun p : X × Y => F (p.1, Sum.inl p.2)) ⁻¹' U) :=
      h1.isOpen_preimage U hU
    rw [isOpen_prod_iff] at h1o
    obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := h1o x y hxy
    refine ⟨A, Sum.inl '' B, hA, Topology.IsOpenEmbedding.inl.isOpenMap B hB, hxA,
      ⟨y, hyB, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨hx', hy'⟩
    obtain ⟨b, hb, rfl⟩ := hy'
    exact hAB (show (x', b) ∈ A ×ˢ B from ⟨hx', hb⟩)
  · have h2o : IsOpen ((fun p : X × Z => F (p.1, Sum.inr p.2)) ⁻¹' U) :=
      h2.isOpen_preimage U hU
    rw [isOpen_prod_iff] at h2o
    obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := h2o x y hxy
    refine ⟨A, Sum.inr '' B, hA, Topology.IsOpenEmbedding.inr.isOpenMap B hB, hxA,
      ⟨y, hyB, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨hx', hy'⟩
    obtain ⟨b, hb, rfl⟩ := hy'
    exact hAB (show (x', b) ∈ A ×ˢ B from ⟨hx', hb⟩)

end Work.Space

namespace Work.Space.Assembly

variable (a : Assembly)

theorem incShell_injective : Function.Injective a.incShell := by
  rintro ⟨v, ⟨⟨p, hp⟩, t⟩⟩ ⟨v', ⟨⟨p', hp'⟩, t'⟩⟩ h
  simp only [incShell] at h
  obtain ⟨hvv, hxx⟩ := Sigma.mk.inj_iff.mp h
  subst hvv
  rw [heq_eq_eq] at hxx
  rw [Prod.mk.injEq] at hxx
  obtain ⟨h1, h2⟩ := hxx
  have hpt : (⟨⟨p, hp⟩, t⟩ : SS × a.Torus v) = ⟨⟨p', hp'⟩, t'⟩ := by
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext h1, h2⟩
  rw [hpt]

/-- The radial collapse of a shell point to the boundary of the filling piece. -/
def radShellV (v : Cusp) (x : SS × a.Torus v) : {q : a.Y // q ∈ a.boundarySet} :=
  ⟨⟨v, (radPt x.1.1 x.1.2, x.2)⟩, sqNorm_radPt x.1.1 x.1.2⟩

theorem continuous_radShellV (v : Cusp) : Continuous (a.radShellV v) :=
  Continuous.subtype_mk
    (continuous_sigmaMk.comp ((continuous_radPt.comp continuous_fst).prodMk continuous_snd))
    (fun x => sqNorm_radPt x.1.1 x.1.2)

def radShell (y : a.ShellY) : {q : a.Y // q ∈ a.boundarySet} := a.radShellV y.1 y.2

theorem continuous_radShell : Continuous a.radShell := by
  rw [continuous_sigma_iff]
  intro v
  exact a.continuous_radShellV v

/-- The retraction on the unrolled shell: collapse to the boundary, then apply `glue.symm`. -/
def gShell (y : a.ShellY) : a.Mbar := (a.glue.symm (a.radShell y)).1

theorem continuous_gShell : Continuous a.gShell :=
  continuous_subtype_val.comp ((a.glue.symm.continuous).comp a.continuous_radShell)

/-- The retraction on the unrolled `A`, as a plain function. -/
def gFun (x : a.U) : a.Mbar := Sum.elim id a.gShell x

theorem continuous_gFun : Continuous a.gFun := by
  rw [continuous_sum_dom]
  exact ⟨continuous_id, a.continuous_gShell⟩

/-- The radial collapse of a shell point glued to `m` gives back `m`. -/
theorem glue_symm_radShell_eq {y : a.ShellY} {m : a.Mbar} {hm : m ∈ a.Tset}
    (hgl : (a.glue ⟨m, hm⟩ : {q : a.Y // q ∈ a.boundarySet}) = a.incShell y) :
    a.glue.symm (a.radShell y) = ⟨m, hm⟩ := by
  obtain ⟨hv, ⟨⟨p, hp⟩, t⟩⟩ := y
  have hb : a.incShell ⟨hv, (⟨p, hp⟩, t)⟩ ∈ a.boundarySet := hgl ▸ (a.glue ⟨m, hm⟩).2
  have hbsq : sqNorm p = 1 := hb
  have hrad : a.radShell ⟨hv, (⟨p, hp⟩, t)⟩ =
      ⟨a.incShell ⟨hv, (⟨p, hp⟩, t)⟩, hb⟩ := by
    apply Subtype.ext
    show (⟨hv, (radPt p hp, t)⟩ : a.Y) = a.incShell ⟨hv, (⟨p, hp⟩, t)⟩
    rw [show a.incShell ⟨hv, (⟨p, hp⟩, t)⟩ = (⟨hv, (p, t)⟩ : a.Y) from rfl,
      show radPt p hp = p from radPt_eq_self p hbsq]
  rw [hrad,
    show (⟨a.incShell ⟨hv, (⟨p, hp⟩, t)⟩, hb⟩ : {q : a.Y // q ∈ a.boundarySet}) =
      a.glue ⟨m, hm⟩ from Subtype.ext hgl.symm]
  exact a.glue.symm_apply_apply ⟨m, hm⟩

theorem factorsThrough_gFun : ∀ x x' : a.U, a.qA x = a.qA x' → a.gFun x = a.gFun x' := by
  intro x x' h
  rcases x with m | y <;> rcases x' with m' | y'
  · change m = m'
    exact a.incMbar_injective (Subtype.ext_iff.mp h)
  · obtain ⟨hm, hgl⟩ := a.incMbar_eq_incY_iff.mp (Subtype.ext_iff.mp h)
    change m = (a.glue.symm (a.radShell y')).1
    rw [a.glue_symm_radShell_eq hgl]
  · obtain ⟨hm, hgl⟩ := a.incY_eq_incMbar_iff.mp (Subtype.ext_iff.mp h)
    change (a.glue.symm (a.radShell y)).1 = m'
    rw [a.glue_symm_radShell_eq hgl]
  · change (a.glue.symm (a.radShell y)).1 = (a.glue.symm (a.radShell y')).1
    have h1 : a.incShell y = a.incShell y' := a.incY_injective (Subtype.ext_iff.mp h)
    rw [a.incShell_injective h1]

/-- The quotient map `qA` as a continuous map. -/
def qACM : C(a.U, {z : a.Mhat // z ∈ a.Aset}) := ⟨a.qA, a.continuous_qA⟩

/-- The map `U → M̄` as a continuous map. -/
def gCM : C(a.U, a.Mbar) := ⟨a.gFun, a.continuous_gFun⟩

/-- **The retraction `r : A → M̄`.** -/
noncomputable def r : C({z : a.Mhat // z ∈ a.Aset}, a.Mbar) :=
  Topology.IsQuotientMap.lift (f := a.qACM) a.isQuotientMap_qA a.gCM a.factorsThrough_gFun

theorem r_comp_qACM : a.r.comp a.qACM = a.gCM :=
  Topology.IsQuotientMap.lift_comp (f := a.qACM) a.isQuotientMap_qA a.gCM a.factorsThrough_gFun

theorem r_qA (x : a.U) : a.r (a.qACM x) = a.gCM x := by
  simpa using DFunLike.congr_fun a.r_comp_qACM x

/-- The inclusion `M̄ → A`. -/
def i : C(a.Mbar, {z : a.Mhat // z ∈ a.Aset}) :=
  ⟨fun m => ⟨a.incMbar m, a.incMbar_mem_Aset m⟩,
    Continuous.subtype_mk a.continuous_incMbar fun m => a.incMbar_mem_Aset m⟩

theorem r_comp_i : a.r.comp a.i = ContinuousMap.id a.Mbar := by
  ext m
  have h := a.r_qA (Sum.inl m)
  simpa [qACM, gCM, gFun, i, qA] using h

end Work.Space.Assembly
