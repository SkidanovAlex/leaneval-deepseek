import Mathlib
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
import Submission.Work.SSGRoute.PT.mapH2_zsmulHomEnd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `α²` on the trivial module: the description on the generator

Everything here is at a **single universe** `u`: in this workspace a statement whose binder is
`H2 G M` only elaborates when `G` and `M` live in the same universe, which is why the assembly is
done at one universe (sufficient for the target, where all the relevant types are at universe `0`).
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- **`α²` on the trivial module, evaluated at `↑k`.** -/
theorem alphaTwo_trivMod_apply {G : Type u} [TopologicalSpace G] [Group G] (p : ℕ) [Fact p.Prime]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C] (k : ℤ)
    (hZ : Work.GroupCohomology.IsEquivariant G (zsmulHomEnd k C))
    (hcomp : Work.GroupCohomology.IsEquivariant G
      ((zsmulHomEnd k C).comp (evalOne G p C)))
    (x : Work.AbsoluteKummer.H2 G (ConjHom (TrivMod G p) C))
    (hk : ((k : ℤ) : TrivMod G p) ∈ Work.GroupCohomology.invariants G (TrivMod G p)) :
    alphaTwo x ⟨((k : ℤ) : TrivMod G p), hk⟩
      = k • (Work.AbsoluteKummer.mapH2 (evalOne G p C) (evalOne_equivariant G p C) x) := by
  have h1 := alphaTwo_evalHom x ⟨((k : ℤ) : TrivMod G p), hk⟩
  rw [h1]
  simp only [Subtype.coe_mk]
  have h2 := mapH2_congr_coeff (hφ := evalHom_smul (C := C) ((k : ℤ) : TrivMod G p) hk)
    (hψ := hcomp) (h := evalHom_eq_zsmul_comp_evalOne G p C k)
  rw [h2]
  have h3 := mapH2_comp (φ := evalOne G p C) (ψ := zsmulHomEnd k C)
    (hφ := evalOne_equivariant G p C) (hψ := hZ) (hc := hcomp) (x := x)
  rw [h3]
  exact mapH2_zsmulHomEnd k hZ _

/-- `mapZ2` of a composite coefficient map: both sides have components `ψ (φ (c q))`. -/
theorem mapZ2_comp {G : Type u} [TopologicalSpace G] [Group G] {M : Type u} {N : Type u}
    {P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hc : Work.GroupCohomology.IsEquivariant G (ψ.comp φ)) (c : Work.AbsoluteKummer.Z2 G M) :
    Work.AbsoluteKummer.mapZ2 (ψ.comp φ) hc c
      = Work.AbsoluteKummer.mapZ2 ψ hψ (Work.AbsoluteKummer.mapZ2 φ hφ c) :=
  Subtype.ext (funext (fun _ => rfl))

/-- The gate used by the base-case wrapper: `alphaTwo x` **at the generator** `1` is the class
`y = mapH2 (evalOne G p C) _ x` — so `homZModEquivPTor`'s coercion equation
`↑(e f) = f 1` identifies `alphaTwo` with `kummerH2Map`. -/
theorem alphaTwo_trivMod_apply_one {G : Type u} [TopologicalSpace G] [Group G] (p : ℕ)
    [Fact p.Prime] {C : Type u} [AddCommGroup C] [DistribMulAction G C]
    (x : Work.AbsoluteKummer.H2 G (ConjHom (TrivMod G p) C))
    (hk : (((1 : ℤ) : TrivMod G p)) ∈ Work.GroupCohomology.invariants G (TrivMod G p)) :
    alphaTwo x ⟨((1 : ℤ) : TrivMod G p), hk⟩
      = Work.AbsoluteKummer.mapH2 (evalOne G p C) (evalOne_equivariant G p C) x := by
  have hZ : Work.GroupCohomology.IsEquivariant G (zsmulHomEnd (1 : ℤ) C) := by
    intro g c
    simp [zsmulHomEnd_apply]
  have hcomp : Work.GroupCohomology.IsEquivariant G
      ((zsmulHomEnd (1 : ℤ) C).comp (evalOne G p C)) :=
    hZ.comp (evalOne_equivariant G p C)
  rw [alphaTwo_trivMod_apply p 1 hZ hcomp x hk]
  exact one_zsmul _

end

end Work.SSGRoute.PT
