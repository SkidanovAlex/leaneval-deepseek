import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.TowerRank.ker_eq_twoTorsion

/-!
# Compatibility of levelwise isomorphisms of a `(ℤ/2^n)^r`-tower

This file proves `NK.NUV2.TowerRank.TowerCompatible r` (the group-theoretic crux of
`Submission/Work/NUV2/TowerRank/NOTES.md` §2): for two towers `G`, `H` of finite groups whose
level `n` is `(ℤ/2^n)^r`, with surjective transition maps, every *levelwise* family of
isomorphisms `G n ≃* H n` can be corrected to a family which is compatible with the two towers.

## The two steps

* **(i) the kernel of the transition map is the `2`-torsion** —
  `NK.NUV2.TowerRank.ker_eq_twoTorsion`: a surjection `(ℤ/2^{n+1})^r ↠ (ℤ/2^n)^r` has kernel
  exactly the subgroup `{x | x² = 1}`.

* **(ii) the *descending* construction.**  Given an isomorphism `ψ : G (n+1) ≃* H (n+1)`, the
  composite `β = qH n ∘ ψ : G (n+1) →* H n` has kernel `ψ⁻¹(H (n+1)[2]) = G (n+1)[2] = ker (qG n)`
  by (i) — *computed*, not chosen — so it factors through `qG n`, and the induced map
  `G n →* H n` is an isomorphism.  This is the map `descend n ψ`; by construction
  `descend n ψ ∘ qG n = qH n ∘ ψ`.

  Hence for every `N` a single isomorphism `e N` produces a family `fam e N` which is compatible
  up to level `N`.  The `N`-dependence is resolved by an ultrafilter limit: for each `n` the type
  `G n ≃* H n` is finite, so along a non-principal ultrafilter there is a value `φ n` attained on
  an ultrafilter-large set of `N`; all compatibility requirements hold simultaneously on the
  (nonempty) intersection of finitely many such sets.

## Formalisation note

All the group-theoretic statements are made for a bundled `TowerData r` (a pair of towers with
their structure), so that the towers occur *in the statements* and every declaration is a plain
function of the bundle.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.NUV2.TowerRank

/-- A pair of towers of `(ℤ/2^n)^r`-quotients, with surjective transition maps and levelwise
isomorphisms to the standard tower. -/
structure TowerData (r : ℕ) where
  G : ℕ → Type
  H : ℕ → Type
  grpG : ∀ n, Group (G n)
  grpH : ∀ n, Group (H n)
  fintG : ∀ n, Fintype (G n)
  fintH : ∀ n, Fintype (H n)
  qG : ∀ n, G (n + 1) →* G n
  qH : ∀ n, H (n + 1) →* H n
  hqG : ∀ n, Function.Surjective (qG n)
  hqH : ∀ n, Function.Surjective (qH n)
  isoG : ∀ n, G n ≃* Multiplicative (Fin r → ZMod (2 ^ n))
  isoH : ∀ n, H n ≃* Multiplicative (Fin r → ZMod (2 ^ n))

attribute [instance] TowerData.grpG TowerData.grpH TowerData.fintG TowerData.fintH

/-- (i) for `G`: the kernel of the transition map is the `2`-torsion. -/
private lemma qG_two_torsion {r : ℕ} (T : TowerData r) (n : ℕ) (x : T.G (n + 1)) :
    T.qG n x = 1 ↔ x ^ 2 = 1 :=
  ker_eq_twoTorsion (T.qG n) (T.hqG n) (T.isoG (n + 1)) (T.isoG n) x

/-- (i) for `H`. -/
private lemma qH_two_torsion {r : ℕ} (T : TowerData r) (n : ℕ) (x : T.H (n + 1)) :
    T.qH n x = 1 ↔ x ^ 2 = 1 :=
  ker_eq_twoTorsion (T.qH n) (T.hqH n) (T.isoH (n + 1)) (T.isoH n) x

/-- The composite `qH n ∘ ψ : G (n+1) →* H n`. -/
private def descendBeta {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) : T.G (n + 1) →* T.H n :=
  (T.qH n).comp ψ.toMonoidHom

private lemma descendBeta_apply {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) (x : T.G (n + 1)) :
    descendBeta T n ψ x = T.qH n (ψ x) := rfl

private lemma descendBeta_ker {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) : (descendBeta T n ψ).ker
      = ((T.qH n).comp ψ.toMonoidHom).ker := rfl

private lemma descendBeta_surjective {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) :
    Function.Surjective (descendBeta T n ψ) := by
  intro y
  obtain ⟨x, hx⟩ := T.hqH n y
  obtain ⟨z, hz⟩ := MulEquiv.surjective ψ x
  exact ⟨z, by rw [descendBeta_apply, hz, hx]⟩

/-- The kernel of `qH n ∘ ψ` is the kernel of `qG n`: both are the `2`-torsion. -/
private lemma descend_ker_eq {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) :
    (T.qG n).ker = (descendBeta T n ψ).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, descendBeta_apply]
  rw [qG_two_torsion T n x, qH_two_torsion T n (ψ x)]
  constructor
  · intro hx
    rw [← map_pow, hx, map_one]
  · intro hx
    have h : ψ (x ^ 2) = ψ 1 := by rw [map_pow, hx, map_one]
    exact ψ.injective h

/-- **The descending step**: from an isomorphism at level `n+1` produce the isomorphism at level
`n` which makes the square commute. -/
private noncomputable def descend {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) : T.G n ≃* T.H n :=
  (QuotientGroup.quotientKerEquivOfSurjective (T.qG n) (T.hqG n)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (descend_ker_eq T n ψ)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (descendBeta T n ψ)
        (descendBeta_surjective T n ψ)))

/-- The inverse of the canonical isomorphism `G (n+1) ⧸ ker (qG n) ≃* G n` is given by `mk`. -/
private lemma quotientKerEquivOfSurjective_symm_apply {r : ℕ} (T : TowerData r) (n : ℕ)
    (x : T.G (n + 1)) :
    (QuotientGroup.quotientKerEquivOfSurjective (T.qG n) (T.hqG n)).symm (T.qG n x)
      = (QuotientGroup.mk x : T.G (n + 1) ⧸ (T.qG n).ker) := by
  apply (QuotientGroup.quotientKerEquivOfSurjective (T.qG n) (T.hqG n)).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The canonical isomorphism `G (n+1) ⧸ ker (descendBeta T n ψ) ≃* H n` is computed by `mk`. -/
private lemma descendBeta_quotientKerEquivOfSurjective_mk {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) (x : T.G (n + 1)) :
    (QuotientGroup.quotientKerEquivOfSurjective (descendBeta T n ψ)
        (descendBeta_surjective T n ψ))
      (QuotientGroup.mk x : T.G (n + 1) ⧸ (descendBeta T n ψ).ker) = T.qH n (ψ x) := rfl

/-- The defining property of the descending step. -/
private lemma descend_spec {r : ℕ} (T : TowerData r) (n : ℕ)
    (ψ : T.G (n + 1) ≃* T.H (n + 1)) :
    (descend T n ψ).toMonoidHom.comp (T.qG n) = (T.qH n).comp ψ.toMonoidHom := by
  ext x
  have h1 : (descend T n ψ).toMonoidHom (T.qG n x) = descendBeta T n ψ x := by
    simp only [descend, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      quotientKerEquivOfSurjective_symm_apply T n x, QuotientGroup.quotientMulEquivOfEq_mk,
      descendBeta_quotientKerEquivOfSurjective_mk, descendBeta_apply]
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, descendBeta_apply]
  rfl

/-- The family obtained from `e N` by descending.  Levels above `N` are filled with `e`. -/
private noncomputable def fam {r : ℕ} (T : TowerData r) (e : ∀ n, T.G n ≃* T.H n)
    (N n : ℕ) : T.G n ≃* T.H n :=
  if _h : n < N then descend T n (fam T e N (n + 1)) else e n
termination_by N - n
decreasing_by omega

private lemma fam_of_lt {r : ℕ} (T : TowerData r) (e : ∀ n, T.G n ≃* T.H n) (N n : ℕ)
    (h : n < N) :
    fam T e N n = descend T n (fam T e N (n + 1)) := by
  rw [fam]
  simp [h]

private lemma fam_of_le {r : ℕ} (T : TowerData r) (e : ∀ n, T.G n ≃* T.H n) (N n : ℕ)
    (h : N ≤ n) : fam T e N n = e n := by
  rw [fam]
  simp [Nat.not_lt.mpr h]

/-- **The main group-theoretic statement.** -/
private theorem exists_compatible_family {r : ℕ} (T : TowerData r) (e : ∀ n, T.G n ≃* T.H n) :
    ∃ φ : ∀ n, T.G n ≃* T.H n,
      ∀ n, (φ n).toMonoidHom.comp (T.qG n) = (T.qH n).comp (φ (n + 1)).toMonoidHom := by
  classical
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hUle : (U : Filter ℕ) ≤ Filter.cofinite := Filter.hyperfilter_le_cofinite
  -- for each level, a value which the ultrafilter sees
  have key : ∀ n, ∃ a : T.G n ≃* T.H n, {N : ℕ | fam T e N n = a} ∈ U := by
    intro n
    have h1 : ∀ᶠ (N : ℕ) in (U : Filter ℕ), ∃ a : T.G n ≃* T.H n, fam T e N n = a :=
      Filter.Eventually.of_forall fun N => ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := (Ultrafilter.eventually_exists_iff (f := U)
      (P := fun (a : T.G n ≃* T.H n) (N : ℕ) => fam T e N n = a)).mp h1
    exact ⟨a, Ultrafilter.mem_coe.mp ha⟩
  choose φ hφ using key
  refine ⟨φ, fun n => ?_⟩
  -- a level `N` at which the ultrafilter sees everything needed
  have hcof : {N : ℕ | n < N} ∈ U := by
    refine hUle (Filter.mem_cofinite.mpr ?_)
    exact (Set.finite_Iic n).subset (fun x hx => by simpa using Nat.le_of_not_lt hx)
  have hI : ({N : ℕ | n < N} ∩ {N : ℕ | fam T e N n = φ n}
      ∩ {N : ℕ | fam T e N (n + 1) = φ (n + 1)}) ∈ U :=
    Filter.inter_mem (Filter.inter_mem hcof (hφ n)) (hφ (n + 1))
  obtain ⟨N, hN⟩ := Filter.nonempty_of_mem hI
  obtain ⟨⟨hN1, hN2⟩, hN3⟩ := hN
  have hstep : φ n = descend T n (φ (n + 1)) := by
    rw [← hN2, fam_of_lt T e N n hN1, hN3]
  rw [hstep]
  exact descend_spec T n (φ (n + 1))

theorem towerCompatible (r : ℕ) : NK.NUV2.TowerRank.TowerCompatible r := by
  intro G H hgrpG hgrpH hfintG hfintH qG qH hqG hqH isoG isoH e
  exact exists_compatible_family
    { G := G, H := H, grpG := hgrpG, grpH := hgrpH, fintG := hfintG, fintH := hfintH,
      qG := qG, qH := qH, hqG := hqG, hqH := hqH, isoG := isoG, isoH := isoH } e

end NK.NUV2.TowerRank
