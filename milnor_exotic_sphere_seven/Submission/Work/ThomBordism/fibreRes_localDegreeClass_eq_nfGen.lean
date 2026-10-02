import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.branchSign_uniform_of_fibreGen
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.nfRelCohIso
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.nfRes_span_top_of_generator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# VERDICT on the requested lemma `Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen`

## 1. The request cannot be proved as written: it does not elaborate

The statement sent to me (kept verbatim below) carries the hypothesis type
`Work.Tubular.NormalSubE`, which **is not defined anywhere in this workspace**.  Machine-checked,
by building this file with the text exactly as sent:

```
error: Submission/Work/ThomBordism/fibreRes_localDegreeClass_eq_nfGen.lean:12:52:
  Unknown identifier `Work.Tubular.NormalSubE`
```

(`grep -rn NormalSubE --include=*.lean .` returns the requested file, and nothing else.)  The evident
intended hypothesis is `Work.Tubular.NormalSphSub E ε`: that is the type used by every other statement
in this area, by the previous attempt at this very path (child `H4-L2645`), and by the sibling request
`Submission/Work/ThomBordism/fibreRes_localDegreeClass_eq_nfGen_uniform.lean` which the same requester
created in the same round — the two requests differ only by this typo.  I therefore report the
defect (`declare_false` on this path) so that the repaired statement can be carried at its sibling
path.

## 2. The requested statement, verbatim

```
theorem fibreRes_localDegreeClass_eq_nfGen (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSubE ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      ∀ x : V.pt, nfRes E x k U = t • nfGen hk E ND x := by sorry
```

## 3. The content of the (repaired) statement, and where the recorded API stops

`Work.ThomBordism.nfGen hk E ND x` (the pullback of `Work.ThomBordism.stdThomGen` along the frame
reading `nfRead`) is a generator of `H^k(ν_x, ν_x∖0) ≅ ℤ` (`nfGen_span`, `nfRelCohIso`), and by §4
below *every* local-degree class `U` restricts to `± nfGen` on every fibre.  Writing
`nfRes U = t_D • nfGen` for the datum `D` of `U`, the requested statement is exactly

> `t_D` does not depend on `D`.

(It is *not* a statement about the *value* of `t_D` — that is why it does not meet the obstruction
that killed the sharp form.)  Since `stdThomGen` is a single class, one has `nfGen = s • o` with a
*global* opaque `s = ±1` and `o` the frame-reading generator, while `nfRes U` is pinned by the local
degree equation and does not involve any opaque choice; hence the statement is *equivalent* to the
constancy in the datum of a choice-independent sign.  The `∃ t` weakening therefore does **not** evade
the obstruction recorded by the previous attempts on this content — the sharp form at this path
(`H4-L2645`: the theory records only that `nfGen` is *one of the two* generators of a free rank-one
group), `Work.ThomBordism.localDegreeSign_uniform` (`H4-L2639`) and
`Work.ThomBordism.univLocalDegreeClass` (`H4-L2636`): the tree has per-datum statements only (the
sign-blind constructions of `localDegreeSpan`/`tubeLocalDegreeGlobalSign`, "the sign `s` is not
determined here", `gtdU_localDegreeExists`), and **no lemma relates the signs of two distinct data**.
What the repaired statement needs is the *localisation* of the local degree equation to a fibre — the
unbuilt last-mile/`PT-CONV` chapter — not merely a de-opaquing of `Classical.choice`.

## 4. What this file proves instead (the provable half, and the exact boundary)

* `isLocalDegreeClass_eq_of_nondeg` — **the local-degree class is determined**: a generating
  local-degree class `U₀` (as produced by `Work.ThomBordism.localDegreeGenExists`) is the *unique*
  local-degree class, provided one class `x` has `⟨z^*x, V.c⟩ ≠ 0`.  This is the reduction that turns
  the target's `∀ U` into a statement about a single canonical class (the requester's own notes use
  this fact; here it is machine-checked).
* `exists_pm_smul_eq_of_span_eq_top`, `nfRes_eq_pm_nfGen_of_span` — the elementary bookkeeping: two
  generators of a `ℤ`-module isomorphic to `ℤ` differ by a sign.
* `nfRes_localDegreeClass_eq_pm_nfGen_of_generatorPres` and
  **`nfRes_localDegreeClass_eq_pm_nfGen`** — **the per-datum form of the requested statement**,
  unconditionally:

  `∀ D, ∃ t ∈ {±1}, nfRes E x k U = t • nfGen hk E ND x`.

  The two statements differ exactly by the cross-datum constancy of §3: this file's theorem is the
  provable half, and it is the ingredient any future proof of the uniform statement will contain.

The two inputs of the last theorem were delegated this session, reviewed and proved:
`Work.ThomBordism.nfRes_span_top_of_generator` (the fibre restriction of a generator of
`H^k(ν, ν∖0)` generates the fibre module — an isomorphism because `ν` is the normal bundle of an
*oriented* closed embedding, the Möbius-type counterexample for general bundles being excluded by
`Man8`) and `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero` (the non-degeneracy
`∃x, ⟨z^*x, V.c⟩ ≠ 0`: the fundamental class of a connected `Man8` is not torsion).

Everything in this file is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); the module has
no `sorry`.  It is importable as `Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen`.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-! ## The local-degree class is determined (given a generating solution) -/

/-- **Uniqueness of the local-degree class.**  If `U₀` is a local-degree class whose span is
everything (the class produced by `Work.ThomBordism.localDegreeGenExists`), and if the functional
`x ↦ ⟨z^*x, V.c⟩` is not identically zero, then *every* local-degree class equals `U₀`.

Proof: for `W = U - U₀` one has `Φ x W = 0` for all `x`, where `Φ x W` is the pairing
`⟨x ⌣ W, collapseRelK8⟩`; since `span{U₀} = ⊤`, `W = m • U₀`, and evaluating at a class `x₀` with
`⟨z^*x₀, V.c⟩ ≠ 0` forces `m = 0`. -/
theorem isLocalDegreeClass_eq_of_nondeg {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} {C : Work.Tubular.TubeChart E ε} (q : Work.Tubular.NormalSphSub E ε)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (hnd : ∃ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c ≠ 0)
    {U₀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)}
    (hspan : Submodule.span ℤ ({U₀} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤)
    (hU₀ : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U₀)
    (hU : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U) : U = U₀ := by
  classical
  let X := TopCat.of (Work.Tubular.NormalTotal E)
  let A := Work.Tubular.normalNonzero E
  let c := Work.Tubular.collapseRelK8 C g hg hR hbox
  let RHS : Work.Thom.Coh ℤ 8 X → ℤ := fun x =>
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c
  -- the local-degree functional, as a family of linear functionals in the *second* variable
  -- (`LinearMap.comp` of the project's `mixedCup`/`relKronH` would force the elaborator to unfold
  -- the module structure of the huge type `RelCoh ℤ k X A`; building the structure by hand is
  -- cheap -- the same device is used in `gtdU_localDegreeExists`.)
  let Φ : Work.Thom.Coh ℤ 8 X → (Work.Thom.RelCoh ℤ k X A →ₗ[ℤ] ℤ) := fun x =>
    { toFun := fun W => Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ c)
      map_add' := by
        intro a b
        rw [map_add (Work.Cohomology.mixedCup X A 8 k x) a b,
            LinearMap.map_add (Work.Tubular.relKronH X A (8 + k)) _ _,
            LinearMap.add_apply]
      map_smul' := by
        intro n a
        rw [LinearMap.map_smul (Work.Cohomology.mixedCup X A 8 k x) n a,
            LinearMap.map_smul (Work.Tubular.relKronH X A (8 + k)) n _,
            LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] }
  have hΦ : ∀ (x : Work.Thom.Coh ℤ 8 X) (W : Work.Thom.RelCoh ℤ k X A),
      Φ x W = Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ c) := fun x W => rfl
  -- the degree bridge between the defining degree `k + 8` and the working degree `8 + k`
  have hbridge : ∀ (W : Work.Thom.RelCoh ℤ k X A) (x : Work.Thom.Coh ℤ 8 X),
      Work.Tubular.relKronH X A (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup X A 8 k x W)) c
      = Φ x W := by
    intro W x
    rw [hΦ x W]
    exact (Work.Tubular.relKronH_bridgeA (Nat.add_comm 8 k)
      ((Work.Cohomology.mixedCup X A 8 k x W)) c).symm
  have hU' : ∀ x, Φ x U = RHS x := by
    intro x
    rw [← hbridge U x]
    exact hU x
  have hU₀' : ∀ x, Φ x U₀ = RHS x := by
    intro x
    rw [← hbridge U₀ x]
    exact hU₀ x
  have hW : ∀ x, Φ x (U - U₀) = 0 := by
    intro x
    rw [map_sub, hU' x, hU₀' x, sub_self]
  obtain ⟨m, hm⟩ := branchSign_exists_int_smul_eq_of_mem_span_singleton
    (U := U₀) (y := U - U₀)
    (show U - U₀ ∈ Submodule.span ℤ ({U₀} : Set (Work.Thom.RelCoh ℤ k X A)) from by
      rw [hspan]; exact Submodule.mem_top)
  obtain ⟨x₀, hx₀⟩ := hnd
  have hzero : Φ x₀ (U - U₀) = 0 := hW x₀
  rw [← hm] at hzero
  -- `Φ x₀` is `ℤ`-linear, so it does not see the multiple `m` as anything but a factor
  have hstep : Φ x₀ (m • U₀) = m * RHS x₀ := by
    have h' : Φ x₀ (m • U₀) = m • Φ x₀ U₀ :=
      AddMonoidHom.map_zsmul (Φ x₀).toAddMonoidHom m U₀
    rw [h', hU₀' x₀, zsmul_eq_mul, Int.cast_id]
  have hm0 : m = 0 := by
    rw [hstep] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hx₀
  have hlast : U - U₀ = 0 := by
    rw [← hm, hm0]
    exact zero_smul ℤ U₀
  exact sub_eq_zero.mp hlast

/-! ## Two generators of a `ℤ`-module isomorphic to `ℤ` differ by a sign -/

/-- **Two generators of a `ℤ`-module isomorphic to `ℤ` differ by `±1`.** -/
theorem exists_pm_smul_eq_of_span_eq_top {M : Type*} [AddCommGroup M] [Module ℤ M]
    (h : Nonempty (M ≃ₗ[ℤ] ℤ)) {a b : M} (ha : Submodule.span ℤ ({a} : Set M) = ⊤)
    (hb : Submodule.span ℤ ({b} : Set M) = ⊤) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ a = t • b := by
  obtain ⟨e⟩ := h
  rcases eq_pm_of_span_eq_top_of_iso e ha hb with h' | h'
  · exact ⟨1, Or.inl rfl, by rw [h']; simp⟩
  · exact ⟨-1, Or.inr rfl, by rw [h']; simp⟩

/-! ## The fibre restriction of a local-degree class is `±` the oriented fibre generator -/

/-- **The per-datum sign, for a class whose fibre restriction generates.**  The fibre module
`H^k(ν_x, ν_x∖0;ℤ)` is `ℤ` (`Work.ThomBordism.nfRelCohIso`) and the oriented fibre generator
`nfGen` is a generator of it (`Work.ThomBordism.nfGen_span`), so any other generator is `± nfGen`. -/
theorem nfRes_eq_pm_nfGen_of_span {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    {U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)}
    (hspan : Submodule.span ℤ ({Work.ThomBordism.nfRes E x k U} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      Work.ThomBordism.nfRes E x k U = t • Work.ThomBordism.nfGen hk E ND x :=
  exists_pm_smul_eq_of_span_eq_top (nfRelCohIso hk E ND x) hspan (nfGen_span hk E ND x)

/-- **The per-datum form of the requested statement.**  *Conditional only on the
generator-preservation of the fibre restriction* (the delegated lemma
`Work.ThomBordism.nfRes_span_top_of_generator`, which is true because `ν` is the normal bundle of an
*oriented* embedding): for every datum and every local-degree class `U`, the restriction of `U` to
any fibre is `± nfGen`.

The proof is the reduction the target's `∀ U` needs: `Work.ThomBordism.localDegreeGenExists` supplies
a local-degree class `U₀` that generates `H^k(ν,ν∖0)`, `Work.ThomBordism.isLocalDegreeClass_eq_of_nondeg`
shows `U = U₀` (using the non-degeneracy `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`),
`hgen` makes `nfRes U₀` generate the fibre module, and
`Work.ThomBordism.nfRes_eq_pm_nfGen_of_span` finishes with `nfRelCohIso`/`nfGen_span`. -/
theorem nfRes_localDegreeClass_eq_pm_nfGen_of_generatorPres (k : ℕ) (hk : 1 ≤ k)
    (hgen : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
      {U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)},
      Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ →
      Submodule.span ℤ ({Work.ThomBordism.nfRes E x k U} : Set (Work.Thom.RelCoh ℤ k
        ↥(Work.ThomBordism.nfSet E x) (Work.ThomBordism.nfPunct E x))) = ⊤) :
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      ∀ x : V.pt, ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
        Work.ThomBordism.nfRes E x k U = t • Work.ThomBordism.nfGen hk E ND x := by
  intro V _inst E ND ε C q hU R hR hbox g hg hg2 U hUld x
  -- a local-degree class that generates `H^k(ν, ν∖0)`
  obtain ⟨U₀, hspan₀, hU₀⟩ := localDegreeGenExists hk E C.eps_pos C q hU hR hbox g hg hg2
  -- the local-degree equation pins it
  have hnd := exists_kronH_zeroSection_fund_ne_zero (k := k) E
  have hUeq : U = U₀ :=
    isLocalDegreeClass_eq_of_nondeg q hR hbox g hg hg2 hnd hspan₀ hU₀ hUld
  rw [hUeq]
  exact nfRes_eq_pm_nfGen_of_span hk E ND x (hgen E ND x hspan₀)

/-- **The per-datum form of the requested statement, unconditionally.**  Every local-degree class
restricts on every fibre to `± nfGen`: the two statements differ exactly by the constancy of this sign
in the datum, which is the unbuilt cross-datum comparison (see the module docstring). -/
theorem nfRes_localDegreeClass_eq_pm_nfGen (k : ℕ) (hk : 1 ≤ k) :
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      ∀ x : V.pt, ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
        Work.ThomBordism.nfRes E x k U = t • Work.ThomBordism.nfGen hk E ND x := by
  refine nfRes_localDegreeClass_eq_pm_nfGen_of_generatorPres k hk ?_
  intro V _inst E ND x U hspan
  exact nfRes_span_top_of_generator (k := k) hk E ND x hspan

end

end Work.ThomBordism
