import Mathlib
import Submission.Work.Serre.serreK2Proved
import Submission.Work.Serre.serreK2Int
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreK2Aux
import Submission.Work.Serre.rangeWhiteheadInclInt
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.cylRelPi
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.Engine

namespace Work.Serre.Assembly

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- **The integral version of `Work.Serre.isIso_ratHomologyMap_attachIncl_aux`.**  The inclusion of
an attachment `attachIncl m Y ι f` induces an isomorphism on *integral* homology in degrees `≤ m`
(attaching `(m+2)`-cells leaves `H_t` unchanged for `t ≤ m`; the proof is the compression property
of `compression_of_relPiVanishing`/`compressRel_attachCells_range`, the integral range Whitehead
theorem `rangeWhiteheadInclInt` in place of its rational counterpart, and the homeomorphism
`rangeHomeo` of the range). -/
theorem isIso_intHomologyMap_attachIncl_aux (m : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere m, Y)) (t : ℕ) (ht : t ≤ m) :
    IsIso (Work.Serre.intHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t) := by
  have hcomp : ∀ d : ℕ, d ≤ m + 1 → Work.RatHurewicz.CompressRel
      (Work.RatHurewicz.attachCells m Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl m Y ι f)) d :=
    Work.RatHurewicz.compressRel_attachCells_range m Y ι f
  have hiso : IsIso (Work.Serre.intHomologyMap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t) :=
    Work.Serre.rangeWhiteheadInclInt hcomp t (by omega)
  let e := Work.RatHurewicz.rangeHomeo m Y ι f
  let eC : C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl m Y ι f))) := ⟨⇑e, e.continuous⟩
  have hfact : (Work.RatHurewicz.setIncl
        (Set.range (Work.RatHurewicz.attachIncl m Y ι f))).comp eC
      = Work.RatHurewicz.attachIncl m Y ι f := by
    ext y
    rfl
  have hsplit : Work.Serre.intHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t
      = Work.Serre.intHomologyMap eC t ≫ Work.Serre.intHomologyMap (Work.RatHurewicz.setIncl
          (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t := by
    rw [← Work.Serre.intHomologyMap_comp eC
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t, hfact]
  rw [hsplit]
  have hE : IsIso (Work.Serre.intHomologyMap eC t) :=
    Work.Serre.isIso_intHomologyMap_of_homotopyEquiv e.toHomotopyEquiv t
  have := hiso
  have := hE
  infer_instance

-- **The sharp integral range Whitehead statement.**  If `f : X → Y` is bijective on `π_i` at every
-- base point for all `i < N`, then `f` induces an isomorphism on integral singular homology in all
-- degrees `0 < i < N`.
--
-- This is the integral analogue of `Work.Serre.SerreK2`, proved over `ℚ` in
-- `Submission/Work/Serre/serreK2Proved.lean`.  That proof writes `N = n + 2` and replaces `f` by
-- `f' = killIncl (n+1) Y ∘ f`, where `KillCells (n+1) Y` is `Y` with an `(n+3)`-cell attached along
-- *every* map `S^{n+2} → Y` (`Submission/Work/Serre/serreAttachKillPi.lean`, `killCells_step`).
-- Then `π_i(f')` is bijective for `i ≤ n+1 = N-1` and `π_N` of the *target* of `f'` is trivial;
-- consequently the relative homotopy groups of the pair `(cyl f', range (cylIncl f'))` vanish in
-- degrees `≤ n+1` (`Work.Serre.cylRelPi_vanish` together with
-- `Work.Serre.subsingleton_pi_cyl_of_subsingleton`, which is where the triviality of `π_N` of the
-- target is used, and `Work.Serre.RangeOne.subsingleton_relPi_range_cylIncl` for the transfer to
-- the subspace), the compression property in dimensions `≤ n+2 = N` follows
-- (`Work.RatHurewicz.compression_of_relPiVanishing`), and the range Whitehead result
-- `Work.Serre.rangeWhiteheadInclInt` (integral; compression up to `M` gives homology isomorphisms
-- in degrees `< M`) gives the isomorphism for the cylinder inclusion in degrees `< N`.  Since the
-- cylinder is homotopy equivalent to its target, and the cell attachment `killIncl (n+1) Y`
-- induces an isomorphism on integral homology in degrees `< N` (the integral analogue of
-- `Work.Serre.isIso_ratHomologyMap_attachIncl_aux`, using `rangeWhiteheadInclInt` in place of
-- `isIso_ratHomologyMap_setIncl_of_compressRel`), the claim for `f` follows by cancellation.
--
-- The degree-`0` case is deliberately excluded (`0 < i`), so the integral form of
-- `Work.Serre.hZeroOfPiZero` is not needed here.  The range is exactly what callers need:
-- `π`-bijectivity through `N - 1` gives homology isomorphisms through `N - 1`, one degree better
-- than `Work.Serre.serreK2Int`, which needs `π`-bijectivity through `N` for the same conclusion. -/
theorem serreK2IntSharp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (N : ℕ)
    (h : ∀ i : ℕ, i < N → ∀ x : X, Function.Bijective (Work.Serre.piMapN f i x)) :
    ∀ i : ℕ, 0 < i → i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) i) := by
  intro j hj0 hjN
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  by_cases hN : N ≤ 1
  · exfalso; omega
  obtain ⟨n, hn⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  subst hn
  -- `h : ∀ i, i < n + 2 → ∀ x, Bijective (piMapN f i x)`, `hjN : j < n + 2`
  -- ### the `π`-data of `f' = killIncl (n+1) Y ∘ f`
  have hbij : ∀ i : ℕ, i ≤ n + 1 → ∀ x : X,
      Function.Bijective (Work.Serre.piMapN ((Work.Serre.killIncl (n + 1) Y).comp f) i x) := by
    intro i hi x
    have h1 : Function.Bijective
        (Work.Serre.piMapN (Work.Serre.killIncl (n + 1) Y) i (f x)) :=
      (Work.Serre.killCells_step (n + 1) Y).1 i hi (f x)
    have h2 : Function.Bijective (Work.Serre.piMapN f i x) := h i (by omega) x
    rw [show Work.Serre.piMapN ((Work.Serre.killIncl (n + 1) Y).comp f) i x
        = (Work.Serre.piMapN (Work.Serre.killIncl (n + 1) Y) i (f x))
          ∘ (Work.Serre.piMapN f i x) from
      funext fun a => Work.Serre.piMapN_comp f (Work.Serre.killIncl (n + 1) Y) i x a]
    exact h1.comp h2
  -- ### `π_{n+2}` of the target of the cylinder inclusion of `f'` is trivial
  have hsub : ∀ y : Work.Serre.cyl ((Work.Serre.killIncl (n + 1) Y).comp f),
      Subsingleton (HomotopyGroup (Fin (n + 2))
        (Work.Serre.cyl ((Work.Serre.killIncl (n + 1) Y).comp f)) y) :=
    fun y => Work.Serre.subsingleton_pi_cyl_of_subsingleton _ (n + 1) y
      ((Work.Serre.killCells_step (n + 1) Y).2.1
        (Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f) y))
  -- ### the relative groups of the cylinder inclusion of `f'` vanish below `n + 2`
  have hrel : ∀ x : X, ∀ k : ℕ, k ≤ n + 1 → Subsingleton
      (Work.RatHurewicz.RelHomotopyGroup
        (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)) x k) := by
    intro x k hk
    refine Work.Serre.cylRelPi_vanish ((Work.Serre.killIncl (n + 1) Y).comp f) x n ?_ ?_ ?_ k hk
    · -- geometric `π₀`-injectivity of `cylIncl f'`
      intro x' hx'
      have h1 : Joined ((Work.Serre.killIncl (n + 1) Y) (f x))
          ((Work.Serre.killIncl (n + 1) Y) (f x')) := by
        obtain ⟨γ⟩ := hx'
        have h3 : Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f)
              (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f) x)
            = (Work.Serre.killIncl (n + 1) Y) (f x) := by
          simpa using congrArg (fun g : C(X, Work.Serre.KillCells (n + 1) Y) => g x)
            (Work.Serre.cylRetract_cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))
        have h4 : Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f)
              (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f) x')
            = (Work.Serre.killIncl (n + 1) Y) (f x') := by
          simpa using congrArg (fun g : C(X, Work.Serre.KillCells (n + 1) Y) => g x')
            (Work.Serre.cylRetract_cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))
        exact ⟨(γ.map (Work.Serre.cylRetract
          ((Work.Serre.killIncl (n + 1) Y).comp f)).continuous).cast h3 h4⟩
      have h2 : Joined (f x) (f x') :=
        Work.Serre.joined_of_piMapN_zero_injective (Work.Serre.killIncl (n + 1) Y) (f x)
          ((Work.Serre.killCells_step (n + 1) Y).1 0 (by omega) (f x)).1 h1
      exact Work.Serre.joined_of_piMapN_zero_injective f x (h 0 (by omega) x).1 h2
    · -- injectivity of `π_m(cylIncl f')` for `m ≤ n`
      intro m hm
      exact (Work.Serre.bijective_piMapN_cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)
        (m + 1) (by omega) x (hbij (m + 1) (by omega) x)).1
    · -- surjectivity of `π_m(cylIncl f')` for `m ≤ n + 1`
      intro m hm
      rcases lt_or_eq_of_le hm with hlt | heq
      · exact (Work.Serre.bijective_piMapN_cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)
          (m + 1) (by omega) x (hbij (m + 1) (by omega) x)).2
      · subst heq
        intro b
        exact ⟨1, (hsub (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f) x)).elim _ _⟩
  -- ### transfer to the subspace `Set.range (cylIncl f')`
  have hset : ∀ a : ↥(Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))),
      ∀ k : ℕ, k ≤ n + 1 → Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl
          (Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)))) a k) := by
    intro a k hk
    obtain ⟨x, hx⟩ := a.2
    have hEq : (⟨Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f) x, x, rfl⟩
        : ↥(Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)))) = a :=
      Subtype.ext hx
    exact hEq ▸ (Work.Serre.RangeOne.subsingleton_relPi_range_cylIncl
      ((Work.Serre.killIncl (n + 1) Y).comp f) x k (hrel x k hk))
  -- ### compression of the pair `(cyl f', range (cylIncl f'))` in dimensions `≤ n + 2`
  have hcomp : ∀ d : ℕ, d ≤ n + 2 → Work.RatHurewicz.CompressRel
      (Work.Serre.cyl ((Work.Serre.killIncl (n + 1) Y).comp f))
      (Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))) d := by
    have hc := Work.RatHurewicz.compression_of_relPiVanishing
      (Y := Work.Serre.cyl ((Work.Serre.killIncl (n + 1) Y).comp f))
      (A := Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))) (n + 1)
      (Work.Serre.RangeOne.cyl_joined_range ((Work.Serre.killIncl (n + 1) Y).comp f) x₀
        (hbij 0 (by omega) x₀))
      (fun a k hk => hset a k hk)
    intro d hd
    exact hc d (by omega)
  have hsetiso : ∀ t : ℕ, t < n + 2 → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (Work.Serre.cyl
        ((Work.Serre.killIncl (n + 1) Y).comp f)))
        (Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)))) t) :=
    fun t ht => Work.Serre.rangeWhiteheadInclInt hcomp t ht
  -- ### the homology isomorphism for the cylinder inclusion of `f'`
  obtain ⟨ec, hec⟩ := Work.Serre.cylHomeoExplicit ((Work.Serre.killIncl (n + 1) Y).comp f)
  have hcylincl : ∀ t : ℕ, t < n + 2 → IsIso (Work.Serre.intHomologyMap
      (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)) t) := by
    intro t ht
    let ecm : C(X, ↥(Set.range (Work.Serre.cylIncl
        ((Work.Serre.killIncl (n + 1) Y).comp f)))) := ec.toHomotopyEquiv.toFun
    have hfact : (Work.RatHurewicz.setIncl
          (Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)))).comp ecm
        = Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f) :=
      ContinuousMap.ext (fun x => hec x)
    have hsplit : Work.Serre.intHomologyMap
          (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)) t
        = Work.Serre.intHomologyMap ecm t ≫ Work.Serre.intHomologyMap
            (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl
              ((Work.Serre.killIncl (n + 1) Y).comp f)))) t := by
      rw [← Work.Serre.intHomologyMap_comp ecm
        (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl
          ((Work.Serre.killIncl (n + 1) Y).comp f)))) t, hfact]
    rw [hsplit]
    have h1 : IsIso (Work.Serre.intHomologyMap ecm t) :=
      Work.Serre.isIso_intHomologyMap_of_homotopyEquiv ec.toHomotopyEquiv t
    have h2 : IsIso (Work.Serre.intHomologyMap (Work.RatHurewicz.setIncl
        (Set.range (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)))) t) :=
      hsetiso t ht
    haveI := h1
    haveI := h2
    infer_instance
  -- ### the homology isomorphism for `f'` (retraction of the cylinder)
  have hisoF' : ∀ t : ℕ, t < n + 2 → IsIso
      (Work.Serre.intHomologyMap ((Work.Serre.killIncl (n + 1) Y).comp f) t) := by
    intro t ht
    obtain ⟨E, hE⟩ := Work.Serre.cylHomotopyEquivExplicit ((Work.Serre.killIncl (n + 1) Y).comp f)
    have hret : IsIso (Work.Serre.intHomologyMap
        (Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f)) t) := by
      have h1 : IsIso (Work.Serre.intHomologyMap E.toFun t) :=
        Work.Serre.isIso_intHomologyMap_of_homotopyEquiv E t
      rwa [hE] at h1
    have hff : Work.Serre.intHomologyMap ((Work.Serre.killIncl (n + 1) Y).comp f) t
        = Work.Serre.intHomologyMap
            (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)) t
          ≫ Work.Serre.intHomologyMap
            (Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f)) t := by
      rw [← Work.Serre.intHomologyMap_comp
          (Work.Serre.cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f))
          (Work.Serre.cylRetract ((Work.Serre.killIncl (n + 1) Y).comp f)) t,
        Work.Serre.cylRetract_cylIncl ((Work.Serre.killIncl (n + 1) Y).comp f)]
    rw [hff]
    have h1 := hcylincl t ht
    have h2 := hret
    haveI := h1
    haveI := h2
    infer_instance
  -- ### the homology isomorphism for `killIncl (n+1) Y`
  have hisoK : ∀ t : ℕ, t < n + 2 →
      IsIso (Work.Serre.intHomologyMap (Work.Serre.killIncl (n + 1) Y) t) :=
    fun t ht => isIso_intHomologyMap_attachIncl_aux (n + 1) Y
      (Work.Serre.KillIdx (n + 1) Y) (fun g => g) t (by omega)
  -- ### conclude for `f`
  haveI h1 : IsIso (Work.Serre.intHomologyMap ((Work.Serre.killIncl (n + 1) Y).comp f) j) :=
    hisoF' j hjN
  haveI h2 : IsIso (Work.Serre.intHomologyMap (Work.Serre.killIncl (n + 1) Y) j) :=
    hisoK j hjN
  have h3 : Work.Serre.intHomologyMap ((Work.Serre.killIncl (n + 1) Y).comp f) j
      ≫ inv (Work.Serre.intHomologyMap (Work.Serre.killIncl (n + 1) Y) j)
      = Work.Serre.intHomologyMap f j := by
    rw [Work.Serre.intHomologyMap_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change IsIso (Work.Serre.intHomologyMap f j)
  rw [← h3]
  infer_instance

end

end Work.Serre.Assembly
