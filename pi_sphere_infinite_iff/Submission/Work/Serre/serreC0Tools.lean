import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Stems.hurewiczMapN_surjective
import Submission.Work.Serre.AttachCompress.Assemble
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.serreC0Defs

/-!
# Tools for the C0 construction

* `subsingleton_homotopyGroup_of_compressRel_singleton`: if the pair `(X, {x₀})` has the
  compression property in dimension `d ≥ 1`, then `π_d(X,x₀)` is trivial;
* `wedgeCells_connected`: the wedge `⋁_J S^(k+1) = attachCells (k-1) PUnit J (const)` is
  `k`-connected, i.e. has trivial `π_j` for `j ≤ k`;
* `exists_sphereMap_hurewiczClass_eq`: every homology class in `H_m(X)` (for `X`
  `(m-1)`-connected, `m ≥ 2`) is the Hurewicz class of a map `S^m → X`.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- **Compression in dimension `d` against a point forces `π_d` to vanish.** -/
theorem subsingleton_homotopyGroup_of_compressRel_singleton {X : Type} [TopologicalSpace X]
    (x₀ : X) (d : ℕ) (hd : 1 ≤ d) (h : Work.RatHurewicz.CompressRel X ({x₀} : Set X) d) :
    Subsingleton (HomotopyGroup (Fin d) X x₀) := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨fun a b => ?_⟩
  suffices hkey : ∀ a : HomotopyGroup (Fin d) X x₀, a = 1 by rw [hkey a, hkey b]
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    have hbdr : ∀ x, x ∈ Cube.boundary (Fin d) → p.1 x ∈ ({x₀} : Set X) := by
      intro x hx
      simpa using p.2 x hx
    obtain ⟨G, hG0, hGb, hG1⟩ := h p.1 hbdr
    have hH1 : ∀ y, G (y, 1) = x₀ := by
      intro y
      have := hG1 y
      simpa using this
    have hHb : ∀ (y y' : Fin d → unitInterval) (t : unitInterval),
        y ∈ Cube.boundary (Fin d) → y' ∈ Cube.boundary (Fin d) → G (y, t) = G (y', t) := by
      intro y y' t hy hy'
      rw [hGb y hy t, hGb y' hy' t]
      simp only [p.2 y hy, p.2 y' hy']
    have hhom := Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased d p G hG0 hH1 hHb
    have hq : (Quotient.mk _ p : HomotopyGroup (Fin d) X x₀) = Quotient.mk _ GenLoop.const :=
      Quotient.sound hhom
    rw [hq, ← HomotopyGroup.one_def]

section Wedge

/-- The wedge `⋁_J S^{k+1}` is `k`-connected: `π_j` vanishes for `j ≤ k` (`k ≥ 1`). -/
theorem wedgeCells_connected (k : ℕ) (hk : 1 ≤ k) (J : Type) :
    ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (wedgeSpace k J) (wedgeBase k J)) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    haveI : Subsingleton (GenLoop (Fin 0) PUnit PUnit.unit) :=
      ⟨fun a b => Subtype.ext (ContinuousMap.ext (fun x => Subsingleton.elim _ _))⟩
    haveI : Subsingleton (HomotopyGroup (Fin 0) PUnit PUnit.unit) :=
      Quotient.mk_surjective.subsingleton
    exact (Work.Serre.attachIncl_pi0_bijective (k - 1) PUnit J (wedgeAttach k J)
      PUnit.unit).surjective.subsingleton
  · have hcomp : Work.RatHurewicz.CompressRel (wedgeSpace k J)
        (Set.range (Work.RatHurewicz.attachIncl (k - 1) PUnit J (wedgeAttach k J))) j :=
      Work.Serre.AttachCompress.compression (k - 1) PUnit J (wedgeAttach k J) j (by omega)
    have hrange : Set.range (Work.RatHurewicz.attachIncl (k - 1) PUnit J (wedgeAttach k J)) =
        ({wedgeBase k J} : Set (wedgeSpace k J)) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        have hy : y = PUnit.unit := Subsingleton.elim y PUnit.unit
        subst hy
        exact Set.mem_singleton _
      · rintro ⟨rfl, -⟩
        exact ⟨PUnit.unit, rfl⟩
    rw [hrange] at hcomp
    exact subsingleton_homotopyGroup_of_compressRel_singleton (wedgeBase k J) j hpos hcomp

end Wedge

section HurewiczMap

/-- **Every homology class in the first non-vanishing degree is the Hurewicz class of a map of
spheres.** -/
theorem exists_sphereMap_hurewiczClass_eq {X : Type} [TopologicalSpace X] {m : ℕ} (hm : 2 ≤ m)
    (x₀ : X) (hconn : ∀ j, j < m → Subsingleton (HomotopyGroup (Fin j) X x₀))
    (h : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology m) :
    ∃ g : C(Work.Stems.sphere m, X), Work.Stems.hurewiczClass m (by omega) g = h := by
  obtain ⟨α, hα⟩ := Work.Stems.hurewiczMapN_surjective m hm x₀ hconn h
  refine ⟨Work.Stems.cubeLift m (by omega) (Quotient.out α), ?_⟩
  rw [← hα]
  exact (Work.Stems.hurewiczMapN_out m (by omega) x₀ α).symm

end HurewiczMap

end Work.Serre
