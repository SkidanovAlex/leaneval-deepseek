import Mathlib
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Stems.homotopyGroup_prod
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.RatHurewicz.SuspRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pair `(X × ℝ^k, X × (ℝ^k ∖ {0}))` has the compression property below the fibre dimension

**Target.** `Work.ThomBordism.Grassmann.ClosedPiece.fibreCompress`: for every space `X`, every
`k : ℕ` and every `d` with `d + 1 ≤ k`, the pair
`(X × ℝ^k, X × (ℝ^k ∖ {0}))` has the compression property `Work.RatHurewicz.CompressRel` in
dimension `d`.

**Route.**  The statement is proved first for `X = PUnit` (i.e. for the pair
`(ℝ^k, ℝ^k ∖ {0})`, `Work.ThomBordism.Grassmann.ClosedPiece.compressRel_euclidean`) and then
lifted to general `X` by homotoping only the second coordinate
(`compressRel_prod_of_compressRel`); homotoping the fibre coordinate relative to the boundary of
the cube is always possible for a map of pairs into a product, independently of `X`.

For the Euclidean pair the proof is the standard one:
* the ambient space `ℝ^k` is a normed space, hence carries a *connector*
  (`Work.RatHurewicz.Connector`, `euclidConnector`): the straight-line contraction
  `c (p, q, t) = (1 - t) • p + t • q`.  By `Work.RatHurewicz.relPiVanishingOfConnector` the
  homotopy fibre of `{v | v ≠ 0} ↪ ℝ^k` is homotopy equivalent to `{v | v ≠ 0}`, so the relative
  groups `π_e` of the pair are those of the punctured space;
* the punctured space `ℝ^k ∖ {0}` is homotopy equivalent to the unit sphere `S^{k-1}`
  (`Work.Cohomology.punctured_homotopyEquiv_sphere`), so
  `π_e(ℝ^k ∖ {0}) = 0` for `e ≤ k - 2` (`Work.Stems.sphereConnectivity`);
* `Work.RatHurewicz.compression_of_relPiVanishing` converts the vanishing of the relative groups
  (plus the `0`-connectivity of the pair) into the compression property.
-/

namespace Work.ThomBordism.Grassmann.ClosedPiece

noncomputable section

open scoped Topology unitInterval

/-! ## Helper lemmas -/

/-- **The straight-line connector of a Euclidean space**: `c (p, q, t) = (1 - t) • p + t • q`. -/
def euclidConnector (m : ℕ) :
    Work.RatHurewicz.Connector (EuclideanSpace ℝ (Fin m)) where
  c := ⟨fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) × unitInterval =>
      (1 - (p.2.2 : ℝ)) • p.1 + (p.2.2 : ℝ) • p.2.1, by fun_prop⟩
  zero := fun p q => by simp
  one := fun p q => by simp
  diag := fun p t => by
    change (1 - (t : ℝ)) • p + (t : ℝ) • p = p
    rw [← add_smul, sub_add_cancel, one_smul]

/-- A fixed nonzero vector of `ℝ^{n+1}`. -/
def euclidBase (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single ⟨0, Nat.succ_pos n⟩ 1

theorem euclidBase_ne_zero (n : ℕ) : euclidBase n ≠ 0 := by
  simp [euclidBase]

/-- **The homotopy groups of the punctured Euclidean space vanish below the sphere dimension.**
`ℝ^{n+1} ∖ {0}` is homotopy equivalent to `Sⁿ`, whose `π_e` vanishes for `e < n`
(`Work.Stems.sphereConnectivity`). -/
theorem punctured_homotopyGroup_subsingleton (n : ℕ) :
    ∀ e, e + 1 ≤ n → ∀ x : {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0},
      Subsingleton (HomotopyGroup (Fin e)
        {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0} x) := by
  intro e he x
  obtain ⟨ee⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere
    (EuclideanSpace ℝ (Fin (n + 1)))
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · -- `π₀`: both spaces are path connected
    subst h0
    haveI : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      (isPathConnected_iff_pathConnectedSpace).mp
        (isPathConnected_sphere (E := EuclideanSpace ℝ (Fin (n + 1))) ?_ 0 (by norm_num))
    · haveI : Subsingleton
          (ZerothHomotopy (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
      haveI : Subsingleton
          (ZerothHomotopy {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0}) :=
        Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv ee inferInstance
      exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy
        (X := {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0}) (x := x)).injective
          (Subsingleton.elim _ _)⟩
    · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n + 1)
  · -- `e ≥ 1`: transport along the homotopy equivalence with the sphere
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    haveI : Subsingleton (HomotopyGroup (Fin (e' + 1))
        (Work.Stems.sphere n) (ee.toFun x)) :=
      Work.Stems.sphereConnectivity n (e' + 1) (by omega) (ee.toFun x)
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (e' + 1)) ee x
    exact ⟨fun u v => me.injective (Subsingleton.elim _ _)⟩

/-- **The relative homotopy groups of `(ℝ^{n+1}, ℝ^{n+1} ∖ {0})` vanish below the sphere
dimension.**  The connector on the ambient Euclidean space identifies the homotopy fibre of the
inclusion with the punctured space itself. -/
theorem relPiVanishing_punctured (n : ℕ) (hn : 1 ≤ n)
    (a : {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0}) :
    ∀ e, e ≤ n - 1 → Subsingleton (Work.RatHurewicz.RelHomotopyGroup
      (Work.RatHurewicz.setIncl {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0}) a e) := by
  intro e he
  exact Work.RatHurewicz.relPiVanishingOfConnector (euclidConnector (n + 1))
    (Work.RatHurewicz.setIncl {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0}) a e
    (punctured_homotopyGroup_subsingleton n e (by omega) a)

/-- **The compression property of the Euclidean pair `(ℝ^{n+1}, ℝ^{n+1} ∖ {0})` in all dimensions
`d` with `d + 1 ≤ n + 1`.** -/
theorem compressRel_euclidean (n : ℕ) :
    ∀ d, d + 1 ≤ n + 1 →
      Work.RatHurewicz.CompressRel (EuclideanSpace ℝ (Fin (n + 1)))
        {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} d := by
  intro d hd
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`, i.e. `ℝ¹`: then `d = 0` and the statement is `0`-connectivity
    subst hn0
    have hd0 : d = 0 := by omega
    subst hd0
    intro f hf
    refine ⟨⟨fun p : Work.RatHurewicz.ICube 0 × I =>
        (1 - (p.2 : ℝ)) • f (fun i => i.elim0) + (p.2 : ℝ) • euclidBase 0, by fun_prop⟩,
      ?_, ?_, ?_⟩
    · intro x
      have hx : x = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      show (1 - ((0 : I) : ℝ)) • f (fun i => i.elim0) + ((0 : I) : ℝ) • euclidBase 0 = f x
      rw [hx]
      simp
    · intro x hx t
      obtain ⟨i, -⟩ := hx
      exact i.elim0
    · intro x
      show (1 - ((1 : I) : ℝ)) • f (fun i => i.elim0) + ((1 : I) : ℝ) • euclidBase 0
        ∈ {v : EuclideanSpace ℝ (Fin (0 + 1)) | v ≠ 0}
      simpa using euclidBase_ne_zero 0
  · -- `n ≥ 1`: `compression_of_relPiVanishing`
    have hn : 1 ≤ n := hnpos
    refine Work.RatHurewicz.compression_of_relPiVanishing
      (Y := EuclideanSpace ℝ (Fin (n + 1)))
      (A := {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0}) (n - 1) ?_ ?_ d (by omega)
    · -- `0`-connectivity: join any point to `euclidBase n` by a straight line
      intro y
      exact ⟨⟨euclidBase n, euclidBase_ne_zero n⟩, ⟨⟨
        fun t : unitInterval => (1 - (t : ℝ)) • y + (t : ℝ) • euclidBase n,
        by fun_prop⟩, by simp, by simp⟩⟩
    · -- vanishing of the relative groups
      intro a e he
      exact relPiVanishing_punctured n hn a e (by omega)

/-- **The compression property is stable under taking the product with a factor in which the
homotopy takes place**: if the pair `(Y, B)` has the compression property in dimension `d`, then so
does `(X × Y, X × B)` — a map of pairs `(I^d, ∂I^d) → (X × Y, X × B)` is homotoped, relative to
the boundary and *without changing its first coordinate*, by applying the compression of `(Y, B)`
to its second coordinate. -/
theorem compressRel_prod_of_compressRel (X : Type) [TopologicalSpace X]
    (Y : Type) [TopologicalSpace Y] (B : Set Y) (d : ℕ)
    (h : Work.RatHurewicz.CompressRel Y B d) :
    Work.RatHurewicz.CompressRel (X × Y) {p : X × Y | p.2 ∈ B} d := by
  intro f hf
  let f₂ : C(Work.RatHurewicz.ICube d, Y) :=
    ⟨fun x => (f x).2, continuous_snd.comp f.continuous⟩
  have hf₂ : ∀ x, x ∈ Cube.boundary (Fin d) → f₂ x ∈ B := fun x hx => hf x hx
  obtain ⟨H, hH0, hHb, hH1⟩ := h f₂ hf₂
  refine ⟨⟨fun p : Work.RatHurewicz.ICube d × I => ((f p.1).1, H p), by fun_prop⟩,
    ?_, ?_, ?_⟩
  · intro x
    exact Prod.ext rfl (hH0 x)
  · intro x hx t
    exact Prod.ext rfl (hHb x hx t)
  · intro x
    exact hH1 x

/-- **The pair `(X × ℝ^k, X × (ℝ^k ∖ {0}))` has the compression property in all dimensions
`d` with `d + 1 ≤ k`.** -/
theorem fibreCompress (X : Type) [TopologicalSpace X] (k : ℕ) :
    ∀ d, d + 1 ≤ k → Work.RatHurewicz.CompressRel (X × EuclideanSpace ℝ (Fin k))
      {p : X × EuclideanSpace ℝ (Fin k) | p.2 ≠ 0} d := by
  intro d hd
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · omega
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    exact compressRel_prod_of_compressRel X (EuclideanSpace ℝ (Fin (n + 1)))
      {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} d
      (compressRel_euclidean n d (by omega))

end

end Work.ThomBordism.Grassmann.ClosedPiece
