import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Cover
import Submission.Work.RatHurewicz.Cofibre.VContract
import Submission.Work.RatHurewicz.Cofibre.collarHomotopyEquiv
import Submission.Work.RatHurewicz.Cofibre.PiTransfer
import Submission.Work.ThomBordism.TwoSet.Assembly
import Submission.Work.Stems.subsingleton_of_contraction
import Submission.Work.RatHurewicz.ExcisionSetup

/-!
# The compression property of the collar of `cofibreV`

`compressRel_cofibreV_collar`: for `ι : C(F, E)` with `π_j(F) = 0` for `j ≤ n`, the pair

  `(↥(cofibreV ι), {z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι})`

has the compression property in all dimensions `d ≤ n + 1` (`Work.RatHurewicz.CompressRel`).

This is the pair `(V, V ∩ U)` of the Blakers–Massey cover of the cofibre, i.e. the "punctured cone
relative to its collar" pair.  The proof combines the connectivity of the two pieces with
`Work.ThomBordism.TwoSet.Compress.ofSubsingleton`:

* `↥(cofibreV ι)` is contractible (`exists_contraction_cofibreV`), so all its homotopy groups vanish;
* the collar is homeomorphic to `↥(cofibreU ι ∩ cofibreV ι)`, which is homotopy equivalent to `F`
  (`Cofibre.collarHomotopyEquiv`), so its homotopy groups vanish in degrees `≤ n`.

`Compress.ofSubsingleton` turns the vanishing of `π_d(Y)` and `π_{d-1}(Z)` into the compression of
the pair `(Y, Z)` in dimension `d` (and the case `d = 0` is path connectedness plus a point of `Z`).
-/

open scoped Topology unitInterval

set_option linter.style.haveILetI false

namespace Work.RatHurewicz.Cofibre

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-! ## Two elementary `π₀` facts -/

/-- **Path connectedness transports along a homotopy equivalence.** -/
theorem nonempty_path_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hY : ∀ a b : Y, Nonempty (Path a b)) :
    ∀ a b : X, Nonempty (Path a b) := by
  intro a b
  obtain ⟨γ⟩ := hY (e.toFun a) (e.toFun b)
  obtain ⟨H⟩ := e.left_inv
  have hA : Path (e.invFun (e.toFun a)) a :=
    ⟨⟨fun t => H (t, a), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left a, H.map_one_left a⟩
  have hB : Path (e.invFun (e.toFun b)) b :=
    ⟨⟨fun t => H (t, b), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left b, H.map_one_left b⟩
  exact ⟨hA.symm.trans ((γ.map (f := ⇑e.invFun) e.invFun.continuous).trans hB)⟩

/-- **`π₀` of a path connected space is trivial.** -/
theorem subsingleton_piZero_of_paths {X : Type} [TopologicalSpace X] (x : X)
    (h : ∀ a b : X, Nonempty (Path a b)) : Subsingleton (HomotopyGroup (Fin 0) X x) := by
  have hZ : Subsingleton (ZerothHomotopy X) := by
    rw [subsingleton_iff]
    intro u v
    induction u using ZerothHomotopy.rec with
    | mk a =>
      induction v using ZerothHomotopy.rec with
      | mk b => exact ZerothHomotopy.sound (Classical.choice (h a b))
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
    (hZ.elim _ _)⟩

/-! ## The collar of `cofibreV` -/

/-- The collar of `cofibreV ι`, as a subset of `cofibreV ι`: the points of the punctured cone
lying in the lower half `cofibreU ι`. -/
abbrev collarSetV (ι : C(F, E)) : Set ↥(Work.RatHurewicz.cofibreV ι) :=
  {z : ↥(Work.RatHurewicz.cofibreV ι) |
    (z : Work.RatHurewicz.cofibre ι) ∈ Work.RatHurewicz.cofibreU ι}

/-- **The collar of `cofibreV ι` is homeomorphic to `cofibreU ι ∩ cofibreV ι`** (the elements are
the same points of the cofibre, packaged in the two possible subtypes). -/
def collarHomeo (ι : C(F, E)) :
    ↥(collarSetV ι) ≃ₜ ↥(Work.RatHurewicz.cofibreU ι ∩ Work.RatHurewicz.cofibreV ι) where
  toFun z := ⟨z.1.1, ⟨z.2, z.1.2⟩⟩
  invFun w := ⟨⟨w.1, w.2.2⟩, w.2.1⟩
  left_inv z := by ext; rfl
  right_inv w := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The collar of `cofibreV ι` is homotopy equivalent to `F`.** -/
theorem nonempty_homotopyEquiv_collarSetV (ι : C(F, E)) [Nonempty F] :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(collarSetV ι) F) :=
  ⟨(collarHomeo ι).toHomotopyEquiv.trans (collarHomotopyEquiv ι).some⟩

/-! ## The compression property -/

theorem compressRel_cofibreV_collar {E F : Type} [TopologicalSpace E] [TopologicalSpace F] [Nonempty F]
    (ι : C(F, E)) (n : ℕ)
    (hF : ∀ (j : ℕ), j ≤ n → ∀ y : F, Subsingleton (HomotopyGroup (Fin j) F y)) :
    ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel (↥(Work.RatHurewicz.cofibreV ι))
      {z : ↥(Work.RatHurewicz.cofibreV ι) |
        (z : Work.RatHurewicz.cofibre ι) ∈ Work.RatHurewicz.cofibreU ι} d := by
  obtain ⟨eZ⟩ := nonempty_homotopyEquiv_collarSetV ι
  -- `F` is path connected
  have hFpc : ∀ a b : F, Nonempty (Path a b) := by
    haveI : PathConnectedSpace F :=
      pathConnectedSpace_of_subsingleton_pi_zero (Classical.ofNonempty : F) (hF 0 (by omega) _)
    exact fun a b => PathConnectedSpace.joined a b
  -- the collar is path connected
  have hZpc : ∀ a b : ↥(collarSetV ι), Nonempty (Path a b) :=
    nonempty_path_of_homotopyEquiv eZ hFpc
  -- the homotopy groups of the collar vanish in degrees `≤ n`
  have hZpi : ∀ j, j ≤ n → ∀ z : ↥(collarSetV ι),
      Subsingleton (HomotopyGroup (Fin j) ↥(collarSetV ι) z) := by
    intro j hj z
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      exact subsingleton_piZero_of_paths z hZpc
    · haveI : Nonempty (Fin j) := ⟨⟨0, hpos⟩⟩
      exact (subsingleton_homotopyGroup_of_homotopyEquiv eZ z).mpr (hF j hj (eZ.toFun z))
  -- the collar is nonempty
  have hZne : (collarSetV ι).Nonempty :=
    ⟨(eZ.invFun (Classical.ofNonempty : F)), (eZ.invFun (Classical.ofNonempty : F)).2⟩
  -- `cofibreV ι` is contractible, so all its homotopy groups vanish
  obtain ⟨H, h0, b, h1⟩ := exists_contraction_cofibreV ι
  have hVpi : ∀ j, ∀ v : ↥(Work.RatHurewicz.cofibreV ι),
      Subsingleton (HomotopyGroup (Fin j) ↥(Work.RatHurewicz.cofibreV ι) v) :=
    fun j v => Work.Stems.subsingleton_of_contraction b H h0 h1 j v
  intro d hd
  change Work.ThomBordism.TwoSet.Compress ↥(Work.RatHurewicz.cofibreV ι) (collarSetV ι) d
  rcases Nat.eq_zero_or_pos d with h0d | hpos
  · subst h0d
    exact Work.ThomBordism.TwoSet.Compress.ofSubsingletonZero (hVpi 0) hZne
  · refine Work.ThomBordism.TwoSet.Compress.ofSubsingleton hpos (hVpi d) ?_
    intro z
    exact hZpi (d - 1) (by omega) z

end

end Work.RatHurewicz.Cofibre
